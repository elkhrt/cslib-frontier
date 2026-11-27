/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ExistsReal
public import CslibFrontier.Computability.Complexity.Problems.RealArithmetic
public import CslibFrontier.Logics.RealArithmetic.Basic
public import CslibFrontier.Logics.RealArithmetic.Encoding
public import CslibFrontier.Computability.Complexity.Problems.AffineRankMinimization.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Logics.RealArithmetic.FormulaTokenDecoding
import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
import CslibFrontier.Logics.RealArithmetic.TermTokenDecoding
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ETR Term and Formula Gate-Block Compilers

Right-to-left stack compilers from encoded real-arithmetic formula words into arithmetic
circuits, together with evaluation lemmas for comparison, Boolean, and sum-of-squares blocks.
-/

public section

namespace Cslib.Complexity

open Matrix Cslib.Logic.RealArithmetic Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Unary-Indexed Encoding of `ArithGate` -/

/-- Unary-indexed binary encoding of `ArithGate` (used for polynomial-time compilation when
gate counts are polynomially bounded in the input length). -/
@[expose] def encArithGateUnary : ArithGate ↪ List Bool where
  toFun
    | .input i => encSum encUnary (encSum encRat (encSum (encPair encUnary encUnary)
        (encSum (encPair encUnary encUnary) encUnary))) (.inl i)
    | .const c => encSum encUnary (encSum encRat (encSum (encPair encUnary encUnary)
        (encSum (encPair encUnary encUnary) encUnary))) (.inr (.inl c))
    | .add a b => encSum encUnary (encSum encRat (encSum (encPair encUnary encUnary)
        (encSum (encPair encUnary encUnary) encUnary))) (.inr (.inr (.inl (a, b))))
    | .mul a b => encSum encUnary (encSum encRat (encSum (encPair encUnary encUnary)
        (encSum (encPair encUnary encUnary) encUnary))) (.inr (.inr (.inr (.inl (a, b)))))
    | .neg a => encSum encUnary (encSum encRat (encSum (encPair encUnary encUnary)
        (encSum (encPair encUnary encUnary) encUnary))) (.inr (.inr (.inr (.inr a))))
  inj' a b h := by
    cases a <;> cases b <;>
      have h' := (encSum encUnary (encSum encRat (encSum (encPair encUnary encUnary)
        (encSum (encPair encUnary encUnary) encUnary)))).injective h <;>
      simp_all

/-- Encoding length bound for `encArithGateUnary` in terms of index and constant bounds. -/
theorem length_encArithGateUnary_le (g : ArithGate) {B C : ℕ}
    (hidx : ∀ i, g = .input i → i ≤ B)
    (harg : ∀ a, g = .neg a → a ≤ B)
    (hbin : ∀ l r, (g = .add l r ∨ g = .mul l r) → l ≤ B ∧ r ≤ B)
    (hc : ∀ c, g = .const c → (encRat c).length ≤ C) :
    (encArithGateUnary g).length ≤ 6 * B + C + 12 := by
  cases g with
  | input i =>
    have hi := hidx i rfl
    simp only [encArithGateUnary, Function.Embedding.coeFn_mk, encSum_inl, List.length_cons,
      encUnary_apply, List.length_replicate]
    omega
  | const c =>
    have hcc := hc c rfl
    simp only [encArithGateUnary, Function.Embedding.coeFn_mk, encSum_inr, encSum_inl,
      List.length_cons]
    omega
  | add l r =>
    obtain ⟨hl, hr⟩ := hbin l r (Or.inl rfl)
    simp only [encArithGateUnary, Function.Embedding.coeFn_mk, encSum_inr, encSum_inl,
      List.length_cons, length_encPair, encUnary_apply, List.length_replicate]
    omega
  | mul l r =>
    obtain ⟨hl, hr⟩ := hbin l r (Or.inr rfl)
    simp only [encArithGateUnary, Function.Embedding.coeFn_mk, encSum_inr, encSum_inl,
      List.length_cons, length_encPair, encUnary_apply, List.length_replicate]
    omega
  | neg a =>
    have ha := harg a rfl
    simp only [encArithGateUnary, Function.Embedding.coeFn_mk, encSum_inr, List.length_cons,
      encUnary_apply, List.length_replicate]
    omega

/-! ### Right-to-Left Stack Compilation of `Term` Token Streams -/

/-- One right-to-left step compiling a `TermToken` onto `(stack, gates)`. -/
@[expose] def compileTermTokenStep (state : List ℕ × List ArithGate) (tok : TermToken) :
    List ℕ × List ArithGate :=
  let stack := state.1
  let gates := state.2
  let gid := gates.length
  match tok with
  | .inl z => (gid :: stack, gates ++ [.const (z : ℚ)])
  | .inr (.inl i) => (gid :: stack, gates ++ [.input i])
  | .inr (.inr (.inl ())) =>
      (gid :: stack.tail.tail, gates ++ [.add (stack.headD 0) (stack.tail.headD 0)])
  | .inr (.inr (.inr ())) =>
      (gid :: stack.tail.tail, gates ++ [.mul (stack.headD 0) (stack.tail.headD 0)])

/-- Compile a `TermToken` stream from right to left starting from existing `gates`. -/
@[expose] def compileTermTokens (tokens : List TermToken) (gates : List ArithGate) :
    List ℕ × List ArithGate :=
  tokens.reverse.foldl compileTermTokenStep ([], gates)

/-- Gate-count and stack-size bounds for one step of `compileTermTokenStep`. -/
theorem compileTermTokenStep_length (state : List ℕ × List ArithGate) (tok : TermToken) :
    (compileTermTokenStep state tok).2.length = state.2.length + 1 ∧
    (compileTermTokenStep state tok).1.length ≤ state.1.length + 1 := by
  rcases tok with z | i | ⟨⟩ | ⟨⟩ <;>
    simp [compileTermTokenStep, List.length_tail] <;> omega

/-! ### Shared Evaluation Helpers for Appended Gate Blocks -/

/-- Stepwise evaluation of an appended gate block. -/
theorem evalGatesList_append_step {n : ℕ} (y : Fin n → ℝ) (gs newGs : List ArithGate)
    (idx : ℕ) (hidx : idx < newGs.length) :
    (evalGatesList y (gs ++ newGs)).getD (gs.length + idx) 0 =
      evalGateStep y ((evalGatesList y (gs ++ newGs)).take (gs.length + idx)) newGs[idx] := by
  have hlen : (gs ++ newGs.take idx).length = gs.length + idx := by
    simp [List.length_take]; omega
  have hsplit : gs ++ newGs = (gs ++ newGs.take idx) ++ [newGs[idx]] ++
      newGs.drop (idx + 1) := by
    rw [List.append_assoc, List.append_assoc]
    congr 1
    have hdrop : newGs.drop idx = newGs[idx] :: newGs.drop (idx + 1) :=
      List.drop_eq_getElem_cons hidx
    conv_lhs => rw [← List.take_append_drop idx newGs]
    rw [hdrop]
    simp
  have hlen_lt : gs.length + idx < ((gs ++ newGs.take idx) ++ [newGs[idx]]).length := by
    simp [List.length_take]; omega
  rw [hsplit, evalGatesList_append_getD y _ _ hlen_lt, ← hlen, evalGatesList_snoc_last]
  have htake : (evalGatesList y ((gs ++ newGs.take idx) ++ [newGs[idx]] ++
      newGs.drop (idx + 1))).take (gs ++ newGs.take idx).length =
      evalGatesList y (gs ++ newGs.take idx) := by
    apply List.ext_getElem
    · simp [evalGatesList_length, hlen]; omega
    · intro j hj1 hj2
      simp only [List.getElem_take]
      have hj_len : j < (gs ++ newGs.take idx).length := by
        simpa [evalGatesList_length] using hj2
      have hj_len2 : j < ((gs ++ newGs.take idx) ++ [newGs[idx]]).length := by
        simp; omega
      have h1 := evalGatesList_append_getD y ((gs ++ newGs.take idx) ++ [newGs[idx]])
        (newGs.drop (idx + 1)) hj_len2
      have h2 := evalGatesList_append_getD y (gs ++ newGs.take idx) [newGs[idx]] hj_len
      have h3 := h1.trans h2
      have hj1' : j < (evalGatesList y ((gs ++ newGs.take idx) ++ [newGs[idx]] ++
          newGs.drop (idx + 1))).length := by
        rw [evalGatesList_length]; simp; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1',
        List.getElem?_eq_getElem hj2, Option.getD_some] at h3
      exact h3
  rw [htake]

/-- Evaluate an appended addition gate at offset `idx`. -/
theorem evalGatesList_at_add {n : ℕ} (y : Fin n → ℝ) (gs newGs : List ArithGate)
    {idx l r : ℕ} (hidx : idx < newGs.length) (hg : newGs[idx] = .add l r)
    (hl : l < gs.length + idx) (hr : r < gs.length + idx) :
    (evalGatesList y (gs ++ newGs)).getD (gs.length + idx) 0 =
      (evalGatesList y (gs ++ newGs)).getD l 0 + (evalGatesList y (gs ++ newGs)).getD r 0 := by
  rw [evalGatesList_append_step y gs newGs idx hidx, hg]
  simp [List.getD_eq_getElem?_getD, hl, hr]

/-- Evaluate an appended multiplication gate at offset `idx`. -/
theorem evalGatesList_at_mul {n : ℕ} (y : Fin n → ℝ) (gs newGs : List ArithGate)
    {idx l r : ℕ} (hidx : idx < newGs.length) (hg : newGs[idx] = .mul l r)
    (hl : l < gs.length + idx) (hr : r < gs.length + idx) :
    (evalGatesList y (gs ++ newGs)).getD (gs.length + idx) 0 =
      (evalGatesList y (gs ++ newGs)).getD l 0 * (evalGatesList y (gs ++ newGs)).getD r 0 := by
  rw [evalGatesList_append_step y gs newGs idx hidx, hg]
  simp [List.getD_eq_getElem?_getD, hl, hr]

/-- Evaluate an appended negation gate at offset `idx`. -/
theorem evalGatesList_at_neg {n : ℕ} (y : Fin n → ℝ) (gs newGs : List ArithGate)
    {idx a : ℕ} (hidx : idx < newGs.length) (hg : newGs[idx] = .neg a)
    (ha : a < gs.length + idx) :
    (evalGatesList y (gs ++ newGs)).getD (gs.length + idx) 0 =
      -(evalGatesList y (gs ++ newGs)).getD a 0 := by
  rw [evalGatesList_append_step y gs newGs idx hidx, hg]
  simp [List.getD_eq_getElem?_getD, ha]

/-- Evaluate an appended constant gate at offset `idx`. -/
theorem evalGatesList_at_const {n : ℕ} (y : Fin n → ℝ) (gs newGs : List ArithGate)
    {idx : ℕ} {c : ℚ} (hidx : idx < newGs.length) (hg : newGs[idx] = .const c) :
    (evalGatesList y (gs ++ newGs)).getD (gs.length + idx) 0 = (c : ℝ) := by
  rw [evalGatesList_append_step y gs newGs idx hidx, hg]; rfl

/-- Evaluate an appended input gate at offset `idx`. -/
theorem evalGatesList_at_input {n : ℕ} (y : Fin n → ℝ) (gs newGs : List ArithGate)
    {idx v : ℕ} (hidx : idx < newGs.length) (hg : newGs[idx] = .input v) (hv : v < n) :
    (evalGatesList y (gs ++ newGs)).getD (gs.length + idx) 0 = y ⟨v, hv⟩ := by
  rw [evalGatesList_append_step y gs newGs idx hidx, hg]
  simp [hv]

private theorem compileTermTokenStep_const {n : ℕ} (st : List ℕ × List ArithGate) (z : ℤ) :
    compileTermTokenStep st (TermToken.ofFin (n := n) (.inl z)) =
      (st.2.length :: st.1, st.2 ++ [.const (z : ℚ)]) := rfl

private theorem compileTermTokenStep_var {n : ℕ} (st : List ℕ × List ArithGate) (i : Fin n) :
    compileTermTokenStep st (TermToken.ofFin (.inr (.inl i))) =
      (st.2.length :: st.1, st.2 ++ [.input i.1]) := rfl

private theorem compileTermTokenStep_add {n : ℕ} (st : List ℕ × List ArithGate) :
    compileTermTokenStep st (TermToken.ofFin (n := n) (.inr (.inr (.inl ())))) =
      (st.2.length :: st.1.tail.tail,
        st.2 ++ [.add (st.1.headD 0) (st.1.tail.headD 0)]) := rfl

private theorem compileTermTokenStep_mul {n : ℕ} (st : List ℕ × List ArithGate) :
    compileTermTokenStep st (TermToken.ofFin (n := n) (.inr (.inr (.inr ())))) =
      (st.2.length :: st.1.tail.tail,
        st.2 ++ [.mul (st.1.headD 0) (st.1.tail.headD 0)]) := rfl

/-- Correctness and well-formedness of right-to-left term compilation. -/
theorem compileTermTokens_correct {n N : ℕ} (hn : n ≤ N) (t : Term n)
    (stack : List ℕ) (gates : List ArithGate)
    (hwf : ∀ (k : ℕ) (hk : k < gates.length), gates[k].WellFormed N k)
    (hstack : ∀ g ∈ stack, g < gates.length) :
    let res := ((encTerm_tokens n t).map TermToken.ofFin).reverse.foldl
      compileTermTokenStep (stack, gates)
    ∃ (gt : ℕ),
      res.1 = gt :: stack ∧
      gt < res.2.length ∧
      gates <+: res.2 ∧
      (∀ (k : ℕ) (hk : k < res.2.length), res.2[k].WellFormed N k) ∧
      (∀ (x : Fin N → ℝ),
        (evalGatesList x res.2).getD gt 0 = t.eval (fun i ↦ x ⟨i.1, i.2.trans_le hn⟩)) := by
  induction t generalizing stack gates with
  | const z =>
    simp only [encTerm_tokens, List.map_singleton, List.reverse_singleton,
      List.foldl_cons, List.foldl_nil, compileTermTokenStep_const]
    refine ⟨gates.length, rfl, by simp, by simp, ?_, ?_⟩
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk ⊢
      by_cases hlt : k < gates.length
      · rw [List.getElem_append_left hlt]; exact hwf k hlt
      · have heq : k = gates.length := by omega
        subst heq; simp
    · intro x
      rw [evalGatesList_snoc_last]; simp [Term.eval]
  | var i =>
    simp only [encTerm_tokens, List.map_singleton, List.reverse_singleton,
      List.foldl_cons, List.foldl_nil, compileTermTokenStep_var]
    refine ⟨gates.length, rfl, by simp, by simp, ?_, ?_⟩
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk ⊢
      by_cases hlt : k < gates.length
      · rw [List.getElem_append_left hlt]; exact hwf k hlt
      · have heq : k = gates.length := by omega
        subst heq; simp [i.2.trans_le hn]
    · intro x
      rw [evalGatesList_snoc_last]; simp [Term.eval, i.2.trans_le hn]
  | add a b iha ihb =>
    obtain ⟨gb, hsb, hgb_lt, hpref_b, hwf_b, heval_b⟩ := ihb stack gates hwf hstack
    set res_b := ((encTerm_tokens n b).map TermToken.ofFin).reverse.foldl
      compileTermTokenStep (stack, gates)
    have hsb_mem : ∀ g ∈ gb :: stack, g < res_b.2.length := fun g hg ↦ by
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hgb_lt
      · exact (hstack g hg).trans_le hpref_b.length_le
    have hres_b_eq : res_b = (gb :: stack, res_b.2) := Prod.ext hsb rfl
    have hiha := iha (gb :: stack) res_b.2 hwf_b hsb_mem
    rw [← hres_b_eq] at hiha
    obtain ⟨ga, hsa, hga_lt, hpref_a, hwf_a, heval_a⟩ := hiha
    set res_a := ((encTerm_tokens n a).map TermToken.ofFin).reverse.foldl
      compileTermTokenStep res_b
    have hgb_lt' : gb < res_a.2.length := hgb_lt.trans_le hpref_a.length_le
    have hfold : ((encTerm_tokens n (a.add b)).map TermToken.ofFin).reverse.foldl
        compileTermTokenStep (stack, gates) =
        (res_a.2.length :: res_a.1.tail.tail,
          res_a.2 ++ [.add (res_a.1.headD 0) (res_a.1.tail.headD 0)]) := by
      have htok : encTerm_tokens n (a.add b) =
          .inr (.inr (.inl ())) :: (encTerm_tokens n a ++ encTerm_tokens n b) := by
        simp [encTerm_tokens]
      rw [htok, List.map_cons, List.map_append, List.reverse_cons, List.reverse_append,
        List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact compileTermTokenStep_add res_a
    dsimp only
    rw [hfold]
    refine ⟨res_a.2.length, by simp [hsa], by simp,
      hpref_b.trans (hpref_a.trans (by simp)), ?_, ?_⟩
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk ⊢
      by_cases hlt : k < res_a.2.length
      · rw [List.getElem_append_left hlt]; exact hwf_a k hlt
      · have heq : k = res_a.2.length := by omega
        subst heq; simp [ArithGate.wellFormed_add, hsa, hga_lt, hgb_lt']
    · intro x
      rw [evalGatesList_snoc_last]
      simp only [hsa, List.headD_cons, List.tail_cons, evalGateStep_add, Term.eval]
      obtain ⟨ext, hext⟩ := hpref_a
      rw [heval_a x, ← hext, evalGatesList_append_getD x _ _ hgb_lt, heval_b x]
  | mul a b iha ihb =>
    obtain ⟨gb, hsb, hgb_lt, hpref_b, hwf_b, heval_b⟩ := ihb stack gates hwf hstack
    set res_b := ((encTerm_tokens n b).map TermToken.ofFin).reverse.foldl
      compileTermTokenStep (stack, gates)
    have hsb_mem : ∀ g ∈ gb :: stack, g < res_b.2.length := fun g hg ↦ by
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hgb_lt
      · exact (hstack g hg).trans_le hpref_b.length_le
    have hres_b_eq : res_b = (gb :: stack, res_b.2) := Prod.ext hsb rfl
    have hiha := iha (gb :: stack) res_b.2 hwf_b hsb_mem
    rw [← hres_b_eq] at hiha
    obtain ⟨ga, hsa, hga_lt, hpref_a, hwf_a, heval_a⟩ := hiha
    set res_a := ((encTerm_tokens n a).map TermToken.ofFin).reverse.foldl
      compileTermTokenStep res_b
    have hgb_lt' : gb < res_a.2.length := hgb_lt.trans_le hpref_a.length_le
    have hfold : ((encTerm_tokens n (a.mul b)).map TermToken.ofFin).reverse.foldl
        compileTermTokenStep (stack, gates) =
        (res_a.2.length :: res_a.1.tail.tail,
          res_a.2 ++ [.mul (res_a.1.headD 0) (res_a.1.tail.headD 0)]) := by
      have htok : encTerm_tokens n (a.mul b) =
          .inr (.inr (.inr ())) :: (encTerm_tokens n a ++ encTerm_tokens n b) := by
        simp [encTerm_tokens]
      rw [htok, List.map_cons, List.map_append, List.reverse_cons, List.reverse_append,
        List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact compileTermTokenStep_mul res_a
    dsimp only
    rw [hfold]
    refine ⟨res_a.2.length, by simp [hsa], by simp,
      hpref_b.trans (hpref_a.trans (by simp)), ?_, ?_⟩
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk ⊢
      by_cases hlt : k < res_a.2.length
      · rw [List.getElem_append_left hlt]; exact hwf_a k hlt
      · have heq : k = res_a.2.length := by omega
        subst heq; simp [ArithGate.wellFormed_mul, hsa, hga_lt, hgb_lt']
    · intro x
      rw [evalGatesList_snoc_last]
      simp only [hsa, List.headD_cons, List.tail_cons, evalGateStep_mul, Term.eval]
      obtain ⟨ext, hext⟩ := hpref_a
      rw [heval_a x, ← hext, evalGatesList_append_getD x _ _ hgb_lt, heval_b x]

/-! ### Right-to-Left Stack Compilation of `Formula` Token Streams -/

/-- State of the formula-to-circuit compiler: `(stack, zeroGates, gates, nextSlack)`. -/
abbrev FormulaCompileState := List ℕ × List ℕ × List ArithGate × ℕ

/-- Gate block appended for an `eqZero` comparison (`11` gates). -/
@[expose] def eqZeroGateBlock (k gt nextSlack : ℕ) : List ArithGate :=
  [ .input nextSlack, .input (nextSlack + 1), .const 1, .neg k,
    .add (k + 2) (k + 3), .mul k (k + 4), .mul k gt, .mul gt (k + 1),
    .neg (k + 2), .add (k + 7) (k + 8), .mul (k + 4) (k + 9) ]

/-- Gate block appended for an `ltZero` comparison (`19` gates). -/
@[expose] def ltZeroGateBlock (k gt nextSlack : ℕ) : List ArithGate :=
  [ .input nextSlack, .input (nextSlack + 1), .input (nextSlack + 2),
    .input (nextSlack + 3), .const 1, .neg k, .add (k + 4) (k + 5),
    .mul k (k + 6), .mul (k + 1) (k + 1), .add gt (k + 8), .mul k (k + 9),
    .mul (k + 1) (k + 2), .neg (k + 4), .add (k + 11) (k + 12), .mul k (k + 13),
    .mul (k + 3) (k + 3), .neg (k + 15), .add gt (k + 16), .mul (k + 6) (k + 17) ]

/-- One right-to-left step compiling a `FormulaToken` into Tseitin Boolean-variable arithmetic
gates and zero-forced residual gates. -/
@[expose] def compileFormulaTokenStep (st : FormulaCompileState) (tok : FormulaToken) :
    FormulaCompileState :=
  let stack := st.1
  let zeros := st.2.1
  let gates := st.2.2.1
  let nextSlack := st.2.2.2
  match tok with
  | .inl () =>
      (gates.length :: stack, zeros, gates ++ [.const 0], nextSlack)
  | .inr (.inl termWord) =>
      let ts := (termTokensDecoder.decode termWord).getD []
      let res := compileTermTokens ts gates
      let gt := res.1.headD 0
      let gates₁ := res.2
      let k := gates₁.length
      (k :: stack, (k + 5) :: (k + 6) :: (k + 10) :: zeros,
        gates₁ ++ eqZeroGateBlock k gt nextSlack, nextSlack + 2)
  | .inr (.inr (.inl termWord)) =>
      let ts := (termTokensDecoder.decode termWord).getD []
      let res := compileTermTokens ts gates
      let gt := res.1.headD 0
      let gates₁ := res.2
      let k := gates₁.length
      (k :: stack, (k + 7) :: (k + 10) :: (k + 14) :: (k + 18) :: zeros,
        gates₁ ++ ltZeroGateBlock k gt nextSlack, nextSlack + 4)
  | .inr (.inr (.inr (.inl ()))) =>
      let bp := stack.headD 0
      let k := gates.length
      ((k + 2) :: stack.tail, zeros, gates ++ [.const 1, .neg bp, .add k (k + 1)], nextSlack)
  | .inr (.inr (.inr (.inr (.inl ())))) =>
      let bp := stack.headD 0
      let bq := stack.tail.headD 0
      let k := gates.length
      (k :: stack.tail.tail, zeros, gates ++ [.mul bp bq], nextSlack)
  | .inr (.inr (.inr (.inr (.inr ())))) =>
      let bp := stack.headD 0
      let bq := stack.tail.headD 0
      let k := gates.length
      ((k + 3) :: stack.tail.tail, zeros,
        gates ++ [.add bp bq, .mul bp bq, .neg (k + 1), .add k (k + 2)], nextSlack)

/-- Append sum-of-squares output gates for a list of zero-forced gate indices. -/
@[expose] def sumOfSquaresStep (st : ℕ × List ArithGate) (g : ℕ) : ℕ × List ArithGate :=
  let j := st.2.length
  (j + 1, st.2 ++ [.mul g g, .add st.1 j])

/-- Compile a raw ETR formula word into an `(numInputs, gates, output)` triple. -/
@[expose] def etrWordToRawCircuit (word : List Bool) : ℕ × List ArithGate × ℕ :=
  let toks := formulaWordTokens word
  let st := toks.reverse.foldl compileFormulaTokenStep ([], [], [], word.length)
  let bRoot := st.1.headD 0
  let k := st.2.2.1.length
  let gates₁ := st.2.2.1 ++ [.const 1, .neg k, .add bRoot (k + 1)]
  let allZeros := (k + 2) :: st.2.1
  let initIdx := gates₁.length
  let gates₂ := gates₁ ++ [.const 0]
  let final := allZeros.foldl sumOfSquaresStep (initIdx, gates₂)
  (st.2.2.2, final.2, final.1)

/-! ### Block Evaluation Lemmas for `eqZero`, `ltZero`, `not`, `or`, and `sumOfSquares` -/

/-- Exact evaluation of the 11-gate `eqZeroGateBlock`. -/
theorem eval_eqZeroGateBlock {N : ℕ} (y : Fin N → ℝ) (gs : List ArithGate)
    {gt nextSlack : ℕ} (hgt : gt < gs.length) (hns : nextSlack + 1 < N) :
    let k := gs.length
    let out := evalGatesList y (gs ++ eqZeroGateBlock k gt nextSlack)
    let bv := y ⟨nextSlack, by omega⟩
    let vv := y ⟨nextSlack + 1, hns⟩
    let tv := (evalGatesList y gs).getD gt 0
    out.getD k 0 = bv ∧
    out.getD (k + 5) 0 = bv * (1 - bv) ∧
    out.getD (k + 6) 0 = bv * tv ∧
    out.getD (k + 10) 0 = (1 - bv) * (tv * vv - 1) := by
  set k := gs.length
  set newGs := eqZeroGateBlock k gt nextSlack
  have hgt' : (evalGatesList y (gs ++ newGs)).getD gt 0 = (evalGatesList y gs).getD gt 0 :=
    evalGatesList_append_getD y gs newGs hgt
  have h0 : (evalGatesList y (gs ++ newGs)).getD (k + 0) 0 = y ⟨nextSlack, by omega⟩ :=
    evalGatesList_at_input y gs newGs (by simp [newGs, eqZeroGateBlock]) rfl (by omega)
  have h1 : (evalGatesList y (gs ++ newGs)).getD (k + 1) 0 = y ⟨nextSlack + 1, hns⟩ :=
    evalGatesList_at_input y gs newGs (by simp [newGs, eqZeroGateBlock]) rfl hns
  have h2 : (evalGatesList y (gs ++ newGs)).getD (k + 2) 0 = 1 := by
    simpa using evalGatesList_at_const y gs newGs (idx := 2) (by simp [newGs, eqZeroGateBlock]) rfl
  have h3 := evalGatesList_at_neg y gs newGs (idx := 3) (by simp [newGs, eqZeroGateBlock]) rfl
    (by omega)
  have h4 := evalGatesList_at_add y gs newGs (idx := 4) (by simp [newGs, eqZeroGateBlock]) rfl
    (by omega) (by omega)
  have h5 := evalGatesList_at_mul y gs newGs (idx := 5) (by simp [newGs, eqZeroGateBlock]) rfl
    (by omega) (by omega)
  have h6 := evalGatesList_at_mul y gs newGs (idx := 6) (by simp [newGs, eqZeroGateBlock]) rfl
    (by omega) (by omega)
  have h7 := evalGatesList_at_mul y gs newGs (idx := 7) (by simp [newGs, eqZeroGateBlock]) rfl
    (by omega) (by omega)
  have h8 := evalGatesList_at_neg y gs newGs (idx := 8) (by simp [newGs, eqZeroGateBlock]) rfl
    (by omega)
  have h9 := evalGatesList_at_add y gs newGs (idx := 9) (by simp [newGs, eqZeroGateBlock]) rfl
    (by omega) (by omega)
  have h10 := evalGatesList_at_mul y gs newGs (idx := 10) (by simp [newGs, eqZeroGateBlock]) rfl
    (by omega) (by omega)
  simp only [Nat.add_zero] at h0
  refine ⟨h0, ?_, ?_, ?_⟩
  · rw [h5, h0, h4, h2, h3, h0]; ring
  · rw [h6, h0, hgt']
  · rw [h10, h4, h2, h3, h0, h9, h7, hgt', h1, h8, h2]; ring

/-- Exact evaluation of the 19-gate `ltZeroGateBlock`. -/
theorem eval_ltZeroGateBlock {N : ℕ} (y : Fin N → ℝ) (gs : List ArithGate)
    {gt nextSlack : ℕ} (hgt : gt < gs.length) (hns : nextSlack + 3 < N) :
    let k := gs.length
    let out := evalGatesList y (gs ++ ltZeroGateBlock k gt nextSlack)
    let bv := y ⟨nextSlack, by omega⟩
    let uv := y ⟨nextSlack + 1, by omega⟩
    let vv := y ⟨nextSlack + 2, by omega⟩
    let wv := y ⟨nextSlack + 3, hns⟩
    let tv := (evalGatesList y gs).getD gt 0
    out.getD k 0 = bv ∧
    out.getD (k + 7) 0 = bv * (1 - bv) ∧
    out.getD (k + 10) 0 = bv * (tv + uv * uv) ∧
    out.getD (k + 14) 0 = bv * (uv * vv - 1) ∧
    out.getD (k + 18) 0 = (1 - bv) * (tv - wv * wv) := by
  set k := gs.length
  set newGs := ltZeroGateBlock k gt nextSlack
  have hgt' : (evalGatesList y (gs ++ newGs)).getD gt 0 = (evalGatesList y gs).getD gt 0 :=
    evalGatesList_append_getD y gs newGs hgt
  have h0 : (evalGatesList y (gs ++ newGs)).getD (k + 0) 0 = y ⟨nextSlack, by omega⟩ :=
    evalGatesList_at_input y gs newGs (by simp [newGs, ltZeroGateBlock]) rfl (by omega)
  have h1 : (evalGatesList y (gs ++ newGs)).getD (k + 1) 0 = y ⟨nextSlack + 1, by omega⟩ :=
    evalGatesList_at_input y gs newGs (by simp [newGs, ltZeroGateBlock]) rfl (by omega)
  have h2 : (evalGatesList y (gs ++ newGs)).getD (k + 2) 0 = y ⟨nextSlack + 2, by omega⟩ :=
    evalGatesList_at_input y gs newGs (by simp [newGs, ltZeroGateBlock]) rfl (by omega)
  have h3 : (evalGatesList y (gs ++ newGs)).getD (k + 3) 0 = y ⟨nextSlack + 3, hns⟩ :=
    evalGatesList_at_input y gs newGs (by simp [newGs, ltZeroGateBlock]) rfl hns
  have h4 : (evalGatesList y (gs ++ newGs)).getD (k + 4) 0 = 1 := by
    simpa using evalGatesList_at_const y gs newGs (idx := 4) (by simp [newGs, ltZeroGateBlock]) rfl
  have h5 := evalGatesList_at_neg y gs newGs (idx := 5) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega)
  have h6 := evalGatesList_at_add y gs newGs (idx := 6) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  have h7 := evalGatesList_at_mul y gs newGs (idx := 7) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  have h8 := evalGatesList_at_mul y gs newGs (idx := 8) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  have h9 := evalGatesList_at_add y gs newGs (idx := 9) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  have h10 := evalGatesList_at_mul y gs newGs (idx := 10) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  have h11 := evalGatesList_at_mul y gs newGs (idx := 11) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  have h12 := evalGatesList_at_neg y gs newGs (idx := 12) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega)
  have h13 := evalGatesList_at_add y gs newGs (idx := 13) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  have h14 := evalGatesList_at_mul y gs newGs (idx := 14) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  have h15 := evalGatesList_at_mul y gs newGs (idx := 15) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  have h16 := evalGatesList_at_neg y gs newGs (idx := 16) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega)
  have h17 := evalGatesList_at_add y gs newGs (idx := 17) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  have h18 := evalGatesList_at_mul y gs newGs (idx := 18) (by simp [newGs, ltZeroGateBlock]) rfl
    (by omega) (by omega)
  simp only [Nat.add_zero] at h0
  refine ⟨h0, ?_, ?_, ?_, ?_⟩
  · rw [h7, h0, h6, h4, h5, h0]; ring
  · rw [h10, h0, h9, hgt', h8, h1]
  · rw [h14, h0, h13, h11, h1, h2, h12, h4]; ring
  · rw [h18, h6, h4, h5, h0, h17, hgt', h16, h15, h3]; ring

/-- Exact evaluation of the 3-gate negation Boolean block. -/
theorem eval_notGateBlock {N : ℕ} (y : Fin N → ℝ) (gs : List ArithGate)
    {bp : ℕ} (hbp : bp < gs.length) :
    let k := gs.length
    (evalGatesList y (gs ++ [.const 1, .neg bp, .add k (k + 1)])).getD (k + 2) 0 =
      1 - (evalGatesList y gs).getD bp 0 := by
  set k := gs.length
  set newGs : List ArithGate := [.const 1, .neg bp, .add k (k + 1)]
  have hbp' := evalGatesList_append_getD y gs newGs hbp
  have h0 : (evalGatesList y (gs ++ newGs)).getD (k + 0) 0 = 1 := by
    simpa using evalGatesList_at_const y gs newGs (idx := 0) (by simp [newGs]) rfl
  have h1 := evalGatesList_at_neg y gs newGs (idx := 1) (by simp [newGs]) rfl (by omega)
  have h2 := evalGatesList_at_add y gs newGs (idx := 2) (by simp [newGs]) rfl (by omega) (by omega)
  simp only [Nat.add_zero] at h0
  change (evalGatesList y (gs ++ newGs)).getD (k + 2) 0 = 1 - (evalGatesList y gs).getD bp 0
  rw [h2, h0, h1, hbp']; ring

/-- Exact evaluation of the 4-gate disjunction Boolean block. -/
theorem eval_orGateBlock {N : ℕ} (y : Fin N → ℝ) (gs : List ArithGate)
    {bp bq : ℕ} (hbp : bp < gs.length) (hbq : bq < gs.length) :
    let k := gs.length
    let vp := (evalGatesList y gs).getD bp 0
    let vq := (evalGatesList y gs).getD bq 0
    (evalGatesList y (gs ++ [.add bp bq, .mul bp bq, .neg (k + 1), .add k (k + 2)])).getD
      (k + 3) 0 = vp + vq - vp * vq := by
  set k := gs.length
  set newGs : List ArithGate := [.add bp bq, .mul bp bq, .neg (k + 1), .add k (k + 2)]
  have hbp' := evalGatesList_append_getD y gs newGs hbp
  have hbq' := evalGatesList_append_getD y gs newGs hbq
  have h0 := evalGatesList_at_add y gs newGs (idx := 0) (by simp [newGs]) rfl (by omega) (by omega)
  have h1 := evalGatesList_at_mul y gs newGs (idx := 1) (by simp [newGs]) rfl (by omega) (by omega)
  have h2 := evalGatesList_at_neg y gs newGs (idx := 2) (by simp [newGs]) rfl (by omega)
  have h3 := evalGatesList_at_add y gs newGs (idx := 3) (by simp [newGs]) rfl (by omega) (by omega)
  simp only [Nat.add_zero] at h0
  change (evalGatesList y (gs ++ newGs)).getD (k + 3) 0 =
    (evalGatesList y gs).getD bp 0 + (evalGatesList y gs).getD bq 0 -
      (evalGatesList y gs).getD bp 0 * (evalGatesList y gs).getD bq 0
  rw [h3, h0, h2, h1, hbp', hbq']; ring

/-- Exact zero-forcing semantics of `sumOfSquaresStep` folds. -/
theorem sumOfSquares_eval_zero_iff {n : ℕ} (x : Fin n → ℝ) (zs : List ℕ)
    (acc : ℕ) (gates : List ArithGate) (hacc : acc < gates.length)
    (hzs : ∀ g ∈ zs, g < gates.length) :
    let res := zs.foldl sumOfSquaresStep (acc, gates)
    acc < res.2.length ∧ res.1 < res.2.length ∧ gates <+: res.2 ∧
    (∀ (k : ℕ) (hk : k < res.2.length),
      (∀ (j : ℕ) (hj : j < gates.length), gates[j].WellFormed n j) → res.2[k].WellFormed n k) ∧
    ((evalGatesList x res.2).getD res.1 0 =
      (evalGatesList x gates).getD acc 0 +
        (zs.map fun g ↦ ((evalGatesList x gates).getD g 0) ^ 2).sum) := by
  induction zs generalizing acc gates with
  | nil =>
    refine ⟨hacc, hacc, List.prefix_rfl, fun k hk hwf ↦ hwf k hk, by simp⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg : g < gates.length := hzs g (List.mem_cons_self ..)
    let st₁ := sumOfSquaresStep (acc, gates) g
    have hst1_acc : st₁.1 < st₁.2.length := by simp [st₁, sumOfSquaresStep]
    have hpref1 : gates <+: st₁.2 := by simp [st₁, sumOfSquaresStep]
    have hgs' : ∀ h ∈ gs, h < st₁.2.length := fun h hh ↦
      (hzs h (List.mem_cons_of_mem _ hh)).trans_le hpref1.length_le
    obtain ⟨_, hres_lt, hpref2, hwf2, heval2⟩ := ih st₁.1 st₁.2 hst1_acc hgs'
    have hwf1 : (∀ j (hj : j < gates.length), gates[j].WellFormed n j) →
        ∀ j (hj : j < st₁.2.length), st₁.2[j].WellFormed n j := by
      intro hwf j hj
      simp only [st₁, sumOfSquaresStep] at hj ⊢
      by_cases hlt : j < gates.length
      · rw [List.getElem_append_left hlt]; exact hwf j hlt
      · have hcases : j = gates.length ∨ j = gates.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hj; omega
        rcases hcases with rfl | rfl
        · simp [ArithGate.wellFormed_mul, hg]
        · simp only [List.getElem_append_right (by omega : gates.length ≤ gates.length + 1),
            show gates.length + 1 - gates.length = 1 by omega, List.getElem_cons_succ,
            List.getElem_cons_zero, ArithGate.wellFormed_add]
          exact ⟨hacc.trans (by omega), by omega⟩
    have heval1 : (evalGatesList x st₁.2).getD st₁.1 0 =
        (evalGatesList x gates).getD acc 0 + ((evalGatesList x gates).getD g 0) ^ 2 := by
      have h0 := evalGatesList_at_mul x gates [.mul g g, .add acc gates.length]
        (idx := 0) (by simp) rfl (by omega) (by omega)
      have h1 := evalGatesList_at_add x gates [.mul g g, .add acc gates.length]
        (idx := 1) (by simp) rfl (by omega) (by omega)
      have hacc' := evalGatesList_append_getD x gates [.mul g g, .add acc gates.length] hacc
      have hg' := evalGatesList_append_getD x gates [.mul g g, .add acc gates.length] hg
      simp only [Nat.add_zero] at h0
      dsimp [st₁, sumOfSquaresStep]
      rw [h1, h0, hacc', hg']; ring
    refine ⟨hacc.trans_le (hpref1.trans hpref2).length_le, hres_lt, hpref1.trans hpref2,
      fun k hk hwf ↦ hwf2 k hk (hwf1 hwf), ?_⟩
    rw [heval2, heval1]
    have hmap : gs.map (fun h ↦ ((evalGatesList x st₁.2).getD h 0) ^ 2) =
        gs.map (fun h ↦ ((evalGatesList x gates).getD h 0) ^ 2) := by
      refine List.map_congr_left fun h hh ↦ ?_
      dsimp [st₁, sumOfSquaresStep]
      rw [evalGatesList_append_getD x gates _ (hzs h (List.mem_cons_of_mem _ hh))]
    rw [hmap, List.map_cons, List.sum_cons]; ring

/-- A real sum of squares vanishes iff every term vanishes. -/
theorem sum_sq_eq_zero_iff (l : List ℝ) :
    (l.map fun v ↦ v ^ 2).sum = 0 ↔ ∀ v ∈ l, v = 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      have hrest : 0 ≤ (as.map fun v ↦ v ^ 2).sum :=
        List.sum_nonneg fun y hy ↦ by obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy; exact sq_nonneg v
      exact ⟨sq_eq_zero_iff.mp (by nlinarith [sq_nonneg a]), ih.mp (by linarith [sq_nonneg a])⟩
    · rintro ⟨rfl, h⟩
      rw [ih.mpr h]; norm_num

/-! ### Correctness of `compileFormulaTokenStep` and `etrWordToCircuit` -/

/-- Reduction of `compileFormulaTokenStep` on the `false` token. -/
theorem compileFormulaTokenStep_false {n : ℕ} (st : FormulaCompileState) :
    compileFormulaTokenStep st (FormulaToken.encodeTerms (n := n) (.inl ())) =
      (st.2.2.1.length :: st.1, st.2.1, st.2.2.1 ++ [.const 0], st.2.2.2) := rfl

/-- Reduction of `compileFormulaTokenStep` on an `eqZero` token. -/
theorem compileFormulaTokenStep_eqZero {n : ℕ} (st : FormulaCompileState) (t : Term n) :
    compileFormulaTokenStep st (FormulaToken.encodeTerms (.inr (.inl t))) =
      let resT := compileTermTokens ((termTokensDecoder.decode (encTerm n t)).getD []) st.2.2.1
      let gt := resT.1.headD 0
      let k := resT.2.length
      (k :: st.1, [k + 5, k + 6, k + 10] ++ st.2.1,
        resT.2 ++ eqZeroGateBlock k gt st.2.2.2, st.2.2.2 + 2) := rfl

/-- Reduction of `compileFormulaTokenStep` on an `ltZero` token. -/
theorem compileFormulaTokenStep_ltZero {n : ℕ} (st : FormulaCompileState) (t : Term n) :
    compileFormulaTokenStep st (FormulaToken.encodeTerms (.inr (.inr (.inl t)))) =
      let resT := compileTermTokens ((termTokensDecoder.decode (encTerm n t)).getD []) st.2.2.1
      let gt := resT.1.headD 0
      let k := resT.2.length
      (k :: st.1, [k + 7, k + 10, k + 14, k + 18] ++ st.2.1,
        resT.2 ++ ltZeroGateBlock k gt st.2.2.2, st.2.2.2 + 4) := rfl

/-- Reduction of `compileFormulaTokenStep` on the `not` token. -/
theorem compileFormulaTokenStep_not {n : ℕ} (st : FormulaCompileState) :
    compileFormulaTokenStep st (FormulaToken.encodeTerms (n := n) (.inr (.inr (.inr (.inl ()))))) =
      let bp := st.1.headD 0
      let k := st.2.2.1.length
      ((k + 2) :: st.1.tail, st.2.1,
        st.2.2.1 ++ [.const 1, .neg bp, .add k (k + 1)], st.2.2.2) := rfl

/-- Reduction of `compileFormulaTokenStep` on the `and` token. -/
theorem compileFormulaTokenStep_and {n : ℕ} (st : FormulaCompileState) :
    compileFormulaTokenStep st
        (FormulaToken.encodeTerms (n := n) (.inr (.inr (.inr (.inr (.inl ())))))) =
      let bp := st.1.headD 0
      let bq := st.1.tail.headD 0
      let k := st.2.2.1.length
      (k :: st.1.tail.tail, st.2.1, st.2.2.1 ++ [.mul bp bq], st.2.2.2) := rfl

/-- Reduction of `compileFormulaTokenStep` on the `or` token. -/
theorem compileFormulaTokenStep_or {n : ℕ} (st : FormulaCompileState) :
    compileFormulaTokenStep st
        (FormulaToken.encodeTerms (n := n) (.inr (.inr (.inr (.inr (.inr ())))))) =
      let bp := st.1.headD 0
      let bq := st.1.tail.headD 0
      let k := st.2.2.1.length
      ((k + 3) :: st.1.tail.tail, st.2.1,
        st.2.2.1 ++ [.add bp bq, .mul bp bq, .neg (k + 1), .add k (k + 2)], st.2.2.2) := rfl


/-- Reduction of `compileTermTokenStep` on a constant token. -/
@[simp] theorem compileTermTokenStep_inl (st : List ℕ × List ArithGate) (z : ℤ) :
    compileTermTokenStep st (.inl z) = (st.2.length :: st.1, st.2 ++ [.const (z : ℚ)]) := rfl

/-- Reduction of `compileTermTokenStep` on a variable token. -/
@[simp] theorem compileTermTokenStep_var_raw (st : List ℕ × List ArithGate) (idx : ℕ) :
    compileTermTokenStep st (.inr (.inl idx)) =
      (st.2.length :: st.1, st.2 ++ [.input idx]) := rfl

/-- Reduction of `compileTermTokenStep` on an addition token. -/
@[simp] theorem compileTermTokenStep_add_raw (st : List ℕ × List ArithGate) (u : Unit) :
    compileTermTokenStep st (.inr (.inr (.inl u))) =
      (st.2.length :: st.1.tail.tail, st.2 ++ [.add (st.1.headD 0) (st.1.tail.headD 0)]) := by
  cases u; rfl

/-- Reduction of `compileTermTokenStep` on a multiplication token. -/
@[simp] theorem compileTermTokenStep_mul_raw (st : List ℕ × List ArithGate) (u : Unit) :
    compileTermTokenStep st (.inr (.inr (.inr u))) =
      (st.2.length :: st.1.tail.tail, st.2 ++ [.mul (st.1.headD 0) (st.1.tail.headD 0)]) := by
  cases u; rfl

/-- Characterization of `compileTermTokens` as a right-to-left fold. -/
theorem compileTermTokens_eq_foldl (tokens : List TermToken) (gates : List ArithGate) :
    compileTermTokens tokens gates = tokens.reverse.foldl compileTermTokenStep ([], gates) := rfl

/-- Reduction of `compileFormulaTokenStep` on a raw `false` token. -/
@[simp] theorem compileFormulaTokenStep_inl (st : FormulaCompileState) (u : Unit) :
    compileFormulaTokenStep st (.inl u) =
      (st.2.2.1.length :: st.1, st.2.1, st.2.2.1 ++ [.const 0], st.2.2.2) := by
  cases u; rfl

/-- Reduction of `compileFormulaTokenStep` on a raw `eqZero` token. -/
@[simp] theorem compileFormulaTokenStep_eqZero_raw (st : FormulaCompileState) (tw : List Bool) :
    compileFormulaTokenStep st (.inr (.inl tw)) =
      let res := compileTermTokens ((termTokensDecoder.decode tw).getD []) st.2.2.1
      let k := res.2.length
      (k :: st.1, (k + 5) :: (k + 6) :: (k + 10) :: st.2.1,
        res.2 ++ eqZeroGateBlock k (res.1.headD 0) st.2.2.2, st.2.2.2 + 2) := rfl

/-- Reduction of `compileFormulaTokenStep` on a raw `ltZero` token. -/
@[simp] theorem compileFormulaTokenStep_ltZero_raw (st : FormulaCompileState) (tw : List Bool) :
    compileFormulaTokenStep st (.inr (.inr (.inl tw))) =
      let res := compileTermTokens ((termTokensDecoder.decode tw).getD []) st.2.2.1
      let k := res.2.length
      (k :: st.1, (k + 7) :: (k + 10) :: (k + 14) :: (k + 18) :: st.2.1,
        res.2 ++ ltZeroGateBlock k (res.1.headD 0) st.2.2.2, st.2.2.2 + 4) := rfl

/-- Reduction of `compileFormulaTokenStep` on a raw `not` token. -/
@[simp] theorem compileFormulaTokenStep_not_raw (st : FormulaCompileState) (u : Unit) :
    compileFormulaTokenStep st (.inr (.inr (.inr (.inl u)))) =
      let k := st.2.2.1.length
      ((k + 2) :: st.1.tail, st.2.1,
        st.2.2.1 ++ [.const 1, .neg (st.1.headD 0), .add k (k + 1)], st.2.2.2) := by
  cases u; rfl

/-- Reduction of `compileFormulaTokenStep` on a raw `and` token. -/
@[simp] theorem compileFormulaTokenStep_and_raw (st : FormulaCompileState) (u : Unit) :
    compileFormulaTokenStep st (.inr (.inr (.inr (.inr (.inl u))))) =
      (st.2.2.1.length :: st.1.tail.tail, st.2.1,
        st.2.2.1 ++ [.mul (st.1.headD 0) (st.1.tail.headD 0)], st.2.2.2) := by
  cases u; rfl

/-- Reduction of `compileFormulaTokenStep` on a raw `or` token. -/
@[simp] theorem compileFormulaTokenStep_or_raw (st : FormulaCompileState) (u : Unit) :
    compileFormulaTokenStep st (.inr (.inr (.inr (.inr (.inr u))))) =
      let k := st.2.2.1.length
      ((k + 3) :: st.1.tail.tail, st.2.1,
        st.2.2.1 ++ [.add (st.1.headD 0) (st.1.tail.headD 0),
          .mul (st.1.headD 0) (st.1.tail.headD 0), .neg (k + 1), .add k (k + 2)],
        st.2.2.2) := by
  cases u; rfl

/-- Length of `eqZeroGateBlock`. -/
@[simp] theorem eqZeroGateBlock_length (k gt nextSlack : ℕ) :
    (eqZeroGateBlock k gt nextSlack).length = 11 := rfl

/-- Length of `ltZeroGateBlock`. -/
@[simp] theorem ltZeroGateBlock_length (k gt nextSlack : ℕ) :
    (ltZeroGateBlock k gt nextSlack).length = 19 := rfl

/-- Membership characterization for `eqZeroGateBlock`. -/
theorem mem_eqZeroGateBlock_iff {k gt nextSlack : ℕ} {g : ArithGate} :
    g ∈ eqZeroGateBlock k gt nextSlack ↔
      g = .input nextSlack ∨ g = .input (nextSlack + 1) ∨ g = .const 1 ∨ g = .neg k ∨
      g = .add (k + 2) (k + 3) ∨ g = .mul k (k + 4) ∨ g = .mul k gt ∨ g = .mul gt (k + 1) ∨
      g = .neg (k + 2) ∨ g = .add (k + 7) (k + 8) ∨ g = .mul (k + 4) (k + 9) := by
  simp [eqZeroGateBlock]

/-- Membership characterization for `ltZeroGateBlock`. -/
theorem mem_ltZeroGateBlock_iff {k gt nextSlack : ℕ} {g : ArithGate} :
    g ∈ ltZeroGateBlock k gt nextSlack ↔
      g = .input nextSlack ∨ g = .input (nextSlack + 1) ∨ g = .input (nextSlack + 2) ∨
      g = .input (nextSlack + 3) ∨ g = .const 1 ∨ g = .neg k ∨ g = .add (k + 4) (k + 5) ∨
      g = .mul k (k + 6) ∨ g = .mul (k + 1) (k + 1) ∨ g = .add gt (k + 8) ∨
      g = .mul k (k + 9) ∨ g = .mul (k + 1) (k + 2) ∨ g = .neg (k + 4) ∨
      g = .add (k + 11) (k + 12) ∨ g = .mul k (k + 13) ∨ g = .mul (k + 3) (k + 3) ∨
      g = .neg (k + 15) ∨ g = .add gt (k + 16) ∨ g = .mul (k + 6) (k + 17) := by
  simp [ltZeroGateBlock]

/-- First projection of `sumOfSquaresStep`. -/
@[simp] theorem sumOfSquaresStep_fst (st : ℕ × List ArithGate) (g : ℕ) :
    (sumOfSquaresStep st g).1 = st.2.length + 1 := rfl

/-- Second projection of `sumOfSquaresStep`. -/
@[simp] theorem sumOfSquaresStep_snd (st : ℕ × List ArithGate) (g : ℕ) :
    (sumOfSquaresStep st g).2 = st.2 ++ [.mul g g, .add st.1 st.2.length] := rfl

/-- Formula for `encArithGateUnary` on an input gate. -/
theorem encArithGateUnary_length_input (i : ℕ) :
    (encArithGateUnary (.input i)).length = i + 1 := by
  simp [encArithGateUnary]

/-- Formula for `encArithGateUnary` on a constant gate. -/
theorem encArithGateUnary_length_const (c : ℚ) :
    (encArithGateUnary (.const c)).length = (encRat c).length + 2 := by
  simp [encArithGateUnary]

/-- Well-formedness of every gate in `eqZeroGateBlock`. -/
theorem eqZeroGateBlock_wellFormed {k gt nextSlack : ℕ} (hgt : gt < k) :
    ∀ idx (hidx : idx < 11),
      (eqZeroGateBlock k gt nextSlack)[idx].WellFormed (nextSlack + 2) (k + idx) := by
  intro idx hidx
  interval_cases idx <;>
    simp [eqZeroGateBlock, ArithGate.wellFormed_add, ArithGate.wellFormed_mul] <;> omega

/-- Well-formedness of every gate in `ltZeroGateBlock`. -/
theorem ltZeroGateBlock_wellFormed {k gt nextSlack : ℕ} (hgt : gt < k) :
    ∀ idx (hidx : idx < 19),
      (ltZeroGateBlock k gt nextSlack)[idx].WellFormed (nextSlack + 4) (k + idx) := by
  intro idx hidx
  interval_cases idx <;>
    simp [ltZeroGateBlock, ArithGate.wellFormed_add, ArithGate.wellFormed_mul] <;> omega

/-- Unfolded formula for `etrWordToRawCircuit`. -/
theorem etrWordToRawCircuit_eq (word : List Bool) :
    etrWordToRawCircuit word =
      let toks := formulaWordTokens word
      let st := toks.reverse.foldl compileFormulaTokenStep ([], [], [], word.length)
      let bRoot := st.1.headD 0
      let k := st.2.2.1.length
      let gates₁ := st.2.2.1 ++ [.const 1, .neg k, .add bRoot (k + 1)]
      let allZeros := (k + 2) :: st.2.1
      let initIdx := gates₁.length
      let gates₂ := gates₁ ++ [.const 0]
      let final := allZeros.foldl sumOfSquaresStep (initIdx, gates₂)
      (st.2.2.2, final.2, final.1) := rfl

end Cslib.Complexity
