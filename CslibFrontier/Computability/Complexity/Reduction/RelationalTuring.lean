/-
Copyright (c) 2026 FormalPapers / CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers / CslibFrontier contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.CountingTuring
public import CslibFrontier.Computability.Complexity.Reduction.Turing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
import CslibFrontier.Computability.Complexity.Reduction.BoundedOracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution

/-!
# Polynomial-Time Multi-Bit Turing Reducibility Across Decision, Counting, and Search Problems

This module develops polynomial-time Turing reducibility
(`CslibFrontier.Complexity.PolyTimeOracleReducible`) and equivalence
(`CslibFrontier.Complexity.PolyTimeOracleEquiv`) for general computational problems modeled as
input-output relations `P : α → γ → Prop` (uniformly covering decision languages, counting
functions, and multi-solution search problems), certified on multi-tape oracle Turing machines via
`Cslib.Probability.IsOraclePPTOn` under standard Lean axioms.

## Main definitions

* `CslibFrontier.Complexity.DecisionProblem`, `CslibFrontier.Complexity.FunctionProblem`: relational
  embeddings of decision languages and total functions.
* `CslibFrontier.Complexity.IsPolyBoundedSolver`, `CslibFrontier.Complexity.solverWordOracle`:
  polynomially length-bounded solvers and their induced multi-bit word oracles.
* `CslibFrontier.Complexity.PolyTimeOracleReducible`,
  `CslibFrontier.Complexity.PolyTimeOracleEquiv`: polynomial-time Turing reducibility and
  equivalence between relational computational problems.
* `CslibFrontier.Complexity.queryWordBatchStep`, `CslibFrontier.Complexity.queryWordBatch`: batch
  multi-bit oracle query combinators.

## Main results

* `CslibFrontier.Complexity.PolyTimeOracleReducible.refl`,
  `CslibFrontier.Complexity.PolyTimeOracleReducible.trans`,
  `CslibFrontier.Complexity.PolyTimeOracleReducible.ofPolyTime`,
  `CslibFrontier.Complexity.PolyTimeOracleReducible.ofBatchQueries`: preorder and reduction
  constructors.
* `CslibFrontier.Complexity.polyTimeOracleReducible_decisionProblem_iff`: exact equivalence with
  `Cslib.Complexity.PolyTimeTuringReducible`.
* `CslibFrontier.Complexity.polyTimeOracleReducible_functionProblem_iff_countingTuringReducible`:
  exact equivalence with `Cslib.Complexity.CountingTuringReducible`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-- Relational representation of a decision problem `L : Set α`: `b : Bool` is a valid answer on
`a : α` iff `(b = true ↔ a ∈ L)`. -/
@[expose]
def DecisionProblem {α : Type} (L : Set α) (a : α) (b : Bool) : Prop :=
  b = true ↔ a ∈ L

/-- Relational representation of a total function / counting problem `f : α → γ`: `c : γ` is a valid
answer on `a : α` iff `c = f a`. -/
@[expose]
def FunctionProblem {α γ : Type} (f : α → γ) (a : α) (c : γ) : Prop :=
  c = f a

/-- Predicate asserting that `sol : β → δ` solves `P : β → δ → Prop` on every input with
polynomially bounded encoded output length. -/
@[expose]
def IsPolyBoundedSolver {β δ : Type} (encB : β ↪ List Bool) (encD : δ ↪ List Bool)
    (P : β → δ → Prop) (sol : β → δ) : Prop :=
  (∀ b, P b (sol b)) ∧ PolyBounded (fun b ↦ (encB b).length) (fun b ↦ (encD (sol b)).length)

/-- Word-level oracle induced by a typed solver `sol : β → δ` with total input decoder `D_B` and
output encoding `encD`. -/
def solverWordOracle {β δ : Type} {encB : β ↪ List Bool} (D_B : Decoder encB)
    (encD : δ ↪ List Bool) (sol : β → δ) (w : List Bool) : List Bool :=
  let b := D_B.decode w
  if encB b == w then encD (sol b) else []

/-- Evaluating `solverWordOracle D_B encD sol` on `encB b` returns `encD (sol b)`. -/
@[simp]
theorem solverWordOracle_enc {β δ : Type} {encB : β ↪ List Bool} (D_B : Decoder encB)
    (encD : δ ↪ List Bool) (sol : β → δ) (b : β) :
    solverWordOracle D_B encD sol (encB b) = encD (sol b) := by
  unfold solverWordOracle
  simp [D_B.decode_enc b]

private lemma poly_eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) :
    p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

private lemma length_le_encList_of_mem {α : Type} (encA : α ↪ List Bool) {l : List α} {x : α}
    (hx : x ∈ l) : (encA x).length ≤ (encList encA l).length := by
  induction l with
  | nil => cases hx
  | cons a as ih =>
    simp only [encList_cons, List.length_append, length_frame]
    rcases List.mem_cons.mp hx with rfl | hmem
    · omega
    · have h1 := ih hmem; omega

/-- Polynomial-time Turing reducibility between relational computational problems `P₁` and `P₂`. -/
def PolyTimeOracleReducible {α β γ δ : Type}
    (encA : α ↪ List Bool) (encC : γ ↪ List Bool)
    (encB : β ↪ List Bool) (D_B : Decoder encB) (encD : δ ↪ List Bool)
    (P₁ : α → γ → Prop) (P₂ : β → δ → Prop) : Prop :=
  ∀ p : Polynomial ℕ, ∃ prog : α → WordQueryComp Unit γ,
    IsOraclePPTOn encA encC
      (fun a ↦ OracleComp.interpret ProbOracleComp.query (prog a)) ∧
    ∀ sol : β → δ,
      (∀ b, P₂ b (sol b)) →
      (∀ b, (encD (sol b)).length ≤ p.eval (encB b).length) →
      ∀ a, P₁ a (OracleComp.interpret (m := Id)
        (fun q ↦ solverWordOracle D_B encD sol q.2) (prog a))

/-- Polynomial-time Turing equivalence between relational computational problems `P₁` and `P₂`. -/
@[expose]
def PolyTimeOracleEquiv {α β γ δ : Type}
    (encA : α ↪ List Bool) (D_A : Decoder encA) (encC : γ ↪ List Bool)
    (encB : β ↪ List Bool) (D_B : Decoder encB) (encD : δ ↪ List Bool)
    (P₁ : α → γ → Prop) (P₂ : β → δ → Prop) : Prop :=
  PolyTimeOracleReducible encA encC encB D_B encD P₁ P₂ ∧
    PolyTimeOracleReducible encB encD encA D_A encC P₂ P₁

/-- Reflexivity of `PolyTimeOracleReducible`. -/
theorem PolyTimeOracleReducible.refl {α γ : Type}
    (encA : α ↪ List Bool) (D_A : Decoder encA) (encC : γ ↪ List Bool) (D_C : Decoder encC)
    (P : α → γ → Prop) :
    PolyTimeOracleReducible encA encC encA D_A encC P P := by
  intro p
  let limit : α → ℕ := fun a ↦ p.eval (encA a).length
  have hreq : ComputableInPolyTime (fun a : α ↦ encA a) encA encBits :=
    id'.of_enc_eq fun _ ↦ rfl
  have hlim : ComputableInPolyTime limit encA encUnary :=
    (unary_eval p).comp (encoding_length encA)
  refine ⟨fun a ↦ D_C.decode <$> (List.take (limit a) <$> OracleComp.query ((), encA a)),
    ?_, fun sol hsol hlen a ↦ ?_⟩
  · simpa only [OracleComp.interpret_map, OracleComp.interpret_query] using
      (IsOraclePPTOn.query_take () hreq hlim).map D_C.computableInPolyTime
  · simp only [OracleComp.interpret_map]
    change P a (D_C.decode ((solverWordOracle D_A encC sol (encA a)).take (limit a)))
    rw [solverWordOracle_enc, List.take_of_length_le (hlen a), D_C.decode_enc]
    exact hsol a

/-- Any problem solvable directly in polynomial time reduces in `0` oracle queries to any `P₂`. -/
theorem PolyTimeOracleReducible.ofPolyTime {α β γ δ : Type}
    {encA : α ↪ List Bool} {encC : γ ↪ List Bool}
    (encB : β ↪ List Bool) (D_B : Decoder encB) (encD : δ ↪ List Bool)
    {P₁ : α → γ → Prop} (P₂ : β → δ → Prop)
    {f : α → γ} (hf : ComputableInPolyTime f encA encC) (hspec : ∀ a, P₁ a (f a)) :
    PolyTimeOracleReducible encA encC encB D_B encD P₁ P₂ :=
  fun _ ↦ ⟨fun a ↦ pure (f a), hf.isOraclePPTOn, fun _ _ _ a ↦ hspec a⟩

private lemma runWith_interpret_query_deterministic {β : Type}
    (ans : Unit × List Bool → List Bool) (prog : WordQueryComp Unit β) :
    ProbOracleComp.runWith (fun q (s : Unit) ↦ PMF.pure (ans q, s))
      (OracleComp.interpret ProbOracleComp.query prog) () =
    PMF.pure (OracleComp.interpret (m := Id) ans prog, ()) := by
  rw [ProbOracleComp.runWith_eq_run_interpret, OracleComp.interpret_interpret]
  simp only [ProbOracleComp.interpret_query]
  have hstate : ∀ (s : Unit),
      (OracleComp.interpret (m := StateT Unit PMF)
        (fun q (s : Unit) ↦ PMF.pure (ans q, s)) prog).run s =
      PMF.pure ((OracleComp.interpret (m := StateM Unit)
        (fun q ↦ ((fun s ↦ (ans q, s)) : StateM Unit _)) prog).run s) := by
    intro s
    induction prog using PFunctor.FreeM.induction generalizing s with
    | pure _ => rfl
    | lift_bind q cont ih =>
      rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
        OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, OracleComp.interpret_bind, OracleComp.interpret_query,
        StateT.run_bind]
      exact (PMF.pure_bind _ _).trans (ih _ _)
  rw [hstate ()]
  exact congrArg PMF.pure (OracleComp.run_interpret_stateless (m := Id) ans prog ())

private lemma interpret_length_le_of_isOraclePPTOn {β δ : Type}
    {encB : β ↪ List Bool} {encD : δ ↪ List Bool}
    {prog : β → WordQueryComp Unit δ}
    (hPPT : IsOraclePPTOn encB encD (fun b ↦ OracleComp.interpret ProbOracleComp.query (prog b))) :
    ∃ p : Polynomial ℕ, ∀ (ans : Unit × List Bool → List Bool) (b : β),
      (encD (OracleComp.interpret (m := Id) ans (prog b))).length ≤ p.eval (encB b).length := by
  obtain ⟨c, d, hbd⟩ := hPPT.length_le
  refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun ans b ↦ ?_⟩
  have hsupp : (OracleComp.interpret (m := Id) ans (prog b), ()) ∈
      (ProbOracleComp.runWith (fun q (s : Unit) ↦ PMF.pure (ans q, s))
        (OracleComp.interpret ProbOracleComp.query (prog b)) ()).support := by
    rw [runWith_interpret_query_deterministic]
    simp
  have hle := hbd b Unit (fun q s ↦ PMF.pure (ans q, s)) () () _ hsupp
  simpa using hle

private lemma interpret_subst_eq {γ : Type}
    (ans₁ ans₂ : Unit × List Bool → List Bool)
    (G : Unit × List Bool → WordQueryComp Unit (List Bool))
    (prog : WordQueryComp Unit γ)
    (hG : ∀ q, OracleComp.interpret (m := Id) ans₂ (G q) = ans₁ q) :
    OracleComp.interpret (m := Id) ans₂ (OracleComp.interpret G prog) =
      OracleComp.interpret (m := Id) ans₁ prog := by
  induction prog using PFunctor.FreeM.induction with
  | pure _ => rfl
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      OracleComp.interpret_bind, OracleComp.interpret_query,
      OracleComp.interpret_bind, OracleComp.interpret_bind,
      OracleComp.interpret_query, hG q]
    exact ih (ans₁ q)

/-- Transitivity of `PolyTimeOracleReducible`. -/
theorem PolyTimeOracleReducible.trans {α β ε γ δ ζ : Type}
    {encA : α ↪ List Bool} {encC : γ ↪ List Bool}
    {encB : β ↪ List Bool} {D_B : Decoder encB} {encD : δ ↪ List Bool}
    {encE : ε ↪ List Bool} {D_E : Decoder encE} {encF : ζ ↪ List Bool}
    {P₁ : α → γ → Prop} {P₂ : β → δ → Prop} {P₃ : ε → ζ → Prop}
    (h₁₂ : PolyTimeOracleReducible encA encC encB D_B encD P₁ P₂)
    (h₂₃ : PolyTimeOracleReducible encB encD encE D_E encF P₂ P₃) :
    PolyTimeOracleReducible encA encC encE D_E encF P₁ P₃ := by
  intro p₃
  obtain ⟨prog₂, hPPT₂, hspec₂⟩ := h₂₃ p₃
  obtain ⟨p₂, hp₂_le⟩ := interpret_length_le_of_isOraclePPTOn hPPT₂
  obtain ⟨prog₁, hPPT₁, hspec₁⟩ := h₁₂ p₂
  let G : Unit × List Bool → WordQueryComp Unit (List Bool) := fun q ↦
    let b := D_B.decode q.2
    if encB b == q.2 then
      List.take (p₂.eval q.2.length) <$> (encD <$> prog₂ b)
    else
      pure []
  refine ⟨fun a ↦ OracleComp.interpret G (prog₁ a), ?_, fun sol₃ hsol₃ hlen₃ a ↦ ?_⟩
  · let EIn := encPair encA (encPair (encFinEnum Unit) encBits)
    have hq2 : ComputableInPolyTime (fun p : α × (Unit × List Bool) ↦ p.2.2) EIn encBits :=
      (snd _ _).comp (snd _ _)
    have hb_pt : ComputableInPolyTime (fun p : α × (Unit × List Bool) ↦ D_B.decode p.2.2)
        EIn encB :=
      D_B.computableInPolyTime.comp hq2
    have hcond_pt : ComputableInPolyTime
        (fun p : α × (Unit × List Bool) ↦ encB (D_B.decode p.2.2) == p.2.2) EIn encBool :=
      (encoding_comp hb_pt).beq hq2
    have hcap_pt : ComputableInPolyTime
        (fun p : α × (Unit × List Bool) ↦ p₂.eval p.2.2.length) EIn encUnary :=
      (unary_eval p₂).comp (length_bits.comp hq2)
    have hyes : IsOraclePPTOn EIn encBits (fun p : α × (Unit × List Bool) ↦
        OracleComp.interpret ProbOracleComp.query
          (List.take (p₂.eval p.2.2.length) <$> (encD <$> prog₂ (D_B.decode p.2.2)))) := by
      have h1 := (hPPT₂.preprocess hb_pt).map (encoding_comp id')
      have htake : ComputableInPolyTime
          (fun pr : (α × (Unit × List Bool)) × List Bool ↦ pr.2.take (p₂.eval pr.1.2.2.length))
          (encPair EIn encBits) encBits :=
        bitsTakeWithInput (snd _ _) (hcap_pt.comp (fst _ _))
      simpa only [OracleComp.interpret_map, Functor.map_map] using h1.map_with htake
    have hG_ppt : IsOraclePPTOn EIn encBits (fun p : α × (Unit × List Bool) ↦
        OracleComp.interpret ProbOracleComp.query (G p.2)) := by
      refine (IsOraclePPTOn.cond hcond_pt hyes ((const []).isOraclePPTOn)).congr ?_
      intro p State oracle s
      dsimp only [G]
      by_cases hc : (encB (D_B.decode p.2.2) == p.2.2) = true <;> simp [hc]
    have hres_pt : ComputableInPolyTime (fun pair : α × List Bool ↦ p₂.eval pair.2.length)
        (encPair encA encBits) encUnary :=
      (unary_eval p₂).comp (length_bits.comp (snd _ _))
    simpa only [id_eq, OracleComp.interpret_interpret, ProbOracleComp.interpret_query] using
      hPPT₁.interpret_preprocess_open'
        (operationEncoding := encFinEnum Unit)
        (handler := fun _ q ↦ OracleComp.interpret ProbOracleComp.query (G q))
        (prepare := id) (resources := fun _ w ↦ p₂.eval w.length)
        id' hG_ppt hres_pt fun _ q reply hreply ↦ by
          dsimp only [G] at hreply
          split_ifs at hreply with hc
          · rw [OracleComp.interpret_map] at hreply
            obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
            exact List.length_take_le _ _
          · rw [OracleComp.interpret_pure] at hreply
            rw [OracleComp.eq_of_mem_supportWith_pure hreply]
            simp
  · let ans₃ : Unit × List Bool → List Bool := fun q' ↦ solverWordOracle D_E encF sol₃ q'.2
    let sol₂ : β → δ := fun b ↦ OracleComp.interpret (m := Id) ans₃ (prog₂ b)
    have hsol₂ : ∀ b, P₂ b (sol₂ b) := hspec₂ sol₃ hsol₃ hlen₃
    have hlen₂ : ∀ b, (encD (sol₂ b)).length ≤ p₂.eval (encB b).length := hp₂_le ans₃
    have hG_eval : ∀ q, OracleComp.interpret (m := Id) ans₃ (G q) =
        solverWordOracle D_B encD sol₂ q.2 := by
      intro q
      dsimp only [G, solverWordOracle]
      split_ifs with hc
      · rw [OracleComp.interpret_map, OracleComp.interpret_map]
        change (encD (sol₂ (D_B.decode q.2))).take (p₂.eval q.2.length) =
          encD (sol₂ (D_B.decode q.2))
        have heq_w : encB (D_B.decode q.2) = q.2 := beq_iff_eq.mp hc
        have hle := hlen₂ (D_B.decode q.2)
        rw [heq_w] at hle
        exact List.take_of_length_le hle
      · rfl
    rw [interpret_subst_eq _ ans₃ G (prog₁ a) hG_eval]
    exact hspec₁ sol₂ hsol₂ hlen₂ a

/-- One step of `queryWordBatch`. -/
def queryWordBatchStep (cap : ℕ) (s : List (List Bool) × List (List Bool)) :
    WordQueryComp Unit (List (List Bool) × List (List Bool)) :=
  if s.1.isEmpty then
    pure s
  else
    (fun reply ↦ (s.1.tail, s.2 ++ [reply])) <$>
      (List.take cap <$> OracleComp.query ((), s.1.headD []))

/-- Ask the oracle every word in `words` with unary reply-length cap `cap`. -/
def queryWordBatch (cap : ℕ) (words : List (List Bool)) :
    WordQueryComp Unit (List (List Bool)) :=
  Prod.snd <$> OracleComp.iterate words.length (queryWordBatchStep cap) (words, [])

private lemma interpret_queryWordBatchStep (cap : ℕ) (s : List (List Bool) × List (List Bool)) :
    OracleComp.interpret ProbOracleComp.query (queryWordBatchStep cap s) =
      if s.1.isEmpty then
        pure s
      else
        (fun reply ↦ (s.1.tail, s.2 ++ [reply])) <$>
          (List.take cap <$> ProbOracleComp.query
            (spec := fun _ : Unit × List Bool ↦ List Bool) ((), s.1.headD [])) := by
  unfold queryWordBatchStep
  split <;> simp [OracleComp.interpret_map, OracleComp.interpret_query]

/-- `queryWordBatch` is strict oracle PPT in `(cap, words)`. -/
theorem isOraclePPTOn_queryWordBatch :
    IsOraclePPTOn (encPair encUnary (encList encBits)) (encList encBits)
      (fun p : ℕ × List (List Bool) ↦
        OracleComp.interpret ProbOracleComp.query (queryWordBatch p.1 p.2)) := by
  simp only [queryWordBatch, OracleComp.interpret_map, OracleComp.interpret_iterate]
  have hcount : ComputableInPolyTime (fun p : ℕ × List (List Bool) ↦ p.2.length)
      (encPair encUnary (encList encBits)) encUnary :=
    (length_list encBits).comp (snd _ _)
  have hinit : ComputableInPolyTime
      (fun p : ℕ × List (List Bool) ↦ (p.2, ([] : List (List Bool))))
      (encPair encUnary (encList encBits))
      (encPair (encList encBits) (encList encBits)) :=
    (snd _ _).prod (const [])
  have hstep : IsOraclePPTOn
      (encPair (encPair encUnary (encList encBits))
        (encPair (encList encBits) (encList encBits)))
      (encPair (encList encBits) (encList encBits))
      (fun q ↦ OracleComp.interpret ProbOracleComp.query (queryWordBatchStep q.1.1 q.2)) := by
    simp only [interpret_queryWordBatchStep]
    have hSt := snd (encPair encUnary (encList encBits))
      (encPair (encList encBits) (encList encBits))
    have hCap := (fst (encPair encUnary (encList encBits))
      (encPair (encList encBits) (encList encBits))).fst'
    refine IsOraclePPTOn.cond ((listIsEmpty' encBits).comp hSt.fst') (hSt.isOraclePPTOn) ?_
    have hq := IsOraclePPTOn.query_take ()
      ((headD ([] : List Bool)).comp hSt.fst') hCap
    exact hq.map_with
      (((listTail encBits).comp (hSt.comp (fst _ _)).fst').prod
        ((snoc encBits).comp (((hSt.comp (fst _ _)).snd').prod (snd _ _))))
  refine (IsOraclePPTOn.iterateWith_of_bounded_growth hcount hinit hstep
    (growth := fun p ↦ 2 * p.1 + 2)
    (by
      have h1 : PolyBounded (fun p : ℕ × List (List Bool) ↦
          (encPair encUnary (encList encBits) p).length) (fun p ↦ p.1) :=
        (fst encUnary (encList encBits)).polyBounded
      exact ((PolyBounded.const 2).mul h1).add (.const 2))
    (fun p state next hnext ↦ ?_)).map (snd _ _)
  rw [interpret_queryWordBatchStep] at hnext
  rcases state with ⟨rem, acc⟩
  cases rem with
  | nil =>
    rw [OracleComp.eq_of_mem_supportWith_pure hnext]
    simp
  | cons w ws =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at hnext
    obtain ⟨reply, hrep, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hrep
    have htake_le : (raw.take p.1).length ≤ p.1 := List.length_take_le _ _
    simp only [List.tail_cons, length_encPair, encList_cons, encList_append, encList_nil,
      List.append_nil, List.length_append, length_frame, encBits_apply]
    omega

/-- Evaluating `queryWordBatch cap words` against `ans`. -/
theorem interpret_queryWordBatch (ans : Unit × List Bool → List Bool) (cap : ℕ)
    (words : List (List Bool)) :
    OracleComp.interpret (m := Id) ans (queryWordBatch cap words) =
      words.map fun w ↦ (ans ((), w)).take cap := by
  have key : ∀ (ws : List (List Bool)) (acc : List (List Bool)),
      OracleComp.interpret (m := Id) ans
        (OracleComp.iterate ws.length (queryWordBatchStep cap) (ws, acc)) =
      ([], acc ++ ws.map fun w ↦ (ans ((), w)).take cap) := by
    intro ws
    induction ws with
    | nil =>
      intro acc
      simp only [List.length_nil, List.map_nil, List.append_nil]
      rfl
    | cons w ws ih =>
      intro acc
      rw [List.length_cons, OracleComp.iterate_succ_bind, OracleComp.interpret_bind]
      have hstep : OracleComp.interpret (m := Id) ans (queryWordBatchStep cap (w :: ws, acc)) =
          (ws, acc ++ [(ans ((), w)).take cap]) := by
        unfold queryWordBatchStep
        rfl
      change OracleComp.interpret (m := Id) ans
        (OracleComp.iterate ws.length (queryWordBatchStep cap)
          (OracleComp.interpret (m := Id) ans (queryWordBatchStep cap (w :: ws, acc)))) = _
      rw [hstep, ih, List.append_assoc, List.singleton_append, List.map_cons]
  rw [queryWordBatch, OracleComp.interpret_map, key, List.nil_append]
  rfl

/-- Universal batch-query constructor for `PolyTimeOracleReducible`. -/
theorem PolyTimeOracleReducible.ofBatchQueries {α β γ δ : Type}
    {encA : α ↪ List Bool} {encC : γ ↪ List Bool}
    {encB : β ↪ List Bool} (D_B : Decoder encB)
    {encD : δ ↪ List Bool} (D_D : Decoder encD)
    {P₁ : α → γ → Prop} {P₂ : β → δ → Prop}
    (queries : α → List β) (combine : α × List δ → γ)
    (hqueries : ComputableInPolyTime queries encA (encList encB))
    (hcombine : ComputableInPolyTime combine (encPair encA (encList encD)) encC)
    (hspec : ∀ (a : α) (ans : List δ),
      ans.length = (queries a).length →
      (∀ i (hi : i < (queries a).length) (hia : i < ans.length),
        P₂ ((queries a)[i]'hi) (ans[i]'hia)) →
      P₁ a (combine (a, ans))) :
    PolyTimeOracleReducible encA encC encB D_B encD P₁ P₂ := by
  intro p
  let cap : α → ℕ := fun a ↦ p.eval (encList encB (queries a)).length
  let words : α → List (List Bool) := fun a ↦ (queries a).map encB
  have hcap : ComputableInPolyTime cap encA encUnary :=
    (unary_eval p).comp (length_bits.comp (encoding_comp hqueries))
  have hwords : ComputableInPolyTime words encA (encList encBits) := by
    refine mapWithInput hqueries ?_
    exact encoding_comp (snd _ _)
  have hpost : ComputableInPolyTime
      (fun pr : α × List (List Bool) ↦ combine (pr.1, pr.2.map D_D.decode))
      (encPair encA (encList encBits)) encC :=
    hcombine.comp ((fst _ _).prod ((ComputableInPolyTime.map D_D.computableInPolyTime).comp
      (snd _ _)))
  refine ⟨fun a ↦ (fun replies ↦ combine (a, replies.map D_D.decode)) <$>
      queryWordBatch (cap a) (words a), ?_, fun sol hsol hlen a ↦ ?_⟩
  · simpa only [OracleComp.interpret_map] using
      (isOraclePPTOn_queryWordBatch.preprocess (hcap.prod hwords)).map_with hpost
  · rw [OracleComp.interpret_map, interpret_queryWordBatch]
    change P₁ a (combine (a, ((words a).map fun w ↦
      (solverWordOracle D_B encD sol w).take (cap a)).map D_D.decode))
    have hmap_eq : (((words a).map fun w ↦
        (solverWordOracle D_B encD sol w).take (cap a)).map D_D.decode) =
        (queries a).map sol := by
      dsimp only [words]
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro b hb
      dsimp only [Function.comp_apply]
      have hb_len : (encB b).length ≤ (encList encB (queries a)).length :=
        length_le_encList_of_mem encB hb
      have hcap_le : (encD (sol b)).length ≤ cap a :=
        (hlen b).trans (poly_eval_mono p hb_len)
      rw [solverWordOracle_enc, List.take_of_length_le hcap_le, D_D.decode_enc]
    rw [hmap_eq]
    refine hspec a ((queries a).map sol) (List.length_map _) fun i hi hia ↦ ?_
    rw [List.getElem_map]
    exact hsol _

/-- Exact equivalence between `PolyTimeOracleReducible` on `DecisionProblem`s and
`Cslib.Complexity.PolyTimeTuringReducible`. -/
theorem polyTimeOracleReducible_decisionProblem_iff {α β : Type}
    (encA : α ↪ List Bool) (encB : β ↪ List Bool) (D_B : Decoder encB)
    (L₁ : Set α) (L₂ : Set β) :
    PolyTimeOracleReducible encA encBool encB D_B encBool
      (DecisionProblem L₁) (DecisionProblem L₂) ↔
    PolyTimeTuringReducible encA encB L₁ L₂ := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨prog, hPPT, hspec⟩ := h 1
    let sol : β → Bool := fun b ↦ decide (b ∈ L₂)
    have hsol : ∀ b, DecisionProblem L₂ b (sol b) := fun _ ↦ decide_eq_true_iff
    have hlen : ∀ b, (encBool (sol b)).length ≤ (1 : Polynomial ℕ).eval (encB b).length :=
      fun _ ↦ by simp
    let G : Unit × List Bool → WordQueryComp Unit (List Bool) := fun q ↦
      let b := D_B.decode q.2
      if encB b == q.2 then
        List.take 1 <$> OracleComp.query ((), q.2)
      else
        pure []
    have hG_ppt : IsOraclePPTOn (encPair encA (encPair (encFinEnum Unit) encBits)) encBits
        (fun p : α × (Unit × List Bool) ↦
          OracleComp.interpret ProbOracleComp.query (G p.2)) := by
      let EIn := encPair encA (encPair (encFinEnum Unit) encBits)
      have hq2 : ComputableInPolyTime (fun p : α × (Unit × List Bool) ↦ p.2.2) EIn encBits :=
        (snd _ _).comp (snd _ _)
      have hcond : ComputableInPolyTime
          (fun p : α × (Unit × List Bool) ↦ encB (D_B.decode p.2.2) == p.2.2) EIn encBool :=
        (encoding_comp (D_B.computableInPolyTime.comp hq2)).beq hq2
      refine (IsOraclePPTOn.cond hcond
        (by
          simpa only [OracleComp.interpret_map, OracleComp.interpret_query] using
            IsOraclePPTOn.query_take () hq2 (const 1))
        ((const []).isOraclePPTOn)).congr ?_
      intro p State oracle s
      dsimp only [G]
      split_ifs with hc
      · rfl
      · simp only [OracleComp.interpret_pure]
    have hsub_ppt : IsOraclePPTOn encA encBool (fun a ↦
        OracleComp.interpret ProbOracleComp.query (OracleComp.interpret G (prog a))) := by
      simpa only [id_eq, OracleComp.interpret_interpret, ProbOracleComp.interpret_query] using
        hPPT.interpret_preprocess_open'
          (operationEncoding := encFinEnum Unit)
          (handler := fun _ q ↦ OracleComp.interpret ProbOracleComp.query (G q))
          (prepare := id) (resources := fun _ _ ↦ 1)
          id' hG_ppt (const 1) fun _ q reply hreply ↦ by
            dsimp only [G] at hreply
            split_ifs at hreply with hc
            · rw [OracleComp.interpret_map] at hreply
              obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
              exact List.length_take_le _ _
            · rw [OracleComp.interpret_pure] at hreply
              rw [OracleComp.eq_of_mem_supportWith_pure hreply]
              simp
    have hG_eval : ∀ q, OracleComp.interpret (m := Id) (languageOracle (encB '' L₂)) (G q) =
        solverWordOracle D_B encBool sol q.2 := by
      intro q
      dsimp only [G, solverWordOracle, sol]
      split_ifs with hc
      · rw [OracleComp.interpret_map, OracleComp.interpret_query]
        have heq_w : encB (D_B.decode q.2) = q.2 := beq_iff_eq.mp hc
        change (languageOracle (encB '' L₂) ((), q.2)).take 1 =
          encBool (decide (D_B.decode q.2 ∈ L₂))
        rw [languageOracle_apply, ← heq_w]
        simp [D_B.decode_enc, encB.injective.mem_set_image]
      · rfl
    refine ⟨fun a ↦ OracleComp.interpret (m := Id)
        (fun q ↦ solverWordOracle D_B encBool sol q.2) (prog a),
      ⟨fun a ↦ OracleComp.interpret G (prog a), hsub_ppt, fun a ↦
        interpret_subst_eq _ _ G (prog a) hG_eval⟩,
      fun a ↦ (hspec sol hsol hlen a).symm⟩
  · intro p
    obtain ⟨f, ⟨prog, hPPT, hf_eq⟩, hL₁⟩ := h
    let G : Unit × List Bool → WordQueryComp Unit (List Bool) := fun q ↦
      let b := D_B.decode q.2
      if encB b == q.2 then
        (fun rep ↦ [rep.headD false]) <$> (List.take 1 <$> OracleComp.query ((), q.2))
      else
        pure [false]
    have hG_ppt : IsOraclePPTOn (encPair encA (encPair (encFinEnum Unit) encBits)) encBits
        (fun p : α × (Unit × List Bool) ↦
          OracleComp.interpret ProbOracleComp.query (G p.2)) := by
      let EIn := encPair encA (encPair (encFinEnum Unit) encBits)
      have hq2 : ComputableInPolyTime (fun p : α × (Unit × List Bool) ↦ p.2.2) EIn encBits :=
        (snd _ _).comp (snd _ _)
      have hcond : ComputableInPolyTime
          (fun p : α × (Unit × List Bool) ↦ encB (D_B.decode p.2.2) == p.2.2) EIn encBool :=
        (encoding_comp (D_B.computableInPolyTime.comp hq2)).beq hq2
      have hyes : IsOraclePPTOn EIn encBits (fun p : α × (Unit × List Bool) ↦
          OracleComp.interpret ProbOracleComp.query
            ((fun rep ↦ [rep.headD false]) <$> (List.take 1 <$> OracleComp.query ((),
              p.2.2)))) := by
        have hpost : ComputableInPolyTime (fun rep : List Bool ↦ [rep.headD false])
            encBits encBits :=
          bitsCons (headD false) (const [])
        simpa only [OracleComp.interpret_map, OracleComp.interpret_query] using
          (IsOraclePPTOn.query_take () hq2 (const 1)).map hpost
      refine (IsOraclePPTOn.cond hcond hyes ((const [false]).isOraclePPTOn)).congr ?_
      intro p State oracle s
      dsimp only [G]
      split_ifs with hc
      · rfl
      · simp only [OracleComp.interpret_pure]
    have hsub_ppt : IsOraclePPTOn encA encBool (fun a ↦
        OracleComp.interpret ProbOracleComp.query (OracleComp.interpret G (prog a))) := by
      simpa only [id_eq, OracleComp.interpret_interpret, ProbOracleComp.interpret_query] using
        hPPT.interpret_preprocess_open'
          (operationEncoding := encFinEnum Unit)
          (handler := fun _ q ↦ OracleComp.interpret ProbOracleComp.query (G q))
          (prepare := id) (resources := fun _ _ ↦ 1)
          id' hG_ppt (const 1) fun _ q reply hreply ↦ by
            dsimp only [G] at hreply
            split_ifs at hreply with hc
            · rw [OracleComp.interpret_map] at hreply
              obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
              simp
            · rw [OracleComp.interpret_pure] at hreply
              rw [OracleComp.eq_of_mem_supportWith_pure hreply]
              simp
    refine ⟨fun a ↦ OracleComp.interpret G (prog a), hsub_ppt, fun sol hsol _ a ↦ ?_⟩
    have hG_eval : ∀ q, OracleComp.interpret (m := Id)
        (fun q' ↦ solverWordOracle D_B encBool sol q'.2) (G q) =
        languageOracle (encB '' L₂) q := by
      intro q
      dsimp only [G]
      split_ifs with hc
      · rw [OracleComp.interpret_map, OracleComp.interpret_map, OracleComp.interpret_query]
        have heq_w : encB (D_B.decode q.2) = q.2 := beq_iff_eq.mp hc
        change [((solverWordOracle D_B encBool sol q.2).take 1).headD false] =
          languageOracle (encB '' L₂) q
        rw [← heq_w, solverWordOracle_enc, languageOracle_apply]
        have hiff : sol (D_B.decode q.2) = true ↔ D_B.decode q.2 ∈ L₂ := hsol (D_B.decode q.2)
        have himg : decide (q.2 ∈ encB '' L₂) = sol (D_B.decode q.2) := by
          conv_lhs => rw [← heq_w]
          rw [encB.injective.mem_set_image]
          exact Bool.eq_iff_iff.mpr ⟨fun hm ↦ hiff.mpr (of_decide_eq_true hm),
            fun hs ↦ decide_eq_true (hiff.mp hs)⟩
        rw [himg]
        cases sol (D_B.decode q.2) <;> simp
      · change [false] = [decide (q.2 ∈ encB '' L₂)]
        have hnot_mem : q.2 ∉ encB '' L₂ := by
          rintro ⟨b, _, hbq⟩
          rw [← hbq, D_B.decode_enc b] at hc
          exact hc (beq_self_eq_true _)
        simp [hnot_mem]
    rw [interpret_subst_eq _ _ G (prog a) hG_eval, hf_eq a]
    exact (hL₁ a).symm

/-- Exact equivalence between `PolyTimeOracleReducible` on `FunctionProblem`s and
`Cslib.Complexity.CountingTuringReducible`. -/
theorem polyTimeOracleReducible_functionProblem_iff_countingTuringReducible {α β : Type}
    (encA : α ↪ List Bool) (encB : β ↪ List Bool) (D_B : Decoder encB)
    (f : α → ℕ) (g : β → ℕ) {bound : β → ℕ}
    (hbound : ComputableInPolyTime bound encB encUnary)
    (hsize : ∀ b, (g b).size ≤ bound b) :
    PolyTimeOracleReducible encA encNat encB D_B encNat
      (FunctionProblem f) (FunctionProblem g) ↔
    CountingTuringReducible encA encB f g := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨p, hp⟩ := hbound.polyBounded.exists_polynomial
    obtain ⟨prog, hPPT, hspec⟩ := h p
    have hlen_g : ∀ b, (encNat (g b)).length ≤ p.eval (encB b).length := by
      intro b
      simp only [encNat_apply, Nat.size_eq_bits_len] at hsize ⊢
      exact (hsize b).trans (hp b)
    let G : Unit × List Bool → WordQueryComp Unit (List Bool) := fun q ↦
      let b := D_B.decode q.2
      if encB b == q.2 then
        List.take (p.eval q.2.length) <$> (encNat <$> queryNatBits encB b (bound b))
      else
        pure []
    have hG_ppt : IsOraclePPTOn (encPair encA (encPair (encFinEnum Unit) encBits)) encBits
        (fun pr : α × (Unit × List Bool) ↦
          OracleComp.interpret ProbOracleComp.query (G pr.2)) := by
      let EIn := encPair encA (encPair (encFinEnum Unit) encBits)
      have hq2 : ComputableInPolyTime (fun pr : α × (Unit × List Bool) ↦ pr.2.2) EIn encBits :=
        (snd _ _).comp (snd _ _)
      have hb_pt : ComputableInPolyTime (fun pr : α × (Unit × List Bool) ↦ D_B.decode pr.2.2)
          EIn encB :=
        D_B.computableInPolyTime.comp hq2
      have hcond : ComputableInPolyTime
          (fun pr : α × (Unit × List Bool) ↦ encB (D_B.decode pr.2.2) == pr.2.2) EIn encBool :=
        (encoding_comp hb_pt).beq hq2
      have hcap_pt : ComputableInPolyTime
          (fun pr : α × (Unit × List Bool) ↦ p.eval pr.2.2.length) EIn encUnary :=
        (unary_eval p).comp (length_bits.comp hq2)
      have hyes : IsOraclePPTOn EIn encBits (fun pr : α × (Unit × List Bool) ↦
          OracleComp.interpret ProbOracleComp.query
            (List.take (p.eval pr.2.2.length) <$>
              (encNat <$> queryNatBits encB (D_B.decode pr.2.2)
                (bound (D_B.decode pr.2.2))))) := by
        have hbound_pt : ComputableInPolyTime
            (fun pr : α × (Unit × List Bool) ↦ bound (D_B.decode pr.2.2)) EIn encUnary :=
          (hbound.comp hb_pt).of_enc_eq fun _ ↦ rfl
        have hqb := ((isOraclePPTOn_queryNatBits encB).preprocess
          (hb_pt.prod hbound_pt)).map (encoding_comp id')
        have htake : ComputableInPolyTime
            (fun qr : (α × (Unit × List Bool)) × List Bool ↦ qr.2.take (p.eval qr.1.2.2.length))
            (encPair EIn encBits) encBits :=
          bitsTakeWithInput (snd _ _) (hcap_pt.comp (fst _ _))
        simpa only [OracleComp.interpret_map, Functor.map_map] using hqb.map_with htake
      refine (IsOraclePPTOn.cond hcond hyes ((const []).isOraclePPTOn)).congr ?_
      intro pr State oracle s
      dsimp only [G]
      split_ifs with hc
      · rfl
      · simp only [OracleComp.interpret_pure]
    have hres_pt : ComputableInPolyTime (fun pair : α × List Bool ↦ p.eval pair.2.length)
        (encPair encA encBits) encUnary :=
      (unary_eval p).comp (length_bits.comp (snd _ _))
    have hsub_ppt : IsOraclePPTOn encA encNat (fun a ↦
        OracleComp.interpret ProbOracleComp.query (OracleComp.interpret G (prog a))) := by
      simpa only [id_eq, OracleComp.interpret_interpret, ProbOracleComp.interpret_query] using
        hPPT.interpret_preprocess_open'
          (operationEncoding := encFinEnum Unit)
          (handler := fun _ q ↦ OracleComp.interpret ProbOracleComp.query (G q))
          (prepare := id) (resources := fun _ w ↦ p.eval w.length)
          id' hG_ppt hres_pt fun _ q reply hreply ↦ by
            dsimp only [G] at hreply
            split_ifs at hreply with hc
            · rw [OracleComp.interpret_map] at hreply
              obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
              exact List.length_take_le _ _
            · rw [OracleComp.interpret_pure] at hreply
              rw [OracleComp.eq_of_mem_supportWith_pure hreply]
              simp
    refine ⟨fun a ↦ OracleComp.interpret G (prog a), hsub_ppt, fun A hA ↦ funext fun a ↦ ?_⟩
    have hG_eval : ∀ q, OracleComp.interpret (m := Id) (languageOracle A) (G q) =
        solverWordOracle D_B encNat g q.2 := by
      intro q
      dsimp only [G, solverWordOracle]
      split_ifs with hc
      · rw [OracleComp.interpret_map, OracleComp.interpret_map,
          interpret_queryNatBits hA (hsize (D_B.decode q.2))]
        change (encNat (g (D_B.decode q.2))).take (p.eval q.2.length) =
          encNat (g (D_B.decode q.2))
        have heq_w : encB (D_B.decode q.2) = q.2 := beq_iff_eq.mp hc
        have hle := hlen_g (D_B.decode q.2)
        rw [heq_w] at hle
        exact List.take_of_length_le hle
      · rfl
    rw [interpret_subst_eq _ _ G (prog a) hG_eval]
    exact hspec g (fun _ ↦ rfl) hlen_g a
  · intro p
    obtain ⟨prog, hPPT, hspec⟩ := h
    let DPair := D_B.pair Decoder.nat
    let G : Unit × List Bool → WordQueryComp Unit (List Bool) := fun q ↦
      let bi := DPair.decode q.2
      if encPair encB encNat bi == q.2 then
        (fun rep ↦
          let n := Decoder.nat.decode rep
          [n.testBit (min n.size bi.2)]) <$>
          (List.take (p.eval q.2.length) <$> OracleComp.query ((), encB bi.1))
      else
        pure [false]
    have hG_ppt : IsOraclePPTOn (encPair encA (encPair (encFinEnum Unit) encBits)) encBits
        (fun pr : α × (Unit × List Bool) ↦
          OracleComp.interpret ProbOracleComp.query (G pr.2)) := by
      let EIn := encPair encA (encPair (encFinEnum Unit) encBits)
      have hq2 : ComputableInPolyTime (fun pr : α × (Unit × List Bool) ↦ pr.2.2) EIn encBits :=
        (snd _ _).comp (snd _ _)
      have hbi : ComputableInPolyTime (fun pr : α × (Unit × List Bool) ↦ DPair.decode pr.2.2)
          EIn (encPair encB encNat) :=
        DPair.computableInPolyTime.comp hq2
      have hcond : ComputableInPolyTime
          (fun pr : α × (Unit × List Bool) ↦ encPair encB encNat (DPair.decode pr.2.2) == pr.2.2)
          EIn encBool :=
        (encoding_comp hbi).beq hq2
      have hreq_b : ComputableInPolyTime
          (fun pr : α × (Unit × List Bool) ↦ encB (DPair.decode pr.2.2).1) EIn encBits :=
        encoding_comp hbi.fst'
      have hcap_pt : ComputableInPolyTime
          (fun pr : α × (Unit × List Bool) ↦ p.eval pr.2.2.length) EIn encUnary :=
        (unary_eval p).comp (length_bits.comp hq2)
      have hyes : IsOraclePPTOn EIn encBits (fun pr : α × (Unit × List Bool) ↦
          OracleComp.interpret ProbOracleComp.query
            ((fun rep ↦
              let n := Decoder.nat.decode rep
              [n.testBit (min n.size (DPair.decode pr.2.2).2)]) <$>
              (List.take (p.eval pr.2.2.length) <$>
                OracleComp.query ((), encB (DPair.decode pr.2.2).1)))) := by
        have hpost : ComputableInPolyTime
            (fun qr : (α × (Unit × List Bool)) × List Bool ↦
              let n := Decoder.nat.decode qr.2
              [n.testBit (min n.size (DPair.decode qr.1.2.2).2)])
            (encPair EIn encBits) encBits := by
          have hn : ComputableInPolyTime
              (fun qr : (α × (Unit × List Bool)) × List Bool ↦ Decoder.nat.decode qr.2)
              (encPair EIn encBits) encNat :=
            Decoder.nat.computableInPolyTime.comp (snd _ _)
          have hsize_n : ComputableInPolyTime
              (fun qr : (α × (Unit × List Bool)) × List Bool ↦ (Decoder.nat.decode qr.2).size)
              (encPair EIn encBits) encUnary := by
            have hbits := natBits.comp hn
            simpa only [Function.comp_def, Nat.size_eq_bits_len] using length_bits_comp hbits
          have hi : ComputableInPolyTime
              (fun qr : (α × (Unit × List Bool)) × List Bool ↦ (DPair.decode qr.1.2.2).2)
              (encPair EIn encBits) encNat :=
            (hbi.comp (fst _ _)).snd'
          have hbit := binary_testBit hn (binary_min_unary' hsize_n hi)
          exact bitsCons hbit (const [])
        simpa only [OracleComp.interpret_map, OracleComp.interpret_query] using
          (IsOraclePPTOn.query_take () hreq_b hcap_pt).map_with hpost
      refine (IsOraclePPTOn.cond hcond hyes ((const [false]).isOraclePPTOn)).congr ?_
      intro pr State oracle s
      dsimp only [G]
      split_ifs with hc
      · rfl
      · simp only [OracleComp.interpret_pure]
    have hsub_ppt : IsOraclePPTOn encA encNat (fun a ↦
        OracleComp.interpret ProbOracleComp.query (OracleComp.interpret G (prog a))) := by
      simpa only [id_eq, OracleComp.interpret_interpret, ProbOracleComp.interpret_query] using
        hPPT.interpret_preprocess_open'
          (operationEncoding := encFinEnum Unit)
          (handler := fun _ q ↦ OracleComp.interpret ProbOracleComp.query (G q))
          (prepare := id) (resources := fun _ _ ↦ 1)
          id' hG_ppt (const 1) fun _ q reply hreply ↦ by
            dsimp only [G] at hreply
            split_ifs at hreply with hc
            · rw [OracleComp.interpret_map] at hreply
              obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
              simp
            · rw [OracleComp.interpret_pure] at hreply
              rw [OracleComp.eq_of_mem_supportWith_pure hreply]
              simp
    refine ⟨fun a ↦ OracleComp.interpret G (prog a), hsub_ppt, fun sol hsol hlen a ↦ ?_⟩
    have hsol_eq : sol = g := funext hsol
    rw [hsol_eq] at hlen ⊢
    have hmin (n i : ℕ) : n.testBit (min n.size i) = n.testBit i := by
      rcases le_total i n.size with hle | hle
      · rw [min_eq_right hle]
      · rw [min_eq_left hle, Nat.testBit_eq_false_of_lt (Nat.lt_size_self n),
          Nat.testBit_eq_false_of_lt ((Nat.lt_size_self n).trans_le
            (Nat.pow_le_pow_right two_pos hle))]
    have hG_eval : ∀ q, OracleComp.interpret (m := Id)
        (fun q' ↦ solverWordOracle D_B encNat g q'.2) (G q) =
        languageOracle (bitGraph encB g) q := by
      intro q
      dsimp only [G]
      split_ifs with hc
      · rw [OracleComp.interpret_map, OracleComp.interpret_map, OracleComp.interpret_query]
        set bi := DPair.decode q.2
        have heq_w : encPair encB encNat bi = q.2 := beq_iff_eq.mp hc
        have hlen_b : (encB bi.1).length ≤ q.2.length := by
          rw [← heq_w, length_encPair]
          omega
        have hcap_le : (encNat (g bi.1)).length ≤ p.eval q.2.length :=
          (hlen bi.1).trans (poly_eval_mono p hlen_b)
        let n_dec := Decoder.nat.decode
          ((solverWordOracle D_B encNat g (encB bi.1)).take (p.eval q.2.length))
        change [n_dec.testBit (min n_dec.size bi.2)] = languageOracle (bitGraph encB g) q
        dsimp only [n_dec]
        rw [solverWordOracle_enc, List.take_of_length_le hcap_le, Decoder.nat.decode_enc,
          hmin, languageOracle_apply]
        have hmem_iff : q.2 ∈ bitGraph encB g ↔ (g bi.1).testBit bi.2 = true := by
          rw [← heq_w]
          exact answersBits_bitGraph encB g bi.1 bi.2
        simp [hmem_iff]
      · change [false] = [decide (q.2 ∈ bitGraph encB g)]
        have hnot_mem : q.2 ∉ bitGraph encB g := by
          rintro ⟨x, _, hxq⟩
          rw [← hxq, DPair.decode_enc x] at hc
          exact hc (beq_self_eq_true _)
        simp [hnot_mem]
    rw [FunctionProblem, interpret_subst_eq _ _ G (prog a) hG_eval]
    exact congrFun (hspec (bitGraph encB g) (answersBits_bitGraph encB g)) a

end CslibFrontier.Complexity
