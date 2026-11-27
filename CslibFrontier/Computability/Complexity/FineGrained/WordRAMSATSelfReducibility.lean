/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.WordRAMOracle
public import CslibFrontier.Algorithms.WordRAM.ClauseCode
import CslibFrontier.Computability.WordRAM.CountingLoop
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# SAT / k-SAT Encoding, Word-RAM SETH, and Efficient Self-Reducibility

This module defines the finite-variable SAT and `k`-SAT problems on the standard Word RAM using
the canonical `ClauseCode` word encoding (`Cslib.Algorithms.WordRAM.ClauseCode.encodeClauseBy`,
matching `Cslib.Algorithms.WordRAM.Schoening.encode`), defines `WordRAMSETH`, and proves efficient
`O^*` self-reducibility of SAT and `k`-SAT for `2^n`:

1. `FinCNF`, `FinSAT`, `FinKSATInstance`, `FinKSAT`, `encFinCNF`, `encFinKCNF`,
   `sat_mem_iff_relabel_satisfiable`, `inputFits_encFinCNF`.
2. `WordRAMDecidableInExpStar`, `WordRAMSETH`, `wordRAMDecidableInExpStar_ksat_of_sat`.
3. `restrictClause`, `restrictCNF`, `satisfiable_iff_exists_restrictCNF`, `restrictCNF_kcnf`.
4. `satBranchOracleCode`, `satBranchOracleCode_exec`: adaptive branching oracle reduction fixing
   variables `m .. n - 1` (`m = n / b`) in `O(2^{n - m} · L)` steps.
5. `sat_efficientlySelfReducible_star`, `ksat_efficientlySelfReducible_star`, and concrete
   satisfiable/unsatisfiable non-vacuity witnesses.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

public section

namespace CslibFrontier.Complexity.FineGrained

open Cslib.WordRAM CslibFrontier.WordRAM Cslib.Logic.PL Cslib.Algorithms.WordRAM

/-! ### Finite-Variable SAT, `k`-SAT, and Canonical Word-RAM Encoding -/

/-- The word code `2 v + b` of a literal `(v, b)` on `Fin n` via `ClauseCode.litCodeBy Fin.val`. -/
def litCode {n : ℕ} (l : Literal (Fin n)) : ℕ := ClauseCode.litCodeBy Fin.val l

/-- Word encoding of a clause on `Fin n`: its length followed by its literal codes. -/
def encodeClause {n : ℕ} (c : Clause (Fin n)) : List ℕ := ClauseCode.encodeClauseBy Fin.val c

theorem encodeClause_eq {n : ℕ} (c : Clause (Fin n)) :
    encodeClause c = c.length :: c.map litCode := by
  unfold encodeClause litCode ClauseCode.encodeClauseBy; rfl

/-- Word encoding of a CNF formula's clauses stored consecutively. -/
@[expose] def encodeClauses {n : ℕ} (φ : CNF (Fin n)) : List ℕ := φ.flatMap encodeClause

/-- Canonical Word-RAM encoding of a CNF formula on `Fin n`: `n` followed by `encodeClauses φ`. -/
@[expose] def encode {n : ℕ} (φ : CNF (Fin n)) : List ℕ := n :: encodeClauses φ

@[simp]
theorem length_encodeClause {n : ℕ} (c : Clause (Fin n)) :
    (encodeClause c).length = c.length + 1 :=
  ClauseCode.length_encodeClauseBy Fin.val c

@[simp]
theorem encodeClauses_nil {n : ℕ} : encodeClauses ([] : CNF (Fin n)) = [] := by
  unfold encodeClauses; rfl

@[simp]
theorem encodeClauses_cons {n : ℕ} (c : Clause (Fin n)) (φ : CNF (Fin n)) :
    encodeClauses (c :: φ) = encodeClause c ++ encodeClauses φ := by
  simp [encodeClauses]

theorem encodeClauses_append {n : ℕ} (φ₁ φ₂ : CNF (Fin n)) :
    encodeClauses (φ₁ ++ φ₂) = encodeClauses φ₁ ++ encodeClauses φ₂ :=
  List.flatMap_append

theorem litCode_lt {n : ℕ} (l : Literal (Fin n)) : litCode l < 2 * n := by
  have hle := ClauseCode.litCodeBy_le Fin.val l
  have hv := l.1.isLt
  unfold litCode
  omega

theorem litCode_shiftRight {n : ℕ} (l : Literal (Fin n)) : litCode l >>> 1 = l.1.val :=
  ClauseCode.litCodeBy_shiftRight Fin.val l

theorem litCode_and_one {n : ℕ} (l : Literal (Fin n)) : litCode l &&& 1 = l.2.toNat :=
  ClauseCode.litCodeBy_and_one Fin.val l

/-- A CNF formula together with its finite variable bound `n`. -/
abbrev FinCNF : Type := Σ n : ℕ, CNF (Fin n)

/-- Satisfiable finite-variable CNF formulas (`SAT`). -/
@[expose] def FinSAT : Set FinCNF := { x | x.2.Satisfiable }

theorem mem_finSAT_iff (x : FinCNF) : x ∈ FinSAT ↔ x.2.Satisfiable := Iff.rfl

/-- A `k`-CNF formula: every clause has at most `k` literals. -/
abbrev FinKSATInstance (k : ℕ) : Type := { x : FinCNF // ∀ c ∈ x.2, c.length ≤ k }

/-- Satisfiable finite-variable `k`-CNF formulas (`k`-SAT). -/
@[expose] def FinKSAT (k : ℕ) : Set (FinKSATInstance k) := { x | x.1.2.Satisfiable }

/-- Direct 1-to-1 equivalence with `CNF.Satisfiable` on `ℕ`-indexed variables. -/
theorem sat_mem_iff_relabel_satisfiable (x : FinCNF) :
    x ∈ FinSAT ↔ (x.2.relabel Fin.val).Satisfiable :=
  (CNF.satisfiable_relabel Fin.val_injective x.2).symm

private theorem litCode_injective {n : ℕ} : Function.Injective (litCode (n := n)) := by
  intro ⟨v₁, b₁⟩ ⟨v₂, b₂⟩ h
  have hv := congrArg (· >>> 1) h
  have hb := congrArg (· &&& 1) h
  rw [litCode_shiftRight, litCode_shiftRight] at hv
  rw [litCode_and_one, litCode_and_one] at hb
  have hb' : b₁ = b₂ := by cases b₁ <;> cases b₂ <;> simp_all
  exact Prod.ext (Fin.ext hv) hb'

private theorem encodeClauses_injective {n : ℕ} :
    Function.Injective (encodeClauses (n := n)) := by
  intro φ₁ φ₂ h
  induction φ₁ generalizing φ₂ with
  | nil =>
    cases φ₂ with
    | nil => rfl
    | cons c ψ => simp [encodeClauses, encodeClause_eq] at h
  | cons c₁ ψ₁ ih =>
    cases φ₂ with
    | nil => simp [encodeClauses, encodeClause_eq] at h
    | cons c₂ ψ₂ =>
      simp only [encodeClauses_cons, encodeClause_eq, List.cons_append, List.cons.injEq] at h
      obtain ⟨hlen, hrest⟩ := h
      have hmap : c₁.map litCode = c₂.map litCode := by
        have ht := congrArg (List.take c₁.length) hrest
        rw [List.take_left' (by simp), hlen, List.take_left' (by simp)] at ht
        exact ht
      have htail : encodeClauses ψ₁ = encodeClauses ψ₂ := by
        have hd := congrArg (List.drop c₁.length) hrest
        rw [List.drop_left' (by simp), hlen, List.drop_left' (by simp)] at hd
        exact hd
      have hc : c₁ = c₂ := List.map_injective_iff.mpr litCode_injective |>.eq_iff.mp hmap
      exact congrArg₂ List.cons hc (ih htail)

/-- Injective Word-RAM encoding of `FinCNF` via `ClauseCode.encodeClauseBy Fin.val`. -/
@[expose] def encFinCNF : FinCNF ↪ List ℕ where
  toFun x := encode x.2
  inj' := by
    intro ⟨n₁, φ₁⟩ ⟨n₂, φ₂⟩ h
    simp only [encode, List.cons.injEq] at h
    obtain ⟨rfl, hcl⟩ := h
    exact Sigma.ext rfl (heq_of_eq (encodeClauses_injective hcl))

/-- Injective Word-RAM encoding of `FinKSATInstance k`. -/
@[expose] def encFinKCNF (k : ℕ) : FinKSATInstance k ↪ List ℕ where
  toFun x := encFinCNF x.1
  inj' := fun _ _ h => Subtype.ext (encFinCNF.injective h)

theorem encFinCNF_eq_cons (x : FinCNF) : encFinCNF x = x.1 :: encodeClauses x.2 := rfl

theorem encFinCNF_length (x : FinCNF) :
    (encFinCNF x).length = (encodeClauses x.2).length + 1 := rfl

theorem encFinCNF_length_pos (x : FinCNF) : 1 ≤ (encFinCNF x).length := by
  simp [encFinCNF, encode]

private theorem mem_encodeClauses_lt {n : ℕ} (φ : CNF (Fin n)) {v : ℕ}
    (hv : v ∈ encodeClauses φ) : v < (encodeClauses φ).length + 2 * n + 1 := by
  induction φ with
  | nil => simp at hv
  | cons c ψ ih =>
    rw [encodeClauses_cons, List.mem_append] at hv
    rcases hv with hc | hψ
    · rw [encodeClause_eq, List.mem_cons] at hc
      rcases hc with rfl | hl
      · have h1 : c.length < (encodeClause c).length := by simp
        have h2 : (encodeClause c).length ≤ (encodeClauses (c :: ψ)).length := by
          rw [encodeClauses_cons, List.length_append]; omega
        omega
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hl
        have := litCode_lt l; omega
    · have h1 := ih hψ
      have h2 : (encodeClauses ψ).length ≤ (encodeClauses (c :: ψ)).length := by
        rw [encodeClauses_cons, List.length_append]; omega
      omega

/-- Every `FinCNF` instance fits in any word width `w ≥ logWidth 2 (x.1 + (encFinCNF x).length)`. -/
theorem inputFits_encFinCNF {w : ℕ} {x : FinCNF}
    (hw : logWidth 2 (x.1 + (encFinCNF x).length) ≤ w) : InputFits w (encFinCNF x) := by
  set S := x.1 + (encFinCNF x).length
  have hlt : S < 2 ^ (Nat.log 2 S + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two S
  have h2_le : Nat.log 2 S + 2 ≤ w := by
    have : 2 * (Nat.log 2 S + 1) ≤ w := by simpa [logWidth] using hw
    omega
  have h2S : 2 * S + 1 < 2 ^ w := by
    have h1 : 2 * S + 1 < 2 ^ (Nat.log 2 S + 2) := by rw [pow_succ]; omega
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right Nat.two_pos h2_le)
  refine ⟨show (encFinCNF x).length < 2 ^ w by omega, fun v hv => ?_⟩
  simp only [encFinCNF, Function.Embedding.coeFn_mk, encode, List.mem_cons] at hv
  rcases hv with rfl | hcl
  · exact show x.1 < 2 ^ w by omega
  · have hlt_v := mem_encodeClauses_lt x.2 hcl
    have hlen : (encodeClauses x.2).length + 1 = (encFinCNF x).length := by
      simp [encFinCNF, encode]
    exact show v < 2 ^ w by omega

/-! ### Word-RAM `O^*` Exponential-Time Classes and `WordRAMSETH` -/

/-- `P` is decidable on the standard Word RAM in time `O^*(2^{c · size(a)})`. -/
@[expose] def WordRAMDecidableInExpStar {α : Type*} (P : Set α) (enc : α ↪ List ℕ)
    (size : α → ℕ) (c_exp : ℝ) : Prop :=
  ∃ (C e : ℕ), 0 < C ∧
    WordRAMDecidableInTime P enc
      (fun a => C * ((enc a).length + 1) ^ e * ⌈(2 : ℝ) ^ (c_exp * (size a : ℝ))⌉₊ + C)

/-- **Strong Exponential Time Hypothesis (SETH)** on the standard Word RAM: for every `ε > 0`,
there exists `k` such that `k`-SAT cannot be decided in time `O^*(2^{(1 - ε) n})`. -/
@[expose] def WordRAMSETH : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ k : ℕ, ¬ WordRAMDecidableInExpStar (FinKSAT k) (encFinKCNF k) (fun x => x.1.1) (1 - ε)

/-- Any `O^*(2^{c · n})` Word-RAM solver for `FinSAT` immediately yields one for every
`FinKSAT k`. -/
theorem wordRAMDecidableInExpStar_ksat_of_sat {c_exp : ℝ}
    (h : WordRAMDecidableInExpStar FinSAT encFinCNF (·.1) c_exp) (k : ℕ) :
    WordRAMDecidableInExpStar (FinKSAT k) (encFinKCNF k) (fun x => x.1.1) c_exp := by
  obtain ⟨C, e, hC, r, c, out, kw, hrf, hkw, hdec⟩ := h
  exact ⟨C, e, hC, r, c, out, kw, hrf, hkw, fun x w hw hi => hdec x.1 w hw hi⟩

/-! ### Variable Restriction (`restrictCNF`) -/

/-- Restrict a clause on `Fin n` to `Fin m` by fixing variables `v ≥ m` according to bitmask `r`.
Returns `none` if the clause is already satisfied, and `some c'` otherwise. -/
def restrictClause {n : ℕ} (m r : ℕ) (c : Clause (Fin n)) : Option (Clause (Fin m)) :=
  if c.any (fun l => decide (m ≤ l.1.val ∧ decide ((r >>> (l.1.val - m)) % 2 = 1) = l.2))
  then none
  else some (c.filterMap fun l => if h : l.1.val < m then some (⟨l.1.val, h⟩, l.2) else none)

/-- Restrict a CNF formula on `Fin n` to `Fin m` by fixing variables `v ≥ m` using bitmask `r`. -/
def restrictCNF {n : ℕ} (m r : ℕ) (φ : CNF (Fin n)) : CNF (Fin m) :=
  φ.filterMap (restrictClause m r)

theorem restrictCNF_kcnf {n k : ℕ} (m r : ℕ) {φ : CNF (Fin n)} (hk : ∀ c ∈ φ, c.length ≤ k) :
    ∀ c' ∈ restrictCNF m r φ, c'.length ≤ k := by
  intro c' hc'
  obtain ⟨c, hc, hrc⟩ := List.mem_filterMap.mp hc'
  unfold restrictClause at hrc
  split_ifs at hrc with hsat
  simp only [Option.some.injEq] at hrc
  subst hrc
  exact (List.length_filterMap_le _ _).trans (hk c hc)

theorem length_encodeClauses_restrictCNF_le {n : ℕ} (m r : ℕ) (φ : CNF (Fin n)) :
    (encodeClauses (restrictCNF m r φ)).length ≤ (encodeClauses φ).length := by
  induction φ with
  | nil => simp [restrictCNF]
  | cons c ψ ih =>
    simp only [restrictCNF, List.filterMap_cons]
    cases hrc : restrictClause m r c with
    | none =>
      simp only [encodeClauses_cons, List.length_append]
      change (encodeClauses (restrictCNF m r ψ)).length ≤
        (encodeClause c).length + (encodeClauses ψ).length
      omega
    | some c' =>
      have hlen : c'.length ≤ c.length := by
        unfold restrictClause at hrc
        split_ifs at hrc
        simp only [Option.some.injEq] at hrc; rw [← hrc]; exact List.length_filterMap_le _ _
      simp only [encodeClauses_cons, List.length_append, length_encodeClause]
      change c'.length + 1 + (encodeClauses (restrictCNF m r ψ)).length ≤
        c.length + 1 + (encodeClauses ψ).length
      omega

/-- Exact satisfiability equivalence for variable branching (`m ≤ n`). -/
theorem satisfiable_iff_exists_restrictCNF {n m : ℕ} (hm : m ≤ n) (φ : CNF (Fin n)) :
    φ.Satisfiable ↔ ∃ r < 2 ^ (n - m), (restrictCNF m r φ).Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    let bits : List Bool := List.ofFn fun i : Fin (n - m) => σ ⟨m + i.val, by omega⟩
    let r := bitStringMask bits
    have hr_lt : r < 2 ^ (n - m) := by
      have h := bitStringMask_lt bits
      simpa [bits] using h
    have hr_bit : ∀ i (hi : i < n - m), decide ((r >>> i) % 2 = 1) = σ ⟨m + i, by omega⟩ := by
      intro i hi
      have htb := bitStringMask_testBit bits i (by simpa [bits] using hi)
      simp only [bits, List.getElem_ofFn] at htb
      rw [htb]; cases σ ⟨m + i, by omega⟩ <;> rfl
    refine ⟨r, hr_lt, fun i => σ ⟨i.val, by omega⟩, ?_⟩
    rw [CNF.eval_eq_true_iff] at hσ ⊢
    intro c' hc'
    obtain ⟨c, hc, hrc⟩ := List.mem_filterMap.mp hc'
    unfold restrictClause at hrc
    split_ifs at hrc with hsat
    simp only [Option.some.injEq] at hrc; subst hrc
    obtain ⟨l, hl, hlev⟩ := (Clause.eval_eq_true_iff σ c).mp (hσ c hc)
    rw [Clause.eval_eq_true_iff]
    by_cases hlm : l.1.val < m
    · refine ⟨(⟨l.1.val, hlm⟩, l.2), ?_, hlev⟩
      exact List.mem_filterMap.mpr ⟨l, hl, by simp [hlm]⟩
    · exfalso
      have hge : m ≤ l.1.val := by omega
      have hi : l.1.val - m < n - m := by have := l.1.isLt; omega
      have hb := hr_bit (l.1.val - m) hi
      have hfin : (⟨m + (l.1.val - m), by have := l.1.isLt; omega⟩ : Fin n) = l.1 :=
        Fin.ext (by dsimp only; omega)
      rw [hfin, hlev] at hb
      have hany : c.any (fun l => decide (m ≤ l.1.val ∧
        decide ((r >>> (l.1.val - m)) % 2 = 1) = l.2)) = true :=
        List.any_eq_true.mpr ⟨l, hl, by simp [hge, hb]⟩
      exact hsat hany
  · rintro ⟨r, -, τ, hτ⟩
    let σ : Fin n → Bool := fun v =>
      if h : v.val < m then τ ⟨v.val, h⟩ else decide ((r >>> (v.val - m)) % 2 = 1)
    refine ⟨σ, ?_⟩
    rw [CNF.eval_eq_true_iff] at hτ ⊢
    intro c hc
    cases hrc : restrictClause m r c with
    | none =>
      unfold restrictClause at hrc
      split_ifs at hrc with hsat
      obtain ⟨l, hl, hcond⟩ := List.any_eq_true.mp hsat
      obtain ⟨hge, hb⟩ := of_decide_eq_true hcond
      rw [Clause.eval_eq_true_iff]
      refine ⟨l, hl, ?_⟩
      simp only [σ, show ¬(l.1.val < m) by omega, ↓reduceDIte]; exact hb
    | some c' =>
      have hc'_mem : c' ∈ restrictCNF m r φ := List.mem_filterMap.mpr ⟨c, hc, hrc⟩
      obtain ⟨l', hl', hlev⟩ := (Clause.eval_eq_true_iff τ c').mp (hτ c' hc'_mem)
      unfold restrictClause at hrc
      split_ifs at hrc with hsat
      simp only [Option.some.injEq] at hrc; rw [← hrc] at hl'
      obtain ⟨l, hl, hfl⟩ := List.mem_filterMap.mp hl'
      split_ifs at hfl with hlm
      · simp only [Option.some.injEq] at hfl
        rw [Clause.eval_eq_true_iff]
        refine ⟨l, hl, ?_⟩
        have h1 : l' = (⟨l.1.val, hlm⟩, l.2) := hfl.symm
        rw [h1] at hlev
        simp only [σ, hlm, ↓reduceDIte]; exact hlev

/-! ### Branching Oracle Reduction (`satBranchOracleCode`) -/

private def satLitStep : OracleCode .standard 24 :=
  .seq (.op (.load 18 13))
    (.seq (.op (.bin .shiftRight 19 18 1))
      (.seq (.op (.bin .and 20 18 1))
        (.seq (.branch (.lt 19 5)
          (.seq (.op (.store 10 18))
            (.seq (.op (.bin .add 10 10 1))
              (.op (.bin .add 17 17 1))))
          (.seq (.op (.bin .sub 21 19 5))
            (.seq (.op (.bin .shiftRight 21 9 21))
              (.seq (.op (.bin .and 21 21 1))
                (.branch (.eq 21 20) (.op (.const 16 1)) (.op (.const 21 0)))))))
          (.op (.bin .add 13 13 1)))))

private def satClauseStep : OracleCode .standard 24 :=
  .seq (.op (.load 12 11))
    (.seq (.op (.bin .add 13 11 1))
      (.seq (.op (.bin .add 14 13 12))
        (.seq (.op (.copy 15 10))
          (.seq (.op (.bin .add 10 10 1))
            (.seq (.op (.const 16 0))
              (.seq (.op (.const 17 0))
                (.seq (.loop (.lt 13 14) satLitStep)
                  (.seq (.branch (.eq 16 1)
                    (.op (.copy 10 15))
                    (.op (.store 15 17)))
                    (.op (.copy 11 14))))))))))

private def satBranchBody : OracleCode .standard 24 :=
  .seq (.op (.store 4 5))
    (.seq (.op (.bin .add 10 4 1))
      (.seq (.op (.const 11 2))
        (.seq (.loop (.lt 11 4) satClauseStep)
          (.seq (.op (.bin .sub 22 10 4))
            (.seq (.query 23 4 22)
              (.seq (.branch (.eq 23 1) (.op (.const 8 1)) (.op (.const 21 0)))
                (.op (.bin .add 9 9 1))))))))

private def satBranchSetup (b : ℕ) : OracleCode .standard 24 :=
  .seq (.op (.const 0 0))
    (.seq (.op (.const 1 1))
      (.seq (.op (.load 2 0))
        (.seq (.op (.load 3 1))
          (.seq (.op (.bin .add 4 2 1))
            (.seq (.op (.const 21 b))
              (.seq (.op (.bin .div 5 3 21))
                (.seq (.op (.bin .sub 6 3 5))
                  (.seq (.op (.bin .shiftLeft 7 1 6))
                    (.seq (.op (.const 8 0))
                      (.op (.const 9 0)))))))))))

/-- Adaptive branching oracle reduction for SAT / `k`-SAT fixing variables `m .. n - 1`
where `m = n / b` (`b ≥ 1`). Enumerates all `2^{n - m}` partial assignments, writes
`encFinCNF ⟨m, restrictCNF m r φ⟩` to `[L + 1, 2*L + 1]`, and queries the oracle. -/
def satBranchOracleCode (b : ℕ) : OracleCode .standard 24 :=
  .seq (satBranchSetup b) (.loop (.lt 9 7) satBranchBody)

private theorem oracleExec_bin {r w : ℕ} {O : List ℕ → Bool} {x : Data r}
    {f : BinOp} {d i j : Fin r} (h : Fits w (f.eval (x.regs i) (x.regs j))) :
    OracleExec (B := .standard) w O (.op (.bin f d i j)) x
      (x.set d (f.eval (x.regs i) (x.regs j))) 1 [] :=
  .op (Data.put_of_fits h)

private def satKeptOf {n : ℕ} (m : ℕ) (c : Clause (Fin n)) (j : ℕ) : List (Literal (Fin m)) :=
  (c.take j).filterMap fun l => if h : l.1.val < m then some (⟨l.1.val, h⟩, l.2) else none

private def satFlagOf {n : ℕ} (m r_idx : ℕ) (c : Clause (Fin n)) (j : ℕ) : Bool :=
  (c.take j).any fun l => decide (m ≤ l.1.val ∧
    decide ((r_idx >>> (l.1.val - m)) % 2 = 1) = l.2)

private theorem satLitLoop_exec {w n m diff r_idx L ptr qPtr d8 : ℕ}
    {O : List ℕ → Bool} {x0 : Data 24} {c : Clause (Fin n)} {ψ_pre : CNF (Fin n)}
    (hr_lt : r_idx < 2 ^ diff) (hm_le : m ≤ n)
    (hw_pow : Fits w (2 ^ diff)) (hw_mem : Fits w (2 * L + 2)) (hw_n : Fits w (2 * n + 2))
    (h1_f : Fits w 1)
    (hptr_lt : ptr < L + 1) (hptr_c : ptr + 1 + c.length ≤ L + 1) (_hqPtr_le : qPtr ≤ 2 * L + 1)
    (hqPtr_c : qPtr + 1 + c.length ≤ 2 * L + 2)
    (hqPtr_lo : L + 2 ≤ qPtr)
    (hmem_lit : ∀ j (hj : j < c.length), x0.mem (ptr + 1 + j) = litCode (c[j])) :
    ∀ (j : ℕ) (v : Data 24),
      j ≤ c.length →
      v.regs 0 = 0 → v.regs 1 = 1 → v.regs 2 = L → v.regs 3 = n → v.regs 4 = L + 1 →
      v.regs 5 = m → v.regs 6 = diff → v.regs 7 = 2 ^ diff → v.regs 8 = d8 →
      v.regs 9 = r_idx → v.regs 13 = ptr + 1 + j → v.regs 14 = ptr + 1 + c.length →
      v.regs 15 = qPtr → v.regs 10 = qPtr + 1 + (satKeptOf m c j).length →
      v.regs 16 = (satFlagOf m r_idx c j).toNat → v.regs 17 = (satKeptOf m c j).length →
      (∀ a ≤ L, v.mem a = x0.mem a) → v.mem (L + 1) = m →
      (∀ i (hi : i < (encodeClauses (restrictCNF m r_idx ψ_pre)).length),
        v.mem (L + 2 + i) = (encodeClauses (restrictCNF m r_idx ψ_pre))[i]'hi) →
      (∀ i (hi : i < (satKeptOf m c j).length),
        v.mem (qPtr + 1 + i) = litCode ((satKeptOf m c j)[i]'hi)) →
      (∀ i, i < (encodeClauses (restrictCNF m r_idx ψ_pre)).length →
        L + 2 + i < qPtr) →
      ∃ (v' : Data 24) (t_l : ℕ),
        OracleExec w O (.loop (.lt 13 14) satLitStep) v v' t_l [] ∧
        v'.regs 0 = 0 ∧ v'.regs 1 = 1 ∧ v'.regs 2 = L ∧ v'.regs 3 = n ∧ v'.regs 4 = L + 1 ∧
        v'.regs 5 = m ∧ v'.regs 6 = diff ∧ v'.regs 7 = 2 ^ diff ∧ v'.regs 8 = d8 ∧
        v'.regs 9 = r_idx ∧ v'.regs 14 = ptr + 1 + c.length ∧ v'.regs 15 = qPtr ∧
        v'.regs 10 = qPtr + 1 + (satKeptOf m c c.length).length ∧
        v'.regs 16 = (satFlagOf m r_idx c c.length).toNat ∧
        v'.regs 17 = (satKeptOf m c c.length).length ∧
        (∀ a ≤ L, v'.mem a = x0.mem a) ∧ v'.mem (L + 1) = m ∧
        (∀ i (hi : i < (encodeClauses (restrictCNF m r_idx ψ_pre)).length),
          v'.mem (L + 2 + i) = (encodeClauses (restrictCNF m r_idx ψ_pre))[i]'hi) ∧
        (∀ i (hi : i < (satKeptOf m c c.length).length),
          v'.mem (qPtr + 1 + i) = litCode ((satKeptOf m c c.length)[i]'hi)) ∧
        t_l ≤ 14 * (c.length - j) + 2 := by
  intro j
  generalize hrem_j : c.length - j = rj
  induction rj generalizing j with
  | zero =>
    intro v hj hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv13 hv14 hv15 hv10 hv16 hv17
      hvmem hvm1 hvq hvkept _
    have hjeq : j = c.length := by omega
    subst hjeq
    have hstop : ¬(Cond.lt 13 14).Holds v := by simp [Cond.Holds, hv13, hv14]
    exact ⟨v, 2, OracleExec.loop_exit hstop, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8,
      hv9, hv14, hv15, hv10, hv16, hv17, hvmem, hvm1, hvq, hvkept, by omega⟩
  | succ rj ihr =>
    intro v hj hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv13 hv14 hv15 hv10 hv16 hv17
      hvmem hvm1 hvq hvkept hq_gt
    have hj_lt : j < c.length := by omega
    have hcond_l : (Cond.lt 13 14).Holds v := by simp [Cond.Holds, hv13, hv14]; omega
    set l := c[j]
    have hkept_succ : satKeptOf m c (j + 1) =
        satKeptOf m c j ++ (if h : l.1.val < m then [(⟨l.1.val, h⟩, l.2)] else []) := by
      simp only [satKeptOf, List.take_succ_eq_append_getElem hj_lt, List.filterMap_append,
        List.filterMap_cons, List.filterMap_nil]
      split_ifs <;> rfl
    have hsat_succ : satFlagOf m r_idx c (j + 1) =
        (satFlagOf m r_idx c j || decide (m ≤ l.1.val ∧
          decide ((r_idx >>> (l.1.val - m)) % 2 = 1) = l.2)) := by
      simp only [satFlagOf, l, List.take_succ_eq_append_getElem hj_lt, List.any_append,
        List.any_cons, List.any_nil, Bool.or_false]
    have hlen_kept_le : (satKeptOf m c (j + 1)).length ≤ j + 1 := by
      have := List.length_filterMap_le (fun l : Literal (Fin n) =>
        if h : l.1.val < m then some ((⟨l.1.val, h⟩, l.2) : Literal (Fin m)) else none)
        (c.take (j + 1))
      simpa [satKeptOf, List.length_take, Nat.min_eq_left (show j + 1 ≤ c.length by omega)]
        using this
    have hvmem_l : v.mem (ptr + 1 + j) = litCode l := by
      rw [hvmem _ (by omega)]; exact hmem_lit j hj_lt
    let v1 := v.set 18 (litCode l); let v2 := v1.set 19 l.1.val; let v3 := v2.set 20 l.2.toNat
    have lo1 : OracleExec (B := .standard) w O (.op (.load 18 13)) v v1 1 [] :=
      OracleExec.op (by simp [Op.eval, v1, hv13, hvmem_l])
    have lo2 : OracleExec (B := .standard) w O (.op (.bin .shiftRight 19 18 1)) v1 v2 1 [] := by
      simpa [v2, v1, hv1, BinOp.eval, litCode_shiftRight] using
        oracleExec_bin (w := w) (O := O) (x := v1) (f := .shiftRight) (d := 19) (i := 18) (j := 1)
          (by simpa [v1, hv1, BinOp.eval, litCode_shiftRight] using
            Fits.of_le hw_n (by have := l.1.isLt; omega))
    have lo3 : OracleExec (B := .standard) w O (.op (.bin .and 20 18 1)) v2 v3 1 [] := by
      have h18 : v2.regs 18 = litCode l := by simp [v2, v1]
      have h1' : v2.regs 1 = 1 := by simp [v2, v1, hv1]
      have hval : v2.regs 18 &&& v2.regs 1 = l.2.toNat := by rw [h18, h1', litCode_and_one]
      have hbt : (v2.regs 18 &&& v2.regs 1) ≤ 1 := by rw [hval]; cases l.2 <;> simp
      have h := oracleExec_bin (w := w) (O := O) (x := v2) (f := .and) (d := 20) (i := 18) (j := 1)
        (Fits.of_le h1_f hbt)
      dsimp only [BinOp.eval] at h
      rwa [hval] at h
    by_cases hlm : l.1.val < m
    · have hc_lm : (Cond.lt 19 5).Holds v3 := by simp [Cond.Holds, v3, v2, v1, hv5, hlm]
      have hsat_eq : satFlagOf m r_idx c (j + 1) = satFlagOf m r_idx c j := by
        rw [hsat_succ]; simp [show ¬(m ≤ l.1.val) by omega]
      have hkept_len : (satKeptOf m c (j + 1)).length = (satKeptOf m c j).length + 1 := by
        simp [hkept_succ, hlm]
      let v4 := v3.write (qPtr + 1 + (satKeptOf m c j).length) (litCode l)
      let v5 := v4.set 10 (qPtr + 1 + (satKeptOf m c j).length + 1)
      let v6 := v5.set 17 ((satKeptOf m c j).length + 1)
      let v7 := v6.set 13 (ptr + 1 + (j + 1))
      have o4 : OracleExec (B := .standard) w O (.op (.store 10 18)) v3 v4 1 [] :=
        OracleExec.op (by simp [Op.eval, v4, v3, v2, v1, hv10])
      have o5 : OracleExec (B := .standard) w O (.op (.bin .add 10 10 1)) v4 v5 1 [] := by
        simpa [v5, v4, v3, v2, v1, hv10, hv1, BinOp.eval] using
          oracleExec_bin (w := w) (O := O) (x := v4) (f := .add) (d := 10) (i := 10) (j := 1)
            (by simpa [v4, v3, v2, v1, hv10, hv1, BinOp.eval] using Fits.of_le hw_mem (by omega))
      have o6 : OracleExec (B := .standard) w O (.op (.bin .add 17 17 1)) v5 v6 1 [] := by
        simpa [v6, v5, v4, v3, v2, v1, hv17, hv1, BinOp.eval] using
          oracleExec_bin (w := w) (O := O) (x := v5) (f := .add) (d := 17) (i := 17) (j := 1)
            (by simpa [v5, v4, v3, v2, v1, hv17, hv1, BinOp.eval] using
              Fits.of_le hw_mem (by omega))
      have o7 : OracleExec (B := .standard) w O (.op (.bin .add 13 13 1)) v6 v7 1 [] := by
        simpa [v7, v6, v5, v4, v3, v2, v1, hv13, hv1, BinOp.eval,
          show ptr + 1 + j + 1 = ptr + 1 + (j + 1) by omega] using
          oracleExec_bin (w := w) (O := O) (x := v6) (f := .add) (d := 13) (i := 13) (j := 1)
            (by simpa [v6, v5, v4, v3, v2, v1, hv13, hv1, BinOp.eval] using
              Fits.of_le hw_mem (by omega))
      obtain ⟨v', t_rest, hv', hv'0, hv'1, hv'2, hv'3, hv'4, hv'5, hv'6, hv'7, hv'8, hv'9,
        hv'14, hv'15, hv'10, hv'16, hv'17, hv'mem, hv'm1, hv'q, hv'kept, ht_rest⟩ :=
        ihr (j + 1) (by omega) v7 (by omega)
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv0])
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv1])
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv2])
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv3])
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv4])
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv5])
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv6])
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv7])
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv8])
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv9])
          (by simp [v7]) (by simp [v7, v6, v5, v4, v3, v2, v1, hv14])
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv15])
          (by simp [v7, v6, v5, hkept_len]; omega)
          (by simp [v7, v6, v5, v4, v3, v2, v1, hv16, hsat_eq])
          (by simp [v7, v6, hkept_len])
          (fun a ha => by simp [v7, v6, v5, v4, v3, v2, v1,
            Function.update_of_ne (show a ≠ qPtr + 1 + (satKeptOf m c j).length by omega),
            hvmem a ha])
          (by simp [v7, v6, v5, v4, v3, v2, v1,
            Function.update_of_ne (show L + 1 ≠ qPtr + 1 + (satKeptOf m c j).length by omega),
            hvm1])
          (fun i hi => by
            have hne := hq_gt i hi
            simp [v7, v6, v5, v4, v3, v2, v1,
              Function.update_of_ne (show L + 2 + i ≠ qPtr + 1 + (satKeptOf m c j).length by omega),
              hvq i hi])
          (fun i hi => by
            by_cases hil : i = (satKeptOf m c j).length
            · subst hil; simp only [v7, v6, v5, v4, Data.set_mem, Data.write_mem,
                Function.update_self, hkept_succ, hlm, ↓reduceDIte]
              rw [List.getElem_append_right (le_refl _)]; simp [litCode, ClauseCode.litCodeBy]
            · simp only [v7, v6, v5, v4, v3, v2, v1, Data.set_mem, Data.write_mem,
                Function.update_of_ne (show qPtr + 1 + i ≠
                  qPtr + 1 + (satKeptOf m c j).length by omega)]
              rw [hvkept i (by omega)]
              simp only [hkept_succ, hlm, ↓reduceDIte,
                List.getElem_append_left (by omega : i < (satKeptOf m c j).length)])
          hq_gt
      refine ⟨v', _,
        OracleExec.loop_iter hcond_l
          (lo1.seq (lo2.seq (lo3.seq ((OracleExec.branch_pos hc_lm
            (o4.seq (o5.seq o6))).seq o7)))) hv',
        hv'0, hv'1, hv'2, hv'3, hv'4, hv'5, hv'6, hv'7, hv'8, hv'9, hv'14, hv'15, hv'10, hv'16,
        hv'17, hv'mem, hv'm1, hv'q, hv'kept, by omega⟩
    · have hc_lm : ¬(Cond.lt 19 5).Holds v3 := by simp [Cond.Holds, v3, v2, v1, hv5, hlm]
      have hkept_eq : satKeptOf m c (j + 1) = satKeptOf m c j := by simp [hkept_succ, hlm]
      have hge : m ≤ l.1.val := by omega
      have hdiff_v : Fits w (l.1.val - m) := Fits.of_le hw_n (by have := l.1.isLt; omega)
      have hr_sh_f : Fits w (r_idx >>> (l.1.val - m)) :=
        Fits.of_le (Fits.of_le hw_pow (le_of_lt hr_lt))
          (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
      let v4 := v3.set 21 (l.1.val - m); let v5 := v4.set 21 (r_idx >>> (l.1.val - m))
      let v6 := v5.set 21 ((r_idx >>> (l.1.val - m)) % 2)
      have o4 : OracleExec (B := .standard) w O (.op (.bin .sub 21 19 5)) v3 v4 1 [] := by
        simpa [v4, v3, v2, v1, hv5, BinOp.eval] using
          oracleExec_bin (w := w) (O := O) (x := v3) (f := .sub) (d := 21) (i := 19) (j := 5)
            (by simpa [v3, v2, v1, hv5, BinOp.eval] using hdiff_v)
      have o5 : OracleExec (B := .standard) w O (.op (.bin .shiftRight 21 9 21)) v4 v5 1 [] := by
        simpa [v5, v4, v3, v2, v1, hv9, BinOp.eval] using
          oracleExec_bin (w := w) (O := O) (x := v4) (f := .shiftRight) (d := 21) (i := 9) (j := 21)
            (by simpa [v4, v3, v2, v1, hv9, BinOp.eval] using hr_sh_f)
      have o6 : OracleExec (B := .standard) w O (.op (.bin .and 21 21 1)) v5 v6 1 [] := by
        simpa [v6, v5, v4, v3, v2, v1, hv1, BinOp.eval, Nat.and_one_is_mod] using
          oracleExec_bin (w := w) (O := O) (x := v5) (f := .and) (d := 21) (i := 21) (j := 1)
            (by simpa [v5, v4, v3, v2, v1, hv1, BinOp.eval, Nat.and_one_is_mod] using
              Fits.of_le h1_f (by omega : (r_idx >>> (l.1.val - m)) % 2 ≤ 1))
      have hmatch_iff : ((r_idx >>> (l.1.val - m)) % 2 = l.2.toNat) ↔
          (decide ((r_idx >>> (l.1.val - m)) % 2 = 1) = l.2) := by
        rcases Nat.mod_two_eq_zero_or_one (r_idx >>> (l.1.val - m)) with hm0 | hm1
        · cases l.2 <;> simp [hm0]
        · cases l.2 <;> simp [hm1]
      let v7 := if (r_idx >>> (l.1.val - m)) % 2 = l.2.toNat then v6.set 16 1 else v6.set 21 0
      have ho7 : ∃ t7 ≤ 3, OracleExec (B := .standard) w O
          (.branch (.eq 21 20) (.op (.const 16 1)) (.op (.const 21 0))) v6 v7 t7 [] := by
        by_cases hmeq : (r_idx >>> (l.1.val - m)) % 2 = l.2.toNat
        · refine ⟨2, by omega, ?_⟩
          simpa [v7, hmeq] using OracleExec.branch_pos (by simp [Cond.Holds, v6, v5, v4, v3, hmeq])
            (OracleExec.op (by simp [Op.eval, Data.put, h1_f]))
        · refine ⟨3, by omega, ?_⟩
          simpa [v7, hmeq] using OracleExec.branch_neg (by simp [Cond.Holds, v6, v5, v4, v3, hmeq])
            (OracleExec.op (by simp [Op.eval, Data.put, fits_zero]))
      obtain ⟨t7, ht7, ho7_ex⟩ := ho7
      let v8 := v7.set 13 (ptr + 1 + (j + 1))
      have ho8 : OracleExec (B := .standard) w O (.op (.bin .add 13 13 1)) v7 v8 1 [] := by
        have h13 : v7.regs 13 = ptr + 1 + j := by
          dsimp [v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv13]
        have h1' : v7.regs 1 = 1 := by
          dsimp [v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv1]
        simpa [v8, h13, h1', BinOp.eval, show ptr + 1 + j + 1 = ptr + 1 + (j + 1) by omega] using
          oracleExec_bin (w := w) (O := O) (x := v7) (f := .add) (d := 13) (i := 13) (j := 1)
            (by simpa [h13, h1', BinOp.eval] using Fits.of_le hw_mem (by omega))
      have hv7_16 : v7.regs 16 = (satFlagOf m r_idx c (j + 1)).toNat := by
        dsimp [v7]; rw [hsat_succ]; split_ifs with hmeq
        · simp [hge, hmatch_iff.mp hmeq]
        · have hne : ¬(decide ((r_idx >>> (l.1.val - m)) % 2 = 1) = l.2) :=
            fun h => hmeq (hmatch_iff.mpr h)
          have h16 : v6.regs 16 = (satFlagOf m r_idx c j).toNat := by
            simp [v6, v5, v4, v3, v2, v1, hv16]
          simp only [Data.set_regs, Function.update_of_ne (by decide : (16 : Fin 24) ≠ 21), h16,
            hge, true_and, decide_eq_false hne, Bool.or_false]
      obtain ⟨v', t_rest, hv', hv'0, hv'1, hv'2, hv'3, hv'4, hv'5, hv'6, hv'7, hv'8, hv'9,
        hv'14, hv'15, hv'10, hv'16, hv'17, hv'mem, hv'm1, hv'q, hv'kept, ht_rest⟩ :=
        ihr (j + 1) (by omega) v8 (by omega)
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv0])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv1])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv2])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv3])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv4])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv5])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv6])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv7])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv8])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv9])
          (by simp [v8])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv14])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv15])
          (by dsimp [v8, v7]; rw [hkept_eq]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv10])
          (by simp [v8, hv7_16])
          (by dsimp [v8, v7]; rw [hkept_eq]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hv17])
          (fun a ha => by
            dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hvmem a ha])
          (by dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hvm1])
          (fun i hi => by
            dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, hvq i hi])
          (fun i hi => by
            have hcongr : ∀ {α : Type} {l₁ l₂ : List α} (h : l₁ = l₂) (i : ℕ)
                (hi₁ : i < l₁.length), l₁[i]'hi₁ = l₂[i]'(h ▸ hi₁) := by
              rintro _ _ _ rfl _ _; rfl
            have hk : v8.mem (qPtr + 1 + i) = litCode ((satKeptOf m c j)[i]'(hkept_eq ▸ hi)) := by
              have h := hvkept i (hkept_eq ▸ hi)
              dsimp [v8, v7]; split_ifs <;> simp [v6, v5, v4, v3, v2, v1, h]
            rw [hk, hcongr hkept_eq i hi])
          hq_gt
      refine ⟨v', _,
        OracleExec.loop_iter hcond_l
          (lo1.seq (lo2.seq (lo3.seq ((OracleExec.branch_neg hc_lm
            (o4.seq (o5.seq (o6.seq ho7_ex)))).seq ho8)))) hv',
        hv'0, hv'1, hv'2, hv'3, hv'4, hv'5, hv'6, hv'7, hv'8, hv'9, hv'14, hv'15, hv'10, hv'16,
        hv'17, hv'mem, hv'm1, hv'q, hv'kept, by omega⟩

private theorem encodeClauses_restrictCNF_append_singleton {n : ℕ} (m r : ℕ)
    (ψ : CNF (Fin n)) (c : Clause (Fin n)) :
    encodeClauses (restrictCNF m r (ψ ++ [c])) =
      match restrictClause m r c with
      | none => encodeClauses (restrictCNF m r ψ)
      | some c' => encodeClauses (restrictCNF m r ψ) ++ encodeClause c' := by
  unfold restrictCNF
  rw [List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases restrictClause m r c with
  | none => simp [encodeClauses]
  | some c' => simp [encodeClauses]

private theorem encodeClause_getElem_succ {n : ℕ} (c : Clause (Fin n)) (i : ℕ)
    (hi : i < (encodeClause c).length) (hne : i ≠ 0) :
    (encodeClause c)[i]'hi =
      litCode (c[i - 1]'(by rw [length_encodeClause] at hi; omega)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
  simp only [encodeClause_eq, List.getElem_cons_succ, List.getElem_map, Nat.succ_sub_one]

private theorem satClauseLoop_exec {w n m diff r_idx L d8 : ℕ}
    {O : List ℕ → Bool} {x : FinCNF} {x0 : Data 24} {φ : CNF (Fin n)}
    (hx : x = ⟨n, φ⟩) (hL : L = (encFinCNF x).length)
    (hx0 : x0 = Data.init (encFinCNF x))
    (hr_lt : r_idx < 2 ^ diff) (hm_le : m ≤ n)
    (hw_pow : Fits w (2 ^ diff)) (hw_mem : Fits w (2 * L + 2)) (hw_n : Fits w (2 * n + 2))
    (h1_f : Fits w 1) :
    ∀ (ψ_pre ψ_rem : CNF (Fin n)) (ptr qPtr : ℕ) (u : Data 24),
      φ = ψ_pre ++ ψ_rem →
      ptr = 2 + (encodeClauses ψ_pre).length →
      qPtr = L + 2 + (encodeClauses (restrictCNF m r_idx ψ_pre)).length →
      u.regs 0 = 0 → u.regs 1 = 1 → u.regs 2 = L → u.regs 3 = n → u.regs 4 = L + 1 →
      u.regs 5 = m → u.regs 6 = diff → u.regs 7 = 2 ^ diff → u.regs 8 = d8 →
      u.regs 9 = r_idx → u.regs 10 = qPtr → u.regs 11 = ptr →
      (∀ a ≤ L, u.mem a = x0.mem a) → u.mem (L + 1) = m →
      (∀ i (hi : i < (encodeClauses (restrictCNF m r_idx ψ_pre)).length),
        u.mem (L + 2 + i) = (encodeClauses (restrictCNF m r_idx ψ_pre))[i]'hi) →
      ∃ (v : Data 24) (t_cl : ℕ),
        OracleExec w O (.loop (.lt 11 4) satClauseStep) u v t_cl [] ∧
        v.regs 0 = 0 ∧ v.regs 1 = 1 ∧ v.regs 2 = L ∧ v.regs 3 = n ∧ v.regs 4 = L + 1 ∧
        v.regs 5 = m ∧ v.regs 6 = diff ∧ v.regs 7 = 2 ^ diff ∧ v.regs 8 = d8 ∧
        v.regs 9 = r_idx ∧ v.regs 10 = L + 2 + (encodeClauses (restrictCNF m r_idx φ)).length ∧
        (∀ a ≤ L, v.mem a = x0.mem a) ∧ v.mem (L + 1) = m ∧
        (∀ i (hi : i < (encodeClauses (restrictCNF m r_idx φ)).length),
          v.mem (L + 2 + i) = (encodeClauses (restrictCNF m r_idx φ))[i]'hi) ∧
        t_cl ≤ 16 * (encodeClauses ψ_rem).length + 2 := by
  have hL_eq : L = (encodeClauses φ).length + 1 := by simp [hL, hx, encFinCNF, encode]
  intro ψ_pre ψ_rem
  induction ψ_rem generalizing ψ_pre with
  | nil =>
    intro ptr qPtr u hφ hptr hqPtr hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7 hu8 hu9 hu10 hu11
      humem hum1 huq
    have hφ' : ψ_pre = φ := by simpa using hφ.symm
    have hptr_eq : ptr = L + 1 := by rw [hφ'] at hptr; omega
    have hstop : ¬(Cond.lt 11 4).Holds u := by simp [Cond.Holds, hu11, hu4, hptr_eq]
    exact ⟨u, 2, OracleExec.loop_exit hstop, hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9,
      by rw [hu10, hqPtr, hφ'], humem, hum1, by simpa [hφ'] using huq, by omega⟩
  | cons c ψ_rem ih_cl =>
    intro ptr qPtr u hφ hptr hqPtr hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7 hu8 hu9 hu10 hu11
      humem hum1 huq
    have hlen_c_le : c.length + 1 + (encodeClauses ψ_rem).length +
        (encodeClauses ψ_pre).length = L - 1 := by
      have h1 : (encodeClauses φ).length =
          (encodeClauses ψ_pre).length + (c.length + 1 + (encodeClauses ψ_rem).length) := by
        rw [hφ]; simp [encodeClauses, length_encodeClause]
      omega
    have hptr_lt : ptr < L + 1 := by omega
    have hqPtr_le : qPtr ≤ 2 * L + 1 := by
      have := length_encodeClauses_restrictCNF_le m r_idx ψ_pre; omega
    have hcond_cl : (Cond.lt 11 4).Holds u := by simp [Cond.Holds, hu11, hu4, hptr_lt]
    have hmem_cLen : u.mem ptr = c.length := by
      rw [humem ptr (by omega)]
      have hget : (encodeClauses φ)[(encodeClauses ψ_pre).length]? = some c.length := by
        rw [hφ]; simp [encodeClauses, encodeClause_eq]
      rw [show ptr = ((encodeClauses ψ_pre).length + 1) + 1 by omega]
      simp only [hx0, hx, Data.init_mem_succ, encFinCNF, Function.Embedding.coeFn_mk, encode]
      simpa [List.getD_eq_getElem?_getD] using congrArg (fun o => o.getD 0) hget
    have hmem_lit : ∀ j (hj : j < c.length), x0.mem (ptr + 1 + j) = litCode (c[j]) := by
      intro j hj
      have hget : (encodeClauses φ)[(encodeClauses ψ_pre).length + 1 + j]? =
          some (litCode c[j]) := by
        rw [hφ]
        have h1 : encodeClauses (ψ_pre ++ c :: ψ_rem) =
            encodeClauses ψ_pre ++ (c.length :: c.map litCode ++ encodeClauses ψ_rem) := by
          simp [encodeClauses, encodeClause_eq]
        rw [h1, List.getElem?_append_right (by omega)]
        have h2 : (encodeClauses ψ_pre).length + 1 + j - (encodeClauses ψ_pre).length =
          j + 1 := by omega
        rw [h2, List.getElem?_append_left (by simp; omega), List.getElem?_cons_succ,
          List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]
      rw [show ptr + 1 + j = ((encodeClauses ψ_pre).length + 1 + j + 1) + 1 by omega]
      simp only [hx0, hx, Data.init_mem_succ, encFinCNF, Function.Embedding.coeFn_mk, encode]
      simpa [List.getD_eq_getElem?_getD] using congrArg (fun o => o.getD 0) hget
    let u1 := u.set 12 c.length; let u2 := u1.set 13 (ptr + 1)
    let u3 := u2.set 14 (ptr + 1 + c.length); let u4 := u3.set 15 qPtr
    let u5 := u4.set 10 (qPtr + 1); let u6 := u5.set 16 0; let u7 := u6.set 17 0
    have uo1 : OracleExec (B := .standard) w O (.op (.load 12 11)) u u1 1 [] :=
      OracleExec.op (by simp [Op.eval, u1, hu11, hmem_cLen])
    have uo2 : OracleExec (B := .standard) w O (.op (.bin .add 13 11 1)) u1 u2 1 [] := by
      simpa [u2, u1, hu11, hu1, BinOp.eval] using
        oracleExec_bin (w := w) (O := O) (x := u1) (f := .add) (d := 13) (i := 11) (j := 1)
          (by simpa [u1, hu11, hu1, BinOp.eval] using Fits.of_le hw_mem (by omega))
    have uo3 : OracleExec (B := .standard) w O (.op (.bin .add 14 13 12)) u2 u3 1 [] := by
      simpa [u3, u2, u1, BinOp.eval] using
        oracleExec_bin (w := w) (O := O) (x := u2) (f := .add) (d := 14) (i := 13) (j := 12)
          (by simpa [u2, u1, BinOp.eval] using Fits.of_le hw_mem (by omega))
    have uo4 : OracleExec (B := .standard) w O (.op (.copy 15 10)) u3 u4 1 [] :=
      OracleExec.op (by simp [Op.eval, u4, u3, u2, u1, hu10])
    have uo5 : OracleExec (B := .standard) w O (.op (.bin .add 10 10 1)) u4 u5 1 [] := by
      simpa [u5, u4, u3, u2, u1, hu10, hu1, BinOp.eval] using
        oracleExec_bin (w := w) (O := O) (x := u4) (f := .add) (d := 10) (i := 10) (j := 1)
          (by simpa [u4, u3, u2, u1, hu10, hu1, BinOp.eval] using Fits.of_le hw_mem (by omega))
    have uo6 : OracleExec (B := .standard) w O (.op (.const 16 0)) u5 u6 1 [] :=
      OracleExec.op (by simp [Op.eval, Data.put, fits_zero, u6])
    have uo7 : OracleExec (B := .standard) w O (.op (.const 17 0)) u6 u7 1 [] :=
      OracleExec.op (by simp [Op.eval, Data.put, fits_zero, u7])
    have hq_c_le : qPtr + 1 + c.length ≤ 2 * L + 2 := by
      have := length_encodeClauses_restrictCNF_le m r_idx ψ_pre; omega
    obtain ⟨v_l, t_l, hv_l, hvl0, hvl1, hvl2, hvl3, hvl4, hvl5, hvl6, hvl7, hvl8, hvl9,
      hvl14, hvl15, hvl10, hvl16, hvl17, hvlmem, hvlm1, hvlq, hvlkept, htl_le⟩ :=
      satLitLoop_exec (O := O) (d8 := d8) (c := c) (ψ_pre := ψ_pre) hr_lt hm_le hw_pow hw_mem
        hw_n h1_f hptr_lt (by omega) hqPtr_le hq_c_le (by omega) hmem_lit 0 u7 (Nat.zero_le _)
        (by simp [u7, u6, u5, u4, u3, u2, u1, hu0]) (by simp [u7, u6, u5, u4, u3, u2, u1, hu1])
        (by simp [u7, u6, u5, u4, u3, u2, u1, hu2]) (by simp [u7, u6, u5, u4, u3, u2, u1, hu3])
        (by simp [u7, u6, u5, u4, u3, u2, u1, hu4]) (by simp [u7, u6, u5, u4, u3, u2, u1, hu5])
        (by simp [u7, u6, u5, u4, u3, u2, u1, hu6]) (by simp [u7, u6, u5, u4, u3, u2, u1, hu7])
        (by simp [u7, u6, u5, u4, u3, u2, u1, hu8]) (by simp [u7, u6, u5, u4, u3, u2, u1, hu9])
        (by simp [u7, u6, u5, u4, u3, u2]) (by simp [u7, u6, u5, u4, u3])
        (by simp [u7, u6, u5, u4]) (by simp [u7, u6, u5, satKeptOf])
        (by simp [u7, u6, satFlagOf]) (by simp [u7, satKeptOf])
        (fun a ha => by simp [u7, u6, u5, u4, u3, u2, u1, humem a ha])
        (by simp [u7, u6, u5, u4, u3, u2, u1, hum1])
        (fun i hi => by simp [u7, u6, u5, u4, u3, u2, u1, huq i hi])
        (fun i hi => by simp [satKeptOf] at hi) (fun i hi => by omega)
    have hrc_eq : restrictClause m r_idx c =
        if satFlagOf m r_idx c c.length then none else some (satKeptOf m c c.length) := by
      simp [restrictClause, satFlagOf, satKeptOf]
    have hnext_φ : φ = (ψ_pre ++ [c]) ++ ψ_rem := by simp [hφ]
    have hnext_ptr : ptr + 1 + c.length = 2 + (encodeClauses (ψ_pre ++ [c])).length := by
      simp [hptr, encodeClauses, length_encodeClause]; omega
    let v_c := if satFlagOf m r_idx c c.length = true then v_l.set 10 qPtr
      else v_l.write qPtr (satKeptOf m c c.length).length
    have hbr_c : ∃ t_bc ≤ 3, OracleExec (B := .standard) w O
        (.branch (.eq 16 1) (.op (.copy 10 15)) (.op (.store 15 17))) v_l v_c t_bc [] := by
      by_cases hsat : satFlagOf m r_idx c c.length = true
      · refine ⟨2, by omega, ?_⟩
        simpa [v_c, hsat, hvl15] using OracleExec.branch_pos (by simp [Cond.Holds, hvl16,
          hvl1, hsat]) (OracleExec.op (by simp [Op.eval, hvl15]))
      · refine ⟨3, by omega, ?_⟩
        simpa [v_c, hsat, hvl15, hvl17] using OracleExec.branch_neg (by simp [Cond.Holds,
          hvl16, hvl1, hsat]) (OracleExec.op (by simp [Op.eval, hvl15, hvl17]))
    obtain ⟨t_bc, ht_bc, hbr_c_ex⟩ := hbr_c
    let v_next := v_c.set 11 (ptr + 1 + c.length)
    have ho_next : OracleExec (B := .standard) w O (.op (.copy 11 14)) v_c v_next 1 [] :=
      OracleExec.op (by
        have h14 : v_c.regs 14 = ptr + 1 + c.length := by
          dsimp [v_c]; split_ifs <;> simp [hvl14]
        simp [Op.eval, v_next, h14])
    have hvc_state : v_c.regs 10 =
        L + 2 + (encodeClauses (restrictCNF m r_idx (ψ_pre ++ [c]))).length ∧
        (∀ a ≤ L, v_c.mem a = x0.mem a) ∧ v_c.mem (L + 1) = m ∧
        ∀ i (hi : i < (encodeClauses (restrictCNF m r_idx (ψ_pre ++ [c]))).length),
          v_c.mem (L + 2 + i) =
            (encodeClauses (restrictCNF m r_idx (ψ_pre ++ [c])))[i]'hi := by
      rw [encodeClauses_restrictCNF_append_singleton, hrc_eq]
      dsimp [v_c]
      split_ifs with hsat
      · exact ⟨by simp [hqPtr], fun a ha => by simp [hvlmem a ha], hvlm1,
          fun i hi => by simpa using hvlq i hi⟩
      · simp only [List.length_append, length_encodeClause]
        refine ⟨by simp [hvl10, hqPtr]; omega,
          fun a ha => by rw [Data.write_mem, Function.update_of_ne (by omega)]; exact hvlmem a ha,
          by rw [Data.write_mem, Function.update_of_ne (by omega)]; exact hvlm1,
          fun i hi => ?_⟩
        rw [Data.write_mem]
        by_cases hi1 : i < (encodeClauses (restrictCNF m r_idx ψ_pre)).length
        · rw [Function.update_of_ne (by omega), hvlq i hi1, List.getElem_append_left hi1]
        · by_cases hi2 : i = (encodeClauses (restrictCNF m r_idx ψ_pre)).length
          · subst hi2
            have heq : L + 2 + (encodeClauses (restrictCNF m r_idx ψ_pre)).length = qPtr := by
              omega
            rw [heq, Function.update_self, List.getElem_append_right (le_refl _)]
            simp [encodeClause_eq]
          · rw [Function.update_of_ne (by omega), List.getElem_append_right (by omega),
              encodeClause_getElem_succ _ _ _ (by omega)]
            have heq_addr : L + 2 + i =
                qPtr + 1 + (i - (encodeClauses (restrictCNF m r_idx ψ_pre)).length - 1) := by
              omega
            rw [heq_addr]; exact hvlkept _ (by omega)
    have hvc_r : ∀ k : Fin 24, k ≠ 10 → v_c.regs k = v_l.regs k := fun k hk => by
      dsimp [v_c]; split_ifs <;> simp [Data.set_regs, Function.update_of_ne hk]
    obtain ⟨v_end, t_end, hv_end, hve0, hve1, hve2, hve3, hve4, hve5, hve6, hve7, hve8, hve9,
      hve10, hvemem, hvem1, hveq, hte_le⟩ :=
      ih_cl (ψ_pre ++ [c]) (ptr + 1 + c.length) (L + 2 +
        (encodeClauses (restrictCNF m r_idx (ψ_pre ++ [c]))).length)
        v_next hnext_φ hnext_ptr rfl
        (by simp [v_next, hvc_r 0 (by decide), hvl0])
        (by simp [v_next, hvc_r 1 (by decide), hvl1])
        (by simp [v_next, hvc_r 2 (by decide), hvl2])
        (by simp [v_next, hvc_r 3 (by decide), hvl3])
        (by simp [v_next, hvc_r 4 (by decide), hvl4])
        (by simp [v_next, hvc_r 5 (by decide), hvl5])
        (by simp [v_next, hvc_r 6 (by decide), hvl6])
        (by simp [v_next, hvc_r 7 (by decide), hvl7])
        (by simp [v_next, hvc_r 8 (by decide), hvl8])
        (by simp [v_next, hvc_r 9 (by decide), hvl9])
        (by simp [v_next, hvc_state.1]) (by simp [v_next])
        (fun a ha => by simp [v_next, hvc_state.2.1 a ha]) (by simp [v_next, hvc_state.2.2.1])
        (fun i hi => by simp [v_next, hvc_state.2.2.2 i hi])
    have hcl_time :
        1 + (1 + (1 + (1 + (1 + (1 + (1 + (t_l + (t_bc + 1)))))))) + t_end + 2 ≤
          16 * (encodeClauses (c :: ψ_rem)).length + 2 := by
      simp only [encodeClauses_cons, List.length_append, length_encodeClause]; omega
    refine ⟨v_end, _,
      OracleExec.loop_iter hcond_cl
        (uo1.seq (uo2.seq (uo3.seq (uo4.seq (uo5.seq (uo6.seq
          (uo7.seq (hv_l.seq (hbr_c_ex.seq ho_next))))))))) hv_end,
      hve0, hve1, hve2, hve3, hve4, hve5, hve6, hve7, hve8, hve9, hve10, hvemem, hvem1, hveq,
      hcl_time⟩

/-- Execution specification of `satBranchOracleCode`: on input `x = ⟨n, φ⟩` and `1 ≤ b`, produces
exactly the `2^{n - m}` restricted queries `encFinCNF ⟨m, restrictCNF m r φ⟩` (`m = n / b`) in
time `≤ 2^(n - m) * (20 * L + 25) + 20`, outputting `1` iff `x ∈ FinSAT`. -/
theorem satBranchOracleCode_exec {b w : ℕ} {O : List ℕ → Bool} {x : FinCNF}
    (_hb : 1 ≤ b)
    (hO : ∀ r < 2 ^ (x.1 - x.1 / b),
      O (encFinCNF ⟨x.1 / b, restrictCNF (x.1 / b) r x.2⟩) =
        @decide ((restrictCNF (x.1 / b) r x.2).Satisfiable) (Classical.propDecidable _))
    (hw_b : Fits w b)
    (hw_pow : Fits w (2 ^ (x.1 - x.1 / b)))
    (hw_mem : Fits w (2 * (encFinCNF x).length + 2))
    (hw_n : Fits w (2 * x.1 + 2)) :
    ∃ (y : Data 24) (t : ℕ) (qs : List (List ℕ)),
      OracleExec w O (satBranchOracleCode b) (.init (encFinCNF x)) y t qs ∧
      y.regs 8 ≤ 1 ∧ (y.regs 8 = 1 ↔ x ∈ FinSAT) ∧
      qs = (List.range (2 ^ (x.1 - x.1 / b))).map
        (fun r => encFinCNF ⟨x.1 / b, restrictCNF (x.1 / b) r x.2⟩) ∧
      t ≤ 2 ^ (x.1 - x.1 / b) * (20 * (encFinCNF x).length + 25) + 20 := by
  rcases x with ⟨n, φ⟩
  dsimp only at hO hw_pow hw_n ⊢
  set L := (encFinCNF ⟨n, φ⟩).length
  set m := n / b
  set diff := n - m
  have hm_le : m ≤ n := Nat.div_le_self n b
  have hL_pos : 1 ≤ L := encFinCNF_length_pos ⟨n, φ⟩
  have h1_f : Fits w 1 := Fits.of_le hw_mem (by omega)
  have h2_f : Fits w 2 := Fits.of_le hw_mem (by omega)
  have hL1_f : Fits w (L + 1) := Fits.of_le hw_mem (by omega)
  have hm_f : Fits w m := Fits.of_le hw_n (by omega)
  have hdiff_f : Fits w diff := Fits.of_le hw_n (le_trans (Nat.sub_le n m) (by omega))
  -- Execute setup
  let x0 : Data 24 := .init (encFinCNF ⟨n, φ⟩)
  have hmem0 : x0.mem 0 = L := by simp [x0, Data.init_mem_zero, L]
  have hmem1 : x0.mem 1 = n := by
    change x0.mem (0 + 1) = n; simp [x0, Data.init_mem_succ, encFinCNF, encode]
  let s1 := x0.set 0 0; let s2 := s1.set 1 1; let s3 := s2.set 2 L; let s4 := s3.set 3 n
  let s5 := s4.set 4 (L + 1); let s6 := s5.set 21 b; let s7 := s6.set 5 m
  let s8 := s7.set 6 diff; let s9 := s8.set 7 (2 ^ diff); let s10 := s9.set 8 0; let s11 :=
    s10.set 9 0
  have hsetup : OracleExec w O (satBranchSetup b) x0 s11 11 [] := by
    have o1 : OracleExec (B := .standard) w O (.op (.const 0 0)) x0 s1 1 [] :=
      OracleExec.op (by simp [Op.eval, Data.put, fits_zero, s1])
    have o2 : OracleExec (B := .standard) w O (.op (.const 1 1)) s1 s2 1 [] :=
      OracleExec.op (by simp [Op.eval, Data.put, h1_f, s2])
    have o3 : OracleExec (B := .standard) w O (.op (.load 2 0)) s2 s3 1 [] :=
      OracleExec.op (by simp [Op.eval, s3, s2, s1, hmem0])
    have o4 : OracleExec (B := .standard) w O (.op (.load 3 1)) s3 s4 1 [] :=
      OracleExec.op (by simp [Op.eval, s4, s3, s2, s1, hmem1])
    have o5 : OracleExec (B := .standard) w O (.op (.bin .add 4 2 1)) s4 s5 1 [] := by
      simpa [s5, s4, s3, s2, BinOp.eval] using
        oracleExec_bin (w := w) (O := O) (x := s4) (f := .add) (d := 4) (i := 2) (j := 1)
          (by simpa [s4, s3, s2, BinOp.eval] using hL1_f)
    have o6 : OracleExec (B := .standard) w O (.op (.const 21 b)) s5 s6 1 [] :=
      OracleExec.op (by simp [Op.eval, Data.put, hw_b, s6])
    have o7 : OracleExec (B := .standard) w O (.op (.bin .div 5 3 21)) s6 s7 1 [] := by
      simpa [s7, s6, s5, s4, BinOp.eval, m] using
        oracleExec_bin (w := w) (O := O) (x := s6) (f := .div) (d := 5) (i := 3) (j := 21)
          (by simpa [s6, s5, s4, BinOp.eval, m] using hm_f)
    have o8 : OracleExec (B := .standard) w O (.op (.bin .sub 6 3 5)) s7 s8 1 [] := by
      simpa [s8, s7, s6, s5, s4, BinOp.eval, diff] using
        oracleExec_bin (w := w) (O := O) (x := s7) (f := .sub) (d := 6) (i := 3) (j := 5)
          (by simpa [s7, s6, s5, s4, BinOp.eval, diff] using hdiff_f)
    have o9 : OracleExec (B := .standard) w O (.op (.bin .shiftLeft 7 1 6)) s8 s9 1 [] := by
      simpa [s9, s8, s7, s6, s5, s4, s3, s2, BinOp.eval, Nat.shiftLeft_eq] using
        oracleExec_bin (w := w) (O := O) (x := s8) (f := .shiftLeft) (d := 7) (i := 1) (j := 6)
          (by simpa [s8, s7, s6, s5, s4, s3, s2, BinOp.eval, Nat.shiftLeft_eq] using hw_pow)
    have o10 : OracleExec (B := .standard) w O (.op (.const 8 0)) s9 s10 1 [] :=
      OracleExec.op (by simp [Op.eval, Data.put, fits_zero, s10])
    have o11 : OracleExec (B := .standard) w O (.op (.const 9 0)) s10 s11 1 [] :=
      OracleExec.op (by simp [Op.eval, Data.put, fits_zero, s11])
    exact o1.seq (o2.seq (o3.seq (o4.seq (o5.seq (o6.seq
      (o7.seq (o8.seq (o9.seq (o10.seq o11)))))))))
  -- Helper: clause-scanning loop writes encodeClauses (restrictCNF m r_idx φ) at [L+2, L+2+len)
  have hbranch : ∀ (r_idx : ℕ) (d : Data 24),
      r_idx ≤ 2 ^ diff →
      d.regs 0 = 0 → d.regs 1 = 1 → d.regs 2 = L → d.regs 3 = n → d.regs 4 = L + 1 →
      d.regs 5 = m → d.regs 6 = diff → d.regs 7 = 2 ^ diff → d.regs 9 = r_idx →
      d.regs 8 ≤ 1 →
      (d.regs 8 = 1 ↔ ∃ r < r_idx, (restrictCNF m r φ).Satisfiable) →
      (∀ a ≤ L, d.mem a = x0.mem a) →
      ∃ (y : Data 24) (t : ℕ) (qs : List (List ℕ)),
        OracleExec w O (.loop (.lt 9 7) satBranchBody) d y t qs ∧
        y.regs 8 ≤ 1 ∧ (y.regs 8 = 1 ↔ ∃ r < 2 ^ diff, (restrictCNF m r φ).Satisfiable) ∧
        qs = ((List.range (2 ^ diff)).drop r_idx).map
          (fun r => encFinCNF ⟨m, restrictCNF m r φ⟩) ∧
        t ≤ (2 ^ diff - r_idx) * (20 * L + 25) + 2 := by
    intro r_idx
    generalize hk_def : 2 ^ diff - r_idx = k
    induction k generalizing r_idx with
    | zero =>
      intro d hr_le _ _ _ _ _ _ _ hd7 hd9 hd8le hd8iff _
      have hr_eq : r_idx = 2 ^ diff := by omega
      subst hr_eq
      have hstop : ¬(Cond.lt 9 7).Holds d := by simp [Cond.Holds, hd9, hd7]
      refine ⟨d, 2, [], OracleExec.loop_exit hstop, hd8le, hd8iff, ?_, by omega⟩
      simp [List.drop_eq_nil_of_le]
    | succ k ih =>
      intro d hr_le hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd9 hd8le hd8iff hdmem
      have hr_lt : r_idx < 2 ^ diff := by omega
      have hcond : (Cond.lt 9 7).Holds d := by simp [Cond.Holds, hd9, hd7, hr_lt]
      -- Execute one iteration of branchBody
      let d1 := d.write (L + 1) m; let d2 := d1.set 10 (L + 2); let d3 := d2.set 11 2
      have bo1 : OracleExec (B := .standard) w O (.op (.store 4 5)) d d1 1 [] :=
        OracleExec.op (by simp [Op.eval, d1, hd4, hd5])
      have bo2 : OracleExec (B := .standard) w O (.op (.bin .add 10 4 1)) d1 d2 1 [] := by
        simpa [d2, d1, hd4, hd1, BinOp.eval, show L + 1 + 1 = L + 2 by omega] using
          oracleExec_bin (w := w) (O := O) (x := d1) (f := .add) (d := 10) (i := 4) (j := 1)
            (by simpa [d1, hd4, hd1, BinOp.eval] using Fits.of_le hw_mem (by omega))
      have bo3 : OracleExec (B := .standard) w O (.op (.const 11 2)) d2 d3 1 [] :=
        OracleExec.op (by simp [Op.eval, Data.put, h2_f, d3])
      obtain ⟨d4, t_cl, hd4_ex, hd4_0, hd4_1, hd4_2, hd4_3, hd4_4, hd4_5, hd4_6, hd4_7, hd4_8,
        hd4_9, hd4_10, hd4_mem, hd4_m1, hd4_q, ht_cl⟩ :=
        satClauseLoop_exec (L := L) (m := m) (diff := diff) (x0 := x0) (O := O) (d8 := d.regs 8)
          rfl rfl rfl hr_lt hm_le hw_pow hw_mem hw_n h1_f [] φ 2 (L + 2) d3
          (by simp) (by simp [encodeClauses_nil]) (by simp [restrictCNF, encodeClauses_nil])
          (by simp [d3, d2, d1, hd0]) (by simp [d3, d2, d1, hd1]) (by simp [d3, d2, d1, hd2])
          (by simp [d3, d2, d1, hd3]) (by simp [d3, d2, d1, hd4]) (by simp [d3, d2, d1, hd5])
          (by simp [d3, d2, d1, hd6]) (by simp [d3, d2, d1, hd7]) (by simp [d3, d2, d1])
          (by simp [d3, d2, d1, hd9]) (by simp [d3, d2]) (by simp [d3])
          (fun a ha => by simp [d3, d2, d1, Function.update_of_ne (show a ≠ L + 1 by omega),
            hdmem a ha])
          (by simp [d3, d2, d1]) (fun i hi => by simp [restrictCNF, encodeClauses_nil] at hi)
      set q_cur := encFinCNF ⟨m, restrictCNF m r_idx φ⟩
      have hq_len : q_cur.length = (encodeClauses (restrictCNF m r_idx φ)).length + 1 := by
        simp [q_cur, encFinCNF, encode]
      have hq_len_le : q_cur.length ≤ L := by
        have := length_encodeClauses_restrictCNF_le m r_idx φ
        have hL_eq : L = (encodeClauses φ).length + 1 := by simp [L, encFinCNF, encode]
        omega
      let d5 := d4.set 22 q_cur.length
      have ho5 : OracleExec (B := .standard) w O (.op (.bin .sub 22 10 4)) d4 d5 1 [] := by
        simpa [d5, hd4_10, hd4_4, hq_len, BinOp.eval,
          show L + 2 + (encodeClauses (restrictCNF m r_idx φ)).length - (L + 1) =
            (encodeClauses (restrictCNF m r_idx φ)).length + 1 by omega] using
          oracleExec_bin (w := w) (O := O) (x := d4) (f := .sub) (d := 22) (i := 10) (j := 4)
            (by simpa [hd4_10, hd4_4, BinOp.eval] using Fits.of_le hw_mem (by omega))
      have hq_mem : (List.range q_cur.length).map (fun i => d5.mem (L + 1 + i)) = q_cur := by
        refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
        have hi : i < q_cur.length := by simpa using hi₁
        simp only [List.getElem_map, List.getElem_range, d5, Data.set_mem]
        cases i with
        | zero => simp [q_cur, encFinCNF, encode, hd4_m1]
        | succ i =>
          have hi' : i < (encodeClauses (restrictCNF m r_idx φ)).length := by omega
          have heq : L + 1 + (i + 1) = L + 2 + i := by omega
          rw [heq, hd4_q i hi']; simp [q_cur, encFinCNF, encode]
      let d6 := d5.set 23 (O q_cur).toNat
      have ho6 : OracleExec (B := .standard) w O
          (.query 23 4 22) d5 d6 (q_cur.length + 1) [q_cur] := by
        have hbl : Fits w (d5.regs 4 + d5.regs 22) := by
          simp only [d5, Data.set_regs, Function.update_of_ne (by decide : (4 : Fin 24) ≠ 22),
            Function.update_self, hd4_4]
          exact Fits.of_le hw_mem (by omega)
        have hq_ex := OracleExec.query (B := .standard) (w := w) (O := O) (dst := 23) (base := 4)
          (len := 22) (x := d5) h1_f hbl
        have hq_r : ((List.range (d5.regs 22)).map fun i => d5.mem (d5.regs 4 + i)) = q_cur := by
          simpa [d5, hd4_4] using hq_mem
        have hq_len22 : d5.regs 22 = q_cur.length := by simp [d5]
        rw [hq_r, hq_len22] at hq_ex
        exact hq_ex
      let d7 := if O q_cur = true then d6.set 8 1 else d6.set 21 0
      have ho7 : ∃ t7 ≤ 3, OracleExec (B := .standard) w O
          (.branch (.eq 23 1) (.op (.const 8 1)) (.op (.const 21 0))) d6 d7 t7 [] := by
        by_cases hOq : O q_cur = true
        · refine ⟨2, by omega, ?_⟩
          simpa [d7, hOq] using OracleExec.branch_pos (by simp [Cond.Holds, d6, d5, hd4_1,
            hOq]) (OracleExec.op (by simp [Op.eval, Data.put, h1_f]))
        · refine ⟨3, by omega, ?_⟩
          have hOf : O q_cur = false := Bool.eq_false_iff.mpr hOq
          simpa [d7, hOq] using OracleExec.branch_neg (by simp [Cond.Holds, d6, d5, hd4_1,
            hOf]) (OracleExec.op (by simp [Op.eval, Data.put, fits_zero]))
      obtain ⟨t7, ht7, ho7_ex⟩ := ho7
      let d8 := d7.set 9 (r_idx + 1)
      have ho8 : OracleExec (B := .standard) w O (.op (.bin .add 9 9 1)) d7 d8 1 [] := by
        have h9' : d7.regs 9 = r_idx := by dsimp [d7]; split_ifs <;> simp [d6, d5, hd4_9]
        have h1' : d7.regs 1 = 1 := by dsimp [d7]; split_ifs <;> simp [d6, d5, hd4_1]
        simpa [d8, h9', h1', BinOp.eval] using
          oracleExec_bin (w := w) (O := O) (x := d7) (f := .add) (d := 9) (i := 9) (j := 1)
            (by simpa [h9', h1', BinOp.eval] using Fits.of_le hw_pow (by omega))
      have hd8_8_le : d8.regs 8 ≤ 1 := by dsimp [d8, d7]; split_ifs <;> simp [d6, d5, hd4_8, hd8le]
      have hd8_8_iff : d8.regs 8 = 1 ↔ ∃ r < r_idx + 1, (restrictCNF m r φ).Satisfiable := by
        have hO_cur := hO r_idx hr_lt
        dsimp [d8, d7]; split_ifs with hOq
        · simp only [Data.set_regs, Function.update_of_ne (by decide : (8 : Fin 24) ≠ 9),
            Function.update_self, true_iff]
          rw [hO_cur, @decide_eq_true_eq _ (Classical.propDecidable _)] at hOq
          exact ⟨r_idx, by omega, hOq⟩
        · dsimp only [d6, d5]
          simp only [Data.set_regs, Function.update_of_ne (by decide : (8 : Fin 24) ≠ 9),
            Function.update_of_ne (by decide : (8 : Fin 24) ≠ 21),
            Function.update_of_ne (by decide : (8 : Fin 24) ≠ 23),
            Function.update_of_ne (by decide : (8 : Fin 24) ≠ 22), hd4_8, hd8iff]
          constructor
          · rintro ⟨r, hr, hsat⟩; exact ⟨r, by omega, hsat⟩
          · rintro ⟨r, hr, hsat⟩
            by_cases hreq : r = r_idx
            · subst hreq
              rw [hO_cur, @decide_eq_true_eq _ (Classical.propDecidable _)] at hOq
              exact absurd hsat hOq
            · exact ⟨r, by omega, hsat⟩
      have hk_next : 2 ^ diff - (r_idx + 1) = k := by
        rw [← Nat.sub_sub, hk_def, Nat.add_sub_cancel]
      obtain ⟨y, t_rest, qs_rest, hy, hy8le, hy8iff, hqs_rest, ht_rest⟩ :=
        ih (r_idx + 1) hk_next d8 (by omega)
          (by dsimp [d8, d7]; split_ifs <;> simp [d6, d5, hd4_0])
          (by dsimp [d8, d7]; split_ifs <;> simp [d6, d5, hd4_1])
          (by dsimp [d8, d7]; split_ifs <;> simp [d6, d5, hd4_2])
          (by dsimp [d8, d7]; split_ifs <;> simp [d6, d5, hd4_3])
          (by dsimp [d8, d7]; split_ifs <;> simp [d6, d5, hd4_4])
          (by dsimp [d8, d7]; split_ifs <;> simp [d6, d5, hd4_5])
          (by dsimp [d8, d7]; split_ifs <;> simp [d6, d5, hd4_6])
          (by dsimp [d8, d7]; split_ifs <;> simp [d6, d5, hd4_7])
          (by simp [d8]) hd8_8_le hd8_8_iff
          (fun a ha => by dsimp [d8, d7]; split_ifs <;> simp [d6, d5, hd4_mem a ha])
      have hqs_eq : [q_cur] ++ qs_rest =
        ((List.range (2 ^ diff)).drop r_idx).map (fun r => encFinCNF ⟨m, restrictCNF m r φ⟩) := by
        rw [hqs_rest]
        conv_rhs => rw [List.drop_eq_getElem_cons (by rw [List.length_range]; exact hr_lt),
          List.map_cons]
        simp [q_cur]
      have htime_step :
          1 + (1 + (1 + (t_cl + (1 + ((q_cur.length + 1) + (t7 + 1)))))) + t_rest + 2 ≤
            (k + 1) * (20 * L + 25) + 2 := by
        have hlen_φ : (encodeClauses φ).length ≤ L := by simp [L, encFinCNF, encode]
        rw [Nat.add_mul, Nat.one_mul]; omega
      refine ⟨y, _, [q_cur] ++ qs_rest, ?_, hy8le, hy8iff, hqs_eq, htime_step⟩
      have hstep_ex :=
        OracleExec.loop_iter hcond
          (bo1.seq (bo2.seq (bo3.seq (hd4_ex.seq (ho5.seq (ho6.seq (ho7_ex.seq ho8))))))) hy
      simpa only [satBranchBody, List.nil_append, List.append_nil] using hstep_ex
  obtain ⟨y, t_loop, qs, hloop, hy8le, hy8iff, hqs, ht_loop⟩ :=
    hbranch 0 s11 (Nat.zero_le _) (by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1])
      (by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2])
      (by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3])
      (by simp [s11, s10, s9, s8, s7, s6, s5, s4]) (by simp [s11, s10, s9, s8, s7, s6, s5])
      (by simp [s11, s10, s9, s8, s7]) (by simp [s11, s10, s9, s8]) (by simp [s11, s10, s9])
      (by simp [s11]) (by simp [s11, s10]) (by simp [s11, s10])
      (fun _ _ => by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1])
  rw [Nat.sub_zero] at ht_loop
  refine ⟨y, 11 + t_loop, qs,
    (by simpa only [satBranchOracleCode, List.nil_append] using hsetup.seq hloop),
    hy8le, ?_, by simpa using hqs, by omega⟩
  rw [hy8iff, FinSAT, Set.mem_ofPred_eq, satisfiable_iff_exists_restrictCNF hm_le]

/-! ### SAT and `k`-SAT Efficient Self-Reducibility -/

private theorem satBranch_fits {b n L w : ℕ} (hb : 2 ≤ b)
    (hw : logWidth (4 + b) (⌈(2 : ℝ) ^ n⌉₊ + L) ≤ w) :
    Fits w b ∧ Fits w (2 ^ (n - n / b)) ∧ Fits w (2 * L + 2) ∧ Fits w (2 * n + 2) := by
  have hlog_ge_n : n ≤ Nat.log 2 (⌈(2 : ℝ) ^ n⌉₊ + L) := by
    have h1 : 2 ^ n ≤ ⌈(2 : ℝ) ^ n⌉₊ + L := by
      have hc : (2 : ℝ) ^ n ≤ (⌈(2 : ℝ) ^ n⌉₊ : ℝ) := Nat.le_ceil _
      have hc' : 2 ^ n ≤ ⌈(2 : ℝ) ^ n⌉₊ := by exact_mod_cast hc
      omega
    exact Nat.le_log_of_pow_le Nat.one_lt_two h1
  have hlog_ge_L : Nat.log 2 L ≤ Nat.log 2 (⌈(2 : ℝ) ^ n⌉₊ + L) :=
    Nat.log_mono_right (Nat.le_add_left _ _)
  have hw_ge : (4 + b) * (Nat.log 2 (⌈(2 : ℝ) ^ n⌉₊ + L) + 1) ≤ w := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : b < 2 ^ (4 + b) := by
      have := Nat.lt_two_pow_self (n := b)
      have := Nat.pow_le_pow_right Nat.two_pos (show b ≤ 4 + b by omega)
      omega
    have h2 : 4 + b ≤ w := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hw_ge
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right Nat.two_pos h2)
  · have h4 : 4 * (n + 1) ≤ w :=
      le_trans (Nat.mul_le_mul (by omega : 4 ≤ 4 + b) (Nat.add_le_add_right hlog_ge_n 1)) hw_ge
    have hsub : n - n / b ≤ n := Nat.sub_le n _
    exact Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
  · have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two L
    have h1 : 2 * L + 2 < 2 ^ (Nat.log 2 L + 3) := by rw [pow_add]; norm_num; omega
    have : 4 * (Nat.log 2 L + 1) ≤ w :=
      le_trans (Nat.mul_le_mul (by omega : 4 ≤ 4 + b) (Nat.add_le_add_right hlog_ge_L 1)) hw_ge
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right Nat.two_pos (by omega))
  · have h1 : 2 * n + 2 < 2 ^ (n + 2) := by
      have := Nat.lt_two_pow_self (n := n); rw [pow_add]; norm_num; omega
    have : 4 * (n + 1) ≤ w :=
      le_trans (Nat.mul_le_mul (by omega : 4 ≤ 4 + b) (Nat.add_le_add_right hlog_ge_n 1)) hw_ge
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right Nat.two_pos (by omega))

private theorem satBranch_bounds {a_exp ε : ℝ} {n L t : ℕ}
    (ha_pos : 0 < a_exp) (hε : 0 < ε)
    (ht : t ≤ 2 ^ (n - n / (⌈1 / a_exp⌉₊ + 2)) * (20 * L + 25) + 20) :
    let b : ℕ := ⌈1 / a_exp⌉₊ + 2
    let m : ℕ := n / b
    let C : ℕ := 100 * 2 ^ b
    let d : ℝ := min (ε / (b : ℝ)) (1 / (2 * (b : ℝ)))
    (t : ℝ) ≤ (C : ℝ) * (((L + 1 : ℕ) : ℝ)) ^ 1 * ((2 : ℝ) ^ n) ^ (1 - d) +
      (C : ℝ) * (((L + 1 : ℕ) : ℝ)) ^ 1 ∧
    ((2 : ℝ) ^ (n - m)) * ((2 : ℝ) ^ m) ^ (1 - ε) ≤
      (C : ℝ) * (((L + 1 : ℕ) : ℝ)) ^ 1 * ((2 : ℝ) ^ n) ^ (1 - d) +
      (C : ℝ) * (((L + 1 : ℕ) : ℝ)) ^ 1 ∧
    (2 : ℝ) ^ m ≤ ((2 : ℝ) ^ n) ^ a_exp := by
  intro b m C d
  have hb_pos : 0 < b := by omega
  have hb_inv : 1 / (b : ℝ) ≤ a_exp := by
    have h1 : 1 / a_exp ≤ (b : ℝ) := by
      have := Nat.le_ceil (1 / a_exp); dsimp only [b]; push_cast; linarith
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ ha_pos).mp h1; linarith
  have hlt_mb : n < (m + 1) * b := by
    have := Nat.lt_div_mul_add hb_pos (a := n)
    have hmb : n / b * b + b = (m + 1) * b := by dsimp only [m]; ring
    omega
  have hdiv_ge : (n : ℝ) / (b : ℝ) - 1 ≤ (m : ℝ) := by
    have hr : (n : ℝ) < ((m : ℝ) + 1) * (b : ℝ) := by exact_mod_cast hlt_mb
    have := (div_lt_iff₀ (by positivity)).mpr hr; linarith
  have hdiv_le : (m : ℝ) ≤ (n : ℝ) / (b : ℝ) := Nat.cast_div_le
  have hpow_branch : ((2 : ℝ) ^ (n - m)) ≤ 2 * ((2 : ℝ) ^ n) ^ (1 - d) := by
    have h1 : ((n - m : ℕ) : ℝ) ≤ (n : ℝ) - ((n : ℝ) / (b : ℝ) - 1) := by
      rw [Nat.cast_sub (Nat.div_le_self n b)]; linarith
    have hd : d ≤ 1 / (2 * (b : ℝ)) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ (n : ℝ))
    have h3 : ((n - m : ℕ) : ℝ) ≤ (n : ℝ) * (1 - d) + 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) / (b : ℝ) := by positivity
      have hhalf : (n : ℝ) / (2 * (b : ℝ)) = ((n : ℝ) / (b : ℝ)) / 2 := by ring
      linarith [show (n : ℝ) * (1 / (2 * (b : ℝ))) = (n : ℝ) / (2 * (b : ℝ)) by ring]
    calc ((2 : ℝ) ^ (n - m)) = (2 : ℝ) ^ ((n - m : ℕ) : ℝ) := (Real.rpow_natCast 2 _).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (1 - d) + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
      _ = (2 : ℝ) ^ ((n : ℝ) * (1 - d)) * 2 := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
      _ = 2 * ((2 : ℝ) ^ n) ^ (1 - d) := by
        rw [← Real.rpow_natCast 2 n, ← Real.rpow_mul (by norm_num)]; ring
  have hL1 : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos L
  have h2p : (0 : ℝ) ≤ ((2 : ℝ) ^ n) ^ (1 - d) := Real.rpow_nonneg (by positivity) _
  refine ⟨?_, ?_, ?_⟩
  · have ht_r : (t : ℝ) ≤ ((2 : ℝ) ^ (n - m)) * (20 * (L : ℝ) + 25) + 20 := by exact_mod_cast ht
    have hC1 : (100 : ℝ) ≤ (C : ℝ) := by
      have : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      dsimp only [C]; exact_mod_cast (by omega : 100 ≤ 100 * 2 ^ b)
    have hstep1 : ((2 : ℝ) ^ (n - m)) * (20 * (L : ℝ) + 25) ≤
        2 * ((2 : ℝ) ^ n) ^ (1 - d) * (25 * ((L : ℝ) + 1)) :=
      mul_le_mul hpow_branch (by linarith) (by positivity) (by positivity)
    have hstep2 : 50 * ((L : ℝ) + 1) * ((2 : ℝ) ^ n) ^ (1 - d) ≤
        (C : ℝ) * ((L : ℝ) + 1) * ((2 : ℝ) ^ n) ^ (1 - d) := by
      have : 50 * ((L : ℝ) + 1) ≤ (C : ℝ) * ((L : ℝ) + 1) := by nlinarith
      exact mul_le_mul_of_nonneg_right this h2p
    rw [pow_one]; push_cast; nlinarith
  · have hexp_le : ((2 : ℝ) ^ (n - m)) * ((2 : ℝ) ^ m) ^ (1 - ε) ≤
        ((2 : ℝ) ^ b) * ((2 : ℝ) ^ n) ^ (1 - d) := by
      have hlhs : ((2 : ℝ) ^ (n - m)) * ((2 : ℝ) ^ m) ^ (1 - ε) =
        (2 : ℝ) ^ ((n : ℝ) - (m : ℝ) + (m : ℝ) * (1 - ε)) := by
        rw [← Real.rpow_natCast 2 (n - m), ← Real.rpow_natCast 2 m, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num), Nat.cast_sub (Nat.div_le_self n b)]
      have hrhs : ((2 : ℝ) ^ b) * ((2 : ℝ) ^ n) ^ (1 - d) =
        (2 : ℝ) ^ ((b : ℝ) + (n : ℝ) * (1 - d)) := by
        rw [← Real.rpow_natCast 2 b, ← Real.rpow_natCast 2 n, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num)]
      rw [hlhs, hrhs]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hd_le : d ≤ ε / (b : ℝ) := min_le_left _ _
      have hεm : (n : ℝ) * d ≤ ε * (m : ℝ) + (b : ℝ) := by
        have h1' : (n : ℝ) * d ≤ (n : ℝ) * (ε / (b : ℝ)) :=
          mul_le_mul_of_nonneg_left hd_le (by positivity)
        have h2' : (n : ℝ) * (ε / (b : ℝ)) = ε * ((n : ℝ) / (b : ℝ)) := by ring
        have h3' : ε * ((n : ℝ) / (b : ℝ)) ≤ ε * ((m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hε)
        by_cases hεb : ε ≤ (b : ℝ)
        · linarith
        · by_cases hm0 : m = 0
          · have hnb : n < b := by
              by_contra hge; push Not at hge
              have : 1 ≤ n / b := Nat.div_pos hge hb_pos; omega
            have hnr : (n : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_of_lt hnb
            have hd1 : d ≤ 1 := (min_le_right _ _).trans (div_le_one_of_le₀
              (by exact_mod_cast (by omega : 1 ≤ 2 * b)) (by positivity))
            have : 0 ≤ (n : ℝ) * (1 - d) := mul_nonneg (by positivity) (by linarith)
            nlinarith
          · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
            have hbm : (b : ℝ) * (m : ℝ) ≤ ε * (m : ℝ) :=
              mul_le_mul_of_nonneg_right (le_of_lt (not_le.mp hεb)) (by positivity)
            have hnbm : (n : ℝ) ≤ (b : ℝ) * (m : ℝ) + (b : ℝ) := by
              have hr : (n : ℝ) < ((m : ℝ) + 1) * (b : ℝ) := by exact_mod_cast hlt_mb
              linarith
            have hd1 : d ≤ 1 := (min_le_right _ _).trans (div_le_one_of_le₀
              (by exact_mod_cast (by omega : 1 ≤ 2 * b)) (by positivity))
            have : (n : ℝ) * d ≤ (n : ℝ) := by nlinarith
            linarith
      linarith
    have hC_ge : (2 : ℝ) ^ b ≤ (C : ℝ) := by
      dsimp only [C]; push_cast
      have : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num); nlinarith
    have hmul_C : (2 : ℝ) ^ b * ((2 : ℝ) ^ n) ^ (1 - d) ≤
        (C : ℝ) * (((L + 1 : ℕ) : ℝ)) ^ 1 * ((2 : ℝ) ^ n) ^ (1 - d) := by
      rw [pow_one]; exact mul_le_mul_of_nonneg_right (by nlinarith) h2p
    have hnn_C : (0 : ℝ) ≤ (C : ℝ) * (((L + 1 : ℕ) : ℝ)) ^ 1 := by positivity
    linarith
  · rw [← Real.rpow_natCast 2 m, ← Real.rpow_natCast 2 n, ← Real.rpow_mul (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h1 : (m : ℝ) ≤ (n : ℝ) * (1 / (b : ℝ)) := by simpa [div_eq_mul_inv] using hdiv_le
    exact h1.trans (mul_le_mul_of_nonneg_left hb_inv (by positivity))

/-- `FinSAT` is efficiently self-reducible in `O^*` for `p(n) = 2^n`. -/
theorem sat_efficientlySelfReducible_star :
    ∀ a_exp : ℝ, 0 < a_exp → a_exp < 1 →
      ∃ δ : ℝ → ℝ, (∀ ε, 0 < ε → 0 < δ ε) ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ (r : ℕ) (c : OracleCode .standard r) (out : Fin r) (C e k : ℕ),
            0 < C ∧ 0 < k ∧
            ∀ (x : FinCNF) (w : ℕ),
              logWidth k (⌈(2 : ℝ) ^ x.1⌉₊ + (encFinCNF x).length) ≤ w →
              InputFits w (encFinCNF x) →
              ∃ y t qs,
                OracleExec w (oracleOf FinSAT encFinCNF) c (.init (encFinCNF x)) y t qs ∧
                y.regs out ≤ 1 ∧ (y.regs out = 1 ↔ x ∈ FinSAT) ∧
                (∀ qi ∈ qs, qi ∈ Set.range encFinCNF) ∧
                (t : ℝ) ≤ (C : ℝ) * (((encFinCNF x).length + 1 : ℕ) : ℝ) ^ e *
                  ((2 : ℝ) ^ x.1) ^ (1 - δ ε) + (C : ℝ) * (((encFinCNF x).length + 1 : ℕ) : ℝ) ^ e ∧
                ((qs.map fun qi => ((2 : ℝ) ^ (querySize encFinCNF (·.1) qi)) ^ (1 - ε)).sum : ℝ) ≤
                  (C : ℝ) * (((encFinCNF x).length + 1 : ℕ) : ℝ) ^ e *
                  ((2 : ℝ) ^ x.1) ^ (1 - δ ε) + (C : ℝ) * (((encFinCNF x).length + 1 : ℕ) : ℝ) ^ e ∧
                (∀ qi ∈ qs, ∀ x', encFinCNF x' = qi →
                  (2 : ℝ) ^ x'.1 ≤ ((2 : ℝ) ^ x.1) ^ a_exp) := by
  intro a_exp ha_pos _
  let b : ℕ := ⌈1 / a_exp⌉₊ + 2
  refine ⟨fun ε => min (ε / (b : ℝ)) (1 / (2 * (b : ℝ))),
    fun ε hε => lt_min (by positivity) (by positivity), fun ε hε => ?_⟩
  refine ⟨24, satBranchOracleCode b, 8, 100 * 2 ^ b, 1, 4 + b, by positivity, by positivity,
    fun x w hw _ => ?_⟩
  obtain ⟨hw_b, hw_pow, hw_mem, hw_n⟩ := satBranch_fits (by omega : 2 ≤ b) hw
  obtain ⟨y, t, qs, hex, hy8, hyiff, hqs, ht⟩ :=
    satBranchOracleCode_exec (w := w) (O := oracleOf FinSAT encFinCNF) (x := x) (by omega)
      (fun r _ => by rw [Bool.eq_iff_iff, oracleOf_enc]; simp [FinSAT]) hw_b hw_pow hw_mem hw_n
  obtain ⟨ht_b, hsum_b, hsz_b⟩ := satBranch_bounds ha_pos hε ht
  refine ⟨y, t, qs, hex, hy8, hyiff, ?_, ht_b, ?_, ?_⟩
  · intro qi hqi; rw [hqs] at hqi; obtain ⟨r, -, rfl⟩ := List.mem_map.mp hqi; exact ⟨_, rfl⟩
  · rw [hqs, List.map_map]; dsimp only [Function.comp_def]
    have hcongr : ((List.range (2 ^ (x.1 - x.1 / b))).map fun r =>
        ((2 : ℝ) ^ (querySize encFinCNF (·.1) (encFinCNF ⟨x.1 / b, restrictCNF (x.1 / b) r x.2⟩)))
          ^ (1 - ε)) = List.replicate (2 ^ (x.1 - x.1 / b)) (((2 : ℝ) ^ (x.1 / b)) ^ (1 - ε)) := by
      refine List.ext_getElem (by simp) fun i _ _ => ?_
      simp only [List.getElem_map, List.getElem_replicate, querySize_enc]
    rw [hcongr, List.sum_replicate, nsmul_eq_mul]; simpa [b] using hsum_b
  · intro qi hqi x' hx'
    rw [hqs] at hqi; obtain ⟨r, -, hr_eq⟩ := List.mem_map.mp hqi
    have hx'eq : x' = ⟨x.1 / b, restrictCNF (x.1 / b) r x.2⟩ :=
      encFinCNF.injective (hx'.trans hr_eq.symm)
    rw [hx'eq]; exact hsz_b

/-- `FinKSAT k` is efficiently self-reducible in `O^*` for `p(n) = 2^n`. -/
theorem ksat_efficientlySelfReducible_star (k : ℕ) :
    ∀ a_exp : ℝ, 0 < a_exp → a_exp < 1 →
      ∃ δ : ℝ → ℝ, (∀ ε, 0 < ε → 0 < δ ε) ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ (r : ℕ) (c : OracleCode .standard r) (out : Fin r) (C e kw : ℕ),
            0 < C ∧ 0 < kw ∧
            ∀ (x : FinKSATInstance k) (w : ℕ),
              logWidth kw (⌈(2 : ℝ) ^ x.1.1⌉₊ + (encFinKCNF k x).length) ≤ w →
              InputFits w (encFinKCNF k x) →
              ∃ y t qs,
                OracleExec w (oracleOf (FinKSAT k) (encFinKCNF k))
                  c (.init (encFinKCNF k x)) y t qs ∧
                y.regs out ≤ 1 ∧ (y.regs out = 1 ↔ x ∈ FinKSAT k) ∧
                (∀ qi ∈ qs, qi ∈ Set.range (encFinKCNF k)) ∧
                (t : ℝ) ≤ (C : ℝ) * (((encFinKCNF k x).length + 1 : ℕ) : ℝ) ^ e *
                  ((2 : ℝ) ^ x.1.1) ^ (1 - δ ε) + (C : ℝ) * (((encFinKCNF k x).length +
                    1 : ℕ) : ℝ) ^ e ∧
                ((qs.map fun qi => ((2 : ℝ) ^ (querySize (encFinKCNF k) (fun z => z.1.1) qi)) ^ (1 -
                  ε)).sum : ℝ) ≤
                  (C : ℝ) * (((encFinKCNF k x).length + 1 : ℕ) : ℝ) ^ e *
                  ((2 : ℝ) ^ x.1.1) ^ (1 - δ ε) + (C : ℝ) * (((encFinKCNF k x).length +
                    1 : ℕ) : ℝ) ^ e ∧
                (∀ qi ∈ qs, ∀ x', encFinKCNF k x' = qi →
                  (2 : ℝ) ^ x'.1.1 ≤ ((2 : ℝ) ^ x.1.1) ^ a_exp) := by
  intro a_exp ha_pos _
  let b : ℕ := ⌈1 / a_exp⌉₊ + 2
  refine ⟨fun ε => min (ε / (b : ℝ)) (1 / (2 * (b : ℝ))),
    fun ε hε => lt_min (by positivity) (by positivity), fun ε hε => ?_⟩
  refine ⟨24, satBranchOracleCode b, 8, 100 * 2 ^ b, 1, 4 + b, by positivity, by positivity,
    fun x w hw _ => ?_⟩
  obtain ⟨hw_b, hw_pow, hw_mem, hw_n⟩ := satBranch_fits (by omega : 2 ≤ b) hw
  obtain ⟨y, t, qs, hex, hy8, hyiff, hqs, ht⟩ :=
    satBranchOracleCode_exec (w := w) (O := oracleOf (FinKSAT k) (encFinKCNF k)) (x := x.1)
      (by omega)
      (fun r _ => by
        let x' : FinKSATInstance k :=
          ⟨⟨x.1.1 / b, restrictCNF (x.1.1 / b) r x.1.2⟩, restrictCNF_kcnf (x.1.1 / b) r x.2⟩
        change oracleOf (FinKSAT k) (encFinKCNF k) (encFinKCNF k x') = _
        rw [Bool.eq_iff_iff, oracleOf_enc]; simp [FinKSAT, x']) hw_b hw_pow hw_mem hw_n
  obtain ⟨ht_b, hsum_b, hsz_b⟩ := satBranch_bounds ha_pos hε ht
  have hlen_k : (encFinKCNF k x).length = (encFinCNF x.1).length := rfl
  refine ⟨y, t, qs, hex, hy8, hyiff, ?_, by rw [hlen_k]; simpa [b] using ht_b, ?_, ?_⟩
  · intro qi hqi; rw [hqs] at hqi; obtain ⟨r, -, rfl⟩ := List.mem_map.mp hqi
    exact ⟨⟨⟨x.1.1 / b, restrictCNF (x.1.1 / b) r x.1.2⟩, restrictCNF_kcnf _ r x.2⟩, rfl⟩
  · rw [hqs, List.map_map]; dsimp only [Function.comp_def]
    have hcongr : ((List.range (2 ^ (x.1.1 - x.1.1 / b))).map fun r =>
        ((2 : ℝ) ^ (querySize (encFinKCNF k) (fun z => z.1.1)
          (encFinCNF ⟨x.1.1 / b, restrictCNF (x.1.1 / b) r x.1.2⟩))) ^ (1 - ε)) =
        List.replicate (2 ^ (x.1.1 - x.1.1 / b)) (((2 : ℝ) ^ (x.1.1 / b)) ^ (1 - ε)) := by
      refine List.ext_getElem (by simp) fun i _ _ => ?_
      let xi : FinKSATInstance k :=
        ⟨⟨x.1.1 / b, restrictCNF (x.1.1 / b) i x.1.2⟩, restrictCNF_kcnf _ i x.2⟩
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      have hq := querySize_enc (encFinKCNF k) (fun z => z.1.1) xi
      change ((2 : ℝ) ^ (querySize (encFinKCNF k) (fun z => z.1.1) (encFinKCNF k xi))) ^ (1 - ε) =
        ((2 : ℝ) ^ (x.1.1 / b)) ^ (1 - ε)
      rw [hq]
    rw [hcongr, List.sum_replicate, nsmul_eq_mul, hlen_k]; simpa [b] using hsum_b
  · intro qi hqi x' hx'
    rw [hqs] at hqi; obtain ⟨r, -, hr_eq⟩ := List.mem_map.mp hqi
    have hx'eq : x'.1 = ⟨x.1.1 / b, restrictCNF (x.1.1 / b) r x.1.2⟩ :=
      encFinCNF.injective (hx'.trans hr_eq.symm)
    rw [hx'eq]; exact hsz_b

/-- Concrete non-vacuity witnesses for `FinSAT` and `FinKSAT 2`. -/
theorem finSAT_nonvacuous :
    (⟨2, [[(0, true)], [(0, true), (1, false)]]⟩ : FinCNF) ∈ FinSAT ∧
    (⟨1, [[(0, true)], [(0, false)]]⟩ : FinCNF) ∉ FinSAT := by
  constructor
  · exact ⟨fun _ => true, by simp [CNF.eval, Clause.eval, Literal.eval]⟩
  · rintro ⟨σ, hσ⟩
    simp only [CNF.eval_cons, CNF.eval_nil, Clause.eval_cons, Clause.eval_nil, Literal.eval_mk,
      Bool.or_false, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hσ
    have := hσ.1.symm.trans hσ.2; contradiction

end CslibFrontier.Complexity.FineGrained
