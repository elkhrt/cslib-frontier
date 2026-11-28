/-
Copyright (c) 2026 The cslib-frontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.SparseLinearSystemHardness

import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Foundations.Data.List.GetD
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# NP-Completeness of Sparse Subspace Clustering Decision (`SSCDecision`)

This module establishes NP-completeness (under standard Lean axioms) on multi-tape Turing machines
for **Sparse Subspace Clustering Decision (`SSCDecision`)**: given a `d × N` rational data matrix
`X` and a total off-diagonal sparsity budget `k ∈ ℕ`, decide whether there exists an `N × N`
rational self-representation matrix `Z` satisfying `X Z = X`, `diag(Z) = 0`, and `‖Z‖₀ ≤ k`.

NP-membership reduces fixed-support off-diagonal self-representation feasibility to
`Cslib.Complexity.LPFeasibility ∈ NP`; NP-hardness reduces from `SparseLinearSystem` via
zero-column stripping and the duplicated-dictionary gadget `X' = [A' | A' | b]` with budget
`k = 2 n' + t`.

## Main definitions

- `CslibFrontier.Computability.Complexity.SSCDecisionInstance`,
  `CslibFrontier.Computability.Complexity.encSSCDecision`,
  `CslibFrontier.Computability.Complexity.SSCDecision`: sparse subspace clustering `ℓ₀` problem.
- `CslibFrontier.Computability.Complexity.SSCDecision.nonzeroCols`,
  `CslibFrontier.Computability.Complexity.SSCDecision.yesInstance`,
  `CslibFrontier.Computability.Complexity.SSCDecision.fromSparseLinearSystem`: polynomial-time
  reduction from `SparseLinearSystem` to `SSCDecision`.

## Main results

- `CslibFrontier.Computability.Complexity.SSCDecision.mem_NP`,
  `CslibFrontier.Computability.Complexity.SSCDecision.fromSparseLinearSystem_mem_iff`,
  `CslibFrontier.Computability.Complexity.polyTimeReducible_SparseLinearSystem_SSCDecision`,
  `CslibFrontier.Computability.Complexity.SSCDecision_npHard`,
  `CslibFrontier.Computability.Complexity.SSCDecision_npComplete`.

## Tags

computational complexity, NP-completeness, sparse subspace clustering, self-representation
-/

public section

namespace CslibFrontier.Computability.Complexity

open Finset Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- An instance `(d, N, data, budget)` of **Sparse Subspace Clustering Decision**: a `d × N`
rational data matrix `data` (`d, N` in unary) and a binary off-diagonal `ℓ₀` budget `budget`. -/
@[ext]
structure SSCDecisionInstance where
  /-- Ambient dimension (rows of `X`), encoded in unary. -/
  d : ℕ
  /-- Number of data points (columns of `X`), encoded in unary. -/
  N : ℕ
  /-- Explicit `d × N` rational data matrix `X`. -/
  data : List (List ℚ)
  /-- Total off-diagonal sparsity budget `k` (`‖Z‖₀ ≤ k`), encoded in binary. -/
  budget : ℕ
  deriving DecidableEq, Repr

/-- Encoding of `SSCDecisionInstance`. -/
enc_structure encSSCDecision : SSCDecisionInstance where
  d : encUnary,
  N : encUnary,
  data : (encList (encList encRat)),
  budget : encNat

attribute [fun_prop] encSSCDecision_d_polyTime encSSCDecision_N_polyTime
  encSSCDecision_data_polyTime encSSCDecision_budget_polyTime encSSCDecision_mk_polyTime

/-- **Sparse Subspace Clustering Decision (`SSCDecision`)**: instances admitting an `N × N`
rational self-representation matrix `Z` satisfying `X Z = X`, `diag(Z) = 0`, and `‖Z‖₀ ≤ budget`.
-/
@[expose]
def SSCDecision : Set SSCDecisionInstance :=
  {x | ∃ Z : Fin x.N → Fin x.N → ℚ,
    (∀ r : Fin x.d, ∀ j : Fin x.N,
      ∑ l : Fin x.N, matEntry x.data r.1 l.1 * Z l j = matEntry x.data r.1 j.1) ∧
    (∀ j : Fin x.N, Z j j = 0) ∧
    ((univ : Finset (Fin x.N × Fin x.N)).filter fun p ↦ Z p.1 p.2 ≠ 0).card ≤ x.budget}

namespace SSCDecision

private def sscPairEq (x : SSCDecisionInstance) (r j : ℕ) : List ℚ × ℚ :=
  ((List.range (x.N * x.N)).map (fun idx ↦
    if decide (idx % x.N = j) then matEntry x.data r (idx / x.N) else 0),
   matEntry x.data r j)

private def sscMaskEqs (x : SSCDecisionInstance) (mask : List Bool) : List (List ℚ × ℚ) :=
  let M := x.N * x.N
  (((List.range x.d).map fun r ↦
    (List.range x.N).map fun j ↦ sscPairEq x r j).flatten) ++
  ((List.range M).map fun idx ↦
    ((List.range M).map (fun idx' ↦
      if !mask.getD idx false && decide (idx' = idx) then (1 : ℚ) else 0), (0 : ℚ)))

private def sscMaskGuard (p : SSCDecisionInstance × List Bool) : Bool :=
  decide (bitsCountTrue p.2 ≤ p.1.budget) &&
    ((List.range p.1.N).all fun j ↦ !p.2.getD (j * p.1.N + j) false)

private theorem computableInPolyTime_sscMaskEqs :
    ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ sscMaskEqs p.1 p.2)
      (encPair encSSCDecision encBits)
      (encList (encPair (encList encRat) encRat)) := by
  let E := encPair encSSCDecision encBits
  have hx : ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ p.1)
      E encSSCDecision := fst _ _
  have hmask : ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ p.2)
      E encBits := snd _ _
  have hd : ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ p.1.d)
      E encUnary := encSSCDecision_d_polyTime hx
  have hN : ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ p.1.N)
      E encUnary := encSSCDecision_N_polyTime hx
  have hN_bin : ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ p.1.N)
      E encNat := unary_to_binary.comp hN
  have hM : ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ p.1.N * p.1.N)
      E encUnary := unary_mul' hN hN
  have hdata : ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ p.1.data)
      E (encList (encList encRat)) := encSSCDecision_data_polyTime hx
  have hpart1 : ComputableInPolyTime
      (fun p : SSCDecisionInstance × List Bool ↦
        ((List.range p.1.d).map fun r ↦
          (List.range p.1.N).map fun j ↦ sscPairEq p.1 r j).flatten)
      E (encList (encPair (encList encRat) encRat)) := by
    unfold sscPairEq
    refine (ComputableInPolyTime.flatten (encPair (encList encRat) encRat)).comp
      (mapWithInput (ComputableInPolyTime.range.comp hd) ?_)
    refine mapWithInput (ComputableInPolyTime.range.comp (hN.comp (fst _ _))) ?_
    let E2 := encPair (encPair E encUnary) encUnary
    let E3 := encPair E2 encUnary
    refine (mapWithInput (ComputableInPolyTime.range.comp
        (hM.comp ((fst _ _).comp (fst _ _)))) ?_).prod
      (computableInPolyTime_matEntry_unary
        (hdata.comp ((fst _ _).comp (fst _ _)))
        ((snd _ _).comp (fst _ _)) (snd _ _))
    have hidx_bin : ComputableInPolyTime
        (fun t : (((SSCDecisionInstance × List Bool) × ℕ) × ℕ) × ℕ ↦ t.2) E3 encNat :=
      unary_to_binary.comp (snd _ _)
    have hN3_bin : ComputableInPolyTime
        (fun t : (((SSCDecisionInstance × List Bool) × ℕ) × ℕ) × ℕ ↦ t.1.1.1.1.N) E3 encNat :=
      hN_bin.comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))
    have hj3_bin : ComputableInPolyTime
        (fun t : (((SSCDecisionInstance × List Bool) × ℕ) × ℕ) × ℕ ↦ t.1.2) E3 encNat :=
      unary_to_binary.comp ((snd _ _).comp (fst _ _))
    have hmat_div : ComputableInPolyTime
        (fun t : (((SSCDecisionInstance × List Bool) × ℕ) × ℕ) × ℕ ↦
          matEntry t.1.1.1.1.data t.1.1.2 (t.2 / t.1.1.1.1.N)) E3 encRat :=
      listGetD_binary (encA := encRat) (0 : ℚ)
        (listGetDWithInput
          (hdata.comp ((fst _ _).comp ((fst _ _).comp (fst _ _))))
          ((snd _ _).comp ((fst _ _).comp (fst _ _))) ([] : List ℚ))
        (binary_div' hidx_bin hN3_bin)
    exact ite' (decide_eq' (binary_mod' hidx_bin hN3_bin) hj3_bin) hmat_div (const (0 : ℚ))
  have hpart2 : ComputableInPolyTime
      (fun p : SSCDecisionInstance × List Bool ↦
        (List.range (p.1.N * p.1.N)).map fun idx ↦
          ((List.range (p.1.N * p.1.N)).map (fun idx' ↦
            if !p.2.getD idx false && decide (idx' = idx) then (1 : ℚ) else 0), (0 : ℚ)))
      E (encList (encPair (encList encRat) encRat)) := by
    refine mapWithInput (ComputableInPolyTime.range.comp hM) ?_
    refine (mapWithInput (ComputableInPolyTime.range.comp (hM.comp (fst _ _))) ?_).prod
      (const (0 : ℚ))
    have hbit : ComputableInPolyTime
        (fun q : ((SSCDecisionInstance × List Bool) × ℕ) × ℕ ↦
          !q.1.1.2.getD q.1.2 false)
        (encPair (encPair E encUnary) encUnary) encBool :=
      bool_not.comp (bitsGetDWithInput (hmask.comp ((fst _ _).comp (fst _ _)))
        ((snd _ _).comp (fst _ _)) false)
    exact ite' (bool_and' hbit (decide_eq' (snd _ _) ((snd _ _).comp (fst _ _))))
      (const (1 : ℚ)) (const (0 : ℚ))
  unfold sscMaskEqs
  dsimp only
  exact listAppend' hpart1 hpart2

private theorem computableInPolyTime_sscMaskGuard :
    ComputableInPolyTime sscMaskGuard (encPair encSSCDecision encBits) encBool := by
  let E := encPair encSSCDecision encBits
  have hx : ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ p.1)
      E encSSCDecision := fst _ _
  have hmask : ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ p.2)
      E encBits := snd _ _
  have hN : ComputableInPolyTime (fun p : SSCDecisionInstance × List Bool ↦ p.1.N)
      E encUnary := encSSCDecision_N_polyTime hx
  have hdiag : ComputableInPolyTime
      (fun p : SSCDecisionInstance × List Bool ↦
        (List.range p.1.N).all fun j ↦ !p.2.getD (j * p.1.N + j) false) E encBool := by
    apply allWithInput (ComputableInPolyTime.range.comp hN)
    have hdiagIdx : ComputableInPolyTime
        (fun q : (SSCDecisionInstance × List Bool) × ℕ ↦ q.2 * q.1.1.N + q.2)
        (encPair E encUnary) encUnary :=
      unary_add' (unary_mul' (snd _ _) (hN.comp (fst _ _))) (snd _ _)
    exact bool_not.comp (bitsGetDWithInput (hmask.comp (fst _ _)) hdiagIdx false)
  unfold sscMaskGuard
  exact bool_and'
    (binary_le'
      (unary_to_binary.comp (computableInPolyTime_bitsCountTrue.comp hmask))
      (encSSCDecision_budget_polyTime hx))
    hdiag

/-- `SSCDecision` belongs to `NP`. -/
theorem mem_NP : SSCDecision ∈ NP encSSCDecision := by
  let S : Set (SSCDecisionInstance × List Bool) :=
    {p | sscMaskGuard p = true ∧ ratEqSystemToLP (sscMaskEqs p.1 p.2) ∈ LPFeasibility}
  have hLP_pull :
      {p : SSCDecisionInstance × List Bool |
        ratEqSystemToLP (sscMaskEqs p.1 p.2) ∈ LPFeasibility} ∈
      NP (encPair encSSCDecision encBits) :=
    PolyTimeReducible.mem_NP
      ⟨fun p ↦ ratEqSystemToLP (sscMaskEqs p.1 p.2),
        computableInPolyTime_ratEqSystemToLP.comp computableInPolyTime_sscMaskEqs,
        fun _ ↦ Iff.rfl⟩
      LPFeasibility.mem_NP
  have hS_NP : S ∈ NP (encPair encSSCDecision encBits) :=
    mem_NP_of_guard computableInPolyTime_sscMaskGuard hLP_pull fun _ ↦ Iff.rfl
  have hExt : SSCDecision =
      {x | ∃ m : List Bool, m.length = x.N * x.N ∧ (x, m) ∈ S} := by
    ext x
    let M := x.N * x.N
    let pairEquiv : Fin x.N × Fin x.N ≃ Fin M :=
      { toFun := fun p ↦ ⟨p.1.1 * x.N + p.2.1, by dsimp [M]; nlinarith [p.1.2, p.2.2]⟩
        invFun := fun idx ↦
          have hNpos : 0 < x.N := by
            by_contra h0
            have hx0 : x.N = 0 := by omega
            have hM0 : M = 0 := by dsimp [M]; rw [hx0]
            exact Fin.elim0 (hM0 ▸ idx)
          (⟨idx.1 / x.N, (Nat.div_lt_iff_lt_mul hNpos).mpr idx.2⟩,
           ⟨idx.1 % x.N, Nat.mod_lt _ hNpos⟩)
        left_inv := fun ⟨l, j⟩ ↦ by
          have hNpos : 0 < x.N := Nat.pos_of_ne_zero (fun h ↦ Fin.elim0 (h ▸ l))
          ext
          · dsimp only
            rw [Nat.mul_comm l.1 x.N, Nat.mul_add_div hNpos, Nat.div_eq_of_lt j.2, Nat.add_zero]
          · dsimp only
            rw [Nat.mul_add_mod', Nat.mod_eq_of_lt j.2]
        right_inv := fun idx ↦ by
          ext
          dsimp only
          rw [Nat.mul_comm (idx.1 / x.N) x.N]
          exact Nat.div_add_mod idx.1 x.N }
    simp only [SSCDecision, S, sscMaskGuard, Set.mem_ofPred_eq, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true',
      ratEqSystemToLP_mem_LPFeasibility_iff]
    constructor
    · rintro ⟨Z, hXZ, hdiag, hcard⟩
      let m : List Bool := List.ofFn fun idx : Fin M ↦
        decide (Z (pairEquiv.symm idx).1 (pairEquiv.symm idx).2 ≠ 0)
      refine ⟨m, List.length_ofFn, ⟨?_, ?_⟩, ?_⟩
      · rw [bitsCountTrue_eq]
        have hrec : ∀ (k : ℕ) (f : Fin k → Bool),
            ((List.ofFn f).countP (· = true)) = ∑ idx : Fin k, if f idx = true then 1 else 0 := by
          intro k f
          induction k with
          | zero => simp
          | succ k ih =>
            rw [List.ofFn_succ, List.countP_cons, ih, Fin.sum_univ_succ]
            cases f 0 <;> simp [Nat.add_comm]
        have hcnt : m.countP (· = true) =
            ((univ : Finset (Fin x.N × Fin x.N)).filter fun p ↦ Z p.1 p.2 ≠ 0).card := by
          dsimp [m]
          rw [hrec]
          simp only [decide_eq_true_eq, sum_boole, Nat.cast_id]
          refine Finset.card_bij (fun idx _ ↦ pairEquiv.symm idx)
            (fun idx hidx ↦ mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hidx).2⟩)
            (fun _ _ _ _ h ↦ pairEquiv.symm.injective h)
            (fun p hp ↦ ⟨pairEquiv p, mem_filter.mpr ⟨mem_univ _, by
              rw [pairEquiv.symm_apply_apply]; exact (mem_filter.mp hp).2⟩,
              pairEquiv.symm_apply_apply p⟩)
        rw [hcnt]
        exact hcard
      · intro j hj
        let jFin : Fin x.N := ⟨j, hj⟩
        have hlt : j * x.N + j < M := (pairEquiv (jFin, jFin)).2
        have hget : m.getD (j * x.N + j) false =
            decide (Z (pairEquiv.symm ⟨j * x.N + j, hlt⟩).1
              (pairEquiv.symm ⟨j * x.N + j, hlt⟩).2 ≠ 0) := by
          simp [m, List.getD_eq_getElem?_getD, hlt]
        have hsymm : pairEquiv.symm ⟨j * x.N + j, hlt⟩ = (jFin, jFin) :=
          pairEquiv.symm_apply_apply (jFin, jFin)
        rw [hget, hsymm, hdiag jFin]
        simp
      · refine ⟨fun idx ↦
          if hlt : idx < M then
            Z (pairEquiv.symm ⟨idx, hlt⟩).1 (pairEquiv.symm ⟨idx, hlt⟩).2
          else 0, fun p hp ↦ ?_⟩
        simp only [sscMaskEqs, List.mem_append] at hp
        rcases hp with hp1 | hp2
        · obtain ⟨rowList, hrowList, hp_in⟩ := List.mem_flatten.mp hp1
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrowList
          rw [List.mem_range] at hr
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp_in
          rw [List.mem_range] at hj
          unfold sscPairEq
          simp only [List.length_map, List.length_range]
          change ∑ idx ∈ Finset.range M,
              ((List.range M).map (fun idx' ↦
                if decide (idx' % x.N = j) then matEntry x.data r (idx' / x.N) else 0)).getD idx 0 *
              (if hlt : idx < M then
                Z (pairEquiv.symm ⟨idx, hlt⟩).1 (pairEquiv.symm ⟨idx, hlt⟩).2
              else 0) = matEntry x.data r j
          rw [← Fin.sum_univ_eq_sum_range (fun idx ↦
            ((List.range M).map (fun idx' ↦
              if decide (idx' % x.N = j) then matEntry x.data r (idx' / x.N) else 0)).getD idx 0 *
            if hlt : idx < M then
              Z (pairEquiv.symm ⟨idx, hlt⟩).1 (pairEquiv.symm ⟨idx, hlt⟩).2
            else 0)]
          rw [← Fintype.sum_equiv pairEquiv
            (fun q : Fin x.N × Fin x.N ↦
              if q.2.1 = j then matEntry x.data r q.1.1 * Z q.1 q.2 else 0)
            _ (fun ⟨l, j'⟩ ↦ by
              have hNpos : 0 < x.N := Nat.pos_of_ne_zero (fun h ↦ Fin.elim0 (h ▸ l))
              have hlt : l.1 * x.N + j'.1 < M := (pairEquiv (l, j')).2
              have hmod : (l.1 * x.N + j'.1) % x.N = j'.1 := by
                rw [Nat.mul_add_mod', Nat.mod_eq_of_lt j'.2]
              have hdiv : (l.1 * x.N + j'.1) / x.N = l.1 := by
                rw [Nat.mul_comm l.1 x.N, Nat.mul_add_div hNpos, Nat.div_eq_of_lt j'.2,
                  Nat.add_zero]
              have hsymm : pairEquiv.symm ⟨l.1 * x.N + j'.1, hlt⟩ = (l, j') :=
                pairEquiv.symm_apply_apply (l, j')
              have hval : (pairEquiv (l, j')).1 = l.1 * x.N + j'.1 := rfl
              rw [hval]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
                Option.map_some, Option.getD_some, hlt, ↓reduceDIte, hmod, hdiv, decide_eq_true_eq,
                hsymm]
              split_ifs <;> ring)]
          rw [Fintype.sum_prod_type]
          let jFin : Fin x.N := ⟨j, hj⟩
          have hinner : ∀ l : Fin x.N,
              ∑ j' : Fin x.N, (if j'.1 = j then matEntry x.data r l.1 * Z l j' else 0) =
              matEntry x.data r l.1 * Z l jFin := by
            intro l
            have heq_ite : ∀ j' : Fin x.N,
                (if j'.1 = j then matEntry x.data r l.1 * Z l j' else 0) =
                (if j' = jFin then matEntry x.data r l.1 * Z l jFin else 0) := by
              intro j'
              by_cases hjj : j' = jFin
              · subst hjj; simp [jFin]
              · have hne : j'.1 ≠ j := fun h ↦ hjj (Fin.ext h)
                simp [hjj, hne]
            rw [sum_congr rfl fun j' _ ↦ heq_ite j']
            simp
          rw [sum_congr rfl fun l _ ↦ hinner l]
          exact hXZ ⟨r, hr⟩ jFin
        · obtain ⟨idx, hidx_mem, rfl⟩ := List.mem_map.mp hp2
          have hidx : idx < M := List.mem_range.mp hidx_mem
          simp only [List.length_map, List.length_range]
          refine sum_eq_zero fun idx' hidx' ↦ ?_
          have hlt' : idx' < M := Finset.mem_range.mp hidx'
          have hlt'' : idx' < x.N * x.N := hlt'
          have hget_row :
              ((List.range (x.N * x.N)).map
                (fun idx'_1 ↦ if !m.getD idx false && decide (idx'_1 =
                  idx) then (1 : ℚ) else 0)).getD
                  idx' 0 =
              if !m.getD idx false && decide (idx' = idx) then (1 : ℚ) else 0 := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_range hlt'', Option.map_some, Option.getD_some]
          rw [hget_row]
          by_cases heq : idx' = idx
          · subst heq
            have hmget : m.getD idx' false =
                decide (Z (pairEquiv.symm ⟨idx', hlt'⟩).1
                  (pairEquiv.symm ⟨idx', hlt'⟩).2 ≠ 0) := by
              simp [m, List.getD_eq_getElem?_getD, hlt']
            rw [hmget]
            by_cases hznz :
              Z (pairEquiv.symm ⟨idx', hlt'⟩).1 (pairEquiv.symm ⟨idx', hlt'⟩).2 = 0 <;>
              simp [hznz]
          · simp [heq]
    · rintro ⟨m, hmlen, ⟨hbudget, hdiag_m⟩, z, hz⟩
      let Z : Fin x.N → Fin x.N → ℚ := fun l j ↦ z (pairEquiv (l, j)).1
      have hzero_of_false : ∀ idx : Fin M, m.getD idx.1 false = false → z idx.1 = 0 := by
        intro idx hmf
        have hmem :
            ((List.range M).map (fun idx' ↦
              if !m.getD idx.1 false && decide (idx' = idx.1) then (1 : ℚ) else 0), (0 : ℚ)) ∈
            sscMaskEqs x m := by
          unfold sscMaskEqs
          exact List.mem_append_right _
            (List.mem_map.mpr ⟨idx.1, List.mem_range.mpr idx.2, rfl⟩)
        have hrow := hz _ hmem
        simp only [List.length_map, List.length_range, hmf, Bool.not_false, Bool.true_and] at hrow
        rw [← Fin.sum_univ_eq_sum_range (fun idx' ↦
          ((List.range M).map (fun k ↦ if decide (k = idx.1) then (1 : ℚ) else 0)).getD idx' 0 *
            z idx')] at hrow
        have hterm : ∀ idx' : Fin M,
            ((List.range M).map (fun k ↦ if decide (k = idx.1) then (1 : ℚ) else 0)).getD idx'.1 0 *
              z idx'.1 = if idx' = idx then z idx.1 else 0 := by
          intro idx'
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range idx'.2, Option.map_some, Option.getD_some, decide_eq_true_eq]
          by_cases heq : idx' = idx
          · subst heq; simp
          · have hne : idx'.1 ≠ idx.1 := fun h ↦ heq (Fin.ext h)
            simp [heq, hne]
        rw [sum_congr rfl fun idx' _ ↦ hterm idx'] at hrow
        simpa only [sum_ite_eq', mem_univ, ↓reduceIte] using hrow
      refine ⟨Z, fun r j ↦ ?_, fun j ↦ ?_, ?_⟩
      · have hmem : sscPairEq x r.1 j.1 ∈ sscMaskEqs x m := by
          unfold sscMaskEqs
          refine List.mem_append_left _ (List.mem_flatten.mpr ?_)
          exact ⟨(List.range x.N).map fun j' ↦ sscPairEq x r.1 j',
            List.mem_map.mpr ⟨r.1, List.mem_range.mpr r.2, rfl⟩,
            List.mem_map.mpr ⟨j.1, List.mem_range.mpr j.2, rfl⟩⟩
        have hrow := hz _ hmem
        unfold sscPairEq at hrow
        simp only [List.length_map, List.length_range] at hrow
        change ∑ idx ∈ Finset.range M,
            ((List.range M).map (fun idx' ↦
              if decide (idx' % x.N = j.1) then matEntry x.data r.1 (idx' / x.N) else 0)).getD
                idx 0 * z idx = matEntry x.data r.1 j.1 at hrow
        rw [← hrow, ← Fin.sum_univ_eq_sum_range (fun idx ↦
          ((List.range M).map (fun idx' ↦
            if decide (idx' % x.N = j.1) then matEntry x.data r.1 (idx' / x.N) else 0)).getD idx 0 *
            z idx)]
        rw [← Fintype.sum_equiv pairEquiv
          (fun q : Fin x.N × Fin x.N ↦
            if q.2 = j then matEntry x.data r.1 q.1.1 * Z q.1 q.2 else 0)
          _ (fun ⟨l, j'⟩ ↦ by
            have hNpos : 0 < x.N := Nat.pos_of_ne_zero (fun h ↦ Fin.elim0 (h ▸ l))
            have hlt : l.1 * x.N + j'.1 < M := (pairEquiv (l, j')).2
            have hmod : (l.1 * x.N + j'.1) % x.N = j'.1 := by
              rw [Nat.mul_add_mod', Nat.mod_eq_of_lt j'.2]
            have hdiv : (l.1 * x.N + j'.1) / x.N = l.1 := by
              rw [Nat.mul_comm l.1 x.N, Nat.mul_add_div hNpos, Nat.div_eq_of_lt j'.2,
                Nat.add_zero]
            have hval : (pairEquiv (l, j')).1 = l.1 * x.N + j'.1 := rfl
            simp only [Z, hval, List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_range hlt, Option.map_some, Option.getD_some, hmod, hdiv,
              decide_eq_true_eq]
            by_cases hjj : j' = j
            · subst hjj; simp
            · have hne : j'.1 ≠ j.1 := fun h ↦ hjj (Fin.ext h)
              simp [hjj, hne])]
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun l _ ↦ ?_
        simp
      · exact hzero_of_false (pairEquiv (j, j)) (hdiag_m j.1 j.2)
      · have hcnt_M : bitsCountTrue m =
            (univ.filter fun idx : Fin M ↦ m.getD idx.1 false = true).card := by
          unfold bitsCountTrue
          rw [hmlen]
          have hrec : ∀ (k : ℕ) (p : ℕ → Bool),
              (List.range k).countP p = (Finset.range k |>.filter fun i ↦ p i = true).card := by
            intro k p
            induction k with
            | zero => simp
            | succ k ih =>
              rw [List.range_succ, List.countP_append, ih, Finset.range_add_one,
                Finset.filter_insert]
              cases hk : p k <;> simp [hk, Nat.add_comm]
          rw [hrec]
          refine Finset.card_bij (fun i hi ↦ ⟨i, Finset.mem_range.mp (mem_filter.mp hi).1⟩)
            (fun i hi ↦ mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩)
            (fun _ _ _ _ h ↦ congrArg Fin.val h)
            (fun idx hidx ↦ ⟨idx.1,
              mem_filter.mpr ⟨Finset.mem_range.mpr idx.2, (mem_filter.mp hidx).2⟩,
              Fin.eta idx idx.2⟩)
        have hbij_pair :
            ((univ : Finset (Fin x.N × Fin x.N)).filter fun p ↦ Z p.1 p.2 ≠ 0).card ≤
              (univ.filter fun idx : Fin M ↦ m.getD idx.1 false = true).card := by
          have hinj :
              ((univ : Finset (Fin x.N × Fin x.N)).filter fun p ↦ Z p.1 p.2 ≠ 0).card =
                ((univ : Finset (Fin M)).filter fun idx ↦ z idx.1 ≠ 0).card := by
            refine Finset.card_bij (fun p _ ↦ pairEquiv p)
              (fun p hp ↦ mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩)
              (fun _ _ _ _ h ↦ pairEquiv.injective h)
              (fun idx hidx ↦ ⟨pairEquiv.symm idx,
                mem_filter.mpr ⟨mem_univ _, by
                  dsimp [Z]; rw [pairEquiv.apply_symm_apply]; exact (mem_filter.mp hidx).2⟩,
                pairEquiv.apply_symm_apply idx⟩)
          rw [hinj]
          refine card_le_card fun idx hidx ↦ ?_
          rw [mem_filter] at hidx ⊢
          refine ⟨mem_univ _, ?_⟩
          cases hmb : m.getD idx.1 false
          · exact (hidx.2 (hzero_of_false idx hmb)).elim
          · rfl
        exact hbij_pair.trans (hcnt_M.symm ▸ hbudget)
  rw [hExt]
  exact mem_NP_of_boundedBits_NP
    (unary_mul' (encSSCDecision_N_polyTime id') (encSSCDecision_N_polyTime id')) hS_NP

/-! #### Reduction from `SparseLinearSystem` to `SSCDecision` -/

/-- Indices `j < n` of nonzero columns of `mat` across rows `0 .. m - 1`. -/
def nonzeroCols (x : SparseLinearSystemInstance) : List ℕ :=
  ((List.range x.n).map fun j ↦
    if (List.range x.m).any (fun i ↦ !decide (matEntry x.mat i j = 0)) then [j] else []).flatten

private lemma mem_nonzeroCols_iff (x : SparseLinearSystemInstance) (j : ℕ) :
    j ∈ nonzeroCols x ↔ j < x.n ∧ ∃ i < x.m, matEntry x.mat i j ≠ 0 := by
  simp only [nonzeroCols, List.mem_flatten, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨l, ⟨j', hj', hEq⟩, hjl⟩
    by_cases hany : (List.range x.m).any (fun i ↦ !decide (matEntry x.mat i j' = 0)) = true
    · simp only [hany, ↓reduceIte] at hEq
      rw [← hEq, List.mem_singleton] at hjl
      subst hjl
      simp only [List.any_eq_true, List.mem_range, Bool.not_eq_true',
        decide_eq_false_iff_not] at hany
      exact ⟨hj', hany⟩
    · simp only [hany, Bool.false_eq_true, ↓reduceIte] at hEq
      rw [← hEq] at hjl
      nomatch hjl
  · rintro ⟨hj, i, hi, hnz⟩
    have hany : (List.range x.m).any (fun i' ↦ !decide (matEntry x.mat i' j = 0)) = true := by
      simp only [List.any_eq_true, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨i, hi, hnz⟩
    exact ⟨[j], ⟨j, hj, by simp [hany]⟩, List.mem_singleton_self j⟩

private lemma nodup_nonzeroCols (x : SparseLinearSystemInstance) : (nonzeroCols x).Nodup := by
  have hsub : (nonzeroCols x).Sublist (List.range x.n) := by
    unfold nonzeroCols
    have hrec : ∀ (l : List ℕ) (p : ℕ → Bool),
        ((l.map fun j ↦ if p j then [j] else []).flatten).Sublist l := by
      intro l p
      induction l with
      | nil => simp
      | cons a as ih =>
        simp only [List.map_cons, List.flatten_cons]
        cases p a <;> simp [ih, List.Sublist.cons]
    exact hrec (List.range x.n) _
  exact hsub.nodup List.nodup_range

@[local fun_prop]
private theorem computableInPolyTime_nonzeroCols :
    ComputableInPolyTime nonzeroCols encSparseLinearSystem (encList encNat) := by
  let E := encSparseLinearSystem
  have hm : ComputableInPolyTime (fun x : SparseLinearSystemInstance ↦ x.m) E encUnary :=
    encSparseLinearSystem_m_polyTime id'
  have hn : ComputableInPolyTime (fun x : SparseLinearSystemInstance ↦ x.n) E encUnary :=
    encSparseLinearSystem_n_polyTime id'
  have hmat : ComputableInPolyTime (fun x : SparseLinearSystemInstance ↦ x.mat)
      E (encList (encList encRat)) := encSparseLinearSystem_mat_polyTime id'
  unfold nonzeroCols
  refine (ComputableInPolyTime.flatten encNat).comp
    (mapWithInput (ComputableInPolyTime.range.comp hn) ?_)
  have hany : ComputableInPolyTime
      (fun q : SparseLinearSystemInstance × ℕ ↦
        (List.range q.1.m).any fun i ↦ !decide (matEntry q.1.mat i q.2 = 0))
      (encPair E encUnary) encBool := by
    apply anyWithInput (ComputableInPolyTime.range.comp (hm.comp (fst _ _)))
    exact bool_not.comp (rat_isZero.comp
      (computableInPolyTime_matEntry_unary
        (hmat.comp ((fst _ _).comp (fst _ _))) (snd _ _) ((snd _ _).comp (fst _ _))))
  exact ite' hany (cons' (unary_to_binary.comp (snd _ _)) (const [])) (const [])

/-- Fixed accepted `SSCDecision` instance (`0 × 0`). -/
def yesInstance : SSCDecisionInstance := ⟨0, 0, [], 0⟩

private theorem yesInstance_mem : yesInstance ∈ SSCDecision :=
  ⟨fun i ↦ Fin.elim0 i, fun r ↦ Fin.elim0 r, fun j ↦ Fin.elim0 j,
    le_trans (card_le_univ _) (by decide)⟩

/-- Polynomial-time reduction from `SparseLinearSystem` to `SSCDecision` via `[A' | A' | b]`. -/
def fromSparseLinearSystem (x : SparseLinearSystemInstance) : SSCDecisionInstance :=
  if (List.range x.m).all (fun i ↦ decide (vecEntry x.rhs i = 0)) then yesInstance
  else
    let cols := nonzeroCols x
    let n' := cols.length
    let N := 2 * n' + 1
    let data := (List.range x.m).map fun i ↦
      (List.range N).map fun l ↦
        if decide (l < n') then matEntry x.mat i (cols.getD l 0)
        else if decide (l < 2 * n') then matEntry x.mat i (cols.getD (l - n') 0)
        else vecEntry x.rhs i
    ⟨x.m, N, data, 2 * n' + x.budget⟩

@[fun_prop]
theorem computableInPolyTime_fromSparseLinearSystem :
    ComputableInPolyTime fromSparseLinearSystem encSparseLinearSystem encSSCDecision := by
  let E := encSparseLinearSystem
  have hm : ComputableInPolyTime (fun x : SparseLinearSystemInstance ↦ x.m) E encUnary :=
    encSparseLinearSystem_m_polyTime id'
  have hmat : ComputableInPolyTime (fun x : SparseLinearSystemInstance ↦ x.mat)
      E (encList (encList encRat)) := encSparseLinearSystem_mat_polyTime id'
  have hrhs : ComputableInPolyTime (fun x : SparseLinearSystemInstance ↦ x.rhs)
      E (encList encRat) := encSparseLinearSystem_rhs_polyTime id'
  have hbud : ComputableInPolyTime (fun x : SparseLinearSystemInstance ↦ x.budget) E encNat :=
    encSparseLinearSystem_budget_polyTime id'
  have hcols : ComputableInPolyTime nonzeroCols E (encList encNat) :=
    computableInPolyTime_nonzeroCols
  have hn' : ComputableInPolyTime
      (fun x : SparseLinearSystemInstance ↦ (nonzeroCols x).length) E encUnary :=
    (length_list encNat).comp hcols
  have hn'_bin : ComputableInPolyTime
      (fun x : SparseLinearSystemInstance ↦ (nonzeroCols x).length) E encNat :=
    unary_to_binary.comp hn'
  have hN : ComputableInPolyTime
      (fun x : SparseLinearSystemInstance ↦ 2 * (nonzeroCols x).length + 1) E encUnary :=
    unary_add' (unary_mul' (const 2) hn') (const 1)
  have hzeroRhs : ComputableInPolyTime
      (fun x : SparseLinearSystemInstance ↦
        (List.range x.m).all fun i ↦ decide (vecEntry x.rhs i = 0)) E encBool :=
    allWithInput (ComputableInPolyTime.range.comp hm)
      (rat_isZero.comp (computableInPolyTime_vecEntry_unary (hrhs.comp (fst _ _)) (snd _ _)))
  have hdata : ComputableInPolyTime
      (fun x : SparseLinearSystemInstance ↦
        let cols := nonzeroCols x
        let n' := cols.length
        let N := 2 * n' + 1
        (List.range x.m).map fun i ↦
          (List.range N).map fun l ↦
            if decide (l < n') then matEntry x.mat i (cols.getD l 0)
            else if decide (l < 2 * n') then matEntry x.mat i (cols.getD (l - n') 0)
            else vecEntry x.rhs i)
      E (encList (encList encRat)) := by
    dsimp only
    refine mapWithInput (ComputableInPolyTime.range.comp hm) ?_
    refine mapWithInput (ComputableInPolyTime.range.comp (hN.comp (fst _ _))) ?_
    let E2 := encPair (encPair E encUnary) encUnary
    have hx2 : ComputableInPolyTime
        (fun q : (SparseLinearSystemInstance × ℕ) × ℕ ↦ q.1.1) E2 E :=
      (fst _ _).comp (fst _ _)
    have hi2 : ComputableInPolyTime
        (fun q : (SparseLinearSystemInstance × ℕ) × ℕ ↦ q.1.2) E2 encUnary :=
      (snd _ _).comp (fst _ _)
    have hl2 : ComputableInPolyTime
        (fun q : (SparseLinearSystemInstance × ℕ) × ℕ ↦ q.2) E2 encUnary := snd _ _
    have hl_bin : ComputableInPolyTime
        (fun q : (SparseLinearSystemInstance × ℕ) × ℕ ↦ q.2) E2 encNat :=
      unary_to_binary.comp hl2
    have hn'2 : ComputableInPolyTime
        (fun q : (SparseLinearSystemInstance × ℕ) × ℕ ↦ (nonzeroCols q.1.1).length) E2 encUnary :=
      hn'.comp hx2
    have hn'2_bin : ComputableInPolyTime
        (fun q : (SparseLinearSystemInstance × ℕ) × ℕ ↦ (nonzeroCols q.1.1).length) E2 encNat :=
      hn'_bin.comp hx2
    have hcol1 : ComputableInPolyTime
        (fun q : (SparseLinearSystemInstance × ℕ) × ℕ ↦ (nonzeroCols q.1.1).getD q.2 0)
        E2 encNat :=
      listGetDWithInput (hcols.comp hx2) hl2 0
    have hcol2 : ComputableInPolyTime
        (fun q : (SparseLinearSystemInstance × ℕ) × ℕ ↦
          (nonzeroCols q.1.1).getD (q.2 - (nonzeroCols q.1.1).length) 0)
        E2 encNat :=
      listGetDWithInput (hcols.comp hx2) (unary_sub' hl2 hn'2) 0
    have hmat1 : ComputableInPolyTime
        (fun q : (SparseLinearSystemInstance × ℕ) × ℕ ↦
          matEntry q.1.1.mat q.1.2 ((nonzeroCols q.1.1).getD q.2 0)) E2 encRat :=
      listGetD_binary (encA := encRat) (0 : ℚ)
        (listGetDWithInput (hmat.comp hx2) hi2 ([] : List ℚ)) hcol1
    have hmat2 : ComputableInPolyTime
        (fun q : (SparseLinearSystemInstance × ℕ) × ℕ ↦
          matEntry q.1.1.mat q.1.2
            ((nonzeroCols q.1.1).getD (q.2 - (nonzeroCols q.1.1).length) 0)) E2 encRat :=
      listGetD_binary (encA := encRat) (0 : ℚ)
        (listGetDWithInput (hmat.comp hx2) hi2 ([] : List ℚ)) hcol2
    exact ite' (binary_lt' hl_bin hn'2_bin) hmat1
      (ite' (binary_lt' hl_bin (binary_mul' (const 2) hn'2_bin)) hmat2
        (computableInPolyTime_vecEntry_unary (hrhs.comp hx2) hi2))
  unfold fromSparseLinearSystem
  dsimp only
  exact ite' hzeroRhs (const yesInstance)
    (encSSCDecision_mk_polyTime hm hN hdata
      (binary_add' (binary_mul' (const 2) hn'_bin) hbud))

theorem fromSparseLinearSystem_mem_iff (x : SparseLinearSystemInstance) :
    fromSparseLinearSystem x ∈ SSCDecision ↔ x ∈ SparseLinearSystem := by
  by_cases hb0 : (List.range x.m).all (fun i ↦ decide (vecEntry x.rhs i = 0)) = true
  · have hfx : fromSparseLinearSystem x = yesInstance := by
      simp [fromSparseLinearSystem, hb0]
    rw [hfx]
    have hmemSLS : x ∈ SparseLinearSystem := by
      refine ⟨fun _ ↦ 0, fun i ↦ ?_, by simp⟩
      have hall := List.all_eq_true.mp hb0 i.1 (List.mem_range.mpr i.2)
      simp only [decide_eq_true_eq] at hall
      simp [hall]
    exact ⟨fun _ ↦ hmemSLS, fun _ ↦ yesInstance_mem⟩
  · let cols := nonzeroCols x
    let n' := cols.length
    let N := 2 * n' + 1
    let data := (List.range x.m).map fun i ↦
      (List.range N).map fun l ↦
        if decide (l < n') then matEntry x.mat i (cols.getD l 0)
        else if decide (l < 2 * n') then matEntry x.mat i (cols.getD (l - n') 0)
        else vecEntry x.rhs i
    have hfx : fromSparseLinearSystem x = ⟨x.m, N, data, 2 * n' + x.budget⟩ := by
      simp [fromSparseLinearSystem, hb0, cols, n', N, data]
    rw [hfx]
    have hdata_entry : ∀ (i : Fin x.m) (l : Fin N),
        matEntry data i.1 l.1 =
          if l.1 < n' then matEntry x.mat i.1 (cols.getD l.1 0)
          else if l.1 < 2 * n' then matEntry x.mat i.1 (cols.getD (l.1 - n') 0)
          else vecEntry x.rhs i.1 := by
      intro i l
      simp [data, matEntry, List.getD_eq_getElem?_getD, i.2, l.2]
    have hcols_nd : cols.Nodup := nodup_nonzeroCols x
    have hcols_mem : ∀ c : Fin n', cols.getD c.1 0 < x.n ∧
        ∃ i < x.m, matEntry x.mat i (cols.getD c.1 0) ≠ 0 := by
      intro c
      have hc_lt : c.1 < cols.length := c.2
      rw [List.getD_eq_getElem cols 0 hc_lt]
      exact (mem_nonzeroCols_iff x cols[c.1]).mp (List.getElem_mem hc_lt)
    have hcols_inj : ∀ c₁ c₂ : Fin n', cols.getD c₁.1 0 = cols.getD c₂.1 0 → c₁ = c₂ := by
      intro c₁ c₂ hEq
      rw [List.getD_eq_getElem cols 0 c₁.2, List.getD_eq_getElem cols 0 c₂.2] at hEq
      have h1 := hcols_nd.idxOf_getElem c₁.1 c₁.2
      have h2 := hcols_nd.idxOf_getElem c₂.1 c₂.2
      rw [hEq] at h1
      exact Fin.ext (h1.symm.trans h2)
    constructor
    · -- Soundness: `SSCDecision → SparseLinearSystem`
      rintro ⟨Z, hXZ, hdiag, hcard⟩
      dsimp only at Z hXZ hdiag hcard
      let colNnz (j : Fin N) : Finset (Fin N) := univ.filter fun l : Fin N ↦ Z l j ≠ 0
      have hsum_cols :
          ∑ j : Fin N, (colNnz j).card =
            ((univ : Finset (Fin N × Fin N)).filter fun p ↦ Z p.1 p.2 ≠ 0).card := by
        simp only [colNnz, card_filter]
        symm
        rw [Fintype.sum_prod_type, sum_comm]
      have hge1 : ∀ j : Fin N, j.1 < 2 * n' → 1 ≤ (colNnz j).card := by
        intro j hj2n
        by_cases hj1 : j.1 < n'
        · obtain ⟨_, i_nat, hi_lt, hnz_col⟩ := hcols_mem ⟨j.1, hj1⟩
          let i : Fin x.m := ⟨i_nat, hi_lt⟩
          have heq := hXZ i j
          rw [hdata_entry i j] at heq
          simp only [hj1, ↓reduceIte] at heq
          by_contra h0
          have hcard0 : (colNnz j).card = 0 := by omega
          have hemp : colNnz j = ∅ := card_eq_zero.mp hcard0
          have hsum0 : ∑ l : Fin N, matEntry data i.1 l.1 * Z l j = 0 :=
            sum_eq_zero fun l _ ↦ by
              have hl0 : Z l j = 0 := by
                by_contra hlnz
                have : l ∈ colNnz j := mem_filter.mpr ⟨mem_univ _, hlnz⟩
                rw [hemp] at this; exact notMem_empty l this
              rw [hl0, mul_zero]
          rw [hsum0] at heq
          exact hnz_col heq.symm
        · have hsub_lt : j.1 - n' < n' := by omega
          obtain ⟨_, i_nat, hi_lt, hnz_col⟩ := hcols_mem ⟨j.1 - n', hsub_lt⟩
          let i : Fin x.m := ⟨i_nat, hi_lt⟩
          have heq := hXZ i j
          rw [hdata_entry i j] at heq
          simp only [hj1, hj2n, ↓reduceIte] at heq
          by_contra h0
          have hcard0 : (colNnz j).card = 0 := by omega
          have hemp : colNnz j = ∅ := card_eq_zero.mp hcard0
          have hsum0 : ∑ l : Fin N, matEntry data i.1 l.1 * Z l j = 0 :=
            sum_eq_zero fun l _ ↦ by
              have hl0 : Z l j = 0 := by
                by_contra hlnz
                have : l ∈ colNnz j := mem_filter.mpr ⟨mem_univ _, hlnz⟩
                rw [hemp] at this; exact notMem_empty l this
              rw [hl0, mul_zero]
          rw [hsum0] at heq
          exact hnz_col heq.symm
      let lastCol : Fin N := ⟨2 * n', by dsimp [N]; omega⟩
      have hsplit_N : ∑ j : Fin N, (colNnz j).card =
          (∑ j ∈ univ.erase lastCol, (colNnz j).card) + (colNnz lastCol).card :=
        (sum_erase_add _ _ (mem_univ lastCol)).symm
      have herase_ge : 2 * n' ≤ ∑ j ∈ univ.erase lastCol, (colNnz j).card := by
        have herase_card : (univ.erase lastCol).card = 2 * n' := by
          rw [card_erase_of_mem (mem_univ lastCol), card_univ, Fintype.card_fin]
          rfl
        calc
          2 * n' = ∑ _j ∈ univ.erase lastCol, 1 := by simp [herase_card]
          _ ≤ ∑ j ∈ univ.erase lastCol, (colNnz j).card := sum_le_sum fun j hj ↦ by
            have hne : j ≠ lastCol := (mem_erase.mp hj).1
            have hj_lt : j.1 < 2 * n' := by
              have := j.2
              have : j.1 ≠ 2 * n' := fun h ↦ hne (Fin.ext h)
              dsimp [N] at this ⊢; omega
            exact hge1 j hj_lt
      have hlast_le : (colNnz lastCol).card ≤ x.budget := by
        have htot := hcard
        rw [← hsum_cols, hsplit_N] at htot
        omega
      let u : Fin n' → ℚ := fun c ↦
        Z ⟨c.1, by dsimp [N]; omega⟩ lastCol + Z ⟨n' + c.1, by dsimp [N]; omega⟩ lastCol
      have hu_card : (univ.filter fun c : Fin n' ↦ u c ≠ 0).card ≤ (colNnz lastCol).card := by
        let pick (c : Fin n') : Fin N :=
          if Z ⟨c.1, by dsimp [N]; omega⟩ lastCol ≠ 0 then ⟨c.1, by dsimp [N]; omega⟩
          else ⟨n' + c.1, by dsimp [N]; omega⟩
        refine Finset.card_le_card_of_injOn pick
          (fun c hc ↦ ?_) (fun c₁ _ c₂ _ hEq ↦ ?_)
        · have huc : u c ≠ 0 := (mem_filter.mp hc).2
          refine mem_filter.mpr ⟨mem_univ _, ?_⟩
          dsimp [pick]
          by_cases h1 : Z ⟨c.1, by dsimp [N]; omega⟩ lastCol ≠ 0
          · simp only [h1, not_false_eq_true, ↓reduceIte]
          · simp only [h1, ↓reduceIte]
            push Not at h1
            intro h2
            apply huc
            dsimp [u]
            rw [h1, h2, add_zero]
        · have hv : (pick c₁).1 = (pick c₂).1 := congrArg Fin.val hEq
          dsimp [pick] at hv
          have hc1_lt : c₁.1 < n' := c₁.2
          have hc2_lt : c₂.1 < n' := c₂.2
          by_cases h1 : Z ⟨c₁.1, by dsimp [N]; omega⟩ lastCol ≠ 0 <;>
            by_cases h2 : Z ⟨c₂.1, by dsimp [N]; omega⟩ lastCol ≠ 0
          · simp only [h1, h2, not_false_eq_true, ↓reduceIte] at hv
            exact Fin.ext hv
          · simp only [h1, h2, not_false_eq_true, ↓reduceIte] at hv
            omega
          · simp only [h1, h2, not_false_eq_true, ↓reduceIte] at hv
            omega
          · simp only [h1, h2, ↓reduceIte] at hv
            exact Fin.ext (by omega)
      let z : Fin x.n → ℚ := fun j ↦
        if hmem : j.1 ∈ cols then
          u ⟨cols.idxOf j.1, List.idxOf_lt_length_iff.mpr hmem⟩
        else 0
      refine ⟨z, fun i ↦ ?_, ?_⟩
      · have heq := hXZ i lastCol
        have hlast_rhs : matEntry data i.1 lastCol.1 = vecEntry x.rhs i.1 := by
          rw [hdata_entry i lastCol]
          have hnot1 : ¬(lastCol.1 < n') := by dsimp [lastCol]; omega
          have hnot2 : ¬(lastCol.1 < 2 * n') := by dsimp [lastCol]; omega
          simp [hnot1, hnot2]
        rw [hlast_rhs] at heq
        rw [← heq]
        have hlhs : ∑ j : Fin x.n, matEntry x.mat i.1 j.1 * z j =
            ∑ c : Fin n', matEntry x.mat i.1 (cols.getD c.1 0) * u c := by
          let embFun (c : Fin n') : Fin x.n := ⟨cols.getD c.1 0, (hcols_mem c).1⟩
          let emb : Fin n' ↪ Fin x.n :=
            ⟨embFun, fun c₁ c₂ h ↦ hcols_inj c₁ c₂ (congrArg Fin.val h)⟩
          have hvanish : ∀ j : Fin x.n, j ∉ univ.map emb → matEntry x.mat i.1 j.1 * z j = 0 := by
            intro j hjnot
            have hnot_cols : j.1 ∉ cols := by
              intro hmem
              apply hjnot
              let c : Fin n' := ⟨cols.idxOf j.1, List.idxOf_lt_length_iff.mpr hmem⟩
              refine mem_map.mpr ⟨c, mem_univ c, Fin.ext ?_⟩
              change cols.getD (cols.idxOf j.1) 0 = j.1
              rw [List.getD_eq_getElem cols 0 (List.idxOf_lt_length_iff.mpr hmem),
                List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hmem)]
            dsimp [z]
            simp [hnot_cols]
          rw [← sum_subset (subset_univ (univ.map emb)) fun j _ hj ↦ hvanish j hj, sum_map]
          refine sum_congr rfl fun c _ ↦ ?_
          have hc_lt : c.1 < cols.length := c.2
          have hget : cols.getD c.1 0 = cols[c.1] := List.getD_eq_getElem cols 0 hc_lt
          have hmem : cols[c.1] ∈ cols := List.getElem_mem hc_lt
          have hidx : cols.idxOf cols[c.1] = c.1 := hcols_nd.idxOf_getElem c.1 hc_lt
          have hz_c : z (emb c) = u c := by
            have hval : (emb c).1 = cols[c.1] := hget
            dsimp [z]
            simp only [hval, hmem, ↓reduceDIte]
            congr 1
            ext
            exact hidx
          rw [hz_c]
          rfl
        have hrhs_sum : ∑ l : Fin N, matEntry data i.1 l.1 * Z l lastCol =
            ∑ c : Fin n', matEntry x.mat i.1 (cols.getD c.1 0) * u c := by
          have hdiag0 : Z lastCol lastCol = 0 := hdiag lastCol
          rw [← sum_erase_add _ _ (mem_univ lastCol), hdiag0, mul_zero, add_zero]
          let emb1Fun (c : Fin n') : Fin N := ⟨c.1, by dsimp [N]; omega⟩
          let emb1 : Fin n' ↪ Fin N :=
            ⟨emb1Fun, fun c₁ c₂ h ↦ Fin.ext (congrArg (Fin.val : Fin N → ℕ) h)⟩
          let emb2Fun (c : Fin n') : Fin N := ⟨n' + c.1, by dsimp [N]; omega⟩
          let emb2 : Fin n' ↪ Fin N :=
            ⟨emb2Fun, fun c₁ c₂ h ↦ by
              have hv : n' + c₁.1 = n' + c₂.1 := congrArg Fin.val h
              exact Fin.ext (by omega)⟩
          have hdisj12 : Disjoint (univ.map emb1) (univ.map emb2) := by
            refine Finset.disjoint_left.mpr fun l hl1 hl2 ↦ ?_
            obtain ⟨c₁, _, rfl⟩ := mem_map.mp hl1
            obtain ⟨c₂, _, hEq⟩ := mem_map.mp hl2
            have hv : (emb1 c₁).1 = (emb2 c₂).1 := congrArg (Fin.val : Fin N → ℕ) hEq.symm
            change c₁.1 = n' + c₂.1 at hv
            have hc1_lt : c₁.1 < n' := c₁.2
            omega
          have hunion12 : univ.map emb1 ∪ univ.map emb2 = univ.erase lastCol := by
            ext l
            simp only [mem_union, mem_map, mem_univ, true_and, mem_erase]
            constructor
            · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
              · refine ⟨fun h ↦ ?_, trivial⟩
                have hv : c.1 = 2 * n' := congrArg Fin.val h
                have := c.2; omega
              · refine ⟨fun h ↦ ?_, trivial⟩
                have hv : n' + c.1 = 2 * n' := congrArg Fin.val h
                have := c.2; omega
            · rintro ⟨hne, _⟩
              have hl_lt : l.1 < 2 * n' := by
                have := l.2
                have : l.1 ≠ 2 * n' := fun h ↦ hne (Fin.ext h)
                dsimp [N] at this ⊢; omega
              by_cases hl1 : l.1 < n'
              · exact Or.inl ⟨⟨l.1, hl1⟩, Fin.ext rfl⟩
              · exact Or.inr ⟨⟨l.1 - n', by omega⟩, Fin.ext (by
                  change n' + (l.1 - n') = l.1; omega)⟩
          rw [← hunion12, sum_union hdisj12, sum_map, sum_map, ← sum_add_distrib]
          refine sum_congr rfl fun c _ ↦ ?_
          have h1 : matEntry data i.1 (emb1 c).1 = matEntry x.mat i.1 (cols.getD c.1 0) := by
            rw [hdata_entry i (emb1 c)]
            have hval1 : (emb1 c).1 = c.1 := rfl
            rw [hval1]
            simp [c.2]
          have h2 : matEntry data i.1 (emb2 c).1 = matEntry x.mat i.1 (cols.getD c.1 0) := by
            rw [hdata_entry i (emb2 c)]
            have hval2 : (emb2 c).1 = n' + c.1 := rfl
            rw [hval2]
            have hnot1 : ¬(n' + c.1 < n') := by omega
            have hlt2 : n' + c.1 < 2 * n' := by have := c.2; omega
            have hsub : n' + c.1 - n' = c.1 := by omega
            simp [hnot1, hlt2, hsub]
          have hZ1 : Z (emb1 c) lastCol = Z ⟨c.1, by dsimp [N]; omega⟩ lastCol := rfl
          have hZ2 : Z (emb2 c) lastCol = Z ⟨n' + c.1, by dsimp [N]; omega⟩ lastCol := rfl
          rw [h1, h2, hZ1, hZ2]
          dsimp [u]
          ring
        rw [hlhs, hrhs_sum]
      · have hz_le : (univ.filter fun j : Fin x.n ↦ z j ≠ 0).card ≤
            (univ.filter fun c : Fin n' ↦ u c ≠ 0).card := by
          by_cases hfilt_emp : (univ.filter fun j : Fin x.n ↦ z j ≠ 0) = ∅
          · rw [hfilt_emp, card_empty]; exact Nat.zero_le _
          · obtain ⟨j₀, hj₀⟩ := nonempty_iff_ne_empty.mpr hfilt_emp
            have hzj₀ : z j₀ ≠ 0 := (mem_filter.mp hj₀).2
            have hj₀_mem : j₀.1 ∈ cols := by
              by_contra hnot; dsimp [z] at hzj₀; simp [hnot] at hzj₀
            have hn'_pos : 0 < n' :=
              Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_iff.mpr hj₀_mem)
            refine Finset.card_le_card_of_injOn
              (fun j ↦ if hmem : j.1 ∈ cols then
                ⟨cols.idxOf j.1, List.idxOf_lt_length_iff.mpr hmem⟩ else ⟨0, hn'_pos⟩)
              (fun j hj ↦ ?_) (fun j₁ hj₁ j₂ hj₂ hEq ↦ ?_)
            · have hzj : z j ≠ 0 := (mem_filter.mp hj).2
              have hmem : j.1 ∈ cols := by
                by_contra hnot; dsimp [z] at hzj; simp [hnot] at hzj
              dsimp [z] at hzj
              simp only [hmem, ↓reduceDIte] at hzj ⊢
              exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hzj⟩)
            · have hzj1 : z j₁ ≠ 0 := (mem_filter.mp (mem_coe.mp hj₁)).2
              have hzj2 : z j₂ ≠ 0 := (mem_filter.mp (mem_coe.mp hj₂)).2
              have hm1 : j₁.1 ∈ cols := by
                by_contra hnot; dsimp [z] at hzj1; simp [hnot] at hzj1
              have hm2 : j₂.1 ∈ cols := by
                by_contra hnot; dsimp [z] at hzj2; simp [hnot] at hzj2
              simp only [hm1, hm2, ↓reduceDIte] at hEq
              have hv : cols.idxOf j₁.1 = cols.idxOf j₂.1 := congrArg Fin.val hEq
              have hlt1 := List.idxOf_lt_length_iff.mpr hm1
              have hlt2 := List.idxOf_lt_length_iff.mpr hm2
              have he1 := List.getElem_idxOf hlt1
              have he2 := List.getElem_idxOf hlt2
              have h12 : cols[cols.idxOf j₁.1]'hlt1 = cols[cols.idxOf j₂.1]'hlt2 := by simp [hv]
              exact Fin.ext (he1.symm.trans (h12.trans he2))
        exact hz_le.trans (hu_card.trans hlast_le)
    · -- Completeness: `SparseLinearSystem → SSCDecision`
      rintro ⟨z, hAz, hcard⟩
      let u : Fin n' → ℚ := fun c ↦ z ⟨cols.getD c.1 0, (hcols_mem c).1⟩
      let Z : Fin N → Fin N → ℚ := fun l j ↦
        if j.1 < n' then
          if l.1 = n' + j.1 then 1 else 0
        else if j.1 < 2 * n' then
          if l.1 = j.1 - n' then 1 else 0
        else
          if hl1 : l.1 < n' then u ⟨l.1, hl1⟩ else 0
      refine ⟨Z, fun i j ↦ ?_, fun j ↦ ?_, ?_⟩
      · dsimp only at i j ⊢
        by_cases hj1 : j.1 < n'
        · let l₀ : Fin N := ⟨n' + j.1, by dsimp [N]; omega⟩
          have hterm : ∀ l : Fin N,
              matEntry data i.1 l.1 * Z l j =
                if l = l₀ then matEntry x.mat i.1 (cols.getD j.1 0) else 0 := by
            intro l
            dsimp [Z]
            simp only [hj1, ↓reduceIte]
            by_cases hll₀ : l = l₀
            · subst hll₀
              have hl₀_eq : l₀.1 = n' + j.1 := rfl
              simp only [hl₀_eq, ↓reduceIte, mul_one]
              rw [hdata_entry i l₀, hl₀_eq]
              have hnot1 : ¬(n' + j.1 < n') := by omega
              have hlt2 : n' + j.1 < 2 * n' := by omega
              have hsub : n' + j.1 - n' = j.1 := by omega
              simp [hnot1, hlt2, hsub]
            · have hne : l.1 ≠ n' + j.1 := fun h ↦ hll₀ (Fin.ext h)
              simp [hne, hll₀]
          rw [sum_congr rfl fun l _ ↦ hterm l]
          simp only [sum_ite_eq', mem_univ, ↓reduceIte]
          rw [hdata_entry i j]
          simp [hj1]
        · by_cases hj2 : j.1 < 2 * n'
          · let l₀ : Fin N := ⟨j.1 - n', by dsimp [N]; omega⟩
            have hterm : ∀ l : Fin N,
                matEntry data i.1 l.1 * Z l j =
                  if l = l₀ then matEntry x.mat i.1 (cols.getD (j.1 - n') 0) else 0 := by
              intro l
              dsimp [Z]
              simp only [hj1, hj2, ↓reduceIte]
              by_cases hll₀ : l = l₀
              · subst hll₀
                have hl₀_eq : l₀.1 = j.1 - n' := rfl
                simp only [hl₀_eq, ↓reduceIte, mul_one]
                rw [hdata_entry i l₀, hl₀_eq]
                have hlt1 : j.1 - n' < n' := by omega
                simp [hlt1]
              · have hne : l.1 ≠ j.1 - n' := fun h ↦ hll₀ (Fin.ext h)
                simp [hne, hll₀]
            rw [sum_congr rfl fun l _ ↦ hterm l]
            simp only [sum_ite_eq', mem_univ, ↓reduceIte]
            rw [hdata_entry i j]
            simp [hj1, hj2]
          · have hrhs_j : matEntry data i.1 j.1 = vecEntry x.rhs i.1 := by
              rw [hdata_entry i j]
              simp [hj1, hj2]
            rw [hrhs_j, ← hAz i]
            let emb1Fun' (c : Fin n') : Fin N := ⟨c.1, by dsimp [N]; omega⟩
            let emb1 : Fin n' ↪ Fin N :=
              ⟨emb1Fun', fun c₁ c₂ h ↦ Fin.ext (congrArg (Fin.val : Fin N → ℕ) h)⟩
            have hlhs_Z : ∑ l : Fin N, matEntry data i.1 l.1 * Z l j =
                ∑ c : Fin n', matEntry x.mat i.1 (cols.getD c.1 0) * u c := by
              have hvanish : ∀ l : Fin N, l ∉ univ.map emb1 →
                matEntry data i.1 l.1 * Z l j = 0 := by
                intro l hlnot
                have hnot1 : ¬(l.1 < n') := fun hl1 ↦
                  hlnot (mem_map.mpr ⟨⟨l.1, hl1⟩, mem_univ _, Fin.ext rfl⟩)
                dsimp [Z]
                simp [hj1, hj2, hnot1]
              rw [← sum_subset (subset_univ (univ.map emb1)) fun l _ hl ↦ hvanish l hl, sum_map]
              refine sum_congr rfl fun c _ ↦ ?_
              rw [hdata_entry i (emb1 c)]
              have hval1 : (emb1 c).1 = c.1 := rfl
              dsimp [Z]
              simp [hval1, c.2, hj1, hj2]
            let embColsFun (c : Fin n') : Fin x.n := ⟨cols.getD c.1 0, (hcols_mem c).1⟩
            let embCols : Fin n' ↪ Fin x.n :=
              ⟨embColsFun, fun c₁ c₂ h ↦ hcols_inj c₁ c₂ (congrArg Fin.val h)⟩
            have hrhs_A : ∑ k : Fin x.n, matEntry x.mat i.1 k.1 * z k =
                ∑ c : Fin n', matEntry x.mat i.1 (cols.getD c.1 0) * u c := by
              have hvanishA : ∀ k : Fin x.n, k ∉ univ.map embCols →
                  matEntry x.mat i.1 k.1 * z k = 0 := by
                intro k hknot
                have hnot_cols : k.1 ∉ cols := by
                  intro hmem
                  apply hknot
                  let c : Fin n' := ⟨cols.idxOf k.1, List.idxOf_lt_length_iff.mpr hmem⟩
                  refine mem_map.mpr ⟨c, mem_univ c, Fin.ext ?_⟩
                  change cols.getD (cols.idxOf k.1) 0 = k.1
                  rw [List.getD_eq_getElem cols 0 (List.idxOf_lt_length_iff.mpr hmem),
                    List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hmem)]
                have hzero_entry : matEntry x.mat i.1 k.1 = 0 := by
                  by_contra hnz_e
                  exact hnot_cols ((mem_nonzeroCols_iff x k.1).mpr ⟨k.2, i.1, i.2, hnz_e⟩)
                rw [hzero_entry, zero_mul]
              rw [← sum_subset (subset_univ (univ.map embCols)) fun k _ hk ↦ hvanishA k hk,
                sum_map]
              rfl
            rw [hlhs_Z, hrhs_A]
      · dsimp only at j ⊢
        dsimp [Z]
        by_cases hj1 : j.1 < n'
        · have hne : ¬(j.1 = n' + j.1) := by omega
          simp only [hj1, hne, ↓reduceIte]
        · by_cases hj2 : j.1 < 2 * n'
          · have hne : ¬(j.1 = j.1 - n') := by omega
            simp only [hj1, hj2, hne, ↓reduceIte]
          · simp [hj1, hj2]
      · dsimp only
        let colNnz (j : Fin N) : Finset (Fin N) := univ.filter fun l : Fin N ↦ Z l j ≠ 0
        have hsum_cols :
            ((univ : Finset (Fin N × Fin N)).filter fun p ↦ Z p.1 p.2 ≠ 0).card =
              ∑ j : Fin N, (colNnz j).card := by
          simp only [colNnz, card_filter]
          rw [Fintype.sum_prod_type, sum_comm]
        rw [hsum_cols]
        let lastCol : Fin N := ⟨2 * n', by dsimp [N]; omega⟩
        rw [← sum_erase_add _ _ (mem_univ lastCol)]
        have herase_le : ∑ j ∈ univ.erase lastCol, (colNnz j).card ≤ 2 * n' := by
          have herase_card : (univ.erase lastCol).card = 2 * n' := by
            rw [card_erase_of_mem (mem_univ lastCol), card_univ, Fintype.card_fin]
            rfl
          calc
            ∑ j ∈ univ.erase lastCol, (colNnz j).card ≤ ∑ _j ∈ univ.erase lastCol, 1 :=
              sum_le_sum fun j hj ↦ by
                have hne : j ≠ lastCol := (mem_erase.mp hj).1
                have hj2 : j.1 < 2 * n' := by
                  have := j.2
                  have : j.1 ≠ 2 * n' := fun h ↦ hne (Fin.ext h)
                  dsimp [N] at this ⊢; omega
                by_cases hj1 : j.1 < n'
                · let l₀ : Fin N := ⟨n' + j.1, by dsimp [N]; omega⟩
                  have hsub : colNnz j ⊆ {l₀} := by
                    intro l hl
                    have hlz : Z l j ≠ 0 := (mem_filter.mp hl).2
                    dsimp [Z] at hlz
                    simp only [hj1, ↓reduceIte] at hlz
                    by_contra hne_l
                    have : l.1 ≠ n' + j.1 := fun h ↦ hne_l (mem_singleton.mpr (Fin.ext h))
                    simp [this] at hlz
                  exact (card_le_card hsub).trans_eq (card_singleton l₀)
                · let l₀ : Fin N := ⟨j.1 - n', by dsimp [N]; omega⟩
                  have hsub : colNnz j ⊆ {l₀} := by
                    intro l hl
                    have hlz : Z l j ≠ 0 := (mem_filter.mp hl).2
                    dsimp [Z] at hlz
                    simp only [hj1, hj2, ↓reduceIte] at hlz
                    by_contra hne_l
                    have : l.1 ≠ j.1 - n' := fun h ↦ hne_l (mem_singleton.mpr (Fin.ext h))
                    simp [this] at hlz
                  exact (card_le_card hsub).trans_eq (card_singleton l₀)
            _ = 2 * n' := by simp [herase_card]
        have hlast_le : (colNnz lastCol).card ≤ x.budget := by
          by_cases hlast_emp : colNnz lastCol = ∅
          · rw [hlast_emp, card_empty]; exact Nat.zero_le _
          · obtain ⟨l₀, hl₀⟩ := nonempty_iff_ne_empty.mpr hlast_emp
            have hlz₀ : Z l₀ lastCol ≠ 0 := (mem_filter.mp hl₀).2
            dsimp [Z, lastCol] at hlz₀
            have hnot1 : ¬(2 * n' < n') := by omega
            have hnot2 : ¬(2 * n' < 2 * n') := by omega
            simp only [hnot1, hnot2, ↓reduceIte] at hlz₀
            have hl₀_lt : l₀.1 < n' := by
              by_contra hnot_l; simp [hnot_l] at hlz₀
            have hx_n_pos : 0 < x.n :=
              Nat.lt_of_le_of_lt (Nat.zero_le _) (hcols_mem ⟨l₀.1, hl₀_lt⟩).1
            have hinj_last : (colNnz lastCol).card ≤
                (univ.filter fun k : Fin x.n ↦ z k ≠ 0).card := by
              refine Finset.card_le_card_of_injOn
                (fun l ↦ if hl1 : l.1 < n' then ⟨cols.getD l.1 0, (hcols_mem ⟨l.1, hl1⟩).1⟩
                         else ⟨0, hx_n_pos⟩)
                (fun l hl ↦ ?_) (fun l₁ hl₁ l₂ hl₂ hEq ↦ ?_)
              · have hlz : Z l lastCol ≠ 0 := (mem_filter.mp hl).2
                dsimp [Z, lastCol] at hlz
                simp only [hnot1, hnot2, ↓reduceIte] at hlz
                have hl1 : l.1 < n' := by
                  by_contra hnot_l; simp [hnot_l] at hlz
                simp only [hl1, ↓reduceDIte] at hlz ⊢
                exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hlz⟩)
              · have hlz1 : Z l₁ lastCol ≠ 0 := (mem_filter.mp (mem_coe.mp hl₁)).2
                have hlz2 : Z l₂ lastCol ≠ 0 := (mem_filter.mp (mem_coe.mp hl₂)).2
                dsimp [Z, lastCol] at hlz1 hlz2
                simp only [hnot1, hnot2, ↓reduceIte] at hlz1 hlz2
                have h1 : l₁.1 < n' := by
                  by_contra h; simp [h] at hlz1
                have h2 : l₂.1 < n' := by
                  by_contra h; simp [h] at hlz2
                simp only [h1, h2, ↓reduceDIte] at hEq
                have hv : cols.getD l₁.1 0 = cols.getD l₂.1 0 := congrArg Fin.val hEq
                have hc_eq := hcols_inj ⟨l₁.1, h1⟩ ⟨l₂.1, h2⟩ hv
                have hv_l : l₁.1 = l₂.1 := congrArg (Fin.val : Fin n' → ℕ) hc_eq
                exact Fin.ext hv_l
            exact hinj_last.trans hcard
        omega

end SSCDecision

/-- `SparseLinearSystem` reduces to `SSCDecision` in polynomial time. -/
theorem polyTimeReducible_SparseLinearSystem_SSCDecision :
    PolyTimeReducible encSparseLinearSystem encSSCDecision
      SparseLinearSystem SSCDecision :=
  ⟨SSCDecision.fromSparseLinearSystem,
    SSCDecision.computableInPolyTime_fromSparseLinearSystem,
    fun x ↦ (SSCDecision.fromSparseLinearSystem_mem_iff x).symm⟩

/-- **Sparse Subspace Clustering Decision (`SSCDecision`) is `NP`-hard.** -/
theorem SSCDecision_npHard : NPHard encSSCDecision SSCDecision :=
  SparseLinearSystem_npHard.trans polyTimeReducible_SparseLinearSystem_SSCDecision

/-- **Sparse Subspace Clustering Decision (`SSCDecision`) is `NP`-complete.** -/
theorem SSCDecision_npComplete : NPComplete encSSCDecision SSCDecision :=
  ⟨SSCDecision.mem_NP, SSCDecision_npHard⟩

end CslibFrontier.Computability.Complexity
