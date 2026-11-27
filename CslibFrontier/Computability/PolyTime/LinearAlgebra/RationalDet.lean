/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Exact Rational Matrix Determinant (`ratDet`)

This module implements and certifies `ratDet : RatTable → ℚ`, computing the exact determinant
`Matrix.det M.toMatrix` of any square rational `Cslib.LinearAlgebra.RatTable` in polynomial time
on multi-tape Turing machines (`Turing.MultiTapeTM.ComputableInPolyTime`).

The algorithm checks full rank via `ratRank`, and for invertible `n × n` matrices iterates Cramer's
rule on shrinking submatrices `S_r` of the original matrix `M` (`ratSolve` on `S_r * x = e_0`),
keeping every intermediate accumulator equal to `det(M) / det(S_r)` and hence polynomially
bounded in bit-length by Hadamard's bound.
-/

public section

namespace Cslib.LinearAlgebra

open Matrix
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Delete index `j` from a list of natural numbers (matching `Fin.succAbove j`). -/
def eraseIdxAt (l : List ℕ) (j : ℕ) : List ℕ :=
  (List.range (l.length - 1)).map fun i => l.getD (if i < j then i else i + 1) 0

/-- Extract the submatrix of `M` on rows `rowStart, ..., M.numRows - 1` and column indices
`cols`. -/
def subRatTable (M : RatTable) (rowStart : ℕ) (cols : List ℕ) : RatTable :=
  let m := M.numRows - rowStart
  let n := cols.length
  let rows := (List.range m).map fun r =>
    (List.range n).map fun c => M.entry (rowStart + r) (cols.getD c 0)
  { numRows := m, numCols := n, rows := rows }

/-- State of the Cramer-rule determinant loop. -/
structure RatDetState where
  /-- Current top row index of the remaining submatrix. -/
  rowIdx : ℕ
  /-- Remaining column indices in the current submatrix. -/
  cols : List ℕ
  /-- Accumulated determinant factor from previous elimination steps. -/
  acc : ℚ

/-- One step of the Cramer-rule determinant loop on an invertible square `RatTable`. -/
def ratDetStep (M : RatTable) (st : RatDetState) : RatDetState :=
  let sub := subRatTable M st.rowIdx st.cols
  let m := sub.numRows
  if m = 0 then st
  else
    let e0 : List ℚ := 1 :: List.replicate (m - 1) 0
    let sol := ((ratSolve { matrix := sub, rhs := e0 }).solution).getD []
    let jOpt := (List.range m).find? fun j => decide (sol.getD j 0 ≠ 0)
    let j := jOpt.getD 0
    let xj := sol.getD j 0
    let sgn : ℚ := if j % 2 = 0 then 1 else -1
    { rowIdx := st.rowIdx + 1
      cols := eraseIdxAt st.cols j
      acc := st.acc * (sgn / xj) }

/-- Exact rational determinant of a `RatTable`, returning `0` on non-square or singular tables. -/
def ratDet (M : RatTable) : ℚ :=
  if M.numRows ≠ M.numCols || ratRank M < M.numRows then 0
  else
    let init : RatDetState := { rowIdx := 0, cols := List.range M.numRows, acc := 1 }
    ((ratDetStep M)^[M.numRows] init).acc

private theorem det_eq_sgn_div_mul_submatrix {n : ℕ} {K : Type*} [Field K]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) {x : Fin (n + 1) → K}
    (hx : A *ᵥ x = Pi.single 0 1) {j : Fin (n + 1)} (hxj : x j ≠ 0) :
    A.det = ((if (j : ℕ) % 2 = 0 then (1 : K) else -1) / x j) *
      (A.submatrix Fin.succ j.succAbove).det := by
  let A' : Matrix (Fin (n + 1)) (Fin (n + 1)) K := A.updateCol j (A *ᵥ x)
  have hdet1 : A'.det = x j * A.det := by
    rw [show A' = A.updateCol j (fun i => ∑ k : Fin (n + 1), x k • A i k) from by
      ext i l
      by_cases hlj : l = j
      · subst hlj
        simp [A', Matrix.updateCol_self, Matrix.mulVec, dotProduct, mul_comm]
      · simp [A', Matrix.updateCol_ne hlj]]
    rw [Matrix.det_updateCol_sum, smul_eq_mul]
  have hdet2 : A'.det = (-1 : K) ^ (j : ℕ) * (A.submatrix Fin.succ j.succAbove).det := by
    rw [Matrix.det_succ_column A' j]
    rw [Finset.sum_eq_single 0]
    · simp only [Fin.val_zero, zero_add, A', Matrix.updateCol_self, hx, Pi.single_eq_same,
        mul_one]
      congr 1
      congr 1
      ext r c
      simp only [Matrix.submatrix_apply, Matrix.updateCol_ne (Fin.succAbove_ne j c),
        Fin.succAbove_zero]
    · intro i _ hi0
      simp [A', Matrix.updateCol_self, hx, Pi.single_eq_of_ne hi0]
    · intro h; exact absurd (Finset.mem_univ 0) h
  have hsgn : (-1 : K) ^ (j : ℕ) = if (j : ℕ) % 2 = 0 then (1 : K) else -1 := by
    rcases Nat.even_or_odd (j : ℕ) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hmod : (j : ℕ) % 2 = 0 := by omega
      simp only [hmod, ↓reduceIte]
      rw [hm, ← two_mul, pow_mul]; norm_num
    · have hmod : (j : ℕ) % 2 ≠ 0 := by omega
      simp only [hmod, ↓reduceIte]
      rw [hm, pow_add, pow_mul]; norm_num
  rw [hdet2, hsgn] at hdet1
  have hEq : x j * A.det = (if (j : ℕ) % 2 = 0 then (1 : K) else -1) *
      (A.submatrix Fin.succ j.succAbove).det := hdet1.symm
  field_simp [hxj]
  rw [mul_comm, hEq]

private theorem det_ne_zero_iff_rank_eq (M : RatTable) (hsq : M.numRows = M.numCols) :
    (M.toMatrix.reindex (Equiv.refl _) (finCongr hsq.symm)).det ≠ 0 ↔
      ratRank M = M.numRows := by
  let A := M.toMatrix.reindex (Equiv.refl _) (finCongr hsq.symm)
  have hrank_eq : ratRank M = A.rank := by
    rw [ratRank_eq, Matrix.rank_reindex]
  rw [hrank_eq]
  constructor
  · intro hdet
    have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
    have hli : LinearIndependent ℚ A.col := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hmv : A *ᵥ c = 0 := by
        ext i; simpa [Matrix.mulVec, dotProduct, mul_comm, Matrix.col_apply] using congrFun hc i
      have h0 : c = 0 := by
        have := congrArg (A⁻¹ *ᵥ ·) hmv
        simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit] using this
      exact fun j => congrFun h0 j
    rw [Matrix.rank_eq_finrank_span_cols]
    simpa using finrank_span_eq_card hli
  · intro hrank h0
    rw [Matrix.rank_eq_finrank_span_cols] at hrank
    have hfull : Submodule.span ℚ (Set.range A.col) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by simpa [Module.finrank_pi] using hrank)
    have hli : LinearIndependent ℚ A.col :=
      linearIndependent_of_top_le_span_of_card_eq_finrank (by rw [hfull]) (by simp)
    have hinj : Function.Injective (Matrix.mulVecLin A) := by
      rw [injective_iff_map_eq_zero]
      intro c hc
      have hsum : ∑ j, c j • A.col j = 0 := by
        ext i
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, mul_comm, Matrix.col_apply] using
          congrFun hc i
      exact funext (Fintype.linearIndependent_iff.mp hli c hsum)
    obtain ⟨v, hv0, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hv0 (hinj (by rw [Matrix.mulVecLin_apply, hAv, map_zero]))

private theorem ratDet_spec_aux (M : RatTable) (hsq : M.numRows = M.numCols)
    (hdet_ne : (M.toMatrix.reindex (Equiv.refl _) (finCongr hsq.symm)).det ≠ 0) :
    let n := M.numRows
    ∀ r ≤ n,
      let st := (ratDetStep M)^[r] { rowIdx := 0, cols := List.range n, acc := 1 }
      st.rowIdx = r ∧ st.cols.length = n - r ∧
        (∀ c ∈ st.cols, c < n) ∧
        let S : Matrix (Fin (n - r)) (Fin (n - r)) ℚ :=
          Matrix.of fun i j => M.entry (r + i.val) (st.cols.getD j.val 0)
        (M.toMatrix.reindex (Equiv.refl _) (finCongr hsq.symm)).det = st.acc * S.det := by
  intro n r hr
  induction r with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.sub_zero, List.length_range, true_and, one_mul]
    refine ⟨fun c hc => List.mem_range.mp hc, ?_⟩
    congr 1
    ext i j
    simp [Cslib.RowTable.toMatrix_apply, List.getD_eq_getElem?_getD]
  | succ r ih =>
    obtain ⟨hrow, hlen, hlt, hdet_eq⟩ := ih (by omega)
    set st := (ratDetStep M)^[r] { rowIdx := 0, cols := List.range n, acc := 1 }
    have hm_eq : (subRatTable M st.rowIdx st.cols).numRows = n - r := by
      simp [subRatTable, hrow, n]
    have hm_pos : n - r ≠ 0 := by omega
    have hcols_eq : (subRatTable M st.rowIdx st.cols).numCols = n - r := by
      simp [subRatTable, hlen]
    set sub := subRatTable M st.rowIdx st.cols
    let S : Matrix (Fin (n - r)) (Fin (n - r)) ℚ :=
      Matrix.of fun i j => M.entry (r + i.val) (st.cols.getD j.val 0)
    have hS_det_ne : S.det ≠ 0 := fun h0 => hdet_ne (by rw [hdet_eq, h0, mul_zero])
    have hsub_eq : ∀ (i : Fin sub.numRows) (j : Fin sub.numCols),
        sub.toMatrix i j = S ⟨i.val, hm_eq ▸ i.isLt⟩ ⟨j.val, hcols_eq ▸ j.isLt⟩ := fun i j => by
      rw [Cslib.RowTable.toMatrix_apply, Cslib.RowTable.entry]
      simp only [sub, subRatTable, S, Matrix.of_apply, hrow]
      have hi' : i.val < M.numRows - r := by simpa [sub, subRatTable, hrow] using i.isLt
      have hj' : j.val < st.cols.length := by simpa [sub, subRatTable] using j.isLt
      simp [List.getD_eq_getElem?_getD, hi', hj']
    have hex_sol : ∃ x : Fin sub.numCols → ℚ,
        sub.toMatrix *ᵥ x = fun i => (1 :: List.replicate (sub.numRows - 1) 0).getD i.val 0 := by
      have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hS_det_ne
      let zeroFin : Fin (n - r) := ⟨0, by omega⟩
      let x0 : Fin (n - r) → ℚ := S⁻¹ *ᵥ (Pi.single zeroFin (1 : ℚ) : Fin (n - r) → ℚ)
      refine ⟨fun j => x0 ⟨j.val, hcols_eq ▸ j.isLt⟩, ?_⟩
      ext i
      rw [Matrix.mulVec, dotProduct]
      have hmul0 : (S *ᵥ x0) ⟨i.val, hm_eq ▸ i.isLt⟩ =
          (Pi.single zeroFin (1 : ℚ) : Fin (n - r) → ℚ) ⟨i.val, hm_eq ▸ i.isLt⟩ := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hunit, Matrix.one_mulVec]
      have hsum_eq : ∑ j : Fin sub.numCols, sub.toMatrix i j * x0 ⟨j.val, hcols_eq ▸ j.isLt⟩ =
          (S *ᵥ x0) ⟨i.val, hm_eq ▸ i.isLt⟩ := by
        rw [Matrix.mulVec, dotProduct]
        refine Finset.sum_equiv (finCongr hcols_eq) (fun _ => by simp) (fun j _ => ?_)
        rw [hsub_eq i j]; rfl
      rw [hsum_eq, hmul0]
      rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
      · simp [zeroFin, hi0]
      · have hk : i.val - 1 < sub.numRows - 1 := by have := i.isLt; omega
        have hi_eq : i.val = (i.val - 1) + 1 := by omega
        have hne : (⟨i.val, hm_eq ▸ i.isLt⟩ : Fin (n - r)) ≠ zeroFin := by
          intro h; have := congrArg Fin.val h; dsimp [zeroFin] at this; omega
        rw [Pi.single_eq_of_ne hne, hi_eq, List.getD_cons_succ, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp [hk]), Option.getD_some, List.getElem_replicate]
    have hsol_some : ∃ sol : List ℚ,
        (ratSolve { matrix := sub, rhs := 1 :: List.replicate (sub.numRows - 1) 0 }).solution =
          some sol := by
      let rhs : List ℚ := 1 :: List.replicate (sub.numRows - 1) 0
      cases h : (ratSolve { matrix := sub, rhs := rhs }).solution with
      | none => exact absurd hex_sol ((ratSolve_spec _).2.mp h)
      | some sol => exact ⟨sol, rfl⟩
    obtain ⟨sol, hsol_eq⟩ := hsol_some
    obtain ⟨_, hsol_mv⟩ := (ratSolve_spec _).1 sol hsol_eq
    have hex_nz : ∃ j ∈ List.range sub.numRows, decide (sol.getD j 0 ≠ 0) = true := by
      by_contra hall
      push Not at hall
      have h0 := congrFun hsol_mv ⟨0, by dsimp; omega⟩
      rw [Matrix.mulVec, dotProduct] at h0
      have hsum0 : ∑ j : Fin sub.numCols,
          sub.toMatrix ⟨0, by omega⟩ j * sol.getD j.val 0 = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        have hdj := hall j.val (List.mem_range.mpr (by have := j.isLt; omega))
        have hdj0 : sol.getD j.val 0 = 0 := by simpa using hdj
        rw [hdj0, mul_zero]
      dsimp only at h0
      rw [hsum0] at h0
      simp at h0
    have hfind : ∃ j,
        ((List.range sub.numRows).find? fun j => decide (sol.getD j 0 ≠ 0)) = some j :=
      Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex_nz)
    obtain ⟨j, hj_eq⟩ := hfind
    have hj_lt : j < n - r := by
      have := List.mem_of_find?_eq_some hj_eq
      rw [List.mem_range] at this; omega
    have hxj_ne : sol.getD j 0 ≠ 0 := by
      have := List.find?_some hj_eq; simpa using this
    rw [Function.iterate_succ_apply']
    have hstep_eq : ratDetStep M st =
        { rowIdx := st.rowIdx + 1, cols := eraseIdxAt st.cols j,
          acc := st.acc * ((if j % 2 = 0 then (1 : ℚ) else -1) / sol.getD j 0) } := by
      unfold ratDetStep
      have hsub_ne : sub.numRows ≠ 0 := by omega
      have hsol_eq' := hsol_eq
      have hj_eq' := hj_eq
      dsimp only [sub] at hsub_ne hsol_eq' hj_eq'
      simp only [hsub_ne, ↓reduceIte, hsol_eq', Option.getD_some, hj_eq']
    rw [hstep_eq]
    refine ⟨by dsimp; omega, by simp [eraseIdxAt, hlen]; omega, fun c hc => ?_, ?_⟩
    · simp only [eraseIdxAt, List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      have hidx : (if i < j then i else i + 1) < st.cols.length := by
        split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
      exact hlt _ (List.getElem_mem hidx)
    · have hdim_succ : n - (r + 1) + 1 = n - r := by omega
      let e_dim : Fin (n - (r + 1) + 1) ≃ Fin (n - r) := finCongr hdim_succ
      let A : Matrix (Fin (n - (r + 1) + 1)) (Fin (n - (r + 1) + 1)) ℚ :=
        S.reindex e_dim.symm e_dim.symm
      have hAdet : A.det = S.det := Matrix.det_reindex_self e_dim.symm S
      let xVec : Fin (n - (r + 1) + 1) → ℚ := fun k => sol.getD k.val 0
      have hAx : A *ᵥ xVec = Pi.single 0 1 := by
        ext i
        have hi_sub : i.val < sub.numRows := by omega
        have h0 := congrFun hsol_mv ⟨i.val, by dsimp; omega⟩
        dsimp only at h0
        rw [Matrix.mulVec, dotProduct] at h0 ⊢
        have hsum_A : ∑ k : Fin (n - (r + 1) + 1), A i k * xVec k =
            ∑ k : Fin sub.numCols, sub.toMatrix ⟨i.val, hi_sub⟩ k * sol.getD k.val 0 := by
          refine Finset.sum_equiv (finCongr (by omega : n - (r + 1) + 1 = sub.numCols))
            (fun _ => by simp) (fun k _ => ?_)
          simp only [A, Matrix.reindex_apply, Matrix.submatrix_apply, xVec, hsub_eq]
          rfl
        rw [hsum_A, h0]
        cases hi : i.val with
        | zero =>
          simp only [Pi.single_apply, Fin.ext_iff, Fin.val_zero, hi, ↓reduceIte,
            List.getD_cons_zero]
        | succ k' =>
          have hk' : k' < sub.numRows - 1 := by omega
          simp [Fin.ext_iff, hi, List.getD_eq_getElem?_getD, hk']
      let jFin : Fin (n - (r + 1) + 1) := ⟨j, by omega⟩
      have hCramer := det_eq_sgn_div_mul_submatrix A hAx (j := jFin) hxj_ne
      rw [hAdet] at hCramer
      dsimp only
      rw [hdet_eq, hCramer, ← mul_assoc]
      congr 1
      congr 1
      ext i k
      simp only [Matrix.submatrix_apply, A, Matrix.reindex_apply, S, Matrix.of_apply, e_dim,
        finCongr_symm, finCongr_apply, Fin.val_cast, Fin.val_succ, eraseIdxAt]
      have hk_len : k.val < st.cols.length - 1 := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk_len,
        Option.map_some, Option.getD_some]
      have hsucc : (jFin.succAbove k).val = if k.val < j then k.val else k.val + 1 := by
        simp only [Fin.succAbove, jFin, Fin.lt_def, Fin.val_castSucc]
        split_ifs <;> simp
      rw [hsucc, show r + (i.val + 1) = r + 1 + i.val by omega]

/-- Exact specification of `ratDet`: for any square `RatTable`, `ratDet M = M.toMatrix.det`. -/
theorem ratDet_spec (M : RatTable) (hsq : M.numRows = M.numCols) :
    ratDet M = (M.toMatrix.reindex (Equiv.refl _) (finCongr hsq.symm)).det := by
  unfold ratDet
  have hnotne : ¬(M.numRows ≠ M.numCols) := not_not.mpr hsq
  by_cases hrank : ratRank M < M.numRows
  · simp only [hnotne, decide_false, hrank, decide_true, Bool.false_or, ↓reduceIte]
    by_contra hne
    have hrank_eq := (det_ne_zero_iff_rank_eq M hsq).mp (fun h => hne h.symm)
    omega
  · simp only [hnotne, decide_false, hrank, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    have hrank_le : ratRank M ≤ M.numRows := by
      rw [ratRank_eq]
      exact Matrix.rank_le_height _
    have hdet_ne : (M.toMatrix.reindex (Equiv.refl _) (finCongr hsq.symm)).det ≠ 0 :=
      (det_ne_zero_iff_rank_eq M hsq).mpr (by omega)
    obtain ⟨_, _, _, hdet_eq⟩ := ratDet_spec_aux M hsq hdet_ne M.numRows le_rfl
    have h0 : M.numRows - M.numRows = 0 := Nat.sub_self _
    have hdet0 : (Matrix.of fun (i j : Fin (M.numRows - M.numRows)) =>
        M.entry (M.numRows + i.val) (((ratDetStep M)^[M.numRows]
          { rowIdx := 0, cols := List.range M.numRows, acc := 1 }).cols.getD j.val 0)).det = 1 := by
      have : IsEmpty (Fin (M.numRows - M.numRows)) := by rw [h0]; infer_instance
      exact Matrix.det_isEmpty
    rw [hdet_eq, hdet0, mul_one]

private enc_structure encRatDetState : RatDetState where
  rowIdx : encUnary,
  cols : (encList encUnary),
  acc : encRat

private theorem eraseIdxAt_polyTime :
    ComputableInPolyTime (fun p : List ℕ × ℕ => eraseIdxAt p.1 p.2)
      (encPair (encList encUnary) encUnary) (encList encUnary) := by
  unfold eraseIdxAt
  have hl := fst (encList encUnary) encUnary
  have hj := snd (encList encUnary) encUnary
  refine mapWithInput (range.comp (unary_sub' ((length_list encUnary).comp hl) (const 1))) ?_
  have hi := snd (encPair (encList encUnary) encUnary) encUnary
  have hl' := hl.comp (fst (encPair (encList encUnary) encUnary) encUnary)
  have hj' := hj.comp (fst (encPair (encList encUnary) encUnary) encUnary)
  have hidx := (unary_lt' hi hj').ite_decide hi (unary_add' hi (const 1))
  exact listGetDWithInput hl' hidx 0

private theorem entry_polyTime :
    ComputableInPolyTime (fun p : (RatTable × ℕ) × ℕ => p.1.1.entry p.1.2 p.2)
      (encPair (encPair RatTable.enc encUnary) encUnary) encRat := by
  have hrow1 : ComputableInPolyTime (fun p : RatTable × ℕ => p.1.rows.getD p.2 [])
      (encPair RatTable.enc encUnary) (encList encRat) :=
    listGetDWithInput (RatTable.enc_rows_polyTime (fst RatTable.enc encUnary))
      (snd RatTable.enc encUnary) ([] : List ℚ)
  exact (listGetDWithInput
    (hrow1.comp (fst (encPair RatTable.enc encUnary) encUnary))
    (snd (encPair RatTable.enc encUnary) encUnary) (0 : ℚ)).of_enc_eq fun _ => rfl

private theorem subRatTable_polyTime :
    ComputableInPolyTime (fun p : (RatTable × ℕ) × List ℕ => subRatTable p.1.1 p.1.2 p.2)
      (encPair (encPair RatTable.enc encUnary) (encList encUnary)) RatTable.enc := by
  unfold subRatTable
  have hM := (fst RatTable.enc encUnary).comp
    (fst (encPair RatTable.enc encUnary) (encList encUnary))
  have hrs := (snd RatTable.enc encUnary).comp
    (fst (encPair RatTable.enc encUnary) (encList encUnary))
  have hcols := snd (encPair RatTable.enc encUnary) (encList encUnary)
  have hm := unary_sub' (RatTable.enc_numRows_polyTime hM) hrs
  have hn := (length_list encUnary).comp hcols
  have hrow : ComputableInPolyTime
      (fun q : ((RatTable × ℕ) × List ℕ) × ℕ =>
        (List.range q.1.2.length).map fun c =>
          q.1.1.1.entry (q.1.1.2 + q.2) (q.1.2.getD c 0))
      (encPair (encPair (encPair RatTable.enc encUnary) (encList encUnary)) encUnary)
      (encList encRat) := by
    refine mapWithInput
      (f := fun (a : ((RatTable × ℕ) × List ℕ) × ℕ) (c : ℕ) =>
        a.1.1.1.entry (a.1.1.2 + a.2) (a.1.2.getD c 0))
      (range.comp (hn.comp (fst _ _))) ?_
    let encOuter :=
      encPair (encPair (encPair RatTable.enc encUnary) (encList encUnary)) encUnary
    have hc := snd encOuter encUnary
    have hr := (snd (encPair (encPair RatTable.enc encUnary) (encList encUnary)) encUnary).comp
      (fst encOuter encUnary)
    have hfst2 := (fst (encPair (encPair RatTable.enc encUnary) (encList encUnary)) encUnary).comp
      (fst encOuter encUnary)
    have hM' := hM.comp hfst2
    have hrs' := hrs.comp hfst2
    have hcols' := hcols.comp hfst2
    have hcolIdx := listGetDWithInput hcols' hc 0
    have hrowIdx := unary_add' hrs' hr
    exact (entry_polyTime.comp ((hM'.prod hrowIdx).prod hcolIdx)).of_enc_eq fun _ => rfl
  have hrows := mapWithInput
    (f := fun (a : (RatTable × ℕ) × List ℕ) (r : ℕ) =>
      (List.range a.2.length).map fun c => a.1.1.entry (a.1.2 + r) (a.2.getD c 0))
    (range.comp hm) hrow
  exact RatTable.enc_mk_polyTime hm hn hrows

private theorem ratDetStep_polyTime :
    ComputableInPolyTime (fun p : RatTable × RatDetState => ratDetStep p.1 p.2)
      (encPair RatTable.enc encRatDetState) encRatDetState := by
  unfold ratDetStep
  have hM := fst RatTable.enc encRatDetState
  have hst := snd RatTable.enc encRatDetState
  have hrow := encRatDetState_rowIdx_polyTime hst
  have hcols := encRatDetState_cols_polyTime hst
  have hacc := encRatDetState_acc_polyTime hst
  have hsub := subRatTable_polyTime.comp ((hM.prod hrow).prod hcols)
  have hm := RatTable.enc_numRows_polyTime hsub
  have he0 := (cons encRat).comp
    ((const (1 : ℚ)).prod (replicate (unary_sub' hm (const 1)) (const (0 : ℚ))))
  have hres := ratSolve_computableInPolyTime.comp (LinearSystemInput.enc_mk_polyTime hsub he0)
  have hsol := (optionGetD (encList encRat)).comp
    ((LinearSolveResult.enc_solution_polyTime hres).prod (const ([] : List ℚ)))
  have hjOpt : ComputableInPolyTime
      (fun p : RatTable × RatDetState =>
        let sub := subRatTable p.1 p.2.rowIdx p.2.cols
        let rhs := 1 :: List.replicate (sub.numRows - 1) 0
        let sol := ((ratSolve { matrix := sub, rhs := rhs }).solution).getD []
        (List.range sub.numRows).find? fun j => decide (sol.getD j 0 ≠ 0))
      (encPair RatTable.enc encRatDetState) (encOption encUnary) := by
    refine findWithInput (range.comp hm) ?_
    have hj := snd (encPair RatTable.enc encRatDetState) encUnary
    exact bool_not.comp (rat_isZero' (listGetDWithInput (hsol.comp (fst _ _)) hj 0))
  have hj := (optionGetD encUnary).comp (hjOpt.prod (const 0))
  have hxj := listGetDWithInput hsol hj 0
  have hsgn : ComputableInPolyTime
      (fun p : RatTable × RatDetState =>
        let sub := subRatTable p.1 p.2.rowIdx p.2.cols
        let rhs := 1 :: List.replicate (sub.numRows - 1) 0
        let sol := ((ratSolve { matrix := sub, rhs := rhs }).solution).getD []
        let j := ((List.range sub.numRows).find? fun j => decide (sol.getD j 0 ≠ 0)).getD 0
        if j % 2 = 0 then (1 : ℚ) else -1)
      (encPair RatTable.enc encRatDetState) encRat :=
    ((beq (binary_mod' (unary_to_binary.comp hj) (const 2)) (const 0)).of_enc_eq fun _ =>
      rfl).ite_decide (const (1 : ℚ)) (const (-1 : ℚ))
  have hnext := encRatDetState_mk_polyTime (unary_add' hrow (const 1))
    (eraseIdxAt_polyTime.comp (hcols.prod hj))
    (rat_mul' hacc (rat_div' hsgn hxj))
  exact ((unary_beq hm (const 0)).of_enc_eq fun _ => rfl).ite_decide hst hnext

/-- **Polynomial-time computability of `ratDet`**: computing the exact rational determinant of
a `RatTable` is computable in polynomial time on multi-tape Turing machines. -/
@[fun_prop]
theorem ratDet_computableInPolyTime :
    ComputableInPolyTime ratDet RatTable.enc encRat := by
  have hcond : ComputableInPolyTime
      (fun M : RatTable => decide (M.numRows ≠ M.numCols) || decide (ratRank M < M.numRows))
      RatTable.enc encBool :=
    bool_or' (bool_not.comp ((unary_beq
      (RatTable.enc_numRows_polyTime id') (RatTable.enc_numCols_polyTime id')).of_enc_eq
        fun _ => rfl))
      (unary_lt' ratRank_computableInPolyTime (RatTable.enc_numRows_polyTime id'))
  have hcount : ComputableInPolyTime
      (fun M : RatTable =>
        if decide (M.numRows ≠ M.numCols) || decide (ratRank M < M.numRows) then 0 else M.numRows)
      RatTable.enc encUnary :=
    hcond.ite (const 0) (RatTable.enc_numRows_polyTime id')
  have hinit := encRatDetState_mk_polyTime (const 0)
    (range.comp (RatTable.enc_numRows_polyTime id')) (const (1 : ℚ))
  have hiter := iterateWith (step := ratDetStep) id' hcount hinit ratDetStep_polyTime
    (bound := fun M => 60 * ((RatTable.enc M).length + 1) ^ 3)
    (PolyBounded.of_forall_le 60 3 fun _ => le_rfl)
    fun M r hr => by
      set L := (RatTable.enc M).length
      have hM_rows : M.numRows ≤ L := by
        have := RatTable.enc_numRows_length_le M
        dsimp only [L]
        simpa [encUnary_apply, List.length_replicate] using this
      have hM_cols : M.numCols ≤ L := by
        have := RatTable.enc_numCols_length_le M
        dsimp only [L]
        simpa [encUnary_apply, List.length_replicate] using this
      by_cases hbad : (decide (M.numRows ≠ M.numCols) || decide (ratRank M < M.numRows)) = true
      · simp only [hbad, ↓reduceIte, Nat.le_zero] at hr
        subst hr
        simp only [Function.iterate_zero, id_eq]
        have hcols_enc : (encList encUnary (List.range M.numRows)).length ≤
            M.numRows * (2 * M.numRows + 1) := by
          refine (length_encList_le encUnary (List.range M.numRows) (b := M.numRows) fun c hc =>
            ?_).trans (by simp)
          simp only [encUnary_apply, List.length_replicate]
          exact (List.mem_range.mp hc).le
        have h1_enc : (encRat 1).length ≤ 10 := by
          have := length_encRat_le (1 : ℚ) (A := 1) (B := 1) (by decide) (by decide)
          have hs : (1 : ℕ).size ≤ 1 := by decide
          omega
        dsimp only [Function.comp_apply]
        rw [encRatDetState_apply]
        dsimp only [encRatDetStateFields]
        rw [length_encPair, length_encPair]
        simp only [encUnary_apply, List.length_replicate]
        have hL3 := Nat.one_le_pow 3 (L + 1) (by omega)
        have hmr : M.numRows * (2 * M.numRows + 1) ≤ L * (2 * L + 1) := by nlinarith
        nlinarith
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hr
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_ne_iff, not_lt] at hbad
        obtain ⟨hsq, hrank_ge⟩ := hbad
        have hrank_le : ratRank M ≤ M.numRows := by rw [ratRank_eq]; exact Matrix.rank_le_height _
        have hdet_ne : (M.toMatrix.reindex (Equiv.refl _) (finCongr hsq.symm)).det ≠ 0 :=
          (det_ne_zero_iff_rank_eq M hsq).mpr (by omega)
        set st := (ratDetStep M)^[r] { rowIdx := 0, cols := List.range M.numRows, acc := 1 }
        obtain ⟨hrow, hlen, hlt, hdet_eq⟩ := ratDet_spec_aux M hsq hdet_ne r hr
        change st.rowIdx = r at hrow
        change st.cols.length = M.numRows - r at hlen
        change ∀ c ∈ st.cols, c < M.numRows at hlt
        have hacc_enc : (encRat st.acc).length ≤ 25 * (L + 1) ^ 3 := by
          have hsub_det_bound : ∀ {m : ℕ} (hm : m ≤ M.numRows) (R C : Fin m → Fin M.numRows),
              let A : Matrix (Fin m) (Fin m) ℚ :=
                fun i j => M.toMatrix (R i) ⟨(C j).val, hsq ▸ (C j).isLt⟩
              ∃ (num : ℤ) (den : ℕ), 1 ≤ den ∧ A.det = (num : ℚ) / (den : ℚ) ∧
                num.natAbs ≤ 2 ^ (3 * (L + 1) ^ 3) ∧ den ≤ 2 ^ (3 * (L + 1) ^ 3) := by
            intro m hm R C A
            have hmL : m ≤ L := hm.trans hM_rows
            have hEntry : ∀ i j,
                (M.toMatrix i j).num.natAbs ≤ 2 ^ L ∧ (M.toMatrix i j).den ≤ 2 ^ L := by
              intro i j
              have hrows_enc : (encList (encList encRat) M.rows).length ≤ L :=
                RatTable.enc_rows_length_le M
              rw [Cslib.RowTable.toMatrix_apply, Cslib.RowTable.entry]
              by_cases hi : i.val < M.rows.length
              · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
                  Option.getD_some]
                have hrow_l : (encList encRat M.rows[i.val]).length ≤ L :=
                  (length_le_encList_of_mem _ (List.getElem_mem hi)).trans hrows_enc
                by_cases hj : j.val < M.rows[i.val].length
                · simp only [List.getElem?_eq_getElem hj, Option.getD_some]
                  have hq : (encRat M.rows[i.val][j.val]).length ≤ L :=
                    (length_le_encList_of_mem _ (List.getElem_mem hj)).trans hrow_l
                  exact ⟨(natAbs_num_lt_two_pow_length_encRat _).le.trans
                      (Nat.pow_le_pow_right (by omega) hq),
                    (den_lt_two_pow_length_encRat _).le.trans
                      (Nat.pow_le_pow_right (by omega) hq)⟩
                · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD_none]
                  exact ⟨Nat.zero_le _, Nat.one_le_two_pow⟩
              · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi),
                  Option.getD_none, List.getElem?_nil]
                exact ⟨Nat.zero_le _, Nat.one_le_two_pow⟩
            let Drow : Fin m → ℕ := fun i => ∏ j : Fin m, (A i j).den
            let D : ℕ := ∏ i : Fin m, Drow i
            have hDrow_pos : ∀ i, 1 ≤ Drow i := fun i =>
              Nat.succ_le_of_lt (Finset.prod_pos fun j _ => (A i j).den_pos)
            have hDpos : 1 ≤ D := Nat.succ_le_of_lt (Finset.prod_pos fun i _ => hDrow_pos i)
            let Aint : Matrix (Fin m) (Fin m) ℤ := fun i j =>
              (A i j).num * ((Drow i / (A i j).den : ℕ) : ℤ)
            have hAint_eq : A.det = (Aint.det : ℚ) / (D : ℚ) := by
              have hrow_scale : Aint.map (algebraMap ℤ ℚ) =
                  Matrix.of fun i j => (Drow i : ℚ) * A i j := by
                ext i j
                change (algebraMap ℤ ℚ) ((A i j).num * ((Drow i / (A i j).den : ℕ) : ℤ)) =
                  (Drow i : ℚ) * A i j
                have hdvd : (A i j).den ∣ Drow i :=
                  Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
                have hqd : ((A i j).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (A i j).den_ne_zero
                rw [eq_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd hqd,
                  ← mul_div_assoc, mul_comm ((A i j).num : ℚ), mul_div_assoc, Rat.num_div_den,
                  mul_comm]
              have hdet_scale : (Aint.det : ℚ) = (D : ℚ) * A.det := by
                rw [show (Aint.det : ℚ) = (Aint.map (algebraMap ℤ ℚ)).det from
                    RingHom.map_det (algebraMap ℤ ℚ) Aint,
                  hrow_scale]
                have hdiag : (Matrix.of fun i j => (Drow i : ℚ) * A i j) =
                    Matrix.diagonal (fun i => (Drow i : ℚ)) * A := by
                  ext i j; simp [Matrix.diagonal_mul]
                rw [hdiag, Matrix.det_mul, Matrix.det_diagonal]; simp [D]
              rw [hdet_scale, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (by omega))]
            have hDrow_le : ∀ i, Drow i ≤ 2 ^ (L * L) := fun i => by
              calc Drow i ≤ ∏ _j : Fin m, 2 ^ L :=
                  Finset.prod_le_prod fun j _ =>
                    (hEntry (R i) ⟨(C j).val, hsq ▸ (C j).isLt⟩).2
                _ = (2 ^ L) ^ m := by simp
                _ = 2 ^ (L * m) := by rw [← pow_mul]
                _ ≤ 2 ^ (L * L) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left L hmL)
            have hD_le : D ≤ 2 ^ (3 * (L + 1) ^ 3) := by
              calc D ≤ ∏ _i : Fin m, 2 ^ (L * L) :=
                  Finset.prod_le_prod fun i _ => hDrow_le i
                _ = (2 ^ (L * L)) ^ m := by simp
                _ = 2 ^ (L * L * m) := by rw [← pow_mul]
                _ ≤ 2 ^ (3 * (L + 1) ^ 3) := Nat.pow_le_pow_right (by omega) (by nlinarith)
            have hAint_le : ∀ i j, (Aint i j).natAbs ≤ 2 ^ ((L + 1) * L) := fun i j => by
              dsimp only [Aint]
              rw [Int.natAbs_mul, Int.natAbs_natCast]
              calc (A i j).num.natAbs * (Drow i / (A i j).den)
                  ≤ 2 ^ L * 2 ^ (L * L) :=
                    Nat.mul_le_mul (hEntry (R i) ⟨(C j).val, hsq ▸ (C j).isLt⟩).1
                      ((Nat.div_le_self _ _).trans (hDrow_le i))
                _ = 2 ^ (L + L * L) := by rw [← pow_add]
                _ = 2 ^ ((L + 1) * L) := by ring_nf
            have hdet_le : Aint.det.natAbs ≤ 2 ^ (3 * (L + 1) ^ 3) := by
              rw [Matrix.det_apply]
              refine (Int.natAbs_sum_le _ _).trans ?_
              have hterm : ∀ σ : Equiv.Perm (Fin m),
                  (Equiv.Perm.sign σ • ∏ i : Fin m, Aint (σ i) i).natAbs ≤
                    (2 ^ ((L + 1) * L)) ^ m := fun σ => by
                have hnatAbs_prod : ∀ (s : Finset (Fin m)) (f : Fin m → ℤ),
                    (∏ i ∈ s, f i).natAbs = ∏ i ∈ s, (f i).natAbs := by
                  intro s f
                  induction s using Finset.induction_on with
                  | empty => simp
                  | insert u s hu ih =>
                    rw [Finset.prod_insert hu, Finset.prod_insert hu, Int.natAbs_mul, ih]
                have hsign : ((Equiv.Perm.sign σ : ℤ)).natAbs = 1 := by
                  cases Int.units_eq_one_or (Equiv.Perm.sign σ) <;> simp [*]
                change ((Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, Aint (σ i) i).natAbs ≤ _
                rw [Int.natAbs_mul, hsign, one_mul, hnatAbs_prod]
                calc ∏ i : Fin m, (Aint (σ i) i).natAbs
                    ≤ ∏ _i : Fin m, 2 ^ ((L + 1) * L) :=
                      Finset.prod_le_prod fun i _ => hAint_le (σ i) i
                  _ = (2 ^ ((L + 1) * L)) ^ m := by simp
              refine (Finset.sum_le_sum fun σ _ => hterm σ).trans ?_
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
                smul_eq_mul]
              have hfac : m.factorial ≤ 2 ^ (m * m) := by
                calc m.factorial ≤ m ^ m := Nat.factorial_le_pow m
                  _ ≤ (2 ^ m) ^ m := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) m
                  _ = 2 ^ (m * m) := by rw [← pow_mul]
              have hpow_exp : m * m + (L + 1) * L * m ≤ 3 * (L + 1) ^ 3 := by
                have h1 : m * m ≤ L * L := Nat.mul_le_mul hmL hmL
                have h2 : (L + 1) * L * m ≤ (L + 1) * L * L := Nat.mul_le_mul_left _ hmL
                nlinarith
              calc m.factorial * (2 ^ ((L + 1) * L)) ^ m
                  ≤ 2 ^ (m * m) * 2 ^ ((L + 1) * L * m) := by
                    rw [← pow_mul]; exact Nat.mul_le_mul hfac le_rfl
                _ = 2 ^ (m * m + (L + 1) * L * m) := by rw [← pow_add]
                _ ≤ 2 ^ (3 * (L + 1) ^ 3) := Nat.pow_le_pow_right (by omega) hpow_exp
            exact ⟨Aint.det, D, hDpos, hAint_eq, hdet_le, hD_le⟩
          obtain ⟨nM, dM, hdM1, hMdet_eq, hnM, hdM⟩ :=
            hsub_det_bound le_rfl (fun i => i) (fun j => j)
          obtain ⟨nS, dS, hdS1, hSdet_eq, hnS, hdS⟩ :=
            hsub_det_bound (Nat.sub_le M.numRows r)
              (fun i => ⟨r + i.val, by omega⟩)
              (fun j => ⟨st.cols.getD j.val 0, by
                have hj : j.val < st.cols.length := by omega
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
                exact hlt _ (List.getElem_mem hj)⟩)
          have hS_ne : (Matrix.of fun (i j : Fin (M.numRows - r)) =>
              M.entry (r + i.val) (st.cols.getD j.val 0)).det ≠ 0 :=
            fun h0 => hdet_ne (by rw [hdet_eq, h0, mul_zero])
          have hMeq' : (M.toMatrix.reindex (Equiv.refl _) (finCongr hsq.symm)).det =
              (nM : ℚ) / (dM : ℚ) := by
            rw [← hMdet_eq]; congr 1
          have hSeq' : (Matrix.of fun (i j : Fin (M.numRows - r)) =>
              M.entry (r + i.val) (st.cols.getD j.val 0)).det = (nS : ℚ) / (dS : ℚ) := by
            rw [← hSdet_eq]; congr 1
          have hnS_ne : nS ≠ 0 := fun h0 => hS_ne (by rw [hSeq', h0, Int.cast_zero, zero_div])
          have hacc_eq : st.acc = ((nM * (dS : ℤ) : ℤ) : ℚ) / ((nS * (dM : ℤ) : ℤ) : ℚ) := by
            have h1 := hdet_eq
            dsimp only at h1
            rw [hMeq', hSeq'] at h1
            have hdM0 : (dM : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hdS0 : (dS : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hnS0 : (nS : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hnS_ne
            push_cast; field_simp [hdM0, hdS0, hnS0] at h1 ⊢; linarith
          have hnum_le : (nM * (dS : ℤ)).natAbs ≤ 2 ^ (6 * (L + 1) ^ 3) := by
            rw [Int.natAbs_mul, Int.natAbs_natCast]
            calc nM.natAbs * dS ≤ 2 ^ (3 * (L + 1) ^ 3) * 2 ^ (3 * (L + 1) ^ 3) :=
                Nat.mul_le_mul hnM hdS
              _ = 2 ^ (6 * (L + 1) ^ 3) := by rw [← pow_add]; ring_nf
          have hden_le : (nS * (dM : ℤ)).natAbs ≤ 2 ^ (6 * (L + 1) ^ 3) := by
            rw [Int.natAbs_mul, Int.natAbs_natCast]
            calc nS.natAbs * dM ≤ 2 ^ (3 * (L + 1) ^ 3) * 2 ^ (3 * (L + 1) ^ 3) :=
                Nat.mul_le_mul hnS hdM
              _ = 2 ^ (6 * (L + 1) ^ 3) := by rw [← pow_add]; ring_nf
          have hden_ne : nS * (dM : ℤ) ≠ 0 :=
            mul_ne_zero hnS_ne (Int.natCast_ne_zero.mpr (by omega))
          have hdiv_num : st.acc.num.natAbs ≤ 2 ^ (6 * (L + 1) ^ 3) := by
            rw [hacc_eq, ← Rat.divInt_eq_div]
            exact (Rat.natAbs_num_divInt_le _ _ hden_ne).trans hnum_le
          have hdiv_den : st.acc.den ≤ 2 ^ (6 * (L + 1) ^ 3) := by
            rw [hacc_eq, ← Rat.divInt_eq_div]
            exact (Rat.den_divInt_le _ _ hden_ne).trans hden_le
          have hlen_rat := length_encRat_le st.acc hdiv_num hdiv_den
          have hs : (2 ^ (6 * (L + 1) ^ 3)).size ≤ 6 * (L + 1) ^ 3 + 1 :=
            Nat.size_le.mpr (Nat.pow_lt_pow_right (by omega) (by omega))
          have hL3 := Nat.one_le_pow 3 (L + 1) (by omega)
          omega
        have hcols_enc : (encList encUnary st.cols).length ≤ (L + 1) * (2 * (L + 1) + 1) := by
          refine (length_encList_le encUnary st.cols (b := L + 1) fun c hc => ?_).trans
            (Nat.mul_le_mul_right _ (by omega))
          simp only [encUnary_apply, List.length_replicate]
          exact (hlt c hc).le.trans (by omega)
        have hrow_enc : (encUnary st.rowIdx).length ≤ L + 1 := by
          simp only [encUnary_apply, List.length_replicate]; omega
        dsimp only [Function.comp_apply]
        rw [encRatDetState_apply]
        dsimp only [encRatDetStateFields]
        rw [length_encPair, length_encPair]
        have hL3 := Nat.one_le_pow 3 (L + 1) (by omega)
        change 2 * (encUnary st.rowIdx).length + 1 +
            (2 * (encList encUnary st.cols).length + 1 + (encRat st.acc).length) ≤
          60 * (L + 1) ^ 3
        nlinarith
  have hres := hcond.ite (const (0 : ℚ)) (encRatDetState_acc_polyTime hiter)
  refine hres.of_enc_eq fun M => congrArg encRat ?_
  unfold ratDet
  dsimp only [Function.comp_apply]
  split_ifs with h
  · rfl
  · rfl

end Cslib.LinearAlgebra
