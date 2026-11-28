module

public import CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.ABP
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Deterministic Polynomial-Time Identity Testing for Noncommutative ABPs

This module implements deterministic polynomial-time polynomial identity testing for homogeneous
layered noncommutative algebraic branching programs (`Cslib.Circuits.Arithmetic.NoncommABP`) over
any field `F` with decidable equality via incremental row-echelon basis reduction (`RowBasis`,
`rowReduce`) and layer-by-layer coordinate extraction (`razShpilkaRun`, `razShpilkaABP`).

## Main definitions

* `CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.RowBasis`: incremental
  row-echelon basis reduction over a field.
* `CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.rowReduce`: computable matrix
  row reduction returning basis rows and coordinate matrix.
* `CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.razShpilkaABP`: deterministic
  polynomial identity test for homogeneous layered noncommutative ABPs.
* `CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.razShpilkaABPOps`: explicit
  field-operation count upper bound.

## Main results

* `CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.razShpilkaABP_eq_true_iff`:
  soundness and completeness of `razShpilkaABP` (`razShpilkaABP e A = true ↔ A.polynomial = 0`).
* `CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.razShpilkaABPOps_le`:
  polynomial arithmetic complexity bound `O(d * W^3 * (n + 1))`.
-/

public section

namespace CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative

open Cslib.Circuits.Arithmetic FreeAlgebra

/-! ### Computable incremental row-echelon reduction over a field -/

section RowReduce

variable {F : Type*} [Field F]

/-- An incremental echelon basis for a set of vectors in `Fin q → F`: a list of pivot rows
`(piv, vec)` where `vec piv = 1` and every later row vanishes at earlier pivot columns. -/
structure RowBasis (F : Type*) (q : ℕ) where
  /-- List of `(pivotColumn, basisRow)` pairs in order of insertion. -/
  rows : List (Fin q × (Fin q → F))

/-- Echelon invariant for `RowBasis`: each row has `1` at its pivot and `0` at earlier pivots. -/
def RowBasis.Valid {q : ℕ} (B : RowBasis F q) : Prop :=
  (∀ p ∈ B.rows, p.2 p.1 = 1) ∧
    ∀ i j : Fin B.rows.length, i.val < j.val →
      (B.rows.get j).2 (B.rows.get i).1 = 0

/-- Reduce a vector `v : Fin q → F` against a list of echelon rows, returning the reduced residual
and the list of coefficients on the basis rows. -/
def reduceVec {q : ℕ} :
    List (Fin q × (Fin q → F)) → (Fin q → F) → (Fin q → F) × List F
  | [], v => (v, [])
  | (p, u) :: rest, v =>
    let c := v p
    let v' := fun j => v j - c * u j
    let (res, cs) := reduceVec rest v'
    (res, c :: cs)

private theorem reduceVec_length {q : ℕ} (rs : List (Fin q × (Fin q → F))) (v : Fin q → F) :
    (reduceVec rs v).2.length = rs.length := by
  induction rs generalizing v with
  | nil => rfl
  | cons pu rest ih => simp [reduceVec, ih]

private theorem reduceVec_spec {q : ℕ} (rs : List (Fin q × (Fin q → F))) (v : Fin q → F) :
    ∀ j : Fin q,
      v j = (reduceVec rs v).1 j +
        ∑ i : Fin rs.length,
          ((reduceVec rs v).2.get (i.cast (reduceVec_length rs v).symm)) * (rs.get i).2 j := by
  induction rs generalizing v with
  | nil => intro j; simp [reduceVec]
  | cons pu rest ih =>
    intro j
    rcases pu with ⟨p, u⟩
    have h := ih (fun k => v k - v p * u k) j
    change v j = (reduceVec ((p, u) :: rest) v).1 j +
      ∑ i : Fin (rest.length + 1),
        ((reduceVec ((p, u) :: rest) v).2.get (i.cast (reduceVec_length ((p, u) :: rest) v).symm)) *
          (((p, u) :: rest).get i).2 j
    rw [Fin.sum_univ_succ]
    have hrhs :
        (reduceVec ((p, u) :: rest) v).1 j +
          ((reduceVec ((p, u) :: rest) v).2.get
            ((0 : Fin (rest.length + 1)).cast (reduceVec_length ((p, u) :: rest) v).symm) *
            (((p, u) :: rest).get 0).2 j +
          ∑ i : Fin rest.length,
            (reduceVec ((p, u) :: rest) v).2.get
              (i.succ.cast (reduceVec_length ((p, u) :: rest) v).symm) *
              (((p, u) :: rest).get i.succ).2 j) =
        (reduceVec rest (fun k => v k - v p * u k)).1 j +
          (v p * u j +
          ∑ i : Fin rest.length,
            (reduceVec rest (fun k => v k - v p * u k)).2.get
              (i.cast (reduceVec_length rest _).symm) * (rest.get i).2 j) := rfl
    rw [hrhs]
    linear_combination h

private theorem reduceVec_zero_of_zero {q : ℕ} (p : Fin q) (rs : List (Fin q × (Fin q → F)))
    (w : Fin q → F) (hw : w p = 0)
    (hrest : ∀ j : Fin rs.length, (rs.get j).2 p = 0) :
    (reduceVec rs w).1 p = 0 := by
  induction rs generalizing w with
  | nil => simpa [reduceVec] using hw
  | cons r rs' ih =>
    rcases r with ⟨p', u'⟩
    simp only [reduceVec]
    refine ih _ ?_ (fun j => hrest j.succ)
    have hr : u' p = 0 := hrest ⟨0, Nat.zero_lt_succ _⟩
    simp [hw, hr]

private theorem reduceVec_pivot_zero {q : ℕ} (rs : List (Fin q × (Fin q → F))) (v : Fin q → F)
    (h1 : ∀ p ∈ rs, p.2 p.1 = 1)
    (h2 : ∀ i j : Fin rs.length, i.val < j.val → (rs.get j).2 (rs.get i).1 = 0) :
    ∀ i : Fin rs.length, (reduceVec rs v).1 (rs.get i).1 = 0 := by
  induction rs generalizing v with
  | nil => intro i; exact Fin.elim0 i
  | cons pu rest ih =>
    rcases pu with ⟨p, u⟩
    have h1' : ∀ r ∈ rest, r.2 r.1 = 1 := fun r hr => h1 r (List.mem_cons_of_mem _ hr)
    have h2' : ∀ i j : Fin rest.length, i.val < j.val →
        (rest.get j).2 (rest.get i).1 = 0 := fun i j hij =>
      h2 i.succ j.succ (by simpa using hij)
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [reduceVec, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero]
      have hsub : (fun k => v k - v p * u k) p = 0 := by
        have hp : u p = 1 := h1 (p, u) List.mem_cons_self
        simp [hp]
      exact reduceVec_zero_of_zero p rest _ hsub fun j =>
        h2 ⟨0, Nat.zero_lt_succ _⟩ j.succ (Nat.zero_lt_succ _)
    · simp only [reduceVec, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ]
      exact ih _ h1' h2' i'

/-- Any valid `RowBasis` has linearly independent rows over `F`. -/
theorem RowBasis.linearIndependent {q : ℕ} {B : RowBasis F q} (hB : B.Valid) :
    LinearIndependent F fun α : Fin B.rows.length => (B.rows.get α).2 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hstrong : ∀ k : ℕ, (hk : k < B.rows.length) → g ⟨k, hk⟩ = 0 := by
    intro k
    refine Nat.strongRecOn k fun k ih hk => ?_
    have hpi := congrFun hg (B.rows.get ⟨k, hk⟩).1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hpi
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin B.rows.length)] at hpi
    · have h1 := hB.1 (B.rows.get ⟨k, hk⟩) (List.get_mem _ _)
      rwa [h1, mul_one] at hpi
    · intro j _ hji
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hji) with hlt | hgt
      · rw [ih j.val hlt j.isLt, zero_mul]
      · rw [hB.2 ⟨k, hk⟩ j hgt, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact hstrong i.val i.isLt

/-- Lift linear independence of basis vectors along linearly independent row combinations. -/
theorem linearIndependent_comb {M : Type*} [AddCommGroup M] [Module F M]
    {q r : ℕ} {b : Fin q → M} (hb : LinearIndependent F b)
    {B : Fin r → (Fin q → F)} (hB : LinearIndependent F B) :
    LinearIndependent F fun α : Fin r => ∑ j : Fin q, B α j • b j := by
  rw [Fintype.linearIndependent_iff] at hb hB ⊢
  intro g hg
  have hsum : ∑ j : Fin q, (∑ α : Fin r, g α * B α j) • b j = 0 := by
    calc ∑ j : Fin q, (∑ α : Fin r, g α * B α j) • b j
        = ∑ j : Fin q, ∑ α : Fin r, g α • (B α j • b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_smul]
          exact Finset.sum_congr rfl fun α _ => (smul_smul _ _ _).symm
      _ = ∑ α : Fin r, ∑ j : Fin q, g α • (B α j • b j) := Finset.sum_comm
      _ = ∑ α : Fin r, g α • ∑ j : Fin q, B α j • b j := by
          refine Finset.sum_congr rfl fun α _ => (Finset.smul_sum).symm
      _ = 0 := hg
  have hB0 : ∑ α : Fin r, g α • B α = 0 := by
    funext j
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hb _ hsum j
  exact hB g hB0

section Decidable

variable [DecidableEq F]

/-- Find the first nonzero coordinate of a vector `v : Fin q → F`. -/
def findPivot {q : ℕ} (v : Fin q → F) : Option (Fin q) :=
  (List.finRange q).find? fun j => decide (v j ≠ 0)

private theorem findPivot_some {q : ℕ} {v : Fin q → F} {p : Fin q}
    (h : findPivot v = some p) : v p ≠ 0 := by
  have := List.find?_some h
  simpa using this

private theorem findPivot_none {q : ℕ} {v : Fin q → F}
    (h : findPivot v = none) (j : Fin q) : v j = 0 := by
  have := List.find?_eq_none.1 h j (List.mem_finRange j)
  simpa using this

/-- Insert a vector into a `RowBasis`, returning the updated basis and the coordinate list of the
vector in the updated basis. -/
def RowBasis.insert {q : ℕ} (B : RowBasis F q) (v : Fin q → F) :
    RowBasis F q × List F :=
  let (res, cs) := reduceVec B.rows v
  match findPivot res with
  | none => (B, cs)
  | some p =>
    let u := fun j => (res p)⁻¹ * res j
    (⟨B.rows ++ [(p, u)]⟩, cs ++ [res p])

private theorem RowBasis.insert_valid {q : ℕ} {B : RowBasis F q} (hB : B.Valid) (v : Fin q → F) :
    (B.insert v).1.Valid := by
  simp only [RowBasis.insert]
  split
  · exact hB
  · rename_i p hp
    have hne : (reduceVec B.rows v).1 p ≠ 0 := findPivot_some hp
    constructor
    · intro r hr
      rcases List.mem_append.1 hr with h1 | h2
      · exact hB.1 r h1
      · simp only [List.mem_singleton] at h2
        subst h2
        exact inv_mul_cancel₀ hne
    · intro i j hij
      have hjlt : j.val < B.rows.length + 1 := by simpa using j.isLt
      by_cases hj : j.val < B.rows.length
      · have hi : i.val < B.rows.length := by omega
        have h := hB.2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
        simpa [List.get_eq_getElem, List.getElem_append_left hi,
          List.getElem_append_left hj] using h
      · have hj_eq : j.val = B.rows.length := by omega
        have hi : i.val < B.rows.length := by omega
        simp only [List.get_eq_getElem, List.getElem_append_left hi, hj_eq,
          List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
        have hz := reduceVec_pivot_zero B.rows v hB.1 hB.2 ⟨i.val, hi⟩
        rw [List.get_eq_getElem] at hz
        simp [hz]

private theorem RowBasis.insert_length_eq {q : ℕ} (B : RowBasis F q) (v : Fin q → F) :
    (B.insert v).2.length = (B.insert v).1.rows.length := by
  simp only [RowBasis.insert]
  split <;> simp [reduceVec_length]

private theorem RowBasis.insert_reconstruct {q : ℕ} (B : RowBasis F q) (v : Fin q → F) (j : Fin q) :
    v j =
      ∑ α : Fin (B.insert v).1.rows.length,
        (B.insert v).2.get (α.cast (B.insert_length_eq v).symm) *
          ((B.insert v).1.rows.get α).2 j := by
  have hr := reduceVec_spec B.rows v j
  cases hfp : findPivot (reduceVec B.rows v).1 with
  | none =>
    have hB' : B.insert v = (B, (reduceVec B.rows v).2) := by simp [RowBasis.insert, hfp]
    have hlen' : B.rows.length = (B.insert v).1.rows.length := by rw [hB']
    rw [findPivot_none hfp j, zero_add] at hr
    rw [hr, ← Equiv.sum_comp (finCongr hlen')]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [List.get_eq_getElem, hB']
  | some p =>
    have hne : (reduceVec B.rows v).1 p ≠ 0 := findPivot_some hfp
    let u : Fin q → F := fun k => ((reduceVec B.rows v).1 p)⁻¹ * (reduceVec B.rows v).1 k
    have hB' : B.insert v =
        (⟨B.rows ++ [(p, u)]⟩, (reduceVec B.rows v).2 ++ [(reduceVec B.rows v).1 p]) := by
      simp [RowBasis.insert, hfp, u]
    have hlen' : B.rows.length + 1 = (B.insert v).1.rows.length := by rw [hB']; simp
    rw [← Equiv.sum_comp (finCongr hlen'), Fin.sum_univ_castSucc, hr, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hi : i.val < B.rows.length := i.isLt
      have hi' : i.val < (reduceVec B.rows v).2.length := by rwa [reduceVec_length]
      simp [List.get_eq_getElem, hB', List.getElem_append_left hi, List.getElem_append_left hi']
    · have hclen := reduceVec_length B.rows v
      simp only [List.get_eq_getElem, finCongr_apply, Fin.val_cast, Fin.val_last, hB',
        List.getElem_append_right (le_refl B.rows.length), Nat.sub_self,
        List.getElem_cons_zero, u]
      have hget : ((reduceVec B.rows v).2 ++ [(reduceVec B.rows v).1 p])[B.rows.length]'(by
          rw [List.length_append, hclen]; simp) = (reduceVec B.rows v).1 p := by
        rw [List.getElem_append_right (le_of_eq hclen)]
        simp [hclen]
      rw [hget, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- Result of reducing all `m` rows of a matrix `N : Matrix (Fin m) (Fin q) F`:
a reduced rank `r ≤ m`, coordinate matrix `R : Matrix (Fin m) (Fin r) F`, and echelon basis rows
`basis : RowBasis F q` of length `r`. -/
structure RowReduction (F : Type*) (m q : ℕ) where
  /-- Number of linearly independent basis rows. -/
  rank : ℕ
  /-- Coordinate matrix expressing each input row in the basis. -/
  coords : Matrix (Fin m) (Fin rank) F
  /-- The echelon basis rows. -/
  basis : RowBasis F q
  /-- Length of the basis equals `rank`. -/
  length_eq : basis.rows.length = rank

/-- Auxiliary recursion inserting rows `0, ..., k - 1` of a list into an echelon basis. -/
private def rowReduceAux {q : ℕ} :
    List (Fin q → F) → RowBasis F q → RowBasis F q × List (List F)
  | [], B => (B, [])
  | v :: vs, B =>
    let (B', cs) := B.insert v
    let (B'', css) := rowReduceAux vs B'
    (B'', cs :: css)

private theorem rowReduceAux_prefix {q : ℕ} (vs : List (Fin q → F)) (B : RowBasis F q) :
    ∃ ext, (rowReduceAux vs B).1.rows = B.rows ++ ext := by
  induction vs generalizing B with
  | nil => exact ⟨[], by simp [rowReduceAux]⟩
  | cons v vs ih =>
    simp only [rowReduceAux]
    obtain ⟨ext₂, hext₂⟩ := ih (B.insert v).1
    simp only [RowBasis.insert] at hext₂ ⊢
    split at hext₂
    · exact ⟨ext₂, hext₂⟩
    · rename_i p hp
      refine ⟨[(p, fun j => ((reduceVec B.rows v).1 p)⁻¹ * (reduceVec B.rows v).1 j)] ++ ext₂, ?_⟩
      simpa [List.append_assoc] using hext₂

private theorem rowReduceAux_valid {q : ℕ} (vs : List (Fin q → F)) {B : RowBasis F q}
    (hB : B.Valid) : (rowReduceAux vs B).1.Valid := by
  induction vs generalizing B with
  | nil => exact hB
  | cons v vs ih => exact ih (B.insert_valid hB v)

private theorem rowReduceAux_length_coords {q : ℕ} (vs : List (Fin q → F)) (B : RowBasis F q) :
    (rowReduceAux vs B).2.length = vs.length := by
  induction vs generalizing B with
  | nil => rfl
  | cons v vs ih => simp [rowReduceAux, ih]

private theorem rowReduceAux_le_length {q : ℕ} (vs : List (Fin q → F)) (B : RowBasis F q) :
    (rowReduceAux vs B).1.rows.length ≤ B.rows.length + vs.length := by
  induction vs generalizing B with
  | nil => simp [rowReduceAux]
  | cons v vs ih =>
    simp only [rowReduceAux, List.length_cons]
    have h1 := ih (B.insert v).1
    have h2 : (B.insert v).1.rows.length ≤ B.rows.length + 1 := by
      simp only [RowBasis.insert]; split <;> simp
    omega

/-- Compute the row-echelon factorization `N = R * B` of `N : Matrix (Fin m) (Fin q) F`. -/
def rowReduce {m q : ℕ} (N : Matrix (Fin m) (Fin q) F) : RowReduction F m q :=
  let vs := List.ofFn fun i : Fin m => N i
  let res := rowReduceAux vs ⟨[]⟩
  let r := res.1.rows.length
  { rank := r
    coords := Matrix.of fun i α =>
      let cs := res.2.get (i.cast (by rw [rowReduceAux_length_coords, List.length_ofFn]))
      cs.getD α.val 0
    basis := res.1
    length_eq := rfl }

/-- The reduced rank is at most the number of rows `m`. -/
theorem rowReduce_rank_le {m q : ℕ} (N : Matrix (Fin m) (Fin q) F) :
    (rowReduce N).rank ≤ m := by
  simpa [rowReduce] using rowReduceAux_le_length (List.ofFn fun i : Fin m => N i) ⟨[]⟩

/-- The basis rows returned by `rowReduce` satisfy the echelon invariant. -/
theorem rowReduce_valid {m q : ℕ} (N : Matrix (Fin m) (Fin q) F) :
    (rowReduce N).basis.Valid :=
  rowReduceAux_valid _ ⟨by simp, fun i => Fin.elim0 i⟩

private theorem rowReduceAux_reconstruct {q : ℕ} (vs : List (Fin q → F)) (B : RowBasis F q) :
    ∀ idx : Fin vs.length, ∀ j : Fin q,
      vs.get idx j =
        ∑ α : Fin (rowReduceAux vs B).1.rows.length,
          ((rowReduceAux vs B).2.get (idx.cast (rowReduceAux_length_coords vs B).symm)).getD
            α.val 0 *
            ((rowReduceAux vs B).1.rows.get α).2 j := by
  induction vs generalizing B with
  | nil => intro idx; exact Fin.elim0 idx
  | cons v vs ih =>
    intro idx j
    match idx with
    | ⟨0, _⟩ =>
      obtain ⟨ext, hext⟩ := rowReduceAux_prefix vs (B.insert v).1
      set B' := (B.insert v).1
      set cs := (B.insert v).2
      have hcs_len : cs.length = B'.rows.length := B.insert_length_eq v
      have hspec : v j =
          ∑ α : Fin B'.rows.length,
            cs.get (α.cast hcs_len.symm) * (B'.rows.get α).2 j :=
        B.insert_reconstruct v j
      change v j =
        ∑ α : Fin (rowReduceAux vs B').1.rows.length,
          cs.getD α.val 0 * ((rowReduceAux vs B').1.rows.get α).2 j
      rw [hspec]
      have hlen_full : (rowReduceAux vs B').1.rows.length = B'.rows.length + ext.length := by
        rw [hext, List.length_append]
      let e : Fin (B'.rows.length + ext.length) ≃ Fin (rowReduceAux vs B').1.rows.length :=
        finCongr hlen_full.symm
      rw [← Equiv.sum_comp e, Fin.sum_univ_add]
      have htail : ∑ β : Fin ext.length,
          cs.getD (e (Fin.natAdd B'.rows.length β)).val 0 *
            ((rowReduceAux vs B').1.rows.get (e (Fin.natAdd B'.rows.length β))).2 j = 0 :=
        Finset.sum_eq_zero fun β _ => by
          have hge : cs.length ≤ (e (Fin.natAdd B'.rows.length β)).val := by
            simp [e, hcs_len]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
      rw [htail, add_zero]
      refine Finset.sum_congr rfl fun α _ => ?_
      have hlt : α.val < cs.length := by rw [hcs_len]; exact α.isLt
      have hval : (e (Fin.castAdd ext.length α)).val = α.val := by simp [e]
      rw [hval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      congr 1
      simp only [List.get_eq_getElem, hval]
      have hget : ((rowReduceAux vs B').1.rows)[α.val]'(by omega) = (B'.rows)[α.val]'α.isLt := by
        simp [hext, List.getElem_append_left α.isLt]
      rw [hget]
    | ⟨k + 1, hk⟩ =>
      exact ih (B.insert v).1 ⟨k, Nat.lt_of_succ_lt_succ hk⟩ j

/-- The factorization `N = R * B`: every entry `N i j` equals the dot product of row `i` of
`(rowReduce N).coords` with column `j` of the echelon basis rows. -/
theorem rowReduce_eq_mul {m q : ℕ} (N : Matrix (Fin m) (Fin q) F) (i : Fin m) (j : Fin q) :
    N i j =
      ∑ α : Fin (rowReduce N).rank,
        (rowReduce N).coords i α *
          ((rowReduce N).basis.rows.get (α.cast (rowReduce N).length_eq.symm)).2 j := by
  have h := rowReduceAux_reconstruct (List.ofFn fun i : Fin m => N i) ⟨[]⟩
    ⟨i.val, by simp⟩ j
  simp only [List.get_eq_getElem, List.getElem_ofFn, Fin.eta] at h
  exact h

end Decidable

end RowReduce

/-! ### Raz–Shpilka PIT for homogeneous layered ABPs and noncommutative formulas -/

section RazShpilka

variable {F V : Type*} [Field F]

/-- Shifting a linearly independent family in `FreeAlgebra F V` on the right by all variables
`x : V` produces a linearly independent family indexed by `Fin r × V`. -/
theorem linearIndependent_mul_ι [Finite V] {r : ℕ} {b : Fin r → FreeAlgebra F V}
    (hb : LinearIndependent F b) :
    LinearIndependent F fun p : Fin r × V => b p.1 * FreeAlgebra.ι F p.2 := by
  classical
  have : Fintype V := Fintype.ofFinite V
  rw [Fintype.linearIndependent_iff] at hb ⊢
  intro g hg ⟨α₀, x₀⟩
  have hcoeff : ∀ (a : FreeAlgebra F V) (u : FreeMonoid V) (x : V),
      FreeAlgebra.coeff (u * FreeMonoid.of x₀) (a * FreeAlgebra.ι F x) =
        if x = x₀ then FreeAlgebra.coeff u a else 0 := by
    intro a u x
    rw [FreeAlgebra.coeff_mul]
    have hlen : (u * FreeMonoid.of x₀).toList.length = u.toList.length + 1 := by simp
    rw [hlen, Finset.sum_eq_single u.toList.length]
    · have htake : FreeMonoid.ofList ((u * FreeMonoid.of x₀).toList.take u.toList.length) = u := by
        simp [FreeMonoid.toList_mul]
      have hdrop : FreeMonoid.ofList ((u * FreeMonoid.of x₀).toList.drop u.toList.length) =
          FreeMonoid.of x₀ := by
        simp [FreeMonoid.toList_mul]
      rw [htake, hdrop, FreeAlgebra.coeff_ι, Finsupp.single_apply]
      by_cases hx : x = x₀
      · subst hx; simp
      · have hne : FreeMonoid.of x ≠ FreeMonoid.of x₀ := fun h => hx (FreeMonoid.of_injective h)
        simp [hx, hne]
    · intro i hi hiu
      rw [FreeAlgebra.coeff_ι]
      have hne : FreeMonoid.of x ≠
          FreeMonoid.ofList ((u * FreeMonoid.of x₀).toList.drop i) := by
        intro h
        have hlen' := congrArg (fun w : FreeMonoid V => w.toList.length) h
        simp only [FreeMonoid.toList_of, List.length_singleton,
          List.length_drop, FreeMonoid.toList_mul, List.length_append] at hlen'
        have hi' := Finset.mem_range.mp hi
        omega
      rw [Finsupp.single_eq_of_ne' hne, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hslice : ∑ α : Fin r, g (α, x₀) • b α = 0 := by
    apply FreeAlgebra.ext_coeff
    intro u
    have h0 := congrArg (FreeAlgebra.coeff (u * FreeMonoid.of x₀)) hg
    rw [map_sum, map_zero, Fintype.sum_prod_type] at h0
    simp only [map_smul, smul_eq_mul, hcoeff, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at h0
    simpa [map_sum, map_smul] using h0
  exact hb (fun α => g (α, x₀)) hslice α₀

variable [DecidableEq F]

/-- Layer state of the Raz–Shpilka algorithm on a `NoncommABP`: reduced dimension `r` and
coordinate matrix `M : Matrix (Fin w) (Fin r) F`. -/
structure RazShpilkaState (F : Type*) (w : ℕ) where
  /-- Current basis dimension. -/
  dim : ℕ
  /-- Coordinate matrix of the `w` layer polynomials in the basis. -/
  coords : Matrix (Fin w) (Fin dim) F

/-- Advance the Raz–Shpilka state by one ABP layer using an enumeration `e : Fin n ≃ V`. -/
def razShpilkaStep {n : ℕ} (e : Fin n ≃ V) {w₁ w₂ : ℕ}
    (W : V → Matrix (Fin w₁) (Fin w₂) F) (st : RazShpilkaState F w₁) :
    RazShpilkaState F w₂ :=
  let N : Matrix (Fin w₂) (Fin (st.dim * n)) F := Matrix.of fun j idx =>
    let p := finProdFinEquiv.symm idx
    ∑ i : Fin w₁, st.coords i p.1 * W (e p.2) i j
  let red := rowReduce N
  ⟨red.rank, red.coords⟩

/-- Run the Raz–Shpilka algorithm through layers `0, ..., k` of an ABP. -/
def razShpilkaRun {n d : ℕ} (e : Fin n ≃ V) (A : NoncommABP F V d) :
    (k : ℕ) → RazShpilkaState F (A.width k)
  | 0 => ⟨1, Matrix.of fun _ _ => 1⟩
  | k + 1 => razShpilkaStep e (A.weight k) (razShpilkaRun e A k)

/-- The Raz–Shpilka basis dimension at every layer `k ≥ 1` is at most `A.width k`. -/
theorem razShpilkaRun_dim_le {n d : ℕ} (e : Fin n ≃ V) (A : NoncommABP F V d) (k : ℕ) :
    (razShpilkaRun e A k).dim ≤ max 1 (A.width k) := by
  cases k with
  | zero => simp [razShpilkaRun]
  | succ k =>
    exact (rowReduce_rank_le _).trans (le_max_right _ _)

/-- Invariant of `razShpilkaRun`: there exists a linearly independent basis `b` in `FreeAlgebra F V`
representing every `A.pre k j` via the coordinates `(razShpilkaRun e A k).coords`. -/
theorem razShpilkaRun_spec [Fintype V] {n d : ℕ} (e : Fin n ≃ V) (A : NoncommABP F V d) (k : ℕ) :
    ∃ b : Fin (razShpilkaRun e A k).dim → FreeAlgebra F V,
      LinearIndependent F b ∧
      ∀ j : Fin (A.width k),
        A.pre k j =
          ∑ α : Fin (razShpilkaRun e A k).dim, (razShpilkaRun e A k).coords j α • b α := by
  induction k with
  | zero =>
    simp only [razShpilkaRun]
    refine ⟨fun _ => (1 : FreeAlgebra F V), ?_, fun j => ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      have h0 : g 0 • (1 : FreeAlgebra F V) = 0 := by simpa using hg
      have hc := congrArg (FreeAlgebra.coeff 1) h0
      simpa [FreeAlgebra.coeff_one] using hc
    · rw [NoncommABP.pre_zero]
      change (1 : FreeAlgebra F V) = ∑ α : Fin 1, (1 : F) • (1 : FreeAlgebra F V)
      rw [Fin.sum_univ_one, one_smul]
  | succ k ih =>
    let st := razShpilkaRun e A k
    change ∃ b : Fin st.dim → FreeAlgebra F V,
      LinearIndependent F b ∧
      ∀ j : Fin (A.width k), A.pre k j = ∑ α : Fin st.dim, st.coords j α • b α at ih
    obtain ⟨b, hb, hpre⟩ := ih
    set N : Matrix (Fin (A.width (k + 1))) (Fin (st.dim * n)) F := Matrix.of fun j idx =>
      let p := finProdFinEquiv.symm idx
      ∑ i : Fin (A.width k), st.coords i p.1 * A.weight k (e p.2) i j
    set red := rowReduce N
    let bShift : Fin (st.dim * n) → FreeAlgebra F V := fun idx =>
      let p := finProdFinEquiv.symm idx
      b p.1 * FreeAlgebra.ι F (e p.2)
    have hbShift : LinearIndependent F bShift := by
      have h1 : LinearIndependent F fun p : Fin st.dim × V => b p.1 * FreeAlgebra.ι F p.2 :=
        linearIndependent_mul_ι hb
      let hequiv : Fin (st.dim * n) ≃ Fin st.dim × V :=
        finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) e)
      have hcomp : bShift = (fun p : Fin st.dim × V => b p.1 * FreeAlgebra.ι F p.2) ∘ hequiv := by
        funext idx; simp [bShift, hequiv]
      rw [hcomp]
      exact h1.comp hequiv hequiv.injective
    let bNext : Fin red.rank → FreeAlgebra F V := fun α =>
      ∑ idx : Fin (st.dim * n),
        (red.basis.rows.get (α.cast red.length_eq.symm)).2 idx • bShift idx
    have hB_li : LinearIndependent F fun α : Fin red.rank =>
        (red.basis.rows.get (α.cast red.length_eq.symm)).2 := by
      have hli := RowBasis.linearIndependent (rowReduce_valid N)
      exact hli.comp (finCongr red.length_eq.symm) (finCongr red.length_eq.symm).injective
    refine ⟨bNext, linearIndependent_comb hbShift hB_li, fun j => ?_⟩
    have hexpand : A.pre (k + 1) j = ∑ idx : Fin (st.dim * n), N j idx • bShift idx := by
      rw [NoncommABP.pre_succ]
      have h1 : ∑ i : Fin (A.width k), A.pre k i * A.edge k i j =
          ∑ p : Fin st.dim × V,
            (∑ i : Fin (A.width k), st.coords i p.1 * A.weight k p.2 i j) •
              (b p.1 * FreeAlgebra.ι F p.2) := by
        calc ∑ i : Fin (A.width k), A.pre k i * A.edge k i j
            = ∑ i : Fin (A.width k),
                (∑ α : Fin st.dim, st.coords i α • b α) *
                  (∑ x : V, A.weight k x i j • FreeAlgebra.ι F x) := by
              refine Finset.sum_congr rfl fun i _ => by rw [hpre i, NoncommABP.edge]
          _ = ∑ i : Fin (A.width k), ∑ α : Fin st.dim, ∑ x : V,
                (st.coords i α * A.weight k x i j) • (b α * FreeAlgebra.ι F x) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun α _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
          _ = ∑ α : Fin st.dim, ∑ x : V,
                (∑ i : Fin (A.width k), st.coords i α * A.weight k x i j) •
                  (b α * FreeAlgebra.ι F x) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun α _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun x _ => (Finset.sum_smul).symm
          _ = _ := (Fintype.sum_prod_type fun p : Fin st.dim × V =>
                (∑ i : Fin (A.width k), st.coords i p.1 * A.weight k p.2 i j) •
                  (b p.1 * FreeAlgebra.ι F p.2)).symm
      rw [h1]
      let hequiv : Fin (st.dim * n) ≃ Fin st.dim × V :=
        finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) e)
      rw [← Equiv.sum_comp hequiv]
      refine Finset.sum_congr rfl fun idx _ => rfl
    rw [hexpand]
    calc ∑ idx : Fin (st.dim * n), N j idx • bShift idx
        = ∑ idx : Fin (st.dim * n),
            (∑ α : Fin red.rank,
              red.coords j α * (red.basis.rows.get (α.cast red.length_eq.symm)).2 idx) •
              bShift idx := by
          refine Finset.sum_congr rfl fun idx _ => by rw [rowReduce_eq_mul N j idx]
      _ = ∑ idx : Fin (st.dim * n), ∑ α : Fin red.rank,
            red.coords j α •
              ((red.basis.rows.get (α.cast red.length_eq.symm)).2 idx • bShift idx) := by
          refine Finset.sum_congr rfl fun idx _ => ?_
          rw [Finset.sum_smul]
          exact Finset.sum_congr rfl fun α _ => (smul_smul _ _ _).symm
      _ = ∑ α : Fin red.rank, red.coords j α • bNext α := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun α _ => (Finset.smul_sum).symm

/-- Deterministic PIT decision procedure for a homogeneous layered `NoncommABP`. -/
def razShpilkaABP {n d : ℕ} (e : Fin n ≃ V) (A : NoncommABP F V d) : Bool :=
  let st := razShpilkaRun e A d
  (List.finRange st.dim).all fun α => decide (∑ j : Fin (A.width d), st.coords j α = 0)

/-- **Soundness and completeness of Raz–Shpilka PIT on `NoncommABP`**. -/
theorem razShpilkaABP_eq_true_iff [Fintype V] {n d : ℕ} (e : Fin n ≃ V) (A : NoncommABP F V d) :
    razShpilkaABP e A = true ↔ A.polynomial = 0 := by
  obtain ⟨b, hb, hpre⟩ := razShpilkaRun_spec e A d
  have hpoly : A.polynomial =
      ∑ α : Fin (razShpilkaRun e A d).dim,
        (∑ j : Fin (A.width d), (razShpilkaRun e A d).coords j α) • b α := by
    rw [NoncommABP.polynomial]
    calc ∑ j : Fin (A.width d), A.pre d j
        = ∑ j : Fin (A.width d), ∑ α : Fin (razShpilkaRun e A d).dim,
            (razShpilkaRun e A d).coords j α • b α :=
          Finset.sum_congr rfl fun j _ => hpre j
      _ = ∑ α : Fin (razShpilkaRun e A d).dim, ∑ j : Fin (A.width d),
            (razShpilkaRun e A d).coords j α • b α := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun α _ => (Finset.sum_smul).symm
  rw [hpoly]
  simp only [razShpilkaABP, List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies]
  refine ⟨fun h => Finset.sum_eq_zero fun α _ => by rw [h α, zero_smul],
    fun h => (Fintype.linearIndependent_iff.1 hb) _ h⟩


/-! ### Arithmetic operation count for deterministic ABP identity testing -/

omit [Field F] [DecidableEq F] in
/-- Upper bound on field operations performed by `rowReduce` on an `m × q` matrix. -/
@[expose] def rowReduceOps (m q : ℕ) : ℕ :=
  m * (2 * m * q + q)

omit [Field F] [DecidableEq F] in
/-- Upper bound on field operations performed by `razShpilkaABP` on a degree-`d` layered
noncommutative ABP over `n` variables with layer widths `w`. -/
@[expose] def razShpilkaABPOps (n d : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ k ∈ Finset.range d,
    let r := max 1 (w k)
    let wNext := w (k + 1)
    2 * wNext * r * n * w k + rowReduceOps wNext (r * n)

omit [Field F] [DecidableEq F] in
/-- Polynomial arithmetic complexity bound for `razShpilkaABP` when every layer width is at most
`W ≥ 1`. -/
theorem razShpilkaABPOps_le {n d W : ℕ} (hW : 1 ≤ W) {w : ℕ → ℕ}
    (hw : ∀ k ≤ d, w k ≤ W) :
    razShpilkaABPOps n d w ≤ 6 * d * W ^ 3 * (n + 1) := by
  have hrow : ∀ m q : ℕ, rowReduceOps m q ≤ 3 * m ^ 2 * q + m * q := by
    intro m q
    simp only [rowReduceOps, Nat.mul_add]
    have h1 : m * (2 * m * q) = 2 * m ^ 2 * q := by ring
    have h2 : 2 * m ^ 2 * q ≤ 3 * m ^ 2 * q :=
      Nat.mul_le_mul_right q (Nat.mul_le_mul_right (m ^ 2) (by omega))
    omega
  calc razShpilkaABPOps n d w
      ≤ ∑ _k ∈ Finset.range d, (2 * W * W * n * W + (3 * W ^ 2 * (W * n) + W * (W * n))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hklt : k < d := Finset.mem_range.1 hk
        have h1 : w k ≤ W := hw k (by omega)
        have h2 : w (k + 1) ≤ W := hw (k + 1) (by omega)
        have h3 : max 1 (w k) ≤ W := max_le hW h1
        have h4 := hrow (w (k + 1)) (max 1 (w k) * n)
        refine Nat.add_le_add ?_ (h4.trans ?_)
        · gcongr
        · gcongr
    _ = d * (2 * W * W * n * W + (3 * W ^ 2 * (W * n) + W * (W * n))) := by simp
    _ ≤ d * (6 * W ^ 3 * (n + 1)) := by
        refine Nat.mul_le_mul_left d ?_
        have hW2 : W ^ 2 ≤ W ^ 3 := Nat.pow_le_pow_right hW (by omega)
        have h3 : W ^ 2 * n ≤ W ^ 3 * n := Nat.mul_le_mul_right n hW2
        have h4 : 6 * (W ^ 3 * n) ≤ 6 * (W ^ 3 * (n + 1)) :=
          Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left (W ^ 3) (Nat.le_succ n))
        calc 2 * W * W * n * W + (3 * W ^ 2 * (W * n) + W * (W * n))
            = 5 * (W ^ 3 * n) + W ^ 2 * n := by ring
          _ ≤ 5 * (W ^ 3 * n) + W ^ 3 * n := Nat.add_le_add_left h3 _
          _ = 6 * (W ^ 3 * n) := by ring
          _ ≤ 6 * (W ^ 3 * (n + 1)) := h4
          _ = 6 * W ^ 3 * (n + 1) := by ring
    _ = 6 * d * W ^ 3 * (n + 1) := by ring

end RazShpilka

end CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative
