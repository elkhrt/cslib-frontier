module

public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Euclidean Ellipsoids, Loewner Monotonicity, and Khachiyan's Rank-One Update

This module develops the finite-dimensional matrix-analytic and geometric theory of Euclidean
ellipsoids underlying Khachiyan's ellipsoid algorithm for linear programming, proved strictly under
standard Lean axioms without measure theory.

Given a symmetric positive definite shape matrix `E : Matrix (Fin n) (Fin n) ℝ` and center
`c : Fin n → ℝ`, we define the closed ellipsoid
`ellipsoidSet c E = {x | (x - c) ⬝ᵥ (E⁻¹ *ᵥ (x - c)) ≤ 1}`, prove Loewner monotonicity of the
determinant and antitonicity of the inverse quadratic form via orthogonal spectral decomposition,
establish the spectral determinant lower bound `r ^ (2 * n) ≤ E.det` for any ellipsoid containing a
Euclidean ball of radius `r`, and analyze the exact Khachiyan half-ellipsoid center and matrix
update (two-sided spectral bounds, positive definiteness, half-ellipsoid containment, and
multiplicative determinant contraction `≤ exp (-1 / (2 * (n + 1) ^ 2))` for `n ≥ 2`), together with
symmetric perturbation and center-shift inequalities for fixed-precision rounding.

## Main definitions

* `CslibFrontier.Complexity.LinearProgramming.ellipsoidSet`: closed Euclidean ellipsoid `{x | (x -
  c)ᵀ E⁻¹ (x - c) ≤ 1}`.
* `CslibFrontier.Complexity.LinearProgramming.exactEllipsoidCenter`: Khachiyan half-ellipsoid center
  update.
* `CslibFrontier.Complexity.LinearProgramming.exactEllipsoidMatrix`: Khachiyan half-ellipsoid
  shape-matrix update.

## Main results

* `CslibFrontier.Complexity.LinearProgramming.posDef_det_le_det`,
  `CslibFrontier.Complexity.LinearProgramming.posDef_inv_quad_anti`:
  Loewner monotonicity of `Matrix.det` and antitonicity of `v ↦ v ⬝ᵥ (A⁻¹ *ᵥ v)` on real symmetric
  positive definite matrices.
* `CslibFrontier.Complexity.LinearProgramming.pow_le_det_of_ball_subset_ellipsoidSet`: if a
  Euclidean ball of radius
  `r > 0` lies in `ellipsoidSet c E`, then `r ^ (2 * n) ≤ E.det`.
* `CslibFrontier.Complexity.LinearProgramming.exactEllipsoidMatrix_quad_bounds`,
    `CslibFrontier.Complexity.LinearProgramming.exactEllipsoidMatrix_posDef`: two-sided
  quadratic-form bounds and positive
  definiteness of `exactEllipsoidMatrix E a`.
* `CslibFrontier.Complexity.LinearProgramming.mem_exactEllipsoidSet_of_halfspace`: half-ellipsoid
  containment
  `{x ∈ ellipsoidSet c E | a ⬝ᵥ x ≤ a ⬝ᵥ c} ⊆ ellipsoidSet c' F`.
* `CslibFrontier.Complexity.LinearProgramming.det_exactEllipsoidMatrix_le`,
    `CslibFrontier.Complexity.LinearProgramming.ellipsoid_shrink_factor_le`: exact and inflated
  multiplicative determinant
  contraction bounds for `n ≥ 2`.
* `CslibFrontier.Complexity.LinearProgramming.symm_quad_perturbation_le`,
  `CslibFrontier.Complexity.LinearProgramming.posDef_entry_abs_le`,
    `CslibFrontier.Complexity.LinearProgramming.posDef_center_shift_quad_le`: quadratic-form
  perturbation, entrywise
  magnitude, and center-shift bounds for rounded ellipsoid updates.

-/

public section

open Matrix
open scoped BigOperators

namespace CslibFrontier.Complexity.LinearProgramming

/-! ### Positive definite matrices, Loewner monotonicity, and ellipsoids -/

/-- The closed Euclidean ellipsoid `{x : Fin n → ℝ | (x - c) ⬝ᵥ (E⁻¹ *ᵥ (x - c)) ≤ 1}` centered at
`c` with shape matrix `E`. -/
def ellipsoidSet {n : ℕ} (c : Fin n → ℝ) (E : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | (x - c) ⬝ᵥ (E⁻¹ *ᵥ (x - c)) ≤ 1}

/-- Membership characterization for `ellipsoidSet`. -/
theorem mem_ellipsoidSet_iff {n : ℕ} {c x : Fin n → ℝ} {E : Matrix (Fin n) (Fin n) ℝ} :
    x ∈ ellipsoidSet c E ↔ (x - c) ⬝ᵥ (E⁻¹ *ᵥ (x - c)) ≤ 1 :=
  Iff.rfl

/-- The center `c` always belongs to `ellipsoidSet c E`. -/
@[simp] theorem center_mem_ellipsoidSet {n : ℕ} (c : Fin n → ℝ) (E : Matrix (Fin n) (Fin n) ℝ) :
    c ∈ ellipsoidSet c E := by
  simp [ellipsoidSet]

private theorem quad_comm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (u v : Fin n → ℝ) : (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (A *ᵥ v) := by
  have hT : Aᵀ = A := by simpa [Matrix.IsHermitian] using hA
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]

private theorem posDef_quad_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (show 0 < v ⬝ᵥ (A *ᵥ v) from hA.dotProduct_mulVec_pos hv).le

private theorem posDef_isUnit_det {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    IsUnit A.det :=
  isUnit_iff_ne_zero.mpr hA.det_pos.ne'

private theorem eigenvector_dot_self {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (i : Fin n) :
    (⇑(hA.eigenvectorBasis i) : Fin n → ℝ) ⬝ᵥ (⇑(hA.eigenvectorBasis i) : Fin n → ℝ) = 1 := by
  have h1 : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have h2 : inner ℝ (hA.eigenvectorBasis i) (hA.eigenvectorBasis i) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, h1, one_pow]
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h2
  exact h2

private theorem isHermitian_eigenvalue_ge {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {m : ℝ} (hlow : ∀ v, m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) (i : Fin n) :
    m ≤ hA.eigenvalues i := by
  let e : Fin n → ℝ := ⇑(hA.eigenvectorBasis i)
  have heig : hA.eigenvalues i = e ⬝ᵥ (A *ᵥ e) := by simpa [e] using hA.eigenvalues_eq i
  have h := hlow e
  rwa [eigenvector_dot_self hA i, mul_one, ← heig] at h

/-- A real symmetric matrix with uniform positive quadratic lower bound
`m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)` (`m > 0`) is positive definite. -/
theorem posDef_of_quad_lower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {m : ℝ} (hm : 0 < m)
    (hlow : ∀ v : Fin n → ℝ, m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) :
    A.PosDef :=
  hA.posDef_iff_eigenvalues_pos.mpr fun i => hm.trans_le (isHermitian_eigenvalue_ge hA hlow i)

private theorem unitary_spectral_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    let U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    A = U * Matrix.diagonal hA.eigenvalues * Uᵀ := by
  intro U
  have h := hA.spectral_theorem
  simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using h

private theorem unitary_mul_transpose {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    let U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    U * Uᵀ = 1 ∧ Uᵀ * U = 1 := by
  intro U
  have h1 : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have h2 : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  simpa [U, Matrix.star_eq_conjTranspose] using And.intro h1 h2

private theorem posDef_inv_spectral {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    let U : Matrix (Fin n) (Fin n) ℝ :=
      (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    A⁻¹ = U * Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹) * Uᵀ := by
  intro U
  obtain ⟨hUUt, hUtU⟩ := unitary_mul_transpose hA.isHermitian
  have hAspec : A = U * Matrix.diagonal hA.isHermitian.eigenvalues * Uᵀ :=
    unitary_spectral_eq hA.isHermitian
  refine Matrix.inv_eq_right_inv ?_
  have hdiag : Matrix.diagonal hA.isHermitian.eigenvalues *
      Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have hfn : (fun i => hA.isHermitian.eigenvalues i * (hA.isHermitian.eigenvalues i)⁻¹) =
        fun _ => (1 : ℝ) :=
      funext fun i => mul_inv_cancel₀ (hA.eigenvalues_pos i).ne'
    rw [hfn, Matrix.diagonal_one]
  set D := Matrix.diagonal hA.isHermitian.eigenvalues
  set Dinv := Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹)
  have h1 : (U * D * Uᵀ) * (U * Dinv * Uᵀ) = U * (D * ((Uᵀ * U) * (Dinv * Uᵀ))) := by
    simp only [Matrix.mul_assoc]
  rw [hAspec, h1, hUtU, Matrix.one_mul, ← Matrix.mul_assoc D Dinv Uᵀ, hdiag, Matrix.one_mul, hUUt]

private theorem posDef_exists_inv_sqrt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ Sinv : Matrix (Fin n) (Fin n) ℝ,
      Sinvᵀ = Sinv ∧ IsUnit Sinv.det ∧ Sinv * A * Sinv = 1 ∧ Sinv * Sinv = A⁻¹ := by
  let U : Matrix (Fin n) (Fin n) ℝ :=
    (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  obtain ⟨hUUt, hUtU⟩ := unitary_mul_transpose hA.isHermitian
  let d : Fin n → ℝ := fun i => (Real.sqrt (hA.isHermitian.eigenvalues i))⁻¹
  let Sinv : Matrix (Fin n) (Fin n) ℝ := U * Matrix.diagonal d * Uᵀ
  have hsymm : Sinvᵀ = Sinv := by simp [Sinv, Matrix.transpose_mul, Matrix.mul_assoc]
  have hsq : Sinv * Sinv = A⁻¹ := by
    have hd2 : (fun i => d i * d i) = fun i => (hA.isHermitian.eigenvalues i)⁻¹ := by
      funext i
      dsimp [d]
      rw [← mul_inv, Real.mul_self_sqrt (hA.eigenvalues_pos i).le]
    have h1 : Sinv * Sinv =
        U * (Matrix.diagonal d * ((Uᵀ * U) * (Matrix.diagonal d * Uᵀ))) := by
      simp only [Sinv, Matrix.mul_assoc]
    rw [h1, hUtU, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal d),
      Matrix.diagonal_mul_diagonal, hd2, ← Matrix.mul_assoc, ← posDef_inv_spectral hA]
  have hconj : Sinv * A * Sinv = 1 := by
    have hAspec : A = U * Matrix.diagonal hA.isHermitian.eigenvalues * Uᵀ :=
      unitary_spectral_eq hA.isHermitian
    have hmid : (fun i => d i * hA.isHermitian.eigenvalues i * d i) = fun _ => (1 : ℝ) := by
      funext i
      have hpos := hA.eigenvalues_pos i
      have hsq' := Real.mul_self_sqrt hpos.le
      dsimp [d]
      have hs0 : Real.sqrt (hA.isHermitian.eigenvalues i) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      field_simp
      linarith
    set D := Matrix.diagonal hA.isHermitian.eigenvalues
    set Dd := Matrix.diagonal d
    have hDmid : Dd * (D * Dd) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      have hmid' : (fun i => d i * (hA.isHermitian.eigenvalues i * d i)) = fun _ => (1 : ℝ) := by
        funext i; rw [← mul_assoc]; exact congrFun hmid i
      rw [hmid', Matrix.diagonal_one]
    have h1 : (U * Dd * Uᵀ) * (U * D * Uᵀ) * (U * Dd * Uᵀ) =
        U * (Dd * ((Uᵀ * U) * (D * ((Uᵀ * U) * (Dd * Uᵀ))))) := by
      simp only [Matrix.mul_assoc]
    change (U * Dd * Uᵀ) * A * (U * Dd * Uᵀ) = 1
    rw [hAspec, h1, hUtU, Matrix.one_mul, Matrix.one_mul, ← Matrix.mul_assoc D Dd Uᵀ,
      ← Matrix.mul_assoc Dd (D * Dd) Uᵀ, hDmid, Matrix.one_mul, hUUt]
  have hunit : IsUnit Sinv.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h := congrArg Matrix.det hconj
    simp [Matrix.det_mul, h0] at h
  exact ⟨Sinv, hsymm, hunit, hconj, hsq⟩

/-- If `A` is symmetric positive definite with `m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)` (`m > 0`), then
`v ⬝ᵥ (A⁻¹ *ᵥ v) ≤ m⁻¹ * (v ⬝ᵥ v)` for all `v`. -/
theorem posDef_inv_quad_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {m : ℝ} (hm : 0 < m) (hlow : ∀ v : Fin n → ℝ, m * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (v : Fin n → ℝ) :
    v ⬝ᵥ (A⁻¹ *ᵥ v) ≤ m⁻¹ * (v ⬝ᵥ v) := by
  let U : Matrix (Fin n) (Fin n) ℝ :=
    (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  obtain ⟨hUUt, _⟩ := unitary_mul_transpose hA.isHermitian
  let w : Fin n → ℝ := Uᵀ *ᵥ v
  have hnorm : w ⬝ᵥ w = v ⬝ᵥ v := by
    dsimp [w]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
      dotProduct_comm, Matrix.mulVec_mulVec, hUUt, Matrix.one_mulVec]
  have hquad : v ⬝ᵥ (A⁻¹ *ᵥ v) =
      ∑ i : Fin n, (hA.isHermitian.eigenvalues i)⁻¹ * (w i * w i) := by
    rw [posDef_inv_spectral hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    change w ⬝ᵥ (Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹) *ᵥ w) = _
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hquad, ← hnorm]
  simp only [dotProduct, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (inv_anti₀ hm (isHermitian_eigenvalue_ge hA.isHermitian hlow i))
      (mul_self_nonneg (w i))

/-- **Loewner monotonicity of the determinant.** If `A` and `B` are real symmetric positive
definite matrices with `v ⬝ᵥ (A *ᵥ v) ≤ v ⬝ᵥ (B *ᵥ v)` for all `v`, then `A.det ≤ B.det`. -/
theorem posDef_det_le_det {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosDef)
    (hle : ∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ v ⬝ᵥ (B *ᵥ v)) :
    A.det ≤ B.det := by
  obtain ⟨Sinv, hsymm, _, hconj, hsq⟩ := posDef_exists_inv_sqrt hA
  let C : Matrix (Fin n) (Fin n) ℝ := Sinv * B * Sinv
  have hC_herm : C.IsHermitian := by
    have hBT : Bᵀ = B := by simpa [Matrix.IsHermitian] using hB.isHermitian
    change Cᵀ = C
    simp [C, Matrix.transpose_mul, hsymm, hBT, Matrix.mul_assoc]
  have hC_low : ∀ w : Fin n → ℝ, 1 * (w ⬝ᵥ w) ≤ w ⬝ᵥ (C *ᵥ w) := by
    intro w
    have h1 : w ⬝ᵥ (C *ᵥ w) = (Sinv *ᵥ w) ⬝ᵥ (B *ᵥ (Sinv *ᵥ w)) := by
      simp only [C, ← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
    have h2 : w ⬝ᵥ w = (Sinv *ᵥ w) ⬝ᵥ (A *ᵥ (Sinv *ᵥ w)) := by
      calc w ⬝ᵥ w = w ⬝ᵥ ((Sinv * A * Sinv) *ᵥ w) := by rw [hconj, Matrix.one_mulVec]
        _ = (Sinv *ᵥ w) ⬝ᵥ (A *ᵥ (Sinv *ᵥ w)) := by
            simp only [← Matrix.mulVec_mulVec]
            rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
    rw [one_mul, h1, h2]
    exact hle (Sinv *ᵥ w)
  have hdetC : (1 : ℝ) ≤ C.det := by
    rw [hC_herm.det_eq_prod_eigenvalues]
    have hle' : ∏ _i : Fin n, (1 : ℝ) ≤ ∏ i : Fin n, hC_herm.eigenvalues i := by
      gcongr with i
      exact isHermitian_eigenvalue_ge hC_herm hC_low i
    simpa using hle'
  have hdetEq : C.det = (A.det)⁻¹ * B.det := by
    calc (Sinv * B * Sinv).det = (Sinv.det * Sinv.det) * B.det := by
            simp only [Matrix.det_mul]; ring
      _ = A⁻¹.det * B.det := by rw [← Matrix.det_mul, hsq]
      _ = (A.det)⁻¹ * B.det := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hAdet : 0 < A.det := hA.det_pos
  rw [hdetEq] at hdetC
  have h := mul_le_mul_of_nonneg_left hdetC hAdet.le
  rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ hAdet.ne', one_mul] at h

/-- **Loewner antitonicity of the inverse quadratic form.** If `A` and `B` are real symmetric
positive definite matrices with `v ⬝ᵥ (A *ᵥ v) ≤ v ⬝ᵥ (B *ᵥ v)` for all `v`, then
`v ⬝ᵥ (B⁻¹ *ᵥ v) ≤ v ⬝ᵥ (A⁻¹ *ᵥ v)` for all `v`. -/
theorem posDef_inv_quad_anti {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosDef)
    (hle : ∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ v ⬝ᵥ (B *ᵥ v)) (v : Fin n → ℝ) :
    v ⬝ᵥ (B⁻¹ *ᵥ v) ≤ v ⬝ᵥ (A⁻¹ *ᵥ v) := by
  obtain ⟨Sinv, hsymm, hunit, hconj, hsq⟩ := posDef_exists_inv_sqrt hA
  let C : Matrix (Fin n) (Fin n) ℝ := Sinv * B * Sinv
  have hC_herm : C.IsHermitian := by
    have hBT : Bᵀ = B := by simpa [Matrix.IsHermitian] using hB.isHermitian
    change Cᵀ = C
    simp [C, Matrix.transpose_mul, hsymm, hBT, Matrix.mul_assoc]
  have hC_low : ∀ w : Fin n → ℝ, 1 * (w ⬝ᵥ w) ≤ w ⬝ᵥ (C *ᵥ w) := by
    intro w
    have h1 : w ⬝ᵥ (C *ᵥ w) = (Sinv *ᵥ w) ⬝ᵥ (B *ᵥ (Sinv *ᵥ w)) := by
      simp only [C, ← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
    have h2 : w ⬝ᵥ w = (Sinv *ᵥ w) ⬝ᵥ (A *ᵥ (Sinv *ᵥ w)) := by
      calc w ⬝ᵥ w = w ⬝ᵥ ((Sinv * A * Sinv) *ᵥ w) := by rw [hconj, Matrix.one_mulVec]
        _ = (Sinv *ᵥ w) ⬝ᵥ (A *ᵥ (Sinv *ᵥ w)) := by
            simp only [← Matrix.mulVec_mulVec]
            rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
    rw [one_mul, h1, h2]
    exact hle (Sinv *ᵥ w)
  have hC_pos : C.PosDef := posDef_of_quad_lower hC_herm zero_lt_one hC_low
  have hBinv : B⁻¹ = Sinv * C⁻¹ * Sinv := by
    refine Matrix.inv_eq_right_inv ?_
    have hCinv : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (posDef_isUnit_det hC_pos)
    have hSinvinv : Sinv⁻¹ * Sinv = 1 := Matrix.nonsing_inv_mul Sinv hunit
    have h1 : Sinv * (B * (Sinv * C⁻¹ * Sinv)) = Sinv := by
      have hassoc : Sinv * (B * (Sinv * C⁻¹ * Sinv)) = (C * C⁻¹) * Sinv := by
        simp only [C, Matrix.mul_assoc]
      rw [hassoc, hCinv, Matrix.one_mul]
    calc B * (Sinv * C⁻¹ * Sinv)
        = (Sinv⁻¹ * Sinv) * (B * (Sinv * C⁻¹ * Sinv)) := by rw [hSinvinv, Matrix.one_mul]
      _ = Sinv⁻¹ * Sinv := by rw [Matrix.mul_assoc, h1]
      _ = 1 := hSinvinv
  have hCinv_le := posDef_inv_quad_le hC_pos zero_lt_one hC_low (Sinv *ᵥ v)
  rw [inv_one, one_mul] at hCinv_le
  calc v ⬝ᵥ (B⁻¹ *ᵥ v) = (Sinv *ᵥ v) ⬝ᵥ (C⁻¹ *ᵥ (Sinv *ᵥ v)) := by
          rw [hBinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
            ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
    _ ≤ (Sinv *ᵥ v) ⬝ᵥ (Sinv *ᵥ v) := hCinv_le
    _ = v ⬝ᵥ (A⁻¹ *ᵥ v) := by
          rw [← hsq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
            hsymm, dotProduct_comm]

/-- **Spectral determinant lower bound for balls inside ellipsoids.** If a Euclidean ball of radius
`r > 0` around `u` lies in `ellipsoidSet c E` for a positive definite matrix `E`, then
`r ^ (2 * n) ≤ E.det`. -/
theorem pow_le_det_of_ball_subset_ellipsoidSet {n : ℕ} {c u : Fin n → ℝ}
    {E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) {r : ℝ} (hr : 0 < r)
    (hsub : ∀ x : Fin n → ℝ, (x - u) ⬝ᵥ (x - u) ≤ r ^ 2 → x ∈ ellipsoidSet c E) :
    r ^ (2 * n) ≤ E.det := by
  have hEinv : E⁻¹.PosDef := hE.inv
  have heig : ∀ i : Fin n, r ^ 2 ≤ hE.isHermitian.eigenvalues i := by
    intro i
    let e : Fin n → ℝ := ⇑(hE.isHermitian.eigenvectorBasis i)
    have hnorm : e ⬝ᵥ e = 1 := eigenvector_dot_self hE.isHermitian i
    have hplus : u + r • e ∈ ellipsoidSet c E :=
      hsub _ (by simp [add_sub_cancel_left, dotProduct_smul, smul_dotProduct, hnorm, sq])
    have hminus : u - r • e ∈ ellipsoidSet c E := by
      apply hsub
      have hdiff : u - r • e - u = -(r • e) := by abel
      rw [hdiff]
      simp [dotProduct_smul, smul_dotProduct, hnorm, sq]
    rw [mem_ellipsoidSet_iff] at hplus hminus
    set w : Fin n → ℝ := u - c
    have hp : u + r • e - c = w + r • e := by dsimp [w]; abel
    have hm : u - r • e - c = w - r • e := by dsimp [w]; abel
    rw [hp] at hplus
    rw [hm] at hminus
    have hcomm : w ⬝ᵥ (E⁻¹ *ᵥ e) = e ⬝ᵥ (E⁻¹ *ᵥ w) := by
      rw [← quad_comm hEinv.isHermitian w e, dotProduct_comm]
    have hpar : (w + r • e) ⬝ᵥ (E⁻¹ *ᵥ (w + r • e)) + (w - r • e) ⬝ᵥ (E⁻¹ *ᵥ (w - r • e)) =
        2 * (w ⬝ᵥ (E⁻¹ *ᵥ w)) + 2 * r ^ 2 * (e ⬝ᵥ (E⁻¹ *ᵥ e)) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, add_dotProduct,
        sub_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, hcomm]
      ring
    have hw0 : 0 ≤ w ⬝ᵥ (E⁻¹ *ᵥ w) := posDef_quad_nonneg hEinv w
    have hre : r ^ 2 * (e ⬝ᵥ (E⁻¹ *ᵥ e)) ≤ 1 := by linarith
    have hpos_lam : 0 < hE.isHermitian.eigenvalues i := hE.eigenvalues_pos i
    have hEinve : E⁻¹ *ᵥ e = (hE.isHermitian.eigenvalues i)⁻¹ • e := by
      have h1 : E⁻¹ *ᵥ (E *ᵥ e) = e := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul E (posDef_isUnit_det hE),
          Matrix.one_mulVec]
      rw [hE.isHermitian.mulVec_eigenvectorBasis i, Matrix.mulVec_smul] at h1
      have h2 := congrArg ((hE.isHermitian.eigenvalues i)⁻¹ • ·) h1
      simpa [smul_smul, inv_mul_cancel₀ hpos_lam.ne'] using h2
    rw [hEinve, dotProduct_smul, smul_eq_mul, hnorm, mul_one] at hre
    have h3 := mul_le_mul_of_nonneg_right hre hpos_lam.le
    rwa [mul_assoc, inv_mul_cancel₀ hpos_lam.ne', mul_one, one_mul] at h3
  rw [hE.isHermitian.det_eq_prod_eigenvalues]
  calc r ^ (2 * n) = (r ^ 2) ^ n := by rw [← pow_mul]
    _ = ∏ _i : Fin n, r ^ 2 := by simp
    _ ≤ ∏ i : Fin n, hE.isHermitian.eigenvalues i := by gcongr with i; exact heig i

/-! ### Exact Khachiyan half-ellipsoid update -/

/-- Exact Khachiyan half-ellipsoid center update
`c - (((n + 1) * √(a ⬝ᵥ (E *ᵥ a)))⁻¹) • (E *ᵥ a)`. -/
noncomputable def exactEllipsoidCenter {n : ℕ} (c : Fin n → ℝ) (E : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) : Fin n → ℝ :=
  c - (((n + 1 : ℝ) * Real.sqrt (a ⬝ᵥ (E *ᵥ a)))⁻¹) • (E *ᵥ a)

/-- Coordinate formula for `exactEllipsoidCenter`. -/
theorem exactEllipsoidCenter_apply {n : ℕ} (c : Fin n → ℝ) (E : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) (i : Fin n) :
    exactEllipsoidCenter c E a i =
      c i - (((n + 1 : ℝ) * Real.sqrt (a ⬝ᵥ (E *ᵥ a)))⁻¹) * (E *ᵥ a) i := by
  rfl

/-- Exact Khachiyan half-ellipsoid shape-matrix update
`(n ^ 2 / (n ^ 2 - 1)) • (E - (2 / ((n + 1) * (a ⬝ᵥ (E *ᵥ a)))) • vecMulVec (E *ᵥ a) (E *ᵥ a))`. -/
noncomputable def exactEllipsoidMatrix {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1))) •
    (E - (2 / ((n + 1 : ℝ) * (a ⬝ᵥ (E *ᵥ a)))) • Matrix.vecMulVec (E *ᵥ a) (E *ᵥ a))

/-- Entry formula for `exactEllipsoidMatrix`. -/
theorem exactEllipsoidMatrix_apply {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) (i j : Fin n) :
    exactEllipsoidMatrix E a i j =
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) *
        (E i j - (2 / ((n + 1 : ℝ) * (a ⬝ᵥ (E *ᵥ a)))) * ((E *ᵥ a) i * (E *ᵥ a) j)) := by
  rfl

private theorem vecMulVec_mulVec {n : ℕ} (u v y : Fin n → ℝ) :
    Matrix.vecMulVec u v *ᵥ y = (v ⬝ᵥ y) • u := by
  funext i
  simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

private theorem exactEllipsoidMatrix_inv {n : ℕ} (hn : 2 ≤ n) {E : Matrix (Fin n) (Fin n) ℝ}
    (hE : E.PosDef) {a : Fin n → ℝ} (ha : a ≠ 0) :
    (exactEllipsoidMatrix E a)⁻¹ =
      ((((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2)) •
        (E⁻¹ + (2 / ((n - 1 : ℝ) * (a ⬝ᵥ (E *ᵥ a)))) • Matrix.vecMulVec a a) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set σ := a ⬝ᵥ (E *ᵥ a)
  set b := E *ᵥ a
  have hσ : 0 < σ := hE.dotProduct_mulVec_pos ha
  set G := E - (2 / ((n + 1 : ℝ) * σ)) • Matrix.vecMulVec b b
  set H := E⁻¹ + (2 / ((n - 1 : ℝ) * σ)) • Matrix.vecMulVec a a
  have hGH : G * H = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    set x : Fin n → ℝ := Pi.single j 1
    simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    have hHx : H *ᵥ x = E⁻¹ *ᵥ x + ((2 / ((n - 1 : ℝ) * σ)) * (a ⬝ᵥ x)) • a := by
      simp [H, Matrix.add_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, smul_smul]
    have hEinvx : E *ᵥ (E⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv E (posDef_isUnit_det hE), Matrix.one_mulVec]
    have hEHx : E *ᵥ (H *ᵥ x) = x + ((2 / ((n - 1 : ℝ) * σ)) * (a ⬝ᵥ x)) • b := by
      rw [hHx, Matrix.mulVec_add, hEinvx, Matrix.mulVec_smul]
    have hbEinvx : b ⬝ᵥ (E⁻¹ *ᵥ x) = a ⬝ᵥ x := by
      rw [quad_comm hE.isHermitian a (E⁻¹ *ᵥ x), hEinvx]
    have hbHx : b ⬝ᵥ (H *ᵥ x) = (((n + 1 : ℝ) / (n - 1 : ℝ))) * (a ⬝ᵥ x) := by
      rw [hHx, dotProduct_add, hbEinvx, dotProduct_smul, smul_eq_mul, dotProduct_comm b a]
      have hσne : σ ≠ 0 := hσ.ne'
      have hnne : (n : ℝ) - 1 ≠ 0 := by linarith
      change a ⬝ᵥ x + 2 / ((n - 1 : ℝ) * σ) * (a ⬝ᵥ x) * σ = _
      field_simp
      ring
    simp only [G, Matrix.sub_mulVec, Matrix.smul_mulVec, hEHx, vecMulVec_mulVec, hbHx, smul_smul]
    have hcoeff : 2 / ((n + 1 : ℝ) * σ) * (((n + 1 : ℝ) / (n - 1 : ℝ)) * (a ⬝ᵥ x)) =
        2 / ((n - 1 : ℝ) * σ) * (a ⬝ᵥ x) := by
      have hσne : σ ≠ 0 := hσ.ne'
      have hnne : (n : ℝ) - 1 ≠ 0 := by linarith
      have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
      field_simp
    rw [hcoeff, add_sub_cancel_right]
  refine Matrix.inv_eq_right_inv ?_
  change (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) • G) * ((((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) • H) = 1
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hGH]
  have hprod : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) * (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) = 1 := by
    have h1 : (n : ℝ) ^ 2 ≠ 0 := by nlinarith
    have h2 : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
  rw [hprod, one_smul]

/-- **Two-sided quadratic-form bounds for the exact Khachiyan shape update.** -/
theorem exactEllipsoidMatrix_quad_bounds {n : ℕ} (hn : 2 ≤ n) {E : Matrix (Fin n) (Fin n) ℝ}
    (hE : E.PosDef) {a : Fin n → ℝ} (ha : a ≠ 0) (v : Fin n → ℝ) :
    ((n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2) * (v ⬝ᵥ (E *ᵥ v)) ≤
        v ⬝ᵥ (exactEllipsoidMatrix E a *ᵥ v) ∧
      v ⬝ᵥ (exactEllipsoidMatrix E a *ᵥ v) ≤
        ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) * (v ⬝ᵥ (E *ᵥ v)) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set σ := a ⬝ᵥ (E *ᵥ a)
  set b := E *ᵥ a
  have hσ : 0 < σ := hE.dotProduct_mulVec_pos ha
  have hquad : v ⬝ᵥ (exactEllipsoidMatrix E a *ᵥ v) =
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) *
        (v ⬝ᵥ (E *ᵥ v) - (2 / ((n + 1 : ℝ) * σ)) * (b ⬝ᵥ v) ^ 2) := by
    simp only [exactEllipsoidMatrix, Matrix.smul_mulVec, Matrix.sub_mulVec, vecMulVec_mulVec,
      dotProduct_smul, dotProduct_sub, smul_eq_mul]
    rw [dotProduct_comm v (E *ᵥ a)]
    dsimp [σ, b]; ring
  have hcs : (b ⬝ᵥ v) ^ 2 ≤ σ * (v ⬝ᵥ (E *ᵥ v)) := by
    set t : ℝ := (b ⬝ᵥ v) / σ
    have hw : 0 ≤ (v - t • a) ⬝ᵥ (E *ᵥ (v - t • a)) := posDef_quad_nonneg hE _
    have hsym1 : v ⬝ᵥ (E *ᵥ a) = b ⬝ᵥ v := dotProduct_comm v b
    have hsym2 : a ⬝ᵥ (E *ᵥ v) = b ⬝ᵥ v := (quad_comm hE.isHermitian a v).symm
    have hexp : (v - t • a) ⬝ᵥ (E *ᵥ (v - t • a)) = v ⬝ᵥ (E *ᵥ v) - (b ⬝ᵥ v) ^ 2 / σ := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hsym1, hsym2]
      have hσ0 : σ ≠ 0 := hσ.ne'
      have h1 : a ⬝ᵥ (E *ᵥ a) = σ := rfl
      rw [h1]; dsimp [t]
      field_simp; ring
    rw [hexp, sub_nonneg, div_le_iff₀ hσ] at hw
    linarith
  have hα : 0 < (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) := div_pos (by nlinarith) (by nlinarith)
  rw [hquad]
  constructor
  · have h1 : (2 / ((n + 1 : ℝ) * σ)) * (b ⬝ᵥ v) ^ 2 ≤ (2 / (n + 1 : ℝ)) * (v ⬝ᵥ (E *ᵥ v)) := by
      refine (mul_le_mul_of_nonneg_left hcs (by positivity)).trans_eq ?_
      have hσ0 : σ ≠ 0 := hσ.ne'
      have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
      field_simp
    have h2 : v ⬝ᵥ (E *ᵥ v) - (2 / (n + 1 : ℝ)) * (v ⬝ᵥ (E *ᵥ v)) =
        ((n - 1 : ℝ) / (n + 1 : ℝ)) * (v ⬝ᵥ (E *ᵥ v)) := by
      have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
      field_simp; ring
    have h3 : ((n - 1 : ℝ) / (n + 1 : ℝ)) * (v ⬝ᵥ (E *ᵥ v)) ≤
        v ⬝ᵥ (E *ᵥ v) - (2 / ((n + 1 : ℝ) * σ)) * (b ⬝ᵥ v) ^ 2 := by linarith
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h3 hα.le)
    have hn21 : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
    field_simp; ring
  · refine mul_le_mul_of_nonneg_left ?_ hα.le
    have hnonneg : 0 ≤ (2 / ((n + 1 : ℝ) * σ)) * (b ⬝ᵥ v) ^ 2 :=
      mul_nonneg (div_nonneg zero_le_two (mul_nonneg (by linarith) hσ.le)) (sq_nonneg _)
    linarith

/-- The exact Khachiyan shape-matrix update preserves positive definiteness for `n ≥ 2`. -/
theorem exactEllipsoidMatrix_posDef {n : ℕ} (hn : 2 ≤ n) {E : Matrix (Fin n) (Fin n) ℝ}
    (hE : E.PosDef) {a : Fin n → ℝ} (ha : a ≠ 0) :
    (exactEllipsoidMatrix E a).PosDef := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsym : (exactEllipsoidMatrix E a).IsHermitian := by
    have hET : Eᵀ = E := by simpa [Matrix.IsHermitian] using hE.isHermitian
    change (exactEllipsoidMatrix E a)ᵀ = exactEllipsoidMatrix E a
    ext i j
    have hEij : E j i = E i j := congrFun (congrFun hET i) j
    simp [exactEllipsoidMatrix, Matrix.vecMulVec, hEij, mul_comm]
  refine hsym.posDef_iff_eigenvalues_pos.mpr fun i => ?_
  let e : Fin n → ℝ := ⇑(hsym.eigenvectorBasis i)
  have he_ne : e ≠ 0 := by
    intro h0
    have h := eigenvector_dot_self hsym i
    simp [e, h0] at h
  have heig : hsym.eigenvalues i = e ⬝ᵥ (exactEllipsoidMatrix E a *ᵥ e) := by
    simpa [e] using hsym.eigenvalues_eq i
  rw [heig]
  have h1 := (exactEllipsoidMatrix_quad_bounds hn hE ha e).1
  have hpos : 0 < ((n : ℝ) ^ 2 / ((n : ℝ) + 1) ^ 2) * (e ⬝ᵥ (E *ᵥ e)) :=
    mul_pos (div_pos (by nlinarith) (by positivity)) (hE.dotProduct_mulVec_pos he_ne)
  exact hpos.trans_le h1

/-- **Half-ellipsoid containment.** For `n ≥ 2`, every `x ∈ ellipsoidSet c E` satisfying
`a ⬝ᵥ x ≤ a ⬝ᵥ c` belongs to `ellipsoidSet (exactEllipsoidCenter c E a)
  (exactEllipsoidMatrix E a)`. -/
theorem mem_exactEllipsoidSet_of_halfspace {n : ℕ} (hn : 2 ≤ n) {c x : Fin n → ℝ}
    {E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef) {a : Fin n → ℝ} (ha : a ≠ 0)
    (hx : x ∈ ellipsoidSet c E) (hcut : a ⬝ᵥ x ≤ a ⬝ᵥ c) :
    x ∈ ellipsoidSet (exactEllipsoidCenter c E a) (exactEllipsoidMatrix E a) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [mem_ellipsoidSet_iff] at hx ⊢
  rw [exactEllipsoidMatrix_inv hn hE ha]
  set σ := a ⬝ᵥ (E *ᵥ a)
  set s := Real.sqrt σ
  set b := E *ᵥ a
  have hσ : 0 < σ := hE.dotProduct_mulVec_pos ha
  have hs : 0 < s := Real.sqrt_pos.mpr hσ
  have hs2 : s * s = σ := Real.mul_self_sqrt hσ.le
  set z : Fin n → ℝ := x - c
  set t : ℝ := (a ⬝ᵥ z) / s
  have haz : a ⬝ᵥ z = s * t := by dsimp [t]; have := hs.ne'; field_simp
  have ht_nonpos : t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by simp only [z, dotProduct_sub]; linarith) hs.le
  have hEinvb : E⁻¹ *ᵥ b = a := by
    dsimp [b]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul E (posDef_isUnit_det hE), Matrix.one_mulVec]
  have hzEinvb : z ⬝ᵥ (E⁻¹ *ᵥ b) = s * t := by rw [hEinvb, dotProduct_comm, haz]
  have hbz : b ⬝ᵥ (E⁻¹ *ᵥ z) = s * t := by
    rw [← quad_comm hE.inv.isHermitian b z, hEinvb, haz]
  have hbEinvb : b ⬝ᵥ (E⁻¹ *ᵥ b) = s * s := by rw [hEinvb, dotProduct_comm, hs2]
  have ht_sq : t ^ 2 ≤ z ⬝ᵥ (E⁻¹ *ᵥ z) := by
    have hw : 0 ≤ (z - (t / s) • b) ⬝ᵥ (E⁻¹ *ᵥ (z - (t / s) • b)) :=
      posDef_quad_nonneg hE.inv _
    have hexp : (z - (t / s) • b) ⬝ᵥ (E⁻¹ *ᵥ (z - (t / s) • b)) = z ⬝ᵥ (E⁻¹ *ᵥ z) - t ^ 2 := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hzEinvb, hbz, hbEinvb]
      have hs0 : s ≠ 0 := hs.ne'
      field_simp; ring
    linarith
  have ht_ge : -1 ≤ t := by nlinarith [ht_sq.trans hx]
  set u : Fin n → ℝ := z + (((n + 1 : ℝ) * s)⁻¹) • b
  have hdiff : x - exactEllipsoidCenter c E a = u := by
    dsimp [u, z, exactEllipsoidCenter, b, s, σ]; abel
  rw [hdiff]
  have hau : a ⬝ᵥ u = s * (t + ((n + 1 : ℝ))⁻¹) := by
    simp only [u, dotProduct_add, dotProduct_smul, smul_eq_mul, haz]
    have hab : a ⬝ᵥ b = s * s := hs2.symm
    rw [hab]
    have hs0 : s ≠ 0 := hs.ne'
    have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
    field_simp
  have huEinvu : u ⬝ᵥ (E⁻¹ *ᵥ u) =
      z ⬝ᵥ (E⁻¹ *ᵥ z) + 2 * t / (n + 1 : ℝ) + 1 / ((n + 1 : ℝ)) ^ 2 := by
    simp only [u, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hzEinvb, hbz, hbEinvb]
    have hs0 : s ≠ 0 := hs.ne'
    have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
    field_simp; ring
  have hquad : u ⬝ᵥ (((((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) •
      (E⁻¹ + (2 / ((n - 1 : ℝ) * σ)) • Matrix.vecMulVec a a)) *ᵥ u) =
      (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) *
        (u ⬝ᵥ (E⁻¹ *ᵥ u) + (2 / (n - 1 : ℝ)) * (t + ((n + 1 : ℝ))⁻¹) ^ 2) := by
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, vecMulVec_mulVec, dotProduct_smul,
      dotProduct_add, smul_eq_mul, dotProduct_comm u a, hau]
    congr 1
    have hσeq : σ = s * s := hs2.symm
    rw [hσeq]
    have hs0 : s ≠ 0 := hs.ne'
    have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [hquad, huEinvu]
  have hid : 1 + 2 * t / (n + 1 : ℝ) + 1 / ((n + 1 : ℝ)) ^ 2 +
      (2 / (n - 1 : ℝ)) * (t + ((n + 1 : ℝ))⁻¹) ^ 2 =
      (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + (2 / (n - 1 : ℝ)) * (t * (t + 1)) := by
    have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
    have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
    have hn21 : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp; ring
  have hterm : (2 / (n - 1 : ℝ)) * (t * (t + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg zero_le_two (by linarith))
      (mul_nonpos_of_nonpos_of_nonneg ht_nonpos (by linarith))
  calc (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) *
        (z ⬝ᵥ (E⁻¹ *ᵥ z) + 2 * t / (n + 1 : ℝ) + 1 / ((n + 1 : ℝ)) ^ 2 +
          (2 / (n - 1 : ℝ)) * (t + ((n + 1 : ℝ))⁻¹) ^ 2)
      ≤ (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by nlinarith) (by nlinarith))
    _ = 1 := by
        have h1 : (n : ℝ) ^ 2 ≠ 0 := by nlinarith
        have h2 : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
        field_simp

/-- **Determinant contraction of the exact Khachiyan update.** For `n ≥ 2`,
`(exactEllipsoidMatrix E a).det ≤ exp (-1 / (2 * (n + 1) ^ 2)) * E.det`
(indeed `≤ exp (-1 / (n + 1)) * E.det`). -/
theorem det_exactEllipsoidMatrix_le {n : ℕ} (hn : 2 ≤ n) {E : Matrix (Fin n) (Fin n) ℝ}
    (hE : E.PosDef) {a : Fin n → ℝ} (ha : a ≠ 0) :
    (exactEllipsoidMatrix E a).det ≤ Real.exp (-1 / (2 * ((n : ℝ) + 1) ^ 2)) * E.det := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set σ := a ⬝ᵥ (E *ᵥ a)
  set b := E *ᵥ a
  have hσ : 0 < σ := hE.dotProduct_mulVec_pos ha
  set c : ℝ := -(2 / ((n + 1 : ℝ) * σ))
  have hfactor : E - (2 / ((n + 1 : ℝ) * σ)) • Matrix.vecMulVec b b =
      E * (1 + Matrix.replicateCol Unit (c • a) * Matrix.replicateRow Unit b) := by
    rw [Matrix.mul_add, Matrix.mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
      Pi.smul_apply, Fintype.univ_punit, Finset.sum_singleton, sub_eq_add_neg]
    congr 1
    simp only [c, b, Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdetG : (E - (2 / ((n + 1 : ℝ) * σ)) • Matrix.vecMulVec b b).det =
      (((n : ℝ) - 1) / ((n : ℝ) + 1)) * E.det := by
    rw [hfactor, Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow,
      dotProduct_smul, smul_eq_mul, dotProduct_comm b a]
    have hσ0 : σ ≠ 0 := hσ.ne'
    have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
    have haEa : a ⬝ᵥ b = σ := rfl
    rw [haEa]; dsimp [c]
    field_simp; ring
  have hdetF : (exactEllipsoidMatrix E a).det =
      (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ (n - 1) * ((n : ℝ) / ((n : ℝ) + 1)) ^ 2) * E.det := by
    have hGeq : exactEllipsoidMatrix E a =
        (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1))) •
          (E - (2 / ((n + 1 : ℝ) * σ)) • Matrix.vecMulVec b b) := rfl
    rw [hGeq, Matrix.det_smul, Fintype.card_fin, hdetG]
    set α : ℝ := (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)
    have hpow : α ^ n = α ^ (n - 1) * α := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    rw [hpow]; dsimp [α]
    have hn21 : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
    field_simp; ring
  rw [hdetF]
  refine mul_le_mul_of_nonneg_right ?_ hE.det_pos.le
  have h1 : ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ (n - 1) ≤ Real.exp (1 / ((n : ℝ) + 1)) := by
    have hbase : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) ≤ Real.exp (1 / ((n : ℝ) ^ 2 - 1)) := by
      have heq : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) = 1 / ((n : ℝ) ^ 2 - 1) + 1 := by
        have : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
        field_simp; ring
      rw [heq]; exact Real.add_one_le_exp _
    calc ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ (n - 1)
        ≤ (Real.exp (1 / ((n : ℝ) ^ 2 - 1))) ^ (n - 1) :=
          pow_le_pow_left₀ (div_nonneg (by nlinarith) (by nlinarith)) hbase _
      _ = Real.exp (1 / ((n : ℝ) + 1)) := by
          rw [← Real.exp_nat_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
          congr 1
          have hn21 : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
          have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
          field_simp; ring
  have h2 : ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 ≤ Real.exp (-2 / ((n : ℝ) + 1)) := by
    have hbase : (n : ℝ) / ((n : ℝ) + 1) ≤ Real.exp (-1 / ((n : ℝ) + 1)) := by
      have heq : (n : ℝ) / ((n : ℝ) + 1) = -1 / ((n : ℝ) + 1) + 1 := by
        have : (n : ℝ) + 1 ≠ 0 := by linarith
        field_simp; ring
      rw [heq]; exact Real.add_one_le_exp _
    calc ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 ≤ (Real.exp (-1 / ((n : ℝ) + 1))) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hbase 2
      _ = Real.exp (-2 / ((n : ℝ) + 1)) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ (n - 1) * ((n : ℝ) / ((n : ℝ) + 1)) ^ 2
      ≤ Real.exp (1 / ((n : ℝ) + 1)) * Real.exp (-2 / ((n : ℝ) + 1)) :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-1 / ((n : ℝ) + 1)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-1 / (2 * ((n : ℝ) + 1) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        simp only [neg_div, neg_le_neg_iff]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-- Net determinant contraction factor after inflating the exact Khachiyan shape matrix twice by
`1 + 1 / (16 * n ^ 3)` for `n ≥ 2`. -/
theorem ellipsoid_shrink_factor_le {n : ℕ} (hn : 2 ≤ n) :
    (1 + 1 / (16 * (n : ℝ) ^ 3)) ^ (2 * n) * Real.exp (-1 / (2 * ((n : ℝ) + 1) ^ 2)) ≤
      Real.exp (-1 / (12 * (n : ℝ) ^ 2)) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (1 + 1 / (16 * (n : ℝ) ^ 3)) ^ (2 * n) ≤ Real.exp (1 / (8 * (n : ℝ) ^ 2)) := by
    calc (1 + 1 / (16 * (n : ℝ) ^ 3)) ^ (2 * n)
        ≤ (Real.exp (1 / (16 * (n : ℝ) ^ 3))) ^ (2 * n) :=
          pow_le_pow_left₀ (by positivity) (by rw [add_comm]; exact Real.add_one_le_exp _) _
      _ = Real.exp (1 / (8 * (n : ℝ) ^ 2)) := by
          rw [← Real.exp_nat_mul]
          congr 1; push_cast
          have hne : (n : ℝ) ≠ 0 := by linarith
          field_simp; ring
  calc (1 + 1 / (16 * (n : ℝ) ^ 3)) ^ (2 * n) * Real.exp (-1 / (2 * ((n : ℝ) + 1) ^ 2))
      ≤ Real.exp (1 / (8 * (n : ℝ) ^ 2)) * Real.exp (-1 / (2 * ((n : ℝ) + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (1 / (8 * (n : ℝ) ^ 2) - 1 / (2 * ((n : ℝ) + 1) ^ 2)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-1 / (12 * (n : ℝ) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        have hstep : 2 * ((n : ℝ) + 1) ^ 2 ≤ (9 / 2 : ℝ) * (n : ℝ) ^ 2 := by nlinarith
        have hdiv : 1 / ((9 / 2 : ℝ) * (n : ℝ) ^ 2) ≤ 1 / (2 * ((n : ℝ) + 1) ^ 2) :=
          one_div_le_one_div_of_le (by positivity) hstep
        have heq : 1 / (8 * (n : ℝ) ^ 2) - 1 / ((9 / 2 : ℝ) * (n : ℝ) ^ 2) =
            -(7 / 72 : ℝ) / (n : ℝ) ^ 2 := by
          have hne : (n : ℝ) ≠ 0 := by linarith
          field_simp; ring
        have h72 : -(7 / 72 : ℝ) / (n : ℝ) ^ 2 ≤ -1 / (12 * (n : ℝ) ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith

/-! ### Perturbation, entrywise, and center-shift bounds for rounded updates -/

/-- Entrywise perturbation bound on quadratic forms: if `|Δ i j| ≤ δ` for all `i, j`, then
`|v ⬝ᵥ (Δ *ᵥ v)| ≤ n * δ * (v ⬝ᵥ v)`. -/
theorem symm_quad_perturbation_le {n : ℕ} (Δ : Matrix (Fin n) (Fin n) ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hΔ : ∀ i j, |Δ i j| ≤ δ) (v : Fin n → ℝ) :
    |v ⬝ᵥ (Δ *ᵥ v)| ≤ (n : ℝ) * δ * (v ⬝ᵥ v) := by
  have hexp : v ⬝ᵥ (Δ *ᵥ v) = ∑ i : Fin n, ∑ j : Fin n, v i * Δ i j * v j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hexp]
  have habs : |∑ i : Fin n, ∑ j : Fin n, v i * Δ i j * v j| ≤
      δ * (∑ i : Fin n, |v i|) ^ 2 := by
    calc |∑ i : Fin n, ∑ j : Fin n, v i * Δ i j * v j|
        ≤ ∑ i : Fin n, ∑ j : Fin n, |v i * Δ i j * v j| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, δ * (|v i| * |v j|) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_mul]
            have h := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hΔ i j) (abs_nonneg (v i))) (abs_nonneg (v j))
            linarith
      _ = δ * (∑ i : Fin n, |v i|) ^ 2 := by
          rw [sq, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by simp only [Finset.mul_sum]
  have hcs : (∑ i : Fin n, |v i|) ^ 2 ≤ (n : ℝ) * (v ⬝ᵥ v) := by
    have h0 : (0 : ℝ) ≤ ∑ i : Fin n, ∑ j : Fin n, (|v i| - |v j|) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hid : (∑ i : Fin n, ∑ j : Fin n, (|v i| - |v j|) ^ 2) =
        2 * ((n : ℝ) * (v ⬝ᵥ v) - (∑ i : Fin n, |v i|) ^ 2) := by
      have hsub : ∀ i j : Fin n,
          (|v i| - |v j|) ^ 2 = v i * v i + v j * v j - 2 * (|v i| * |v j|) := by
        intro i j
        have hi : |v i| ^ 2 = v i * v i := by rw [sq_abs, sq]
        have hj : |v j| ^ 2 = v j * v j := by rw [sq_abs, sq]
        linarith [show (|v i| - |v j|) ^ 2 = |v i| ^ 2 + |v j| ^ 2 - 2 * (|v i| * |v j|) by ring]
      simp_rw [hsub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have h1 : (∑ i : Fin n, ∑ _j : Fin n, v i * v i) = (n : ℝ) * (v ⬝ᵥ v) := by
        simp [dotProduct, Finset.mul_sum, mul_comm]
      have h2 : (∑ _i : Fin n, ∑ j : Fin n, v j * v j) = (n : ℝ) * (v ⬝ᵥ v) := by
        simp [dotProduct]
      have h3 : (∑ i : Fin n, ∑ j : Fin n, 2 * (|v i| * |v j|)) =
          2 * (∑ i : Fin n, |v i|) ^ 2 := by
        rw [sq, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp only [Finset.mul_sum]
      rw [h1, h2, h3]; ring
    linarith
  calc |∑ i : Fin n, ∑ j : Fin n, v i * Δ i j * v j|
      ≤ δ * ((n : ℝ) * (v ⬝ᵥ v)) := habs.trans (mul_le_mul_of_nonneg_left hcs hδ)
    _ = (n : ℝ) * δ * (v ⬝ᵥ v) := by ring

/-- Every entry of a symmetric positive definite matrix `E` with `v ⬝ᵥ (E *ᵥ v) ≤ M * (v ⬝ᵥ v)`
satisfies `|E i j| ≤ M`. -/
theorem posDef_entry_abs_le {n : ℕ} {E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    {M : ℝ} (hhi : ∀ v : Fin n → ℝ, v ⬝ᵥ (E *ᵥ v) ≤ M * (v ⬝ᵥ v)) (i j : Fin n) :
    |E i j| ≤ M := by
  have hET : Eᵀ = E := by simpa [Matrix.IsHermitian] using hE.isHermitian
  have hdiag : ∀ k : Fin n, 0 ≤ E k k ∧ E k k ≤ M := by
    intro k
    let ek : Fin n → ℝ := Pi.single k 1
    have hek : ek ⬝ᵥ (E *ᵥ ek) = E k k := by simp [ek]
    have hnk : ek ⬝ᵥ ek = 1 := by simp [ek]
    exact ⟨hek ▸ posDef_quad_nonneg hE ek, by have h := hhi ek; rwa [hek, hnk, mul_one] at h⟩
  by_cases hij : i = j
  · subst hij; rw [abs_of_nonneg (hdiag i).1]; exact (hdiag i).2
  · let vp : Fin n → ℝ := Pi.single i 1 + Pi.single j 1
    let vm : Fin n → ℝ := Pi.single i 1 - Pi.single j 1
    have hEji : E j i = E i j := congrFun (congrFun hET i) j
    have hqp : vp ⬝ᵥ (E *ᵥ vp) = E i i + E j j + 2 * E i j := by
      simp only [vp, Matrix.mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct,
        one_mul, Matrix.mulVec_single_one, Matrix.col_apply, hEji]
      ring
    have hqm : vm ⬝ᵥ (E *ᵥ vm) = E i i + E j j - 2 * E i j := by
      simp only [vm, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, single_dotProduct,
        one_mul, Matrix.mulVec_single_one, Matrix.col_apply, hEji]
      ring
    have hp0 : 0 ≤ E i i + E j j + 2 * E i j := hqp ▸ posDef_quad_nonneg hE vp
    have hm0 : 0 ≤ E i i + E j j - 2 * E i j := hqm ▸ posDef_quad_nonneg hE vm
    rw [abs_le]
    constructor <;> linarith [(hdiag i).2, (hdiag j).2]

/-- Cauchy–Schwarz coordinate bound `|(E *ᵥ a) i| ≤ √M * √(a ⬝ᵥ (E *ᵥ a))` for a positive definite
matrix `E` with `v ⬝ᵥ (E *ᵥ v) ≤ M * (v ⬝ᵥ v)`. -/
theorem posDef_mulVec_coord_abs_le {n : ℕ} {E : Matrix (Fin n) (Fin n) ℝ} (hE : E.PosDef)
    {M : ℝ} (hM : 0 ≤ M) (hhi : ∀ v : Fin n → ℝ, v ⬝ᵥ (E *ᵥ v) ≤ M * (v ⬝ᵥ v))
    (a : Fin n → ℝ) (i : Fin n) :
    |(E *ᵥ a) i| ≤ Real.sqrt M * Real.sqrt (a ⬝ᵥ (E *ᵥ a)) := by
  by_cases ha : a = 0
  · simp [ha]
  · set σ := a ⬝ᵥ (E *ᵥ a)
    have hσ : 0 < σ := hE.dotProduct_mulVec_pos ha
    let ei : Fin n → ℝ := Pi.single i 1
    set t := (E *ᵥ a) i / σ
    have hw : 0 ≤ (ei - t • a) ⬝ᵥ (E *ᵥ (ei - t • a)) := posDef_quad_nonneg hE _
    have heiEa : ei ⬝ᵥ (E *ᵥ a) = (E *ᵥ a) i := by simp [ei]
    have haEei : a ⬝ᵥ (E *ᵥ ei) = (E *ᵥ a) i := by
      rw [← quad_comm hE.isHermitian a ei, dotProduct_comm, heiEa]
    have heiEei : ei ⬝ᵥ (E *ᵥ ei) = E i i := by simp [ei]
    have hexp : (ei - t • a) ⬝ᵥ (E *ᵥ (ei - t • a)) = E i i - ((E *ᵥ a) i) ^ 2 / σ := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, heiEa, haEei, heiEei]
      have haEa : a ⬝ᵥ (E *ᵥ a) = σ := rfl
      rw [haEa]; dsimp [t]
      have hσ0 : σ ≠ 0 := hσ.ne'
      field_simp; ring
    rw [hexp, sub_nonneg, div_le_iff₀ hσ] at hw
    have hEii : E i i ≤ M := (le_abs_self _).trans (posDef_entry_abs_le hE hhi i i)
    have hsq : ((E *ᵥ a) i) ^ 2 ≤ (Real.sqrt M * Real.sqrt σ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hM, Real.sq_sqrt hσ.le]
      exact hw.trans (mul_le_mul_of_nonneg_right hEii hσ.le)
    exact abs_le_of_sq_le_sq hsq (by positivity)

/-- Young's inequality for center perturbations in the `F⁻¹`-quadratic form. -/
theorem posDef_center_shift_quad_le {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosDef)
    (u δ : Fin n → ℝ) {η : ℝ} (hη : 0 < η) :
    (u - δ) ⬝ᵥ (F⁻¹ *ᵥ (u - δ)) ≤
      (1 + η) * (u ⬝ᵥ (F⁻¹ *ᵥ u)) + (1 + η⁻¹) * (δ ⬝ᵥ (F⁻¹ *ᵥ δ)) := by
  have hFinv := hF.inv
  let s := Real.sqrt η
  have hs : 0 < s := Real.sqrt_pos.mpr hη
  have hs2 : s * s = η := Real.mul_self_sqrt hη.le
  have hw : 0 ≤ (s • u + s⁻¹ • δ) ⬝ᵥ (F⁻¹ *ᵥ (s • u + s⁻¹ • δ)) :=
    posDef_quad_nonneg hFinv _
  have hcomm : δ ⬝ᵥ (F⁻¹ *ᵥ u) = u ⬝ᵥ (F⁻¹ *ᵥ δ) := by
    rw [← quad_comm hFinv.isHermitian u δ, dotProduct_comm]
  have hdiff : (1 + η) * (u ⬝ᵥ (F⁻¹ *ᵥ u)) + (1 + η⁻¹) * (δ ⬝ᵥ (F⁻¹ *ᵥ δ)) -
      (u - δ) ⬝ᵥ (F⁻¹ *ᵥ (u - δ)) = (s • u + s⁻¹ • δ) ⬝ᵥ (F⁻¹ *ᵥ (s • u + s⁻¹ • δ)) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, add_dotProduct,
      sub_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hcomm]
    rw [← hs2]
    have hs0 : s ≠ 0 := hs.ne'
    field_simp; ring
  linarith

-- Non-vacuity check on the 2-dimensional unit ball and coordinate halfspace.
example : (fun _ : Fin 2 => (0 : ℝ)) ∈
    ellipsoidSet (exactEllipsoidCenter 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) (Pi.single 0 1))
      (exactEllipsoidMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) (Pi.single 0 1)) :=
  mem_exactEllipsoidSet_of_halfspace (by decide)
    (posDef_of_quad_lower (by change (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = 1; simp) zero_lt_one
      fun v => by simp)
    (fun h => by simpa using congrFun h 0) (center_mem_ellipsoidSet 0 1) le_rfl

end CslibFrontier.Complexity.LinearProgramming
