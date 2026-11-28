module

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.PolarDecomposition
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Matrix.Basic

import CslibFrontier.Foundations.Quantum.DensityMatrix.TraceDistanceDataProcessing
import Mathlib.Data.Fintype.BigOperators

/-!
# Weighted Trace-Norm Bound for Complex Matrices

Provides the weighted Hilbert–Schmidt upper bound on the matrix trace norm:
for any strictly positive probability vector `w : ι → ℝ` (`w > 0`, `∑ i, w i = 1`) and
any complex matrix `X : Matrix ι ι ℂ`,
`‖X‖_1^2 ≤ ∑ i, ∑ j, ‖X i j‖^2 / √(w i * w j)`.

## Main results

* `CslibFrontier.Quantum.weighted_trace_norm_le`: weighted trace-norm Cauchy–Schwarz inequality.
-/

public section

namespace CslibFrontier.Quantum

open scoped BigOperators
open Matrix

/-- For any strictly positive probability vector `w : ι → ℝ` (`∑ i, w i = 1`) and any matrix
`X : Matrix ι ι ℂ`, `‖X‖_1^2 ≤ ∑ i, ∑ j, ‖X i j‖^2 / √(w i * w j)`. -/
theorem weighted_trace_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw_pos : ∀ i, 0 < w i) (hw_sum : ∑ i, w i = 1) (X : Matrix ι ι ℂ) :
    X.traceNorm ^ 2 ≤ ∑ i : ι, ∑ j : ι, ‖X i j‖ ^ 2 / Real.sqrt (w i * w j) := by
  obtain ⟨U, hU, hmax, _⟩ := Matrix.traceNorm_eq_max_re_trace X
  have hU_rows : ∀ i : ι, ∑ j : ι, ‖U i j‖ ^ 2 = 1 := by
    intro i
    have h1 : (U * Uᴴ) i i = 1 := by
      have hUU : U * Uᴴ = 1 := by
        simpa only [star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
      rw [hUU, Matrix.one_apply_eq]
    have h2 : ((U * Uᴴ) i i).re = 1 := by rw [h1]; simp
    rw [Matrix.mul_apply, Complex.re_sum] at h2
    convert h2 using 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    have hmul : (U i j * starRingEnd ℂ (U i j)).re = ‖U i j‖ ^ 2 := by
      rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact hmul.symm
  have hU_cols : ∀ j : ι, ∑ i : ι, ‖U i j‖ ^ 2 = 1 := by
    intro j
    have h1 : (Uᴴ * U) j j = 1 := by
      have hUU : Uᴴ * U = 1 := by
        simpa only [star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
      rw [hUU, Matrix.one_apply_eq]
    have h2 : ((Uᴴ * U) j j).re = 1 := by rw [h1]; simp
    rw [Matrix.mul_apply, Complex.re_sum] at h2
    convert h2 using 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    have hmul : (starRingEnd ℂ (U i j) * U i j).re = ‖U i j‖ ^ 2 := by
      rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact hmul.symm
  have htr_le :
      X.traceNorm ≤
        ∑ i : ι, ∑ j : ι,
          (Real.sqrt (Real.sqrt (w i * w j)) * ‖U j i‖) *
            (‖X j i‖ / Real.sqrt (Real.sqrt (w i * w j))) := by
    rw [← hmax, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hsqrt_pos : 0 < Real.sqrt (Real.sqrt (w i * w j)) :=
      Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos (hw_pos i) (hw_pos j)))
    calc (star (U j i) * X j i).re
        ≤ ‖star (U j i) * X j i‖ := Complex.re_le_norm _
      _ = ‖U j i‖ * ‖X j i‖ := by rw [norm_mul, norm_star]
      _ = (Real.sqrt (Real.sqrt (w i * w j)) * ‖U j i‖) *
            (‖X j i‖ / Real.sqrt (Real.sqrt (w i * w j))) := by
          field_simp [hsqrt_pos.ne']
  have hcs1 :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
      (fun p => Real.sqrt (Real.sqrt (w p.1 * w p.2)) * ‖U p.2 p.1‖)
      (fun p => ‖X p.2 p.1‖ / Real.sqrt (Real.sqrt (w p.1 * w p.2)))
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hcs1
  have htr_sq :
      X.traceNorm ^ 2 ≤
        (∑ i : ι, ∑ j : ι, Real.sqrt (w i * w j) * ‖U j i‖ ^ 2) *
          (∑ i : ι, ∑ j : ι, ‖X j i‖ ^ 2 / Real.sqrt (w i * w j)) := by
    have hnn : 0 ≤ X.traceNorm := Matrix.traceNorm_nonneg X
    calc X.traceNorm ^ 2
        ≤ (∑ i : ι, ∑ j : ι,
            (Real.sqrt (Real.sqrt (w i * w j)) * ‖U j i‖) *
              (‖X j i‖ / Real.sqrt (Real.sqrt (w i * w j)))) ^ 2 :=
          pow_le_pow_left₀ hnn htr_le 2
      _ ≤ (∑ i : ι, ∑ j : ι, (Real.sqrt (Real.sqrt (w i * w j)) * ‖U j i‖) ^ 2) *
            (∑ i : ι, ∑ j : ι, (‖X j i‖ / Real.sqrt (Real.sqrt (w i * w j))) ^ 2) := hcs1
      _ = (∑ i : ι, ∑ j : ι, Real.sqrt (w i * w j) * ‖U j i‖ ^ 2) *
            (∑ i : ι, ∑ j : ι, ‖X j i‖ ^ 2 / Real.sqrt (w i * w j)) := by
          congr 1
          · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
          · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [div_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hfirst_le_one : ∑ i : ι, ∑ j : ι, Real.sqrt (w i * w j) * ‖U j i‖ ^ 2 ≤ 1 := by
    have hcs2 :=
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
        (fun p => Real.sqrt (w p.1) * ‖U p.2 p.1‖)
        (fun p => Real.sqrt (w p.2) * ‖U p.2 p.1‖)
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hcs2
    have hlhs :
        (∑ i : ι, ∑ j : ι, (Real.sqrt (w i) * ‖U j i‖) * (Real.sqrt (w j) * ‖U j i‖)) =
          ∑ i : ι, ∑ j : ι, Real.sqrt (w i * w j) * ‖U j i‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Real.sqrt_mul (hw_pos i).le]
      ring
    have hr1 : ∑ i : ι, ∑ j : ι, (Real.sqrt (w i) * ‖U j i‖) ^ 2 = 1 := by
      have h : ∀ i : ι, ∑ j : ι, (Real.sqrt (w i) * ‖U j i‖) ^ 2 = w i := by
        intro i
        simp_rw [mul_pow, Real.sq_sqrt (hw_pos i).le, ← Finset.mul_sum, hU_cols i, mul_one]
      simp_rw [h, hw_sum]
    have hr2 : ∑ i : ι, ∑ j : ι, (Real.sqrt (w j) * ‖U j i‖) ^ 2 = 1 := by
      rw [Finset.sum_comm]
      have h : ∀ j : ι, ∑ i : ι, (Real.sqrt (w j) * ‖U j i‖) ^ 2 = w j := by
        intro j
        simp_rw [mul_pow, Real.sq_sqrt (hw_pos j).le, ← Finset.mul_sum, hU_rows j, mul_one]
      simp_rw [h, hw_sum]
    rw [hlhs, hr1, hr2, mul_one] at hcs2
    have hnn : 0 ≤ ∑ i : ι, ∑ j : ι, Real.sqrt (w i * w j) * ‖U j i‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    nlinarith
  have hsecond_eq :
      (∑ i : ι, ∑ j : ι, ‖X j i‖ ^ 2 / Real.sqrt (w i * w j)) =
        ∑ i : ι, ∑ j : ι, ‖X i j‖ ^ 2 / Real.sqrt (w i * w j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (w j) (w i)]
  have hsecond_nn : 0 ≤ ∑ i : ι, ∑ j : ι, ‖X i j‖ ^ 2 / Real.sqrt (w i * w j) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  rw [hsecond_eq] at htr_sq
  calc X.traceNorm ^ 2
      ≤ (∑ i : ι, ∑ j : ι, Real.sqrt (w i * w j) * ‖U j i‖ ^ 2) *
          (∑ i : ι, ∑ j : ι, ‖X i j‖ ^ 2 / Real.sqrt (w i * w j)) := htr_sq
    _ ≤ 1 * (∑ i : ι, ∑ j : ι, ‖X i j‖ ^ 2 / Real.sqrt (w i * w j)) :=
        mul_le_mul_of_nonneg_right hfirst_le_one hsecond_nn
    _ = ∑ i : ι, ∑ j : ι, ‖X i j‖ ^ 2 / Real.sqrt (w i * w j) := one_mul _

end CslibFrontier.Quantum
