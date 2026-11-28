module

public import CslibFrontier.Foundations.Probability.Gaussian.Correlated
public import CslibFrontier.Foundations.Probability.Gaussian.Quadrant
import CslibFrontier.Foundations.MeasureTheory.Integral.CauchySchwarz
import CslibFrontier.Foundations.Probability.Gaussian.Moments
import CslibFrontier.Foundations.Probability.Gaussian.OrnsteinUhlenbeck
import CslibFrontier.Foundations.Probability.Gaussian.QuadrantDeriv
import CslibFrontier.Foundations.Probability.Gaussian.Quantile
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.Gaussian.Stein
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One-Dimensional Ornstein–Uhlenbeck Heat Kernel and Gaussian IBP

This module develops the one-dimensional Ornstein–Uhlenbeck transition density (`mehlerKernel`),
establishes the exact pointwise heat equation `r ∂_r u = x ∂_x u - ∂_{xx} u` and uniform
derivative bounds for `u(r, x) = (U_r f)(x)`, and proves the Gaussian integration-by-parts
identity (`heatflow_ibp_left`) along the first coordinate of a correlated Gaussian pair.

## Main definitions

* `CslibFrontier.Probability.Gaussian.ou1D`: 1D Ornstein–Uhlenbeck operator.
* `CslibFrontier.Probability.Gaussian.mehlerKernel`, `mehlerKernelDx`, `mehlerKernelDxx`,
  `mehlerKernelDr`: Mehler transition density and its partial derivatives.

## Main results

* `CslibFrontier.Probability.Gaussian.ou1D_derivs_and_pde`: differentiation under the integral
  sign, exact heat PDE, and uniform derivative bounds for `ou1D r f`.
* `CslibFrontier.Probability.Gaussian.heatflow_ibp_left`: 1D Gaussian integration by parts along
  the first coordinate of `correlatedGaussian ρ`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace CslibFrontier.Probability.Gaussian

local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

/-! ### 1D Ornstein–Uhlenbeck kernel and exact heat equation -/

/-- One-dimensional Ornstein–Uhlenbeck operator `(U_r f)(x) = 𝔼[f(r x + √(1 - r²) G)]`. -/
@[expose] noncomputable def ou1D (r : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f (r * x + √(1 - r ^ 2) * y) ∂gaussianReal 0 1

/-- Integral formula for the 1D Ornstein–Uhlenbeck operator. -/
theorem ou1D_eq_integral (r : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    ou1D r f x = ∫ y, f (r * x + √(1 - r ^ 2) * y) ∂gaussianReal 0 1 := rfl

/-- The Mehler transition density
`K(r, x, y) = (2π(1 - r²))^{-1/2} exp(-(y - rx)² / (2(1 - r²)))`. -/
noncomputable def mehlerKernel (r x y : ℝ) : ℝ :=
  (√(2 * π * (1 - r ^ 2)))⁻¹ * rexp (-(y - r * x) ^ 2 / (2 * (1 - r ^ 2)))

/-- `x`-partial derivative of `mehlerKernel`. -/
noncomputable def mehlerKernelDx (r x y : ℝ) : ℝ :=
  (r * (y - r * x) / (1 - r ^ 2)) * mehlerKernel r x y

/-- Second `x`-partial derivative of `mehlerKernel`. -/
noncomputable def mehlerKernelDxx (r x y : ℝ) : ℝ :=
  (r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2 - r ^ 2 / (1 - r ^ 2)) * mehlerKernel r x y

/-- `r`-partial derivative of `mehlerKernel`. -/
noncomputable def mehlerKernelDr (r x y : ℝ) : ℝ :=
  (r / (1 - r ^ 2) + x * (y - r * x) / (1 - r ^ 2) - r * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2) *
    mehlerKernel r x y

/-- Measurability of `y ↦ mehlerKernel r x y`. -/
theorem measurable_mehlerKernel (r x : ℝ) : Measurable (fun y => mehlerKernel r x y) := by
  unfold mehlerKernel; fun_prop

/-- Joint measurability of `(x, y) ↦ mehlerKernelDr r x y`. -/
theorem measurable_mehlerKernelDr_prod (r : ℝ) :
    Measurable (fun q : ℝ × ℝ => mehlerKernelDr r q.1 q.2) := by
  unfold mehlerKernelDr mehlerKernel; fun_prop

private theorem mehlerKernel_nonneg (r x y : ℝ) : 0 ≤ mehlerKernel r x y := by
  unfold mehlerKernel; positivity

/-- The Mehler kernel equals the Gaussian PDF with mean `r * x` and variance `1 - r²`. -/
theorem mehlerKernel_eq_gaussianPDFReal {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    mehlerKernel r x y = gaussianPDFReal (r * x) (1 - r ^ 2).toNNReal y := by
  have hv : 0 ≤ 1 - r ^ 2 := sub_nonneg.2 ((sq_le_one_iff_abs_le_one r).2 hr.le)
  simp [mehlerKernel, gaussianPDFReal_def, Real.coe_toNNReal _ hv]

private theorem mehlerKernel_pde {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    r * mehlerKernelDr r x y = x * mehlerKernelDx r x y - mehlerKernelDxx r x y := by
  have hv : 1 - r ^ 2 ≠ 0 := (sub_pos.2 ((sq_lt_one_iff_abs_lt_one r).2 hr)).ne'
  unfold mehlerKernelDr mehlerKernelDx mehlerKernelDxx
  field_simp [hv]
  ring

private theorem hasDerivAt_mehlerKernel_x {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    HasDerivAt (fun x' => mehlerKernel r x' y) (mehlerKernelDx r x y) x := by
  have hv : 0 < 1 - r ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one r).2 hr)
  unfold mehlerKernel mehlerKernelDx
  have h1 : HasDerivAt (fun x' => y - r * x') (-r) x := by
    simpa using ((hasDerivAt_id' x).const_mul r).const_sub y
  have h2 : HasDerivAt (fun x' => -(y - r * x') ^ 2 / (2 * (1 - r ^ 2)))
      (r * (y - r * x) / (1 - r ^ 2)) x := by
    refine (((h1.pow 2).neg).div_const (2 * (1 - r ^ 2))).congr_deriv ?_
    field_simp [hv.ne']; ring
  refine (h2.exp.const_mul (√(2 * π * (1 - r ^ 2)))⁻¹).congr_deriv ?_
  unfold mehlerKernel
  ring

private theorem hasDerivAt_mehlerKernelDx_x {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    HasDerivAt (fun x' => mehlerKernelDx r x' y) (mehlerKernelDxx r x y) x := by
  have hv : 0 < 1 - r ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one r).2 hr)
  have hcoeff : HasDerivAt (fun x' => r * (y - r * x') / (1 - r ^ 2))
      (-(r ^ 2 / (1 - r ^ 2))) x := by
    have h1 : HasDerivAt (fun x' => y - r * x') (-r) x := by
      simpa using ((hasDerivAt_id' x).const_mul r).const_sub y
    refine ((h1.const_mul r).div_const (1 - r ^ 2)).congr_deriv ?_
    field_simp [hv.ne']
  unfold mehlerKernelDx mehlerKernelDxx
  refine (hcoeff.mul (hasDerivAt_mehlerKernel_x hr x y)).congr_deriv ?_
  unfold mehlerKernelDx
  field_simp [hv.ne']; ring

/-- `r`-derivative of `r' ↦ mehlerKernel r' x y`. -/
theorem hasDerivAt_mehlerKernel_r {r : ℝ} (hr : |r| < 1) (x y : ℝ) :
    HasDerivAt (fun r' => mehlerKernel r' x y) (mehlerKernelDr r x y) r := by
  have hv : 0 < 1 - r ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one r).2 hr)
  have h2πv : 0 < 2 * π * (1 - r ^ 2) := by positivity
  have hv_d : HasDerivAt (fun r' => 1 - r' ^ 2) (-2 * r) r := by
    have := (hasDerivAt_pow 2 r).const_sub 1
    refine this.congr_deriv ?_; ring
  have hpref_d : HasDerivAt (fun r' => (√(2 * π * (1 - r' ^ 2)))⁻¹)
      ((r / (1 - r ^ 2)) * (√(2 * π * (1 - r ^ 2)))⁻¹) r := by
    have hsq := ((Real.hasDerivAt_sqrt h2πv.ne').comp r
      (hv_d.const_mul (2 * π))).inv (Real.sqrt_pos.2 h2πv).ne'
    refine hsq.congr_deriv ?_
    have hsq_eq : √(2 * π * (1 - r ^ 2)) ^ 2 = 2 * π * (1 - r ^ 2) := Real.sq_sqrt h2πv.le
    have hne : √(2 * π * (1 - r ^ 2)) ≠ 0 := (Real.sqrt_pos.2 h2πv).ne'
    simp only [Function.comp_apply]
    rw [hsq_eq]
    field_simp [hv.ne', h2πv.ne', hne]
  have hexp_arg_d : HasDerivAt (fun r' => -(y - r' * x) ^ 2 / (2 * (1 - r' ^ 2)))
      (x * (y - r * x) / (1 - r ^ 2) - r * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2) r := by
    have hnum_d : HasDerivAt (fun r' => -(y - r' * x) ^ 2) (2 * x * (y - r * x)) r := by
      have h1 : HasDerivAt (fun r' => y - r' * x) (-x) r := by
        simpa using ((hasDerivAt_id' r).mul_const x).const_sub y
      refine ((h1.pow 2).neg).congr_deriv ?_; ring
    have hden_d : HasDerivAt (fun r' => 2 * (1 - r' ^ 2)) (-4 * r) r := by
      refine (hv_d.const_mul 2).congr_deriv ?_; ring
    refine (hnum_d.fun_div hden_d (by positivity)).congr_deriv ?_
    field_simp [hv.ne']; ring
  unfold mehlerKernel mehlerKernelDr
  refine (hpref_d.fun_mul hexp_arg_d.exp).congr_deriv ?_
  unfold mehlerKernel
  ring

/-- Kernel representation `ou1D r f x = ∫ y, mehlerKernel r x y * f y`. -/
theorem ou1D_eq_integral_mehler {r : ℝ} (hr : |r| < 1) {f : ℝ → ℝ} (hf : Measurable f)
    (x : ℝ) :
    ou1D r f x = ∫ y, mehlerKernel r x y * f y := by
  have hv : 0 < 1 - r ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one r).2 hr)
  have hvn : (1 - r ^ 2).toNNReal ≠ 0 := by simpa [hv]
  have hmap : (gaussianReal 0 1).map (fun y => r * x + √(1 - r ^ 2) * y) =
      gaussianReal (r * x) (1 - r ^ 2).toNNReal := by
    rw [show (fun y => r * x + √(1 - r ^ 2) * y) = (fun s => r * x + s) ∘
          fun y => √(1 - r ^ 2) * y from rfl,
      ← Measure.map_map (measurable_const_add (r * x)) (measurable_const_mul _),
      gaussianReal_map_const_mul, gaussianReal_map_const_add]
    exact congrArg₂ _ (by ring)
      (Subtype.ext (by simp [Real.sq_sqrt hv.le, Real.coe_toNNReal _ hv.le]))
  rw [ou1D, ← integral_map (by fun_prop) hf.aestronglyMeasurable, hmap,
    integral_gaussianReal_eq_integral_smul hvn]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  rw [smul_eq_mul, mehlerKernel_eq_gaussianPDFReal hr]

/-- Gaussian domination: `(1 + |y| + y^2) exp(-c y^2)` is Lebesgue integrable for `c > 0`. -/
theorem integrable_poly_mul_exp_neg_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ => (1 + |y| + y ^ 2) * rexp (-(c * y ^ 2))) := by
  set v : ℝ≥0 := (1 / (2 * c)).toNNReal
  have hv_val : (v : ℝ) = 1 / (2 * c) := Real.coe_toNNReal _ (by positivity)
  have hv_pos : 0 < (v : ℝ) := by rw [hv_val]; positivity
  have hv_ne : v ≠ 0 := NNReal.coe_ne_zero.1 hv_pos.ne'
  have hpdf_eq : ∀ y : ℝ, rexp (-(c * y ^ 2)) = √(2 * π * v) * gaussianPDFReal 0 v y := fun y => by
    have h2v : 2 * (v : ℝ) = c⁻¹ := by rw [hv_val]; field_simp [hc.ne']
    rw [gaussianPDFReal_def]
    dsimp only
    rw [sub_zero, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, h2v]
    congr 1; field_simp [hc.ne']
  have hpoly : Integrable (fun y : ℝ => 1 + |y| + y ^ 2) (gaussianReal 0 v) :=
    ((integrable_const 1).add ((memLp_id_gaussianReal 1).integrable le_rfl).abs).add
      (memLp_id_gaussianReal 2).integrable_sq
  have h1 := (integrable_gaussianReal_iff_integrable_mul_gaussianPDFReal (μ := 0) hv_ne).1 hpoly
  exact (h1.const_mul √(2 * π * v)).congr (ae_of_all _ fun y => by
    dsimp only; rw [hpdf_eq y]; ring)

/-- Pointwise prefactor bound for the `r`-derivative of the Mehler kernel. -/
private theorem mehlerKernelDr_prefactor_le {r x y R vmin rmax : ℝ}
    (hR : 0 ≤ R) (hvmin_pos : 0 < vmin) (hvmin_def : vmin = 1 - rmax ^ 2)
    (hv : vmin ≤ 1 - r ^ 2) (hr1 : |r| ≤ 1) (hxR : |x| ≤ R)
    (hz_le : |y - r * x| ≤ |y| + R) (hz2_le : (y - r * x) ^ 2 ≤ 2 * (y ^ 2 + R ^ 2))
    (h1y : |y| + R ≤ (1 + R) * (1 + |y| + y ^ 2))
    (h2y : 2 * (y ^ 2 + R ^ 2) ≤ 2 * (1 + R) ^ 2 * (1 + |y| + y ^ 2)) :
    |r / (1 - r ^ 2) + x * (y - r * x) / (1 - r ^ 2) - r * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2| ≤
      4 * ((1 + R) ^ 2 / vmin ^ 2 + (1 + R) / vmin + 1 / vmin + 1) * (1 + |y| + y ^ 2) := by
  have hv_pos : 0 < 1 - r ^ 2 := lt_of_lt_of_le hvmin_pos hv
  have hinv_v : (1 - r ^ 2)⁻¹ ≤ vmin⁻¹ := inv_anti₀ hvmin_pos hv
  have hinv_v2 : ((1 - r ^ 2) ^ 2)⁻¹ ≤ (vmin ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hvmin_pos) (pow_le_pow_left₀ hvmin_pos.le hv 2)
  have h1 : |r / (1 - r ^ 2)| ≤ 1 / vmin * (1 + |y| + y ^ 2) := by
    rw [abs_div, abs_of_pos hv_pos]
    calc |r| / (1 - r ^ 2) ≤ 1 / vmin := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul hr1 hinv_v (by positivity) zero_le_one
      _ ≤ 1 / vmin * (1 + |y| + y ^ 2) :=
            le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg y, sq_nonneg y])
  have h2 : |x * (y - r * x) / (1 - r ^ 2)| ≤ (1 + R) ^ 2 / vmin * (1 + |y| + y ^ 2) := by
    rw [abs_div, abs_mul, abs_of_pos hv_pos]
    calc |x| * |y - r * x| / (1 - r ^ 2) ≤ (1 + R) * (|y| + R) / vmin := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul (mul_le_mul (by linarith) hz_le (abs_nonneg _) (by linarith)) hinv_v
            (by positivity) (by positivity)
      _ ≤ (1 + R) ^ 2 / vmin * (1 + |y| + y ^ 2) := by
          rw [div_mul_eq_mul_div, sq, mul_assoc]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1y (by linarith))
            hvmin_pos.le
  have h3 : |r * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2| ≤
      2 * (1 + R) ^ 2 / vmin ^ 2 * (1 + |y| + y ^ 2) := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y - r * x)),
      abs_of_pos (sq_pos_of_pos hv_pos)]
    calc |r| * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2 ≤ 1 * (2 * (y ^ 2 + R ^ 2)) / vmin ^ 2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul (mul_le_mul hr1 hz2_le (sq_nonneg _) zero_le_one) hinv_v2
            (by positivity) (by positivity)
      _ ≤ 2 * (1 + R) ^ 2 / vmin ^ 2 * (1 + |y| + y ^ 2) := by
          rw [one_mul, div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right h2y (sq_nonneg _)
  have hvmin_le1 : vmin ≤ 1 := by rw [hvmin_def]; exact sub_le_self 1 (sq_nonneg rmax)
  have h2' : (1 + R) ^ 2 / vmin ≤ (1 + R) ^ 2 / vmin ^ 2 := by
    rw [div_le_div_iff₀ hvmin_pos (sq_pos_of_pos hvmin_pos)]
    have hv_sq : vmin ^ 2 ≤ vmin := by
      rw [sq]; exact mul_le_of_le_one_right hvmin_pos.le hvmin_le1
    exact mul_le_mul_of_nonneg_left hv_sq (sq_nonneg (1 + R))
  have hcoeff : 1 / vmin + (1 + R) ^ 2 / vmin + 2 * (1 + R) ^ 2 / vmin ^ 2 ≤
      4 * ((1 + R) ^ 2 / vmin ^ 2 + (1 + R) / vmin + 1 / vmin + 1) := by
    have hdiv2 : 2 * (1 + R) ^ 2 / vmin ^ 2 = 2 * ((1 + R) ^ 2 / vmin ^ 2) :=
      mul_div_assoc 2 _ _
    have ha := div_nonneg (sq_nonneg (1 + R)) (sq_nonneg vmin)
    have hb := div_nonneg (show 0 ≤ 1 + R by linarith only [hR]) hvmin_pos.le
    have hc := div_nonneg zero_le_one hvmin_pos.le
    linarith only [hdiv2, h2', ha, hb, hc]
  calc
    |r / (1 - r ^ 2) + x * (y - r * x) / (1 - r ^ 2) - r * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2|
        ≤ |r / (1 - r ^ 2) + x * (y - r * x) / (1 - r ^ 2)| +
            |r * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2| := abs_sub _ _
    _ ≤ |r / (1 - r ^ 2)| + |x * (y - r * x) / (1 - r ^ 2)| +
          |r * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 1 / vmin * (1 + |y| + y ^ 2) + (1 + R) ^ 2 / vmin * (1 + |y| + y ^ 2) +
          2 * (1 + R) ^ 2 / vmin ^ 2 * (1 + |y| + y ^ 2) := add_le_add (add_le_add h1 h2) h3
    _ = (1 / vmin + (1 + R) ^ 2 / vmin + 2 * (1 + R) ^ 2 / vmin ^ 2) * (1 + |y| + y ^ 2) := by ring
    _ ≤ 4 * ((1 + R) ^ 2 / vmin ^ 2 + (1 + R) / vmin + 1 / vmin + 1) * (1 + |y| + y ^ 2) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)

/-- Local dominating bound on `mehlerKernel` and its derivatives for `r ∈ [a, b] ⊂ (-1, 1)` and
`|x| ≤ R`. -/
theorem mehlerKernel_dom {a b R : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) (hR : 0 ≤ R) :
    ∃ C > 0, ∃ c > 0, ∀ r ∈ Icc a b, ∀ x ∈ Icc (-R) R, ∀ y : ℝ,
      |mehlerKernel r x y| ≤ C * (1 + |y| + y ^ 2) * rexp (-(c * y ^ 2)) ∧
      |mehlerKernelDx r x y| ≤ C * (1 + |y| + y ^ 2) * rexp (-(c * y ^ 2)) ∧
      |mehlerKernelDxx r x y| ≤ C * (1 + |y| + y ^ 2) * rexp (-(c * y ^ 2)) ∧
      |mehlerKernelDr r x y| ≤ C * (1 + |y| + y ^ 2) * rexp (-(c * y ^ 2)) := by
  set rmax := max |a| |b|
  have hrmax_lt1 : rmax < 1 :=
    max_lt (abs_lt.2 ⟨ha, hab.trans_lt hb⟩) (abs_lt.2 ⟨ha.trans_le hab, hb⟩)
  have hrmax_nn : 0 ≤ rmax := le_trans (abs_nonneg a) (le_max_left _ _)
  set vmin := 1 - rmax ^ 2
  have hvmin_pos : 0 < vmin := sub_pos.2 (by nlinarith)
  have hr_abs : ∀ r ∈ Icc a b, |r| ≤ rmax := fun r hr =>
    abs_le.2 ⟨by linarith [neg_abs_le a, le_max_left |a| |b|, hr.1],
      by linarith [le_abs_self b, le_max_right |a| |b|, hr.2]⟩
  have hv_ge : ∀ r ∈ Icc a b, vmin ≤ 1 - r ^ 2 := fun r hr => by
    have h1 := hr_abs r hr
    have : r ^ 2 ≤ rmax ^ 2 := by rw [← sq_abs r]; nlinarith [abs_nonneg r]
    linarith
  have hv_le1 : ∀ r ∈ Icc a b, 1 - r ^ 2 ≤ 1 := fun r _ => by nlinarith [sq_nonneg r]
  set A : ℝ := (√(2 * π * vmin))⁻¹ * rexp (R ^ 2 / (2 * vmin))
  have hA_pos : 0 < A := by positivity
  have hK_le : ∀ r ∈ Icc a b, ∀ x ∈ Icc (-R) R, ∀ y : ℝ,
      mehlerKernel r x y ≤ A * rexp (-(1 / 4 * y ^ 2)) := by
    intro r hr x hx y
    have hv : vmin ≤ 1 - r ^ 2 := hv_ge r hr
    have hv1 : 1 - r ^ 2 ≤ 1 := hv_le1 r hr
    have hv_pos : 0 < 1 - r ^ 2 := lt_of_lt_of_le hvmin_pos hv
    have hrx : |r * x| ≤ R := by
      rw [abs_mul]
      calc |r| * |x| ≤ 1 * R :=
            mul_le_mul ((hr_abs r hr).trans hrmax_lt1.le) (abs_le.2 hx) (abs_nonneg x) zero_le_one
        _ = R := one_mul R
    have hsq : y ^ 2 / 2 - R ^ 2 ≤ (y - r * x) ^ 2 := by
      have h1 : (r * x) ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs (r * x)]; nlinarith [abs_nonneg (r * x)]
      nlinarith [sq_nonneg (y - 2 * (r * x))]
    have hexp_le : -(y - r * x) ^ 2 / (2 * (1 - r ^ 2)) ≤ R ^ 2 / (2 * vmin) - 1 / 4 * y ^ 2 := by
      have hnum : -(y - r * x) ^ 2 ≤ R ^ 2 - y ^ 2 / 2 := by linarith
      have h1 : -(y - r * x) ^ 2 / (2 * (1 - r ^ 2)) ≤
          R ^ 2 / (2 * (1 - r ^ 2)) - (y ^ 2 / 2) / (2 * (1 - r ^ 2)) := by
        rw [← sub_div]; exact div_le_div_of_nonneg_right hnum (by positivity)
      have h2 : R ^ 2 / (2 * (1 - r ^ 2)) ≤ R ^ 2 / (2 * vmin) :=
        div_le_div_of_nonneg_left (sq_nonneg R) (by positivity) (by linarith)
      have h3 : 1 / 4 * y ^ 2 ≤ (y ^ 2 / 2) / (2 * (1 - r ^ 2)) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg y, hv1]
      linarith
    have hpref : (√(2 * π * (1 - r ^ 2)))⁻¹ ≤ (√(2 * π * vmin))⁻¹ :=
      inv_anti₀ (by positivity) (Real.sqrt_le_sqrt (by nlinarith [pi_pos]))
    unfold mehlerKernel A
    calc
      (√(2 * π * (1 - r ^ 2)))⁻¹ * rexp (-(y - r * x) ^ 2 / (2 * (1 - r ^ 2)))
          ≤ (√(2 * π * vmin))⁻¹ * rexp (R ^ 2 / (2 * vmin) - 1 / 4 * y ^ 2) :=
            mul_le_mul hpref (Real.exp_le_exp.2 hexp_le) (Real.exp_nonneg _) (by positivity)
      _ = (√(2 * π * vmin))⁻¹ * rexp (R ^ 2 / (2 * vmin)) * rexp (-(1 / 4 * y ^ 2)) := by
            rw [sub_eq_add_neg, Real.exp_add]; ring
  set M : ℝ := (1 + R) ^ 2 / vmin ^ 2 + (1 + R) / vmin + 1 / vmin + 1
  have hM_ge1 : 1 ≤ M := by
    unfold M
    have := div_nonneg (sq_nonneg (1 + R)) (sq_nonneg vmin)
    have := div_nonneg (show 0 ≤ 1 + R by linarith) hvmin_pos.le
    have := div_nonneg zero_le_one hvmin_pos.le
    linarith
  have hM_pos : 0 < M := by linarith
  refine ⟨A * (4 * M), by positivity, 1 / 4, by norm_num, fun r hr x hx y => ?_⟩
  have hv : vmin ≤ 1 - r ^ 2 := hv_ge r hr
  have hv_pos : 0 < 1 - r ^ 2 := lt_of_lt_of_le hvmin_pos hv
  have hr1 : |r| ≤ 1 := (hr_abs r hr).trans hrmax_lt1.le
  have hr2 : r ^ 2 ≤ 1 := by rw [← sq_abs r]; nlinarith [abs_nonneg r]
  have hxR : |x| ≤ R := abs_le.2 hx
  have hz_le : |y - r * x| ≤ |y| + R := by
    calc |y - r * x| ≤ |y| + |r * x| := abs_sub _ _
      _ = |y| + |r| * |x| := by rw [abs_mul]
      _ ≤ |y| + 1 * R := add_le_add le_rfl (mul_le_mul hr1 hxR (abs_nonneg x) zero_le_one)
      _ = |y| + R := by rw [one_mul]
  have hz2_le : (y - r * x) ^ 2 ≤ 2 * (y ^ 2 + R ^ 2) := by
    have : |y - r * x| ^ 2 ≤ (|y| + R) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hz_le 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (|y| - R), sq_abs y]
  have hK := hK_le r hr x hx y
  have hK_nn := mehlerKernel_nonneg r x y
  have hpoly_ge1 : 1 ≤ 1 + |y| + y ^ 2 := by nlinarith [abs_nonneg y, sq_nonneg y]
  have h1y : |y| + R ≤ (1 + R) * (1 + |y| + y ^ 2) := by nlinarith [abs_nonneg y, sq_nonneg y, hR]
  have h2y : 2 * (y ^ 2 + R ^ 2) ≤ 2 * (1 + R) ^ 2 * (1 + |y| + y ^ 2) := by
    nlinarith [abs_nonneg y, sq_nonneg y, hR]
  have hinv_v : (1 - r ^ 2)⁻¹ ≤ vmin⁻¹ := inv_anti₀ hvmin_pos hv
  have hinv_v2 : ((1 - r ^ 2) ^ 2)⁻¹ ≤ (vmin ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hvmin_pos) (pow_le_pow_left₀ hvmin_pos.le hv 2)
  have hbase : A * (4 * M) * (1 + |y| + y ^ 2) * rexp (-(1 / 4 * y ^ 2)) =
      4 * M * (1 + |y| + y ^ 2) * (A * rexp (-(1 / 4 * y ^ 2))) := by ring
  rw [hbase]
  have hK_step : ∀ {B : ℝ}, 0 ≤ B → B ≤ 4 * M * (1 + |y| + y ^ 2) →
      B * mehlerKernel r x y ≤ 4 * M * (1 + |y| + y ^ 2) * (A * rexp (-(1 / 4 * y ^ 2))) :=
    fun hB0 hBle => mul_le_mul hBle hK hK_nn (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_of_nonneg hK_nn]
    simpa only [one_mul] using hK_step zero_le_one (by nlinarith [hpoly_ge1, hM_ge1])
  · unfold mehlerKernelDx
    rw [abs_mul, abs_of_nonneg hK_nn]
    refine hK_step (abs_nonneg _) ?_
    rw [abs_div, abs_mul, abs_of_pos hv_pos]
    calc
      |r| * |y - r * x| / (1 - r ^ 2) ≤ 1 * (|y| + R) / vmin := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul (mul_le_mul hr1 hz_le (abs_nonneg _) zero_le_one) hinv_v
              (by positivity) (by positivity)
      _ ≤ (1 + R) / vmin * (1 + |y| + y ^ 2) := by
            rw [one_mul, div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h1y hvmin_pos.le
      _ ≤ 4 * M * (1 + |y| + y ^ 2) :=
            mul_le_mul_of_nonneg_right (by
              unfold M
              linarith [div_nonneg (sq_nonneg (1 + R)) (sq_nonneg vmin),
                div_nonneg zero_le_one hvmin_pos.le]) (by linarith)
  · unfold mehlerKernelDxx
    rw [abs_mul, abs_of_nonneg hK_nn]
    refine hK_step (abs_nonneg _) ?_
    have htr := abs_sub (r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2) (r ^ 2 / (1 - r ^ 2))
    have h1 : |r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2| ≤
        2 * (1 + R) ^ 2 / vmin ^ 2 * (1 + |y| + y ^ 2) := by
      rw [abs_of_nonneg (by positivity)]
      calc r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2
          ≤ 1 * (2 * (y ^ 2 + R ^ 2)) / vmin ^ 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul (mul_le_mul hr2 hz2_le (sq_nonneg _) zero_le_one) hinv_v2
              (by positivity) (by positivity)
        _ ≤ 2 * (1 + R) ^ 2 / vmin ^ 2 * (1 + |y| + y ^ 2) := by
            rw [one_mul, div_mul_eq_mul_div]
            exact div_le_div_of_nonneg_right h2y (sq_nonneg _)
    have h2 : |r ^ 2 / (1 - r ^ 2)| ≤ 1 / vmin * (1 + |y| + y ^ 2) := by
      rw [abs_of_nonneg (by positivity)]
      calc r ^ 2 / (1 - r ^ 2) ≤ 1 / vmin := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul hr2 hinv_v (by positivity) zero_le_one
        _ ≤ 1 / vmin * (1 + |y| + y ^ 2) :=
              le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg y, sq_nonneg y])
    calc
      |r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2 - r ^ 2 / (1 - r ^ 2)|
          ≤ 2 * (1 + R) ^ 2 / vmin ^ 2 * (1 + |y| + y ^ 2) + 1 / vmin * (1 + |y| + y ^ 2) :=
            htr.trans (add_le_add h1 h2)
      _ ≤ 4 * M * (1 + |y| + y ^ 2) := by
            have hcoeff : 2 * (1 + R) ^ 2 / vmin ^ 2 + 1 / vmin ≤ 4 * M := by
              unfold M
              have hdiv2 : 2 * (1 + R) ^ 2 / vmin ^ 2 = 2 * ((1 + R) ^ 2 / vmin ^ 2) :=
                mul_div_assoc 2 _ _
              have := div_nonneg (sq_nonneg (1 + R)) (sq_nonneg vmin)
              have := div_nonneg (show 0 ≤ 1 + R by linarith) hvmin_pos.le
              have := div_nonneg zero_le_one hvmin_pos.le
              linarith
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
  · unfold mehlerKernelDr
    rw [abs_mul, abs_of_nonneg hK_nn]
    exact hK_step (abs_nonneg _)
      (mehlerKernelDr_prefactor_le hR hvmin_pos rfl hv hr1 hxR hz_le hz2_le h1y h2y)

/-- Differentiating `ou1D r f x` in `x`, twice in `x`, and in `r`, yielding the exact pointwise
Ornstein–Uhlenbeck PDE `r ∂_r u = x ∂_x u - ∂_{xx} u` and uniform derivative bounds. -/
theorem ou1D_derivs_and_pde {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {f : ℝ → ℝ} (hf : Measurable f) (hf01 : ∀ y, f y ∈ Icc 0 1) (x : ℝ) :
    HasDerivAt (ou1D r f) (∫ y, mehlerKernelDx r x y * f y) x ∧
    HasDerivAt (deriv (ou1D r f)) (∫ y, mehlerKernelDxx r x y * f y) x ∧
    HasDerivAt (fun r' => ou1D r' f x) (∫ y, mehlerKernelDr r x y * f y) r ∧
    r * deriv (fun r' => ou1D r' f x) r =
      x * deriv (ou1D r f) x - deriv (deriv (ou1D r f)) x ∧
    |deriv (ou1D r f) x| ≤ 1 / √(1 - r ^ 2) ∧
    |deriv (deriv (ou1D r f)) x| ≤ 2 / (1 - r ^ 2) := by
  have hr : |r| < 1 := abs_lt.2 ⟨by linarith, hr1⟩
  have hv : 0 < 1 - r ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one r).2 hr)
  have hf_abs : ∀ y, |f y| ≤ 1 := fun y => abs_le.2 ⟨by linarith [(hf01 y).1], (hf01 y).2⟩
  set a := r / 2
  set b := (r + 1) / 2
  set R := |x| + 1
  have ha_gt : -1 < a := by simp only [a]; linarith
  have hb_lt : b < 1 := by simp only [b]; linarith
  have hab_le : a ≤ b := by simp only [a, b]; linarith
  have har : a < r := by simp only [a]; linarith
  have hrb : r < b := by simp only [b]; linarith
  obtain ⟨C, hC, c, hc, hdom⟩ :=
    mehlerKernel_dom (a := a) (b := b) (R := R) ha_gt hb_lt hab_le (by positivity)
  set bound : ℝ → ℝ := fun y => C * (1 + |y| + y ^ 2) * rexp (-(c * y ^ 2))
  have hbound_int : Integrable bound := by
    have h := (integrable_poly_mul_exp_neg_sq hc).const_mul C
    exact h.congr (ae_of_all _ fun y => by unfold bound; ring)
  have hr_mem : r ∈ Icc a b := ⟨har.le, hrb.le⟩
  have hIoo_r : Ioo a b ∈ 𝓝 r := Ioo_mem_nhds har hrb
  have hIoo_x : Ioo (x - 1) (x + 1) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
  have hx_sub : ∀ x' ∈ Ioo (x - 1) (x + 1), x' ∈ Icc (-R) R := fun x' hx' =>
    ⟨by linarith [neg_abs_le x, hx'.1], by linarith [le_abs_self x, hx'.2]⟩
  have hmK (r' x' : ℝ) : Measurable (fun y => mehlerKernel r' x' y) := by
    unfold mehlerKernel; fun_prop
  have hmKx (r' x' : ℝ) : Measurable (fun y => mehlerKernelDx r' x' y) := by
    unfold mehlerKernelDx mehlerKernel; fun_prop
  have hmKxx (r' x' : ℝ) : Measurable (fun y => mehlerKernelDxx r' x' y) := by
    unfold mehlerKernelDxx mehlerKernel; fun_prop
  have hmKr (r' x' : ℝ) : Measurable (fun y => mehlerKernelDr r' x' y) := by
    unfold mehlerKernelDr mehlerKernel; fun_prop
  have hint_prod : ∀ {g : ℝ → ℝ}, Measurable g → (∀ y, |g y| ≤ bound y) →
      Integrable (fun y => g y * f y) := fun {g} hg hgle =>
    hbound_int.mono' (hg.mul hf).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hf_abs y)).trans (hgle y))
  have hdx : HasDerivAt (ou1D r f) (∫ y, mehlerKernelDx r x y * f y) x := by
    have hraw := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioo (x - 1) (x + 1))
      (F := fun x' y => mehlerKernel r x' y * f y)
      (F' := fun x' y => mehlerKernelDx r x' y * f y) (bound := bound) hIoo_x
      (Eventually.of_forall fun x' => ((hmK r x').mul hf).aestronglyMeasurable)
      (hint_prod (hmK r x) fun y => (hdom r hr_mem x (hx_sub x ⟨by linarith, by linarith⟩) y).1)
      ((hmKx r x).mul hf).aestronglyMeasurable
      (ae_of_all _ fun y x' hx' => by
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) (hf_abs y)).trans
          (hdom r hr_mem x' (hx_sub x' hx') y).2.1)
      hbound_int
      (ae_of_all _ fun y x' _ => (hasDerivAt_mehlerKernel_x hr x' y).mul_const (f y))).2
    refine hraw.congr_of_eventuallyEq
      (Eventually.of_forall fun x' => (ou1D_eq_integral_mehler hr hf x'))
  have hdx_loc : ∀ x' ∈ Ioo (x - 1) (x + 1),
      deriv (ou1D r f) x' = ∫ y, mehlerKernelDx r x' y * f y := by
    intro x' hx'
    have hraw := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioo (x - 1) (x + 1))
      (F := fun u y => mehlerKernel r u y * f y)
      (F' := fun u y => mehlerKernelDx r u y * f y) (bound := bound)
      (isOpen_Ioo.mem_nhds hx')
      (Eventually.of_forall fun u => ((hmK r u).mul hf).aestronglyMeasurable)
      (hint_prod (hmK r x') fun y => (hdom r hr_mem x' (hx_sub x' hx') y).1)
      ((hmKx r x').mul hf).aestronglyMeasurable
      (ae_of_all _ fun y u hu => by
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) (hf_abs y)).trans
          (hdom r hr_mem u (hx_sub u hu) y).2.1)
      hbound_int
      (ae_of_all _ fun y u _ => (hasDerivAt_mehlerKernel_x hr u y).mul_const (f y))).2
    exact (hraw.congr_of_eventuallyEq
      (Eventually.of_forall fun u => ou1D_eq_integral_mehler hr hf u)).deriv
  have hdxx : HasDerivAt (deriv (ou1D r f)) (∫ y, mehlerKernelDxx r x y * f y) x := by
    have hraw := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioo (x - 1) (x + 1))
      (F := fun x' y => mehlerKernelDx r x' y * f y)
      (F' := fun x' y => mehlerKernelDxx r x' y * f y) (bound := bound) hIoo_x
      (Eventually.of_forall fun x' => ((hmKx r x').mul hf).aestronglyMeasurable)
      (hint_prod (hmKx r x) fun y =>
        (hdom r hr_mem x (hx_sub x ⟨by linarith, by linarith⟩) y).2.1)
      ((hmKxx r x).mul hf).aestronglyMeasurable
      (ae_of_all _ fun y x' hx' => by
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) (hf_abs y)).trans
          (hdom r hr_mem x' (hx_sub x' hx') y).2.2.1)
      hbound_int
      (ae_of_all _ fun y x' _ => (hasDerivAt_mehlerKernelDx_x hr x' y).mul_const (f y))).2
    refine hraw.congr_of_eventuallyEq ?_
    filter_upwards [hIoo_x] with x' hx' using hdx_loc x' hx'
  have hdr : HasDerivAt (fun r' => ou1D r' f x) (∫ y, mehlerKernelDr r x y * f y) r := by
    have hraw := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioo a b)
      (F := fun r' y => mehlerKernel r' x y * f y)
      (F' := fun r' y => mehlerKernelDr r' x y * f y) (bound := bound) hIoo_r
      (Eventually.of_forall fun r' => ((hmK r' x).mul hf).aestronglyMeasurable)
      (hint_prod (hmK r x) fun y => (hdom r hr_mem x (hx_sub x ⟨by linarith, by linarith⟩) y).1)
      ((hmKr r x).mul hf).aestronglyMeasurable
      (ae_of_all _ fun y r' hr' => by
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) (hf_abs y)).trans
          (hdom r' ⟨hr'.1.le, hr'.2.le⟩ x (hx_sub x ⟨by linarith, by linarith⟩) y).2.2.2)
      hbound_int
      (ae_of_all _ fun y r' hr' =>
        (hasDerivAt_mehlerKernel_r (abs_lt.2 ⟨ha_gt.trans hr'.1, hr'.2.trans hb_lt⟩)
          x y).mul_const (f y))).2
    refine hraw.congr_of_eventuallyEq ?_
    filter_upwards [hIoo_r] with r' hr'
    exact ou1D_eq_integral_mehler (abs_lt.2 ⟨ha_gt.trans hr'.1, hr'.2.trans hb_lt⟩) hf x
  have hpde : r * deriv (fun r' => ou1D r' f x) r =
      x * deriv (ou1D r f) x - deriv (deriv (ou1D r f)) x := by
    rw [hdr.deriv, hdx.deriv, hdxx.deriv, ← integral_const_mul, ← integral_const_mul]
    have hix := hint_prod (hmKx r x) fun y =>
      (hdom r hr_mem x (hx_sub x ⟨by linarith, by linarith⟩) y).2.1
    have hixx := hint_prod (hmKxx r x) fun y =>
      (hdom r hr_mem x (hx_sub x ⟨by linarith, by linarith⟩) y).2.2.1
    rw [← integral_sub (hix.const_mul x) hixx]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have h := mehlerKernel_pde hr x y
    linear_combination h * f y
  have hvn : (1 - r ^ 2).toNNReal ≠ 0 := by simpa [hv]
  have hmap : (gaussianReal 0 1).map (fun w => r * x + √(1 - r ^ 2) * w) =
      gaussianReal (r * x) (1 - r ^ 2).toNNReal := by
    rw [show (fun w => r * x + √(1 - r ^ 2) * w) = (fun s => r * x + s) ∘
          fun w => √(1 - r ^ 2) * w from rfl,
      ← Measure.map_map (measurable_const_add (r * x)) (measurable_const_mul _),
      gaussianReal_map_const_mul, gaussianReal_map_const_add]
    exact congrArg₂ _ (by ring)
      (Subtype.ext (by simp [Real.sq_sqrt hv.le, Real.coe_toNNReal _ hv.le]))
  have hdx_bound : |deriv (ou1D r f) x| ≤ 1 / √(1 - r ^ 2) := by
    rw [hdx.deriv]
    have hix := hint_prod (hmKx r x) fun y =>
      (hdom r hr_mem x (hx_sub x ⟨by linarith, by linarith⟩) y).2.1
    refine abs_integral_le_integral_abs.trans ?_
    have hgauss : ∫ y, |r * (y - r * x) / (1 - r ^ 2)| * mehlerKernel r x y =
        r / √(1 - r ^ 2) * ∫ w, |w| ∂gaussianReal 0 1 := by
      have h1 : ∀ y, |r * (y - r * x) / (1 - r ^ 2)| * mehlerKernel r x y =
          gaussianPDFReal (r * x) (1 - r ^ 2).toNNReal y • |r * (y - r * x) / (1 - r ^ 2)| :=
        fun y => by rw [smul_eq_mul, mehlerKernel_eq_gaussianPDFReal hr, mul_comm]
      simp_rw [h1]
      rw [← integral_gaussianReal_eq_integral_smul hvn, ← hmap,
        integral_map (by fun_prop) (by fun_prop)]
      have hsimp : ∀ w : ℝ, |r * (r * x + √(1 - r ^ 2) * w - r * x) / (1 - r ^ 2)| =
          r / √(1 - r ^ 2) * |w| := fun w => by
        rw [add_sub_cancel_left, abs_div, abs_mul, abs_mul, abs_of_pos hr0, abs_of_pos hv,
          abs_of_pos (Real.sqrt_pos.2 hv)]
        have hs : 0 < √(1 - r ^ 2) := Real.sqrt_pos.2 hv
        rw [div_eq_iff hv.ne', show r / √(1 - r ^ 2) * |w| * (1 - r ^ 2) =
          r * |w| * ((1 - r ^ 2) / √(1 - r ^ 2)) by ring]
        rw [show (1 - r ^ 2) / √(1 - r ^ 2) = √(1 - r ^ 2) by
          rw [div_eq_iff hs.ne', Real.mul_self_sqrt hv.le]]
        ring
      simp_rw [hsimp, integral_const_mul]
    have hid2 : Integrable (fun w : ℝ => w ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 2).integrable_sq
    have habs_le1 : ∫ w, |w| ∂gaussianReal 0 1 ≤ 1 := by
      have hcs := sq_integral_mul_le (P := gaussianReal 0 1) (f := fun w => |w|)
        (g := fun _ => (1 : ℝ))
        (by simpa only [sq_abs] using hid2)
        (by simpa only [one_pow] using integrable_const (1 : ℝ))
        (by simpa using ((memLp_id_gaussianReal 1).integrable le_rfl).abs)
      simp only [mul_one, sq_abs, one_pow, integral_const, probReal_univ, smul_eq_mul,
        integral_sq_gaussianReal] at hcs
      nlinarith [integral_nonneg (μ := gaussianReal 0 1) fun w : ℝ => abs_nonneg w]
    have hdom_g : Integrable (fun y => |r * (y - r * x) / (1 - r ^ 2)| * mehlerKernel r x y) := by
      refine hbound_int.mono' (by fun_prop) (ae_of_all _ fun y => ?_)
      have h := (hdom r hr_mem x (hx_sub x ⟨by linarith, by linarith⟩) y).2.1
      unfold mehlerKernelDx at h
      rw [abs_mul, abs_of_nonneg (mehlerKernel_nonneg r x y)] at h
      simpa [Real.norm_eq_abs, abs_of_nonneg (mehlerKernel_nonneg r x y)] using h
    calc
      ∫ y, |mehlerKernelDx r x y * f y|
          ≤ ∫ y, |r * (y - r * x) / (1 - r ^ 2)| * mehlerKernel r x y := by
            refine integral_mono hix.abs hdom_g fun y => ?_
            unfold mehlerKernelDx
            rw [abs_mul, abs_mul, abs_of_nonneg (mehlerKernel_nonneg r x y)]
            exact mul_le_of_le_one_right
              (mul_nonneg (abs_nonneg _) (mehlerKernel_nonneg r x y)) (hf_abs y)
      _ = r / √(1 - r ^ 2) * ∫ w, |w| ∂gaussianReal 0 1 := hgauss
      _ ≤ 1 / √(1 - r ^ 2) * 1 :=
            mul_le_mul (div_le_div_of_nonneg_right hr1.le (by positivity)) habs_le1
              (integral_nonneg fun _ => abs_nonneg _) (by positivity)
      _ = 1 / √(1 - r ^ 2) := mul_one _
  have hdxx_bound : |deriv (deriv (ou1D r f)) x| ≤ 2 / (1 - r ^ 2) := by
    rw [hdxx.deriv]
    have hixx := hint_prod (hmKxx r x) fun y =>
      (hdom r hr_mem x (hx_sub x ⟨by linarith, by linarith⟩) y).2.2.1
    refine abs_integral_le_integral_abs.trans ?_
    have hgauss : ∫ y, (r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2 + r ^ 2 / (1 - r ^ 2)) *
        mehlerKernel r x y = 2 * r ^ 2 / (1 - r ^ 2) := by
      have h1 : ∀ y, (r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2 + r ^ 2 / (1 - r ^ 2)) *
          mehlerKernel r x y =
          gaussianPDFReal (r * x) (1 - r ^ 2).toNNReal y •
            (r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2 + r ^ 2 / (1 - r ^ 2)) :=
        fun y => by rw [smul_eq_mul, mehlerKernel_eq_gaussianPDFReal hr, mul_comm]
      simp_rw [h1]
      rw [← integral_gaussianReal_eq_integral_smul hvn, ← hmap,
        integral_map (by fun_prop) (by fun_prop)]
      have hsimp : ∀ w : ℝ,
          r ^ 2 * (r * x + √(1 - r ^ 2) * w - r * x) ^ 2 / (1 - r ^ 2) ^ 2 +
              r ^ 2 / (1 - r ^ 2) =
            (r ^ 2 / (1 - r ^ 2)) * (w ^ 2 + 1) := fun w => by
        rw [add_sub_cancel_left, mul_pow, Real.sq_sqrt hv.le]
        field_simp [hv.ne']
      simp_rw [hsimp, integral_const_mul]
      have hid2 : Integrable (fun w : ℝ => w ^ 2) (gaussianReal 0 1) :=
        (memLp_id_gaussianReal 2).integrable_sq
      rw [integral_add hid2 (integrable_const 1),
        integral_sq_gaussianReal, integral_const, probReal_univ, smul_eq_mul, one_mul]
      ring
    have hdom_g : Integrable (fun y =>
        (r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2 + r ^ 2 / (1 - r ^ 2)) *
          mehlerKernel r x y) := by
      have hq : Integrable (fun y : ℝ => (y - r * x) ^ 2)
          (gaussianReal (r * x) (1 - r ^ 2).toNNReal) :=
        ((memLp_id_gaussianReal 2).sub (memLp_const (r * x))).integrable_sq
      have h0 : Integrable
          (fun y : ℝ => r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2 + r ^ 2 / (1 - r ^ 2))
          (gaussianReal (r * x) (1 - r ^ 2).toNNReal) :=
        ((hq.const_mul (r ^ 2)).div_const ((1 - r ^ 2) ^ 2)).add (integrable_const _)
      exact ((integrable_gaussianReal_iff_integrable_mul_gaussianPDFReal (μ :=
        r * x) hvn).1 h0).congr
        (ae_of_all _ fun y => by dsimp only; rw [mehlerKernel_eq_gaussianPDFReal hr, mul_comm])
    calc
      ∫ y, |mehlerKernelDxx r x y * f y|
          ≤ ∫ y, (r ^ 2 * (y - r * x) ^ 2 / (1 - r ^ 2) ^ 2 + r ^ 2 / (1 - r ^ 2)) *
              mehlerKernel r x y := by
            refine integral_mono hixx.abs hdom_g fun y => ?_
            unfold mehlerKernelDxx
            rw [abs_mul, abs_mul, abs_of_nonneg (mehlerKernel_nonneg r x y)]
            refine (mul_le_of_le_one_right
              (mul_nonneg (abs_nonneg _) (mehlerKernel_nonneg r x y)) (hf_abs y)).trans ?_
            refine mul_le_mul_of_nonneg_right ?_ (mehlerKernel_nonneg r x y)
            exact (abs_sub _ _).trans (by
              rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)])
      _ = 2 * r ^ 2 / (1 - r ^ 2) := hgauss
      _ ≤ 2 / (1 - r ^ 2) := by
            refine div_le_div_of_nonneg_right ?_ hv.le
            nlinarith
  exact ⟨hdx, hdxx, hdr, hpde, hdx_bound, hdxx_bound⟩

/-- `ou1D r` preserves the closed interval `[δ, 1 - δ]`. -/
theorem ou1D_mem_Icc {δ : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hfδ : ∀ y, f y ∈ Icc δ (1 - δ)) (r x : ℝ) :
    ou1D r f x ∈ Icc δ (1 - δ) := by
  have hint : Integrable (fun y => f (r * x + √(1 - r ^ 2) * y)) (gaussianReal 0 1) :=
    Integrable.of_mem_Icc δ (1 - δ) (hf.comp (by fun_prop)).aemeasurable
      (ae_of_all _ fun y => hfδ _)
  constructor
  · simpa [ou1D] using integral_mono (integrable_const δ) hint fun y => (hfδ _).1
  · simpa [ou1D] using integral_mono hint (integrable_const (1 - δ)) fun y => (hfδ _).2

/-- 1D Gaussian IBP step along the first coordinate of `correlatedGaussian ρ`. -/
theorem heatflow_ibp_left {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {u v : ℝ → ℝ}
    (hu_mem : ∀ x, u x ∈ Icc δ (1 - δ)) (hv_mem : ∀ y, v y ∈ Icc δ (1 - δ))
    (hu_d1 : Differentiable ℝ u) (hu_d2 : Differentiable ℝ (deriv u))
    (hv_d1 : Differentiable ℝ v)
    {Cu Cv : ℝ} (hCu : ∀ x, |deriv u x| ≤ Cu) (hCu2 : ∀ x, |deriv (deriv u) x| ≤ Cu)
    (hCv : ∀ y, |deriv v y| ≤ Cv) :
    ∫ p, (p.1 * deriv u p.1 - deriv (deriv u) p.1) *
        deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1) ∂correlatedGaussian ρ =
      ∫ p, (deriv (fun α => deriv (fun α => gaussianQuadrant ρ α (v p.2)) α) (u p.1) *
          deriv u p.1 ^ 2 +
        ρ * deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (u p.1)) (v p.2) *
          deriv u p.1 * deriv v p.2) ∂correlatedGaussian ρ := by
  have hρ : |ρ| < 1 := abs_lt.2 ⟨by linarith, hρ1⟩
  have hIcc_sub : Icc δ (1 - δ) ×ˢ Icc δ (1 - δ) ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 :=
    Set.prod_mono (fun t ht => ⟨lt_of_lt_of_le hδ0 ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
      (fun t ht => ⟨lt_of_lt_of_le hδ0 ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
  have hu_oo : ∀ x, u x ∈ Ioo (0 : ℝ) 1 := fun x =>
    ⟨lt_of_lt_of_le hδ0 (hu_mem x).1, lt_of_le_of_lt (hu_mem x).2 (by linarith)⟩
  have hv_oo : ∀ y, v y ∈ Ioo (0 : ℝ) 1 := fun y =>
    ⟨lt_of_lt_of_le hδ0 (hv_mem y).1, lt_of_le_of_lt (hv_mem y).2 (by linarith)⟩
  have hL1_cont : ContinuousOn (fun q : ℝ × ℝ =>
      deriv (fun α => deriv (fun α => gaussianQuadrant ρ α q.2) α) q.1)
      (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := by
    have heq : EqOn (fun q : ℝ × ℝ =>
        deriv (fun α => deriv (fun α => gaussianQuadrant ρ α q.2) α) q.1)
        (fun q : ℝ × ℝ => -(ρ / √(1 - ρ ^ 2)) * (φ (gaussianQuantile q.1))⁻¹ *
          φ ((gaussianQuantile q.2 - ρ * gaussianQuantile q.1) / √(1 - ρ ^ 2)))
        (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := fun q hq =>
      (hasDerivAt_gaussianQuadrant_left_left hρ (hIcc_sub hq).1 (hIcc_sub hq).2).deriv
    refine ContinuousOn.congr ?_ heq
    have hq1 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.1)
        (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) :=
      continuousOn_gaussianQuantile.comp continuousOn_fst fun q hq => (hIcc_sub hq).1
    have hq2 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.2)
        (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) :=
      continuousOn_gaussianQuantile.comp continuousOn_snd fun q hq => (hIcc_sub hq).2
    refine ((continuousOn_const.mul ((continuous_gaussianPDFReal 0 1).comp_continuousOn hq1 |>.inv₀
      fun q _ => (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne')).mul ?_)
    exact (continuous_gaussianPDFReal 0 1).comp_continuousOn
      ((hq2.sub (continuousOn_const.mul hq1)).div_const _)
  have hL2_cont : ContinuousOn (fun q : ℝ × ℝ =>
      deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) q.1) q.2)
      (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := by
    have heq : EqOn (fun q : ℝ × ℝ =>
        deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) q.1) q.2)
        (fun q : ℝ × ℝ => (√(1 - ρ ^ 2))⁻¹ * (φ (gaussianQuantile q.2))⁻¹ *
          φ ((gaussianQuantile q.2 - ρ * gaussianQuantile q.1) / √(1 - ρ ^ 2)))
        (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := fun q hq =>
      (hasDerivAt_gaussianQuadrant_left_right hρ (hIcc_sub hq).1 (hIcc_sub hq).2).deriv
    refine ContinuousOn.congr ?_ heq
    have hq1 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.1)
        (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) :=
      continuousOn_gaussianQuantile.comp continuousOn_fst fun q hq => (hIcc_sub hq).1
    have hq2 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.2)
        (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) :=
      continuousOn_gaussianQuantile.comp continuousOn_snd fun q hq => (hIcc_sub hq).2
    refine ((continuousOn_const.mul ((continuous_gaussianPDFReal 0 1).comp_continuousOn hq2 |>.inv₀
      fun q _ => (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne')).mul ?_)
    exact (continuous_gaussianPDFReal 0 1).comp_continuousOn
      ((hq2.sub (continuousOn_const.mul hq1)).div_const _)
  have hcomp : IsCompact (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M1, hM1⟩ := hcomp.exists_bound_of_continuousOn hL1_cont
  obtain ⟨M2, hM2⟩ := hcomp.exists_bound_of_continuousOn hL2_cont
  have hCu_nn : 0 ≤ Cu := (abs_nonneg _).trans (hCu 0)
  have hCv_nn : 0 ≤ Cv := (abs_nonneg _).trans (hCv 0)
  have hM1_nn : 0 ≤ M1 := (norm_nonneg _).trans (hM1 (u 0, v 0) ⟨hu_mem 0, hv_mem 0⟩)
  have hM2_nn : 0 ≤ M2 := (norm_nonneg _).trans (hM2 (u 0, v 0) ⟨hu_mem 0, hv_mem 0⟩)
  have hL_bdd : ∀ x y, |deriv (fun α => gaussianQuadrant ρ α (v y)) (u x)| ≤ 1 := fun x y => by
    rw [deriv_gaussianQuadrant_left hρ (hu_oo x) (hv_oo y), abs_of_nonneg (cdf_nonneg _ _)]
    exact cdf_le_one _ _
  have hL_cont : Continuous (fun p : ℝ × ℝ =>
      deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1)) := by
    have heq : (fun p : ℝ × ℝ => deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1)) =
        fun p => Φ ((gaussianQuantile (v p.2) - ρ * gaussianQuantile (u p.1)) / √(1 - ρ ^ 2)) :=
      funext fun p => deriv_gaussianQuadrant_left hρ (hu_oo p.1) (hv_oo p.2)
    rw [heq]
    have hcu : Continuous fun p : ℝ × ℝ => gaussianQuantile (u p.1) :=
      (continuous_iff_continuousAt.2 fun x =>
        (continuousAt_gaussianQuantile (hu_oo x)).comp hu_d1.continuous.continuousAt).comp
        continuous_fst
    have hcv : Continuous fun p : ℝ × ℝ => gaussianQuantile (v p.2) :=
      (continuous_iff_continuousAt.2 fun y =>
        (continuousAt_gaussianQuantile (hv_oo y)).comp hv_d1.continuous.continuousAt).comp
        continuous_snd
    exact (continuous_cdf_gaussianReal 0 one_ne_zero).comp
      ((hcv.sub (continuous_const.mul hcu)).div_const _)
  have hL1_cont_all : Continuous (fun p : ℝ × ℝ =>
      deriv (fun α => deriv (fun α => gaussianQuadrant ρ α (v p.2)) α) (u p.1)) :=
    hL1_cont.comp_continuous ((hu_d1.continuous.comp continuous_fst).prodMk
      (hv_d1.continuous.comp continuous_snd)) fun p => ⟨hu_mem p.1, hv_mem p.2⟩
  have hL2_cont_all : Continuous (fun p : ℝ × ℝ =>
      deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (u p.1)) (v p.2)) :=
    hL2_cont.comp_continuous ((hu_d1.continuous.comp continuous_fst).prodMk
      (hv_d1.continuous.comp continuous_snd)) fun p => ⟨hu_mem p.1, hv_mem p.2⟩
  set mapρ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, ρ * q.1 + √(1 - ρ ^ 2) * q.2)
  have hLHS_int : Integrable (fun q : ℝ × ℝ =>
      (q.1 * deriv u q.1 - deriv (deriv u) q.1) *
        deriv (fun α => gaussianQuadrant ρ α (v (mapρ q).2)) (u q.1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have hdom : Integrable (fun q : ℝ × ℝ => (|q.1| * Cu + Cu) * 1)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have hfst : Integrable (fun q : ℝ × ℝ => |q.1|)
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
        MeasurePreserving.integrable_comp_of_integrable
          ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
          ((memLp_id_gaussianReal 1).integrable le_rfl).abs
      simpa using (hfst.mul_const Cu).add (integrable_const Cu)
    refine hdom.mono' ?_ (ae_of_all _ fun q => ?_)
    · exact (((measurable_fst.mul (hu_d2.continuous.measurable.comp measurable_fst)).sub
        ((measurable_deriv (deriv u)).comp measurable_fst)).mul
        (hL_cont.measurable.comp (by fun_prop : Measurable mapρ))).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul, mul_one]
      refine (mul_le_of_le_one_right (abs_nonneg _) (hL_bdd q.1 (mapρ q).2)).trans ?_
      refine (abs_sub _ _).trans (add_le_add ?_ (hCu2 q.1))
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hCu q.1) (abs_nonneg _)
  have hRHS_int : Integrable (fun q : ℝ × ℝ =>
      deriv (fun α => deriv (fun α => gaussianQuadrant ρ α (v (mapρ q).2)) α) (u q.1) *
          deriv u q.1 ^ 2 +
        ρ * deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (u q.1)) (v (mapρ q).2) *
          deriv u q.1 * deriv v (mapρ q).2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    refine Integrable.of_bound ?_ (M1 * Cu ^ 2 + ρ * M2 * Cu * Cv) (ae_of_all _ fun q => ?_)
    · have hm1 : Measurable (fun q : ℝ × ℝ => deriv (fun α => deriv (fun α =>
          gaussianQuadrant ρ α (v (mapρ q).2)) α) (u q.1)) :=
        hL1_cont_all.measurable.comp (by fun_prop : Measurable mapρ)
      have hm2 : Measurable (fun q : ℝ × ℝ => deriv (fun β => deriv (fun α =>
          gaussianQuadrant ρ α β) (u q.1)) (v (mapρ q).2)) :=
        hL2_cont_all.measurable.comp (by fun_prop : Measurable mapρ)
      have hmu : Measurable (fun q : ℝ × ℝ => deriv u q.1) :=
        hu_d2.continuous.measurable.comp measurable_fst
      have hmv : Measurable (fun q : ℝ × ℝ => deriv v (mapρ q).2) :=
        (measurable_deriv v).comp (by fun_prop)
      exact ((hm1.mul (hmu.pow_const 2)).add
        (((measurable_const.mul hm2).mul hmu).mul hmv)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_pow]
        have h1 : |deriv (fun α => deriv (fun α => gaussianQuadrant ρ α (v (mapρ q).2)) α)
            (u q.1)| ≤ M1 := hM1 (u q.1, v (mapρ q).2) ⟨hu_mem _, hv_mem _⟩
        exact mul_le_mul h1 (pow_le_pow_left₀ (abs_nonneg _) (hCu _) 2) (sq_nonneg _) hM1_nn
      · rw [abs_mul, abs_mul, abs_mul, abs_of_pos hρ0]
        have h2 : |deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (u q.1))
            (v (mapρ q).2)| ≤ M2 := hM2 (u q.1, v (mapρ q).2) ⟨hu_mem _, hv_mem _⟩
        exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left h2 hρ0.le) (hCu _) (abs_nonneg _) (by positivity))
          (hCv _) (abs_nonneg _) (by positivity)
  rw [correlatedGaussian_def, integral_map (by fun_prop) ?_, integral_map (by fun_prop) ?_]
  · rw [integral_prod_symm _ hLHS_int, integral_prod_symm _ hRHS_int]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    let G : ℝ → ℝ := fun x =>
      deriv (fun α => gaussianQuadrant ρ α (v (ρ * x + √(1 - ρ ^ 2) * z))) (u x)
    have hG_deriv : ∀ x, HasDerivAt G
        (deriv (fun α => deriv (fun α =>
            gaussianQuadrant ρ α (v (ρ * x + √(1 - ρ ^ 2) * z))) α) (u x) *
            deriv u x +
          ρ * deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (u x))
              (v (ρ * x + √(1 - ρ ^ 2) * z)) * deriv v (ρ * x + √(1 - ρ ^ 2) * z)) x := by
      intro x
      set y := ρ * x + √(1 - ρ ^ 2) * z
      have hy_d : HasDerivAt (fun x' => ρ * x' + √(1 - ρ ^ 2) * z) ρ x := by
        simpa using ((hasDerivAt_id x).const_mul ρ).add_const (√(1 - ρ ^ 2) * z)
      have hpair : HasDerivAt (fun x' => (u x', v (ρ * x' + √(1 - ρ ^ 2) * z)))
          (deriv u x, deriv v y * ρ) x :=
        (hu_d1 x).hasDerivAt.prodMk (((hv_d1 y).hasDerivAt).comp x hy_d)
      have hf := (hasFDerivAt_deriv_gaussianQuadrant_left hρ (hu_oo x) (hv_oo y)).comp_hasDerivAt x
        hpair
      refine hf.congr_deriv ?_
      simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        smul_eq_mul,
        (hasDerivAt_gaussianQuadrant_left_left hρ (hu_oo x) (hv_oo y)).deriv,
        (hasDerivAt_gaussianQuadrant_left_right hρ (hu_oo x) (hv_oo y)).deriv]
      ring
    have hGm : Measurable G :=
      hL_cont.measurable.comp
        (by fun_prop : Measurable fun x : ℝ => (x, ρ * x + √(1 - ρ ^ 2) * z))
    have h1 : Integrable (fun x => deriv u x * G x) (gaussianReal 0 1) :=
      Integrable.of_bound (hu_d2.continuous.measurable.mul hGm).aestronglyMeasurable Cu
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_mul]
          exact (mul_le_of_le_one_right (abs_nonneg _) (hL_bdd x _)).trans (hCu x))
    have h2 : Integrable (fun x => x * deriv u x * G x) (gaussianReal 0 1) :=
      (((memLp_id_gaussianReal 1).integrable le_rfl).abs.mul_const Cu).mono'
        (((measurable_id.mul hu_d2.continuous.measurable).mul hGm).aestronglyMeasurable)
        (ae_of_all _ fun x => by
          simp only [Real.norm_eq_abs, abs_mul]
          exact (mul_le_of_le_one_right (by positivity) (hL_bdd x _)).trans
            (mul_le_mul_of_nonneg_left (hCu x) (abs_nonneg _)))
    have h3 : Integrable (fun x => deriv (deriv u) x * G x) (gaussianReal 0 1) :=
      Integrable.of_bound ((measurable_deriv (deriv u)).mul hGm).aestronglyMeasurable Cu
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_mul]
          exact (mul_le_of_le_one_right (abs_nonneg _) (hL_bdd x _)).trans (hCu2 x))
    have h4 : Integrable (fun x => deriv u x * deriv G x) (gaussianReal 0 1) :=
      Integrable.of_bound
        (hu_d2.continuous.measurable.mul (measurable_deriv G)).aestronglyMeasurable
        (Cu * (M1 * Cu + ρ * M2 * Cv)) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_mul, (hG_deriv x).deriv]
          have h1' : |deriv (fun α => deriv (fun α => gaussianQuadrant ρ α
              (v (ρ * x + √(1 - ρ ^ 2) * z))) α) (u x)| ≤ M1 :=
            hM1 (u x, v _) ⟨hu_mem _, hv_mem _⟩
          have h2' : |deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (u x))
              (v (ρ * x + √(1 - ρ ^ 2) * z))| ≤ M2 :=
            hM2 (u x, v _) ⟨hu_mem _, hv_mem _⟩
          refine mul_le_mul (hCu x) ((abs_add_le _ _).trans (add_le_add ?_ ?_))
            (abs_nonneg _) hCu_nn
          · rw [abs_mul]; exact mul_le_mul h1' (hCu x) (abs_nonneg _) hM1_nn
          · rw [abs_mul, abs_mul, abs_of_pos hρ0]
            exact mul_le_mul (mul_le_mul_of_nonneg_left h2' hρ0.le) (hCv _) (abs_nonneg _)
              (by positivity))
    have hibp := integral_mul_deriv_sub_deriv_deriv_mul_gaussianReal hu_d2
      (fun x => (hG_deriv x).differentiableAt) h1 h2 h3 h4
    refine hibp.trans (integral_congr_ae (ae_of_all _ fun x => ?_))
    dsimp only [mapρ]
    rw [(hG_deriv x).deriv]; ring
  · exact (((hL1_cont_all.measurable.mul
      ((hu_d2.continuous.measurable.comp measurable_fst).pow_const 2)).add
      (((measurable_const.mul hL2_cont_all.measurable).mul
        (hu_d2.continuous.measurable.comp measurable_fst)).mul
        ((measurable_deriv v).comp measurable_snd)))).aestronglyMeasurable
  · exact (((measurable_fst.mul (hu_d2.continuous.measurable.comp measurable_fst)).sub
      ((measurable_deriv (deriv u)).comp measurable_fst)).mul
      hL_cont.measurable).aestronglyMeasurable

end CslibFrontier.Probability.Gaussian
