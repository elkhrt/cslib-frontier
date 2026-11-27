/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import CslibFrontier.Foundations.Probability.Gaussian.Quadrant

import CslibFrontier.Foundations.Probability.Gaussian.QuadrantDeriv
import CslibFrontier.Foundations.Probability.Gaussian.QuadrantMono
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.Gaussian.Slepian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Bivariate Normal Tail Bounds (Willink and KKMO Estimates)

This module proves bivariate standard normal tail inequalities for the Gaussian quadrant probability
`ProbabilityTheory.gaussianQuadrant` (`Λ_ρ`) and the upper-quadrant probability
`L(h, k, ρ) = P[X ≥ h, Y ≥ k]` under standard Lean axioms:

1. Exact symmetry/inclusion-exclusion transform `L(h, k, ρ) = 1 - Φ(h) - Φ(k) + Φ(h, k, ρ)`
.
2. Classical Mills ratio lower and upper bounds and monotonicity of `t ↦ t * Φ(-t) / φ(t)` on
   `(0, ∞)`.
3. Willink's bivariate normal upper bound `L(h, h, ρ) ≤ Φ(-h) * Φ(-θ * h) * (1 + ρ)` for `h > 0`,
   `0 ≤ ρ ≤ 1`, and `θ = √((1 - ρ) / (1 + ρ))`.
4. Uniform quadratic-plus-linear bound `Λ_ρ(μ) ≤ μ^2 + 3 * ρ` for `0 ≤ ρ ≤ 1` and `0 ≤ μ ≤ 1`.
5. Small-`μ` upper bound for `Λ_ρ(μ)` yielding the Khot–Kindler–Mossel–O'Donnell small-volume
   estimate as a corollary.

## Main definitions

* `CslibFrontier.Foundations.Probability.Gaussian.upperBivariateNormal`: the upper bivariate
  standard normal quadrant
  probability `L(h, k, ρ) = P[X ≥ h, Y ≥ k]`.
* `CslibFrontier.Foundations.Probability.Gaussian.willinkTheta`: the correlation parameter `θ = √((1
  - ρ) / (1 + ρ))`.

## Main results

* `CslibFrontier.Foundations.Probability.Gaussian.upperBivariateNormal_eq_gaussianQuadrant_neg`:
  `L(h, k, ρ) = Λ_ρ(Φ(-h), Φ(-k))`.
* `CslibFrontier.Foundations.Probability.Gaussian.upperBivariateNormal_transform`:
  `L(h, k, ρ) = 1 - Φ(h) - Φ(k) + Λ_ρ(Φ(h), Φ(k))`.
* `CslibFrontier.Foundations.Probability.Gaussian.willink_upperBivariateNormal_le`:
  `L(h, h, ρ) ≤ Φ(-h) * Φ(-θ * h) * (1 + ρ)`.
* `CslibFrontier.Foundations.Probability.Gaussian.gaussianQuadrant_le_sq_add_three_mul`:
  `Λ_ρ(μ) ≤ μ^2 + 3 * ρ` for `0 ≤ ρ ≤ 1` and `0 ≤ μ ≤ 1`.
* `CslibFrontier.Foundations.Probability.Gaussian.gaussianQuadrant_small_mu_le`: sharp small-`μ`
  upper bound from Willink's
  inequality.
* `CslibFrontier.Foundations.Probability.Gaussian.kkmo_gaussianQuadrant_estimate`: small-`μ`
  estimate for
  `0 < ρ ≤ 1 / (log (1 / μ))^3`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal Topology

namespace CslibFrontier.Foundations.Probability.Gaussian

local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

/-! ### Upper bivariate normal probability and exact transform -/

/-- The upper-quadrant probability `L(h, k, ρ) = P[X ≥ h, Y ≥ k]` for a `ρ`-correlated pair
`(X, Y)` of standard normal random variables. -/
noncomputable def upperBivariateNormal (ρ h k : ℝ) : ℝ :=
  (correlatedGaussian ρ).real {p | h ≤ p.1 ∧ k ≤ p.2}

/-- The correlation parameter `θ(ρ) = √((1 - ρ) / (1 + ρ))` appearing in Willink's bivariate
normal bound. -/
noncomputable def willinkTheta (ρ : ℝ) : ℝ :=
  √((1 - ρ) / (1 + ρ))

/-- Nonnegativity of `upperBivariateNormal`. -/
theorem upperBivariateNormal_nonneg (ρ h k : ℝ) : 0 ≤ upperBivariateNormal ρ h k :=
  measureReal_nonneg

/-- `upperBivariateNormal` is at most `1`. -/
theorem upperBivariateNormal_le_one (ρ h k : ℝ) : upperBivariateNormal ρ h k ≤ 1 :=
  measureReal_le_one

/-- Symmetry of `(X, Y) ↦ (-X, -Y)` identifies `L(h, k, ρ)` with `Λ_ρ(Φ(-h), Φ(-k))`. -/
theorem upperBivariateNormal_eq_gaussianQuadrant_neg {ρ : ℝ} (hρ : |ρ| ≤ 1) (h k : ℝ) :
    upperBivariateNormal ρ h k = gaussianQuadrant ρ (Φ (-h)) (Φ (-k)) := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | h ≤ p.1 ∧ k ≤ p.2} :=
    (measurableSet_Ici.preimage measurable_fst).inter
      (measurableSet_Ici.preimage measurable_snd)
  rw [upperBivariateNormal, ← correlatedGaussian_map_neg hρ,
    map_measureReal_apply measurable_neg hmeas, gaussianQuadrant_cdf_cdf]
  congr 1
  ext p
  simp only [mem_preimage, mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg, le_neg]

/-- **Willink, Equation (1.1)**: inclusion-exclusion identity relating the upper and lower
quadrant probabilities of a `ρ`-correlated standard normal pair:
`L(h, k, ρ) = 1 - Φ(h) - Φ(k) + Λ_ρ(Φ(h), Φ(k))`.
-/
theorem upperBivariateNormal_transform {ρ : ℝ} (hρ : |ρ| ≤ 1) (h k : ℝ) :
    upperBivariateNormal ρ h k =
      1 - Φ h - Φ k + gaussianQuadrant ρ (Φ h) (Φ k) := by
  rw [upperBivariateNormal_eq_gaussianQuadrant_neg hρ,
    cdf_gaussianReal_neg one_ne_zero, cdf_gaussianReal_neg one_ne_zero,
    gaussianQuadrant_one_sub_one_sub hρ (cdf_nonneg _ _) (cdf_le_one _ _)
      (cdf_nonneg _ _) (cdf_le_one _ _)]

/-- Diagonal specialization: `Λ_ρ(1 - μ) = 1 - 2 μ + Λ_ρ(μ)` for `μ ∈ [0, 1]`. -/
theorem gaussianQuadrant_diag_one_sub {ρ : ℝ} (hρ : |ρ| ≤ 1) {μ : ℝ}
    (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    gaussianQuadrant ρ (1 - μ) (1 - μ) = 1 - 2 * μ + gaussianQuadrant ρ μ μ := by
  linarith [gaussianQuadrant_one_sub_one_sub hρ h0 h1 h0 h1]

/-! ### Mills ratio bounds and monotonicity -/

private theorem hasDerivAt_stdGaussianPDF (t : ℝ) : HasDerivAt φ (-t * φ t) t := by
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2 / 2)) (-t) t := by
    have hsq := hasDerivAt_pow 2 t
    convert (hsq.div_const 2).fun_neg using 1
    ring
  have h2 : HasDerivAt (fun x : ℝ => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)))
      ((√(2 * π))⁻¹ * (Real.exp (-(t ^ 2 / 2)) * (-t))) t :=
    (h1.exp).const_mul _
  have heq : (fun x : ℝ => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2))) = φ := by
    ext x
    simp [gaussianPDFReal_def, neg_div]
  rw [heq] at h2
  convert h2 using 1
  simp only [gaussianPDFReal_def, neg_div, NNReal.coe_one, mul_one, sub_zero]
  ring

private theorem stdGaussianPDF_neg (t : ℝ) : φ (-t) = φ t := by
  simp [gaussianPDFReal_def]

private theorem hasDerivAt_cdf_neg (t : ℝ) : HasDerivAt (fun x => Φ (-x)) (-φ t) t := by
  have h1 := (hasDerivAt_cdf_gaussianReal 0 one_ne_zero (-t)).comp t (hasDerivAt_neg t)
  change HasDerivAt (fun x => Φ (-x)) (φ (-t) * -1) t at h1
  simpa [stdGaussianPDF_neg] using h1

/-- Standard Mills ratio lower bound: `(h / (h^2 + 1)) * φ(h) ≤ Φ(-h)` for all `h : ℝ`. -/
theorem millsRatio_lower (h : ℝ) : h / (h ^ 2 + 1) * φ h ≤ Φ (-h) := by
  rw [cdf_gaussianReal_neg one_ne_zero]
  exact div_sq_add_one_mul_gaussianPDFReal_le h

/-- Standard Mills ratio upper bound: `Φ(-h) ≤ φ(h) / h` for all `h > 0`. -/
theorem millsRatio_upper {h : ℝ} (hh : 0 < h) : Φ (-h) ≤ φ h / h := by
  let g : ℝ → ℝ := fun t => φ t / t - Φ (-t)
  have hg_deriv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g (-(φ t / t ^ 2)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hdiv := (hasDerivAt_stdGaussianPDF t).fun_div (hasDerivAt_id' t) ht0
    convert hdiv.fun_sub (hasDerivAt_cdf_neg t) using 1
    field_simp [ht0]
    ring
  have hg_anti : AntitoneOn g (Ioi 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (fun t ht => (hg_deriv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hg_deriv t (interior_subset ht)).deriv]
        exact neg_nonpos.mpr (div_nonneg (gaussianPDFReal_nonneg _ _ _) (sq_nonneg _)))
  have hlim_zero : Tendsto g atTop (𝓝 0) := by
    have hΦ_tend : Tendsto (fun t => Φ (-t)) atTop (𝓝 0) :=
      (tendsto_cdf_atBot (gaussianReal 0 1)).comp tendsto_neg_atTop_atBot
    have hφ_bdd : ∀ t : ℝ, 0 ≤ φ t ∧ φ t ≤ (√(2 * π))⁻¹ := fun t =>
      ⟨gaussianPDFReal_nonneg _ _ _, by simpa using gaussianPDFReal_le 0 1 t⟩
    have hdiv_tend : Tendsto (fun t => φ t / t) atTop (𝓝 0) :=
      squeeze_zero' (eventually_of_mem (Ioi_mem_atTop 0) fun t ht =>
          div_nonneg (hφ_bdd t).1 (le_of_lt ht))
        (eventually_of_mem (Ioi_mem_atTop 0) fun t ht =>
          div_le_div_of_nonneg_right (hφ_bdd t).2 (le_of_lt ht))
        (tendsto_const_nhds.div_atTop tendsto_id)
    simpa using hdiv_tend.sub hΦ_tend
  have hge : 0 ≤ g h := by
    refine le_of_tendsto hlim_zero ?_
    filter_upwards [Ici_mem_atTop h] with t ht
    exact hg_anti (mem_Ioi.mpr hh) (mem_Ioi.mpr (hh.trans_le ht)) ht
  dsimp only [g] at hge
  linarith

/-- On `(0, ∞)`, the normalized Mills ratio `t ↦ t * Φ(-t) / φ(t)` equals
`∫ s in Ioi 0, exp (-s - s^2 / (2 * t^2))`. -/
private theorem mul_millsRatio_eq_integral {t : ℝ} (ht : 0 < t) :
    t * Φ (-t) / φ t = ∫ s in Ioi (0 : ℝ), Real.exp (-s - s ^ 2 / (2 * t ^ 2)) := by
  have hΦ_eq : Φ (-t) = ∫ y in Ioi t, φ y := by
    rw [cdf_gaussianReal_eq_integral 0 one_ne_zero, ← integral_comp_neg_Ioi t φ]
    simp only [stdGaussianPDF_neg]
  have hratio : ∀ y : ℝ, φ y / φ t = Real.exp ((t ^ 2 - y ^ 2) / 2) := by
    intro y
    simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
    have hsqrt : (√(2 * π))⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    rw [mul_div_mul_left _ _ hsqrt, ← Real.exp_sub]
    congr 1
    ring
  calc
    t * Φ (-t) / φ t
        = ∫ y in Ioi t, t * (φ y / φ t) := by
          rw [hΦ_eq, ← integral_const_mul, ← integral_div]
          refine setIntegral_congr_fun measurableSet_Ioi fun y _ => by ring
    _ = ∫ y in Ioi t, t * Real.exp ((t ^ 2 - y ^ 2) / 2) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun y _ => by rw [hratio]
    _ = ∫ u in Ioi (0 : ℝ), t * Real.exp ((t ^ 2 - (u + t) ^ 2) / 2) := by
          rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
            ← integral_add_right_eq_self
              (fun y => (Ioi t).indicator (fun y => t * Real.exp ((t ^ 2 - y ^ 2) / 2)) y) t]
          congr 1
          ext u
          by_cases hu : 0 < u <;> simp [Set.indicator, Set.mem_Ioi, hu]
    _ = ∫ s in Ioi (0 : ℝ), Real.exp (-s - s ^ 2 / (2 * t ^ 2)) := by
          have h := integral_comp_mul_left_Ioi
            (fun u => Real.exp ((t ^ 2 - (u + t) ^ 2) / 2)) (0 : ℝ) (inv_pos.mpr ht)
          rw [mul_zero, inv_inv, smul_eq_mul, ← integral_const_mul] at h
          rw [← h]
          refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
          have h1 : (t ^ 2 - (t⁻¹ * s + t) ^ 2) / 2 = -s - s ^ 2 / (2 * t ^ 2) := by
            field_simp [ht.ne']
            ring
          rw [h1]

private theorem integrableOn_exp_neg_sub_sq (t : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-s - s ^ 2 / (2 * t ^ 2))) (Ioi 0) := by
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi (0 : ℝ)) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  refine hint.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s _
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (sub_le_self _ (by positivity))

/-- Monotonicity of `t ↦ t * Φ(-t) / φ(t)` on `(0, ∞)`. -/
theorem monotoneOn_mul_millsRatio : MonotoneOn (fun t => t * Φ (-t) / φ t) (Ioi 0) := by
  intro t₁ ht₁ t₂ ht₂ h12
  dsimp only
  have ht₁' : 0 < t₁ := mem_Ioi.mp ht₁
  have ht₂' : 0 < t₂ := mem_Ioi.mp ht₂
  rw [mul_millsRatio_eq_integral ht₁', mul_millsRatio_eq_integral ht₂']
  refine setIntegral_mono_on (integrableOn_exp_neg_sub_sq t₁) (integrableOn_exp_neg_sub_sq t₂)
    measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 ≤ s := le_of_lt (mem_Ioi.mp hs)
  refine Real.exp_le_exp.mpr (sub_le_sub_left ?_ (-s))
  exact div_le_div_of_nonneg_left (sq_nonneg s) (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht₁'.le h12 2) (by norm_num))

/-! ### Willink's bivariate normal upper bound -/

/-- **Willink, Equation (1.2)**: for `h > 0` and `0 ≤ ρ ≤ 1`,
`L(h, h, ρ) ≤ Φ(-h) * Φ(-θ * h) * (1 + ρ)` where `θ = √((1 - ρ) / (1 + ρ))`.
-/
theorem willink_upperBivariateNormal_le {h ρ : ℝ} (hh : 0 < h) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    upperBivariateNormal ρ h h ≤ Φ (-h) * Φ (-(willinkTheta ρ * h)) * (1 + ρ) := by
  have habs : |ρ| ≤ 1 := abs_le.mpr ⟨by linarith, hρ1⟩
  rw [upperBivariateNormal_eq_gaussianQuadrant_neg habs]
  rcases eq_or_lt_of_le hρ1 with rfl | hρ_lt
  · simp only [willinkTheta, sub_self, zero_div, sqrt_zero, zero_mul, neg_zero,
      gaussianQuadrant_one (cdf_nonneg _ _) (cdf_le_one _ _) (cdf_nonneg _ _), min_self,
      cdf_gaussianReal_zero_zero one_ne_zero]
    linarith
  have hρ_abs_lt : |ρ| < 1 := abs_lt.mpr ⟨by linarith, hρ_lt⟩
  have h1p : 0 < 1 + ρ := by linarith
  have h1m : 0 < 1 - ρ := by linarith
  have hθ_pos : 0 < willinkTheta ρ := sqrt_pos.mpr (div_pos h1m h1p)
  have hθ_le : willinkTheta ρ ≤ 1 := by
    rw [willinkTheta, sqrt_le_one]
    exact (div_le_one h1p).mpr (by linarith)
  have hθ_sq : willinkTheta ρ ^ 2 = (1 - ρ) / (1 + ρ) :=
    sq_sqrt (div_nonneg h1m.le h1p.le)
  have hsqrt_eq : (1 - ρ) / √(1 - ρ ^ 2) = willinkTheta ρ := by
    have hfac : 1 - ρ ^ 2 = (1 - ρ) * (1 + ρ) := by ring
    rw [hfac, sqrt_mul h1m.le, willinkTheta, sqrt_div h1m.le]
    have hs1 : √(1 - ρ) ≠ 0 := (sqrt_pos.mpr h1m).ne'
    have hs2 : √(1 + ρ) ≠ 0 := (sqrt_pos.mpr h1p).ne'
    field_simp [hs1, hs2]
    rw [sq_sqrt h1m.le]
  let D : ℝ → ℝ := fun t =>
    Φ (-t) * Φ (-(willinkTheta ρ * t)) * (1 + ρ) -
      (correlatedGaussian ρ).real {p | p.1 ≤ -t ∧ p.2 ≤ -t}
  have hD_deriv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt D
        ((1 + ρ) * willinkTheta ρ *
          (willinkTheta ρ * φ t * Φ (-(willinkTheta ρ * t)) -
            Φ (-t) * φ (willinkTheta ρ * t))) t := by
    intro t _
    have hL : HasDerivAt (fun x => (correlatedGaussian ρ).real {p | p.1 ≤ -x ∧ p.2 ≤ -x})
        (-2 * φ t * Φ (-(willinkTheta ρ * t))) t := by
      have hdiag : HasDerivAt
          (fun u => (correlatedGaussian ρ).real {p | p.1 ≤ u ∧ p.2 ≤ u})
          (2 * φ (-t) * Φ ((-t - ρ * -t) / √(1 - ρ ^ 2))) (-t) := by
        have hΦ_mem : Φ (-t) ∈ Ioo (0 : ℝ) 1 :=
          ⟨cdf_pos (gaussianReal_absolutelyContinuous' 0 one_ne_zero) (-t),
            cdf_lt_one (gaussianReal_absolutelyContinuous' 0 one_ne_zero) (-t)⟩
        have hq := hasFDerivAt_gaussianQuadrant hρ_abs_lt hΦ_mem hΦ_mem
        have hpair : HasDerivAt (fun u : ℝ => (Φ u, Φ u)) (φ (-t), φ (-t)) (-t) :=
          (hasDerivAt_cdf_gaussianReal 0 one_ne_zero (-t)).prodMk
            (hasDerivAt_cdf_gaussianReal 0 one_ne_zero (-t))
        have hcomp := hq.comp_hasDerivAt (-t) hpair
        have heq : (Function.uncurry (gaussianQuadrant ρ) ∘ fun u => (Φ u, Φ u)) =
            (fun u => (correlatedGaussian ρ).real {p | p.1 ≤ u ∧ p.2 ≤ u}) := by
          ext u
          exact gaussianQuadrant_cdf_cdf ρ u u
        rw [heq] at hcomp
        convert hcomp using 1
        simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', gaussianQuantile_cdf, smul_eq_mul]
        ring
      have hcomp := hdiag.comp t (hasDerivAt_neg t)
      have harg : (-t - ρ * -t) / √(1 - ρ ^ 2) = -(willinkTheta ρ * t) := by
        rw [← hsqrt_eq]
        ring
      have hcomp' : HasDerivAt (fun x => (correlatedGaussian ρ).real {p | p.1 ≤ -x ∧ p.2 ≤ -x})
          (2 * φ (-t) * Φ ((-t - ρ * -t) / √(1 - ρ ^ 2)) * -1) t := hcomp
      convert hcomp' using 1
      rw [stdGaussianPDF_neg, harg]
      ring
    have hΦ1 : HasDerivAt (fun x => Φ (-x)) (-φ t) t := hasDerivAt_cdf_neg t
    have hΦ2 : HasDerivAt (fun x => Φ (-(willinkTheta ρ * x)))
        (-(willinkTheta ρ * φ (willinkTheta ρ * t))) t := by
      have hlin : HasDerivAt (fun x => -(willinkTheta ρ * x)) (-willinkTheta ρ) t := by
        simpa using ((hasDerivAt_id t).const_mul (willinkTheta ρ)).fun_neg
      have hc := (hasDerivAt_cdf_gaussianReal 0 one_ne_zero (-(willinkTheta ρ * t))).comp t hlin
      change HasDerivAt (fun x => Φ (-(willinkTheta ρ * x))) _ t at hc
      convert hc using 1
      rw [stdGaussianPDF_neg]
      ring
    have hprod := (hΦ1.fun_mul hΦ2).mul_const (1 + ρ)
    convert hprod.fun_sub hL using 1
    have h1m_eq : 1 - ρ = (1 + ρ) * willinkTheta ρ ^ 2 := by
      rw [hθ_sq]
      field_simp [h1p.ne']
    calc
      (1 + ρ) * willinkTheta ρ *
          (willinkTheta ρ * φ t * Φ (-(willinkTheta ρ * t)) - Φ (-t) * φ (willinkTheta ρ * t))
          = (1 + ρ) * willinkTheta ρ ^ 2 * φ t * Φ (-(willinkTheta ρ * t)) -
              (1 + ρ) * willinkTheta ρ * Φ (-t) * φ (willinkTheta ρ * t) := by ring
      _ = (1 - ρ) * φ t * Φ (-(willinkTheta ρ * t)) -
            (1 + ρ) * willinkTheta ρ * Φ (-t) * φ (willinkTheta ρ * t) := by rw [← h1m_eq]
      _ = (-φ t * Φ (-(willinkTheta ρ * t)) +
            Φ (-t) * -(willinkTheta ρ * φ (willinkTheta ρ * t))) * (1 + ρ) -
            -2 * φ t * Φ (-(willinkTheta ρ * t)) := by ring
  have hD_anti : AntitoneOn D (Ioi 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (fun t ht => (hD_deriv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hD_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        have ht0 : 0 < t := mem_Ioi.mp (interior_subset ht)
        rw [(hD_deriv t (interior_subset ht)).deriv]
        have hmono := monotoneOn_mul_millsRatio (mem_Ioi.mpr (mul_pos hθ_pos ht0))
          (mem_Ioi.mpr ht0) (mul_le_of_le_one_left ht0.le hθ_le)
        dsimp only at hmono
        have hφ1 : 0 < φ (willinkTheta ρ * t) := gaussianPDFReal_pos 0 1 _ one_ne_zero
        have hφ2 : 0 < φ t := gaussianPDFReal_pos 0 1 _ one_ne_zero
        rw [div_le_div_iff₀ hφ1 hφ2] at hmono
        have hsub : willinkTheta ρ * φ t * Φ (-(willinkTheta ρ * t)) -
            Φ (-t) * φ (willinkTheta ρ * t) ≤ 0 := by
          have : willinkTheta ρ * t * Φ (-(willinkTheta ρ * t)) * φ t ≤
              t * Φ (-t) * φ (willinkTheta ρ * t) := hmono
          nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hsub)
  have hD_tend : Tendsto D atTop (𝓝 0) := by
    have hΦ_tend : Tendsto (fun t => Φ (-t)) atTop (𝓝 0) :=
      (tendsto_cdf_atBot (gaussianReal 0 1)).comp tendsto_neg_atTop_atBot
    have hΦθ_tend : Tendsto (fun t => Φ (-(willinkTheta ρ * t))) atTop (𝓝 0) :=
      (tendsto_cdf_atBot (gaussianReal 0 1)).comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hθ_pos))
    have hprod_tend : Tendsto (fun t => Φ (-t) * Φ (-(willinkTheta ρ * t)) * (1 + ρ))
        atTop (𝓝 0) := by
      simpa using (hΦ_tend.mul hΦθ_tend).mul_const (1 + ρ)
    have hQ_tend : Tendsto (fun t => (correlatedGaussian ρ).real {p | p.1 ≤ -t ∧ p.2 ≤ -t})
        atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => measureReal_nonneg) (fun t => ?_) hΦ_tend
      rw [← gaussianQuadrant_cdf_cdf]
      exact (gaussianQuadrant_le_min habs (cdf_nonneg _ _) (cdf_le_one _ _)
        (cdf_nonneg _ _) (cdf_le_one _ _)).trans (min_le_left _ _)
    simpa using hprod_tend.sub hQ_tend
  have hge : 0 ≤ D h := by
    refine le_of_tendsto hD_tend ?_
    filter_upwards [Ici_mem_atTop h] with t ht
    exact hD_anti (mem_Ioi.mpr hh) (mem_Ioi.mpr (hh.trans_le ht)) ht
  dsimp only [D] at hge
  rw [gaussianQuadrant_cdf_cdf]
  linarith

/-! ### Uniform and small-volume bounds on `gaussianQuadrant` -/

/-- Auxiliary bound `1 - ρ ≤ θ(ρ)` for `0 ≤ ρ ≤ 1`. -/
private theorem one_sub_le_willinkTheta {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    1 - ρ ≤ willinkTheta ρ := by
  rw [willinkTheta]
  refine le_sqrt_of_sq_le ?_
  rw [le_div_iff₀ (by linarith : 0 < 1 + ρ)]
  nlinarith [sq_nonneg ρ]

/-- Uniform quadratic-plus-linear upper bound: for `0 ≤ ρ ≤ 1` and `0 ≤ μ ≤ 1`,
`Λ_ρ(μ) ≤ μ^2 + 3 * ρ`. -/
theorem gaussianQuadrant_le_sq_add_three_mul {ρ μ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    gaussianQuadrant ρ μ μ ≤ μ ^ 2 + 3 * ρ := by
  have habs : |ρ| ≤ 1 := abs_le.mpr ⟨by linarith, hρ1⟩
  have hlt_half : ∀ {m : ℝ}, 0 < m → m < 1 / 2 → gaussianQuadrant ρ m m ≤ m ^ 2 + 3 * ρ := by
    intro m hm0 hm1
    have hmem : m ∈ Ioo (0 : ℝ) 1 := ⟨hm0, by linarith⟩
    set u := gaussianQuantile m
    have hΦu : Φ u = m := cdf_gaussianQuantile hmem
    have hu_neg : u < 0 := by
      have h0 : gaussianQuantile m < gaussianQuantile (2⁻¹ : ℝ) :=
        strictMonoOn_gaussianQuantile hmem ⟨by norm_num, by norm_num⟩ (by linarith)
      rwa [gaussianQuantile_half] at h0
    have hh_pos : 0 < -u := neg_pos.mpr hu_neg
    have hwil := willink_upperBivariateNormal_le hh_pos hρ0 hρ1
    rw [upperBivariateNormal_eq_gaussianQuadrant_neg habs, neg_neg, hΦu] at hwil
    have hφ_le_one : φ (-u) ≤ 1 := by
      have h1 := gaussianPDFReal_le 0 1 (-u)
      have hpi : (1 : ℝ) ≤ √(2 * π) := by
        rw [one_le_sqrt]
        linarith [Real.pi_gt_three]
      exact h1.trans (by simpa using inv_le_one_of_one_le₀ hpi)
    have hneg_u_le : -u ≤ 1 / m := by
      have hmills := millsRatio_upper hh_pos
      rw [neg_neg, hΦu] at hmills
      have hm_le : m ≤ 1 / (-u) := hmills.trans (div_le_div_of_nonneg_right hφ_le_one hh_pos.le)
      rw [le_div_iff₀ hm0]
      rw [le_div_iff₀ hh_pos] at hm_le
      linarith
    have hθ_ge : 1 - ρ ≤ willinkTheta ρ := one_sub_le_willinkTheta hρ0 hρ1
    have hθ_le : willinkTheta ρ ≤ 1 := by
      rw [willinkTheta, sqrt_le_one]
      exact (div_le_one (by linarith : 0 < 1 + ρ)).mpr (by linarith)
    have hΦθ : Φ (-(willinkTheta ρ * -u)) ≤ m + (1 - willinkTheta ρ) / m := by
      have hanti := gaussianReal_real_Iic_add_le 0 u one_ne_zero
        (ε := (1 - willinkTheta ρ) * (-u)) (mul_nonneg (by linarith) hh_pos.le)
      have heq_arg : u + (1 - willinkTheta ρ) * (-u) = -(willinkTheta ρ * -u) := by ring
      rw [heq_arg, ← cdf_eq_real, ← cdf_eq_real, hΦu] at hanti
      have hpi : (1 : ℝ) ≤ √(2 * π * (1 : ℝ≥0)) := by
        rw [one_le_sqrt]
        simp only [NNReal.coe_one, mul_one]
        linarith [Real.pi_gt_three]
      have hstep : (1 - willinkTheta ρ) * (-u) / √(2 * π * (1 : ℝ≥0)) ≤
          (1 - willinkTheta ρ) / m := by
        calc
          (1 - willinkTheta ρ) * (-u) / √(2 * π * (1 : ℝ≥0))
              ≤ (1 - willinkTheta ρ) * (-u) :=
                div_le_self (mul_nonneg (by linarith) hh_pos.le) hpi
          _ ≤ (1 - willinkTheta ρ) * (1 / m) :=
                mul_le_mul_of_nonneg_left hneg_u_le (by linarith)
          _ = (1 - willinkTheta ρ) / m := by ring
      exact hanti.trans (by linarith)
    have hstep1 : gaussianQuadrant ρ m m ≤ (1 + ρ) * (m ^ 2 + ρ) := by
      calc
        gaussianQuadrant ρ m m
            ≤ m * Φ (-(willinkTheta ρ * -u)) * (1 + ρ) := hwil
        _ ≤ m * (m + (1 - willinkTheta ρ) / m) * (1 + ρ) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hΦθ hm0.le) (by linarith)
        _ = (1 + ρ) * (m ^ 2 + (1 - willinkTheta ρ)) := by
              field_simp [hm0.ne']
        _ ≤ (1 + ρ) * (m ^ 2 + ρ) := by
              exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hrem : 0 ≤ ρ * (2 - m ^ 2 - ρ) := mul_nonneg hρ0 (by nlinarith)
    nlinarith
  rcases eq_or_lt_of_le hμ0 with rfl | hμ_pos
  · rw [gaussianQuadrant_zero_left]
    nlinarith
  rcases eq_or_lt_of_le hμ1 with rfl | hμ_lt_one
  · rw [gaussianQuadrant_one_left habs zero_le_one le_rfl]
    nlinarith
  rcases lt_trichotomy μ (1 / 2) with hlt | rfl | hgt
  · exact hlt_half hμ_pos hlt
  · -- `μ = 1 / 2`: take limit from below by continuity
    have hcont := continuous_gaussianQuadrant habs
    have hlim : Tendsto (fun t : ℝ => gaussianQuadrant ρ t t) (𝓝[<] (1 / 2))
        (𝓝 (gaussianQuadrant ρ (1 / 2) (1 / 2))) :=
      (hcont.comp (continuous_id.prodMk continuous_id)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hlim_rhs : Tendsto (fun t : ℝ => t ^ 2 + 3 * ρ) (𝓝[<] (1 / 2))
        (𝓝 ((1 / 2 : ℝ) ^ 2 + 3 * ρ)) :=
      ((continuous_pow 2).add continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hlim hlim_rhs ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
    exact hlt_half ht.1 ht.2
  · rw [show μ = 1 - (1 - μ) by ring,
      gaussianQuadrant_diag_one_sub habs (by linarith) (by linarith)]
    have h := hlt_half (by linarith : 0 < 1 - μ) (by linarith : 1 - μ < 1 / 2)
    nlinarith

/-- Elementary exponential bound `exp u ≤ 1 + u + u^2` on `[0, 1/2]`. -/
private theorem exp_le_one_add_add_sq {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Real.exp u ≤ 1 + u + u ^ 2 := by
  have hexp_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h := Real.add_one_le_exp (-1 / 2 : ℝ)
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.exp_neg] at h
    have h' : (1 / 2 : ℝ) ≤ (Real.exp (1 / 2 : ℝ))⁻¹ := by linarith
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 1 / 2) hpos] at h'
    linarith [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
  let q : ℝ → ℝ := fun x => 1 + x + x ^ 2 - Real.exp x
  have hq_deriv : ∀ x : ℝ, HasDerivAt q (1 + 2 * x - Real.exp x) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => 1 + t + t ^ 2) (1 + 2 * x) x := by
      have hsq := hasDerivAt_pow 2 x
      simpa using ((hasDerivAt_const x (1 : ℝ)).fun_add (hasDerivAt_id x)).fun_add hsq
    exact h1.fun_sub (Real.hasDerivAt_exp x)
  have hq'_deriv : ∀ x : ℝ, HasDerivAt (fun t => 1 + 2 * t - Real.exp t) (2 - Real.exp x) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => 1 + 2 * t) 2 x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).fun_add ((hasDerivAt_id x).const_mul 2)
    exact h1.fun_sub (Real.hasDerivAt_exp x)
  have hq'_mono : MonotoneOn (fun t => 1 + 2 * t - Real.exp t) (Icc 0 (1 / 2)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
      (fun x _ => (hq'_deriv x).continuousAt.continuousWithinAt)
      (fun x _ => (hq'_deriv x).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [(hq'_deriv x).deriv]
        have hxle : x ≤ 1 / 2 := (interior_subset hx).2
        linarith [Real.exp_le_exp.mpr hxle])
  have hq_mono : MonotoneOn q (Icc 0 (1 / 2)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
      (fun x _ => (hq_deriv x).continuousAt.continuousWithinAt)
      (fun x _ => (hq_deriv x).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [(hq_deriv x).deriv]
        have h0 : (0 : ℝ) ∈ Icc 0 (1 / 2) := ⟨le_rfl, by norm_num⟩
        have h := hq'_mono h0 (interior_subset hx) (interior_subset hx).1
        simpa using h)
  have hq0 : q 0 = 0 := by simp [q]
  have hle := hq_mono ⟨le_rfl, by norm_num⟩ ⟨hu0, hu1⟩ hu0
  rw [hq0] at hle
  dsimp only [q] at hle
  linarith

/-- Auxiliary lower bound on the standard Gaussian tail at `3`: `exp (-10) ≤ Φ (-3)`. -/
private theorem exp_neg_ten_le_cdf_neg_three : Real.exp (-10) ≤ Φ (-3) := by
  have hm := millsRatio_lower 3
  have hpi : √(2 * π) ≤ 3 := by
    rw [sqrt_le_iff]
    exact ⟨by norm_num, by linarith [Real.pi_lt_four]⟩
  have hφ : (1 / 3 : ℝ) * Real.exp (-9 / 2) ≤ φ 3 := by
    simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
    have hinv : (1 / 3 : ℝ) ≤ (√(2 * π))⁻¹ := by
      rw [one_div]
      exact inv_anti₀ (by positivity) hpi
    have hexp : -(9 / 2 : ℝ) = -(3 ^ 2 / 2) := by norm_num
    rw [neg_div, neg_div, hexp]
    exact mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
  have h1 : (1 / 10 : ℝ) * Real.exp (-9 / 2) ≤ Φ (-3) := by
    have : (3 / (3 ^ 2 + 1 : ℝ)) * ((1 / 3 : ℝ) * Real.exp (-9 / 2)) =
        (1 / 10 : ℝ) * Real.exp (-9 / 2) := by ring
    nlinarith [hm, hφ]
  have h2 : Real.exp (-10) ≤ (1 / 10 : ℝ) * Real.exp (-9 / 2) := by
    have h11 : (10 : ℝ) ≤ Real.exp (11 / 2) := by
      have := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 2) 3
      simp [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    have hmul := mul_le_mul_of_nonneg_right h11 (Real.exp_pos (-10)).le
    rw [← Real.exp_add, show (11 / 2 : ℝ) + -10 = -9 / 2 by norm_num] at hmul
    linarith
  exact h2.trans h1

/-- Auxiliary bound: for `h ≥ 3`, `exp (-h^2) ≤ Φ (-h)`. -/
private theorem exp_neg_sq_le_cdf_neg {h : ℝ} (hh : 3 ≤ h) : Real.exp (-h ^ 2) ≤ Φ (-h) := by
  have hm := millsRatio_lower h
  have hpi : √(2 * π) ≤ 3 := by
    rw [sqrt_le_iff]
    exact ⟨by norm_num, by linarith [Real.pi_lt_four]⟩
  have hpos_h : 0 < h := by linarith
  have hexp_ge : 3 * (h ^ 2 + 1) / h ≤ Real.exp (h ^ 2 / 2) := by
    have htaylor := Real.sum_le_exp_of_nonneg (show 0 ≤ h ^ 2 / 2 by positivity) 3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
      Nat.factorial_two, Nat.cast_ofNat] at htaylor
    rw [div_le_iff₀ hpos_h]
    nlinarith [sq_nonneg (h - 3)]
  have hstep : Real.exp (-h ^ 2) ≤ h / (h ^ 2 + 1) * ((3 : ℝ)⁻¹ * Real.exp (-h ^ 2 / 2)) := by
    have hmul := mul_le_mul_of_nonneg_right hexp_ge (Real.exp_pos (-h ^ 2)).le
    rw [← Real.exp_add, show h ^ 2 / 2 + -h ^ 2 = -h ^ 2 / 2 by ring] at hmul
    have hmul' : 3 * (h ^ 2 + 1) * Real.exp (-h ^ 2) / h ≤ Real.exp (-h ^ 2 / 2) := by
      simpa [div_mul_eq_mul_div] using hmul
    have hdiv := (div_le_iff₀ hpos_h).mp hmul'
    have hden : 0 < 3 * (h ^ 2 + 1) := by positivity
    have hpos_d : 0 < h ^ 2 + 1 := by positivity
    have hrew : h / (h ^ 2 + 1) * ((3 : ℝ)⁻¹ * Real.exp (-h ^ 2 / 2)) =
        h * Real.exp (-h ^ 2 / 2) / (3 * (h ^ 2 + 1)) := by
      field_simp [hpos_d.ne']
    rw [hrew, le_div_iff₀ hden]
    linarith
  have hφ_ge : (3 : ℝ)⁻¹ * Real.exp (-h ^ 2 / 2) ≤ φ h := by
    simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
    have hinv : (3 : ℝ)⁻¹ ≤ (√(2 * π))⁻¹ := inv_anti₀ (by positivity) hpi
    rw [neg_div]
    exact mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
  exact hstep.trans ((mul_le_mul_of_nonneg_left hφ_ge (by positivity)).trans hm)

/-- Sharp small-volume upper bound from Willink's inequality: for `0 < μ ≤ exp (-10)`,
`0 < ρ < 1`, and `2 * ρ * log (1 / μ) ≤ 1 / 2`,
`Λ_ρ(μ) ≤ μ^2 * (1 + 2 * ρ * log (1 / μ) * (1 + 4 / log (1 / μ) + 2 * ρ * log (1 / μ)))`. -/
theorem gaussianQuadrant_small_mu_le {ρ μ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ Real.exp (-10))
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hprod : 2 * ρ * Real.log (1 / μ) ≤ 1 / 2) :
    gaussianQuadrant ρ μ μ ≤
      μ ^ 2 * (1 + 2 * ρ * Real.log (1 / μ) *
        (1 + 4 / Real.log (1 / μ) + 2 * ρ * Real.log (1 / μ))) := by
  have habs : |ρ| ≤ 1 := abs_le.mpr ⟨by linarith, hρ1.le⟩
  set L := Real.log (1 / μ)
  have hL_ge : 10 ≤ L := by
    have h1 : Real.log (Real.exp 10) ≤ Real.log (1 / μ) := by
      refine Real.log_le_log (by positivity) ?_
      rw [Real.exp_neg] at hμ1
      rw [one_div]
      exact (le_inv_comm₀ hμ0 (Real.exp_pos 10)).mp hμ1
    rw [Real.log_exp] at h1
    exact h1
  have hL_pos : 0 < L := by linarith
  have hρ_le : ρ ≤ 1 / (4 * L) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hρ_le_40 : ρ ≤ 1 / 40 :=
    hρ_le.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  have hμ_lt_half : μ < 1 / 2 := by
    have h1 : Real.exp (-10) < 1 / 2 := by
      rw [Real.exp_neg, one_div]
      have h2 : (2 : ℝ) < Real.exp 10 := by
        have := Real.add_one_lt_exp (by norm_num : (10 : ℝ) ≠ 0)
        linarith
      exact inv_strictAnti₀ (by norm_num) h2
    exact hμ1.trans_lt h1
  have hmem : μ ∈ Ioo (0 : ℝ) 1 := ⟨hμ0, by linarith⟩
  set h := -gaussianQuantile μ
  have hΦh : Φ (-h) = μ := by simp [h, cdf_gaussianQuantile hmem]
  have hh_ge_three : 3 ≤ h := by
    by_contra hlt
    push Not at hlt
    have hstrict := (strictMono_cdf_gaussianReal 0 one_ne_zero) (neg_lt_neg hlt)
    rw [hΦh] at hstrict
    linarith [exp_neg_ten_le_cdf_neg_three]
  have hh_pos : 0 < h := by linarith
  have hh_sq_le : h ^ 2 ≤ 2 * L := by
    have hm := millsRatio_upper hh_pos
    rw [hΦh] at hm
    have hφ_le : φ h / h ≤ Real.exp (-h ^ 2 / 2) := by
      simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
      have hpi : (1 : ℝ) ≤ √(2 * π) := by
        rw [one_le_sqrt]; linarith [Real.pi_gt_three]
      have h1 : (√(2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
      have h2 : (√(2 * π))⁻¹ * Real.exp (-(h ^ 2 / 2)) ≤ Real.exp (-(h ^ 2 / 2)) :=
        mul_le_of_le_one_left (Real.exp_pos _).le h1
      have h3 : (√(2 * π))⁻¹ * Real.exp (-(h ^ 2 / 2)) / h ≤
          (√(2 * π))⁻¹ * Real.exp (-(h ^ 2 / 2)) :=
        div_le_self (by positivity) (by linarith)
      simpa [neg_div] using h3.trans h2
    have hμ_le := hm.trans hφ_le
    have hlog := Real.log_le_log hμ0 hμ_le
    rw [Real.log_exp] at hlog
    have hL_eq : L = -Real.log μ := by simp [L, one_div, Real.log_inv]
    linarith
  have hh_sq_ge : L ≤ h ^ 2 := by
    have hle := (exp_neg_sq_le_cdf_neg hh_ge_three).trans_eq hΦh
    have hlog := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at hlog
    have hL_eq : L = -Real.log μ := by simp [L, one_div, Real.log_inv]
    linarith
  set θ := willinkTheta ρ
  have h1p : 0 < 1 + ρ := by linarith
  have h1m : 0 < 1 - ρ := by linarith
  have hθ_pos : 0 < θ := sqrt_pos.mpr (div_pos h1m h1p)
  have hθ_le : θ ≤ 1 := by
    rw [show θ = √((1 - ρ) / (1 + ρ)) from rfl, sqrt_le_one]
    exact (div_le_one h1p).mpr (by linarith)
  have hθ_sq : θ ^ 2 = (1 - ρ) / (1 + ρ) := sq_sqrt (div_nonneg h1m.le h1p.le)
  have hθ_inv_le : θ⁻¹ ≤ 1 + 2 * ρ := by
    rw [inv_le_iff_one_le_mul₀ hθ_pos]
    have hsq : 1 ≤ (1 + 2 * ρ) ^ 2 * θ ^ 2 := by
      rw [hθ_sq, ← mul_div_assoc, le_div_iff₀ h1p]
      have hcub : 0 ≤ ρ * (2 - 4 * ρ ^ 2) := mul_nonneg hρ0.le (by nlinarith)
      nlinarith
    have hpos_prod : 0 ≤ (1 + 2 * ρ) * θ := by positivity
    nlinarith [sq_nonneg ((1 + 2 * ρ) * θ - 1), hsq]
  -- Integral bound on `Φ(-θ h) - Φ(-h)`
  have hdiff : Φ (-(θ * h)) - Φ (-h) ≤
      ((1 + h ^ 2) / (θ * h ^ 2)) * (Real.exp (ρ / (1 + ρ) * h ^ 2) - 1) * μ := by
    have h1 : Φ (-(θ * h)) - Φ (-h) = ∫ y in (θ * h)..h, φ y := by
      have hneg : ∀ x : ℝ, Φ (-x) = 1 - Φ x := cdf_gaussianReal_neg one_ne_zero
      rw [hneg, hneg, show 1 - Φ (θ * h) - (1 - Φ h) = Φ h - Φ (θ * h) by ring]
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_cdf_gaussianReal 0 one_ne_zero x)
        ((continuous_gaussianPDFReal 0 1).intervalIntegrable _ _)).symm
    have h2 : ∫ y in (θ * h)..h, φ y ≤
        ∫ y in (θ * h)..h, (1 / (θ * h)) * (y * φ y) := by
      refine intervalIntegral.integral_mono_on (mul_le_of_le_one_left hh_pos.le hθ_le)
        ((continuous_gaussianPDFReal 0 1).intervalIntegrable _ _)
        (((continuous_id.mul (continuous_gaussianPDFReal 0 1)).const_mul _).intervalIntegrable _ _)
        fun y hy => ?_
      have hφ_nn : 0 ≤ φ y := gaussianPDFReal_nonneg 0 1 y
      have hy_ge : θ * h ≤ y := hy.1
      have hratio : 1 ≤ y / (θ * h) := (one_le_div (mul_pos hθ_pos hh_pos)).mpr hy_ge
      calc
        φ y = 1 * φ y := (one_mul _).symm
        _ ≤ (y / (θ * h)) * φ y := mul_le_mul_of_nonneg_right hratio hφ_nn
        _ = (1 / (θ * h)) * (y * φ y) := by ring
    have h3 : ∫ y in (θ * h)..h, (1 / (θ * h)) * (y * φ y) =
        (φ (θ * h) - φ h) / (θ * h) := by
      rw [intervalIntegral.integral_const_mul]
      have hanti : ∫ y in (θ * h)..h, y * φ y = (-φ h) - (-φ (θ * h)) := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => -φ x) (fun x _ => ?_)
          ((by fun_prop : Continuous fun y : ℝ => y * φ y).intervalIntegrable _ _)
        simpa using (hasDerivAt_stdGaussianPDF x).fun_neg
      rw [hanti]
      ring
    have h4 : φ (θ * h) - φ h = φ h * (Real.exp (ρ / (1 + ρ) * h ^ 2) - 1) := by
      simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
      have hmul_exp : Real.exp (-(h ^ 2 / 2)) * Real.exp (ρ / (1 + ρ) * h ^ 2) =
          Real.exp (-((θ * h) ^ 2 / 2)) := by
        rw [← Real.exp_add]
        congr 1
        rw [mul_pow, hθ_sq]
        field_simp [h1p.ne']
        ring
      simp only [neg_div] at hmul_exp ⊢
      rw [mul_sub, mul_one, mul_assoc, hmul_exp]
    have h5 : φ h / h ≤ ((1 + h ^ 2) / h ^ 2) * μ := by
      have hm := millsRatio_lower h
      rw [hΦh] at hm
      have hden : 0 < h ^ 2 + 1 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hm (div_nonneg hden.le (sq_nonneg h))
      have hcancel : (h ^ 2 + 1) / h ^ 2 * (h / (h ^ 2 + 1) * φ h) = φ h / h := by
        field_simp [hh_pos.ne', hden.ne']
      rw [hcancel] at hmul
      simpa [add_comm] using hmul
    have h6 : (φ (θ * h) - φ h) / (θ * h) =
        (θ⁻¹ * (φ h / h)) * (Real.exp (ρ / (1 + ρ) * h ^ 2) - 1) := by
      rw [h4]
      field_simp [hθ_pos.ne', hh_pos.ne']
    have hexp_nn : 0 ≤ Real.exp (ρ / (1 + ρ) * h ^ 2) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (by positivity))
    calc
      Φ (-(θ * h)) - Φ (-h) ≤ (φ (θ * h) - φ h) / (θ * h) := by
        rw [h1, ← h3]; exact h2
      _ = (θ⁻¹ * (φ h / h)) * (Real.exp (ρ / (1 + ρ) * h ^ 2) - 1) := h6
      _ ≤ (θ⁻¹ * (((1 + h ^ 2) / h ^ 2) * μ)) * (Real.exp (ρ / (1 + ρ) * h ^ 2) - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr hθ_pos.le)) hexp_nn
      _ = ((1 + h ^ 2) / (θ * h ^ 2)) * (Real.exp (ρ / (1 + ρ) * h ^ 2) - 1) * μ := by
        field_simp [hθ_pos.ne', hh_pos.ne']
  -- Combine with Willink's bound and simplify
  have hwil := willink_upperBivariateNormal_le hh_pos hρ0.le hρ1.le
  rw [upperBivariateNormal_eq_gaussianQuadrant_neg habs, hΦh] at hwil
  set u0 := 2 * ρ * L
  have hu0_pos : 0 < u0 := by positivity
  have hu : ρ / (1 + ρ) * h ^ 2 ≤ u0 := by
    have h1 : ρ / (1 + ρ) ≤ ρ := div_le_self hρ0.le (by linarith)
    calc
      ρ / (1 + ρ) * h ^ 2 ≤ ρ * h ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg h)
      _ ≤ ρ * (2 * L) := mul_le_mul_of_nonneg_left hh_sq_le hρ0.le
      _ = u0 := by ring
  have hexp_u : Real.exp (ρ / (1 + ρ) * h ^ 2) - 1 ≤ u0 * (1 + u0) := by
    have h1 := Real.exp_le_exp.mpr hu
    have h2 := exp_le_one_add_add_sq hu0_pos.le hprod
    nlinarith
  have hcoef : (1 + h ^ 2) / (θ * h ^ 2) ≤ (1 + 1 / L) * (1 + 2 * ρ) := by
    have h1 : (1 + h ^ 2) / h ^ 2 = 1 + 1 / h ^ 2 := by field_simp [hh_pos.ne']; ring
    have h2 : 1 / h ^ 2 ≤ 1 / L := one_div_le_one_div_of_le hL_pos hh_sq_ge
    rw [show (1 + h ^ 2) / (θ * h ^ 2) = θ⁻¹ * ((1 + h ^ 2) / h ^ 2) by
      field_simp [hθ_pos.ne', hh_pos.ne'], h1]
    calc
      θ⁻¹ * (1 + 1 / h ^ 2) ≤ (1 + 2 * ρ) * (1 + 1 / L) :=
        mul_le_mul hθ_inv_le (by linarith) (by positivity) (by positivity)
      _ = (1 + 1 / L) * (1 + 2 * ρ) := mul_comm _ _
  have hK : (1 + 1 / L) * (1 + 2 * ρ) * (1 + u0) ≤ 1 + 3 / L + u0 := by
    have h12 : (1 + 1 / L) * (1 + 2 * ρ) ≤ 1 + 2 / L := by
      have h2ρ : 2 * ρ ≤ 1 / (2 * L) := by
        have := mul_le_mul_of_nonneg_left hρ_le (by norm_num : (0 : ℝ) ≤ 2)
        have heq : 2 * (1 / (4 * L)) = 1 / (2 * L) := by field_simp [hL_pos.ne']; ring
        linarith
      have hL2 : 1 / (2 * L ^ 2) ≤ 1 / (2 * L) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith
      have hprod1 : (1 + 1 / L) * (1 + 2 * ρ) ≤ (1 + 1 / L) * (1 + 1 / (2 * L)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hexp1 : (1 + 1 / L) * (1 + 1 / (2 * L)) = 1 + 3 / (2 * L) + 1 / (2 * L ^ 2) := by
        field_simp [hL_pos.ne']; ring
      have h32 : 3 / (2 * L) + 1 / (2 * L) = 2 / L := by field_simp [hL_pos.ne']; ring
      linarith
    have hprod2 : (1 + 1 / L) * (1 + 2 * ρ) * (1 + u0) ≤ (1 + 2 / L) * (1 + u0) :=
      mul_le_mul_of_nonneg_right h12 (by positivity)
    have h2u : 2 / L * u0 ≤ 1 / L := by
      have := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2 / L)
      have heq : 2 / L * (1 / 2) = 1 / L := by field_simp [hL_pos.ne']
      linarith
    have hexp2 : (1 + 2 / L) * (1 + u0) = 1 + 2 / L + u0 + 2 / L * u0 := by ring
    have h21 : 2 / L + 1 / L = 3 / L := by ring
    linarith
  have hΦθ : Φ (-(θ * h)) ≤ μ * (1 + u0 * (1 + 3 / L + u0)) := by
    have h1 : Φ (-(θ * h)) ≤ μ + ((1 + h ^ 2) / (θ * h ^ 2)) * (u0 * (1 + u0)) * μ := by
      have hstep := mul_le_mul_of_nonneg_left hexp_u
        (show 0 ≤ (1 + h ^ 2) / (θ * h ^ 2) by positivity)
      have hstep' := mul_le_mul_of_nonneg_right hstep hμ0.le
      linarith [hdiff]
    have h2 : ((1 + h ^ 2) / (θ * h ^ 2)) * (u0 * (1 + u0)) ≤ u0 * (1 + 3 / L + u0) := by
      have ha := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ 1 + u0)
      have hb := ha.trans hK
      have hc := mul_le_mul_of_nonneg_left hb hu0_pos.le
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hμ0.le
    nlinarith
  have hmain : gaussianQuadrant ρ μ μ ≤
      μ ^ 2 * ((1 + ρ) * (1 + u0 * (1 + 3 / L + u0))) := by
    calc
      gaussianQuadrant ρ μ μ ≤ μ * Φ (-(θ * h)) * (1 + ρ) := hwil
      _ ≤ μ * (μ * (1 + u0 * (1 + 3 / L + u0))) * (1 + ρ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΦθ hμ0.le) h1p.le
      _ = μ ^ 2 * ((1 + ρ) * (1 + u0 * (1 + 3 / L + u0))) := by ring
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg μ))
  have hρ_eq : ρ = u0 * (1 / (2 * L)) := by
    have h2L : (2 * L) ≠ 0 := by positivity
    dsimp only [u0]
    rw [show 2 * ρ * L * (1 / (2 * L)) = ρ * ((2 * L) / (2 * L)) by ring, div_self h2L, mul_one]
  have hK_le_two : 1 + 3 / L + u0 ≤ 2 := by
    have h3L : 3 / L ≤ 3 / 10 := by
      rw [div_le_div_iff₀ hL_pos (by norm_num)]
      linarith
    linarith
  have hρK : ρ * (1 + 3 / L + u0) ≤ 2 * ρ := by
    have h := mul_le_mul_of_nonneg_left hK_le_two hρ0.le
    linarith
  have h2ρ_le : 2 * ρ ≤ 1 / (2 * L) := by
    have h := mul_le_mul_of_nonneg_left hρ_le (by norm_num : (0 : ℝ) ≤ 2)
    have heq : 2 * (1 / (4 * L)) = 1 / (2 * L) := by
      rw [show (2 : ℝ) * (1 / (4 * L)) = (2 / 4) * (1 / L) by ring,
        show (2 : ℝ) / 4 = 1 / 2 by norm_num]
      ring
    linarith
  have hsum : 1 / (2 * L) + 1 / (2 * L) = 1 / L := by ring
  have hlast : (1 + ρ) * (1 + u0 * (1 + 3 / L + u0)) =
      1 + u0 * (1 / (2 * L) + (1 + 3 / L + u0) + ρ * (1 + 3 / L + u0)) := by
    calc
      (1 + ρ) * (1 + u0 * (1 + 3 / L + u0))
          = 1 + ρ + u0 * (1 + 3 / L + u0) + u0 * (ρ * (1 + 3 / L + u0)) := by ring
      _ = 1 + u0 * (1 / (2 * L)) + u0 * (1 + 3 / L + u0) + u0 * (ρ * (1 + 3 / L + u0)) := by
          rw [← hρ_eq]
      _ = 1 + u0 * (1 / (2 * L) + (1 + 3 / L + u0) + ρ * (1 + 3 / L + u0)) := by ring
  rw [hlast]
  have h31 : 3 / L + 1 / L = 4 / L := by ring
  have hbr : 1 / (2 * L) + (1 + 3 / L + u0) + ρ * (1 + 3 / L + u0) ≤ 1 + 4 / L + u0 := by
    linarith
  have hfin := mul_le_mul_of_nonneg_left hbr hu0_pos.le
  linarith

/-- **Khot–Kindler–Mossel–O'Donnell,**: for sufficiently small `μ > 0`
and `0 < ρ ≤ 1 / (log (1 / μ))^3`,
`Λ_ρ(μ) ≤ μ * (μ + 2 * ρ * μ * log (1 / μ) * (1 + C * (log (log (1 / μ)) + log (log (1 / ρ)))
/ log (1 / μ)))`.
-/
theorem kkmo_gaussianQuadrant_estimate :
    ∃ C > 0, ∃ μ₀ > 0, ∀ μ ρ : ℝ,
      0 < μ → μ ≤ μ₀ → 0 < ρ → ρ ≤ 1 / (Real.log (1 / μ)) ^ 3 →
        gaussianQuadrant ρ μ μ ≤
          μ * (μ + 2 * ρ * μ * Real.log (1 / μ) *
            (1 + C * (Real.log (Real.log (1 / μ)) + Real.log (Real.log (1 / ρ))) /
              Real.log (1 / μ))) := by
  refine ⟨5, by norm_num, Real.exp (-10), Real.exp_pos _, fun μ ρ hμ0 hμ1 hρ0 hρ1 => ?_⟩
  set L := Real.log (1 / μ)
  have hL_ge : 10 ≤ L := by
    have h1 : Real.log (Real.exp 10) ≤ Real.log (1 / μ) := by
      refine Real.log_le_log (by positivity) ?_
      rw [Real.exp_neg] at hμ1
      rw [one_div]
      exact (le_inv_comm₀ hμ0 (Real.exp_pos 10)).mp hμ1
    rw [Real.log_exp] at h1
    exact h1
  have hL_pos : 0 < L := by linarith
  have hρ_lt_one : ρ < 1 := by
    refine hρ1.trans_lt ?_
    rw [div_lt_one (by positivity)]
    have hL2 : 100 ≤ L ^ 2 := by nlinarith
    nlinarith
  have hprod : 2 * ρ * L ≤ 1 / 2 := by
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hρ1 (by norm_num : (0 : ℝ) ≤ 2)) hL_pos.le
    have h2 : 2 * (1 / L ^ 3) * L = 2 / L ^ 2 := by field_simp [hL_pos.ne']
    have h3 : 2 / L ^ 2 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hsmall := gaussianQuadrant_small_mu_le hμ0 hμ1 hρ0 hρ_lt_one hprod
  have hlogL : 1 ≤ Real.log L := by
    have he : Real.exp 1 ≤ L :=
      (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 10)).trans hL_ge
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hinv_ρ_ge : L ^ 3 ≤ 1 / ρ := by
    rw [le_div_iff₀ hρ0]
    have := (le_div_iff₀ (by positivity : 0 < L ^ 3)).mp hρ1
    linarith
  have hlog_inv_ρ : 1 ≤ Real.log (Real.log (1 / ρ)) := by
    have hL3 : Real.exp (Real.exp 1) ≤ L ^ 3 := by
      have h1 : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
      have h2 : Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.mpr h1
      have h3 : Real.exp 3 ≤ 10 ^ 3 := by
        have he3 : Real.exp 1 ≤ 3 := h1
        have hpow : (Real.exp 1) ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le he3 3
        rw [← Real.exp_nat_mul] at hpow
        norm_num at hpow ⊢
        linarith
      exact h2.trans (h3.trans (pow_le_pow_left₀ (by norm_num) hL_ge 3))
    have hlog1 : Real.exp 1 ≤ Real.log (1 / ρ) := by
      simpa using Real.log_le_log (Real.exp_pos _) (hL3.trans hinv_ρ_ge)
    simpa using Real.log_le_log (Real.exp_pos 1) hlog1
  have h2ρL_le : 2 * ρ * L ≤ 1 / L := by
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hρ1 (by norm_num : (0 : ℝ) ≤ 2)) hL_pos.le
    have h2 : 2 * (1 / L ^ 3) * L = 2 / L ^ 2 := by field_simp [hL_pos.ne']
    have h3 : 2 / L ^ 2 ≤ 1 / L := by
      rw [div_le_div_iff₀ (by positivity) hL_pos]
      nlinarith
    linarith
  have hbr : 4 / L + 2 * ρ * L ≤ 5 * (Real.log L + Real.log (Real.log (1 / ρ))) / L := by
    have hnum : 5 ≤ 5 * (Real.log L + Real.log (Real.log (1 / ρ))) := by linarith
    have h5L : 5 / L ≤ 5 * (Real.log L + Real.log (Real.log (1 / ρ))) / L :=
      div_le_div_of_nonneg_right hnum hL_pos.le
    have h41 : 4 / L + 1 / L = 5 / L := by ring
    linarith
  have hmul_eq : μ ^ 2 * (1 + 2 * ρ * L * (1 + 4 / L + 2 * ρ * L)) =
      μ * (μ + 2 * ρ * μ * L * (1 + (4 / L + 2 * ρ * L))) := by ring
  rw [hmul_eq] at hsmall
  refine hsmall.trans ?_
  have hstep : 2 * ρ * μ * L * (1 + (4 / L + 2 * ρ * L)) ≤
      2 * ρ * μ * L * (1 + 5 * (Real.log L + Real.log (Real.log (1 / ρ))) / L) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) hμ0.le

end CslibFrontier.Foundations.Probability.Gaussian
