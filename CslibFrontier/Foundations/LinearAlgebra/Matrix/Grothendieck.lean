module

public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Grothendieck's Inequality with Krivine's Constant

This module proves Grothendieck's inequality with Krivine's constant
`K_G = π / (2 * log (1 + √2)) < 2`.

## Main definitions

* `CslibFrontier.Matrix.krivineConst`: Krivine's constant `π / (2 * log (1 + √2))`.

## Main results

* `CslibFrontier.Matrix.grothendieck_krivine`: Grothendieck's inequality with constant
  `krivineConst < 2`.
-/

public section

namespace CslibFrontier.Matrix

open Finset Cslib MeasureTheory Filter
open scoped BigOperators Topology

/-! ### Grothendieck's Inequality with Krivine's Constant -/

section GrothendieckKrivine

/-- Krivine's constant `K_G = π / (2 * log (1 + √2)) < 2`. -/
@[expose]
noncomputable def krivineConst : ℝ :=
  Real.pi / (2 * Real.log (1 + Real.sqrt 2))

theorem four_fifths_lt_log_one_add_sqrt_two :
    (4 / 5 : ℝ) < Real.log (1 + Real.sqrt 2) := by
  have hpos : 0 < 1 + Real.sqrt 2 := by positivity
  rw [Real.lt_log_iff_exp_lt hpos]
  have hexp_inv : (21 / 25 : ℝ) ≤ Real.exp (-(4 / 25 : ℝ)) := by
    have := Real.add_one_le_exp (-(4 / 25 : ℝ))
    linarith
  have hexp_step : Real.exp (4 / 25 : ℝ) ≤ 25 / 21 := by
    rw [Real.exp_neg] at hexp_inv
    have hpos_e : 0 < Real.exp (4 / 25 : ℝ) := Real.exp_pos _
    have h := mul_le_mul_of_nonneg_right hexp_inv hpos_e.le
    rw [inv_mul_cancel₀ hpos_e.ne'] at h
    linarith
  have hexp_pow : Real.exp (4 / 5 : ℝ) ≤ (25 / 21 : ℝ) ^ 5 := by
    have heq : (4 / 5 : ℝ) = (5 : ℕ) * (4 / 25 : ℝ) := by norm_num
    rw [heq, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hexp_step 5
  have hnum : (25 / 21 : ℝ) ^ 5 < 1 + Real.sqrt 2 := by
    have hsq : ((25 / 21 : ℝ) ^ 5 - 1) ^ 2 < 2 := by norm_num
    have hlt : (25 / 21 : ℝ) ^ 5 - 1 < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]
      exact hsq
    linarith
  linarith

theorem log_one_add_sqrt_two_lt_one : Real.log (1 + Real.sqrt 2) < 1 := by
  have hpos : 0 < 1 + Real.sqrt 2 := by positivity
  rw [Real.log_lt_iff_lt_exp hpos]
  have hsqrt : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith [Real.exp_one_gt_d9]

theorem sinh_log_one_add_sqrt_two : Real.sinh (Real.log (1 + Real.sqrt 2)) = 1 := by
  have hpos : 0 < 1 + Real.sqrt 2 := by positivity
  rw [Real.sinh_eq, Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos]
  have hinv : (1 + Real.sqrt 2)⁻¹ = Real.sqrt 2 - 1 := by
    have hmul : (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = 1 := by
      have : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  rw [hinv]
  ring

theorem krivineConst_pos : 0 < krivineConst := by
  unfold krivineConst
  have hlog : 0 < Real.log (1 + Real.sqrt 2) := by linarith [four_fifths_lt_log_one_add_sqrt_two]
  exact div_pos Real.pi_pos (by positivity)

theorem krivineConst_lt_two : krivineConst < 2 := by
  unfold krivineConst
  have hlog : (4 / 5 : ℝ) < Real.log (1 + Real.sqrt 2) := four_fifths_lt_log_one_add_sqrt_two
  rw [div_lt_iff₀ (by linarith)]
  linarith [Real.pi_lt_d2]

/-- Standard sign function taking values in `{+1, -1}`. -/
private noncomputable def stdSign (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

private lemma stdSign_abs (t : ℝ) : |stdSign t| = 1 := by
  unfold stdSign; split_ifs <;> norm_num

private lemma stdSign_mul_pos {r : ℝ} (hr : 0 < r) (t : ℝ) : stdSign (r * t) = stdSign t := by
  unfold stdSign
  by_cases ht : 0 ≤ t
  · simp only [mul_nonneg hr.le ht, ht, ↓reduceIte]
  · simp only [not_le.2 (mul_neg_of_pos_of_neg hr (lt_of_not_ge ht)), ht, ↓reduceIte]

private lemma measurable_stdSign : Measurable stdSign :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- 1D standard Gaussian density `γ₁(t) = (2π)^{-1/2} exp(-t²/2)`. -/
private noncomputable def gauss1 (t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2)

private lemma gauss1_nonneg (t : ℝ) : 0 ≤ gauss1 t := by
  unfold gauss1; positivity

private lemma integrable_gauss1 : Integrable gauss1 := by
  unfold gauss1
  have h := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  have heq : (fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2)) =
      fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    funext t; congr 2; ring
  rw [heq]
  exact h.const_mul _

private lemma integral_gauss1 : ∫ t : ℝ, gauss1 t = 1 := by
  unfold gauss1
  rw [MeasureTheory.integral_const_mul]
  have h := integral_gaussian (1 / 2 : ℝ)
  have heq : (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) = fun t => Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    funext t; congr 1; ring
  rw [heq, h]
  have hpi : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
  rw [hpi, inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by positivity))]

/-- Radial integral `∫_{0}^∞ r * exp(-r²/2) dr = 1`. -/
private lemma integral_radial_gauss :
    ∫ r : ℝ in Set.Ioi 0, r * Real.exp (-(r ^ 2) / 2) = 1 := by
  have hcont : ContinuousWithinAt (fun r : ℝ => -Real.exp (-(r ^ 2) / 2)) (Set.Ici 0) 0 :=
    (by fun_prop : Continuous fun r : ℝ => -Real.exp (-(r ^ 2) / 2)).continuousWithinAt
  have hderiv : ∀ r ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun r : ℝ => -Real.exp (-(r ^ 2) / 2)) (r * Real.exp (-(r ^ 2) / 2)) r := by
    intro r _
    have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-r) r := by
      have := ((hasDerivAt_pow 2 r).neg.div_const 2)
      convert this using 1; ring
    have h2 := ((Real.hasDerivAt_exp _).comp r h1).neg
    exact h2.congr_deriv (by ring)
  have hnn : ∀ r ∈ Set.Ioi (0 : ℝ), 0 ≤ r * Real.exp (-(r ^ 2) / 2) :=
    fun r hr => mul_nonneg (le_of_lt hr) (Real.exp_pos _).le
  have htend : Tendsto (fun r : ℝ => -Real.exp (-(r ^ 2) / 2)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun r : ℝ => -(r ^ 2) / 2) atTop atBot := by
      have h1 : Tendsto (fun r : ℝ => r ^ 2 / 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num)
      have h2 := tendsto_neg_atTop_atBot.comp h1
      exact h2.congr fun r => by dsimp; ring
    simpa using (Real.tendsto_exp_atBot.comp hsq).neg
  have h := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn htend
  simpa using h

/-- Angular integral: for `α ∈ [0, π]`,
`∫ θ in Ioo (-π) π, stdSign (cos θ) * stdSign (cos (θ - α)) = 2 * (π - 2 * α)`. -/
private lemma integral_angular_sign {α : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      stdSign (Real.cos θ) * stdSign (Real.cos (θ - α)) = 2 * (Real.pi - 2 * α) := by
  let g : ℝ → ℝ := fun θ => stdSign (Real.cos θ) * stdSign (Real.cos (θ - α))
  -- Rewrite `∫ in Ioo (-π) π` as interval integral `∫ θ in (-π)..π`.
  rw [MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  -- Note `g` is `π`-periodic a.e. (and `2π`-periodic everywhere!).
  have hper2 : Function.Periodic g (2 * Real.pi) := fun θ => by
    dsimp only [g]
    rw [Real.cos_add_two_pi, show θ + 2 * Real.pi - α = (θ - α) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  have hshift : ∫ θ in (-Real.pi)..Real.pi, g θ =
      ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2), g θ := by
    have h1 := hper2.intervalIntegral_add_eq (-Real.pi) (-(Real.pi / 2))
    have heq1 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    have heq2 : -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2 := by ring
    rw [heq1, heq2] at h1
    exact h1
  rw [hshift]
  have hmeas_g : Measurable g :=
    (measurable_stdSign.comp Real.continuous_cos.measurable).mul
      (measurable_stdSign.comp
        (Real.continuous_cos.comp (continuous_id.sub continuous_const)).measurable)
  have hint_g : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => by
    have hbdd : ∀ θ, ‖g θ‖ ≤ 1 := fun θ => by
      rw [Real.norm_eq_abs, abs_mul, stdSign_abs, stdSign_abs, mul_one]
    exact MeasureTheory.IntegrableOn.intervalIntegrable
      (Integrable.mono' (integrableOn_const (hs := measure_Icc_lt_top.ne))
        hmeas_g.aestronglyMeasurable (Eventually.of_forall hbdd))
  -- Split `[-(π/2), 3π/2]` into `[-(π/2), π/2]` and `[π/2, 3π/2]`.
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint_g (-(Real.pi / 2)) (Real.pi / 2)) (hint_g (Real.pi / 2) (3 * Real.pi / 2))]
  -- Evaluate `∫ θ in (-(π/2))..(π/2), g θ = π - 2 α`.
  have hfirst : ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), g θ = Real.pi - 2 * α := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint_g _ (-(Real.pi / 2) + α))
      (hint_g (-(Real.pi / 2) + α) _)]
    have hneg : ∫ θ in (-(Real.pi / 2))..(-(Real.pi / 2) + α), g θ = -α := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      have hae : ∀ᵐ θ ∂volume.restrict (Set.Ioc (-(Real.pi / 2)) (-(Real.pi / 2) + α)),
          g θ = -1 := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        have hnull : volume ({-(Real.pi / 2) + α} : Set ℝ) = 0 := MeasureTheory.measure_singleton _
        filter_upwards [compl_mem_ae_iff.2 hnull] with θ hθ_ne hθ
        have hlt_r : θ < -(Real.pi / 2) + α := lt_of_le_of_ne hθ.2 (by simpa using hθ_ne)
        have hcos1 : 0 < Real.cos θ :=
          Real.cos_pos_of_mem_Ioo ⟨hθ.1, by linarith⟩
        have hcos2 : Real.cos (θ - α) < 0 := by
          have := Real.cos_pos_of_mem_Ioo (x := θ - α + Real.pi)
            ⟨by linarith [hθ.1], by linarith⟩
          rw [Real.cos_add_pi] at this
          linarith
        simp only [g, stdSign, hcos1.le, not_le.2 hcos2, ↓reduceIte, mul_neg_one]
      rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const, Measure.real_def,
        Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    have hpos : ∫ θ in (-(Real.pi / 2) + α)..(Real.pi / 2), g θ = Real.pi - α := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      have hae : ∀ᵐ θ ∂volume.restrict (Set.Ioc (-(Real.pi / 2) + α) (Real.pi / 2)),
          g θ = 1 := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        have hnull : volume ({Real.pi / 2} : Set ℝ) = 0 := MeasureTheory.measure_singleton _
        filter_upwards [compl_mem_ae_iff.2 hnull] with θ hθ_ne hθ
        have hlt_r : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 (by simpa using hθ_ne)
        have hcos1 : 0 < Real.cos θ :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hlt_r⟩
        have hcos2 : 0 < Real.cos (θ - α) :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith⟩
        simp only [g, stdSign, hcos1.le, hcos2.le, ↓reduceIte, mul_one]
      rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const, Measure.real_def,
        Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    linarith
  -- Second half `[π/2, 3π/2]` equals first half by shifting `θ ↦ θ + π` (`cos(θ + π) = -cos θ`).
  have hsecond : ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), g θ =
      ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), g θ := by
    have hcomp := intervalIntegral.integral_comp_add_right g Real.pi
      (a := -(Real.pi / 2)) (b := Real.pi / 2)
    have ha : -(Real.pi / 2) + Real.pi = Real.pi / 2 := by ring
    have hb : Real.pi / 2 + Real.pi = 3 * Real.pi / 2 := by ring
    rw [ha, hb] at hcomp
    rw [← hcomp]
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    refine MeasureTheory.integral_congr_ae ?_
    change ∀ᵐ θ ∂volume.restrict (Set.Ioc (-(Real.pi / 2)) (Real.pi / 2)), g (θ + Real.pi) = g θ
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    have hnull : volume ({-(Real.pi / 2), Real.pi / 2, -(Real.pi / 2) + α} : Set ℝ) = 0 := by
      simp [Set.Finite.measure_zero (Set.toFinite _)]
    filter_upwards [compl_mem_ae_iff.2 hnull] with θ hθ_ne hθ
    have hne1 : Real.cos θ ≠ 0 := by
      have hlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 (fun h => hθ_ne (by simp [h]))
      exact (Real.cos_pos_of_mem_Ioo ⟨hθ.1, hlt⟩).ne'
    have hne2 : Real.cos (θ - α) ≠ 0 := by
      have hlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 (fun h => hθ_ne (by simp [h]))
      have hneα : θ ≠ -(Real.pi / 2) + α := fun h => hθ_ne (by simp [h])
      rcases lt_or_gt_of_ne hneα with h1 | h2
      · have := Real.cos_pos_of_mem_Ioo (x := θ - α + Real.pi)
          ⟨by linarith [hθ.1], by linarith [hθ.1]⟩
        rw [Real.cos_add_pi] at this; linarith
      · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
    have hflip (t : ℝ) (ht : t ≠ 0) : stdSign (-t) = -stdSign t := by
      unfold stdSign
      rcases lt_or_gt_of_ne ht with h | h
      · simp only [show (0 : ℝ) ≤ -t by linarith, show ¬(0 : ℝ) ≤ t by linarith, ↓reduceIte]; ring
      · simp only [show ¬(0 : ℝ) ≤ -t by linarith, h.le, ↓reduceIte]
    dsimp only [g]
    rw [Real.cos_add_pi, show θ + Real.pi - α = (θ - α) + Real.pi by ring, Real.cos_add_pi,
      hflip _ hne1, hflip _ hne2, neg_mul_neg]
  linarith

/-- **2D Grothendieck Gaussian identity**: for `c ∈ [-1, 1]` and `s = √(1 - c²)`,
`∫_{(x, y) ∈ ℝ²} stdSign(x) * stdSign(c x + s y) * γ₁(x) γ₁(y) = (2 / π) * arcsin c`. -/
private lemma integral_gauss2_sign {c : ℝ} (hc1 : -1 ≤ c) (hc2 : c ≤ 1) :
    ∫ p : ℝ × ℝ, stdSign p.1 * stdSign (c * p.1 + Real.sqrt (1 - c ^ 2) * p.2) *
      (gauss1 p.1 * gauss1 p.2) = (2 / Real.pi) * Real.arcsin c := by
  let α : ℝ := Real.arccos c
  have hα0 : 0 ≤ α := Real.arccos_nonneg c
  have hαπ : α ≤ Real.pi := Real.arccos_le_pi c
  have hcos : Real.cos α = c := Real.cos_arccos hc1 hc2
  have hsin : Real.sin α = Real.sqrt (1 - c ^ 2) := Real.sin_arccos c
  let F : ℝ × ℝ → ℝ := fun p =>
    stdSign p.1 * stdSign (c * p.1 + Real.sqrt (1 - c ^ 2) * p.2) * (gauss1 p.1 * gauss1 p.2)
  rw [← integral_comp_polarCoord_symm F]
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := rfl
  rw [htarget]
  -- Simplify integrand on `Ioi 0 ×ˢ Ioo (-π) π`.
  have hrew : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      p.1 • F (polarCoord.symm p) =
        ((2 * Real.pi)⁻¹ * (p.1 * Real.exp (-(p.1 ^ 2) / 2))) *
          (stdSign (Real.cos p.2) * stdSign (Real.cos (p.2 - α))) := by
    rintro ⟨r, θ⟩ ⟨hr, _⟩
    simp only [smul_eq_mul, F, polarCoord_symm_apply]
    have hr' : 0 < r := hr
    have hgauss : gauss1 (r * Real.cos θ) * gauss1 (r * Real.sin θ) =
        (2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2) := by
      unfold gauss1
      have hsq_pi : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ =
          (2 * Real.pi)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
      have htrig : -((r * Real.cos θ) ^ 2) / 2 + -((r * Real.sin θ) ^ 2) / 2 = -(r ^ 2) / 2 := by
        have h1 := Real.sin_sq_add_cos_sq θ
        nlinarith
      calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((r * Real.cos θ) ^ 2) / 2) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((r * Real.sin θ) ^ 2) / 2))
          = ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹) *
              (Real.exp (-((r * Real.cos θ) ^ 2) / 2) * Real.exp (-((r * Real.sin θ) ^ 2) / 2))
                := by
            ring
        _ = (2 * Real.pi)⁻¹ * Real.exp (-(r ^ 2) / 2) := by
            rw [hsq_pi, ← Real.exp_add, htrig]
    have harg : c * (r * Real.cos θ) + Real.sqrt (1 - c ^ 2) * (r * Real.sin θ) =
        r * Real.cos (θ - α) := by
      rw [← hsin, ← hcos, Real.cos_sub]
      ring
    rw [hgauss, harg, stdSign_mul_pos hr', stdSign_mul_pos hr']
    ring
  rw [MeasureTheory.setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hrew]
  -- Fubini product of radial and angular integrals.
  change ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      ((2 * Real.pi)⁻¹ * (p.1 * Real.exp (-(p.1 ^ 2) / 2))) *
        (stdSign (Real.cos p.2) * stdSign (Real.cos (p.2 - α))) ∂(volume.prod volume) = _
  rw [MeasureTheory.setIntegral_prod_mul (f :=
      fun r : ℝ => (2 * Real.pi)⁻¹ * (r * Real.exp (-(r ^ 2) / 2)))
      (g := fun θ : ℝ => stdSign (Real.cos θ) * stdSign (Real.cos (θ - α)))]
  rw [MeasureTheory.integral_const_mul, integral_radial_gauss, mul_one,
    integral_angular_sign hα0 hαπ]
  have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
  have harc : Real.arcsin c + α = Real.pi / 2 := by
    dsimp only [α]; unfold Real.arccos; ring
  field_simp [hpi_ne]
  linarith

/-- Marginalizing out the tail `d` independent standard Gaussian coordinates leaves the 2D
Gaussian integral unchanged. -/
private lemma integral_gauss_marginal (d : ℕ) (g : ℝ × ℝ → ℝ) :
    ∫ x : Fin (d + 2) → ℝ, g (x 0, x 1) * (∏ i : Fin (d + 2), gauss1 (x i)) =
      ∫ p : ℝ × ℝ, g p * (gauss1 p.1 * gauss1 p.2) := by
  induction d with
  | zero =>
    have hmp := MeasureTheory.volume_preserving_finTwoArrow ℝ
    rw [← hmp.integral_comp' (fun p : ℝ × ℝ => g p * (gauss1 p.1 * gauss1 p.2))]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [MeasurableEquiv.finTwoArrow, Fin.prod_univ_two]
  | succ d ih =>
    -- Split off the last coordinate `Fin.last (d + 2)` via `volume_preserving_piFinSuccAbove`.
    have hmp := MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (d + 3) => ℝ) (Fin.last (d + 2))
    have heq : (∫ x : Fin (d + 3) → ℝ, g (x 0, x 1) * ∏ i : Fin (d + 3), gauss1 (x i)) =
        ∫ q : ℝ × (Fin (d + 2) → ℝ),
          gauss1 q.1 * (g (q.2 0, q.2 1) * ∏ j : Fin (d + 2), gauss1 (q.2 j)) := by
      rw [← hmp.integral_comp' (fun q : ℝ × (Fin (d + 2) → ℝ) =>
        gauss1 q.1 * (g (q.2 0, q.2 1) * ∏ j : Fin (d + 2), gauss1 (q.2 j)))]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hprod : ∏ i : Fin (d + 3), gauss1 (x i) =
          gauss1 (x (Fin.last (d + 2))) *
            ∏ j : Fin (d + 2), gauss1 (x ((Fin.last (d + 2)).succAbove j)) := by
        rw [Fin.prod_univ_succAbove _ (Fin.last (d + 2))]
      have h0 : (Fin.last (d + 2)).succAbove (0 : Fin (d + 2)) = (0 : Fin (d + 3)) := by
        ext; simp
      have h1 : (Fin.last (d + 2)).succAbove (1 : Fin (d + 2)) = (1 : Fin (d + 3)) := by
        ext
        simp only [Fin.succAbove_last, Fin.val_castSucc, Fin.val_one']
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hf1 : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 3) => ℝ)
          (Fin.last (d + 2))) x).1 = x (Fin.last (d + 2)) := rfl
      have hf2 (j : Fin (d + 2)) : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 3) => ℝ)
          (Fin.last (d + 2))) x).2 j = x ((Fin.last (d + 2)).succAbove j) := rfl
      dsimp only
      rw [hf1]
      simp only [hf2, hprod, h0, h1]
      ring
    rw [heq]
    change ∫ q : ℝ × (Fin (d + 2) → ℝ),
        gauss1 q.1 * (g (q.2 0, q.2 1) * ∏ j : Fin (d + 2), gauss1 (q.2 j)) ∂(volume.prod volume) =
          _
    rw [MeasureTheory.integral_prod_mul (f := gauss1)
      (g := fun y : Fin (d + 2) → ℝ => g (y 0, y 1) * ∏ j : Fin (d + 2), gauss1 (y j)),
      integral_gauss1, one_mul]
    exact ih

/-- **High-dimensional Grothendieck Gaussian identity**: for any `d : ℕ` and unit vectors
`u, v : EuclideanSpace ℝ (Fin (d + 2))`,
`∫ x, stdSign ⟨u, x⟩ * stdSign ⟨v, x⟩ * ∏ i, gauss1 (x i) = (2 / π) * arcsin ⟨u, v⟩`. -/
private lemma integral_gauss_unit_vectors (d : ℕ) (u v : EuclideanSpace ℝ (Fin (d + 2)))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∫ x : EuclideanSpace ℝ (Fin (d + 2)),
      stdSign (@inner ℝ _ _ u x) * stdSign (@inner ℝ _ _ v x) *
        (∏ i : Fin (d + 2), gauss1 (x i)) =
      (2 / Real.pi) * Real.arcsin (@inner ℝ _ _ u v) := by
  let c : ℝ := @inner ℝ _ _ u v
  have hc_abs : |c| ≤ 1 := by
    have hcs := abs_real_inner_le_norm u v
    rwa [hu, hv, mul_one] at hcs
  have hc1 : -1 ≤ c := (abs_le.1 hc_abs).1
  have hc2 : c ≤ 1 := (abs_le.1 hc_abs).2
  let w : EuclideanSpace ℝ (Fin (d + 2)) := v - c • u
  have hw_orth : @inner ℝ _ _ u w = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow,
      mul_one, c, sub_self]
  have hw_norm_sq : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    have h1 := norm_sub_sq_real v (c • u)
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, hv, one_pow, inner_smul_right,
      real_inner_comm u v] at h1
    change ‖w‖ ^ 2 = _
    rw [h1, sq_abs]
    dsimp only [c]; ring
  have hw_norm : ‖w‖ = Real.sqrt (1 - c ^ 2) := by
    rw [← hw_norm_sq, Real.sqrt_sq (norm_nonneg w)]
  -- Find an orthonormal pair `(e0, e1)` with `e0 = u` and `v = c • e0 + √(1 - c²) • e1`.
  have hex_pair : ∃ e1 : EuclideanSpace ℝ (Fin (d + 2)),
      ‖e1‖ = 1 ∧ @inner ℝ _ _ u e1 = 0 ∧ v = c • u + Real.sqrt (1 - c ^ 2) • e1 := by
    by_cases hw0 : w = 0
    · -- `w = 0`, so `1 - c² = 0` and `v = c • u`. Pick any unit vector `e1 ⊥ u` (as `d + 2 ≥ 2`).
      have hsqrt0 : Real.sqrt (1 - c ^ 2) = 0 := by rw [← hw_norm, hw0, norm_zero]
      have horth_ne : (Submodule.span ℝ ({u} : Set (EuclideanSpace ℝ (Fin (d + 2)))))ᗮ ≠ ⊥ := by
        intro hbot
        have hdim := Submodule.finrank_add_finrank_orthogonal
          (Submodule.span ℝ ({u} : Set (EuclideanSpace ℝ (Fin (d + 2)))))
        rw [hbot, finrank_bot, add_zero, finrank_euclideanSpace_fin] at hdim
        have hle : Module.finrank ℝ
            (Submodule.span ℝ ({u} : Set (EuclideanSpace ℝ (Fin (d + 2))))) ≤ 1 := by
          simpa using finrank_span_le_card ({u} : Set (EuclideanSpace ℝ (Fin (d + 2))))
        omega
      obtain ⟨z, hz_mem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth_ne
      refine ⟨‖z‖⁻¹ • z, ?_, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz0)]
      · rw [inner_smul_right]
        have := (Submodule.mem_orthogonal _ z).1 hz_mem u
          (Submodule.subset_span (Set.mem_singleton u))
        rw [this, mul_zero]
      · rw [hsqrt0, zero_smul, add_zero]
        exact eq_of_sub_eq_zero hw0
    · refine ⟨‖w‖⁻¹ • w, ?_, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
      · rw [inner_smul_right, hw_orth, mul_zero]
      · rw [← hw_norm, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hw0), one_smul]
        simp [w]
  obtain ⟨e1, he1_norm, he1_orth, hv_eq⟩ := hex_pair
  -- Extend `{u, e1}` to an orthonormal basis `b` of `EuclideanSpace ℝ (Fin (d + 2))`.
  let vecs : Fin (d + 2) → EuclideanSpace ℝ (Fin (d + 2)) := fun i =>
    if i = 0 then u else if i = 1 then e1 else 0
  let s : Set (Fin (d + 2)) := {0, 1}
  have h01 : (0 : Fin (d + 2)) ≠ 1 := Fin.ne_of_val_ne (by simp)
  have horth : Orthonormal ℝ (s.domRestrict vecs) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · simp [vecs, hu]
    · have hne : (⟨0, Or.inl rfl⟩ : ↥s) ≠ ⟨1, Or.inr rfl⟩ :=
        fun h => h01 (congrArg Subtype.val h)
      simp only [Set.domRestrict_apply, vecs, ↓reduceIte, h01.symm, he1_orth, hne]
    · have hne : (⟨1, Or.inr rfl⟩ : ↥s) ≠ ⟨0, Or.inl rfl⟩ :=
        fun h => h01.symm (congrArg Subtype.val h)
      simp only [Set.domRestrict_apply, vecs, ↓reduceIte, h01.symm, real_inner_comm u e1,
        he1_orth, hne]
    · simp [vecs, h01.symm, he1_norm]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin])
  have hb0 : b 0 = u := by simpa [vecs] using hb 0 (Or.inl rfl)
  have hb1 : b 1 = e1 := by
    simpa [vecs, h01.symm] using hb 1 (Or.inr rfl)
  -- Rotate by the linear isometry `T = b.repr.symm` (`T e_0 = u`, `T e_1 = e1`).
  let T : EuclideanSpace ℝ (Fin (d + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 2)) := b.repr.symm
  have hmpT := T.measurePreserving
  have hprod_norm (x : EuclideanSpace ℝ (Fin (d + 2))) :
      ∏ i : Fin (d + 2), gauss1 (x i) =
        ((Real.sqrt (2 * Real.pi))⁻¹) ^ (d + 2) * Real.exp (-(‖x‖ ^ 2) / 2) := by
    unfold gauss1
    rw [Finset.prod_mul_distrib, Finset.prod_const, card_univ, Fintype.card_fin,
      ← Real.exp_sum, EuclideanSpace.norm_sq_eq]
    congr 2
    simp only [Real.norm_eq_abs, sq_abs, ← Finset.sum_div, ← Finset.sum_neg_distrib]
  have hgauss_inv (x : EuclideanSpace ℝ (Fin (d + 2))) :
      ∏ i : Fin (d + 2), gauss1 ((T x) i) = ∏ i : Fin (d + 2), gauss1 (x i) := by
    rw [hprod_norm, hprod_norm, T.norm_map]
  have hinner0 (x : EuclideanSpace ℝ (Fin (d + 2))) : @inner ℝ _ _ u (T x) = x 0 := by
    rw [← hb0]
    have := T.inner_map_map (b.repr (b 0)) x
    simp only [T, LinearIsometryEquiv.symm_apply_apply] at this
    rw [this, b.repr_self, EuclideanSpace.inner_single_left]
    simp
  have hinner1 (x : EuclideanSpace ℝ (Fin (d + 2))) : @inner ℝ _ _ e1 (T x) = x 1 := by
    rw [← hb1]
    have := T.inner_map_map (b.repr (b 1)) x
    simp only [T, LinearIsometryEquiv.symm_apply_apply] at this
    rw [this, b.repr_self, EuclideanSpace.inner_single_left]
    simp
  have hinner_v (x : EuclideanSpace ℝ (Fin (d + 2))) :
      @inner ℝ _ _ v (T x) = c * x 0 + Real.sqrt (1 - c ^ 2) * x 1 := by
    rw [hv_eq, inner_add_left, inner_smul_left, inner_smul_left, conj_trivial, conj_trivial,
      hinner0, hinner1]
  rw [← hmpT.integral_comp T.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin (d + 2)) =>
      stdSign (@inner ℝ _ _ u x) * stdSign (@inner ℝ _ _ v x) * ∏ i : Fin (d + 2), gauss1 (x i))]
  have hrew : (fun x : EuclideanSpace ℝ (Fin (d + 2)) =>
      stdSign (@inner ℝ _ _ u (T x)) * stdSign (@inner ℝ _ _ v (T x)) *
        ∏ i : Fin (d + 2), gauss1 ((T x) i)) =
      fun x => stdSign (x 0) * stdSign (c * x 0 + Real.sqrt (1 - c ^ 2) * x 1) *
        ∏ i : Fin (d + 2), gauss1 (x i) := by
    funext x; rw [hinner0, hinner_v, hgauss_inv]
  rw [hrew]
  -- Pass from `EuclideanSpace ℝ (Fin (d + 2))` to `Fin (d + 2) → ℝ` via
  -- `PiLp.volume_preserving_toLp`.
  have hmpLp := PiLp.volume_preserving_toLp (Fin (d + 2))
  rw [← hmpLp.integral_comp (MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin (d + 2)) =>
      stdSign (x 0) * stdSign (c * x 0 + Real.sqrt (1 - c ^ 2) * x 1) *
        ∏ i : Fin (d + 2), gauss1 (x i))]
  let g2 : ℝ × ℝ → ℝ := fun p => stdSign p.1 * stdSign (c * p.1 + Real.sqrt (1 - c ^ 2) * p.2)
  simpa [g2] using
    (integral_gauss_marginal d g2).trans (integral_gauss2_sign hc1 hc2)

private lemma integrable_gauss_pi :
    ∀ n : ℕ, Integrable (fun x : Fin n → ℝ => ∏ i : Fin n, gauss1 (x i))
  | 0 => by
    have hfin : IsFiniteMeasure (volume : Measure (Fin 0 → ℝ)) := by
      constructor
      have h : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
        have hu : (Set.univ : Set (Fin 0 → ℝ)) = Set.univ.pi fun _ => Set.univ := by ext; simp
        rw [hu, Measure.pi_pi]
        simp
      rw [h]; exact ENNReal.one_lt_top
    simp
  | n + 1 => by
    have hmp := MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
    have hprod : Integrable (fun q : ℝ × (Fin n → ℝ) =>
        gauss1 q.1 * ∏ j : Fin n, gauss1 (q.2 j)) :=
      integrable_gauss1.mul_prod (integrable_gauss_pi n)
    have hcomp := (hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).measurableEmbedding
      ).2 hprod
    refine hcomp.congr (Eventually.of_forall fun x => ?_)
    dsimp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_apply]
    exact (Fin.prod_univ_succAbove (fun i => gauss1 (x i)) (Fin.last n)).symm

private lemma integrable_finset_sum' {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {f : ι → α → ℝ} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun x => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hfun : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x :=
      funext fun x => Finset.sum_insert ha
    rw [hfun]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma integral_finset_sum' {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {f : ι → α → ℝ} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ x, (∑ i ∈ s, f i x) ∂μ = ∑ i ∈ s, ∫ x, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hfun : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x :=
      funext fun x => Finset.sum_insert ha
    rw [hfun, MeasureTheory.integral_add (hf a (Finset.mem_insert_self a s))
      (integrable_finset_sum' s fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi), Finset.sum_insert ha]

private lemma tendsto_finset_sum' {α ι : Type*} {l : Filter α} (s : Finset ι)
    {f : ι → α → ℝ} {a : ι → ℝ} (hf : ∀ i ∈ s, Tendsto (f i) l (𝓝 (a i))) :
    Tendsto (fun x => ∑ i ∈ s, f i x) l (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert b s hb ih =>
    have hfun : (fun x => ∑ i ∈ insert b s, f i x) = fun x => f b x + ∑ i ∈ s, f i x :=
      funext fun x => Finset.sum_insert hb
    rw [hfun, Finset.sum_insert hb]
    exact (hf b (Finset.mem_insert_self b s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Gaussian expectation bound for unit vectors: for any `M : Matrix X Y ℝ` and unit vectors
`u : X → EuclideanSpace ℝ (Fin (d + 2))`, `v : Y → EuclideanSpace ℝ (Fin (d + 2))`,
`∑_{x,y} M x y * (2/π) * arcsin ⟨u_x, v_y⟩ ≤ C` whenever all sign patterns give `≤ C`. -/
private lemma sum_arcsin_le_of_sign_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (M : Matrix X Y ℝ) (d : ℕ)
    (u : X → EuclideanSpace ℝ (Fin (d + 2))) (v : Y → EuclideanSpace ℝ (Fin (d + 2)))
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ y, ‖v y‖ = 1)
    {C : ℝ} (hC : ∀ (s : X → Bool) (t : Y → Bool),
      ∑ x : X, ∑ y : Y, M x y * BitString.signVal (s x) * BitString.signVal (t y) ≤ C) :
    ∑ x : X, ∑ y : Y, M x y * ((2 / Real.pi) * Real.arcsin (@inner ℝ _ _ (u x) (v y))) ≤ C := by
  let dens : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun g => ∏ i : Fin (d + 2), gauss1 (g i)
  have hdens_nn : ∀ g, 0 ≤ dens g := fun g => Finset.prod_nonneg fun i _ => gauss1_nonneg _
  have hdens_int : Integrable dens := by
    have hmp := PiLp.volume_preserving_ofLp (Fin (d + 2))
    have hprod : Integrable (fun x : Fin (d + 2) → ℝ => ∏ i : Fin (d + 2), gauss1 (x i)) :=
      integrable_gauss_pi (d + 2)
    exact hmp.integrable_comp_emb (MeasurableEquiv.toLp 2 (Fin (d + 2) →
      ℝ)).symm.measurableEmbedding
      |>.2 hprod
  have hdens_one : ∫ g : EuclideanSpace ℝ (Fin (d + 2)), dens g = 1 := by
    have hmp := PiLp.volume_preserving_toLp (Fin (d + 2))
    rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).measurableEmbedding dens]
    simpa [dens, integral_gauss1] using
      MeasureTheory.integral_fintype_prod_volume_eq_pow (ι := Fin (d + 2)) gauss1
  have hterm_int (x : X) (y : Y) :
      Integrable (fun g : EuclideanSpace ℝ (Fin (d + 2)) =>
        M x y * (stdSign (@inner ℝ _ _ (u x) g) * stdSign (@inner ℝ _ _ (v y) g) * dens g)) := by
    have hmeas : Measurable (fun g : EuclideanSpace ℝ (Fin (d + 2)) =>
        stdSign (@inner ℝ _ _ (u x) g) * stdSign (@inner ℝ _ _ (v y) g)) :=
      (measurable_stdSign.comp (continuous_const.inner continuous_id).measurable).mul
        (measurable_stdSign.comp (continuous_const.inner continuous_id).measurable)
    refine Integrable.const_mul ?_ (M x y)
    refine hdens_int.mono' (hmeas.aestronglyMeasurable.mul hdens_int.aestronglyMeasurable)
      (Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, stdSign_abs, stdSign_abs, one_mul, one_mul,
      abs_of_nonneg (hdens_nn g)]
  have hpt (g : EuclideanSpace ℝ (Fin (d + 2))) :
      ∑ x : X, ∑ y : Y, M x y *
        (stdSign (@inner ℝ _ _ (u x) g) * stdSign (@inner ℝ _ _ (v y) g) * dens g) ≤
      C * dens g := by
    let s : X → Bool := fun x => decide (@inner ℝ _ _ (u x) g < 0)
    let t : Y → Bool := fun y => decide (@inner ℝ _ _ (v y) g < 0)
    have hst (a : ℝ) : stdSign a = BitString.signVal (decide (a < 0)) := by
      unfold stdSign BitString.signVal
      by_cases h : 0 ≤ a
      · have h' : ¬ a < 0 := not_lt.2 h
        simp [h, h']
      · have h' : a < 0 := lt_of_not_ge h
        simp [h, h']
    have hsum : ∑ x : X, ∑ y : Y, M x y *
          (stdSign (@inner ℝ _ _ (u x) g) * stdSign (@inner ℝ _ _ (v y) g) * dens g) =
        (∑ x : X, ∑ y : Y, M x y * BitString.signVal (s x) * BitString.signVal (t y)) * dens g := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [s, t, ← hst]; ring
    rw [hsum]
    exact mul_le_mul_of_nonneg_right (hC s t) (hdens_nn g)
  have hint_lhs : Integrable (fun g : EuclideanSpace ℝ (Fin (d + 2)) =>
      ∑ x : X, ∑ y : Y, M x y *
        (stdSign (@inner ℝ _ _ (u x) g) * stdSign (@inner ℝ _ _ (v y) g) * dens g)) :=
    integrable_finset_sum' _ fun x _ => integrable_finset_sum' _ fun y _ => hterm_int x y
  have hint_le := MeasureTheory.integral_mono hint_lhs (hdens_int.const_mul C) hpt
  rw [MeasureTheory.integral_const_mul, hdens_one, mul_one] at hint_le
  rw [integral_finset_sum' _ fun x _ =>
    integrable_finset_sum' _ fun y _ => hterm_int x y] at hint_le
  refine le_trans ?_ hint_le
  refine le_of_eq (Finset.sum_congr rfl fun x _ => ?_)
  rw [integral_finset_sum' _ fun y _ => hterm_int x y]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_gauss_unit_vectors d (u x) (v y) (hu x) (hv y)]

/-- **Grothendieck's inequality with Krivine's constant** (`K_G = π / (2 * log (1 + √2)) < 2`):
for any real matrix `M`, if `∑_{x,y} M x y * s_x * t_y ≤ C` for all `±1` sign patterns `(s, t)`,
then for any vectors `u_x, v_y ∈ ℝ^d` with `‖u_x‖₂² ≤ 1` and `‖v_y‖₂² ≤ 1`,
`∑_{x,y} M x y * ⟨u_x, v_y⟩ ≤ krivineConst * C`. -/
theorem grothendieck_krivine {X Y : Type*} [Fintype X] [Fintype Y]
    (M : Matrix X Y ℝ) (d : ℕ) (u : X → Fin d → ℝ) (v : Y → Fin d → ℝ)
    (hu : ∀ x, ∑ k : Fin d, (u x k) ^ 2 ≤ 1)
    (hv : ∀ y, ∑ k : Fin d, (v y k) ^ 2 ≤ 1)
    {C : ℝ} (hC : ∀ (s : X → Bool) (t : Y → Bool),
      ∑ x : X, ∑ y : Y, M x y * BitString.signVal (s x) * BitString.signVal (t y) ≤ C) :
    ∑ x : X, ∑ y : Y, M x y * (∑ k : Fin d, u x k * v y k) ≤ krivineConst * C := by
  classical
  -- Step 1: Pad `u, v` into unit vectors `u', v'` in `Fin (d + 2) → ℝ` preserving inner products.
  let d' := d + 2
  let u' : X → Fin d' → ℝ := fun x k =>
    if hk : k.1 < d then u x ⟨k.1, hk⟩
    else if k.1 = d then Real.sqrt (1 - ∑ i : Fin d, (u x i) ^ 2)
    else 0
  let v' : Y → Fin d' → ℝ := fun y k =>
    if hk : k.1 < d then v y ⟨k.1, hk⟩
    else if k.1 = d + 1 then Real.sqrt (1 - ∑ i : Fin d, (v y i) ^ 2)
    else 0
  have huv' (x : X) (y : Y) : ∑ k : Fin d', u' x k * v' y k = ∑ k : Fin d, u x k * v y k := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h1 : u' x (Fin.last (d + 1)) * v' y (Fin.last (d + 1)) = 0 := by simp [u', d']
    have h2 : u' x (Fin.castSucc (Fin.last d)) * v' y (Fin.castSucc (Fin.last d)) = 0 := by
      simp [v', d']
    rw [h1, h2, add_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => by simp [u', v', k.2]
  have hu'_norm (x : X) : ∑ k : Fin d', (u' x k) ^ 2 = 1 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h1 : (u' x (Fin.last (d + 1))) ^ 2 = 0 := by simp [u', d']
    have h2 : (u' x (Fin.castSucc (Fin.last d))) ^ 2 = 1 - ∑ i : Fin d, (u x i) ^ 2 := by
      simp only [u', d', Fin.val_castSucc, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
        ↓reduceIte, Real.sq_sqrt (sub_nonneg.2 (hu x))]
    rw [h1, h2, add_zero]
    have hsum : ∑ k : Fin d, (u' x k.castSucc.castSucc) ^ 2 = ∑ i : Fin d, (u x i) ^ 2 :=
      Finset.sum_congr rfl fun k _ => by simp [u', k.2]
    rw [hsum]; ring
  have hv'_norm (y : Y) : ∑ k : Fin d', (v' y k) ^ 2 = 1 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h1 : (v' y (Fin.last (d + 1))) ^ 2 = 1 - ∑ i : Fin d, (v y i) ^ 2 := by
      simp only [v', d', Fin.val_last, show ¬ d + 1 < d by omega, ↓reduceDIte, ↓reduceIte,
        Real.sq_sqrt (sub_nonneg.2 (hv y))]
    have h2 : (v' y (Fin.castSucc (Fin.last d))) ^ 2 = 0 := by simp [v', d']
    rw [h1, h2, add_zero]
    have hsum : ∑ k : Fin d, (v' y k.castSucc.castSucc) ^ 2 = ∑ i : Fin d, (v y i) ^ 2 :=
      Finset.sum_congr rfl fun k _ => by simp [v', k.2]
    rw [hsum]; ring
  -- Step 2: Krivine's truncated odd-tensor map for `c = log (1 + √2)` (`sinh c = 1`).
  let c : ℝ := Real.log (1 + Real.sqrt 2)
  have hc_pos : 0 < c := by linarith [four_fifths_lt_log_one_add_sqrt_two]
  have hc_lt1 : c < 1 := log_one_add_sqrt_two_lt_one
  have hsinh_c : Real.sinh c = 1 := sinh_log_one_add_sqrt_two
  let T (N : ℕ) (r : ℝ) : ℝ :=
    ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * (c * r) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)
  have hN_bound (N : ℕ) :
      ∑ x : X, ∑ y : Y, M x y * ((2 / Real.pi) * Real.arcsin (T N (∑ k : Fin d',
        u' x k * v' y k))) ≤ C := by
    let idx := Σ k : Fin (N + 1), (Fin (2 * k.1 + 1) → Fin d')
    let D := Fintype.card idx
    let e : idx ≃ Fin D := Fintype.equivFin idx
    let coeff (k : ℕ) : ℝ := Real.sqrt (c ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
    let rawU (x : X) (p : idx) : ℝ := coeff p.1.1 * ∏ j : Fin (2 * p.1.1 + 1), u' x (p.2 j)
    let rawV (y : Y) (p : idx) : ℝ :=
      (-1 : ℝ) ^ p.1.1 * coeff p.1.1 * ∏ j : Fin (2 * p.1.1 + 1), v' y (p.2 j)
    have hS_le : ∑ k ∈ Finset.range (N + 1), c ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) ≤ 1 := by
      rw [← hsinh_c]
      exact ((Real.hasSum_sinh c).summable.sum_le_tsum (Finset.range (N + 1))
        (fun k _ => by positivity)).trans_eq (Real.hasSum_sinh c).tsum_eq
    have hsum_rawU (x : X) : ∑ p : idx, (rawU x p) ^ 2 =
        ∑ k ∈ Finset.range (N + 1), c ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
      rw [Fintype.sum_sigma, Fin.sum_univ_eq_sum_range (fun k =>
        ∑ f : Fin (2 * k + 1) → Fin d', (coeff k * ∏ j, u' x (f j)) ^ 2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsq : ∑ f : Fin (2 * k + 1) → Fin d', (coeff k * ∏ j, u' x (f j)) ^ 2 =
          (coeff k) ^ 2 * ∑ f : Fin (2 * k + 1) → Fin d', ∏ j, (u' x (f j)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => by rw [mul_pow, Finset.prod_pow]
      rw [hsq, Real.sq_sqrt (by positivity),
        ← Fintype.prod_sum (fun (_ : Fin (2 * k + 1)) (a : Fin d') => (u' x a) ^ 2),
        Finset.prod_const, card_univ, Fintype.card_fin, hu'_norm x, one_pow, mul_one]
    have hsum_rawV (y : Y) : ∑ p : idx, (rawV y p) ^ 2 =
        ∑ k ∈ Finset.range (N + 1), c ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
      rw [Fintype.sum_sigma, Fin.sum_univ_eq_sum_range (fun k =>
        ∑ f : Fin (2 * k + 1) → Fin d', ((-1 : ℝ) ^ k * coeff k * ∏ j, v' y (f j)) ^ 2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsq : ∑ f : Fin (2 * k + 1) → Fin d', ((-1 : ℝ) ^ k * coeff k * ∏ j, v' y (f j)) ^ 2 =
          (coeff k) ^ 2 * ∑ f : Fin (2 * k + 1) → Fin d', ∏ j, (v' y (f j)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm k 2, pow_mul, neg_one_sq, one_pow, one_mul,
            Finset.prod_pow]
      rw [hsq, Real.sq_sqrt (by positivity),
        ← Fintype.prod_sum (fun (_ : Fin (2 * k + 1)) (a : Fin d') => (v' y a) ^ 2),
        Finset.prod_const, card_univ, Fintype.card_fin, hv'_norm y, one_pow, mul_one]
    have hinner_raw (x : X) (y : Y) : ∑ p : idx, rawU x p * rawV y p =
        T N (∑ k : Fin d', u' x k * v' y k) := by
      rw [Fintype.sum_sigma, Fin.sum_univ_eq_sum_range (fun k =>
        ∑ f : Fin (2 * k + 1) → Fin d',
          (coeff k * ∏ j, u' x (f j)) * ((-1 : ℝ) ^ k * coeff k * ∏ j, v' y (f j)))]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hfac : ∑ f : Fin (2 * k + 1) → Fin d',
            (coeff k * ∏ j, u' x (f j)) * ((-1 : ℝ) ^ k * coeff k * ∏ j, v' y (f j)) =
          ((-1 : ℝ) ^ k * (coeff k) ^ 2) *
            ∑ f : Fin (2 * k + 1) → Fin d', ∏ j, (u' x (f j) * v' y (f j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => by rw [Finset.prod_mul_distrib]; ring
      rw [hfac, Real.sq_sqrt (by positivity),
        ← Fintype.prod_sum (fun (_ : Fin (2 * k + 1)) (a : Fin d') => u' x a * v' y a),
        Finset.prod_const, card_univ, Fintype.card_fin, mul_pow]
      ring
    -- Pad `rawU, rawV` into unit vectors in `EuclideanSpace ℝ (Fin (D + 2))`.
    let Sval := ∑ k ∈ Finset.range (N + 1), c ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)
    let U : X → EuclideanSpace ℝ (Fin (D + 2)) := fun x =>
      (WithLp.equiv 2 (Fin (D + 2) → ℝ)).symm fun i =>
        if hi : i.1 < D then rawU x (e.symm ⟨i.1, hi⟩)
        else if i.1 = D then Real.sqrt (1 - Sval)
        else 0
    let V : Y → EuclideanSpace ℝ (Fin (D + 2)) := fun y =>
      (WithLp.equiv 2 (Fin (D + 2) → ℝ)).symm fun i =>
        if hi : i.1 < D then rawV y (e.symm ⟨i.1, hi⟩)
        else if i.1 = D + 1 then Real.sqrt (1 - Sval)
        else 0
    have hU_norm (x : X) : ‖U x‖ = 1 := by
      have hsq : ‖U x‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
        simp only [Real.norm_eq_abs, sq_abs]
        have h1 : (U x (Fin.last (D + 1))) ^ 2 = 0 := by simp [U]
        have h2 : (U x (Fin.castSucc (Fin.last D))) ^ 2 = 1 - Sval := by
          simp only [U, WithLp.equiv_symm_apply, Fin.val_castSucc, Fin.val_last,
            lt_self_iff_false, ↓reduceDIte, ↓reduceIte]
          exact Real.sq_sqrt (sub_nonneg.2 hS_le)
        have h3 : ∑ i : Fin D, (U x i.castSucc.castSucc) ^ 2 = Sval := by
          trans ∑ i : Fin D, (rawU x (e.symm i)) ^ 2
          · refine Finset.sum_congr rfl fun i _ => by simp [U, i.2]
          · rw [Equiv.sum_comp e.symm (fun p => (rawU x p) ^ 2), hsum_rawU x]
        rw [h1, h2, h3]; ring
      nlinarith [norm_nonneg (U x)]
    have hV_norm (y : Y) : ‖V y‖ = 1 := by
      have hsq : ‖V y‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
        simp only [Real.norm_eq_abs, sq_abs]
        have h1 : (V y (Fin.last (D + 1))) ^ 2 = 1 - Sval := by
          simp only [V, WithLp.equiv_symm_apply, Fin.val_last, show ¬ D + 1 < D by omega,
            ↓reduceDIte, ↓reduceIte]
          exact Real.sq_sqrt (sub_nonneg.2 hS_le)
        have h2 : (V y (Fin.castSucc (Fin.last D))) ^ 2 = 0 := by simp [V]
        have h3 : ∑ i : Fin D, (V y i.castSucc.castSucc) ^ 2 = Sval := by
          trans ∑ i : Fin D, (rawV y (e.symm i)) ^ 2
          · refine Finset.sum_congr rfl fun i _ => by simp [V, i.2]
          · rw [Equiv.sum_comp e.symm (fun p => (rawV y p) ^ 2), hsum_rawV y]
        rw [h1, h2, h3]; ring
      nlinarith [norm_nonneg (V y)]
    have hUV_inner (x : X) (y : Y) :
        @inner ℝ _ _ (U x) (V y) = T N (∑ k : Fin d', u' x k * v' y k) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, dotProduct]
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      have h1 : V y (Fin.last (D + 1)) * U x (Fin.last (D + 1)) = 0 := by simp [U]
      have h2 : V y (Fin.castSucc (Fin.last D)) * U x (Fin.castSucc (Fin.last D)) = 0 := by
        simp [V]
      rw [h1, h2, add_zero, add_zero]
      trans ∑ i : Fin D, rawU x (e.symm i) * rawV y (e.symm i)
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [U, V, WithLp.equiv_symm_apply, Fin.val_castSucc, i.2, ↓reduceDIte]
        exact mul_comm _ _
      · rw [Equiv.sum_comp e.symm (fun p => rawU x p * rawV y p), hinner_raw x y]
    simpa only [hUV_inner] using sum_arcsin_le_of_sign_bound M D U V hU_norm hV_norm hC
  -- Step 3: Let `N → ∞`: `T N r → sin (c * r)`, and `arcsin (sin (c * r)) = c * r` since `|c * r| ≤
  -- π / 2`.
  have htend_T (r : ℝ) : Tendsto (fun N : ℕ => T N r) atTop (𝓝 (Real.sin (c * r))) := by
    have hhs := (Real.hasSum_sin (c * r)).tendsto_sum_nat
    exact hhs.comp (tendsto_add_atTop_nat 1)
  have htend_sum : Tendsto (fun N : ℕ =>
      ∑ x : X, ∑ y : Y, M x y * ((2 / Real.pi) * Real.arcsin (T N (∑ k : Fin d', u' x k * v' y k))))
      atTop (𝓝 (∑ x : X, ∑ y : Y, M x y * ((2 * c / Real.pi) * (∑ k : Fin d',
        u' x k * v' y k)))) := by
    refine tendsto_finset_sum' _ fun x _ => tendsto_finset_sum' _ fun y _ => ?_
    set r : ℝ := ∑ k : Fin d', u' x k * v' y k
    have hr_abs : |r| ≤ 1 := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (u' x) (v' y)
      rw [hu'_norm x, hv'_norm y, mul_one] at hcs
      nlinarith [sq_abs r, abs_nonneg r]
    have hcr1 : -(Real.pi / 2) ≤ c * r := by
      have : -1 ≤ c * r := by nlinarith [(abs_le.1 hr_abs).1, (abs_le.1 hr_abs).2]
      linarith [Real.pi_gt_three]
    have hcr2 : c * r ≤ Real.pi / 2 := by
      have : c * r ≤ 1 := by nlinarith [(abs_le.1 hr_abs).1, (abs_le.1 hr_abs).2]
      linarith [Real.pi_gt_three]
    have harc : Real.arcsin (Real.sin (c * r)) = c * r := Real.arcsin_sin hcr1 hcr2
    have hlim : Tendsto (fun N : ℕ => M x y * ((2 / Real.pi) * Real.arcsin (T N r)))
        atTop (𝓝 (M x y * ((2 / Real.pi) * Real.arcsin (Real.sin (c * r))))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((Real.continuous_arcsin.tendsto _).comp (htend_T r)))
    rw [harc] at hlim
    have heq : M x y * ((2 / Real.pi) * (c * r)) = M x y * ((2 * c / Real.pi) * r) := by ring
    rwa [heq] at hlim
  have hlim_le : ∑ x : X, ∑ y : Y, M x y * ((2 * c / Real.pi) * (∑ k : Fin d', u' x k * v' y k)) ≤
    C :=
    le_of_tendsto htend_sum (Eventually.of_forall hN_bound)
  have hfac_out : (2 * c / Real.pi) * (∑ x : X, ∑ y : Y, M x y * (∑ k : Fin d, u x k * v y k)) ≤
    C := by
    rw [Finset.mul_sum]
    refine le_trans (le_of_eq ?_) hlim_le
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by rw [huv' x y]; ring
  have hpos_coeff : 0 < 2 * c / Real.pi := div_pos (by positivity) Real.pi_pos
  have hdiv := (le_div_iff₀' hpos_coeff).2 hfac_out
  calc ∑ x : X, ∑ y : Y, M x y * (∑ k : Fin d, u x k * v y k)
      ≤ C / (2 * c / Real.pi) := hdiv
    _ = krivineConst * C := by
      unfold krivineConst; dsimp only [c]; field_simp [hc_pos.ne', Real.pi_pos.ne']

/-- Bilinear rectangle bound via Grothendieck's inequality: if every combinatorial rectangle
`S × T` satisfies `|∑_{x ∈ S, y ∈ T} M x y| ≤ K`, then for any unit vectors `u_x, v_y ∈ ℝ^d`,
`∑_{x,y} M x y ⟨u_x, v_y⟩ ≤ 4 * krivineConst * K`. -/
theorem bilinear_le_four_mul_krivineConst_mul_maxRect {X Y : Type*} [Fintype X] [Fintype Y]
    (M : Matrix X Y ℝ) (d : ℕ) (u : X → Fin d → ℝ) (v : Y → Fin d → ℝ)
    (hu : ∀ x, ∑ k : Fin d, (u x k) ^ 2 ≤ 1)
    (hv : ∀ y, ∑ k : Fin d, (v y k) ^ 2 ≤ 1)
    {K : ℝ} (hK : ∀ (S : Finset X) (T : Finset Y), |∑ x ∈ S, ∑ y ∈ T, M x y| ≤ K) :
    ∑ x : X, ∑ y : Y, M x y * (∑ k : Fin d, u x k * v y k) ≤ 4 * krivineConst * K := by
  classical
  have hsign (s : X → Bool) (t : Y → Bool) :
      ∑ x : X, ∑ y : Y, M x y * BitString.signVal (s x) * BitString.signVal (t y) ≤ 4 * K := by
    let S0 : Finset X := univ.filter (fun x => s x = false)
    let S1 : Finset X := univ.filter (fun x => s x = true)
    let T0 : Finset Y := univ.filter (fun y => t y = false)
    let T1 : Finset Y := univ.filter (fun y => t y = true)
    have hsplit : ∑ x : X, ∑ y : Y, M x y * BitString.signVal (s x) * BitString.signVal (t y) =
        (∑ x ∈ S0, ∑ y ∈ T0, M x y) - (∑ x ∈ S0, ∑ y ∈ T1, M x y) -
        (∑ x ∈ S1, ∑ y ∈ T0, M x y) + (∑ x ∈ S1, ∑ y ∈ T1, M x y) := by
      have hx (f : X → ℝ) : ∑ x : X, f x = (∑ x ∈ S0, f x) + (∑ x ∈ S1, f x) := by
        rw [← Finset.sum_union]
        · refine Finset.sum_congr (by ext x; cases s x <;> simp [S0, S1]) (fun _ _ => rfl)
        · exact Finset.disjoint_filter.2 fun _ _ h1 h2 => by rw [h1] at h2; cases h2
      have hy (f : Y → ℝ) : ∑ y : Y, f y = (∑ y ∈ T0, f y) + (∑ y ∈ T1, f y) := by
        rw [← Finset.sum_union]
        · refine Finset.sum_congr (by ext y; cases t y <;> simp [T0, T1]) (fun _ _ => rfl)
        · exact Finset.disjoint_filter.2 fun _ _ h1 h2 => by rw [h1] at h2; cases h2
      rw [hx]
      simp_rw [hy, Finset.sum_add_distrib]
      have h00 : ∑ x ∈ S0, ∑ y ∈ T0, M x y * BitString.signVal (s x) * BitString.signVal (t y) =
          ∑ x ∈ S0, ∑ y ∈ T0, M x y :=
        Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by
          rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]; simp [BitString.signVal]
      have h01 : ∑ x ∈ S0, ∑ y ∈ T1, M x y * BitString.signVal (s x) * BitString.signVal (t y) =
          -(∑ x ∈ S0, ∑ y ∈ T1, M x y) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun y hy => by
          rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]; simp [BitString.signVal]
      have h10 : ∑ x ∈ S1, ∑ y ∈ T0, M x y * BitString.signVal (s x) * BitString.signVal (t y) =
          -(∑ x ∈ S1, ∑ y ∈ T0, M x y) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun y hy => by
          rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]; simp [BitString.signVal]
      have h11 : ∑ x ∈ S1, ∑ y ∈ T1, M x y * BitString.signVal (s x) * BitString.signVal (t y) =
          ∑ x ∈ S1, ∑ y ∈ T1, M x y :=
        Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by
          rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]; simp [BitString.signVal]
      rw [h00, h01, h10, h11]; ring
    rw [hsplit]
    have h00 := abs_le.1 (hK S0 T0)
    have h01 := abs_le.1 (hK S0 T1)
    have h10 := abs_le.1 (hK S1 T0)
    have h11 := abs_le.1 (hK S1 T1)
    linarith
  have hgk := grothendieck_krivine M d u v hu hv hsign
  linarith

end GrothendieckKrivine

end CslibFrontier.Matrix
