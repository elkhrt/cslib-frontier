module

public import CslibFrontier.Foundations.Probability.Gaussian.Borell
public import CslibFrontier.Foundations.Probability.Gaussian.Quadrant
import CslibFrontier.Foundations.Probability.Gaussian.BorellHeatKernel
import CslibFrontier.Foundations.Probability.Gaussian.Correlated
import CslibFrontier.Foundations.Probability.Gaussian.NoiseOperator
import CslibFrontier.Foundations.Probability.Gaussian.NoiseSemigroup
import CslibFrontier.Foundations.Probability.Gaussian.QuadrantDeriv
import CslibFrontier.Foundations.Probability.Gaussian.Quantile
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One-Dimensional and Finite-Dimensional Two-Function Borell Isoperimetric Inequality

This module proves the one-dimensional two-function Borell isoperimetric inequality
(`TwoFunctionBorellInequality ρ (Fin 1)`) for all `ρ ∈ [0, 1]` via Ornstein–Uhlenbeck heat flow,
discharging the one-dimensional base case of
`CslibFrontier.Foundations.Probability.Gaussian.Borell`.

Combined with tensorization (`TwoFunctionBorellInequality.of_fin_one`) and the reflection identity
for the Gaussian quadrant function `Λ_ρ`, this establishes the unconditional finite-dimensional
Borell isoperimetric inequality for all `ρ ∈ [0, 1]` (upper bound) and `ρ ∈ [-1, 0]` (lower bound).

## Main results

* `CslibFrontier.Probability.Gaussian.twoFunctionBorellInequality_fin_one`:
  `TwoFunctionBorellInequality ρ (Fin 1)` for `ρ ∈ [0, 1]`.
* `CslibFrontier.Probability.Gaussian.twoFunctionBorellInequality_all`:
  `TwoFunctionBorellInequality ρ ι` for all finite `ι` and `ρ ∈ [0, 1]`.
* `CslibFrontier.Probability.Gaussian.borell_gaussianNoiseStability_le`:
  `GStab_ρ(f) ≤ Λ_ρ(𝔼 f, 𝔼 f)` for `ρ ∈ [0, 1]` and measurable `f : (ι → ℝ) → [0, 1]`.
* `CslibFrontier.Probability.Gaussian.borell_gaussianNoiseStability_ge_of_nonpos`:
  `Λ_ρ(𝔼 f, 𝔼 f) ≤ GStab_ρ(f)` for `ρ ∈ [-1, 0]` and measurable `f : (ι → ℝ) → [0, 1]`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal Matrix

namespace CslibFrontier.Probability.Gaussian

section BorellHeatFlow

local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

/-- Core 1D Two-Function Borell inequality for strictly interior functions
`f, g : ℝ → [δ, 1 - δ]`. -/
private theorem borell_one_dim_interior {ρ δ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfδ : ∀ x, f x ∈ Icc δ (1 - δ)) (hgδ : ∀ x, g x ∈ Icc δ (1 - δ)) :
    ∫ p, gaussianQuadrant ρ (f p.1) (g p.2) ∂correlatedGaussian ρ ≤
      gaussianQuadrant ρ (∫ x, f x ∂gaussianReal 0 1) (∫ x, g x ∂gaussianReal 0 1) := by
  have hρ : |ρ| < 1 := abs_lt.2 ⟨by linarith, hρ1⟩
  have hf01 : ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨by linarith [(hfδ x).1], by linarith [(hfδ x).2]⟩
  have hg01 : ∀ x, g x ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨by linarith [(hgδ x).1], by linarith [(hgδ x).2]⟩
  set ψ : ℝ → ℝ := fun r =>
    ∫ p, gaussianQuadrant ρ (ou1D r f p.1) (ou1D r g p.2) ∂correlatedGaussian ρ
  have hψ_deriv_nonpos : ∀ r ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt ψ d r ∧ d ≤ 0 := by
    intro r hr
    set a := r / 2
    set b := (r + 1) / 2
    have ha0 : 0 < a := by unfold a; linarith [hr.1]
    have hb0 : 0 < b := by unfold b; linarith [hr.1]
    have hb1 : b < 1 := by unfold b; linarith [hr.2]
    have hIoo : Ioo a b ∈ 𝓝 r :=
      Ioo_mem_nhds (by unfold a; linarith [hr.1]) (by unfold b; linarith [hr.2])
    set u : ℝ → ℝ := ou1D r f
    set v : ℝ → ℝ := ou1D r g
    have hu_mem : ∀ x, u x ∈ Icc δ (1 - δ) := fun x => ou1D_mem_Icc hf hfδ r x
    have hv_mem : ∀ y, v y ∈ Icc δ (1 - δ) := fun y => ou1D_mem_Icc hg hgδ r y
    have hu_oo : ∀ x, u x ∈ Ioo (0 : ℝ) 1 := fun x =>
      ⟨lt_of_lt_of_le hδ0 (hu_mem x).1, lt_of_le_of_lt (hu_mem x).2 (by linarith)⟩
    have hv_oo : ∀ y, v y ∈ Ioo (0 : ℝ) 1 := fun y =>
      ⟨lt_of_lt_of_le hδ0 (hv_mem y).1, lt_of_le_of_lt (hv_mem y).2 (by linarith)⟩
    have hD_pt : ∀ r' ∈ Ioo a b, ∀ p : ℝ × ℝ,
        HasDerivAt (fun t => gaussianQuadrant ρ (ou1D t f p.1) (ou1D t g p.2))
          (deriv (fun α => gaussianQuadrant ρ α (ou1D r' g p.2)) (ou1D r' f p.1) *
              deriv (fun t => ou1D t f p.1) r' +
            deriv (fun β => gaussianQuadrant ρ (ou1D r' f p.1) β) (ou1D r' g p.2) *
              deriv (fun t => ou1D t g p.2) r') r' := by
      intro r' hr' p
      have hr'0 : 0 < r' := lt_trans ha0 hr'.1
      have hr'1 : r' < 1 := lt_trans hr'.2 hb1
      have hfu := (ou1D_derivs_and_pde hr'0 hr'1 hf hf01 p.1).2.2.1
      have hgv := (ou1D_derivs_and_pde hr'0 hr'1 hg hg01 p.2).2.2.1
      have hm1 := ou1D_mem_Icc hf hfδ r' p.1
      have hm2 := ou1D_mem_Icc hg hgδ r' p.2
      have ho1 : ou1D r' f p.1 ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_lt_of_le hδ0 hm1.1, lt_of_le_of_lt hm1.2 (by linarith)⟩
      have ho2 : ou1D r' g p.2 ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_lt_of_le hδ0 hm2.1, lt_of_le_of_lt hm2.2 (by linarith)⟩
      have hcomp :=
        ((hasFDerivAt_gaussianQuadrant hρ ho1 ho2).comp r'
          (hfu.hasFDerivAt.prodMk hgv.hasFDerivAt)).hasDerivAt
      refine hcomp.congr_deriv ?_
      simp only [ContinuousLinearMap.comp_apply, add_apply,
        smul_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', smul_eq_mul, one_mul,
        deriv_gaussianQuadrant_left hρ ho1 ho2, deriv_gaussianQuadrant_right hρ ho1 ho2,
        hfu.deriv, hgv.deriv]
    set C1 : ℝ := 1 / (a * √(1 - b ^ 2))
    set C2 : ℝ := 2 / (a * (1 - b ^ 2))
    set dom : ℝ × ℝ → ℝ := fun p => C1 * (|p.1| + |p.2|) + 2 * C2
    have hdom_int : Integrable dom (correlatedGaussian ρ) := by
      have hid : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
        ((memLp_id_gaussianReal 1).integrable le_rfl).abs
      have h1 : Integrable (fun p : ℝ × ℝ => |p.1|) (correlatedGaussian ρ) :=
        (⟨measurable_fst, correlatedGaussian_map_fst ρ⟩ :
          MeasurePreserving Prod.fst (correlatedGaussian ρ)
            (gaussianReal 0 1)).integrable_comp_of_integrable hid
      have h2 : Integrable (fun p : ℝ × ℝ => |p.2|) (correlatedGaussian ρ) :=
        (⟨measurable_snd, correlatedGaussian_map_snd hρ.le⟩ :
          MeasurePreserving Prod.snd (correlatedGaussian ρ)
            (gaussianReal 0 1)).integrable_comp_of_integrable hid
      exact ((h1.add h2).const_mul C1).add (integrable_const _)
    have hdom_le : ∀ p : ℝ × ℝ, ∀ r' ∈ Ioo a b,
        ‖deriv (fun α => gaussianQuadrant ρ α (ou1D r' g p.2)) (ou1D r' f p.1) *
            deriv (fun t => ou1D t f p.1) r' +
          deriv (fun β => gaussianQuadrant ρ (ou1D r' f p.1) β) (ou1D r' g p.2) *
            deriv (fun t => ou1D t g p.2) r'‖ ≤ dom p := by
      intro p r' hr'
      have hr'0 : 0 < r' := lt_trans ha0 hr'.1
      have hr'1 : r' < 1 := lt_trans hr'.2 hb1
      have hv_ge : 1 - b ^ 2 ≤ 1 - r' ^ 2 := by nlinarith [hr'.2, hr'0]
      have hvb_pos : 0 < 1 - b ^ 2 := by nlinarith
      have hbound_r : ∀ {h : ℝ → ℝ}, Measurable h → (∀ y, h y ∈ Icc (0 : ℝ) 1) → ∀ x,
          |deriv (fun t => ou1D t h x) r'| ≤ C1 * |x| + C2 := by
        intro h hh hh01 x
        obtain ⟨_, _, _, hpde, h1, h2⟩ := ou1D_derivs_and_pde hr'0 hr'1 hh hh01 x
        have hdiv : deriv (fun t => ou1D t h x) r' =
            (x * deriv (ou1D r' h) x - deriv (deriv (ou1D r' h)) x) / r' :=
          eq_div_of_mul_eq hr'0.ne' (by linarith)
        rw [hdiv, abs_div, abs_of_pos hr'0]
        have hnum : |x * deriv (ou1D r' h) x - deriv (deriv (ou1D r' h)) x| ≤
            |x| / √(1 - b ^ 2) + 2 / (1 - b ^ 2) := by
          refine (abs_sub _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]
            calc |x| * |deriv (ou1D r' h) x| ≤ |x| * (1 / √(1 - r' ^ 2)) :=
                  mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
              _ ≤ |x| * (1 / √(1 - b ^ 2)) :=
                  mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left zero_le_one
                    (Real.sqrt_pos.2 hvb_pos) (Real.sqrt_le_sqrt hv_ge)) (abs_nonneg x)
              _ = |x| / √(1 - b ^ 2) := by ring
          · exact h2.trans (div_le_div_of_nonneg_left (by norm_num) hvb_pos hv_ge)
        calc
          |x * deriv (ou1D r' h) x - deriv (deriv (ou1D r' h)) x| / r'
              ≤ (|x| / √(1 - b ^ 2) + 2 / (1 - b ^ 2)) / a :=
                div_le_div₀ (by positivity) hnum ha0 hr'.1.le
          _ = C1 * |x| + C2 := by
                unfold C1 C2
                field_simp [ha0.ne', hvb_pos.ne', (Real.sqrt_pos.2 hvb_pos).ne']
      have hm1 := ou1D_mem_Icc hf hfδ r' p.1
      have hm2 := ou1D_mem_Icc hg hgδ r' p.2
      have ho1 : ou1D r' f p.1 ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_lt_of_le hδ0 hm1.1, lt_of_le_of_lt hm1.2 (by linarith)⟩
      have ho2 : ou1D r' g p.2 ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_lt_of_le hδ0 hm2.1, lt_of_le_of_lt hm2.2 (by linarith)⟩
      have hL1 : |deriv (fun α => gaussianQuadrant ρ α (ou1D r' g p.2)) (ou1D r' f p.1)| ≤ 1 := by
        rw [deriv_gaussianQuadrant_left hρ ho1 ho2, abs_of_nonneg (cdf_nonneg _ _)]
        exact cdf_le_one _ _
      have hL2 : |deriv (fun β => gaussianQuadrant ρ (ou1D r' f p.1) β) (ou1D r' g p.2)| ≤ 1 := by
        rw [deriv_gaussianQuadrant_right hρ ho1 ho2, abs_of_nonneg (cdf_nonneg _ _)]
        exact cdf_le_one _ _
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have hb1 := hbound_r hf hf01 p.1
      have hb2 := hbound_r hg hg01 p.2
      have h1' := (mul_le_of_le_one_left (abs_nonneg _) hL1).trans hb1
      have h2' := (mul_le_of_le_one_left (abs_nonneg _) hL2).trans hb2
      unfold dom; linarith
    have hmeas_ou (r' : ℝ) {h : ℝ → ℝ} (hh : Measurable h) : Measurable (ou1D r' h) := by
      have : Measurable fun q : ℝ × ℝ => h (r' * q.1 + √(1 - r' ^ 2) * q.2) :=
        hh.comp (by fun_prop)
      exact this.stronglyMeasurable.integral_prod_right'.measurable
    have hψ_d := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioo a b)
      (F := fun r' p => gaussianQuadrant ρ (ou1D r' f p.1) (ou1D r' g p.2))
      (F' := fun r' p =>
        deriv (fun α => gaussianQuadrant ρ α (ou1D r' g p.2)) (ou1D r' f p.1) *
            deriv (fun t => ou1D t f p.1) r' +
          deriv (fun β => gaussianQuadrant ρ (ou1D r' f p.1) β) (ou1D r' g p.2) *
            deriv (fun t => ou1D t g p.2) r')
      (bound := dom) hIoo
      (Filter.eventually_of_mem hIoo fun r' _ =>
        (Measurable.gaussianQuadrant hρ.le
          ((hmeas_ou r' hf).comp measurable_fst)
          ((hmeas_ou r' hg).comp measurable_snd)).aestronglyMeasurable)
      (Integrable.of_bound
        (Measurable.gaussianQuadrant hρ.le
          ((hmeas_ou r hf).comp measurable_fst)
          ((hmeas_ou r hg).comp measurable_snd)).aestronglyMeasurable
        1 (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs, abs_of_nonneg (gaussianQuadrant_nonneg _ _ _)]
          exact gaussianQuadrant_le_one _ _ _))
      ?_ (ae_of_all _ hdom_le) hdom_int (ae_of_all _ fun p r' hr' => hD_pt r' hr' p))
    · refine ⟨_, hψ_d.2, ?_⟩
      suffices hmul : r * ∫ p, (deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1) *
            deriv (fun t => ou1D t f p.1) r +
          deriv (fun β => gaussianQuadrant ρ (u p.1) β) (v p.2) *
            deriv (fun t => ou1D t g p.2) r) ∂correlatedGaussian ρ ≤ 0 by
        exact nonpos_of_mul_nonpos_right hmul hr.1
      rw [← integral_const_mul]
      have hu_all := fun x => ou1D_derivs_and_pde hr.1 hr.2 hf hf01 x
      have hv_all := fun y => ou1D_derivs_and_pde hr.1 hr.2 hg hg01 y
      set Cu := max (1 / √(1 - r ^ 2)) (2 / (1 - r ^ 2))
      have hu_d1 : Differentiable ℝ u := fun x => (hu_all x).1.differentiableAt
      have hu_d2 : Differentiable ℝ (deriv u) := fun x => (hu_all x).2.1.differentiableAt
      have hv_d1 : Differentiable ℝ v := fun y => (hv_all y).1.differentiableAt
      have hv_d2 : Differentiable ℝ (deriv v) := fun y => (hv_all y).2.1.differentiableAt
      have hCu1 : ∀ x, |deriv u x| ≤ Cu := fun x => (hu_all x).2.2.2.2.1.trans (le_max_left _ _)
      have hCu2 : ∀ x, |deriv (deriv u) x| ≤ Cu := fun x =>
        (hu_all x).2.2.2.2.2.trans (le_max_right _ _)
      have hCv1 : ∀ y, |deriv v y| ≤ Cu := fun y => (hv_all y).2.2.2.2.1.trans (le_max_left _ _)
      have hCv2 : ∀ y, |deriv (deriv v) y| ≤ Cu := fun y =>
        (hv_all y).2.2.2.2.2.trans (le_max_right _ _)
      have hibp1 := heatflow_ibp_left hρ0 hρ1 hδ0 hδ1 hu_mem hv_mem hu_d1 hu_d2 hv_d1 hCu1 hCu2 hCv1
      have hibp2_swap :=
        heatflow_ibp_left hρ0 hρ1 hδ0 hδ1 hv_mem hu_mem hv_d1 hv_d2 hu_d1 hCv1 hCv2 hCu1
      have hsw : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
          (correlatedGaussian ρ) (correlatedGaussian ρ) :=
        ⟨measurable_swap, correlatedGaussian_map_swap hρ.le⟩
      have hrew_pde : ∀ p : ℝ × ℝ,
          r * (deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1) *
              deriv (fun t => ou1D t f p.1) r +
            deriv (fun β => gaussianQuadrant ρ (u p.1) β) (v p.2) *
              deriv (fun t => ou1D t g p.2) r) =
            (p.1 * deriv u p.1 - deriv (deriv u) p.1) *
              deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1) +
            (p.2 * deriv v p.2 - deriv (deriv v) p.2) *
              deriv (fun α => gaussianQuadrant ρ α (u p.1)) (v p.2) := fun p => by
        have hp1 := (hu_all p.1).2.2.2.1
        have hp2 := (hv_all p.2).2.2.2.1
        have hsym : deriv (fun β => gaussianQuadrant ρ (u p.1) β) (v p.2) =
            deriv (fun α => gaussianQuadrant ρ α (u p.1)) (v p.2) := by
          simp_rw [gaussianQuadrant_comm hρ.le (u p.1)]
        rw [hsym]
        linear_combination
          deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1) * hp1 +
          deriv (fun α => gaussianQuadrant ρ α (u p.1)) (v p.2) * hp2
      have hI1 : Integrable (fun p : ℝ × ℝ => (p.1 * deriv u p.1 - deriv (deriv u) p.1) *
          deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1)) (correlatedGaussian ρ) := by
        have hfst : Integrable (fun p : ℝ × ℝ => |p.1|) (correlatedGaussian ρ) :=
          (⟨measurable_fst, correlatedGaussian_map_fst ρ⟩ :
            MeasurePreserving Prod.fst (correlatedGaussian ρ)
              (gaussianReal 0 1)).integrable_comp_of_integrable
            ((memLp_id_gaussianReal 1).integrable le_rfl).abs
        refine ((hfst.mul_const Cu).add (integrable_const Cu)).mono' ?_ (ae_of_all _ fun p => ?_)
        · have hL : Measurable (fun p : ℝ × ℝ =>
              deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1)) := by
            have : (fun p : ℝ × ℝ => deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1)) =
                fun p => Φ ((gaussianQuantile (v p.2) - ρ * gaussianQuantile (u p.1)) /
                  √(1 - ρ ^ 2)) :=
              funext fun p => deriv_gaussianQuadrant_left hρ (hu_oo p.1) (hv_oo p.2)
            rw [this]
            have hcu : Continuous fun x => gaussianQuantile (u x) :=
              continuous_iff_continuousAt.2 fun x =>
                (continuousAt_gaussianQuantile (hu_oo x)).comp hu_d1.continuous.continuousAt
            have hcv : Continuous fun y => gaussianQuantile (v y) :=
              continuous_iff_continuousAt.2 fun y =>
                (continuousAt_gaussianQuantile (hv_oo y)).comp hv_d1.continuous.continuousAt
            exact ((continuous_cdf_gaussianReal 0 one_ne_zero).comp
              (((hcv.comp continuous_snd).sub
                (continuous_const.mul (hcu.comp continuous_fst))).div_const _)).measurable
          exact (((measurable_fst.mul (hu_d2.continuous.measurable.comp measurable_fst)).sub
            ((measurable_deriv (deriv u)).comp measurable_fst)).mul hL).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_mul]
          dsimp only [Pi.add_apply]
          have hL : |deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1)| ≤ 1 := by
            rw [deriv_gaussianQuadrant_left hρ (hu_oo p.1) (hv_oo p.2),
              abs_of_nonneg (cdf_nonneg _ _)]
            exact cdf_le_one _ _
          refine (mul_le_of_le_one_right (abs_nonneg _) hL).trans
            ((abs_sub _ _).trans (add_le_add ?_ (hCu2 p.1)))
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hCu1 p.1) (abs_nonneg _)
      have hI2 : Integrable (fun p : ℝ × ℝ => (p.2 * deriv v p.2 - deriv (deriv v) p.2) *
          deriv (fun α => gaussianQuadrant ρ α (u p.1)) (v p.2)) (correlatedGaussian ρ) := by
        have hsnd : Integrable (fun p : ℝ × ℝ => |p.2|) (correlatedGaussian ρ) :=
          (⟨measurable_snd, correlatedGaussian_map_snd hρ.le⟩ :
            MeasurePreserving Prod.snd (correlatedGaussian ρ)
              (gaussianReal 0 1)).integrable_comp_of_integrable
            ((memLp_id_gaussianReal 1).integrable le_rfl).abs
        refine ((hsnd.mul_const Cu).add (integrable_const Cu)).mono' ?_ (ae_of_all _ fun p => ?_)
        · have hL : Measurable (fun p : ℝ × ℝ =>
              deriv (fun α => gaussianQuadrant ρ α (u p.1)) (v p.2)) := by
            have : (fun p : ℝ × ℝ => deriv (fun α => gaussianQuadrant ρ α (u p.1)) (v p.2)) =
                fun p => Φ ((gaussianQuantile (u p.1) - ρ * gaussianQuantile (v p.2)) /
                  √(1 - ρ ^ 2)) :=
              funext fun p => deriv_gaussianQuadrant_left hρ (hv_oo p.2) (hu_oo p.1)
            rw [this]
            have hcu : Continuous fun x => gaussianQuantile (u x) :=
              continuous_iff_continuousAt.2 fun x =>
                (continuousAt_gaussianQuantile (hu_oo x)).comp hu_d1.continuous.continuousAt
            have hcv : Continuous fun y => gaussianQuantile (v y) :=
              continuous_iff_continuousAt.2 fun y =>
                (continuousAt_gaussianQuantile (hv_oo y)).comp hv_d1.continuous.continuousAt
            exact ((continuous_cdf_gaussianReal 0 one_ne_zero).comp
              (((hcu.comp continuous_fst).sub
                (continuous_const.mul (hcv.comp continuous_snd))).div_const _)).measurable
          exact (((measurable_snd.mul (hv_d2.continuous.measurable.comp measurable_snd)).sub
            ((measurable_deriv (deriv v)).comp measurable_snd)).mul hL).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_mul]
          dsimp only [Pi.add_apply]
          have hL : |deriv (fun α => gaussianQuadrant ρ α (u p.1)) (v p.2)| ≤ 1 := by
            rw [deriv_gaussianQuadrant_left hρ (hv_oo p.2) (hu_oo p.1),
              abs_of_nonneg (cdf_nonneg _ _)]
            exact cdf_le_one _ _
          refine (mul_le_of_le_one_right (abs_nonneg _) hL).trans
            ((abs_sub _ _).trans (add_le_add ?_ (hCv2 p.2)))
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hCv1 p.2) (abs_nonneg _)
      have hibp2 : ∫ p, (p.2 * deriv v p.2 - deriv (deriv v) p.2) *
          deriv (fun α => gaussianQuadrant ρ α (u p.1)) (v p.2) ∂correlatedGaussian ρ =
          ∫ p, (deriv (fun β => deriv (fun β => gaussianQuadrant ρ (u p.1) β) β) (v p.2) *
              deriv v p.2 ^ 2 +
            ρ * deriv (fun α => deriv (fun β => gaussianQuadrant ρ α β) (v p.2)) (u p.1) *
              deriv v p.2 * deriv u p.1) ∂correlatedGaussian ρ := by
        have hL : ∫ p, (p.2 * deriv v p.2 - deriv (deriv v) p.2) *
              deriv (fun α => gaussianQuadrant ρ α (u p.1)) (v p.2) ∂correlatedGaussian ρ =
            ∫ p, (p.1 * deriv v p.1 - deriv (deriv v) p.1) *
              deriv (fun α => gaussianQuadrant ρ α (u p.2)) (v p.1) ∂correlatedGaussian ρ :=
          hsw.integral_comp' (g := fun p => (p.1 * deriv v p.1 - deriv (deriv v) p.1) *
            deriv (fun α => gaussianQuadrant ρ α (u p.2)) (v p.1))
        have hR : ∫ p, (deriv (fun α => deriv (fun α => gaussianQuadrant ρ α (u p.2)) α) (v p.1) *
              deriv v p.1 ^ 2 +
            ρ * deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (v p.1)) (u p.2) *
              deriv v p.1 * deriv u p.2) ∂correlatedGaussian ρ =
            ∫ p, (deriv (fun α => deriv (fun α => gaussianQuadrant ρ α (u p.1)) α) (v p.2) *
              deriv v p.2 ^ 2 +
            ρ * deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (v p.2)) (u p.1) *
              deriv v p.2 * deriv u p.1) ∂correlatedGaussian ρ :=
          (hsw.integral_comp' (g := fun p =>
            deriv (fun α => deriv (fun α => gaussianQuadrant ρ α (u p.2)) α) (v p.1) *
              deriv v p.1 ^ 2 +
            ρ * deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (v p.1)) (u p.2) *
              deriv v p.1 * deriv u p.2)).symm
        rw [hL, hibp2_swap, hR]
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        have h1 : deriv (fun α => deriv (fun α => gaussianQuadrant ρ α (u p.1)) α) (v p.2) =
            deriv (fun β => deriv (fun β => gaussianQuadrant ρ (u p.1) β) β) (v p.2) := by
          simp_rw [gaussianQuadrant_comm hρ.le (u p.1)]
        have h2 : deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (v p.2)) (u p.1) =
            deriv (fun α => deriv (fun β => gaussianQuadrant ρ α β) (v p.2)) (u p.1) := by
          refine congrArg (fun F => deriv F (u p.1)) (funext fun α => ?_)
          simp_rw [gaussianQuadrant_comm hρ.le α]
        dsimp only
        rw [h1, h2]
      rw [integral_congr_ae (ae_of_all _ hrew_pde), integral_add hI1 hI2, hibp1, hibp2]
      have hquad : ∀ p : ℝ × ℝ,
          (deriv (fun α => deriv (fun α => gaussianQuadrant ρ α (v p.2)) α) (u p.1) *
              deriv u p.1 ^ 2 +
            ρ * deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (u p.1)) (v p.2) *
              deriv u p.1 * deriv v p.2) +
          (deriv (fun β => deriv (fun β => gaussianQuadrant ρ (u p.1) β) β) (v p.2) *
              deriv v p.2 ^ 2 +
            ρ * deriv (fun α => deriv (fun β => gaussianQuadrant ρ α β) (v p.2)) (u p.1) *
              deriv v p.2 * deriv u p.1) =
            (![deriv u p.1, deriv v p.2]) ⬝ᵥ
              (rhoHessian ρ (gaussianQuadrant ρ) (u p.1) (v p.2) *ᵥ
                ![deriv u p.1, deriv v p.2]) := by
        intro p
        rw [rhoHessian_def]
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
        ring
      have hR1_int : Integrable (fun p : ℝ × ℝ =>
          deriv (fun α => deriv (fun α => gaussianQuadrant ρ α (v p.2)) α) (u p.1) *
              deriv u p.1 ^ 2 +
            ρ * deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) (u p.1)) (v p.2) *
              deriv u p.1 * deriv v p.2) (correlatedGaussian ρ) := by
        have hcomp : IsCompact (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := isCompact_Icc.prod isCompact_Icc
        have hIcc_sub : Icc δ (1 - δ) ×ˢ Icc δ (1 - δ) ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 :=
          Set.prod_mono (fun t ht => ⟨lt_of_lt_of_le hδ0 ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
            (fun t ht => ⟨lt_of_lt_of_le hδ0 ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
        have h1c : ContinuousOn (fun q : ℝ × ℝ =>
            deriv (fun α => deriv (fun α => gaussianQuadrant ρ α q.2) α) q.1)
            (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := by
          refine ContinuousOn.congr ?_ fun q hq =>
            (hasDerivAt_gaussianQuadrant_left_left hρ (hIcc_sub hq).1 (hIcc_sub hq).2).deriv
          have hq1 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.1) _ :=
            continuousOn_gaussianQuantile.comp continuousOn_fst fun q hq => (hIcc_sub hq).1
          have hq2 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.2) _ :=
            continuousOn_gaussianQuantile.comp continuousOn_snd fun q hq => (hIcc_sub hq).2
          exact (continuousOn_const.mul ((continuous_gaussianPDFReal 0 1).comp_continuousOn hq1
            |>.inv₀ fun q _ => (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne')).mul
            ((continuous_gaussianPDFReal 0 1).comp_continuousOn
              ((hq2.sub (continuousOn_const.mul hq1)).div_const _))
        have h2c : ContinuousOn (fun q : ℝ × ℝ =>
            deriv (fun β => deriv (fun α => gaussianQuadrant ρ α β) q.1) q.2)
            (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := by
          refine ContinuousOn.congr ?_ fun q hq =>
            (hasDerivAt_gaussianQuadrant_left_right hρ (hIcc_sub hq).1 (hIcc_sub hq).2).deriv
          have hq1 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.1) _ :=
            continuousOn_gaussianQuantile.comp continuousOn_fst fun q hq => (hIcc_sub hq).1
          have hq2 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.2) _ :=
            continuousOn_gaussianQuantile.comp continuousOn_snd fun q hq => (hIcc_sub hq).2
          exact (continuousOn_const.mul ((continuous_gaussianPDFReal 0 1).comp_continuousOn hq2
            |>.inv₀ fun q _ => (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne')).mul
            ((continuous_gaussianPDFReal 0 1).comp_continuousOn
              ((hq2.sub (continuousOn_const.mul hq1)).div_const _))
        obtain ⟨M1, hM1⟩ := hcomp.exists_bound_of_continuousOn h1c
        obtain ⟨M2, hM2⟩ := hcomp.exists_bound_of_continuousOn h2c
        have hM1_nn : 0 ≤ M1 := (norm_nonneg _).trans (hM1 (u 0, v 0) ⟨hu_mem 0, hv_mem 0⟩)
        have hM2_nn : 0 ≤ M2 := (norm_nonneg _).trans (hM2 (u 0, v 0) ⟨hu_mem 0, hv_mem 0⟩)
        have hCu_nn : 0 ≤ Cu := (abs_nonneg _).trans (hCu1 0)
        refine Integrable.of_bound ?_ (M1 * Cu ^ 2 + ρ * M2 * Cu ^ 2) (ae_of_all _ fun p => ?_)
        · have hm1 := (h1c.comp_continuous ((hu_d1.continuous.comp continuous_fst).prodMk
            (hv_d1.continuous.comp continuous_snd)) fun p => ⟨hu_mem p.1, hv_mem p.2⟩).measurable
          have hm2 := (h2c.comp_continuous ((hu_d1.continuous.comp continuous_fst).prodMk
            (hv_d1.continuous.comp continuous_snd)) fun p => ⟨hu_mem p.1, hv_mem p.2⟩).measurable
          exact ((hm1.mul ((hu_d2.continuous.measurable.comp measurable_fst).pow_const 2)).add
            (((measurable_const.mul hm2).mul (hu_d2.continuous.measurable.comp measurable_fst)).mul
              (hv_d2.continuous.measurable.comp measurable_snd))).aestronglyMeasurable
        · rw [Real.norm_eq_abs]
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_pow]
            exact mul_le_mul (hM1 (u p.1, v p.2) ⟨hu_mem _, hv_mem _⟩)
              (pow_le_pow_left₀ (abs_nonneg _) (hCu1 _) 2) (sq_nonneg _) hM1_nn
          · rw [abs_mul, abs_mul, abs_mul, abs_of_pos hρ0, sq, ← mul_assoc]
            exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left
              (hM2 (u p.1, v p.2) ⟨hu_mem _, hv_mem _⟩) hρ0.le) (hCu1 _) (abs_nonneg _)
              (by positivity)) (hCv1 _) (abs_nonneg _) (by positivity)
      have hR2_int : Integrable (fun p : ℝ × ℝ =>
          deriv (fun β => deriv (fun β => gaussianQuadrant ρ (u p.1) β) β) (v p.2) *
              deriv v p.2 ^ 2 +
            ρ * deriv (fun α => deriv (fun β => gaussianQuadrant ρ α β) (v p.2)) (u p.1) *
              deriv v p.2 * deriv u p.1) (correlatedGaussian ρ) := by
        have hcomp : IsCompact (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := isCompact_Icc.prod isCompact_Icc
        have hIcc_sub : Icc δ (1 - δ) ×ˢ Icc δ (1 - δ) ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 :=
          Set.prod_mono (fun t ht => ⟨lt_of_lt_of_le hδ0 ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
            (fun t ht => ⟨lt_of_lt_of_le hδ0 ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
        have h1c : ContinuousOn (fun q : ℝ × ℝ =>
            deriv (fun β => deriv (fun β => gaussianQuadrant ρ q.1 β) β) q.2)
            (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := by
          refine ContinuousOn.congr ?_ fun q hq =>
            (hasDerivAt_gaussianQuadrant_right_right hρ (hIcc_sub hq).1 (hIcc_sub hq).2).deriv
          have hq1 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.1) _ :=
            continuousOn_gaussianQuantile.comp continuousOn_fst fun q hq => (hIcc_sub hq).1
          have hq2 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.2) _ :=
            continuousOn_gaussianQuantile.comp continuousOn_snd fun q hq => (hIcc_sub hq).2
          exact (continuousOn_const.mul ((continuous_gaussianPDFReal 0 1).comp_continuousOn hq2
            |>.inv₀ fun q _ => (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne')).mul
            ((continuous_gaussianPDFReal 0 1).comp_continuousOn
              ((hq1.sub (continuousOn_const.mul hq2)).div_const _))
        have h2c : ContinuousOn (fun q : ℝ × ℝ =>
            deriv (fun α => deriv (fun β => gaussianQuadrant ρ α β) q.2) q.1)
            (Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)) := by
          refine ContinuousOn.congr ?_ fun q hq =>
            (hasDerivAt_gaussianQuadrant_right_left hρ (hIcc_sub hq).1 (hIcc_sub hq).2).deriv
          have hq1 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.1) _ :=
            continuousOn_gaussianQuantile.comp continuousOn_fst fun q hq => (hIcc_sub hq).1
          have hq2 : ContinuousOn (fun q : ℝ × ℝ => gaussianQuantile q.2) _ :=
            continuousOn_gaussianQuantile.comp continuousOn_snd fun q hq => (hIcc_sub hq).2
          exact (continuousOn_const.mul ((continuous_gaussianPDFReal 0 1).comp_continuousOn hq1
            |>.inv₀ fun q _ => (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne')).mul
            ((continuous_gaussianPDFReal 0 1).comp_continuousOn
              ((hq1.sub (continuousOn_const.mul hq2)).div_const _))
        obtain ⟨M1, hM1⟩ := hcomp.exists_bound_of_continuousOn h1c
        obtain ⟨M2, hM2⟩ := hcomp.exists_bound_of_continuousOn h2c
        have hM1_nn : 0 ≤ M1 := (norm_nonneg _).trans (hM1 (u 0, v 0) ⟨hu_mem 0, hv_mem 0⟩)
        have hM2_nn : 0 ≤ M2 := (norm_nonneg _).trans (hM2 (u 0, v 0) ⟨hu_mem 0, hv_mem 0⟩)
        have hCu_nn : 0 ≤ Cu := (abs_nonneg _).trans (hCu1 0)
        refine Integrable.of_bound ?_ (M1 * Cu ^ 2 + ρ * M2 * Cu ^ 2) (ae_of_all _ fun p => ?_)
        · have hm1 := (h1c.comp_continuous ((hu_d1.continuous.comp continuous_fst).prodMk
            (hv_d1.continuous.comp continuous_snd)) fun p => ⟨hu_mem p.1, hv_mem p.2⟩).measurable
          have hm2 := (h2c.comp_continuous ((hu_d1.continuous.comp continuous_fst).prodMk
            (hv_d1.continuous.comp continuous_snd)) fun p => ⟨hu_mem p.1, hv_mem p.2⟩).measurable
          exact ((hm1.mul ((hv_d2.continuous.measurable.comp measurable_snd).pow_const 2)).add
            (((measurable_const.mul hm2).mul (hv_d2.continuous.measurable.comp measurable_snd)).mul
              (hu_d2.continuous.measurable.comp measurable_fst))).aestronglyMeasurable
        · rw [Real.norm_eq_abs]
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_pow]
            exact mul_le_mul (hM1 (u p.1, v p.2) ⟨hu_mem _, hv_mem _⟩)
              (pow_le_pow_left₀ (abs_nonneg _) (hCv1 _) 2) (sq_nonneg _) hM1_nn
          · rw [abs_mul, abs_mul, abs_mul, abs_of_pos hρ0, sq, ← mul_assoc]
            exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left
              (hM2 (u p.1, v p.2) ⟨hu_mem _, hv_mem _⟩) hρ0.le) (hCv1 _) (abs_nonneg _)
              (by positivity)) (hCu1 _) (abs_nonneg _) (by positivity)
      rw [← integral_add hR1_int hR2_int, integral_congr_ae (ae_of_all _ hquad)]
      exact integral_nonpos fun p =>
        dotProduct_mulVec_rhoHessian_gaussianQuadrant_nonpos hρ0 hρ1 (hu_oo p.1) (hv_oo p.2) _
    · have hfu_m : Measurable (fun x => deriv (fun t => ou1D t f x) r) := by
        have heq : (fun x => deriv (fun t => ou1D t f x) r) =
            fun x => ∫ y, mehlerKernelDr r x y * f y :=
          funext fun x => (ou1D_derivs_and_pde hr.1 hr.2 hf hf01 x).2.2.1.deriv
        rw [heq]
        have hm : Measurable fun q : ℝ × ℝ => mehlerKernelDr r q.1 q.2 * f q.2 :=
          (measurable_mehlerKernelDr_prod r).mul (hf.comp measurable_snd)
        exact hm.stronglyMeasurable.integral_prod_right'.measurable
      have hgv_m : Measurable (fun y => deriv (fun t => ou1D t g y) r) := by
        have heq : (fun y => deriv (fun t => ou1D t g y) r) =
            fun y => ∫ z, mehlerKernelDr r y z * g z :=
          funext fun y => (ou1D_derivs_and_pde hr.1 hr.2 hg hg01 y).2.2.1.deriv
        rw [heq]
        have hm : Measurable fun q : ℝ × ℝ => mehlerKernelDr r q.1 q.2 * g q.2 :=
          (measurable_mehlerKernelDr_prod r).mul (hg.comp measurable_snd)
        exact hm.stronglyMeasurable.integral_prod_right'.measurable
      have hcu : Continuous fun x => gaussianQuantile (u x) :=
        continuous_iff_continuousAt.2 fun x =>
          (continuousAt_gaussianQuantile (hu_oo x)).comp
            ((Differentiable.continuous
              (fun x => (ou1D_derivs_and_pde hr.1 hr.2 hf hf01 x).1.differentiableAt)).continuousAt)
      have hcv : Continuous fun y => gaussianQuantile (v y) :=
        continuous_iff_continuousAt.2 fun y =>
          (continuousAt_gaussianQuantile (hv_oo y)).comp
            ((Differentiable.continuous
              (fun y => (ou1D_derivs_and_pde hr.1 hr.2 hg hg01 y).1.differentiableAt)).continuousAt)
      have hL1m : Measurable (fun p : ℝ × ℝ =>
          deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1)) := by
        have : (fun p : ℝ × ℝ => deriv (fun α => gaussianQuadrant ρ α (v p.2)) (u p.1)) =
            fun p => Φ ((gaussianQuantile (v p.2) - ρ * gaussianQuantile (u p.1)) /
              √(1 - ρ ^ 2)) :=
          funext fun p => deriv_gaussianQuadrant_left hρ (hu_oo p.1) (hv_oo p.2)
        rw [this]
        exact ((continuous_cdf_gaussianReal 0 one_ne_zero).comp
          (((hcv.comp continuous_snd).sub
            (continuous_const.mul (hcu.comp continuous_fst))).div_const _)).measurable
      have hL2m : Measurable (fun p : ℝ × ℝ =>
          deriv (fun β => gaussianQuadrant ρ (u p.1) β) (v p.2)) := by
        have : (fun p : ℝ × ℝ => deriv (fun β => gaussianQuadrant ρ (u p.1) β) (v p.2)) =
            fun p => Φ ((gaussianQuantile (u p.1) - ρ * gaussianQuantile (v p.2)) /
              √(1 - ρ ^ 2)) :=
          funext fun p => deriv_gaussianQuadrant_right hρ (hu_oo p.1) (hv_oo p.2)
        rw [this]
        exact ((continuous_cdf_gaussianReal 0 one_ne_zero).comp
          (((hcu.comp continuous_fst).sub
            (continuous_const.mul (hcv.comp continuous_snd))).div_const _)).measurable
      exact ((hL1m.mul (hfu_m.comp measurable_fst)).add
        (hL2m.mul (hgv_m.comp measurable_snd))).aestronglyMeasurable
  have hψ_anti : AntitoneOn ψ (Ioo 0 1) :=
    antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
      (fun r hr => (hψ_deriv_nonpos r hr).choose_spec.1.continuousAt.continuousWithinAt)
      (fun r hr =>
        (hψ_deriv_nonpos r (interior_subset hr)).choose_spec.1.differentiableAt
          |>.differentiableWithinAt)
      fun r hr => by
        obtain ⟨d, hd, hd0⟩ := hψ_deriv_nonpos r (interior_subset hr)
        rwa [hd.deriv]
  have hlim0 : Tendsto ψ (𝓝[>] (0 : ℝ))
      (𝓝 (gaussianQuadrant ρ (∫ x, f x ∂gaussianReal 0 1) (∫ x, g x ∂gaussianReal 0 1))) := by
    have hou0 : ∀ {h : ℝ → ℝ}, Measurable h → (∀ y, h y ∈ Icc (0 : ℝ) 1) → ∀ x,
        Tendsto (fun r => ou1D r h x) (𝓝[>] (0 : ℝ)) (𝓝 (∫ y, h y ∂gaussianReal 0 1)) := by
      intro h hh hh01 x
      obtain ⟨C, hC, c, hc, hdom⟩ := mehlerKernel_dom (a := 0) (b := 1 / 2) (R := |x|)
        (by norm_num) (by norm_num) (by norm_num) (abs_nonneg x)
      set bound : ℝ → ℝ := fun y => C * (1 + |y| + y ^ 2) * rexp (-(c * y ^ 2))
      have hbound_int : Integrable bound :=
        ((integrable_poly_mul_exp_neg_sq hc).const_mul C).congr
          (ae_of_all _ fun y => by unfold bound; ring)
      have hgt : ∫ y, h y ∂gaussianReal 0 1 = ∫ y, mehlerKernel 0 x y * h y := by
        rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        dsimp only
        rw [smul_eq_mul, mehlerKernel_eq_gaussianPDFReal (by norm_num)]
        simp
      rw [hgt]
      have ht := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
        (F := fun r y => mehlerKernel r x y * h y) (f := fun y => mehlerKernel 0 x y * h y) bound
        (Eventually.of_forall fun r => ((measurable_mehlerKernel r x).mul hh).aestronglyMeasurable)
        (Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)) fun r hr =>
          ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_mul]
            exact (mul_le_of_le_one_right (abs_nonneg _)
              (abs_le.2 ⟨by linarith [(hh01 y).1], (hh01 y).2⟩)).trans
              (hdom r ⟨hr.1.le, hr.2.le⟩ x ⟨neg_abs_le x, le_abs_self x⟩ y).1)
        hbound_int
        (ae_of_all _ fun y => by
          have hc0 : ContinuousAt (fun r => mehlerKernel r x y * h y) 0 := by
            refine ((hasDerivAt_mehlerKernel_r (by norm_num : |(0 : ℝ)| < 1) x y).continuousAt).mul
              continuousAt_const
          exact hc0.tendsto.mono_left nhdsWithin_le_nhds)
      refine ht.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with r hr
      exact (ou1D_eq_integral_mehler (abs_lt.2 ⟨by linarith [hr.1], by linarith [hr.2]⟩) hh x).symm
    have hconst : gaussianQuadrant ρ (∫ x, f x ∂gaussianReal 0 1) (∫ x, g x ∂gaussianReal 0 1) =
        ∫ _p, gaussianQuadrant ρ (∫ x, f x ∂gaussianReal 0 1) (∫ x, g x ∂gaussianReal 0 1)
          ∂correlatedGaussian ρ := by simp
    rw [hconst]
    refine tendsto_integral_filter_of_dominated_convergence (μ := correlatedGaussian ρ)
      (l := 𝓝[>] (0 : ℝ))
      (F := fun r p => gaussianQuadrant ρ (ou1D r f p.1) (ou1D r g p.2))
      (f := fun _ =>
        gaussianQuadrant ρ (∫ x, f x ∂gaussianReal 0 1) (∫ x, g x ∂gaussianReal 0 1))
      (fun _ => 1)
      (Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)) fun r _ =>
        (Measurable.gaussianQuadrant hρ.le
          (((hf.comp (by fun_prop : Measurable fun q : ℝ × ℝ =>
              r * q.1 + √(1 -
                r ^ 2) * q.2)).stronglyMeasurable.integral_prod_right'.measurable).comp
            measurable_fst)
          (((hg.comp (by fun_prop : Measurable fun q : ℝ × ℝ =>
              r * q.1 + √(1 -
                r ^ 2) * q.2)).stronglyMeasurable.integral_prod_right'.measurable).comp
            measurable_snd)).aestronglyMeasurable)
      (Eventually.of_forall fun _ => ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gaussianQuadrant_nonneg _ _ _)]
        exact gaussianQuadrant_le_one _ _ _)
      (integrable_const 1)
      (ae_of_all _ fun p =>
        ((continuous_gaussianQuadrant hρ.le).tendsto _).comp
          ((hou0 hf hf01 p.1).prodMk_nhds (hou0 hg hg01 p.2)))
  have hlim1 : Tendsto ψ (𝓝[<] (1 : ℝ))
      (𝓝 (∫ p, gaussianQuadrant ρ (f p.1) (g p.2) ∂correlatedGaussian ρ)) := by
    have hou1 : ∀ {h : ℝ → ℝ}, Measurable h → (∀ y, h y ∈ Icc (0 : ℝ) 1) →
        Tendsto (fun r => ∫ x, |ou1D r h x - h x| ∂gaussianReal 0 1) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      intro h hh hh01
      set H : (Fin 1 → ℝ) → ℝ := fun z => h (z 0)
      have hH_int : Integrable H (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) :=
        Integrable.of_mem_Icc 0 1 (hh.comp (measurable_pi_apply 0)).aemeasurable
          (ae_of_all _ fun z => hh01 _)
      have ht := tendsto_eLpNorm_gaussianNoiseOp_sub hH_int
      have htoReal := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp ht
      simp only [ENNReal.toReal_zero] at htoReal
      refine htoReal.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
      have hr_le : |r| ≤ 1 := abs_le.2 ⟨hr.1.le, hr.2.le⟩
      have hmp := measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) (0 : Fin 1)
      have heq_ou : ∀ z : Fin 1 → ℝ, gaussianNoiseOp r H z = ou1D r h (z 0) := fun z => by
        rw [ou1D_eq_integral]
        unfold gaussianNoiseOp H
        have hm_y : Measurable (fun y : ℝ => h (r * z 0 + √(1 - r ^ 2) * y)) :=
          hh.comp (by fun_prop)
        conv_rhs =>
          rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hm_y.aestronglyMeasurable]
      have hm_ou : Measurable (ou1D r h) :=
        (hh.comp (by fun_prop : Measurable fun q : ℝ × ℝ =>
          r * q.1 + √(1 - r ^ 2) * q.2)).stronglyMeasurable.integral_prod_right'.measurable
      have hm_diff : Measurable (fun x : ℝ => |ou1D r h x - h x|) :=
        continuous_abs.measurable.comp (hm_ou.sub hh)
      have hdiff_int : Integrable (fun x => |ou1D r h x - h x|) (gaussianReal 0 1) :=
        Integrable.of_bound hm_diff.aestronglyMeasurable 2
          (ae_of_all _ fun x => by
            have h1 := ou1D_mem_Icc hh (fun y => ⟨(hh01 y).1, by linarith [(hh01 y).2]⟩) r x
            rw [Real.norm_eq_abs, abs_abs, abs_le]
            exact ⟨by linarith [h1.1, (hh01 x).2], by linarith [h1.2, (hh01 x).1]⟩)
      have heLp :
          (eLpNorm (gaussianNoiseOp r H - H) 1
              (Measure.pi fun _ : Fin 1 => gaussianReal 0 1)).toReal =
            ∫ x, |ou1D r h x - h x| ∂gaussianReal 0 1 := by
        rw [eLpNorm_one_eq_lintegral_eNorm ((hH_int.1.gaussianNoiseOp hr_le).sub hH_int.1)]
        have hint_pi : Integrable (fun z : Fin 1 → ℝ => |gaussianNoiseOp r H z - H z|)
            (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) := by
          have : (fun z : Fin 1 → ℝ => |gaussianNoiseOp r H z - H z|) =
              fun z => |ou1D r h (z 0) - h (z 0)| := funext fun z => by rw [heq_ou z]
          rw [this]
          exact hmp.integrable_comp_of_integrable hdiff_int
        have hcongr :
            ∫⁻ z, ‖(gaussianNoiseOp r H - H) z‖ₑ
              ∂Measure.pi (fun _ : Fin 1 => gaussianReal 0 1) =
            ∫⁻ z, ENNReal.ofReal |gaussianNoiseOp r H z - H z|
              ∂Measure.pi (fun _ : Fin 1 => gaussianReal 0 1) :=
          lintegral_congr fun z => by simp [Real.eNorm_eq_ofReal_abs]
        rw [hcongr,
          ← ofReal_integral_eq_lintegral_ofReal hint_pi (ae_of_all _ fun _ => abs_nonneg _),
          ENNReal.toReal_ofReal (integral_nonneg fun _ => abs_nonneg _)]
        have : (fun z : Fin 1 → ℝ => |gaussianNoiseOp r H z - H z|) =
            fun z => |ou1D r h (z 0) - h (z 0)| := funext fun z => by rw [heq_ou z]
        rw [this]
        conv_rhs =>
          rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hm_diff.aestronglyMeasurable]
      exact heLp
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hsum := (hou1 hf hf01).add (hou1 hg hg01)
    rw [add_zero] at hsum
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1),
      (Metric.tendsto_nhds.1 hsum) ε hε] with r hr hclose
    rw [Real.dist_eq] at hclose ⊢
    have h1 : Integrable (fun p : ℝ × ℝ => gaussianQuadrant ρ (ou1D r f p.1) (ou1D r g p.2))
        (correlatedGaussian ρ) :=
      Integrable.of_bound
        (Measurable.gaussianQuadrant hρ.le
          (((hf.comp (by fun_prop : Measurable fun q : ℝ × ℝ =>
              r * q.1 + √(1 -
                r ^ 2) * q.2)).stronglyMeasurable.integral_prod_right'.measurable).comp
            measurable_fst)
          (((hg.comp (by fun_prop : Measurable fun q : ℝ × ℝ =>
              r * q.1 + √(1 -
                r ^ 2) * q.2)).stronglyMeasurable.integral_prod_right'.measurable).comp
            measurable_snd)).aestronglyMeasurable
        1 (ae_of_all _ fun _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (gaussianQuadrant_nonneg _ _ _)]
          exact gaussianQuadrant_le_one _ _ _)
    have h2 : Integrable (fun p : ℝ × ℝ => gaussianQuadrant ρ (f p.1) (g p.2))
        (correlatedGaussian ρ) :=
      Integrable.of_bound
        (Measurable.gaussianQuadrant hρ.le (hf.comp measurable_fst)
          (hg.comp measurable_snd)).aestronglyMeasurable
        1 (ae_of_all _ fun _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (gaussianQuadrant_nonneg _ _ _)]
          exact gaussianQuadrant_le_one _ _ _)
    have hmf : Measurable (fun x : ℝ => |ou1D r f x - f x|) :=
      continuous_abs.measurable.comp
        (((hf.comp (by fun_prop : Measurable fun q : ℝ × ℝ =>
          r * q.1 + √(1 - r ^ 2) * q.2)).stronglyMeasurable.integral_prod_right'.measurable).sub hf)
    have hmg : Measurable (fun y : ℝ => |ou1D r g y - g y|) :=
      continuous_abs.measurable.comp
        (((hg.comp (by fun_prop : Measurable fun q : ℝ × ℝ =>
          r * q.1 + √(1 - r ^ 2) * q.2)).stronglyMeasurable.integral_prod_right'.measurable).sub hg)
    have hif : Integrable (fun p : ℝ × ℝ => |ou1D r f p.1 - f p.1|) (correlatedGaussian ρ) :=
      Integrable.of_bound (hmf.comp measurable_fst).aestronglyMeasurable
        2 (ae_of_all _ fun p => by
          have hm := ou1D_mem_Icc hf hfδ r p.1
          rw [Real.norm_eq_abs, abs_abs, abs_le]
          exact ⟨by linarith [hm.1, (hf01 p.1).2], by linarith [hm.2, (hf01 p.1).1]⟩)
    have hig : Integrable (fun p : ℝ × ℝ => |ou1D r g p.2 - g p.2|) (correlatedGaussian ρ) :=
      Integrable.of_bound (hmg.comp measurable_snd).aestronglyMeasurable
        2 (ae_of_all _ fun p => by
          have hm := ou1D_mem_Icc hg hgδ r p.2
          rw [Real.norm_eq_abs, abs_abs, abs_le]
          exact ⟨by linarith [hm.1, (hg01 p.2).2], by linarith [hm.2, (hg01 p.2).1]⟩)
    have hdiff : |ψ r - ∫ p, gaussianQuadrant ρ (f p.1) (g p.2) ∂correlatedGaussian ρ| ≤
        ∫ x, |ou1D r f x - f x| ∂gaussianReal 0 1 + ∫ y, |ou1D r g y - g y| ∂gaussianReal 0 1 := by
      rw [← integral_sub h1 h2]
      refine abs_integral_le_integral_abs.trans ?_
      calc
        ∫ p, |gaussianQuadrant ρ (ou1D r f p.1) (ou1D r g p.2) -
            gaussianQuadrant ρ (f p.1) (g p.2)| ∂correlatedGaussian ρ
            ≤ ∫ p, (|ou1D r f p.1 - f p.1| + |ou1D r g p.2 - g p.2|) ∂correlatedGaussian ρ :=
              integral_mono (h1.sub h2).abs (hif.add hig) fun p =>
                abs_gaussianQuadrant_sub_le hρ.le _ _ _ _
        _ = (∫ p, |ou1D r f p.1 - f p.1| ∂correlatedGaussian ρ) +
              (∫ p, |ou1D r g p.2 - g p.2| ∂correlatedGaussian ρ) := integral_add hif hig
        _ = ∫ x, |ou1D r f x - f x| ∂gaussianReal 0 1 +
              ∫ y, |ou1D r g y - g y| ∂gaussianReal 0 1 := by
              have h1' : ∫ x, |ou1D r f x - f x| ∂gaussianReal 0 1 =
                  ∫ p, |ou1D r f p.1 - f p.1| ∂correlatedGaussian ρ := by
                rw [← correlatedGaussian_map_fst ρ,
                  integral_map measurable_fst.aemeasurable hmf.aestronglyMeasurable]
              have h2' : ∫ y, |ou1D r g y - g y| ∂gaussianReal 0 1 =
                  ∫ p, |ou1D r g p.2 - g p.2| ∂correlatedGaussian ρ := by
                rw [← correlatedGaussian_map_snd hρ.le,
                  integral_map measurable_snd.aemeasurable hmg.aestronglyMeasurable]
              rw [h1', h2']
    have hnn : 0 ≤ ∫ x, |ou1D r f x - f x| ∂gaussianReal 0 1 +
        ∫ y, |ou1D r g y - g y| ∂gaussianReal 0 1 :=
      add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
    rw [sub_zero, abs_of_nonneg hnn] at hclose
    exact hdiff.trans_lt hclose
  have hmid : ∀ r ∈ Ioo (0 : ℝ) 1,
      ∫ p, gaussianQuadrant ρ (f p.1) (g p.2) ∂correlatedGaussian ρ ≤ ψ r := fun r hr =>
    le_of_tendsto hlim1 (Filter.eventually_of_mem (Ioo_mem_nhdsLT hr.2) fun r' hr' =>
      hψ_anti hr ⟨lt_trans hr.1 hr'.1, hr'.2⟩ hr'.1.le)
  exact ge_of_tendsto hlim0 (Filter.eventually_of_mem (Ioo_mem_nhdsGT zero_lt_one) fun r hr =>
    hmid r hr)

/-- **One-Dimensional Two-Function Borell Isoperimetric Inequality**: for every `ρ ∈ [0, 1]`,
`TwoFunctionBorellInequality ρ (Fin 1)` holds unconditionally. -/
theorem twoFunctionBorellInequality_fin_one {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    TwoFunctionBorellInequality ρ (Fin 1) := by
  rcases hρ0.eq_or_lt with rfl | hρ0_lt
  · exact twoFunctionBorellInequality_zero (Fin 1)
  rcases hρ1.eq_or_lt with rfl | hρ1_lt
  · exact twoFunctionBorellInequality_one (Fin 1)
  have hρ : |ρ| ≤ 1 := abs_le.2 ⟨by linarith, hρ1⟩
  rw [twoFunctionBorellInequality_iff]
  intro F G hF hG hF01 hG01
  set f : ℝ → ℝ := fun x => F (fun _ => x)
  set g : ℝ → ℝ := fun x => G (fun _ => x)
  have hf : Measurable f := hF.comp (measurable_pi_iff.2 fun _ => measurable_id)
  have hg : Measurable g := hG.comp (measurable_pi_iff.2 fun _ => measurable_id)
  have hmp1 : MeasurePreserving (fun z : Fin 1 → ℝ => z 0)
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) (gaussianReal 0 1) :=
    measurePreserving_eval _ 0
  have hmp2 : MeasurePreserving (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (p.1 0, p.2 0))
      (correlatedGaussianPi (Fin 1) ρ) (correlatedGaussian ρ) :=
    ⟨by fun_prop, correlatedGaussianPi_map_eval (Fin 1) ρ 0⟩
  have hEq1 : ∀ z : Fin 1 → ℝ, F z = f (z 0) := fun z =>
    congrArg F (funext fun i => by fin_cases i; rfl)
  have hEq2 : ∀ z : Fin 1 → ℝ, G z = g (z 0) := fun z =>
    congrArg G (funext fun i => by fin_cases i; rfl)
  have hI_lhs : ∫ p, gaussianQuadrant ρ (F p.1) (G p.2) ∂correlatedGaussianPi (Fin 1) ρ =
      ∫ p, gaussianQuadrant ρ (f p.1) (g p.2) ∂correlatedGaussian ρ := by
    have hcongr : (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => gaussianQuadrant ρ (F p.1) (G p.2)) =
        fun p => gaussianQuadrant ρ (f (p.1 0)) (g (p.2 0)) :=
      funext fun p => by rw [hEq1, hEq2]
    rw [hcongr]
    have hq_m : Measurable (fun p : ℝ × ℝ => gaussianQuadrant ρ (f p.1) (g p.2)) :=
      Measurable.gaussianQuadrant hρ (hf.comp measurable_fst) (hg.comp measurable_snd)
    conv_rhs =>
      rw [← hmp2.map_eq, integral_map hmp2.measurable.aemeasurable hq_m.aestronglyMeasurable]
  have hI_f : ∫ z, F z ∂Measure.pi (fun _ : Fin 1 => gaussianReal 0 1) =
      ∫ x, f x ∂gaussianReal 0 1 := by
    rw [funext hEq1]
    conv_rhs => rw [← hmp1.map_eq,
      integral_map hmp1.measurable.aemeasurable hf.aestronglyMeasurable]
  have hI_g : ∫ z, G z ∂Measure.pi (fun _ : Fin 1 => gaussianReal 0 1) =
      ∫ x, g x ∂gaussianReal 0 1 := by
    rw [funext hEq2]
    conv_rhs => rw [← hmp1.map_eq,
      integral_map hmp1.measurable.aemeasurable hg.aestronglyMeasurable]
  rw [hI_lhs, hI_f, hI_g]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := min (1 / 8 : ℝ) (ε / 4)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 / 4 := (min_le_left _ _).trans_lt (by norm_num)
  have h4δ : 4 * δ ≤ ε := by linarith [min_le_right (1 / 8 : ℝ) (ε / 4)]
  set fδ : ℝ → ℝ := fun x => (1 - 2 * δ) * f x + δ
  set gδ : ℝ → ℝ := fun x => (1 - 2 * δ) * g x + δ
  have hfδ_mem : ∀ x, fδ x ∈ Icc δ (1 - δ) := fun x =>
    ⟨by nlinarith [(hF01 (fun _ => x)).1, hδ1], by nlinarith [(hF01 (fun _ => x)).2, hδ1]⟩
  have hgδ_mem : ∀ x, gδ x ∈ Icc δ (1 - δ) := fun x =>
    ⟨by nlinarith [(hG01 (fun _ => x)).1, hδ1], by nlinarith [(hG01 (fun _ => x)).2, hδ1]⟩
  have hfδ_m : Measurable fδ := (measurable_const.mul hf).add measurable_const
  have hgδ_m : Measurable gδ := (measurable_const.mul hg).add measurable_const
  have hcore := borell_one_dim_interior hρ0_lt hρ1_lt hδ0 hδ1 hfδ_m hgδ_m hfδ_mem hgδ_mem
  have hfδ_diff : ∀ x, |f x - fδ x| ≤ δ := fun x => by
    have h01 := hF01 (fun _ => x)
    have : f x - fδ x = δ * (2 * f x - 1) := by unfold fδ; ring
    rw [this, abs_mul, abs_of_pos hδ0]
    refine mul_le_of_le_one_right hδ0.le (abs_le.2 ⟨by linarith [h01.1], by linarith [h01.2]⟩)
  have hgδ_diff : ∀ x, |g x - gδ x| ≤ δ := fun x => by
    have h01 := hG01 (fun _ => x)
    have : g x - gδ x = δ * (2 * g x - 1) := by unfold gδ; ring
    rw [this, abs_mul, abs_of_pos hδ0]
    refine mul_le_of_le_one_right hδ0.le (abs_le.2 ⟨by linarith [h01.1], by linarith [h01.2]⟩)
  have hf_int : Integrable f (gaussianReal 0 1) :=
    Integrable.of_mem_Icc 0 1 hf.aemeasurable (ae_of_all _ fun x => hF01 _)
  have hg_int : Integrable g (gaussianReal 0 1) :=
    Integrable.of_mem_Icc 0 1 hg.aemeasurable (ae_of_all _ fun x => hG01 _)
  have hfδ_int : Integrable fδ (gaussianReal 0 1) := (hf_int.const_mul _).add (integrable_const _)
  have hgδ_int : Integrable gδ (gaussianReal 0 1) := (hg_int.const_mul _).add (integrable_const _)
  have hmean_f : |(∫ x, fδ x ∂gaussianReal 0 1) - ∫ x, f x ∂gaussianReal 0 1| ≤ δ := by
    rw [abs_sub_comm, ← integral_sub hf_int hfδ_int]
    refine abs_integral_le_integral_abs.trans ?_
    simpa using integral_mono (hf_int.sub hfδ_int).abs (integrable_const δ) hfδ_diff
  have hmean_g : |(∫ x, gδ x ∂gaussianReal 0 1) - ∫ x, g x ∂gaussianReal 0 1| ≤ δ := by
    rw [abs_sub_comm, ← integral_sub hg_int hgδ_int]
    refine abs_integral_le_integral_abs.trans ?_
    simpa using integral_mono (hg_int.sub hgδ_int).abs (integrable_const δ) hgδ_diff
  have hlhs_close :
      ∫ p, gaussianQuadrant ρ (f p.1) (g p.2) ∂correlatedGaussian ρ ≤
        ∫ p, gaussianQuadrant ρ (fδ p.1) (gδ p.2) ∂correlatedGaussian ρ + 2 * δ := by
    have h1 : Integrable (fun p : ℝ × ℝ => gaussianQuadrant ρ (f p.1) (g p.2))
        (correlatedGaussian ρ) :=
      Integrable.of_bound
        (Measurable.gaussianQuadrant hρ (hf.comp measurable_fst)
          (hg.comp measurable_snd)).aestronglyMeasurable
        1 (ae_of_all _ fun _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (gaussianQuadrant_nonneg _ _ _)]
          exact gaussianQuadrant_le_one _ _ _)
    have h2 : Integrable (fun p : ℝ × ℝ => gaussianQuadrant ρ (fδ p.1) (gδ p.2))
        (correlatedGaussian ρ) :=
      Integrable.of_bound
        (Measurable.gaussianQuadrant hρ
          (hfδ_m.comp measurable_fst) (hgδ_m.comp measurable_snd)).aestronglyMeasurable
        1 (ae_of_all _ fun _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (gaussianQuadrant_nonneg _ _ _)]
          exact gaussianQuadrant_le_one _ _ _)
    have h12 : Integrable (fun p : ℝ × ℝ =>
        gaussianQuadrant ρ (f p.1) (g p.2) - gaussianQuadrant ρ (fδ p.1) (gδ p.2))
        (correlatedGaussian ρ) := h1.sub h2
    have hsub := integral_mono h12 (integrable_const (2 * δ)) fun p => by
      have h := abs_gaussianQuadrant_sub_le hρ (f p.1) (g p.2) (fδ p.1) (gδ p.2)
      linarith [(abs_le.1 h).2, hfδ_diff p.1, hgδ_diff p.2]
    rw [integral_sub h1 h2, integral_const, probReal_univ, smul_eq_mul, one_mul] at hsub
    linarith
  have hrhs_close :
      gaussianQuadrant ρ (∫ x, fδ x ∂gaussianReal 0 1) (∫ x, gδ x ∂gaussianReal 0 1) ≤
        gaussianQuadrant ρ (∫ x, f x ∂gaussianReal 0 1) (∫ x, g x ∂gaussianReal 0 1) + 2 * δ := by
    have h := abs_gaussianQuadrant_sub_le hρ
      (∫ x, fδ x ∂gaussianReal 0 1) (∫ x, gδ x ∂gaussianReal 0 1)
      (∫ x, f x ∂gaussianReal 0 1) (∫ x, g x ∂gaussianReal 0 1)
    linarith [(abs_le.1 h).2]
  linarith

/-- **Full `n`-Dimensional Two-Function Borell Isoperimetric Inequality**: for every finite index
type `ι` and `ρ ∈ [0, 1]`, `TwoFunctionBorellInequality ρ ι` holds. -/
theorem twoFunctionBorellInequality_all (ι : Type*) [Fintype ι] {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    TwoFunctionBorellInequality ρ ι :=
  (twoFunctionBorellInequality_fin_one hρ0 hρ1).of_fin_one (abs_le.2 ⟨by linarith, hρ1⟩) ι

/-- **Borell's Isoperimetric Inequality (`ρ ∈ [0, 1]`, general `[0, 1]`-valued functions)**:
for every finite `ι`, `ρ ∈ [0, 1]`, and measurable `f : (ι → ℝ) → [0, 1]`,
`GStab_ρ(f) ≤ Λ_ρ(𝔼 f, 𝔼 f)`. -/
theorem borell_gaussianNoiseStability_le {ι : Type*} [Fintype ι] {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (hf01 : ∀ z, f z ∈ Icc 0 1) :
    gaussianNoiseStability ρ f ≤
      gaussianQuadrant ρ (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1)
        (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1) :=
  (twoFunctionBorellInequality_all ι hρ0 hρ1).gaussianNoiseStability_le hρ0 hρ1 hf hf01

/-- **Borell's Isoperimetric Inequality for negative correlation (`ρ ∈ [-1, 0]`)**:
for every finite `ι`, `ρ ∈ [-1, 0]`, and measurable `f : (ι → ℝ) → [0, 1]`,
`Λ_ρ(𝔼 f, 𝔼 f) ≤ GStab_ρ(f)`. -/
theorem borell_gaussianNoiseStability_ge_of_nonpos {ι : Type*} [Fintype ι] {ρ : ℝ}
    (hρ0 : -1 ≤ ρ) (hρ1 : ρ ≤ 0) {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (hf01 : ∀ z, f z ∈ Icc 0 1) :
    gaussianQuadrant ρ (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1)
        (∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 1) ≤
      gaussianNoiseStability ρ f := by
  have hρ_abs : |ρ| ≤ 1 := abs_le.2 ⟨hρ0, by linarith⟩
  have hneg0 : 0 ≤ -ρ := by linarith
  have hneg1 : -ρ ≤ 1 := by linarith
  set γn := Measure.pi fun _ : ι => gaussianReal 0 1
  set α := ∫ z, f z ∂γn
  have hα0 : 0 ≤ α := integral_nonneg fun z => (hf01 z).1
  have hα1 : α ≤ 1 := by
    have hint : Integrable f γn := Integrable.of_mem_Icc 0 1 hf.aemeasurable (ae_of_all _ hf01)
    simpa using integral_mono hint (integrable_const 1) fun z => (hf01 z).2
  set g : (ι → ℝ) → ℝ := fun z => 1 - f (-z)
  have hg : Measurable g := measurable_const.sub (hf.comp measurable_neg)
  have hg01 : ∀ z, g z ∈ Icc 0 1 := fun z =>
    ⟨by linarith [(hf01 (-z)).2], by linarith [(hf01 (-z)).1]⟩
  have hneg_mp : MeasurePreserving (fun z : ι → ℝ => -z) γn γn := by
    refine ⟨measurable_neg, ?_⟩
    have h := Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1) (f := fun _ => fun x : ℝ => -x)
      fun _ => measurable_neg.aemeasurable
    have hfun : (fun z : ι → ℝ => -z) = fun x i => -x i := rfl
    rw [hfun]
    simpa [gaussianReal_zero_map_neg] using h
  have hEg : ∫ z, g z ∂γn = 1 - α := by
    have hint : Integrable (fun z => f (-z)) γn :=
      hneg_mp.integrable_comp_of_integrable
        (Integrable.of_mem_Icc 0 1 hf.aemeasurable (ae_of_all _ hf01))
    have hneg_int : ∫ z, f (-z) ∂γn = α := by
      conv_rhs =>
        rw [show α = ∫ z, f z ∂γn from rfl, ← hneg_mp.map_eq,
          integral_map hneg_mp.measurable.aemeasurable hf.aestronglyMeasurable]
    rw [integral_sub (integrable_const 1) hint, integral_const, probReal_univ, smul_eq_mul, one_mul,
      hneg_int]
  have hrefl : gaussianQuadrant ρ α α = α - gaussianQuadrant (-ρ) α (1 - α) := by
    have h' := gaussianQuadrant_neg (ρ := -ρ) (by rwa [abs_neg]) hα0 hα1 α
    rwa [neg_neg] at h'
  have hcorr_neg : (correlatedGaussianPi ι ρ).map (fun p => (p.1, -p.2)) =
      correlatedGaussianPi ι (-ρ) := by
    have h1 := Measure.pi_map_pi (μ := fun _ : ι => correlatedGaussian ρ)
      (f := fun _ => fun p : ℝ × ℝ => (p.1, -p.2)) fun _ => by fun_prop
    simp only [correlatedGaussian_map_neg_snd] at h1
    rw [correlatedGaussianPi_eq_map_pi, correlatedGaussianPi_eq_map_pi,
      Measure.map_map (by fun_prop) (by fun_prop), ← h1,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hprod_le : ∫ p, f p.1 * g p.2 ∂correlatedGaussianPi ι (-ρ) ≤
      gaussianQuadrant (-ρ) α (1 - α) := by
    have h1 : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => f p.1 * g p.2)
        (correlatedGaussianPi ι (-ρ)) :=
      Integrable.of_mem_Icc 0 1
        ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aemeasurable
        (ae_of_all _ fun p => ⟨mul_nonneg (hf01 _).1 (hg01 _).1,
          (mul_le_of_le_one_left (hg01 _).1 (hf01 _).2).trans (hg01 _).2⟩)
    have h2 : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => gaussianQuadrant (-ρ) (f p.1) (g p.2))
        (correlatedGaussianPi ι (-ρ)) :=
      Integrable.of_mem_Icc 0 1
        (Measurable.gaussianQuadrant (by rwa [abs_neg]) (hf.comp measurable_fst)
          (hg.comp measurable_snd)).aemeasurable
        (ae_of_all _ fun _ => ⟨gaussianQuadrant_nonneg _ _ _, gaussianQuadrant_le_one _ _ _⟩)
    have hmono := integral_mono h1 h2 fun p =>
      mul_le_gaussianQuadrant hneg0 hneg1 (hf01 _).1 (hf01 _).2 (hg01 _).1 (hg01 _).2
    have htwo' := (twoFunctionBorellInequality_iff.1
      (twoFunctionBorellInequality_all ι hneg0 hneg1)) f g hf hg hf01 hg01
    rw [hEg] at htwo'
    exact hmono.trans htwo'
  have hlhs_eq : ∫ p, f p.1 * g p.2 ∂correlatedGaussianPi ι (-ρ) =
      α - gaussianNoiseStability ρ f := by
    have hfg_m : Measurable (fun p : (ι → ℝ) × (ι → ℝ) => f p.1 * g p.2) :=
      (hf.comp measurable_fst).mul (hg.comp measurable_snd)
    have hneg2_m : Measurable (fun p : (ι → ℝ) × (ι → ℝ) => (p.1, -p.2)) := by fun_prop
    rw [← hcorr_neg, integral_map hneg2_m.aemeasurable hfg_m.aestronglyMeasurable]
    have hpt : (fun p : (ι → ℝ) × (ι → ℝ) => f p.1 * g (-p.2)) =
        fun p => f p.1 - f p.1 * f p.2 := funext fun p => by simp [g, mul_sub]
    simp_rw [hpt]
    have hf1 : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => f p.1) (correlatedGaussianPi ι ρ) :=
      Integrable.of_mem_Icc 0 1 (hf.comp measurable_fst).aemeasurable (ae_of_all _ fun p => hf01 _)
    have hf12 : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => f p.1 * f p.2)
        (correlatedGaussianPi ι ρ) :=
      Integrable.of_mem_Icc 0 1
        ((hf.comp measurable_fst).mul (hf.comp measurable_snd)).aemeasurable
        (ae_of_all _ fun p => ⟨mul_nonneg (hf01 _).1 (hf01 _).1,
          (mul_le_of_le_one_left (hf01 _).1 (hf01 _).2).trans (hf01 _).2⟩)
    have hfst_int : ∫ p, f p.1 ∂correlatedGaussianPi ι ρ = α := by
      conv_rhs =>
        rw [show α = ∫ z, f z ∂Measure.pi (fun _ : ι => gaussianReal 0 1) from rfl,
          ← (measurePreserving_fst_correlatedGaussianPi ι ρ).map_eq,
          integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]
    rw [integral_sub hf1 hf12, hfst_int]
    rfl
  linarith

end BorellHeatFlow

end CslibFrontier.Probability.Gaussian
