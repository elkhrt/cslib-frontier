module

public import CslibFrontier.Foundations.Probability.Gaussian.CDF
public import CslibFrontier.Foundations.Probability.Reasonable
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import CslibFrontier.Foundations.MeasureTheory.Integral.CauchySchwarz
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import CslibFrontier.Foundations.Probability.Gaussian.Moments
import CslibFrontier.Foundations.Probability.Gaussian.Quantile
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.Gaussian.Stein
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian Mills Ratio Bounds and Stein 1-Wasserstein Bound for `|·|`

This module establishes quantitative Gaussian Mills-ratio inequalities and Stein-method analytic
bounds, and proves a 1-Wasserstein Stein bound for the absolute value of a standardized sum of
independent finite-third-moment random variables.

## Main results

* `CslibFrontier.Probability.abs_expect_abs_sum_sub_sqrt_two_div_pi_le`:
  `|𝔼|∑ X_i| - √(2/π)| ≤ 3 ∑ 𝔼|X_i|^3` for independent zero-mean `L^3` summands with unit total
  variance.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Set Filter Topology
open scoped BigOperators NNReal ENNReal

namespace CslibFrontier.Probability

local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

/-! ### Elementary real-analysis helpers -/

/-- Mean value bound for a continuous function with bounded derivative on `(a, b)`. -/
theorem abs_sub_le_of_deriv_le_Ioo {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : ∀ x ∈ Ioo a b, ∃ d, HasDerivAt f d x ∧ |d| ≤ C) :
    |f b - f a| ≤ C * (b - a) := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  obtain ⟨c, hc, hmv⟩ := exists_deriv_eq_slope f hlt hcont
    (fun x hx => (hdiff x hx).choose_spec.1.differentiableAt.differentiableWithinAt)
  obtain ⟨d, hd, hdb⟩ := hdiff c hc
  rw [hd.deriv, eq_div_iff (sub_ne_zero.2 hlt.ne')] at hmv
  rw [← hmv, abs_mul, abs_of_pos (sub_pos.2 hlt)]
  exact mul_le_mul_of_nonneg_right hdb (sub_nonneg.2 hab)

/-- For a differentiable function `f` whose derivative `f'` is `L`-Lipschitz,
`|f(a + u) - f(a) - u * f'(a)| ≤ (L / 2) * u^2`. -/
theorem abs_sub_sub_mul_deriv_le {f f' : ℝ → ℝ} {L : ℝ≥0}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : LipschitzWith L f') (a u : ℝ) :
    |f (a + u) - f a - u * f' a| ≤ (L / 2 : ℝ) * u ^ 2 := by
  have hcomp : Continuous fun t => f' (a + t) :=
    hf'.continuous.comp (continuous_const.add continuous_id)
  have hint : IntervalIntegrable (fun t => f' (a + t) - f' a) volume 0 u :=
    (hcomp.sub continuous_const).intervalIntegrable 0 u
  have hftc : f (a + u) - f a - u * f' a = ∫ t in (0 : ℝ)..u, (f' (a + t) - f' a) := by
    have h1 : ∫ t in (0 : ℝ)..u, f' (a + t) = f (a + u) - f a := by
      have hd : ∀ t ∈ uIcc (0 : ℝ) u, HasDerivAt (fun s => f (a + s)) (f' (a + t)) t :=
        fun t _ =>
          ((hf (a + t)).comp t ((hasDerivAt_id' t).const_add a)).congr_deriv (mul_one _)
      simpa [add_zero] using
        intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcomp.intervalIntegrable 0 u)
    rw [intervalIntegral.integral_sub (hcomp.intervalIntegrable 0 u) intervalIntegrable_const,
      h1, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [hftc]
  have hlip : ∀ t, |f' (a + t) - f' a| ≤ L * |t| := fun t => by
    have := hf'.dist_le_mul (a + t) a
    simpa [Real.dist_eq] using this
  rcases le_total 0 u with hu | hu
  · calc
      |∫ t in (0 : ℝ)..u, (f' (a + t) - f' a)|
          ≤ ∫ t in (0 : ℝ)..u, |f' (a + t) - f' a| :=
            intervalIntegral.abs_integral_le_integral_abs hu
      _ ≤ ∫ t in (0 : ℝ)..u, (L : ℝ) * t :=
            intervalIntegral.integral_mono_on hu hint.abs
              ((continuous_const.mul continuous_id).intervalIntegrable 0 u)
              fun t ht => by simpa [abs_of_nonneg ht.1] using hlip t
      _ = (L / 2 : ℝ) * u ^ 2 := by
            rw [intervalIntegral.integral_const_mul, integral_id]
            ring
  · rw [intervalIntegral.integral_symm u 0, abs_neg]
    calc
      |∫ t in u..(0 : ℝ), (f' (a + t) - f' a)|
          ≤ ∫ t in u..(0 : ℝ), |f' (a + t) - f' a| :=
            intervalIntegral.abs_integral_le_integral_abs hu
      _ ≤ ∫ t in u..(0 : ℝ), (L : ℝ) * (-t) :=
            intervalIntegral.integral_mono_on hu hint.symm.abs
              ((continuous_const.mul continuous_neg).intervalIntegrable u 0)
              fun t ht => by simpa [abs_of_nonpos ht.2] using hlip t
      _ = (L / 2 : ℝ) * u ^ 2 := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, integral_id]
            ring

/-- For a real `L^3` probability measure, `(𝔼[X^2]) * (𝔼|X|) ≤ 𝔼|X|^3`. -/
theorem integral_sq_mul_integral_abs_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : MemLp id 3 ν) :
    (∫ s, s ^ 2 ∂ν) * (∫ s, |s| ∂ν) ≤ ∫ s, |s| ^ 3 ∂ν := by
  have h1 : (∫ s, |s| ∂ν) ≤ √(∫ s, s ^ 2 ∂ν) := by
    refine Real.le_sqrt_of_sq_le ?_
    have hcs := sq_integral_mul_le (P := ν) (f := fun s => |s|) (g := fun _ => (1 : ℝ))
      (by
        simpa only [sq_abs] using
          integrable_pow_of_memLp (n := 3) (by exact_mod_cast hν) (j := 2) (by norm_num))
      (by simpa only [one_pow] using integrable_const (1 : ℝ))
      (by
        simpa using
          integrable_abs_pow_of_memLp (n := 3) (by exact_mod_cast hν) (j := 1) (by norm_num))
    simpa only [mul_one, sq_abs, one_pow, integral_const, probReal_univ, smul_eq_mul] using hcs
  have h2 : √(∫ s, s ^ 2 ∂ν) ^ 3 ≤ ∫ s, |s| ^ 3 ∂ν := sqrt_integral_sq_pow_three_le hν
  have hnn : 0 ≤ ∫ s, s ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  calc
    (∫ s, s ^ 2 ∂ν) * (∫ s, |s| ∂ν)
        ≤ (∫ s, s ^ 2 ∂ν) * √(∫ s, s ^ 2 ∂ν) := mul_le_mul_of_nonneg_left h1 hnn
    _ = √(∫ s, s ^ 2 ∂ν) ^ 3 := by
        rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, Real.sq_sqrt hnn]
    _ ≤ ∫ s, |s| ^ 3 ∂ν := h2

/-- Integrability of a function of `(v_i, W_i)` on `Measure.pi μ` reduces to integrability on the
product `(Measure.pi μ).prod (μ i)` via `measurePreserving_update`. -/
theorem integrable_of_integrable_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : ι)
    {F : (ι → ℝ) → ℝ} (hFm : AEStronglyMeasurable F (Measure.pi μ))
    (hupd : Integrable (fun p : (ι → ℝ) × ℝ => F (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i))) :
    Integrable F (Measure.pi μ) := by
  have hmp := measurePreserving_update μ i
  rw [← hmp.map_eq] at hFm ⊢
  exact (integrable_map_measure hFm hmp.measurable.aemeasurable).2 hupd

/-- Restricting a product measure `Measure.pi μ` to coordinates `{j : ι // j ≠ i}` is measure
preserving. -/
theorem measurePreserving_restrict_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun (v : ι → ℝ) (j : {j : ι // j ≠ i}) => v j.1)
      (Measure.pi μ) (Measure.pi fun j : {j : ι // j ≠ i} => μ j.1) where
  measurable := measurable_pi_iff.2 fun j => measurable_pi_apply j.1
  map_eq := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (measurable_pi_iff.2 fun j => measurable_pi_apply j.1)
      (MeasurableSet.univ_pi hs)]
    let t : ι → Set ℝ := fun k => if h : k = i then Set.univ else s ⟨k, h⟩
    have hpre :
        (fun (v : ι → ℝ) (j : {j : ι // j ≠ i}) => v j.1) ⁻¹' Set.univ.pi s = Set.univ.pi t := by
      ext v
      simp only [Set.mem_preimage, Set.mem_univ_pi, t]
      constructor
      · intro hv k
        split_ifs with hk
        · trivial
        · exact hv ⟨k, hk⟩
      · intro hv ⟨k, hk⟩
        simpa [hk] using hv k
    rw [hpre, Measure.pi_pi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [t, ↓reduceDIte, measure_univ, one_mul]
    refine Finset.prod_bij (fun j hj => (⟨j, (Finset.mem_erase.1 hj).1⟩ : {k : ι // k ≠ i}))
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun k _ => ⟨k.1, Finset.mem_erase.2 ⟨k.2, Finset.mem_univ _⟩, rfl⟩)
      fun j hj => by simp [(Finset.mem_erase.1 hj).1]

/-- Second moment of a sum of independent zero-mean `L^2` random variables equals the sum of
their second moments. -/
theorem integral_sum_sq_eq_sum_integral_sq {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, MemLp id 2 (μ i)) (h₁ : ∀ i, ∫ s, s ∂μ i = 0) :
    ∫ z, (∑ i, z i) ^ 2 ∂Measure.pi μ = ∑ i, ∫ s, s ^ 2 ∂μ i := by
  classical
  set P := Measure.pi μ
  have hmem (i : ι) : MemLp (fun z : ι → ℝ => z i) 2 P :=
    (hμ i).comp_measurePreserving (measurePreserving_eval μ i)
  have hsq : (fun z : ι → ℝ => (∑ i, z i) ^ 2) = fun z => ∑ i, ∑ j, z i * z j := funext fun z => by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  have hmul_int (i j : ι) : Integrable (fun z : ι → ℝ => z i * z j) P :=
    (hmem i).integrable_mul (hmem j)
  rw [hsq, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hmul_int i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hmul_int i j, Finset.sum_eq_single i]
  · have h1 : ∫ z, z i * z i ∂P = ∫ z, (fun s : ℝ => s ^ 2) (Function.eval i z) ∂P :=
      integral_congr_ae (ae_of_all _ fun z => (sq (z i)).symm)
    rw [h1, ← integral_map (measurePreserving_eval μ i).measurable.aemeasurable
      (continuous_pow 2).aestronglyMeasurable, (measurePreserving_eval μ i).map_eq]
  · intro j _ hji
    have hint : Integrable (fun z : ι → ℝ => z i * z j) P := hmul_int i j
    rw [← integral_integral_update μ hint j]
    refine integral_eq_zero_of_ae (ae_of_all _ fun v => ?_)
    have hupd : (fun u => Function.update v j u i * Function.update v j u j) =
        fun u => v i * u := funext fun u => by
      rw [Function.update_of_ne hji.symm, Function.update_self]
    dsimp only
    rw [hupd, integral_const_mul, h₁ j, mul_zero]; rfl
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Sum of independent zero-mean `L^2` random variables satisfies `𝔼|∑ X_i| ≤ √(∑ 𝔼[X_i^2])`. -/
theorem integral_abs_sum_le_sqrt_sum_sq {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, MemLp id 2 (μ i)) (h₁ : ∀ i, ∫ s, s ∂μ i = 0) :
    ∫ z, |∑ i, z i| ∂Measure.pi μ ≤ √(∑ i, ∫ s, s ^ 2 ∂μ i) := by
  set P := Measure.pi μ
  have hW : MemLp (fun z : ι → ℝ => ∑ i, z i) 2 P :=
    memLp_finsetSum _ fun i _ => (hμ i).comp_measurePreserving (measurePreserving_eval μ i)
  refine Real.le_sqrt_of_sq_le ?_
  rw [← integral_sum_sq_eq_sum_integral_sq μ hμ h₁]
  have hcs := sq_integral_mul_le (P := P) (f := fun z => |∑ i, z i|) (g := fun _ => (1 : ℝ))
    (by simpa only [sq_abs] using hW.integrable_sq)
    (by simpa only [one_pow] using integrable_const (1 : ℝ))
    (by simpa using (hW.integrable one_le_two).abs)
  simpa only [mul_one, sq_abs, one_pow, integral_const, probReal_univ, smul_eq_mul] using hcs

/-! ### Mills ratio bounds -/

/-- The Gaussian Mills ratio `M(x) = (1 - Φ(x)) / φ(x)`. -/
noncomputable def millsRatio (x : ℝ) : ℝ :=
  (1 - Φ x) / φ x

/-- Characterization of `millsRatio` as `(1 - Φ(x)) / φ(x)`. -/
theorem millsRatio_eq_div (x : ℝ) : millsRatio x = (1 - Φ x) / φ x := by
  unfold millsRatio; rfl

/-- Standard Gaussian PDF vanishes at `+∞`. -/
theorem tendsto_gaussianPDFReal_zero_one_atTop : Tendsto φ atTop (𝓝 0) := by
  simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
  have harg : Tendsto (fun t : ℝ => -(t ^ 2) / (2 * 1)) atTop atBot := by
    have h1 := (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const
      (by norm_num : (0 : ℝ) < 2 * 1)
    exact (tendsto_neg_atTop_atBot.comp h1).congr fun t => by simp [neg_div]
  simpa using (Real.tendsto_exp_atBot.comp harg).const_mul (√(2 * π))⁻¹

/-- Upper Gaussian tail `1 - Φ(x) = ∫_{[x, ∞)} φ`. -/
theorem one_sub_cdf_eq_setIntegral (x : ℝ) :
    1 - Φ x = ∫ y in Ici x, φ y := by
  have htot : ∫ y, φ y = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
  have h1 : Φ x = ∫ y in Iio x, φ y := by
    rw [cdf_gaussianReal_eq_integral 0 one_ne_zero x]
    exact setIntegral_congr_set Iio_ae_eq_Iic.symm
  have hadd := integral_add_compl (s := Iio x) measurableSet_Iio (integrable_gaussianPDFReal 0 1)
  rw [compl_Iio, htot, ← h1] at hadd
  linarith

/-- Derivative of the Gaussian Mills ratio: `M'(x) = x M(x) - 1`. -/
theorem hasDerivAt_millsRatio (x : ℝ) :
    HasDerivAt millsRatio (x * millsRatio x - 1) x := by
  have hφ_pos : φ x ≠ 0 := (gaussianPDFReal_pos 0 1 x one_ne_zero).ne'
  have hnum : HasDerivAt (fun t => 1 - Φ t) (-φ x) x :=
    (hasDerivAt_cdf_gaussianReal 0 one_ne_zero x).const_sub 1
  have hden : HasDerivAt φ (-x * φ x) x := by
    simpa [sub_zero, NNReal.coe_one, div_one] using hasDerivAt_gaussianPDFReal 0 1 x
  refine (hnum.fun_div hden hφ_pos).congr_deriv ?_
  unfold millsRatio
  field_simp [hφ_pos]
  ring

/-- The Gaussian Mills ratio is strictly positive everywhere. -/
theorem millsRatio_pos (x : ℝ) : 0 < millsRatio x :=
  div_pos (sub_pos.2 (cdf_lt_one (gaussianReal_absolutelyContinuous' 0 one_ne_zero) x))
    (gaussianPDFReal_pos 0 1 x one_ne_zero)

/-- Value of the Mills ratio at `0`: `M(0) = √(π / 2)`. -/
theorem millsRatio_zero : millsRatio 0 = √(π / 2) := by
  unfold millsRatio
  rw [cdf_gaussianReal_zero_zero one_ne_zero, gaussianPDFReal_def]
  simp only [sub_zero, NNReal.coe_one, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, neg_zero, zero_div, Real.exp_zero, mul_one, div_inv_eq_mul]
  rw [show (1 - (2 : ℝ)⁻¹) = 1 / 2 by norm_num, Real.sqrt_div pi_nonneg,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) π]
  have hsq2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : √2 ≠ 0 := by positivity
  field_simp
  linarith

/-- Upper Mills-ratio bound: `x M(x) ≤ 1` for `x ≥ 0`. -/
theorem mul_millsRatio_le_one {x : ℝ} (hx : 0 ≤ x) : x * millsRatio x ≤ 1 := by
  rcases hx.eq_or_lt with rfl | hx_pos
  · simp
  unfold millsRatio
  rw [mul_div_assoc', div_le_iff₀ (gaussianPDFReal_pos 0 1 x one_ne_zero), one_mul,
    one_sub_cdf_eq_setIntegral]
  have haux : ∫ y in Ici x, y * φ y = φ x := by
    have hderiv : ∀ y, HasDerivAt (fun t => -φ t) (y * φ y) y := fun y => by
      have := (hasDerivAt_gaussianPDFReal 0 1 y).fun_neg
      simpa [sub_zero, NNReal.coe_one, div_one] using this
    have hlim : Tendsto (fun t => -φ t) atTop (𝓝 0) := by
      simpa using tendsto_gaussianPDFReal_zero_one_atTop.neg
    have hint : IntegrableOn (fun y => y * φ y) (Ici x) := by
      have h := (integrable_gaussianReal_iff_integrable_mul_gaussianPDFReal (μ := 0) (v := 1)
        one_ne_zero).1 ((memLp_id_gaussianReal 1).integrable le_rfl)
      exact (h.congr (ae_of_all _ fun y => mul_comm _ _)).integrableOn
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' (fun y _ => hderiv y)
      (hint.mono_set Ioi_subset_Ici_self) hlim
    rw [integral_Ici_eq_integral_Ioi, hftc]
    ring
  rw [← haux, ← integral_const_mul]
  refine setIntegral_mono_on ((integrable_gaussianPDFReal 0 1).integrableOn.const_mul x) ?_
    measurableSet_Ici fun y hy => mul_le_mul_of_nonneg_right hy (gaussianPDFReal_nonneg 0 1 y)
  have h := (integrable_gaussianReal_iff_integrable_mul_gaussianPDFReal (μ := 0) (v := 1)
    one_ne_zero).1 ((memLp_id_gaussianReal 1).integrable le_rfl)
  exact (h.congr (ae_of_all _ fun y => mul_comm _ _)).integrableOn

/-- For `x ≥ 0`, `M(x) ≤ √(π / 2)`. -/
theorem millsRatio_le_sqrt_pi_div_two {x : ℝ} (hx : 0 ≤ x) :
    millsRatio x ≤ √(π / 2) := by
  have hanti : AntitoneOn millsRatio (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun y _ => (hasDerivAt_millsRatio y).continuousAt.continuousWithinAt)
      (fun y _ => (hasDerivAt_millsRatio y).differentiableAt.differentiableWithinAt)
      fun y hy => by
        rw [(hasDerivAt_millsRatio y).deriv]
        linarith [mul_millsRatio_le_one (interior_subset hy : (0 : ℝ) ≤ y)]
  calc
    millsRatio x ≤ millsRatio 0 := hanti (le_refl 0) hx hx
    _ = √(π / 2) := millsRatio_zero

/-- Lower Mills-ratio bound: `x / (1 + x²) ≤ M(x)` for `x ≥ 0`. -/
theorem millsRatio_ge_div_add_sq {x : ℝ} (_hx : 0 ≤ x) :
    x / (1 + x ^ 2) ≤ millsRatio x := by
  let g : ℝ → ℝ := fun t => (1 - Φ t) - t / (1 + t ^ 2) * φ t
  have hpos : ∀ t : ℝ, 0 < 1 + t ^ 2 := fun t => by positivity
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (-(2 / (1 + t ^ 2) ^ 2) * φ t) t := by
    intro t
    have h1 : HasDerivAt (fun u => 1 - Φ u) (-φ t) t :=
      (hasDerivAt_cdf_gaussianReal 0 one_ne_zero t).const_sub 1
    have h2 : HasDerivAt (fun u => u / (1 + u ^ 2)) ((1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
      have hd := (hasDerivAt_id' t).fun_div ((hasDerivAt_pow 2 t).const_add 1) (hpos t).ne'
      refine hd.congr_deriv ?_
      have hne := (hpos t).ne'
      field_simp; ring
    have h3 : HasDerivAt φ (-t * φ t) t := by
      simpa [sub_zero, NNReal.coe_one, div_one] using hasDerivAt_gaussianPDFReal 0 1 t
    refine (h1.fun_sub (h2.fun_mul h3)).congr_deriv ?_
    have hne := (hpos t).ne'
    field_simp; ring
  have hg_anti : Antitone g :=
    antitone_of_deriv_nonpos (fun t => (hg_deriv t).differentiableAt) fun t => by
      rw [(hg_deriv t).deriv]
      have := gaussianPDFReal_nonneg 0 1 t
      nlinarith [div_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (sq_nonneg (1 + t ^ 2))]
  have hg_lim : Tendsto g atTop (𝓝 0) := by
    have hcdf : Tendsto (fun t => 1 - Φ t) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_cdf_atTop (gaussianReal 0 1))
    have hrat : Tendsto (fun t : ℝ => t / (1 + t ^ 2) * φ t) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := φ) ?_ tendsto_gaussianPDFReal_zero_one_atTop
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t),
        abs_of_nonneg (div_nonneg ht (hpos t).le)]
      refine mul_le_of_le_one_left (gaussianPDFReal_nonneg 0 1 t) ?_
      rw [div_le_one (hpos t)]
      nlinarith [sq_nonneg (t - 1)]
    simpa [g] using hcdf.sub hrat
  have hg_nonneg : 0 ≤ g x :=
    le_of_tendsto hg_lim ((eventually_ge_atTop x).mono fun y hy => hg_anti hy)
  unfold millsRatio
  rw [div_le_div_iff₀ (hpos x) (gaussianPDFReal_pos 0 1 x one_ne_zero)]
  have : x / (1 + x ^ 2) * φ x ≤ 1 - Φ x := by linarith [hg_nonneg]
  rwa [div_mul_eq_mul_div, div_le_iff₀ (hpos x)] at this

/-- Sharp cubic upper bound on the Mills ratio: `M(x) ≤ (x² + 2) / (x (x² + 3))` for `x > 0`. -/
theorem millsRatio_le_cubic_bound {x : ℝ} (hx : 0 < x) :
    millsRatio x ≤ (x ^ 2 + 2) / (x * (x ^ 2 + 3)) := by
  let g : ℝ → ℝ := fun t => (t ^ 2 + 2) / (t * (t ^ 2 + 3)) * φ t - (1 - Φ t)
  have hg_deriv : ∀ t > 0, HasDerivAt g (-(6 / (t * (t ^ 2 + 3)) ^ 2) * φ t) t := by
    intro t ht
    have hden_pos : 0 < t * (t ^ 2 + 3) := by positivity
    have hnum_d : HasDerivAt (fun u => u ^ 2 + 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).add_const 2
    have hden_d : HasDerivAt (fun u => u * (u ^ 2 + 3)) (3 * t ^ 2 + 3) t := by
      have := (hasDerivAt_id' t).fun_mul ((hasDerivAt_pow 2 t).add_const 3)
      refine this.congr_deriv ?_; ring
    have hrat_d := hnum_d.fun_div hden_d hden_pos.ne'
    have hφ_d : HasDerivAt φ (-t * φ t) t := by
      simpa [sub_zero, NNReal.coe_one, div_one] using hasDerivAt_gaussianPDFReal 0 1 t
    have hcdf_d : HasDerivAt (fun u => 1 - Φ u) (-φ t) t :=
      (hasDerivAt_cdf_gaussianReal 0 one_ne_zero t).const_sub 1
    refine ((hrat_d.fun_mul hφ_d).fun_sub hcdf_d).congr_deriv ?_
    have hne := hden_pos.ne'
    field_simp; ring
  have hg_anti : AntitoneOn g (Ioi 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (fun t ht => (hg_deriv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      fun t ht => by
        rw [(hg_deriv t (interior_subset ht)).deriv]
        have := gaussianPDFReal_nonneg 0 1 t
        have := sq_nonneg (t * (t ^ 2 + 3))
        nlinarith [div_nonneg (show (0 : ℝ) ≤ 6 by norm_num) this]
  have hg_lim : Tendsto g atTop (𝓝 0) := by
    have hcdf : Tendsto (fun t => 1 - Φ t) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_cdf_atTop (gaussianReal 0 1))
    have hrat : Tendsto (fun t : ℝ => (t ^ 2 + 2) / (t * (t ^ 2 + 3)) * φ t) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := φ) ?_ tendsto_gaussianPDFReal_zero_one_atTop
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have hden : 0 < t * (t ^ 2 + 3) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t),
        abs_of_nonneg (div_nonneg (by positivity) hden.le)]
      refine mul_le_of_le_one_left (gaussianPDFReal_nonneg 0 1 t) ?_
      rw [div_le_one hden]; nlinarith
    simpa [g] using hrat.sub hcdf
  have hg_nonneg : 0 ≤ g x :=
    le_of_tendsto hg_lim ((eventually_ge_atTop x).mono fun y hy =>
      hg_anti hx (lt_of_lt_of_le hx hy) hy)
  unfold millsRatio
  rw [div_le_iff₀ (gaussianPDFReal_pos 0 1 x one_ne_zero)]
  linarith [hg_nonneg]

/-- Elementary identity `√(2 / π) * √(π / 2) = 1`. -/
theorem sqrt_two_div_pi_mul_sqrt_pi_div_two : √(2 / π) * √(π / 2) = 1 := by
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / π),
    show 2 / π * (π / 2) = 1 by field_simp [pi_ne_zero], Real.sqrt_one]

end CslibFrontier.Probability

namespace CslibFrontier.Probability


/-! ### Stein 1-Wasserstein bound for `|·|` (`|𝔼|W| - √(2/π)| ≤ 3 ∑ 𝔼|X_i|^3`) -/

private noncomputable def steinAbs (x : ℝ) : ℝ :=
  if 0 ≤ x then √(2 / π) * millsRatio x - 1 else -(√(2 / π) * millsRatio (-x) - 1)

private noncomputable def steinAbsDeriv (x : ℝ) : ℝ :=
  x * steinAbs x + |x| - √(2 / π)

private theorem steinAbs_neg (x : ℝ) : steinAbs (-x) = -steinAbs x := by
  unfold steinAbs
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [show 0 ≤ -x by linarith, not_le.2 hx]
  · simp only [neg_zero, le_refl, ↓reduceIte, millsRatio_zero,
      sqrt_two_div_pi_mul_sqrt_pi_div_two]
    norm_num
  · simp [show ¬ (0 ≤ -x) by linarith, hx.le]

private theorem steinAbs_zero : steinAbs 0 = 0 := by
  have := steinAbs_neg 0
  rw [neg_zero] at this
  linarith

private theorem hasDerivAt_steinAbs (x : ℝ) : HasDerivAt steinAbs (steinAbsDeriv x) x := by
  have hpos_d : ∀ y > 0, HasDerivAt (fun t => √(2 / π) * millsRatio t - 1)
      (y * (√(2 / π) * millsRatio y - 1) + y - √(2 / π)) y := fun y _ => by
    have h := ((hasDerivAt_millsRatio y).const_mul √(2 / π)).sub_const 1
    refine h.congr_deriv ?_; ring
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hneg : HasDerivAt (fun t => -(√(2 / π) * millsRatio (-t) - 1)) (steinAbsDeriv x) x := by
      have h := ((hpos_d (-x) (by linarith)).comp x (hasDerivAt_neg x)).neg
      refine h.congr_deriv ?_
      simp only [steinAbsDeriv, steinAbs, not_le.2 hx, ↓reduceIte, abs_of_neg hx]
      ring
    refine hneg.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [steinAbs, not_le.2 hy]
  · have hright : HasDerivWithinAt steinAbs (-√(2 / π)) (Ici 0) 0 := by
      have h0 : HasDerivAt (fun t => √(2 / π) * millsRatio t - 1) (-√(2 / π)) 0 := by
        simpa using ((hasDerivAt_millsRatio 0).const_mul √(2 / π)).sub_const 1
      refine h0.hasDerivWithinAt.congr (fun y hy => by simp [steinAbs, Set.mem_Ici.1 hy])
        (by simp [steinAbs])
    have hleft : HasDerivWithinAt steinAbs (-√(2 / π)) (Iic 0) 0 := by
      have h0 : HasDerivAt (fun t => -(√(2 / π) * millsRatio (-t) - 1)) (-√(2 / π)) 0 := by
        have h : HasDerivAt (fun x => √(2 / π) * millsRatio x - 1) (-√(2 / π)) (-(0 : ℝ)) := by
          simpa using ((hasDerivAt_millsRatio 0).const_mul √(2 / π)).sub_const 1
        exact ((h.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).fun_neg).congr_deriv (by ring)
      refine h0.hasDerivWithinAt.congr (fun y hy => ?_) ?_
      · rcases eq_or_lt_of_le hy with rfl | hlt
        · simp only [steinAbs_zero, neg_zero, millsRatio_zero,
            sqrt_two_div_pi_mul_sqrt_pi_div_two]; norm_num
        · simp [steinAbs, not_le.2 hlt]
      · simp only [steinAbs_zero, neg_zero, millsRatio_zero,
          sqrt_two_div_pi_mul_sqrt_pi_div_two]; norm_num
    simpa [steinAbsDeriv, steinAbs_zero] using
      (hleft.union hright).hasDerivAt (by rw [Set.Iic_union_Ici]; exact Filter.univ_mem)
  · refine ((hpos_d x hx).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [steinAbsDeriv, steinAbs, hx.le, abs_of_pos hx]
    · filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [steinAbs, hy.le]

private theorem steinAbsDeriv_lipschitz : LipschitzWith 2 steinAbsDeriv := by
  have hd_pos : ∀ x > 0, HasDerivAt steinAbsDeriv
      (√(2 / π) * ((1 + x ^ 2) * millsRatio x - x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun t => t * steinAbs t + t - √(2 / π))
        (steinAbs x + x * steinAbsDeriv x + 1) x := by
      have := (((hasDerivAt_id' x).fun_mul (hasDerivAt_steinAbs x)).fun_add
        (hasDerivAt_id' x)).sub_const √(2 / π)
      refine this.congr_deriv ?_; ring
    refine (h1.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [steinAbsDeriv, steinAbs, hx.le, ↓reduceIte, abs_of_pos hx]; ring
    · filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [steinAbsDeriv, abs_of_pos hy]
  have hbound_pos : ∀ x > 0, |√(2 / π) * ((1 + x ^ 2) * millsRatio x - x)| ≤ 2 := by
    intro x hx
    have hlow : 0 ≤ (1 + x ^ 2) * millsRatio x - x := by
      have h := millsRatio_ge_div_add_sq hx.le
      rw [div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)] at h
      linarith
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlow)]
    by_cases hx1 : x ≤ 1
    · have hM := millsRatio_le_sqrt_pi_div_two hx.le
      calc
        √(2 / π) * ((1 + x ^ 2) * millsRatio x - x)
            ≤ √(2 / π) * ((1 + x ^ 2) * √(π / 2)) :=
              mul_le_mul_of_nonneg_left (by nlinarith) (Real.sqrt_nonneg _)
        _ = 1 + x ^ 2 := by
              rw [← mul_assoc, mul_comm √(2 / π), mul_assoc,
                sqrt_two_div_pi_mul_sqrt_pi_div_two, mul_one]
        _ ≤ 2 := by nlinarith
    · push Not at hx1
      have hM := millsRatio_le_cubic_bound hx
      have hdiff : (1 + x ^ 2) * millsRatio x - x ≤ 2 / (x * (x ^ 2 + 3)) := by
        have h1 : (1 + x ^ 2) * millsRatio x ≤ (1 + x ^ 2) * ((x ^ 2 + 2) / (x * (x ^ 2 + 3))) :=
          mul_le_mul_of_nonneg_left hM (by positivity)
        have h2 : (1 + x ^ 2) * ((x ^ 2 + 2) / (x * (x ^ 2 + 3))) - x = 2 / (x * (x ^ 2 + 3)) := by
          have hne : x * (x ^ 2 + 3) ≠ 0 := by positivity
          field_simp; ring
        linarith
      have hfrac : 2 / (x * (x ^ 2 + 3)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have hsqrt : √(2 / π) ≤ 1 := by
        rw [Real.sqrt_le_one, div_le_one pi_pos]; exact Real.two_le_pi
      nlinarith [Real.sqrt_nonneg (2 / π)]
  have hcont : Continuous steinAbsDeriv := by
    unfold steinAbsDeriv
    have hcs : Continuous steinAbs :=
      continuous_iff_continuousAt.2 fun x => (hasDerivAt_steinAbs x).continuousAt
    fun_prop
  have hnonneg : ∀ a b : ℝ, 0 ≤ a → a ≤ b → |steinAbsDeriv b - steinAbsDeriv a| ≤ 2 * (b - a) :=
    fun a b ha hab =>
      abs_sub_le_of_deriv_le_Ioo hab hcont.continuousOn fun x hx =>
        ⟨_, hd_pos x (lt_of_le_of_lt ha hx.1), hbound_pos x (lt_of_le_of_lt ha hx.1)⟩
  have heven : ∀ x, steinAbsDeriv (-x) = steinAbsDeriv x := fun x => by
    simp [steinAbsDeriv, steinAbs_neg, abs_neg]
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat]
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]; exact this b a (le_of_not_ge hab)
  rcases le_total 0 a with ha | ha
  · rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.2 hab)]
    exact hnonneg a b ha hab
  · rcases le_total 0 b with hb | hb
    · rw [← heven a, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.2 hab)]
      rcases le_total (-a) b with h | h
      · rw [abs_sub_comm]
        exact (hnonneg (-a) b (by linarith) h).trans (by linarith)
      · exact (hnonneg b (-a) hb h).trans (by linarith)
    · rw [← heven a, ← heven b, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.2 hab)]
      exact (hnonneg (-b) (-a) (by linarith) (by linarith)).trans_eq (by ring)

/-- **Stein 1-Wasserstein bound for `|·|`**: for independent `L^3` random variables with
`𝔼[X_i] = 0` and `∑ 𝔼[X_i^2] = 1`, `|𝔼|∑ X_i| - √(2/π)| ≤ 3 ∑ 𝔼|X_i|^3`. -/
theorem abs_expect_abs_sum_sub_sqrt_two_div_pi_le {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, MemLp id 3 (μ i))
    (h₁ : ∀ i, ∫ s, s ∂μ i = 0)
    (h₂ : ∑ i, ∫ s, s ^ 2 ∂μ i = 1) :
    |∫ z, |∑ i, z i| ∂Measure.pi μ - √(2 / π)| ≤ 3 * ∑ i, ∫ s, |s| ^ 3 ∂μ i := by
  classical
  set P := Measure.pi μ
  have hmem3 (i : ι) : MemLp (fun z : ι → ℝ => z i) 3 P :=
    (hμ i).comp_measurePreserving (measurePreserving_eval μ i)
  have hW_mem3 : MemLp (fun z : ι → ℝ => ∑ i, z i) 3 P :=
    memLp_finsetSum _ fun i _ => hmem3 i
  have hW_mem2 : MemLp (fun z : ι → ℝ => ∑ i, z i) 2 P :=
    hW_mem3.mono_exponent (by norm_num)
  have hW_int : Integrable (fun z : ι → ℝ => |∑ i, z i|) P :=
    (hW_mem2.integrable one_le_two).abs
  have hf_bdd : ∀ x, |steinAbs x| ≤ 1 := by
    intro x
    have hnonneg : ∀ y ≥ 0, |√(2 / π) * millsRatio y - 1| ≤ 1 := fun y hy => by
      have h0 := millsRatio_pos y
      have h1 := millsRatio_le_sqrt_pi_div_two hy
      have hle : √(2 / π) * millsRatio y ≤ 1 := by
        calc √(2 / π) * millsRatio y ≤ √(2 / π) * √(π / 2) :=
              mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
          _ = 1 := sqrt_two_div_pi_mul_sqrt_pi_div_two
      rw [abs_le]
      exact ⟨by nlinarith [Real.sqrt_nonneg (2 / π)], by linarith⟩
    unfold steinAbs
    split_ifs with hx
    · exact hnonneg x hx
    · rw [abs_neg]; exact hnonneg (-x) (by linarith)
  have hf_cont : Continuous steinAbs :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_steinAbs x).continuousAt
  have hf'_cont : Continuous steinAbsDeriv := steinAbsDeriv_lipschitz.continuous
  have hf'_bdd : ∀ x, |steinAbsDeriv x| ≤ 2 * |x| + 1 := fun x => by
    have h0 := steinAbsDeriv_lipschitz.dist_le_mul x 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero, NNReal.coe_ofNat] at h0
    have hzero : |steinAbsDeriv 0| ≤ 1 := by
      simp only [steinAbsDeriv, zero_mul, abs_zero, add_zero, zero_sub, abs_neg,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one, div_le_one pi_pos]
      exact Real.two_le_pi
    linarith [abs_sub_abs_le_abs_sub (steinAbsDeriv x) (steinAbsDeriv 0)]
  have hInt_Wf : Integrable (fun z : ι → ℝ => (∑ i, z i) * steinAbs (∑ i, z i)) P :=
    hW_int.mono' ((hW_mem2.aestronglyMeasurable).mul
      (hf_cont.comp_aestronglyMeasurable hW_mem2.aestronglyMeasurable))
      (ae_of_all _ fun z => by
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hf_bdd _))
  have hInt_f' : Integrable (fun z : ι → ℝ => steinAbsDeriv (∑ i, z i)) P :=
    ((hW_int.const_mul 2).add (integrable_const 1)).mono'
      (hf'_cont.comp_aestronglyMeasurable hW_mem2.aestronglyMeasurable)
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hf'_bdd (∑ i, z i))
  have hInt_zi_f : ∀ i, Integrable (fun z : ι → ℝ => z i * steinAbs (∑ j, z j)) P := fun i =>
    ((hmem3 i).integrable (by norm_num)).abs.mono'
      (((hmem3 i).aestronglyMeasurable).mul
        (hf_cont.comp_aestronglyMeasurable hW_mem2.aestronglyMeasurable))
      (ae_of_all _ fun z => by
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hf_bdd _))
  have hlhs : ∫ z, |∑ i, z i| ∂P - √(2 / π) =
      ∑ i, ((∫ s, s ^ 2 ∂μ i) * ∫ z, steinAbsDeriv (∑ j, z j) ∂P -
        ∫ z, z i * steinAbs (∑ j, z j) ∂P) := by
    rw [show √(2 / π) = ∫ _ : ι → ℝ, √(2 / π) ∂P by simp,
      ← integral_sub hW_int (integrable_const _)]
    have hcongr : ∫ z, (|∑ i, z i| - √(2 / π)) ∂P =
        ∫ z, steinAbsDeriv (∑ j, z j) ∂P - ∫ z, (∑ j, z j) * steinAbs (∑ j, z j) ∂P := by
      rw [← integral_sub hInt_f' hInt_Wf]
      exact integral_congr_ae (ae_of_all _ fun z => by unfold steinAbsDeriv; ring)
    have hsum_wf : ∫ z, (∑ j, z j) * steinAbs (∑ j, z j) ∂P =
        ∑ i, ∫ z, z i * steinAbs (∑ j, z j) ∂P := by
      have hsplit : (fun z : ι → ℝ => (∑ i, z i) * steinAbs (∑ j, z j)) =
          fun z => ∑ i, z i * steinAbs (∑ j, z j) := funext fun z => Finset.sum_mul _ _ _
      rw [hsplit, integral_finsetSum _ fun i _ => hInt_zi_f i]
    rw [hcongr, hsum_wf]
    conv_lhs =>
      rw [← one_mul (∫ z, steinAbsDeriv (∑ j, z j) ∂P), ← h₂, Finset.sum_mul,
        ← Finset.sum_sub_distrib]
  rw [hlhs, mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  set Wi : (ι → ℝ) → ℝ := fun z => ∑ j ∈ univ.erase i, z j
  have hWi_upd : ∀ v u, Wi (Function.update v i u) = Wi v := fun v u =>
    Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) u v
  have hW_split : ∀ z : ι → ℝ, ∑ j, z j = Wi z + z i := fun z => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_comm]
  have hWi_mem2 : MemLp Wi 2 P :=
    memLp_finsetSum _ fun j _ => (hmem3 j).mono_exponent (by norm_num)
  have hWi_int : Integrable (fun z => |Wi z|) P := (hWi_mem2.integrable one_le_two).abs
  have hInt_f'Wi : Integrable (fun z => steinAbsDeriv (Wi z)) P :=
    ((hWi_int.const_mul 2).add (integrable_const 1)).mono'
      (hf'_cont.comp_aestronglyMeasurable hWi_mem2.aestronglyMeasurable)
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hf'_bdd (Wi z))
  have hInt_zi_fWi : Integrable (fun z => z i * steinAbs (Wi z)) P :=
    ((hmem3 i).integrable (by norm_num)).abs.mono'
      (((hmem3 i).aestronglyMeasurable).mul
        (hf_cont.comp_aestronglyMeasurable hWi_mem2.aestronglyMeasurable))
      (ae_of_all _ fun z => by
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hf_bdd _))
  have hInt_zi2_f'Wi : Integrable (fun z => z i ^ 2 * steinAbsDeriv (Wi z)) P := by
    refine integrable_of_integrable_update μ i
      ((((hmem3 i).aestronglyMeasurable).pow 2).mul
        (hf'_cont.comp_aestronglyMeasurable hWi_mem2.aestronglyMeasurable)) ?_
    have hprod : Integrable (fun p : (ι → ℝ) × ℝ => steinAbsDeriv (Wi p.1) * p.2 ^ 2)
        (P.prod (μ i)) :=
      hInt_f'Wi.mul_prod (integrable_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 2)
        (by norm_num))
    exact hprod.congr (ae_of_all _ fun p => by simp [Function.update_self, hWi_upd, mul_comm])
  have hzero_fWi : ∫ z, z i * steinAbs (Wi z) ∂P = 0 := by
    rw [integral_apply_eval_eq_integral_integral μ (Φ := fun v u => u * steinAbs (Wi v))
      (fun v u => by funext w; simp [hWi_upd]) hInt_zi_fWi]
    refine integral_eq_zero_of_ae (ae_of_all _ fun v => ?_)
    dsimp only
    rw [Pi.zero_apply, integral_mul_const, h₁ i, zero_mul]
  have hsq_f'Wi : ∫ z, z i ^ 2 * steinAbsDeriv (Wi z) ∂P =
      (∫ s, s ^ 2 ∂μ i) * ∫ z, steinAbsDeriv (Wi z) ∂P := by
    rw [integral_apply_eval_eq_integral_integral μ (Φ := fun v u => u ^ 2 * steinAbsDeriv (Wi v))
      (fun v u => by funext w; simp [hWi_upd]) hInt_zi2_f'Wi]
    simp_rw [integral_mul_const]
    rw [integral_const_mul]
  have hdiff1 :
      |∫ z, steinAbsDeriv (∑ j, z j) ∂P - ∫ z, steinAbsDeriv (Wi z) ∂P| ≤
        2 * ∫ s, |s| ∂μ i := by
    rw [← integral_sub hInt_f' hInt_f'Wi]
    refine abs_integral_le_integral_abs.trans ?_
    have hzi_int : Integrable (fun z : ι → ℝ => 2 * |z i|) P :=
      ((hmem3 i).integrable (by norm_num)).abs.const_mul 2
    calc
      ∫ z, |steinAbsDeriv (∑ j, z j) - steinAbsDeriv (Wi z)| ∂P
          ≤ ∫ z, 2 * |z i| ∂P := by
            refine integral_mono (hInt_f'.sub hInt_f'Wi).abs hzi_int fun z => ?_
            have h := steinAbsDeriv_lipschitz.dist_le_mul (∑ j, z j) (Wi z)
            rw [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat] at h
            rw [hW_split z, add_sub_cancel_left] at h
            rw [hW_split z]
            exact h
      _ = 2 * ∫ s, |s| ∂μ i := by
            rw [integral_const_mul]
            congr 1
            rw [← (measurePreserving_eval μ i).map_eq,
              integral_map (measurePreserving_eval μ i).measurable.aemeasurable
                continuous_abs.aestronglyMeasurable]
  have hdiff2 :
      |∫ z, z i * steinAbs (∑ j, z j) ∂P - ∫ z, z i ^ 2 * steinAbsDeriv (Wi z) ∂P| ≤
        ∫ s, |s| ^ 3 ∂μ i := by
    have h12 : Integrable (fun z : ι → ℝ => z i * steinAbs (∑ j, z j) - z i * steinAbs (Wi z)) P :=
      (hInt_zi_f i).sub hInt_zi_fWi
    have hrew : ∫ z, z i * steinAbs (∑ j, z j) ∂P - ∫ z, z i ^ 2 * steinAbsDeriv (Wi z) ∂P =
        ∫ z, z i * (steinAbs (Wi z + z i) - steinAbs (Wi z) - z i * steinAbsDeriv (Wi z)) ∂P := by
      rw [← sub_zero (∫ z, z i * steinAbs (∑ j, z j) ∂P), ← hzero_fWi,
        ← integral_sub (hInt_zi_f i) hInt_zi_fWi, ← integral_sub h12 hInt_zi2_f'Wi]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      dsimp only
      rw [hW_split z]; ring
    rw [hrew]
    have h3_int : Integrable (fun z : ι → ℝ => |z i| ^ 3) P :=
      (measurePreserving_eval μ i).integrable_comp_of_integrable
        (integrable_abs_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 3) le_rfl)
    refine abs_integral_le_integral_abs.trans ?_
    calc
      ∫ z, |z i * (steinAbs (Wi z + z i) - steinAbs (Wi z) - z i * steinAbsDeriv (Wi z))| ∂P
          ≤ ∫ z, |z i| ^ 3 ∂P := by
            refine integral_mono ?_ h3_int fun z => ?_
            · exact ((h12.sub hInt_zi2_f'Wi).congr
                (ae_of_all _ fun z => by
                  change (z i * steinAbs (∑ j, z j) - z i * steinAbs (Wi z)) -
                      z i ^ 2 * steinAbsDeriv (Wi z) = _
                  rw [hW_split z]; ring)).abs
            · rw [abs_mul]
              have ht := abs_sub_sub_mul_deriv_le hasDerivAt_steinAbs steinAbsDeriv_lipschitz
                (Wi z) (z i)
              norm_num at ht
              calc
                |z i| * |steinAbs (Wi z + z i) - steinAbs (Wi z) - z i * steinAbsDeriv (Wi z)|
                    ≤ |z i| * (z i ^ 2) := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
                _ = |z i| ^ 3 := by rw [← sq_abs (z i)]; ring
      _ = ∫ s, |s| ^ 3 ∂μ i := by
            have hmeas3 : AEStronglyMeasurable (fun s : ℝ => |s| ^ 3)
                ((Measure.pi μ).map (Function.eval i)) :=
              (by fun_prop : Continuous fun s : ℝ => |s| ^ 3).aestronglyMeasurable
            rw [← (measurePreserving_eval μ i).map_eq,
              integral_map (measurePreserving_eval μ i).measurable.aemeasurable hmeas3]
  have hvar_nn : 0 ≤ ∫ s, s ^ 2 ∂μ i := integral_nonneg fun _ => sq_nonneg _
  have hlyap := integral_sq_mul_integral_abs_le (hμ i)
  have hident :
      (∫ s, s ^ 2 ∂μ i) * ∫ z, steinAbsDeriv (∑ j, z j) ∂P -
          ∫ z, z i * steinAbs (∑ j, z j) ∂P =
        (∫ s, s ^ 2 ∂μ i) * (∫ z, steinAbsDeriv (∑ j, z j) ∂P - ∫ z, steinAbsDeriv (Wi z) ∂P) -
          (∫ z, z i * steinAbs (∑ j, z j) ∂P - ∫ z, z i ^ 2 * steinAbsDeriv (Wi z) ∂P) := by
    rw [hsq_f'Wi]; ring
  rw [hident]
  calc
    |(∫ s, s ^ 2 ∂μ i) * (∫ z, steinAbsDeriv (∑ j, z j) ∂P - ∫ z, steinAbsDeriv (Wi z) ∂P) -
        (∫ z, z i * steinAbs (∑ j, z j) ∂P - ∫ z, z i ^ 2 * steinAbsDeriv (Wi z) ∂P)|
        ≤ |(∫ s, s ^ 2 ∂μ i) *
            (∫ z, steinAbsDeriv (∑ j, z j) ∂P - ∫ z, steinAbsDeriv (Wi z) ∂P)| +
          |∫ z, z i * steinAbs (∑ j, z j) ∂P - ∫ z, z i ^ 2 * steinAbsDeriv (Wi z) ∂P| :=
            abs_sub _ _
    _ = (∫ s, s ^ 2 ∂μ i) *
          |∫ z, steinAbsDeriv (∑ j, z j) ∂P - ∫ z, steinAbsDeriv (Wi z) ∂P| +
        |∫ z, z i * steinAbs (∑ j, z j) ∂P - ∫ z, z i ^ 2 * steinAbsDeriv (Wi z) ∂P| := by
          rw [abs_mul, abs_of_nonneg hvar_nn]
    _ ≤ (∫ s, s ^ 2 ∂μ i) * (2 * ∫ s, |s| ∂μ i) + ∫ s, |s| ^ 3 ∂μ i := by gcongr
    _ ≤ 3 * ∫ s, |s| ^ 3 ∂μ i := by linarith

end CslibFrontier.Probability
