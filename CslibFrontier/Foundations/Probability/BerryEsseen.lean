module

public import CslibFrontier.Foundations.Probability.BerryEsseenMills
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
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Classical Lyapunov Berry–Esseen Theorem via Stein's Method

This module proves a Stein concentration inequality for sums of independent random variables and
derives the classical Lyapunov Berry–Esseen theorem with explicit constant `41`.

## Main results

* `CslibFrontier.Probability.measureReal_sum_mem_Icc_le`:
  concentration inequality `Pr[a ≤ ∑ X_i ≤ b] ≤ (2 / (3 √V)) (b - a) + 8 γ / (V √V)` for
  independent zero-mean `L^3` summands with total variance `V > 0` and third-moment sum `γ`.
* `CslibFrontier.Probability.berry_esseen_lyapunov`:
  classical Berry–Esseen bound `|Pr[∑ X_i ≤ t] - Φ(t)| ≤ 41 ∑ 𝔼|X_i|^3` for independent zero-mean
  `L^3` summands with unit total variance.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Set Filter
open scoped BigOperators NNReal ENNReal

namespace CslibFrontier.Probability

section BerryEsseenStein

local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

/-! ### Stein concentration inequality (Chen–Shao) -/

/-- Continuous piecewise-linear ramp `g_{a, b, δ}` with slope `1` on `[a - δ, b + δ]` and
bounded by `(b - a) / 2 + δ`. -/
private noncomputable def concRamp (a b δ w : ℝ) : ℝ :=
  max (-(b - a) / 2 - δ) (min ((b - a) / 2 + δ) (w - (a + b) / 2))

private theorem concRamp_mono {a b δ : ℝ} :
    Monotone (concRamp a b δ) := by
  intro x y hxy
  unfold concRamp
  exact max_le_max_left _ (min_le_min_left _ (by linarith))

private theorem abs_concRamp_le {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ) (w : ℝ) :
    |concRamp a b δ w| ≤ (b - a) / 2 + δ := by
  unfold concRamp
  rw [abs_le]
  constructor
  · exact le_trans (by linarith) (le_max_left _ _)
  · exact max_le (by linarith) (min_le_left _ _)

private theorem concRamp_eq_linear {a b δ w : ℝ} (h1 : a - δ ≤ w) (h2 : w ≤ b + δ) :
    concRamp a b δ w = w - (a + b) / 2 := by
  unfold concRamp
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- Pointwise Chen–Shao lower bound:
`x * (g(w) - g(w - x)) ≥ 1_{w ∈ [a, b]} * |x| * min(|x|, δ)`. -/
private theorem mul_concRamp_sub_ge {a b δ w x : ℝ} (hδ : 0 ≤ δ) :
    (if a ≤ w ∧ w ≤ b then |x| * min |x| δ else 0) ≤
      x * (concRamp a b δ w - concRamp a b δ (w - x)) := by
  have hmono := concRamp_mono (a := a) (b := b) (δ := δ)
  have hnn : 0 ≤ x * (concRamp a b δ w - concRamp a b δ (w - x)) := by
    rcases le_total 0 x with hx | hx
    · exact mul_nonneg hx (sub_nonneg.2 (hmono (by linarith)))
    · exact mul_nonneg_of_nonpos_of_nonpos hx (sub_nonpos.2 (hmono (by linarith)))
  split_ifs with hw
  · rcases le_total 0 x with hx | hx
    · set s := min x δ
      have hs0 : 0 ≤ s := le_min hx hδ
      have hsx : s ≤ x := min_le_left _ _
      have hsδ : s ≤ δ := min_le_right _ _
      have h1 : concRamp a b δ (w - x) ≤ concRamp a b δ (w - s) := hmono (by linarith)
      have h2 : concRamp a b δ w = w - (a + b) / 2 :=
        concRamp_eq_linear (by linarith [hw.1]) (by linarith [hw.2])
      have h3 : concRamp a b δ (w - s) = (w - s) - (a + b) / 2 :=
        concRamp_eq_linear (by linarith [hw.1]) (by linarith [hw.2])
      rw [abs_of_nonneg hx]
      nlinarith
    · set s := min (-x) δ
      have hs0 : 0 ≤ s := le_min (by linarith) hδ
      have hsx : s ≤ -x := min_le_left _ _
      have hsδ : s ≤ δ := min_le_right _ _
      have h1 : concRamp a b δ (w + s) ≤ concRamp a b δ (w - x) := hmono (by linarith)
      have h2 : concRamp a b δ w = w - (a + b) / 2 :=
        concRamp_eq_linear (by linarith [hw.1]) (by linarith [hw.2])
      have h3 : concRamp a b δ (w + s) = (w + s) - (a + b) / 2 :=
        concRamp_eq_linear (by linarith [hw.1]) (by linarith [hw.2])
      rw [abs_of_nonpos hx]
      nlinarith
  · exact hnn

/-- **Stein concentration inequality**: for independent `L^3` random variables `X_i` with
`𝔼[X_i] = 0`, total variance `V = ∑ 𝔼[X_i^2] > 0`, and `γ = ∑ 𝔼|X_i|^3 > 0`,
`Pr[a ≤ ∑ X_i ≤ b] ≤ (2 / (3 √V)) (b - a) + 8 γ / (V √V)`. -/
theorem measureReal_sum_mem_Icc_le {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, MemLp id 3 (μ i))
    (h₁ : ∀ i, ∫ s, s ∂μ i = 0)
    {V γ : ℝ} (hV_eq : ∑ i, ∫ s, s ^ 2 ∂μ i = V) (hV : 0 < V)
    (hγ_eq : ∑ i, ∫ s, |s| ^ 3 ∂μ i = γ) (hγ : 0 < γ)
    {a b : ℝ} (hab : a ≤ b) :
    (Measure.pi μ).real {z | a ≤ ∑ i, z i ∧ ∑ i, z i ≤ b} ≤
      2 / (3 * √V) * (b - a) + 8 * γ / (V * √V) := by
  classical
  set P := Measure.pi μ
  set δ : ℝ := 4 * γ / V
  have hδ : 0 < δ := by positivity
  set g : ℝ → ℝ := concRamp a b δ
  have hg_cont : Continuous g := by
    unfold g concRamp; fun_prop
  have hg_bdd : ∀ w, |g w| ≤ (b - a) / 2 + δ := abs_concRamp_le hab hδ.le
  have hmem3 (i : ι) : MemLp (fun z : ι → ℝ => z i) 3 P :=
    (hμ i).comp_measurePreserving (measurePreserving_eval μ i)
  have hmem2 (i : ι) : MemLp id 2 (μ i) := (hμ i).mono_exponent (by norm_num)
  have hW_mem3 : MemLp (fun z : ι → ℝ => ∑ i, z i) 3 P :=
    memLp_finsetSum _ fun i _ => hmem3 i
  have hW_mem2 : MemLp (fun z : ι → ℝ => ∑ i, z i) 2 P :=
    hW_mem3.mono_exponent (by norm_num)
  have hW_int : Integrable (fun z : ι → ℝ => |∑ i, z i|) P :=
    (hW_mem2.integrable one_le_two).abs
  -- Truncated squares `T_i(x) = |x| min(|x|, δ)`
  set tFun : ℝ → ℝ := fun x => |x| * min |x| δ
  set T : (ι → ℝ) → ℝ := fun z => ∑ i, tFun (z i)
  have htFun_cont : Continuous tFun := by unfold tFun; fun_prop
  have htFun_nonneg : ∀ x, 0 ≤ tFun x :=
    fun x => mul_nonneg (abs_nonneg _) (le_min (abs_nonneg _) hδ.le)
  have htFun_le_sq : ∀ x, tFun x ≤ x ^ 2 := fun x => by
    unfold tFun
    calc |x| * min |x| δ ≤ |x| * |x| := mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg _)
      _ = x ^ 2 := by rw [← sq, sq_abs]
  have htFun_sq_le : ∀ x, tFun x ^ 2 ≤ δ * |x| ^ 3 := fun x => by
    unfold tFun
    have h1 : min |x| δ ≤ |x| := min_le_left _ _
    have h2 : min |x| δ ≤ δ := min_le_right _ _
    have h0 : 0 ≤ min |x| δ := le_min (abs_nonneg _) hδ.le
    calc (|x| * min |x| δ) ^ 2 = |x| ^ 2 * (min |x| δ * min |x| δ) := by ring
      _ ≤ |x| ^ 2 * (|x| * δ) := mul_le_mul_of_nonneg_left
            (mul_le_mul h1 h2 h0 (abs_nonneg _)) (sq_nonneg _)
      _ = δ * |x| ^ 3 := by ring
  have hsq_sub_tFun : ∀ x, x ^ 2 - tFun x ≤ |x| ^ 3 / δ := fun x => by
    unfold tFun
    by_cases hx : |x| ≤ δ
    · rw [min_eq_left hx, ← sq, sq_abs, sub_self]; positivity
    · push Not at hx
      rw [min_eq_right hx.le, ← sq_abs x, le_div_iff₀ hδ]
      have hdiff : |x| ^ 3 - (|x| ^ 2 - |x| * δ) * δ = |x| * ((|x| - δ) ^ 2 + |x| * δ) := by ring
      nlinarith [abs_nonneg x, sq_nonneg (|x| - δ), mul_nonneg (abs_nonneg x) hδ.le]
  have hTi_int : ∀ i, Integrable (fun z : ι → ℝ => tFun (z i)) P := fun i =>
    ((hmem3 i).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)).integrable_sq.mono'
      (htFun_cont.comp_aestronglyMeasurable (hmem3 i).aestronglyMeasurable)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (htFun_nonneg _)]
        exact htFun_le_sq _)
  have hT_int : Integrable T P := integrable_finsetSum _ fun i _ => hTi_int i
  have hTi_sq_int : ∀ i, Integrable (fun z : ι → ℝ => tFun (z i) ^ 2) P := fun i =>
    (((measurePreserving_eval μ i).integrable_comp_of_integrable
      (integrable_abs_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 3)
        le_rfl)).const_mul δ).mono'
      ((htFun_cont.pow 2).comp_aestronglyMeasurable (hmem3 i).aestronglyMeasurable)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact htFun_sq_le _)
  -- Step 1: Upper bound `𝔼[W g(W)] ≤ √V * ((b - a) / 2 + δ)`
  have hWg_int : Integrable (fun z : ι → ℝ => (∑ i, z i) * g (∑ i, z i)) P :=
    (hW_int.const_mul ((b - a) / 2 + δ)).mono'
      ((hW_mem2.aestronglyMeasurable).mul
        (hg_cont.comp_aestronglyMeasurable hW_mem2.aestronglyMeasurable))
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hg_bdd _) (abs_nonneg _))
  have hupper : ∫ z, (∑ i, z i) * g (∑ i, z i) ∂P ≤ √V * ((b - a) / 2 + δ) := by
    calc
      ∫ z, (∑ i, z i) * g (∑ i, z i) ∂P
          ≤ ∫ z, ((b - a) / 2 + δ) * |∑ i, z i| ∂P :=
            integral_mono hWg_int (hW_int.const_mul _) fun z => by
              calc (∑ i, z i) * g (∑ i, z i) ≤ |(∑ i, z i) * g (∑ i, z i)| := le_abs_self _
                _ = |∑ i, z i| * |g (∑ i, z i)| := abs_mul _ _
                _ ≤ |∑ i, z i| * ((b - a) / 2 + δ) :=
                    mul_le_mul_of_nonneg_left (hg_bdd _) (abs_nonneg _)
                _ = ((b - a) / 2 + δ) * |∑ i, z i| := mul_comm _ _
      _ = ((b - a) / 2 + δ) * ∫ z, |∑ i, z i| ∂P := integral_const_mul _ _
      _ ≤ ((b - a) / 2 + δ) * √V := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            rw [← hV_eq]
            exact integral_abs_sum_le_sqrt_sum_sq μ hmem2 h₁
      _ = √V * ((b - a) / 2 + δ) := mul_comm _ _
  -- Step 2: Lower bound `𝔼[1_{W ∈ [a, b]} T] ≤ 𝔼[W g(W)]`
  set E : Set (ι → ℝ) := {z | a ≤ ∑ i, z i ∧ ∑ i, z i ≤ b}
  have hsum_meas : Measurable (fun z : ι → ℝ => ∑ i, z i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hE_meas : MeasurableSet E :=
    (measurableSet_le measurable_const hsum_meas).inter
      (measurableSet_le hsum_meas measurable_const)
  have hlower : ∫ z, E.indicator T z ∂P ≤ ∫ z, (∑ i, z i) * g (∑ i, z i) ∂P := by
    have hterm_int (i : ι) :
        Integrable (fun z : ι → ℝ => z i * (g (∑ j, z j) - g (∑ j ∈ univ.erase i, z j))) P := by
      have h1 : Integrable (fun z : ι → ℝ => z i * g (∑ j, z j)) P :=
        (((hmem3 i).integrable (by norm_num)).abs.const_mul ((b - a) / 2 + δ)).mono'
          (((hmem3 i).aestronglyMeasurable).mul
            (hg_cont.comp_aestronglyMeasurable hW_mem2.aestronglyMeasurable))
          (ae_of_all _ fun z => by
            rw [Real.norm_eq_abs, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hg_bdd _) (abs_nonneg _))
      have hWi_m : AEStronglyMeasurable (fun z : ι → ℝ => ∑ j ∈ Finset.univ.erase i, z j) P :=
        (memLp_finsetSum (p := 2) (Finset.univ.erase i) fun j _ =>
          (hmem3 j).mono_exponent (by norm_num)).aestronglyMeasurable
      have h2 : Integrable (fun z : ι → ℝ => z i * g (∑ j ∈ Finset.univ.erase i, z j)) P :=
        (((hmem3 i).integrable (by norm_num)).abs.const_mul ((b - a) / 2 + δ)).mono'
          (((hmem3 i).aestronglyMeasurable).mul (hg_cont.comp_aestronglyMeasurable hWi_m))
          (ae_of_all _ fun z => by
            rw [Real.norm_eq_abs, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hg_bdd _) (abs_nonneg _))
      exact (h1.sub h2).congr (ae_of_all _ fun z => by dsimp only [Pi.sub_apply]; ring)
    have hWg_eq : ∫ z, (∑ i, z i) * g (∑ j, z j) ∂P =
        ∫ z, ∑ i, z i * (g (∑ j, z j) - g (∑ j ∈ Finset.univ.erase i, z j)) ∂P := by
      rw [integral_finsetSum _ fun i _ => hterm_int i]
      have hsplit : (fun z : ι → ℝ => (∑ i, z i) * g (∑ j, z j)) =
          fun z => ∑ i, z i * g (∑ j, z j) := funext fun z => Finset.sum_mul _ _ _
      rw [hsplit, integral_finsetSum _ fun i _ => ?_]
      · refine Finset.sum_congr rfl fun i _ => ?_
        have hWi_m : AEStronglyMeasurable (fun z : ι → ℝ => ∑ j ∈ Finset.univ.erase i, z j) P :=
          (memLp_finsetSum (p := 2) (Finset.univ.erase i) fun j _ =>
            (hmem3 j).mono_exponent (by norm_num)).aestronglyMeasurable
        have h1 : Integrable (fun z : ι → ℝ => z i * g (∑ j, z j)) P :=
          (((hmem3 i).integrable (by norm_num)).abs.const_mul ((b - a) / 2 + δ)).mono'
            (((hmem3 i).aestronglyMeasurable).mul
              (hg_cont.comp_aestronglyMeasurable hW_mem2.aestronglyMeasurable))
            (ae_of_all _ fun z => by
              rw [Real.norm_eq_abs, abs_mul, mul_comm]
              exact mul_le_mul_of_nonneg_right (hg_bdd _) (abs_nonneg _))
        have h2 : Integrable (fun z : ι → ℝ => z i * g (∑ j ∈ Finset.univ.erase i, z j)) P :=
          (((hmem3 i).integrable (by norm_num)).abs.const_mul ((b - a) / 2 + δ)).mono'
            (((hmem3 i).aestronglyMeasurable).mul (hg_cont.comp_aestronglyMeasurable hWi_m))
            (ae_of_all _ fun z => by
              rw [Real.norm_eq_abs, abs_mul, mul_comm]
              exact mul_le_mul_of_nonneg_right (hg_bdd _) (abs_nonneg _))
        have hzero : ∫ z, z i * g (∑ j ∈ Finset.univ.erase i, z j) ∂P = 0 := by
          rw [show P = Measure.pi μ from rfl, ← integral_integral_update μ h2 i]
          refine integral_eq_zero_of_ae (ae_of_all _ fun v => ?_)
          have he : ∀ u : ℝ, ∑ j ∈ Finset.univ.erase i, Function.update v i u j =
              ∑ j ∈ Finset.univ.erase i, v j := fun u =>
            Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) u v
          simp_rw [Function.update_self, he]
          rw [integral_mul_const, h₁ i, zero_mul]; rfl
        have hsub_eq :
            ∫ z, z i * (g (∑ j, z j) - g (∑ j ∈ Finset.univ.erase i, z j)) ∂P =
              ∫ z, z i * g (∑ j, z j) ∂P - ∫ z, z i * g (∑ j ∈ Finset.univ.erase i, z j) ∂P := by
          rw [← integral_sub h1 h2]
          exact integral_congr_ae (ae_of_all _ fun z => by ring)
        rw [hsub_eq, hzero, sub_zero]
      · exact (((hmem3 i).integrable (by norm_num)).abs.const_mul ((b - a) / 2 + δ)).mono'
          (((hmem3 i).aestronglyMeasurable).mul
            (hg_cont.comp_aestronglyMeasurable hW_mem2.aestronglyMeasurable))
          (ae_of_all _ fun z => by
            rw [Real.norm_eq_abs, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hg_bdd _) (abs_nonneg _))
    rw [hWg_eq]
    refine integral_mono (hT_int.indicator hE_meas) (integrable_finsetSum _ fun i _ => hterm_int i)
      fun z => ?_
    have hpt : E.indicator T z = ∑ i, if a ≤ ∑ j, z j ∧ ∑ j, z j ≤ b then tFun (z i) else 0 := by
      by_cases hz : z ∈ E
      · have hz' : a ≤ ∑ j, z j ∧ ∑ j, z j ≤ b := hz
        simp only [Set.indicator_of_mem hz, T]
        exact Finset.sum_congr rfl fun i _ => by simp [hz']
      · simp only [Set.indicator_of_notMem hz]
        refine (Finset.sum_eq_zero fun i _ => ?_).symm
        split_ifs with h
        · exact absurd h hz
        · rfl
    rw [hpt]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsub : ∑ j ∈ Finset.univ.erase i, z j = (∑ j, z j) - z i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
    rw [hsub]
    exact mul_concRamp_sub_ge hδ.le
  -- Step 3: `𝔼[T] ≥ (3/4) V` and `Var(T) ≤ δ γ = 4 γ^2 / V`
  have hET : (3 / 4) * V ≤ ∫ z, T z ∂P := by
    rw [integral_finsetSum _ fun i _ => hTi_int i]
    have hterm : ∀ i, ∫ s, s ^ 2 ∂μ i - (∫ s, |s| ^ 3 ∂μ i) / δ ≤ ∫ z, tFun (z i) ∂P := by
      intro i
      have ht_eval : ∫ z, tFun (z i) ∂P = ∫ s, tFun s ∂μ i := by
        rw [← (measurePreserving_eval μ i).map_eq,
          integral_map (measurePreserving_eval μ i).measurable.aemeasurable
            htFun_cont.aestronglyMeasurable]
      rw [ht_eval]
      have h1 : Integrable (fun s => s ^ 2) (μ i) :=
        integrable_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 2) (by norm_num)
      have h2 : Integrable tFun (μ i) :=
        h1.mono' htFun_cont.aestronglyMeasurable (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (htFun_nonneg _)]
          exact htFun_le_sq s)
      have h3 : Integrable (fun s => |s| ^ 3 / δ) (μ i) :=
        (integrable_abs_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 3) le_rfl).div_const δ
      have hle := integral_mono (h1.sub h2) h3 hsq_sub_tFun
      change ∫ s, (s ^ 2 - tFun s) ∂μ i ≤ ∫ s, |s| ^ 3 / δ ∂μ i at hle
      rw [integral_sub h1 h2, integral_div] at hle
      linarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hV_eq, hγ_eq] at hsum
    have hquot : γ / δ = V / 4 := by unfold δ; field_simp
    linarith
  have hVarT : ∫ z, (T z - ∫ w, T w ∂P) ^ 2 ∂P ≤ 4 * γ ^ 2 / V := by
    let m : ι → ℝ := fun i => ∫ s, tFun s ∂μ i
    have hET_eq : ∫ w, T w ∂P = ∑ i, m i := by
      rw [integral_finsetSum _ fun i _ => hTi_int i]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [m]
      rw [← (measurePreserving_eval μ i).map_eq,
        integral_map (measurePreserving_eval μ i).measurable.aemeasurable
          htFun_cont.aestronglyMeasurable]
    have hcent_mem2 (i : ι) : MemLp (fun z : ι → ℝ => tFun (z i) - m i) 2 P := by
      have h1 : MemLp (fun z : ι → ℝ => tFun (z i)) 2 P :=
        (memLp_two_iff_integrable_sq (htFun_cont.comp_aestronglyMeasurable
          (hmem3 i).aestronglyMeasurable)).2 (hTi_sq_int i)
      exact h1.sub (memLp_const (m i))
    have hdiff_eq : (fun z : ι → ℝ => (T z - ∫ w, T w ∂P) ^ 2) =
        fun z => ∑ i, ∑ j, (tFun (z i) - m i) * (tFun (z j) - m j) := funext fun z => by
      have hsub : T z - ∑ i, m i = ∑ i, (tFun (z i) - m i) :=
        (Finset.sum_sub_distrib (s := Finset.univ) (f := fun i => tFun (z i)) (g := m)).symm
      rw [hET_eq, hsub, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    have hmul_int (i j : ι) :
        Integrable (fun z : ι → ℝ => (tFun (z i) - m i) * (tFun (z j) - m j)) P :=
      (hcent_mem2 i).integrable_mul (hcent_mem2 j)
    rw [hdiff_eq, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hmul_int i j]
    have hdiag : ∀ i, ∫ z, ∑ j, (tFun (z i) - m i) * (tFun (z j) - m j) ∂P =
        ∫ z, (tFun (z i) - m i) ^ 2 ∂P := fun i => by
      rw [integral_finsetSum _ fun j _ => hmul_int i j, Finset.sum_eq_single i]
      · simp only [sq]
      · intro j _ hji
        rw [← integral_integral_update μ (hmul_int i j) j]
        refine integral_eq_zero_of_ae (ae_of_all _ fun v => ?_)
        have hupd : (fun u => (tFun (Function.update v j u i) - m i) *
            (tFun (Function.update v j u j) - m j)) =
            fun u => (tFun (v i) - m i) * (tFun u - m j) := funext fun u => by
          rw [Function.update_of_ne hji.symm, Function.update_self]
        dsimp only
        rw [hupd, integral_const_mul]
        have h1 : Integrable tFun (μ j) :=
          (integrable_pow_of_memLp (n := 3) (by exact_mod_cast hμ j) (j := 2) (by norm_num)).mono'
            htFun_cont.aestronglyMeasurable (ae_of_all _ fun s => by
              rw [Real.norm_eq_abs, abs_of_nonneg (htFun_nonneg _)]
              exact htFun_le_sq s)
        rw [integral_sub h1 (integrable_const _), integral_const, probReal_univ, smul_eq_mul,
          one_mul, sub_self, mul_zero]; rfl
      · intro hi; exact absurd (Finset.mem_univ i) hi
    simp_rw [hdiag]
    have hle_i : ∀ i, ∫ z, (tFun (z i) - m i) ^ 2 ∂P ≤ δ * ∫ s, |s| ^ 3 ∂μ i := fun i => by
      have ht_eval : ∫ z, tFun (z i) ∂P = ∫ s, tFun s ∂μ i := by
        rw [← (measurePreserving_eval μ i).map_eq,
          integral_map (measurePreserving_eval μ i).measurable.aemeasurable
            htFun_cont.aestronglyMeasurable]
      have h1 : ∫ z, (tFun (z i) - m i) ^ 2 ∂P = ∫ z, tFun (z i) ^ 2 ∂P - m i ^ 2 := by
        have hsub : (fun z : ι → ℝ => (tFun (z i) - m i) ^ 2) =
            fun z => tFun (z i) ^ 2 - 2 * m i * tFun (z i) + m i ^ 2 := funext fun z => by ring
        have hsub1 : Integrable (fun z : ι → ℝ => tFun (z i) ^ 2 - 2 * m i * tFun (z i)) P :=
          (hTi_sq_int i).sub ((hTi_int i).const_mul (2 * m i))
        rw [hsub, integral_add hsub1 (integrable_const _),
          integral_sub (hTi_sq_int i) ((hTi_int i).const_mul (2 * m i)), integral_const_mul,
          ht_eval, integral_const, probReal_univ, smul_eq_mul, one_mul]
        ring
      rw [h1]
      have h2 : ∫ z, tFun (z i) ^ 2 ∂P ≤ δ * ∫ s, |s| ^ 3 ∂μ i := by
        have ht2_eval : ∫ z, tFun (z i) ^ 2 ∂P = ∫ s, tFun s ^ 2 ∂μ i := by
          rw [← (measurePreserving_eval μ i).map_eq,
            integral_map (measurePreserving_eval μ i).measurable.aemeasurable
              (by fun_prop : Continuous fun s : ℝ => tFun s ^ 2).aestronglyMeasurable]
        rw [ht2_eval, ← integral_const_mul]
        refine integral_mono ?_ ((integrable_abs_pow_of_memLp (n := 3)
          (by exact_mod_cast hμ i) (j := 3) le_rfl).const_mul δ) htFun_sq_le
        exact ((integrable_abs_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 3)
          le_rfl).const_mul δ).mono' (htFun_cont.pow 2).aestronglyMeasurable
          (ae_of_all _ fun s => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            exact htFun_sq_le s)
      nlinarith [sq_nonneg (m i)]
    calc
      ∑ i, ∫ z, (tFun (z i) - m i) ^ 2 ∂P
          ≤ ∑ i, δ * ∫ s, |s| ^ 3 ∂μ i := Finset.sum_le_sum fun i _ => hle_i i
      _ = δ * γ := by rw [← Finset.mul_sum, hγ_eq]
      _ = 4 * γ ^ 2 / V := by unfold δ; ring
  -- Step 4: Combine `(3/4) V * P(E) - 2 γ / √V ≤ 𝔼[1_E T] ≤ √V * ((b-a)/2 + δ)`
  have hdev : ∫ z, |T z - ∫ w, T w ∂P| ∂P ≤ 2 * γ / √V := by
    have hT_mem2 : MemLp (fun z => T z - ∫ w, T w ∂P) 2 P :=
      (memLp_finsetSum _ fun i _ => (memLp_two_iff_integrable_sq
        (htFun_cont.comp_aestronglyMeasurable (hmem3 i).aestronglyMeasurable)).2
        (hTi_sq_int i)).sub (memLp_const _)
    have hcs := sq_integral_mul_le (P := P) (f := fun z => |T z - ∫ w, T w ∂P|)
      (g := fun _ => (1 : ℝ))
      (by simpa only [sq_abs] using hT_mem2.integrable_sq)
      (by simpa only [one_pow] using integrable_const (1 : ℝ))
      (by simpa using (hT_mem2.integrable one_le_two).abs)
    simp only [mul_one, sq_abs, one_pow, integral_const, probReal_univ, smul_eq_mul] at hcs
    have hsq_bound : (∫ z, |T z - ∫ w, T w ∂P| ∂P) ^ 2 ≤ (2 * γ / √V) ^ 2 := by
      refine hcs.trans (hVarT.trans_eq ?_)
      rw [div_pow, mul_pow, Real.sq_sqrt hV.le]; ring
    have hnn1 : 0 ≤ ∫ z, |T z - ∫ w, T w ∂P| ∂P := integral_nonneg fun _ => abs_nonneg _
    exact (pow_le_pow_iff_left₀ hnn1 (by positivity) two_ne_zero).1 hsq_bound
  have hmain : (∫ w, T w ∂P) * P.real E - ∫ z, |T z - ∫ w, T w ∂P| ∂P ≤
      ∫ z, E.indicator T z ∂P := by
    have h1 : (∫ w, T w ∂P) * P.real E = ∫ z, E.indicator (fun _ => ∫ w, T w ∂P) z ∂P := by
      rw [integral_indicator_const _ hE_meas, smul_eq_mul, mul_comm]
    rw [h1]
    have hdiff_int : Integrable (fun z => E.indicator (fun _ => ∫ w, T w ∂P) z -
      E.indicator T z) P :=
      ((integrable_const _).indicator hE_meas).sub (hT_int.indicator hE_meas)
    have hle : ∫ z, (E.indicator (fun _ => ∫ w, T w ∂P) z - E.indicator T z) ∂P ≤
        ∫ z, |T z - ∫ w, T w ∂P| ∂P := by
      refine integral_mono hdiff_int ((hT_int.sub (integrable_const _)).abs) fun z => ?_
      by_cases hz : z ∈ E
      · simp only [Set.indicator_of_mem hz]
        rw [abs_sub_comm]
        exact le_abs_self _
      · simp [Set.indicator_of_notMem hz, abs_nonneg]
    rw [integral_sub ((integrable_const _).indicator hE_meas) (hT_int.indicator hE_meas)] at hle
    linarith
  have hPE_nn : 0 ≤ P.real E := measureReal_nonneg
  have h34 : (3 / 4) * V * P.real E ≤ √V * ((b - a) / 2 + δ) + 2 * γ / √V := by
    have hmul : (3 / 4) * V * P.real E ≤ (∫ w, T w ∂P) * P.real E :=
      mul_le_mul_of_nonneg_right hET hPE_nn
    linarith [hlower, hupper, hdev, hmain]
  have hrhs_eq : (√V * ((b - a) / 2 + δ) + 2 * γ / √V) / ((3 / 4) * V) =
      2 / (3 * √V) * (b - a) + 8 * γ / (V * √V) := by
    have hsqV : √V ^ 2 = V := Real.sq_sqrt hV.le
    have hneV : √V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
    unfold δ
    field_simp [hV.ne', hneV]
    rw [hsqV]; ring
  rw [← hrhs_eq, le_div_iff₀ (by positivity)]
  linarith

/-! ### Stein solution for `1_{· ≤ t}` and Classical Berry–Esseen -/

/-- The Stein solution `f_t` for `1_{· ≤ t} - Φ(t)`. -/
private noncomputable def steinInd (t x : ℝ) : ℝ :=
  if x ≤ t then Φ x * (1 - Φ t) / φ x else Φ t * (1 - Φ x) / φ x

/-- The piecewise derivative `D_t(x) = x f_t(x) + 1_{x ≤ t} - Φ(t)`. -/
private noncomputable def steinIndDeriv (t x : ℝ) : ℝ :=
  x * steinInd t x + (if x ≤ t then 1 else 0) - Φ t

private theorem continuous_steinInd (t : ℝ) : Continuous (steinInd t) := by
  have hφ_ne : ∀ x, φ x ≠ 0 := fun x => (gaussianPDFReal_pos 0 1 x one_ne_zero).ne'
  have h1 : Continuous fun x => Φ x * (1 - Φ t) / φ x :=
    ((continuous_cdf_gaussianReal 0 one_ne_zero).mul continuous_const).div
      (continuous_gaussianPDFReal 0 1) hφ_ne
  have h2 : Continuous fun x => Φ t * (1 - Φ x) / φ x :=
    (continuous_const.mul (continuous_const.sub (continuous_cdf_gaussianReal 0 one_ne_zero))).div
      (continuous_gaussianPDFReal 0 1) hφ_ne
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases lt_trichotomy x t with hx | rfl | hx
  · exact h1.continuousAt.congr (Filter.eventually_of_mem (Iio_mem_nhds hx) fun y hy => by
      simp [steinInd, hy.le])
  · rw [continuousAt_iff_continuous_left'_right']
    constructor
    · exact h1.continuousWithinAt.congr (fun y hy => by simp [steinInd, hy.le])
        (by simp [steinInd])
    · exact h2.continuousWithinAt.congr (fun y hy => by simp [steinInd, not_le.2 hy])
        (by simp [steinInd])
  · exact h2.continuousAt.congr (Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => by
      simp [steinInd, not_le.2 hy])

private theorem hasDerivAt_steinInd_of_ne {t x : ℝ} (hne : x ≠ t) :
    HasDerivAt (steinInd t) (steinIndDeriv t x) x := by
  have hφ_ne : φ x ≠ 0 := (gaussianPDFReal_pos 0 1 x one_ne_zero).ne'
  have hφ_d : HasDerivAt φ (-x * φ x) x := by
    simpa [sub_zero, NNReal.coe_one, div_one] using hasDerivAt_gaussianPDFReal 0 1 x
  have hΦ_d : HasDerivAt Φ (φ x) x := hasDerivAt_cdf_gaussianReal 0 one_ne_zero x
  rcases lt_or_gt_of_ne hne with hx | hx
  · have hd : HasDerivAt (fun y => Φ y * (1 - Φ t) / φ y) (steinIndDeriv t x) x := by
      refine ((hΦ_d.mul_const (1 - Φ t)).div hφ_d hφ_ne).congr_deriv ?_
      simp only [steinIndDeriv, steinInd, hx.le, ↓reduceIte]
      field_simp [hφ_ne]; ring
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [steinInd, hy.le]
  · have hd : HasDerivAt (fun y => Φ t * (1 - Φ y) / φ y) (steinIndDeriv t x) x := by
      have hsub : HasDerivAt (fun y => 1 - Φ y) (-φ x) x := hΦ_d.const_sub 1
      refine ((hsub.const_mul (Φ t)).div hφ_d hφ_ne).congr_deriv ?_
      simp only [steinIndDeriv, steinInd, not_le.2 hx, ↓reduceIte]
      field_simp [hφ_ne]; ring
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [steinInd, not_le.2 hy]

private theorem steinInd_nonneg (t x : ℝ) : 0 ≤ steinInd t x := by
  unfold steinInd
  have h0 : 0 ≤ φ x := gaussianPDFReal_nonneg 0 1 x
  split_ifs
  · exact div_nonneg (mul_nonneg (cdf_nonneg _ _) (sub_nonneg.2 (cdf_le_one _ _))) h0
  · exact div_nonneg (mul_nonneg (cdf_nonneg _ _) (sub_nonneg.2 (cdf_le_one _ _))) h0

private theorem cdf_div_pdf_eq_millsRatio_neg (x : ℝ) :
    Φ x / φ x = millsRatio (-x) := by
  rw [millsRatio_eq_div]
  have h1 : Φ (-x) = 1 - Φ x := cdf_gaussianReal_neg one_ne_zero x
  have h2 : φ (-x) = φ x := by simp [gaussianPDFReal_def]
  rw [h1, h2]; ring

private theorem steinInd_le_sqrt_pi_div_two (t x : ℝ) : steinInd t x ≤ √(π / 2) := by
  have hφ_pos : 0 < φ x := gaussianPDFReal_pos 0 1 x one_ne_zero
  unfold steinInd
  split_ifs with hxt
  · rcases le_total 0 x with hx | hx
    · have h1 : 1 - Φ t ≤ 1 - Φ x := by linarith [monotone_cdf (gaussianReal 0 1) hxt]
      calc Φ x * (1 - Φ t) / φ x ≤ 1 * (1 - Φ x) / φ x := by
            refine div_le_div_of_nonneg_right ?_ hφ_pos.le
            exact mul_le_mul (cdf_le_one _ _) h1 (sub_nonneg.2 (cdf_le_one _ _)) zero_le_one
        _ = millsRatio x := by rw [one_mul, millsRatio_eq_div]
        _ ≤ √(π / 2) := millsRatio_le_sqrt_pi_div_two hx
    · calc Φ x * (1 - Φ t) / φ x ≤ Φ x * 1 / φ x := by
            refine div_le_div_of_nonneg_right ?_ hφ_pos.le
            exact mul_le_mul_of_nonneg_left (by linarith [cdf_nonneg (gaussianReal 0 1) t])
              (cdf_nonneg _ _)
        _ = millsRatio (-x) := by rw [mul_one, cdf_div_pdf_eq_millsRatio_neg]
        _ ≤ √(π / 2) := millsRatio_le_sqrt_pi_div_two (by linarith)
  · push Not at hxt
    rcases le_total 0 x with hx | hx
    · calc Φ t * (1 - Φ x) / φ x ≤ 1 * (1 - Φ x) / φ x := by
            refine div_le_div_of_nonneg_right ?_ hφ_pos.le
            exact mul_le_mul_of_nonneg_right (cdf_le_one _ _) (sub_nonneg.2 (cdf_le_one _ _))
        _ = millsRatio x := by rw [one_mul, millsRatio_eq_div]
        _ ≤ √(π / 2) := millsRatio_le_sqrt_pi_div_two hx
    · have h1 : Φ t ≤ Φ x := monotone_cdf (gaussianReal 0 1) hxt.le
      calc Φ t * (1 - Φ x) / φ x ≤ Φ x * 1 / φ x := by
            refine div_le_div_of_nonneg_right ?_ hφ_pos.le
            exact mul_le_mul h1 (by linarith [cdf_nonneg (gaussianReal 0 1) x])
              (sub_nonneg.2 (cdf_le_one _ _)) (cdf_nonneg _ _)
        _ = millsRatio (-x) := by rw [mul_one, cdf_div_pdf_eq_millsRatio_neg]
        _ ≤ √(π / 2) := millsRatio_le_sqrt_pi_div_two (by linarith)

private theorem abs_mul_steinInd_le_one (t x : ℝ) : |x * steinInd t x| ≤ 1 := by
  have hφ_pos : 0 < φ x := gaussianPDFReal_pos 0 1 x one_ne_zero
  rw [abs_mul, abs_of_nonneg (steinInd_nonneg t x)]
  unfold steinInd
  split_ifs with hxt
  · rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      have h1 : 1 - Φ t ≤ 1 - Φ x := by linarith [monotone_cdf (gaussianReal 0 1) hxt]
      calc x * (Φ x * (1 - Φ t) / φ x) ≤ x * (1 * (1 - Φ x) / φ x) := by
            refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hφ_pos.le) hx
            exact mul_le_mul (cdf_le_one _ _) h1 (sub_nonneg.2 (cdf_le_one _ _)) zero_le_one
        _ = x * millsRatio x := by rw [one_mul, millsRatio_eq_div]
        _ ≤ 1 := mul_millsRatio_le_one hx
    · rw [abs_of_nonpos hx]
      calc (-x) * (Φ x * (1 - Φ t) / φ x) ≤ (-x) * (Φ x * 1 / φ x) := by
            refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hφ_pos.le) (by linarith)
            exact mul_le_mul_of_nonneg_left (by linarith [cdf_nonneg (gaussianReal 0 1) t])
              (cdf_nonneg _ _)
        _ = (-x) * millsRatio (-x) := by rw [mul_one, cdf_div_pdf_eq_millsRatio_neg]
        _ ≤ 1 := mul_millsRatio_le_one (by linarith)
  · push Not at hxt
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      calc x * (Φ t * (1 - Φ x) / φ x) ≤ x * (1 * (1 - Φ x) / φ x) := by
            refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hφ_pos.le) hx
            exact mul_le_mul_of_nonneg_right (cdf_le_one _ _) (sub_nonneg.2 (cdf_le_one _ _))
        _ = x * millsRatio x := by rw [one_mul, millsRatio_eq_div]
        _ ≤ 1 := mul_millsRatio_le_one hx
    · rw [abs_of_nonpos hx]
      have h1 : Φ t ≤ Φ x := monotone_cdf (gaussianReal 0 1) hxt.le
      calc (-x) * (Φ t * (1 - Φ x) / φ x) ≤ (-x) * (Φ x * 1 / φ x) := by
            refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hφ_pos.le) (by linarith)
            exact mul_le_mul h1 (by linarith [cdf_nonneg (gaussianReal 0 1) x])
              (sub_nonneg.2 (cdf_le_one _ _)) (cdf_nonneg _ _)
        _ = (-x) * millsRatio (-x) := by rw [mul_one, cdf_div_pdf_eq_millsRatio_neg]
        _ ≤ 1 := mul_millsRatio_le_one (by linarith)

private theorem abs_steinIndDeriv_le_one (t x : ℝ) : |steinIndDeriv t x| ≤ 1 := by
  have hφ_pos : 0 < φ x := gaussianPDFReal_pos 0 1 x one_ne_zero
  unfold steinIndDeriv steinInd
  split_ifs with hxt
  · rw [abs_le]
    rcases le_total 0 x with hx | hx
    · have h1 : 1 - Φ t ≤ 1 - Φ x := by linarith [monotone_cdf (gaussianReal 0 1) hxt]
      have hxM : x * (Φ x * (1 - Φ t) / φ x) ≤ Φ x := by
        calc x * (Φ x * (1 - Φ t) / φ x) = Φ x * (x * ((1 - Φ t) / φ x)) := by ring
          _ ≤ Φ x * (x * millsRatio x) := by
                refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hx) (cdf_nonneg _ _)
                rw [millsRatio_eq_div]
                exact div_le_div_of_nonneg_right h1 hφ_pos.le
          _ ≤ Φ x * 1 := mul_le_mul_of_nonneg_left (mul_millsRatio_le_one hx) (cdf_nonneg _ _)
          _ = Φ x := mul_one _
      have hnn : 0 ≤ x * (Φ x * (1 - Φ t) / φ x) :=
        mul_nonneg hx (div_nonneg (mul_nonneg (cdf_nonneg _ _) (sub_nonneg.2 (cdf_le_one _ _)))
          hφ_pos.le)
      have hΦle : Φ x ≤ Φ t := monotone_cdf (gaussianReal 0 1) hxt
      exact ⟨by linarith [cdf_le_one (gaussianReal 0 1) t], by linarith⟩
    · have hneg : -(1 - Φ t) ≤ x * (Φ x * (1 - Φ t) / φ x) := by
        have hm := mul_millsRatio_le_one (show 0 ≤ -x by linarith)
        rw [← cdf_div_pdf_eq_millsRatio_neg] at hm
        have : -((1 - Φ t) * ((-x) * (Φ x / φ x))) ≥ -(1 - Φ t) * 1 := by
          nlinarith [sub_nonneg.2 (cdf_le_one (gaussianReal 0 1) t)]
        linarith [show x * (Φ x * (1 - Φ t) / φ x) = -((1 - Φ t) * ((-x) * (Φ x / φ x))) by ring]
      have hnp : x * (Φ x * (1 - Φ t) / φ x) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hx (div_nonneg (mul_nonneg (cdf_nonneg _ _)
          (sub_nonneg.2 (cdf_le_one _ _))) hφ_pos.le)
      exact ⟨by linarith, by linarith [cdf_nonneg (gaussianReal 0 1) t]⟩
  · push Not at hxt
    rw [abs_le]
    rcases le_total 0 x with hx | hx
    · have hle : x * (Φ t * (1 - Φ x) / φ x) ≤ Φ t := by
        calc x * (Φ t * (1 - Φ x) / φ x) = Φ t * (x * millsRatio x) := by
              rw [millsRatio_eq_div]; ring
          _ ≤ Φ t * 1 := mul_le_mul_of_nonneg_left (mul_millsRatio_le_one hx) (cdf_nonneg _ _)
          _ = Φ t := mul_one _
      have hnn : 0 ≤ x * (Φ t * (1 - Φ x) / φ x) :=
        mul_nonneg hx (div_nonneg (mul_nonneg (cdf_nonneg _ _) (sub_nonneg.2 (cdf_le_one _ _)))
          hφ_pos.le)
      exact ⟨by linarith [cdf_le_one (gaussianReal 0 1) t], by linarith⟩
    · have h1 : Φ t ≤ Φ x := monotone_cdf (gaussianReal 0 1) hxt.le
      have hge : -(1 - Φ x) ≤ x * (Φ t * (1 - Φ x) / φ x) := by
        have hm := mul_millsRatio_le_one (show 0 ≤ -x by linarith)
        rw [← cdf_div_pdf_eq_millsRatio_neg] at hm
        have hstep : (-x) * (Φ t * (1 - Φ x) / φ x) ≤ 1 - Φ x := by
          calc (-x) * (Φ t * (1 - Φ x) / φ x)
              = (1 - Φ x) * ((-x) * (Φ t / φ x)) := by ring
            _ ≤ (1 - Φ x) * ((-x) * (Φ x / φ x)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                  (div_le_div_of_nonneg_right h1 hφ_pos.le) (by linarith))
                  (sub_nonneg.2 (cdf_le_one _ _))
            _ ≤ (1 - Φ x) * 1 := mul_le_mul_of_nonneg_left hm (sub_nonneg.2 (cdf_le_one _ _))
            _ = 1 - Φ x := mul_one _
        linarith
      have hnp : x * (Φ t * (1 - Φ x) / φ x) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hx (div_nonneg (mul_nonneg (cdf_nonneg _ _)
          (sub_nonneg.2 (cdf_le_one _ _))) hφ_pos.le)
      exact ⟨by linarith, by linarith [cdf_nonneg (gaussianReal 0 1) t]⟩

/-- Bound on the variation of `h(x) = x f_t(x)`: `|h(w + u) - h(w)| ≤ (3 + |w|) |u|`. -/
private theorem abs_mul_steinInd_sub_le (t w u : ℝ) :
    |(w + u) * steinInd t (w + u) - w * steinInd t w| ≤ (3 + |w|) * |u| := by
  by_cases hu : 1 < |u|
  · have h1 := abs_mul_steinInd_le_one t (w + u)
    have h2 := abs_mul_steinInd_le_one t w
    calc
      |(w + u) * steinInd t (w + u) - w * steinInd t w|
          ≤ |(w + u) * steinInd t (w + u)| + |w * steinInd t w| := abs_sub _ _
      _ ≤ 2 := by linarith
      _ ≤ 2 * |u| := by linarith
      _ ≤ (3 + |w|) * |u| := by nlinarith [abs_nonneg w, abs_nonneg u]
  · push Not at hu
    set h : ℝ → ℝ := fun x => x * steinInd t x
    have hcont : Continuous h := continuous_id.mul (continuous_steinInd t)
    have hderiv_bdd : ∀ x ≠ t, ∃ d, HasDerivAt h d x ∧ |d| ≤ 2 + |x| := fun x hne => by
      refine ⟨steinInd t x + x * steinIndDeriv t x, ?_, ?_⟩
      · simpa using (hasDerivAt_id' x).fun_mul (hasDerivAt_steinInd_of_ne hne)
      · have h1 : |steinInd t x| ≤ 2 := by
          rw [abs_of_nonneg (steinInd_nonneg t x)]
          refine (steinInd_le_sqrt_pi_div_two t x).trans ?_
          rw [Real.sqrt_le_left (by norm_num)]
          linarith [Real.pi_lt_four]
        have h2 : |x * steinIndDeriv t x| ≤ |x| := by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (abs_steinIndDeriv_le_one t x)
        exact (abs_add_le _ _).trans (by linarith)
    have hseg : ∀ a b : ℝ, a ≤ b → |h b - h a| ≤ (2 + max |a| |b|) * (b - a) := by
      intro a b hab
      have hmax : ∀ x ∈ Ioo a b, 2 + |x| ≤ 2 + max |a| |b| := fun x hx => by
        have : |x| ≤ max |a| |b| := by
          rw [abs_le]
          exact ⟨by linarith [hx.1, neg_abs_le a, le_max_left |a| |b|],
            by linarith [hx.2, le_abs_self b, le_max_right |a| |b|]⟩
        linarith
      by_cases ht : t ∈ Ioo a b
      · have hL := abs_sub_le_of_deriv_le_Ioo ht.1.le hcont.continuousOn fun x hx => by
          obtain ⟨d, hd, hdb⟩ := hderiv_bdd x hx.2.ne
          exact ⟨d, hd, hdb.trans (hmax x ⟨hx.1, hx.2.trans ht.2⟩)⟩
        have hR := abs_sub_le_of_deriv_le_Ioo ht.2.le hcont.continuousOn fun x hx => by
          obtain ⟨d, hd, hdb⟩ := hderiv_bdd x hx.1.ne'
          exact ⟨d, hd, hdb.trans (hmax x ⟨ht.1.trans hx.1, hx.2⟩)⟩
        calc
          |h b - h a| = |(h b - h t) + (h t - h a)| := by ring_nf
          _ ≤ |h b - h t| + |h t - h a| := abs_add_le _ _
          _ ≤ (2 + max |a| |b|) * (b - t) + (2 + max |a| |b|) * (t - a) := add_le_add hR hL
          _ = (2 + max |a| |b|) * (b - a) := by ring
      · refine abs_sub_le_of_deriv_le_Ioo hab hcont.continuousOn fun x hx => ?_
        have hne : x ≠ t := fun h => ht (h ▸ hx)
        obtain ⟨d, hd, hdb⟩ := hderiv_bdd x hne
        exact ⟨d, hd, hdb.trans (hmax x hx)⟩
    have hmw : max |w| |w + u| ≤ |w| + 1 :=
      max_le (by linarith) ((abs_add_le w u).trans (by linarith))
    rcases le_total 0 u with hu0 | hu0
    · rw [abs_of_nonneg hu0]
      exact (hseg w (w + u) (by linarith)).trans (by
        have : w + u - w = u := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (by linarith) hu0)
    · rw [abs_sub_comm, abs_of_nonpos hu0]
      have hmw' : max |w + u| |w| ≤ |w| + 1 := by rw [max_comm]; exact hmw
      exact (hseg (w + u) w (by linarith)).trans (by
        have : w - (w + u) = -u := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (by linarith) (by linarith))

private theorem measurable_steinIndDeriv (t : ℝ) : Measurable (steinIndDeriv t) := by
  unfold steinIndDeriv
  exact (measurable_id.mul (continuous_steinInd t).measurable).add
    (Measurable.ite measurableSet_Iic measurable_const measurable_const) |>.sub measurable_const

/-- Fundamental theorem of calculus for `steinInd`: `f_t(b) - f_t(a) = ∫ y in a..b, D_t(y)`. -/
private theorem steinInd_sub_eq_intervalIntegral (t a b : ℝ) :
    steinInd t b - steinInd t a = ∫ y in a..b, steinIndDeriv t y := by
  have hint (x y : ℝ) : IntervalIntegrable (steinIndDeriv t) volume x y := by
    refine ⟨?_, ?_⟩ <;>
      exact Integrable.of_bound (measurable_steinIndDeriv t).aestronglyMeasurable 1
        (ae_of_all _ fun u => by simpa [Real.norm_eq_abs] using abs_steinIndDeriv_le_one t u)
  have hle : ∀ x y : ℝ, x ≤ y → steinInd t y - steinInd t x = ∫ u in x..y, steinIndDeriv t u := by
    intro x y hxy
    by_cases ht : t ∈ Ioo x y
    · have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1.le
        (continuous_steinInd t).continuousOn
        (fun u hu => hasDerivAt_steinInd_of_ne hu.2.ne) (hint x t)
      have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.2.le
        (continuous_steinInd t).continuousOn
        (fun u hu => hasDerivAt_steinInd_of_ne hu.1.ne') (hint t y)
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint x t) (hint t y), h1, h2]
      ring
    · exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy
        (continuous_steinInd t).continuousOn
        (fun u hu => hasDerivAt_steinInd_of_ne fun h => ht (h ▸ hu)) (hint x y)).symm
  rcases le_total a b with hab | hba
  · exact hle a b hab
  · rw [intervalIntegral.integral_symm, ← hle b a hba]; ring

/-- Parametrized FTC: `f_t(w + u) - f_t(w) = u * ∫ s in Ioc 0 1, D_t(w + s * u)`. -/
private theorem steinInd_add_sub_eq_mul_integral (t w u : ℝ) :
    steinInd t (w + u) - steinInd t w =
      u * ∫ s in Ioc (0 : ℝ) 1, steinIndDeriv t (w + s * u) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, steinInd_sub_eq_intervalIntegral]
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hsub := intervalIntegral.integral_comp_mul_right (fun y => steinIndDeriv t (w + y))
    (a := (0 : ℝ)) (b := 1) hu
  simp only [zero_mul, one_mul, smul_eq_mul] at hsub
  rw [hsub, ← mul_assoc, mul_inv_cancel₀ hu, one_mul,
    intervalIntegral.integral_comp_add_left (steinIndDeriv t) w, add_zero]

/-- **Classical Berry–Esseen theorem (Lyapunov form)**: for independent `L^3` random variables
`X_1, ..., X_n` with `𝔼[X_i] = 0` and `∑ 𝔼[X_i^2] = 1`, for every `t ∈ ℝ`,
`|Pr[∑ X_i ≤ t] - Φ(t)| ≤ 41 ∑ 𝔼|X_i|^3`. -/
theorem berry_esseen_lyapunov {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, MemLp id 3 (μ i))
    (h₁ : ∀ i, ∫ s, s ∂μ i = 0)
    (h₂ : ∑ i, ∫ s, s ^ 2 ∂μ i = 1) (t : ℝ) :
    |(Measure.pi μ).real {z | ∑ i, z i ≤ t} - Φ t| ≤ 41 * ∑ i, ∫ s, |s| ^ 3 ∂μ i := by
  classical
  set P := Measure.pi μ
  set γ : ℝ := ∑ i, ∫ s, |s| ^ 3 ∂μ i
  have hγ_nn : 0 ≤ γ := Finset.sum_nonneg fun i _ => integral_nonneg fun _ => by positivity
  by_cases hγ_big : 1 / 8 ≤ γ
  · have h1 : 0 ≤ P.real {z | ∑ i, z i ≤ t} := measureReal_nonneg
    have h2 : P.real {z | ∑ i, z i ≤ t} ≤ 1 := measureReal_le_one
    have h3 : 0 ≤ Φ t := cdf_nonneg _ _
    have h4 : Φ t ≤ 1 := cdf_le_one _ _
    have hdiff : |P.real {z | ∑ i, z i ≤ t} - Φ t| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  push Not at hγ_big
  have hγ_pos : 0 < γ := by
    by_contra hle
    push Not at hle
    have hγ0 : γ = 0 := le_antisymm hle hγ_nn
    have hvar0 : ∀ i, ∫ s, s ^ 2 ∂μ i = 0 := fun i => by
      have hi0 : ∫ s, |s| ^ 3 ∂μ i = 0 :=
        le_antisymm (by
          have := Finset.single_le_sum (f := fun j => ∫ s, |s| ^ 3 ∂μ j)
            (fun j _ => integral_nonneg fun _ => by positivity) (Finset.mem_univ i)
          linarith) (integral_nonneg fun _ => by positivity)
      have hly := sqrt_integral_sq_pow_three_le (hμ i)
      rw [hi0] at hly
      have hsq0 : √(∫ s, s ^ 2 ∂μ i) = 0 := by
        by_contra hne
        have hpos : 0 < √(∫ s, s ^ 2 ∂μ i) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hne)
        linarith [pow_pos hpos 3]
      have := congrArg (· ^ 2) hsq0
      rwa [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _), zero_pow two_ne_zero] at this
    simp [hvar0] at h₂
  have hmem3 (i : ι) : MemLp (fun z : ι → ℝ => z i) 3 P :=
    (hμ i).comp_measurePreserving (measurePreserving_eval μ i)
  have hmem2 (i : ι) : MemLp id 2 (μ i) := (hμ i).mono_exponent (by norm_num)
  have hW_mem3 : MemLp (fun z : ι → ℝ => ∑ i, z i) 3 P :=
    memLp_finsetSum _ fun i _ => hmem3 i
  have hW_mem2 : MemLp (fun z : ι → ℝ => ∑ i, z i) 2 P :=
    hW_mem3.mono_exponent (by norm_num)
  have hf_bdd : ∀ x, |steinInd t x| ≤ 2 := fun x => by
    rw [abs_of_nonneg (steinInd_nonneg t x)]
    exact (steinInd_le_sqrt_pi_div_two t x).trans (by
      rw [Real.sqrt_le_left (by norm_num)]; linarith [Real.pi_lt_four])
  have hf_cont : Continuous (steinInd t) := continuous_steinInd t
  have hD_meas : Measurable (steinIndDeriv t) := measurable_steinIndDeriv t
  have hD_bdd : ∀ x, |steinIndDeriv t x| ≤ 1 := abs_steinIndDeriv_le_one t
  -- Stein identity: `P[W ≤ t] - Φ t = 𝔼[D_t(W) - W f_t(W)]`
  have hInt_D : Integrable (fun z : ι → ℝ => steinIndDeriv t (∑ i, z i)) P :=
    Integrable.of_bound (hD_meas.comp (by fun_prop)).aestronglyMeasurable 1
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hD_bdd _)
  have hInt_zi_f (i : ι) : Integrable (fun z : ι → ℝ => z i * steinInd t (∑ j, z j)) P :=
    (((hmem3 i).integrable (by norm_num)).abs.const_mul 2).mono'
      (((hmem3 i).aestronglyMeasurable).mul
        (hf_cont.comp_aestronglyMeasurable hW_mem2.aestronglyMeasurable))
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hf_bdd _) (abs_nonneg _))
  have hInt_Wf : Integrable (fun z : ι → ℝ => (∑ i, z i) * steinInd t (∑ j, z j)) P :=
    (integrable_finsetSum _ fun i _ => hInt_zi_f i).congr
      (ae_of_all _ fun z => (Finset.sum_mul _ _ _).symm)
  have hE_meas : MeasurableSet {z : ι → ℝ | ∑ i, z i ≤ t} :=
    measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const
  have hlhs : P.real {z | ∑ i, z i ≤ t} - Φ t =
      ∑ i, ((∫ s, s ^ 2 ∂μ i) * ∫ z, steinIndDeriv t (∑ j, z j) ∂P -
        ∫ z, z i * steinInd t (∑ j, z j) ∂P) := by
    have h1 : P.real {z | ∑ i, z i ≤ t} - Φ t =
        ∫ z, ((if ∑ i, z i ≤ t then (1 : ℝ) else 0) - Φ t) ∂P := by
      rw [integral_sub ((integrable_const 1).indicator hE_meas |>.congr (ae_of_all _ fun z => by
          by_cases h : ∑ i, z i ≤ t <;> simp [Set.indicator, h])) (integrable_const _),
        integral_const, probReal_univ, smul_eq_mul, one_mul]
      congr 1
      rw [← integral_indicator_one hE_meas]
      exact integral_congr_ae (ae_of_all _ fun z => by by_cases h : ∑ i, z i ≤ t <;> simp [h])
    rw [h1]
    have h2 : ∫ z, ((if ∑ i, z i ≤ t then (1 : ℝ) else 0) - Φ t) ∂P =
        ∫ z, steinIndDeriv t (∑ j, z j) ∂P - ∫ z, (∑ j, z j) * steinInd t (∑ j, z j) ∂P := by
      rw [← integral_sub hInt_D hInt_Wf]
      exact integral_congr_ae (ae_of_all _ fun z => by unfold steinIndDeriv; ring)
    have hsum_wf : ∫ z, (∑ j, z j) * steinInd t (∑ j, z j) ∂P =
        ∑ i, ∫ z, z i * steinInd t (∑ j, z j) ∂P := by
      have hsplit : (fun z : ι → ℝ => (∑ i, z i) * steinInd t (∑ j, z j)) =
          fun z => ∑ i, z i * steinInd t (∑ j, z j) := funext fun z => Finset.sum_mul _ _ _
      rw [hsplit, integral_finsetSum _ fun i _ => hInt_zi_f i]
    rw [h2, hsum_wf]
    conv_lhs =>
      rw [← one_mul (∫ z, steinIndDeriv t (∑ j, z j) ∂P), ← h₂, Finset.sum_mul,
        ← Finset.sum_sub_distrib]
  rw [hlhs]
  -- Bound each coordinate `i` by `9 * 𝔼|X_i|^3 + 32 * γ * σ_i^2`, summing to `41 * γ`!
  have hcoord : ∀ i : ι,
      |(∫ s, s ^ 2 ∂μ i) * ∫ z, steinIndDeriv t (∑ j, z j) ∂P -
          ∫ z, z i * steinInd t (∑ j, z j) ∂P| ≤
        9 * ∫ s, |s| ^ 3 ∂μ i + 32 * γ * ∫ s, s ^ 2 ∂μ i := by
    intro i
    set σi2 : ℝ := ∫ s, s ^ 2 ∂μ i
    have hσi2_nn : 0 ≤ σi2 := integral_nonneg fun _ => sq_nonneg _
    have hσi2_lt : σi2 < 1 / 4 := by
      have hly := sqrt_integral_sq_pow_three_le (hμ i)
      have h3le : ∫ s, |s| ^ 3 ∂μ i ≤ γ :=
        Finset.single_le_sum (f := fun j => ∫ s, |s| ^ 3 ∂μ j)
          (fun j _ => integral_nonneg fun _ => by positivity) (Finset.mem_univ i)
      have hcube : √σi2 ^ 3 < (1 / 2 : ℝ) ^ 3 := by
        have : (1 / 2 : ℝ) ^ 3 = 1 / 8 := by norm_num
        linarith
      have hsqrt_lt : √σi2 < 1 / 2 := by
        by_contra hge; push Not at hge
        linarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hge 3]
      have hsq : σi2 = √σi2 ^ 2 := (Real.sq_sqrt hσi2_nn).symm
      rw [hsq]; nlinarith [Real.sqrt_nonneg σi2]
    set Wi : (ι → ℝ) → ℝ := fun z => ∑ j ∈ univ.erase i, z j
    have hWi_upd : ∀ v u, Wi (Function.update v i u) = Wi v := fun v u =>
      Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) u v
    have hW_split : ∀ z : ι → ℝ, ∑ j, z j = Wi z + z i := fun z => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_comm]
    -- Concentration bound for `Wi`: `P.real {v | a ≤ Wi v ≤ b} ≤ (b - a) + 16 * γ`
    have hWi_conc : ∀ (u : ℝ),
        P.real {v | t - |u| ≤ Wi v ∧ Wi v ≤ t + |u|} ≤ 2 * |u| + 16 * γ := by
      intro u
      set ν : {j : ι // j ≠ i} → Measure ℝ := fun j => μ j.1
      have hmp := measurePreserving_restrict_ne μ i
      have hWi_eq : ∀ v : ι → ℝ, Wi v = ∑ j : {j : ι // j ≠ i}, v j.1 := fun v => by
        unfold Wi
        symm
        refine Finset.sum_bij (fun (j : {j : ι // j ≠ i}) _ => j.1)
          (fun j _ => Finset.mem_erase.2 ⟨j.2, Finset.mem_univ _⟩)
          (fun j₁ _ j₂ _ h => Subtype.ext h)
          (fun k hk => ⟨⟨k, (Finset.mem_erase.1 hk).1⟩, Finset.mem_univ _, rfl⟩)
          fun _ _ => rfl
      have hVi_eq : ∑ j : {j : ι // j ≠ i}, ∫ s, s ^ 2 ∂ν j = 1 - σi2 := by
        have hsum : ∑ j : {j : ι // j ≠ i}, ∫ s, s ^ 2 ∂ν j =
            ∑ j ∈ univ.erase i, ∫ s, s ^ 2 ∂μ j :=
          Finset.sum_bij (fun (j : {j : ι // j ≠ i}) _ => j.1)
            (fun j _ => Finset.mem_erase.2 ⟨j.2, Finset.mem_univ _⟩)
            (fun j₁ _ j₂ _ h => Subtype.ext h)
            (fun k hk => ⟨⟨k, (Finset.mem_erase.1 hk).1⟩, Finset.mem_univ _, rfl⟩)
            fun _ _ => rfl
        rw [hsum]
        have := Finset.add_sum_erase univ (fun j => ∫ s, s ^ 2 ∂μ j) (Finset.mem_univ i)
        linarith
      have hVi_gt : 3 / 4 < 1 - σi2 := by linarith
      set γi : ℝ := ∑ j : {j : ι // j ≠ i}, ∫ s, |s| ^ 3 ∂ν j
      have hγi_le : γi ≤ γ := by
        have hsum : γi = ∑ j ∈ univ.erase i, ∫ s, |s| ^ 3 ∂μ j :=
          Finset.sum_bij (fun (j : {j : ι // j ≠ i}) _ => j.1)
            (fun j _ => Finset.mem_erase.2 ⟨j.2, Finset.mem_univ _⟩)
            (fun j₁ _ j₂ _ h => Subtype.ext h)
            (fun k hk => ⟨⟨k, (Finset.mem_erase.1 hk).1⟩, Finset.mem_univ _, rfl⟩)
            fun _ _ => rfl
        rw [hsum]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i univ)
          fun j _ _ => integral_nonneg fun _ => by positivity
      have hγi_pos : 0 < γi := by
        by_contra hle; push Not at hle
        have h0 : γi = 0 := le_antisymm hle
          (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => by positivity)
        have hv0 : ∀ j : {j : ι // j ≠ i}, ∫ s, s ^ 2 ∂ν j = 0 := fun j => by
          have hj0 : ∫ s, |s| ^ 3 ∂ν j = 0 := by
            have hle_j : ∫ s, |s| ^ 3 ∂ν j ≤ γi :=
              Finset.single_le_sum (f := fun k : {j : ι // j ≠ i} => ∫ s, |s| ^ 3 ∂ν k)
                (fun k _ => integral_nonneg fun _ => by positivity) (Finset.mem_univ j)
            exact le_antisymm (by linarith) (integral_nonneg fun _ => by positivity)
          have hly := sqrt_integral_sq_pow_three_le (hμ j.1)
          change √(∫ s, s ^ 2 ∂ν j) ^ 3 ≤ ∫ s, |s| ^ 3 ∂ν j at hly
          rw [hj0] at hly
          have hsq0 : √(∫ s, s ^ 2 ∂ν j) = 0 := by
            by_contra hne
            linarith [pow_pos (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hne)) 3]
          have := congrArg (· ^ 2) hsq0
          rwa [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _), zero_pow two_ne_zero] at this
        simp [hv0] at hVi_eq
        linarith
      have hset_eq : {v : ι → ℝ | t - |u| ≤ Wi v ∧ Wi v ≤ t + |u|} =
          (fun (v : ι → ℝ) (j : {j : ι // j ≠ i}) => v j.1) ⁻¹'
            {w | t - |u| ≤ ∑ j, w j ∧ ∑ j, w j ≤ t + |u|} := by
        ext v; simp [hWi_eq]
      have hS_meas : MeasurableSet {w : {j : ι // j ≠ i} → ℝ |
          t - |u| ≤ ∑ j, w j ∧ ∑ j, w j ≤ t + |u|} := by
        have hm : Measurable (fun w : {j : ι // j ≠ i} → ℝ => ∑ j, w j) :=
          Finset.measurable_sum _ fun j _ => measurable_pi_apply j
        exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
      rw [hset_eq, hmp.measureReal_preimage hS_meas.nullMeasurableSet]
      have hc := measureReal_sum_mem_Icc_le ν (fun j => hμ j.1) (fun j => h₁ j.1)
        hVi_eq (by linarith) rfl hγi_pos (by linarith [abs_nonneg u] : t - |u| ≤ t + |u|)
      have hsqrtV_ge : 3 / 4 ≤ √(1 - σi2) := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]; norm_num; linarith
      have hVsqrtV_ge : 1 / 2 ≤ (1 - σi2) * √(1 - σi2) := by nlinarith
      have h1 : 2 / (3 * √(1 - σi2)) * (t + |u| - (t - |u|)) ≤ 2 * |u| := by
        rw [show t + |u| - (t - |u|) = 2 * |u| by ring]
        have hcoef : 2 / (3 * √(1 - σi2)) * 2 ≤ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; linarith
        calc 2 / (3 * √(1 - σi2)) * (2 * |u|) = (2 / (3 * √(1 - σi2)) * 2) * |u| := by ring
          _ ≤ 2 * |u| := mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
      have h2 : 8 * γi / ((1 - σi2) * √(1 - σi2)) ≤ 16 * γ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    -- Average bound on `|D_t(Wi + u) - D_t(Wi)|` for fixed `u`: `≤ 6 |u| + 16 γ`
    have hWi_abs_le : ∫ v, |Wi v| ∂P ≤ 1 := by
      have hmp := measurePreserving_restrict_ne μ i
      have hWi_eq : ∀ v : ι → ℝ, Wi v = ∑ j : {j : ι // j ≠ i}, v j.1 := fun v => by
        unfold Wi; symm
        refine Finset.sum_bij (fun (j : {j : ι // j ≠ i}) _ => j.1)
          (fun j _ => Finset.mem_erase.2 ⟨j.2, Finset.mem_univ _⟩)
          (fun j₁ _ j₂ _ h => Subtype.ext h)
          (fun k hk => ⟨⟨k, (Finset.mem_erase.1 hk).1⟩, Finset.mem_univ _, rfl⟩)
          fun _ _ => rfl
      have hcomp : ∫ v, |Wi v| ∂P =
          ∫ w, |∑ j : {j : ι // j ≠ i}, w j| ∂Measure.pi (fun j : {j : ι // j ≠ i} => μ j.1) := by
        have hcont_w : Continuous (fun w : {j : ι // j ≠ i} → ℝ => |∑ j, w j|) := by fun_prop
        rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hcont_w.aestronglyMeasurable]
        exact integral_congr_ae (ae_of_all _ fun v => by dsimp only; rw [hWi_eq v])
      rw [hcomp]
      refine (integral_abs_sum_le_sqrt_sum_sq (fun j : {j : ι // j ≠ i} => μ j.1)
        (fun j => hmem2 j.1) (fun j => h₁ j.1)).trans ?_
      rw [Real.sqrt_le_one]
      have hsum : ∑ j : {j : ι // j ≠ i}, ∫ s, s ^ 2 ∂μ j.1 =
          ∑ j ∈ univ.erase i, ∫ s, s ^ 2 ∂μ j :=
        Finset.sum_bij (fun (j : {j : ι // j ≠ i}) _ => j.1)
          (fun j _ => Finset.mem_erase.2 ⟨j.2, Finset.mem_univ _⟩)
          (fun j₁ _ j₂ _ h => Subtype.ext h)
          (fun k hk => ⟨⟨k, (Finset.mem_erase.1 hk).1⟩, Finset.mem_univ _, rfl⟩)
          fun _ _ => rfl
      rw [hsum]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i univ)
        fun j _ _ => integral_nonneg fun _ => sq_nonneg _).trans_eq h₂
    have hD_shift : ∀ u : ℝ,
        ∫ v, |steinIndDeriv t (Wi v + u) - steinIndDeriv t (Wi v)| ∂P ≤ 6 * |u| + 16 * γ := by
      intro u
      have hWi_mem2 : MemLp Wi 2 P :=
        memLp_finsetSum _ fun j _ => (hmem3 j).mono_exponent (by norm_num)
      have hWi_int : Integrable (fun v => |Wi v|) P := (hWi_mem2.integrable one_le_two).abs
      set A : Set (ι → ℝ) := {v | t - |u| ≤ Wi v ∧ Wi v ≤ t + |u|}
      have hA_meas : MeasurableSet A := by
        have hm : Measurable Wi := Finset.measurable_sum _ fun j _ => measurable_pi_apply j
        exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
      have hD_int1 : Integrable (fun v => steinIndDeriv t (Wi v + u)) P :=
        Integrable.of_bound
          (hD_meas.comp ((by fun_prop : Measurable Wi).add measurable_const)).aestronglyMeasurable
          1 (ae_of_all _ fun _ => by simpa [Real.norm_eq_abs] using hD_bdd _)
      have hD_int2 : Integrable (fun v => steinIndDeriv t (Wi v)) P :=
        Integrable.of_bound (hD_meas.comp (by fun_prop : Measurable Wi)).aestronglyMeasurable
          1 (ae_of_all _ fun _ => by simpa [Real.norm_eq_abs] using hD_bdd _)
      have hrhs_int : Integrable (fun v => (3 + |Wi v|) * |u| + A.indicator 1 v) P :=
        (((integrable_const 3).add hWi_int).mul_const |u|).add
          ((integrable_const 1).indicator hA_meas)
      have hpt : ∀ v, |steinIndDeriv t (Wi v + u) - steinIndDeriv t (Wi v)| ≤
          (3 + |Wi v|) * |u| + A.indicator 1 v := fun v => by
        unfold steinIndDeriv
        have heq : (Wi v + u) * steinInd t (Wi v + u) + (if Wi v + u ≤ t then 1 else 0) - Φ t -
            (Wi v * steinInd t (Wi v) + (if Wi v ≤ t then 1 else 0) - Φ t) =
            ((Wi v + u) * steinInd t (Wi v + u) - Wi v * steinInd t (Wi v)) +
            ((if Wi v + u ≤ t then (1 : ℝ) else 0) - (if Wi v ≤ t then 1 else 0)) := by ring
        rw [heq]
        refine (abs_add_le _ _).trans (add_le_add (abs_mul_steinInd_sub_le t (Wi v) u) ?_)
        by_cases h1 : Wi v + u ≤ t <;> by_cases h2 : Wi v ≤ t
        · simp [h1, h2, Set.indicator_apply_nonneg]
        · have hvA : v ∈ A := ⟨by linarith [abs_nonneg u], by linarith [neg_abs_le u]⟩
          simp [h1, h2, Set.indicator_of_mem hvA]
        · have hvA : v ∈ A := ⟨by linarith [le_abs_self u], by linarith [abs_nonneg u]⟩
          simp [h1, h2, Set.indicator_of_mem hvA]
        · simp [h1, h2, Set.indicator_apply_nonneg]
      calc
        ∫ v, |steinIndDeriv t (Wi v + u) - steinIndDeriv t (Wi v)| ∂P
            ≤ ∫ v, ((3 + |Wi v|) * |u| + A.indicator 1 v) ∂P :=
              integral_mono (hD_int1.sub hD_int2).abs hrhs_int hpt
        _ = (3 + ∫ v, |Wi v| ∂P) * |u| + P.real A := by
              have h1 : Integrable (fun v => (3 + |Wi v|) * |u|) P :=
                ((integrable_const 3).add hWi_int).mul_const |u|
              have h2 : Integrable (fun v => A.indicator (1 : (ι → ℝ) → ℝ) v) P :=
                (integrable_const (1 : ℝ)).indicator hA_meas
              rw [integral_add h1 h2, integral_mul_const,
                integral_add (integrable_const 3) hWi_int, integral_const, probReal_univ,
                smul_eq_mul, one_mul, integral_indicator_one hA_meas]
        _ ≤ 4 * |u| + (2 * |u| + 16 * γ) := by
              have hA_le := hWi_conc u
              nlinarith [abs_nonneg u]
        _ = 6 * |u| + 16 * γ := by ring
    -- Split `σ_i^2 𝔼[D_t(W)] - 𝔼[X_i f_t(W)]` around `σ_i^2 𝔼[D_t(W_i)]`
    have hInt_DWi : Integrable (fun v => steinIndDeriv t (Wi v)) P :=
      Integrable.of_bound (hD_meas.comp (by fun_prop : Measurable Wi)).aestronglyMeasurable
        1 (ae_of_all _ fun _ => by simpa [Real.norm_eq_abs] using hD_bdd _)
    -- Term A: `σ_i^2 * |𝔼[D_t(W) - D_t(W_i)]| ≤ 6 𝔼|X_i|^3 + 16 γ σ_i^2`
    have hTermA :
        σi2 * |∫ z, steinIndDeriv t (∑ j, z j) ∂P - ∫ z, steinIndDeriv t (Wi z) ∂P| ≤
          6 * ∫ s, |s| ^ 3 ∂μ i + 16 * γ * σi2 := by
      have hD_sub : Integrable (fun z : ι → ℝ =>
          steinIndDeriv t (∑ j, z j) - steinIndDeriv t (Wi z)) P := hInt_D.sub hInt_DWi
      have hdiff_eq :
          ∫ z, steinIndDeriv t (∑ j, z j) ∂P - ∫ z, steinIndDeriv t (Wi z) ∂P =
            ∫ u, ∫ v, (steinIndDeriv t (Wi v + u) - steinIndDeriv t (Wi v)) ∂P ∂μ i := by
        rw [← integral_sub hInt_D hInt_DWi, ← integral_integral_update_swap μ hD_sub i]
        refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun v => ?_))
        dsimp only
        rw [hW_split, Function.update_self, hWi_upd]
      rw [hdiff_eq]
      have hbound :
          |∫ u, ∫ v, (steinIndDeriv t (Wi v + u) - steinIndDeriv t (Wi v)) ∂P ∂μ i| ≤
            6 * ∫ s, |s| ∂μ i + 16 * γ := by
        have hF_int : Integrable
            (fun u => ∫ v, (steinIndDeriv t (Wi v + u) - steinIndDeriv t (Wi v)) ∂P) (μ i) := by
          have h1 := ((measurePreserving_update μ i).integrable_comp_of_integrable
            hD_sub).integral_prod_right
          refine h1.congr (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun v => ?_))
          dsimp only [Function.comp_apply]
          rw [hW_split, Function.update_self, hWi_upd]
        refine abs_integral_le_integral_abs.trans ?_
        calc
          ∫ u, |∫ v, (steinIndDeriv t (Wi v + u) - steinIndDeriv t (Wi v)) ∂P| ∂μ i
              ≤ ∫ u, (6 * |u| + 16 * γ) ∂μ i := by
                refine integral_mono hF_int.abs
                  (((integrable_abs_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 1)
                    (by norm_num)).congr (ae_of_all _ fun s => by simp)).const_mul 6 |>.add
                    (integrable_const _)) fun u => ?_
                exact abs_integral_le_integral_abs.trans (hD_shift u)
          _ = 6 * ∫ s, |s| ∂μ i + 16 * γ := by
                rw [integral_add
                  (((integrable_abs_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 1)
                    (by norm_num)).congr (ae_of_all _ fun s => by simp)).const_mul 6)
                  (integrable_const _), integral_const_mul, integral_const, probReal_univ,
                  smul_eq_mul, one_mul]
      have hly := integral_sq_mul_integral_abs_le (hμ i)
      calc
        σi2 * |∫ u, ∫ v, (steinIndDeriv t (Wi v + u) - steinIndDeriv t (Wi v)) ∂P ∂μ i|
            ≤ σi2 * (6 * ∫ s, |s| ∂μ i + 16 * γ) := mul_le_mul_of_nonneg_left hbound hσi2_nn
        _ ≤ 6 * ∫ s, |s| ^ 3 ∂μ i + 16 * γ * σi2 := by linarith
    -- Term B: `|𝔼[X_i f_t(W)] - σ_i^2 𝔼[D_t(W_i)]| ≤ 3 𝔼|X_i|^3 + 16 γ σ_i^2`
    have hTermB :
        |∫ z, z i * steinInd t (∑ j, z j) ∂P - σi2 * ∫ z, steinIndDeriv t (Wi z) ∂P| ≤
          3 * ∫ s, |s| ^ 3 ∂μ i + 16 * γ * σi2 := by
      have hInt_zi_fWi : Integrable (fun z : ι → ℝ => z i * steinInd t (Wi z)) P :=
        (((hmem3 i).integrable (by norm_num)).abs.const_mul 2).mono'
          (((hmem3 i).aestronglyMeasurable).mul
            (hf_cont.comp_aestronglyMeasurable (by fun_prop : Measurable Wi).aestronglyMeasurable))
          (ae_of_all _ fun z => by
            rw [Real.norm_eq_abs, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hf_bdd _) (abs_nonneg _))
      have hzero_fWi : ∫ z, z i * steinInd t (Wi z) ∂P = 0 := by
        rw [show P = Measure.pi μ from rfl, ← integral_integral_update μ hInt_zi_fWi i]
        refine integral_eq_zero_of_ae (ae_of_all _ fun v => ?_)
        simp_rw [Function.update_self, hWi_upd]
        rw [integral_mul_const, h₁ i, zero_mul]; rfl
      have hInt_zi2_DWi : Integrable (fun z : ι → ℝ => z i ^ 2 * steinIndDeriv t (Wi z)) P := by
        refine integrable_of_integrable_update μ i
          ((((hmem3 i).aestronglyMeasurable).pow 2).mul
            (hD_meas.comp (by fun_prop : Measurable Wi)).aestronglyMeasurable) ?_
        have hprod : Integrable (fun p : (ι → ℝ) × ℝ => steinIndDeriv t (Wi p.1) * p.2 ^ 2)
            (P.prod (μ i)) :=
          hInt_DWi.mul_prod (integrable_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 2)
            (by norm_num))
        exact hprod.congr (ae_of_all _ fun p => by simp [Function.update_self, hWi_upd, mul_comm])
      have hsq_DWi : ∫ z, z i ^ 2 * steinIndDeriv t (Wi z) ∂P =
          σi2 * ∫ z, steinIndDeriv t (Wi z) ∂P := by
        rw [show P = Measure.pi μ from rfl, ← integral_integral_update μ hInt_zi2_DWi i]
        simp_rw [Function.update_self, hWi_upd, integral_mul_const]
        rw [integral_const_mul]
      have hsub12 : Integrable (fun z : ι → ℝ =>
          z i * steinInd t (∑ j, z j) - z i * steinInd t (Wi z)) P :=
        (hInt_zi_f i).sub hInt_zi_fWi
      have hsub123 : Integrable (fun z : ι → ℝ =>
          z i * steinInd t (∑ j, z j) - z i * steinInd t (Wi z) -
            z i ^ 2 * steinIndDeriv t (Wi z)) P :=
        hsub12.sub hInt_zi2_DWi
      have hsub_eq :
          ∫ z, z i * steinInd t (∑ j, z j) ∂P - σi2 * ∫ z, steinIndDeriv t (Wi z) ∂P =
            ∫ u, (u ^ 2 * ∫ s in Ioc (0 : ℝ) 1,
              (∫ v, (steinIndDeriv t (Wi v + s * u) - steinIndDeriv t (Wi v)) ∂P)) ∂μ i := by
        have hzero_sub : ∫ z, z i * steinInd t (∑ j, z j) ∂P =
            ∫ z, z i * steinInd t (∑ j, z j) ∂P - ∫ z, z i * steinInd t (Wi z) ∂P := by
          rw [hzero_fWi, sub_zero]
        rw [← hsq_DWi, hzero_sub, ← integral_sub (hInt_zi_f i) hInt_zi_fWi,
          ← integral_sub hsub12 hInt_zi2_DWi,
          ← integral_integral_update_swap μ hsub123 i]
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        have hinner_eq : ∀ v : ι → ℝ,
            Function.update v i u i * steinInd t (∑ j, Function.update v i u j) -
                Function.update v i u i * steinInd t (Wi (Function.update v i u)) -
                Function.update v i u i ^ 2 * steinIndDeriv t (Wi (Function.update v i u)) =
              u ^ 2 * ∫ s in Ioc (0 : ℝ) 1,
                (steinIndDeriv t (Wi v + s * u) - steinIndDeriv t (Wi v)) := fun v => by
          rw [hW_split, Function.update_self, hWi_upd]
          have hftc := steinInd_add_sub_eq_mul_integral t (Wi v) u
          have h1 : u * steinInd t (Wi v + u) - u * steinInd t (Wi v) =
              u ^ 2 * ∫ s in Ioc (0 : ℝ) 1, steinIndDeriv t (Wi v + s * u) := by
            calc u * steinInd t (Wi v + u) - u * steinInd t (Wi v)
                = u * (steinInd t (Wi v + u) - steinInd t (Wi v)) := by ring
              _ = u ^ 2 * ∫ s in Ioc (0 : ℝ) 1, steinIndDeriv t (Wi v + s * u) := by
                    rw [hftc]; ring
          have hconst : ∫ _s in Ioc (0 : ℝ) 1, steinIndDeriv t (Wi v) = steinIndDeriv t (Wi v) := by
            rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc]; norm_num
          have hint1 : IntegrableOn (fun s => steinIndDeriv t (Wi v + s * u)) (Ioc (0 : ℝ) 1) :=
            Integrable.of_bound (hD_meas.comp (measurable_const.add
              (measurable_id.mul measurable_const))).aestronglyMeasurable 1
              (ae_of_all _ fun _ => by simpa [Real.norm_eq_abs] using hD_bdd _)
          rw [h1, integral_sub hint1 (integrableOn_const (hs := measure_Ioc_lt_top.ne)), hconst]
          ring
        dsimp only [Function.comp_apply]
        simp_rw [hinner_eq, integral_const_mul]
        congr 1
        have hF_prod : Integrable
            (fun q : (ι → ℝ) × ℝ => steinIndDeriv t (Wi q.1 + q.2 * u) - steinIndDeriv t (Wi q.1))
            (P.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
          have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
            ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
          refine Integrable.of_bound ?_ 2 (ae_of_all _ fun q => ?_)
          · exact ((hD_meas.comp (((by fun_prop : Measurable Wi).comp measurable_fst).add
              (measurable_snd.mul measurable_const))).sub
              (hD_meas.comp
                ((by fun_prop : Measurable Wi).comp measurable_fst))).aestronglyMeasurable
          · rw [Real.norm_eq_abs]
            exact (abs_sub _ _).trans (by linarith [hD_bdd (Wi q.1 + q.2 * u), hD_bdd (Wi q.1)])
        exact integral_integral_swap hF_prod
      rw [hsub_eq]
      have houter_int : Integrable (fun u => u ^ 2 * ∫ s in Ioc (0 : ℝ) 1,
          (∫ v, (steinIndDeriv t (Wi v + s * u) - steinIndDeriv t (Wi v)) ∂P)) (μ i) := by
        have h1 := ((measurePreserving_update μ i).integrable_comp_of_integrable
          hsub123).integral_prod_right
        refine h1.congr (ae_of_all _ fun u => ?_)
        have hinner_eq : ∀ v : ι → ℝ,
            Function.update v i u i * steinInd t (∑ j, Function.update v i u j) -
                Function.update v i u i * steinInd t (Wi (Function.update v i u)) -
                Function.update v i u i ^ 2 * steinIndDeriv t (Wi (Function.update v i u)) =
              u ^ 2 * ∫ s in Ioc (0 : ℝ) 1,
                (steinIndDeriv t (Wi v + s * u) - steinIndDeriv t (Wi v)) := fun v => by
          rw [hW_split, Function.update_self, hWi_upd]
          have hftc := steinInd_add_sub_eq_mul_integral t (Wi v) u
          have hconst : ∫ _s in Ioc (0 : ℝ) 1, steinIndDeriv t (Wi v) = steinIndDeriv t (Wi v) := by
            rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc]; norm_num
          have hint1 : IntegrableOn (fun s => steinIndDeriv t (Wi v + s * u)) (Ioc (0 : ℝ) 1) :=
            Integrable.of_bound (hD_meas.comp (measurable_const.add
              (measurable_id.mul measurable_const))).aestronglyMeasurable 1
              (ae_of_all _ fun _ => by simpa [Real.norm_eq_abs] using hD_bdd _)
          rw [integral_sub hint1 (integrableOn_const (hs := measure_Ioc_lt_top.ne)), hconst]
          linear_combination u * hftc
        dsimp only [Function.comp_apply]
        simp_rw [hinner_eq, integral_const_mul]
        congr 1
        have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
        have hF_prod : Integrable
            (fun q : (ι → ℝ) × ℝ => steinIndDeriv t (Wi q.1 + q.2 * u) - steinIndDeriv t (Wi q.1))
            (P.prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
          Integrable.of_bound
            (((hD_meas.comp (((by fun_prop : Measurable Wi).comp measurable_fst).add
              (measurable_snd.mul measurable_const))).sub
              (hD_meas.comp
                ((by fun_prop : Measurable Wi).comp measurable_fst))).aestronglyMeasurable)
            2 (ae_of_all _ fun q => by
              rw [Real.norm_eq_abs]
              exact (abs_sub _ _).trans (by linarith [hD_bdd (Wi q.1 + q.2 * u), hD_bdd (Wi q.1)]))
        exact integral_integral_swap hF_prod
      have hrhs_int : Integrable (fun u : ℝ => 3 * |u| ^ 3 + 16 * γ * u ^ 2) (μ i) :=
        ((integrable_abs_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j :=
          3) le_rfl).const_mul 3).add
          ((integrable_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j :=
            2) (by norm_num)).const_mul _)
      refine abs_integral_le_integral_abs.trans ?_
      calc
        ∫ u, |u ^ 2 * ∫ s in Ioc (0 : ℝ) 1,
            (∫ v, (steinIndDeriv t (Wi v + s * u) - steinIndDeriv t (Wi v)) ∂P)| ∂μ i
            ≤ ∫ u, (3 * |u| ^ 3 + 16 * γ * u ^ 2) ∂μ i := by
              refine integral_mono houter_int.abs hrhs_int fun u => ?_
              rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
              have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
                ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
              have hF_prod : Integrable
                  (fun q : (ι → ℝ) × ℝ =>
                    steinIndDeriv t (Wi q.1 + q.2 * u) - steinIndDeriv t (Wi q.1))
                  (P.prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
                Integrable.of_bound
                  (((hD_meas.comp (((by fun_prop : Measurable Wi).comp measurable_fst).add
                    (measurable_snd.mul measurable_const))).sub
                    (hD_meas.comp
                      ((by fun_prop : Measurable Wi).comp measurable_fst))).aestronglyMeasurable)
                  2 (ae_of_all _ fun q => by
                    rw [Real.norm_eq_abs]
                    have hb1 := hD_bdd (Wi q.1 + q.2 * u)
                    have hb2 := hD_bdd (Wi q.1)
                    exact (abs_sub _ _).trans (by linarith))
              have hs_int : IntegrableOn (fun s =>
                  ∫ v, (steinIndDeriv t (Wi v + s * u) - steinIndDeriv t (Wi v)) ∂P)
                  (Ioc (0 : ℝ) 1) := hF_prod.integral_prod_right
              have hlin_int : IntegrableOn (fun s : ℝ => 6 * |u| * s + 16 * γ) (Ioc (0 : ℝ) 1) :=
                ((continuous_const.mul continuous_id).add continuous_const).integrableOn_Ioc
              have hinner_le :
                  |∫ s in Ioc (0 : ℝ) 1,
                    ∫ v, (steinIndDeriv t (Wi v + s * u) - steinIndDeriv t (Wi v)) ∂P| ≤
                    3 * |u| + 16 * γ := by
                refine abs_integral_le_integral_abs.trans ?_
                calc
                  ∫ s in Ioc (0 : ℝ) 1,
                      |∫ v, (steinIndDeriv t (Wi v + s * u) - steinIndDeriv t (Wi v)) ∂P|
                      ≤ ∫ s in Ioc (0 : ℝ) 1, (6 * |u| * s + 16 * γ) := by
                        refine setIntegral_mono_on hs_int.abs hlin_int measurableSet_Ioc
                          fun s hs => ?_
                        refine abs_integral_le_integral_abs.trans ((hD_shift (s * u)).trans_eq ?_)
                        rw [abs_mul, abs_of_pos hs.1]; ring
                  _ = 3 * |u| + 16 * γ := by
                        rw [← intervalIntegral.integral_of_le zero_le_one,
                          intervalIntegral.integral_add
                            (Continuous.intervalIntegrable (by fun_prop) 0 1)
                            intervalIntegrable_const,
                          intervalIntegral.integral_const_mul, integral_id,
                          intervalIntegral.integral_const]
                        norm_num; ring
              calc
                u ^ 2 * |∫ s in Ioc (0 : ℝ) 1,
                    ∫ v, (steinIndDeriv t (Wi v + s * u) - steinIndDeriv t (Wi v)) ∂P|
                    ≤ u ^ 2 * (3 * |u| + 16 * γ) :=
                      mul_le_mul_of_nonneg_left hinner_le (sq_nonneg u)
                _ = 3 * |u| ^ 3 + 16 * γ * u ^ 2 := by rw [← sq_abs u]; ring
        _ = 3 * ∫ s, |s| ^ 3 ∂μ i + 16 * γ * σi2 := by
              rw [integral_add
                ((integrable_abs_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 3)
                  le_rfl).const_mul 3)
                ((integrable_pow_of_memLp (n := 3) (by exact_mod_cast hμ i) (j := 2)
                  (by norm_num)).const_mul _),
                integral_const_mul, integral_const_mul]
    have hsplit :
        σi2 * ∫ z, steinIndDeriv t (∑ j, z j) ∂P - ∫ z, z i * steinInd t (∑ j, z j) ∂P =
          σi2 * (∫ z, steinIndDeriv t (∑ j, z j) ∂P - ∫ z, steinIndDeriv t (Wi z) ∂P) -
            (∫ z, z i * steinInd t (∑ j, z j) ∂P - σi2 * ∫ z, steinIndDeriv t (Wi z) ∂P) := by
      ring
    rw [hsplit]
    calc
      |σi2 * (∫ z, steinIndDeriv t (∑ j, z j) ∂P - ∫ z, steinIndDeriv t (Wi z) ∂P) -
          (∫ z, z i * steinInd t (∑ j, z j) ∂P - σi2 * ∫ z, steinIndDeriv t (Wi z) ∂P)|
          ≤ |σi2 * (∫ z, steinIndDeriv t (∑ j, z j) ∂P - ∫ z, steinIndDeriv t (Wi z) ∂P)| +
            |∫ z, z i * steinInd t (∑ j, z j) ∂P - σi2 * ∫ z, steinIndDeriv t (Wi z) ∂P| :=
              abs_sub _ _
      _ = σi2 * |∫ z, steinIndDeriv t (∑ j, z j) ∂P - ∫ z, steinIndDeriv t (Wi z) ∂P| +
            |∫ z, z i * steinInd t (∑ j, z j) ∂P - σi2 * ∫ z, steinIndDeriv t (Wi z) ∂P| := by
              rw [abs_mul, abs_of_nonneg hσi2_nn]
      _ ≤ (6 * ∫ s, |s| ^ 3 ∂μ i + 16 * γ * σi2) + (3 * ∫ s, |s| ^ 3 ∂μ i + 16 * γ * σi2) :=
            add_le_add hTermA hTermB
      _ = 9 * ∫ s, |s| ^ 3 ∂μ i + 32 * γ * σi2 := by ring
  calc
    |∑ i, ((∫ s, s ^ 2 ∂μ i) * ∫ z, steinIndDeriv t (∑ j, z j) ∂P -
        ∫ z, z i * steinInd t (∑ j, z j) ∂P)|
        ≤ ∑ i, |(∫ s, s ^ 2 ∂μ i) * ∫ z, steinIndDeriv t (∑ j, z j) ∂P -
            ∫ z, z i * steinInd t (∑ j, z j) ∂P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (9 * ∫ s, |s| ^ 3 ∂μ i + 32 * γ * ∫ s, s ^ 2 ∂μ i) :=
          Finset.sum_le_sum fun i _ => hcoord i
    _ = 9 * γ + 32 * γ * 1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h₂]
    _ = 41 * γ := by ring

end BerryEsseenStein

end CslibFrontier.Probability
