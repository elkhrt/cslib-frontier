module

public import CslibFrontier.Probability.Chernoff
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strict Multiplicative Chernoff Bounds

Strict multiplicative Chernoff inequalities for sums of independent `[0, 1]`-valued random
variables on general probability spaces and on finite product distributions
(`Cslib.Probability.PMF.pi`).

## Main results

* `CslibFrontier.Probability.Chernoff.chernoff_lower_lt`,
  `CslibFrontier.Probability.Chernoff.chernoff_upper_lt`: strict multiplicative Chernoff bounds
  for sums of independent `{0, 1}`-valued random variables.
* `CslibFrontier.Probability.Chernoff.chernoff_bounds_lower_lt`,
  `CslibFrontier.Probability.Chernoff.chernoff_bounds_upper_lt`: strict multiplicative bounds
  parameterized by upper and lower bounds `μ₁ ≥ E[X] ≥ μ₂ ≥ 0` on the mean.
* `CslibFrontier.Probability.Chernoff.pi_sum_le_one_sub_mul_lt_of_pos`,
  `CslibFrontier.Probability.Chernoff.pi_sum_ge_one_add_mul_lt_of_pos`,
  `CslibFrontier.Probability.Chernoff.bernoulli_ge_lt`,
  `CslibFrontier.Probability.Chernoff.bernoulli_le_lt`: strict `PMF.pi` and i.i.d. Bernoulli
  tail bounds.
-/

public section

namespace CslibFrontier.Probability.Chernoff

open MeasureTheory ProbabilityTheory Cslib.Probability.PMF
open scoped BigOperators ENNReal

/-! ### Scalar strict exponential inequalities -/

/-- Strict Taylor bound `exp (-x) < 1 - x + x^2 / 2` for `x > 0`. -/
theorem exp_neg_lt_one_sub_add_sq_div_two {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) < 1 - x + x ^ 2 / 2 := by
  have hq : 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg hx.le
  have hpos : 0 < 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  rw [Real.exp_neg, inv_lt_iff_one_lt_mul₀ (Real.exp_pos x)]
  have hmul : (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) ≤ (1 - x + x ^ 2 / 2) * Real.exp x :=
    mul_le_mul_of_nonneg_left hq hpos.le
  have hpow : 0 < x ^ 4 / 4 := by positivity
  nlinarith

/-- Strict logarithmic-Chernoff inequality `δ - (1 + δ) log (1 + δ) < -δ^2 / 3` for `0 < δ ≤ 1`. -/
theorem sub_one_add_mul_log_lt_neg_sq_div_three {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    δ - (1 + δ) * Real.log (1 + δ) < -(δ ^ 2 / 3) := by
  rcases hδ1.lt_or_eq with hlt | rfl
  · have hlog : 2 * δ / (δ + 2) ≤ Real.log (1 + δ) := Real.le_log_one_add_of_nonneg hδ0.le
    have hstep : δ - (1 + δ) * Real.log (1 + δ) ≤ -(δ ^ 2 / (2 + δ)) := by
      have h1 : (1 + δ) * (2 * δ / (δ + 2)) ≤ (1 + δ) * Real.log (1 + δ) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)
      have h2 : δ - (1 + δ) * (2 * δ / (δ + 2)) = -(δ ^ 2 / (2 + δ)) := by
        have hne : (δ + 2 : ℝ) ≠ 0 := by linarith
        have hne' : (2 + δ : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      linarith
    have hstrict : δ ^ 2 / 3 < δ ^ 2 / (2 + δ) :=
      div_lt_div_of_pos_left (by positivity) (by linarith) (by linarith)
    linarith
  · have hexp2 : Real.exp 2 < 8 := by
      have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have he0 : 0 < Real.exp 1 := Real.exp_pos 1
      have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [hsq]
      nlinarith
    have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hcube : Real.exp (2 / 3) ^ 3 < 2 ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
        exact hexp2
      by_contra hge
      push Not at hge
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hge 3
      linarith
    norm_num
    linarith

/-! ### Measure-theoretic strict multiplicative Chernoff bounds -/

private theorem exp_mul_le_one_add_mul {s : ℝ} (hs : s ∈ Set.Icc 0 1) (t : ℝ) :
    Real.exp (t * s) ≤ 1 + s * (Real.exp t - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ t) (sub_nonneg.mpr hs.2) hs.1
    (sub_add_cancel 1 s)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, mul_comm s t] at h
  linarith

private theorem integrable_of_mem_Icc {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (hbound : ∀ ω, f ω ∈ Set.Icc (0 : ℝ) 1) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound ω).1]
    exact (hbound ω).2)

private theorem integrable_exp_mul_sum_Icc {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hmeas : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * ∑ i, X i ω)) μ := by
  have hfm : Measurable (fun ω => Real.exp (t * ∑ i, X i ω)) :=
    Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun i _ => hmeas i))
  refine Integrable.of_bound hfm.aestronglyMeasurable
    (Real.exp (|t| * Fintype.card ι)) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  have hsum_nn : 0 ≤ ∑ i, X i ω := Finset.sum_nonneg fun i _ => (h01 i ω).1
  have hsum_le : ∑ i, X i ω ≤ Fintype.card ι := by
    calc ∑ i, X i ω ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (h01 i ω).2
      _ = Fintype.card ι := by simp
  calc t * ∑ i, X i ω ≤ |t| * ∑ i, X i ω :=
        mul_le_mul_of_nonneg_right (le_abs_self t) hsum_nn
    _ ≤ |t| * Fintype.card ι := mul_le_mul_of_nonneg_left hsum_le (abs_nonneg t)

private theorem mgf_sum_le_of_iIndepFun {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (h01 : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    mgf (fun ω => ∑ i, X i ω) μ t ≤
      Real.exp ((∑ i, ∫ ω, X i ω ∂μ) * (Real.exp t - 1)) := by
  have hsum : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω; simp only [Finset.sum_apply]
  rw [hsum, hindep.mgf_sum hmeas, Finset.sum_mul, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => mgf_nonneg) fun i _ => ?_
  have hint_exp : Integrable (fun ω => Real.exp (t * X i ω)) μ := by
    refine Integrable.of_bound
      (Real.measurable_exp.comp (measurable_const.mul (hmeas i))).aestronglyMeasurable
      (Real.exp |t|) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc t * X i ω ≤ |t| * X i ω := mul_le_mul_of_nonneg_right (le_abs_self t) (h01 i ω).1
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (h01 i ω).2 (abs_nonneg t)
      _ = |t| := mul_one _
  have hint_X : Integrable (X i) μ := integrable_of_mem_Icc (hmeas i) (h01 i)
  have hint_rhs : Integrable (fun ω => 1 + X i ω * (Real.exp t - 1)) μ :=
    (integrable_const 1).add (hint_X.mul_const _)
  calc mgf (X i) μ t
      = ∫ ω, Real.exp (t * X i ω) ∂μ := rfl
    _ ≤ ∫ ω, (1 + X i ω * (Real.exp t - 1)) ∂μ :=
        integral_mono hint_exp hint_rhs fun ω => exp_mul_le_one_add_mul (h01 i ω) t
    _ = 1 + (∫ ω, X i ω ∂μ) * (Real.exp t - 1) := by
        rw [integral_add (integrable_const 1) (hint_X.mul_const _), integral_const,
          probReal_univ, one_smul, integral_mul_const]
    _ ≤ Real.exp ((∫ ω, X i ω ∂μ) * (Real.exp t - 1)) := by
        linarith [Real.add_one_le_exp ((∫ ω, X i ω ∂μ) * (Real.exp t - 1))]

/-- Strict lower-tail Chernoff bound: for independent `[0, 1]`-valued random variables `X_i` whose
sum has mean at least `μ₂ ≥ 0`, and any `0 < δ ≤ 1`,
`Pr{∑ X_i < (1 - δ) μ₂} < exp (-μ₂ δ^2 / 2)`. -/
theorem chernoff_bounds_lower_lt {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (h01 : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {μ₂ δ : ℝ} (hμ₂_nn : 0 ≤ μ₂) (hμ₂ : μ₂ ≤ ∫ ω, ∑ i, X i ω ∂μ)
    (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) :
    μ.real {ω | ∑ i, X i ω < (1 - δ) * μ₂} < Real.exp (-(μ₂ * δ ^ 2 / 2)) := by
  rcases hμ₂_nn.eq_or_lt with rfl | hμ₂_pos
  · have hempty : {ω | ∑ i, X i ω < (1 - δ) * 0} = ∅ := by
      ext ω
      simp only [mul_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact Finset.sum_nonneg fun i _ => (h01 i ω).1
    rw [hempty, measureReal_empty]
    exact Real.exp_pos _
  · have hsum_int : ∫ ω, ∑ i, X i ω ∂μ = ∑ i, ∫ ω, X i ω ∂μ :=
      integral_finsetSum _ fun i _ => integrable_of_mem_Icc (hmeas i) (h01 i)
    have hmean : μ₂ ≤ ∑ i, ∫ ω, X i ω ∂μ := hsum_int ▸ hμ₂
    have hsub : μ.real {ω | ∑ i, X i ω < (1 - δ) * μ₂} ≤
        μ.real {ω | ∑ i, X i ω ≤ (1 - δ) * μ₂} :=
      measureReal_mono fun _ h => le_of_lt (Set.mem_ofPred_eq.mp h)
    have hch := measure_le_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i, X i ω)
      (t := -δ) ((1 - δ) * μ₂) (neg_nonpos.mpr hδ0.le)
      (integrable_exp_mul_sum_Icc hmeas h01 (-δ))
    have hmgf := mgf_sum_le_of_iIndepFun hindep hmeas h01 (-δ)
    have hexp_le : Real.exp (-δ) - 1 ≤ 0 :=
      sub_nonpos.mpr (Real.exp_le_one_iff.mpr (by linarith))
    have hstrict : Real.exp (-δ) - 1 < -δ + δ ^ 2 / 2 := by
      linarith [exp_neg_lt_one_sub_add_sq_div_two hδ0]
    have hlt_exp : -(-δ) * ((1 - δ) * μ₂) + μ₂ * (Real.exp (-δ) - 1) <
        -(-δ) * ((1 - δ) * μ₂) + μ₂ * (-δ + δ ^ 2 / 2) := by
      have := mul_lt_mul_of_pos_left hstrict hμ₂_pos
      linarith
    calc μ.real {ω | ∑ i, X i ω < (1 - δ) * μ₂}
        ≤ μ.real {ω | ∑ i, X i ω ≤ (1 - δ) * μ₂} := hsub
      _ ≤ Real.exp (-(-δ) * ((1 - δ) * μ₂)) * mgf (fun ω => ∑ i, X i ω) μ (-δ) := hch
      _ ≤ Real.exp (-(-δ) * ((1 - δ) * μ₂)) *
            Real.exp ((∑ i, ∫ ω, X i ω ∂μ) * (Real.exp (-δ) - 1)) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = Real.exp (-(-δ) * ((1 - δ) * μ₂) +
            (∑ i, ∫ ω, X i ω ∂μ) * (Real.exp (-δ) - 1)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(-δ) * ((1 - δ) * μ₂) + μ₂ * (Real.exp (-δ) - 1)) :=
          Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonpos_right hmean hexp_le))
      _ < Real.exp (-(-δ) * ((1 - δ) * μ₂) + μ₂ * (-δ + δ ^ 2 / 2)) :=
          Real.exp_lt_exp.mpr hlt_exp
      _ = Real.exp (-(μ₂ * δ ^ 2 / 2)) := by congr 1; ring

/-- Strict upper-tail Chernoff bound: for independent `[0, 1]`-valued random variables `X_i` whose
sum has mean at most `μ₁`, and any `0 < δ ≤ 1`,
`Pr{∑ X_i > (1 + δ) μ₁} < exp (-μ₁ δ^2 / 3)`. -/
theorem chernoff_bounds_upper_lt {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (h01 : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {μ₁ δ : ℝ} (hμ₁ : ∫ ω, ∑ i, X i ω ∂μ ≤ μ₁) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | (1 + δ) * μ₁ < ∑ i, X i ω} < Real.exp (-(μ₁ * δ ^ 2 / 3)) := by
  have hsum_int : ∫ ω, ∑ i, X i ω ∂μ = ∑ i, ∫ ω, X i ω ∂μ :=
    integral_finsetSum _ fun i _ => integrable_of_mem_Icc (hmeas i) (h01 i)
  have hmean_nn : 0 ≤ ∑ i, ∫ ω, X i ω ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun ω => (h01 i ω).1
  have hμ₁_nn : 0 ≤ μ₁ := hmean_nn.trans (hsum_int ▸ hμ₁)
  rcases hμ₁_nn.eq_or_lt with rfl | hμ₁_pos
  · have hzero : ∫ ω, ∑ i, X i ω ∂μ = 0 :=
      le_antisymm hμ₁ (hsum_int ▸ hmean_nn)
    have hae : (fun ω => ∑ i, X i ω) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => Finset.sum_nonneg fun i _ => (h01 i ω).1)
        (integrable_finsetSum _ fun i _ => integrable_of_mem_Icc (hmeas i) (h01 i))).mp hzero
    have hnull : μ {ω | (1 + δ) * 0 < ∑ i, X i ω} = 0 := by
      refine measure_mono_null (fun ω hω => ?_) hae
      simp only [mul_zero, Set.mem_ofPred_eq] at hω
      exact ne_of_gt hω
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
    exact Real.exp_pos _
  · have hmean : ∑ i, ∫ ω, X i ω ∂μ ≤ μ₁ := hsum_int ▸ hμ₁
    have ht_nn : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
    have hsub : μ.real {ω | (1 + δ) * μ₁ < ∑ i, X i ω} ≤
        μ.real {ω | (1 + δ) * μ₁ ≤ ∑ i, X i ω} :=
      measureReal_mono fun _ h => le_of_lt (Set.mem_ofPred_eq.mp h)
    have hch := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i, X i ω)
      (t := Real.log (1 + δ)) ((1 + δ) * μ₁) ht_nn
      (integrable_exp_mul_sum_Icc hmeas h01 (Real.log (1 + δ)))
    have hmgf := mgf_sum_le_of_iIndepFun hindep hmeas h01 (Real.log (1 + δ))
    have hexp_log : Real.exp (Real.log (1 + δ)) - 1 = δ := by
      rw [Real.exp_log (by linarith)]; ring
    have hstrict := sub_one_add_mul_log_lt_neg_sq_div_three hδ0 hδ1
    calc μ.real {ω | (1 + δ) * μ₁ < ∑ i, X i ω}
        ≤ μ.real {ω | (1 + δ) * μ₁ ≤ ∑ i, X i ω} := hsub
      _ ≤ Real.exp (-Real.log (1 + δ) * ((1 + δ) * μ₁)) *
            mgf (fun ω => ∑ i, X i ω) μ (Real.log (1 + δ)) := hch
      _ ≤ Real.exp (-Real.log (1 + δ) * ((1 + δ) * μ₁)) *
            Real.exp ((∑ i, ∫ ω, X i ω ∂μ) * (Real.exp (Real.log (1 + δ)) - 1)) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = Real.exp (-Real.log (1 + δ) * ((1 + δ) * μ₁) +
            (∑ i, ∫ ω, X i ω ∂μ) * δ) := by rw [hexp_log, ← Real.exp_add]
      _ ≤ Real.exp (μ₁ * (δ - (1 + δ) * Real.log (1 + δ))) := by
          refine Real.exp_le_exp.mpr ?_
          have := mul_le_mul_of_nonneg_right hmean hδ0.le
          linarith
      _ < Real.exp (μ₁ * -(δ ^ 2 / 3)) :=
          Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hstrict hμ₁_pos)
      _ = Real.exp (-(μ₁ * δ ^ 2 / 3)) := by congr 1; ring

/-- Strict lower-tail Chernoff bound for independent `{0, 1}`-valued random variables `X_i` with
`μ = E[∑ X_i]` and `0 < δ ≤ 1`. -/
theorem chernoff_lower_lt {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | ∑ i, X i ω < (1 - δ) * ∫ ω', ∑ i, X i ω' ∂μ} <
      Real.exp (-((∫ ω', ∑ i, X i ω' ∂μ) * δ ^ 2 / 2)) := by
  have hIcc : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1 := fun i ω => by
    rcases h01 i ω with h | h <;> simp [h]
  have hnn : 0 ≤ ∫ ω', ∑ i, X i ω' ∂μ :=
    integral_nonneg fun ω' => Finset.sum_nonneg fun i _ => (hIcc i ω').1
  exact chernoff_bounds_lower_lt hindep hmeas hIcc hnn le_rfl hδ0 hδ1

/-- Strict upper-tail Chernoff bound for independent `{0, 1}`-valued random variables `X_i` with
`μ = E[∑ X_i]` and `0 < δ ≤ 1`. -/
theorem chernoff_upper_lt {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | (1 + δ) * ∫ ω', ∑ i, X i ω' ∂μ < ∑ i, X i ω} <
      Real.exp (-((∫ ω', ∑ i, X i ω' ∂μ) * δ ^ 2 / 3)) := by
  have hIcc : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1 := fun i ω => by
    rcases h01 i ω with h | h <;> simp [h]
  exact chernoff_bounds_upper_lt hindep hmeas hIcc le_rfl hδ0 hδ1

/-! ### Strict `PMF.pi` Chernoff bounds -/

/-- Strict lower-tail Chernoff bound on `PMF.pi` when `μ > 0` and `δ > 0`, including equality
at the threshold `∑ score ≤ (1 - δ) μ`. -/
theorem pi_sum_le_one_sub_mul_lt_of_pos {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) {μ δ : ℝ}
    (hμ_pos : 0 < μ) (hμ : μ ≤ ∑ i, ∑ a, (p i a).toReal * score i a) (hδ : 0 < δ) :
    ((pi p).toOuterMeasure {outcome | ∑ i, score i (outcome i) ≤ (1 - δ) * μ}).toReal <
      Real.exp (-(δ ^ 2 * μ / 2)) := by
  have hbase := pi_sum_le_le_exp p score hscore (neg_nonpos.mpr hδ.le) ((1 - δ) * μ)
  have hexp_le : Real.exp (-δ) - 1 ≤ 0 :=
    sub_nonpos.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hstrict : Real.exp (-δ) - 1 < -δ + δ ^ 2 / 2 := by
    linarith [exp_neg_lt_one_sub_add_sq_div_two hδ]
  have hlt_exp : -(-δ) * ((1 - δ) * μ) + μ * (Real.exp (-δ) - 1) < -(δ ^ 2 * μ / 2) := by
    have := mul_lt_mul_of_pos_left hstrict hμ_pos
    linarith
  refine hbase.trans_lt (Real.exp_lt_exp.mpr ?_)
  have hle : -(-δ) * ((1 - δ) * μ) +
      (∑ i, ∑ a, (p i a).toReal * score i a) * (Real.exp (-δ) - 1) ≤
      -(-δ) * ((1 - δ) * μ) + μ * (Real.exp (-δ) - 1) :=
    add_le_add le_rfl (mul_le_mul_of_nonpos_right hμ hexp_le)
  exact hle.trans_lt hlt_exp

/-- Strict upper-tail Chernoff bound on `PMF.pi` when `μ > 0` and `0 < δ ≤ 1`, including
equality at the threshold `(1 + δ) μ ≤ ∑ score`. -/
theorem pi_sum_ge_one_add_mul_lt_of_pos {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) {μ δ : ℝ}
    (hμ_pos : 0 < μ) (hμ : ∑ i, ∑ a, (p i a).toReal * score i a ≤ μ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ((pi p).toOuterMeasure {outcome | (1 + δ) * μ ≤ ∑ i, score i (outcome i)}).toReal <
      Real.exp (-(δ ^ 2 * μ / 3)) := by
  have hbase := pi_sum_ge_one_add_mul_le_exp_log p score hscore hμ hδ0.le
  have hstrict := sub_one_add_mul_log_lt_neg_sq_div_three hδ0 hδ1
  refine hbase.trans_lt (Real.exp_lt_exp.mpr ?_)
  calc μ * (δ - (1 + δ) * Real.log (1 + δ))
      < μ * -(δ ^ 2 / 3) := mul_lt_mul_of_pos_left hstrict hμ_pos
    _ = -(δ ^ 2 * μ / 3) := by ring

private theorem sum_bool_indicator_mean {m : ℕ} (q : PMF Bool) :
    ∑ _i : Fin m, ∑ b : Bool, (q b).toReal * (if b then (1 : ℝ) else 0) =
      (m : ℝ) * (q true).toReal := by
  simp [Fintype.univ_bool]

/-- Upper tail for `m` i.i.d. Bernoulli(`q`) trials: if `q true ≤ r` with `0 < r`, `0 < m`,
and `0 < δ ≤ 1`, then `Pr[count ≥ (1 + δ) m r] < exp (-δ^2 m r / 3)`. -/
theorem bernoulli_ge_lt {m : ℕ} (hm : 0 < m) (q : PMF Bool) {r δ : ℝ}
    (hr_pos : 0 < r) (hq : (q true).toReal ≤ r) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ((pi fun _ : Fin m => q).toOuterMeasure
        {v | (1 + δ) * ((m : ℝ) * r) ≤ ∑ i : Fin m, if v i then (1 : ℝ) else 0}).toReal <
      Real.exp (-(δ ^ 2 * ((m : ℝ) * r) / 3)) := by
  refine pi_sum_ge_one_add_mul_lt_of_pos (fun _ : Fin m => q)
    (fun _ b => if b then (1 : ℝ) else 0)
    (fun _ b _ => by cases b <;> simp)
    (by positivity) ?_ hδ0 hδ1
  rw [sum_bool_indicator_mean]
  exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg m)

/-- Lower tail for `m` i.i.d. Bernoulli(`q`) trials: if `r ≤ q true` with `0 < r`, `0 < m`,
and `0 < δ`, then `Pr[count ≤ (1 - δ) m r] < exp (-δ^2 m r / 2)`. -/
theorem bernoulli_le_lt {m : ℕ} (hm : 0 < m) (q : PMF Bool) {r δ : ℝ}
    (hr_pos : 0 < r) (hq : r ≤ (q true).toReal) (hδ0 : 0 < δ) :
    ((pi fun _ : Fin m => q).toOuterMeasure
        {v | ∑ i : Fin m, (if v i then (1 : ℝ) else 0) ≤ (1 - δ) * ((m : ℝ) * r)}).toReal <
      Real.exp (-(δ ^ 2 * ((m : ℝ) * r) / 2)) := by
  refine pi_sum_le_one_sub_mul_lt_of_pos (fun _ : Fin m => q)
    (fun _ b => if b then (1 : ℝ) else 0)
    (fun _ b _ => by cases b <;> simp)
    (by positivity) ?_ hδ0
  rw [sum_bool_indicator_mean]
  exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg m)

end CslibFrontier.Probability.Chernoff
