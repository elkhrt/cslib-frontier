/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Moments.SubGaussian

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# General-Filtration Azuma–Hoeffding Inequality

This module proves the sub-Gaussian moment-generating-function (MGF) bound and the one-sided,
two-sided, and empirical-average Azuma–Hoeffding tail inequalities for bounded martingale-difference
sequences on arbitrary measurable spaces equipped with a filtration `(ℱ n)`, requiring no
`StandardBorelSpace` or discrete `PMF` assumption (generalizing the discrete `PMF` version in
`CslibFrontier.Probability.Azuma`).

## Main results

* `CslibFrontier.Probability.Martingale.condExp_exp_mul_le_of_abs_le`: one-step conditional MGF
  bound `μ[fun ω ↦ exp (t * Z ω) | m] ≤ᵐ[μ] fun _ ↦ exp (c ^ 2 * t ^ 2 / 2)`.
* `CslibFrontier.Probability.Martingale.hasSubgaussianMGF_sum_of_martingale_diff`: sub-Gaussian
  MGF bound `HasSubgaussianMGF (∑ i < n, Z i) (∑ i < n, c i ^ 2) μ`.
* `CslibFrontier.Probability.Martingale.measure_sum_ge_le_of_martingale_diff`: one-sided
  Azuma–Hoeffding tail inequality.
* `CslibFrontier.Probability.Martingale.measure_abs_sum_ge_le_of_martingale_diff`: two-sided
  Azuma–Hoeffding tail inequality.
* `CslibFrontier.Probability.Martingale.measure_abs_avg_ge_le_of_martingale_diff`: two-sided
  empirical-average Azuma–Hoeffding inequality for uniformly bounded martingale differences.
-/

public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace CslibFrontier.Probability.Martingale

section AzumaHoeffding

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Convexity inequality on `[-M, M]`: `exp (t * x) ≤ cosh (t * M) + (sinh (t * M) / M) * x`
(with linear coefficient `0` when `M = 0`). -/
private lemma exp_mul_le_cosh_add_mul {M t x : ℝ} (hM : 0 ≤ M) (hx : |x| ≤ M) :
    Real.exp (t * x) ≤
      Real.cosh (t * M) + (if M = 0 then 0 else Real.sinh (t * M) / M) * x := by
  rcases eq_or_lt_of_le hM with rfl | hMpos
  · have hx0 : x = 0 := abs_nonpos_iff.mp hx
    subst hx0
    simp
  · rw [ite_eq_right (fun h ↦ absurd h hMpos.ne')]
    let a : ℝ := (M + x) / (2 * M)
    let b : ℝ := (M - x) / (2 * M)
    have hxb := abs_le.mp hx
    have ha : 0 ≤ a := div_nonneg (by linarith) (by positivity)
    have hb : 0 ≤ b := div_nonneg (by linarith) (by positivity)
    have hab : a + b = 1 := by
      dsimp [a, b]; field_simp [hMpos.ne']; ring
    have hcomb : a * (t * M) + b * (-(t * M)) = t * x := by
      dsimp [a, b]; field_simp [hMpos.ne']; ring
    have hconv := convexOn_exp.2 (Set.mem_univ (t * M)) (Set.mem_univ (-(t * M))) ha hb hab
    simp only [smul_eq_mul] at hconv
    rw [hcomb] at hconv
    refine hconv.trans_eq ?_
    rw [Real.cosh_eq, Real.sinh_eq]
    dsimp [a, b]
    field_simp [hMpos.ne']
    ring

/-- One-step conditional MGF bound: if `|Z| ≤ c` `μ`-a.e. and `μ[Z | m] =ᵐ[μ] 0`, then
`μ[fun ω ↦ exp (t * Z ω) | m] ≤ᵐ[μ] fun _ ↦ exp (c ^ 2 * t ^ 2 / 2)`. -/
theorem condExp_exp_mul_le_of_abs_le [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Z : Ω → ℝ} {c : ℝ≥0}
    (hZ_meas : AEStronglyMeasurable[mΩ] Z μ) (hZ_cond : μ[Z | m] =ᵐ[μ] 0)
    (hZ_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ (c : ℝ)) (t : ℝ) :
    μ[fun ω ↦ Real.exp (t * Z ω) | m] ≤ᵐ[μ]
      fun _ ↦ Real.exp ((c : ℝ) ^ 2 * t ^ 2 / 2) := by
  let α : ℝ := if (c : ℝ) = 0 then 0 else Real.sinh (t * (c : ℝ)) / (c : ℝ)
  have hZ_int : Integrable Z μ :=
    Integrable.of_bound hZ_meas (c : ℝ)
      (hZ_bdd.mono fun ω hω ↦ by simpa [Real.norm_eq_abs] using hω)
  have hexp_int : Integrable (fun ω ↦ Real.exp (t * Z ω)) μ := by
    refine Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable
      (hZ_meas.const_mul t)) (Real.exp (|t| * (c : ℝ))) ?_
    filter_upwards [hZ_bdd] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc t * Z ω ≤ |t * Z ω| := le_abs_self _
      _ = |t| * |Z ω| := abs_mul _ _
      _ ≤ |t| * (c : ℝ) := mul_le_mul_of_nonneg_left hω (abs_nonneg t)
  have hlin_int : Integrable (fun ω ↦ Real.cosh (t * (c : ℝ)) + α * Z ω) μ :=
    (integrable_const _).add (hZ_int.const_mul α)
  have hpt : (fun ω ↦ Real.exp (t * Z ω)) ≤ᵐ[μ]
      fun ω ↦ Real.cosh (t * (c : ℝ)) + α * Z ω :=
    hZ_bdd.mono fun ω hω ↦ exp_mul_le_cosh_add_mul c.2 hω
  have hmono : μ[fun ω ↦ Real.exp (t * Z ω) | m] ≤ᵐ[μ]
      μ[fun ω ↦ Real.cosh (t * (c : ℝ)) + α * Z ω | m] :=
    condExp_mono hexp_int hlin_int hpt
  have hadd : μ[fun ω ↦ Real.cosh (t * (c : ℝ)) + α * Z ω | m] =ᵐ[μ]
      (fun _ ↦ Real.cosh (t * (c : ℝ))) + α • μ[Z | m] := by
    have h1 := condExp_add (integrable_const (Real.cosh (t * (c : ℝ))))
      (hZ_int.const_mul α) m
    have h2 : μ[fun ω ↦ α * Z ω | m] =ᵐ[μ] α • μ[Z | m] := by
      simpa [Pi.smul_def, smul_eq_mul] using condExp_smul α Z m
    filter_upwards [h1, h2] with ω hω1 hω2
    change (μ[(fun _ ↦ Real.cosh (t * (c : ℝ))) + (fun x ↦ α * Z x) | m]) ω =
      Real.cosh (t * (c : ℝ)) + α * (μ[Z | m]) ω
    rw [hω1]
    simp only [Pi.add_apply, condExp_const hm]
    rw [hω2, Pi.smul_apply, smul_eq_mul]
  filter_upwards [hmono, hadd, hZ_cond] with ω h1 h2 h3
  have h4 : (μ[fun ω ↦ Real.cosh (t * (c : ℝ)) + α * Z ω | m]) ω =
      Real.cosh (t * (c : ℝ)) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
    rw [h2, h3, Pi.zero_apply, mul_zero, add_zero]
  rw [h4] at h1
  refine h1.trans ?_
  have hcosh := Real.cosh_le_exp_half_sq (t * (c : ℝ))
  refine hcosh.trans_eq ?_
  congr 1; ring

/-- Partial sums of a bounded martingale-difference sequence adapted to `ℱ` (with `Z i`
`ℱ (i + 1)`-measurable and `μ[Z i | ℱ i] =ᵐ[μ] 0`, `|Z i| ≤ c i` a.e.) have a sub-Gaussian MGF
with parameter `∑ i ∈ Finset.range n, c i ^ 2`. -/
theorem hasSubgaussianMGF_sum_of_martingale_diff [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Z : ℕ → Ω → ℝ} {c : ℕ → ℝ≥0} (n : ℕ)
    (h_meas : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (Z i))
    (h_cond : ∀ i < n, μ[Z i | ℱ i] =ᵐ[μ] 0)
    (h_bdd : ∀ i < n, ∀ᵐ ω ∂μ, |Z i ω| ≤ (c i : ℝ)) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ Finset.range n, Z i ω)
      (∑ i ∈ Finset.range n, c i ^ 2) μ := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h_meas_n : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (Z i) :=
      fun i hi ↦ h_meas i (Nat.lt_succ_of_lt hi)
    have h_cond_n : ∀ i < n, μ[Z i | ℱ i] =ᵐ[μ] 0 :=
      fun i hi ↦ h_cond i (Nat.lt_succ_of_lt hi)
    have h_bdd_n : ∀ i < n, ∀ᵐ ω ∂μ, |Z i ω| ≤ (c i : ℝ) :=
      fun i hi ↦ h_bdd i (Nat.lt_succ_of_lt hi)
    have ih' := ih h_meas_n h_cond_n h_bdd_n
    let S : Ω → ℝ := fun ω ↦ ∑ i ∈ Finset.range n, Z i ω
    have hS_meas : StronglyMeasurable[ℱ n] S := by
      refine Finset.stronglyMeasurable_fun_sum (Finset.range n) fun i hi ↦ ?_
      have hilt : i < n := Finset.mem_range.mp hi
      exact (h_meas_n i hilt).mono (ℱ.mono (Nat.succ_le_of_lt hilt))
    have hS_bdd : ∀ᵐ ω ∂μ, |S ω| ≤ ∑ i ∈ Finset.range n, (c i : ℝ) := by
      have h_all : ∀ᵐ ω ∂μ, ∀ i : {i // i < n}, |Z i.1 ω| ≤ (c i.1 : ℝ) :=
        ae_all_iff.mpr fun i ↦ h_bdd_n i.1 i.2
      filter_upwards [h_all] with ω hω
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i hi ↦ hω ⟨i, Finset.mem_range.mp hi⟩)
    have hZn_meas : StronglyMeasurable (Z n) :=
      (h_meas n (Nat.lt_succ_self n)).mono (ℱ.le (n + 1))
    have hZn_bdd := h_bdd n (Nat.lt_succ_self n)
    have h_int_exp : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * (S ω + Z n ω))) μ := by
      intro t
      refine Integrable.of_bound
        (Real.continuous_exp.comp_aestronglyMeasurable
          (((hS_meas.mono (ℱ.le n)).add hZn_meas).aestronglyMeasurable.const_mul t))
        (Real.exp (|t| * ((∑ i ∈ Finset.range n, (c i : ℝ)) + (c n : ℝ)))) ?_
      filter_upwards [hS_bdd, hZn_bdd] with ω hSω hZω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr ?_
      calc t * (S ω + Z n ω)
          ≤ |t * (S ω + Z n ω)| := le_abs_self _
        _ = |t| * |S ω + Z n ω| := abs_mul _ _
        _ ≤ |t| * (|S ω| + |Z n ω|) :=
            mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg t)
        _ ≤ |t| * ((∑ i ∈ Finset.range n, (c i : ℝ)) + (c n : ℝ)) :=
            mul_le_mul_of_nonneg_left (add_le_add hSω hZω) (abs_nonneg t)
    refine ⟨?_, ?_⟩
    · intro t
      simpa only [Finset.sum_range_succ] using h_int_exp t
    · intro t
      simp only [mgf, Finset.sum_range_succ]
      have hexpS_meas : StronglyMeasurable[ℱ n] (fun ω ↦ Real.exp (t * S ω)) :=
        Real.continuous_exp.comp_stronglyMeasurable (hS_meas.const_mul t)
      have hexpZ_int : Integrable (fun ω ↦ Real.exp (t * Z n ω)) μ := by
        refine Integrable.of_bound
          (Real.continuous_exp.comp_aestronglyMeasurable
            (hZn_meas.aestronglyMeasurable.const_mul t))
          (Real.exp (|t| * (c n : ℝ))) ?_
        filter_upwards [hZn_bdd] with ω hω
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        calc t * Z n ω ≤ |t * Z n ω| := le_abs_self _
          _ = |t| * |Z n ω| := abs_mul _ _
          _ ≤ |t| * (c n : ℝ) := mul_le_mul_of_nonneg_left hω (abs_nonneg t)
      have hprod_int : Integrable ((fun ω ↦ Real.exp (t * S ω)) *
          (fun ω ↦ Real.exp (t * Z n ω))) μ := by
        convert h_int_exp t using 1
        ext ω
        simp only [Pi.mul_apply, ← Real.exp_add, mul_add]
      have hpull := condExp_mul_of_stronglyMeasurable_left hexpS_meas hprod_int hexpZ_int
      have hstep := condExp_exp_mul_le_of_abs_le (ℱ.le n) hZn_meas.aestronglyMeasurable
        (h_cond n (Nat.lt_succ_self n)) hZn_bdd t
      have h_eq1 : ∫ ω, Real.exp (t * (S ω + Z n ω)) ∂μ =
          ∫ ω, ((fun ω' ↦ Real.exp (t * S ω')) * (fun ω' ↦ Real.exp (t * Z n ω'))) ω ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
        simp only [Pi.mul_apply, ← Real.exp_add, mul_add]
      rw [h_eq1, ← integral_condExp (ℱ.le n)]
      have h_le_int : ∫ ω, (μ[(fun ω' ↦ Real.exp (t * S ω')) *
            (fun ω' ↦ Real.exp (t * Z n ω')) | ℱ n]) ω ∂μ ≤
          ∫ ω, Real.exp (t * S ω) * Real.exp ((c n : ℝ) ^ 2 * t ^ 2 / 2) ∂μ := by
        refine integral_mono_ae integrable_condExp ?_ ?_
        · exact (ih'.integrable_exp_mul t).mul_const _
        · filter_upwards [hpull, hstep] with ω hω1 hω2
          rw [hω1]
          exact mul_le_mul_of_nonneg_left hω2 (Real.exp_pos _).le
      refine h_le_int.trans ?_
      rw [integral_mul_const]
      have h_ih_mgf := ih'.mgf_le t
      rw [mgf] at h_ih_mgf
      calc (∫ ω, Real.exp (t * S ω) ∂μ) * Real.exp ((c n : ℝ) ^ 2 * t ^ 2 / 2)
          ≤ Real.exp (↑(∑ i ∈ Finset.range n, c i ^ 2) * t ^ 2 / 2) *
              Real.exp ((c n : ℝ) ^ 2 * t ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right h_ih_mgf (Real.exp_pos _).le
        _ = Real.exp ((↑(∑ i ∈ Finset.range n, c i ^ 2) + (c n : ℝ) ^ 2) * t ^ 2 / 2) := by
            rw [← Real.exp_add]; congr 1; ring
        _ = Real.exp (↑(∑ i ∈ Finset.range n, c i ^ 2 + c n ^ 2) * t ^ 2 / 2) := by
            push_cast; rfl

/-- One-sided **Azuma–Hoeffding inequality** for bounded martingale-difference sequences on an
arbitrary measurable space. -/
theorem measure_sum_ge_le_of_martingale_diff [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Z : ℕ → Ω → ℝ} {c : ℕ → ℝ≥0} (n : ℕ)
    (h_meas : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (Z i))
    (h_cond : ∀ i < n, μ[Z i | ℱ i] =ᵐ[μ] 0)
    (h_bdd : ∀ i < n, ∀ᵐ ω ∂μ, |Z i ω| ≤ (c i : ℝ)) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ ∑ i ∈ Finset.range n, Z i ω} ≤
      Real.exp (-u ^ 2 / (2 * ∑ i ∈ Finset.range n, (c i : ℝ) ^ 2)) := by
  have hsub := hasSubgaussianMGF_sum_of_martingale_diff n h_meas h_cond h_bdd
  have h := hsub.measure_ge_le hu
  simpa using h

/-- Two-sided **Azuma–Hoeffding inequality** for bounded martingale-difference sequences on an
arbitrary measurable space. -/
theorem measure_abs_sum_ge_le_of_martingale_diff [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Z : ℕ → Ω → ℝ} {c : ℕ → ℝ≥0} (n : ℕ)
    (h_meas : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (Z i))
    (h_cond : ∀ i < n, μ[Z i | ℱ i] =ᵐ[μ] 0)
    (h_bdd : ∀ i < n, ∀ᵐ ω ∂μ, |Z i ω| ≤ (c i : ℝ)) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |∑ i ∈ Finset.range n, Z i ω|} ≤
      2 * Real.exp (-u ^ 2 / (2 * ∑ i ∈ Finset.range n, (c i : ℝ) ^ 2)) := by
  have hsub := hasSubgaussianMGF_sum_of_martingale_diff n h_meas h_cond h_bdd
  have hpos := hsub.measure_ge_le hu
  have hneg := hsub.neg.measure_ge_le hu
  have h_union : {ω | u ≤ |∑ i ∈ Finset.range n, Z i ω|} ⊆
      {ω | u ≤ ∑ i ∈ Finset.range n, Z i ω} ∪
      {ω | u ≤ -(∑ i ∈ Finset.range n, Z i ω)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h_le : μ.real {ω | u ≤ |∑ i ∈ Finset.range n, Z i ω|} ≤
      μ.real {ω | u ≤ ∑ i ∈ Finset.range n, Z i ω} +
      μ.real {ω | u ≤ -(∑ i ∈ Finset.range n, Z i ω)} :=
    (measureReal_mono h_union).trans (measureReal_union_le _ _)
  have hneg' : μ.real {ω | u ≤ -(∑ i ∈ Finset.range n, Z i ω)} ≤
      Real.exp (-u ^ 2 / (2 * ↑(∑ i ∈ Finset.range n, c i ^ 2))) := by
    simpa [Pi.neg_apply] using hneg
  have hpos' : μ.real {ω | u ≤ ∑ i ∈ Finset.range n, Z i ω} ≤
      Real.exp (-u ^ 2 / (2 * ↑(∑ i ∈ Finset.range n, c i ^ 2))) := by
    simpa using hpos
  have hsum := add_le_add hpos' hneg'
  push_cast at hsum
  linarith

/-- Two-sided empirical-average **Azuma–Hoeffding inequality** for uniformly bounded martingale
differences `|Z i| ≤ M` (`M > 0`, `n ≥ 1`):
`μ.real {ω | u ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω|} ≤ 2 * exp (-n * u ^ 2 / (2 * M ^ 2))`.
-/
theorem measure_abs_avg_ge_le_of_martingale_diff [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Z : ℕ → Ω → ℝ} {M : ℝ} (hM : 0 < M) {n : ℕ} (hn : 1 ≤ n)
    (h_meas : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (Z i))
    (h_cond : ∀ i < n, μ[Z i | ℱ i] =ᵐ[μ] 0)
    (h_bdd : ∀ i < n, ∀ᵐ ω ∂μ, |Z i ω| ≤ M) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω|} ≤
      2 * Real.exp (-(n : ℝ) * u ^ 2 / (2 * M ^ 2)) := by
  let c : ℕ → ℝ≥0 := fun _ ↦ ⟨M, hM.le⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  have h_eq : {ω | u ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Z i ω|} =
      {ω | (n : ℝ) * u ≤ |∑ i ∈ Finset.range n, Z i ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, abs_mul, abs_inv, abs_of_pos hn_pos]
    constructor <;> intro h
    · calc (n : ℝ) * u ≤ (n : ℝ) * ((n : ℝ)⁻¹ * |∑ i ∈ Finset.range n, Z i ω|) :=
            mul_le_mul_of_nonneg_left h hn_pos.le
        _ = |∑ i ∈ Finset.range n, Z i ω| := by field_simp [hn_pos.ne']
    · calc u = (n : ℝ)⁻¹ * ((n : ℝ) * u) := by field_simp [hn_pos.ne']
        _ ≤ (n : ℝ)⁻¹ * |∑ i ∈ Finset.range n, Z i ω| :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hn_pos.le)
  rw [h_eq]
  have h_bound := measure_abs_sum_ge_le_of_martingale_diff (c := c) n h_meas h_cond h_bdd
    (mul_nonneg hn_pos.le hu)
  refine h_bound.trans_eq ?_
  congr 2
  have hsum_c : ∑ i ∈ Finset.range n, (c i : ℝ) ^ 2 = (n : ℝ) * M ^ 2 := by
    simp only [c, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rfl
  rw [hsum_c]
  field_simp [hn_pos.ne', hM.ne']

end AzumaHoeffding

end CslibFrontier.Probability.Martingale
