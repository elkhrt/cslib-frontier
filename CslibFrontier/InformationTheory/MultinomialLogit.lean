/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multinomial Logit Choice Model, Log-Loss, and Kullback–Leibler Excess Risk

This module develops the finite-slate multinomial logit (MNL / softmax) choice model on `Fin K`,
its negative log-likelihood loss, and its exact Kullback–Leibler excess-risk identity, serving
computational learning theory, online RLHF/DPO alignment, and bandit preference feedback.

## Main definitions

* `CslibFrontier.InformationTheory.mnlProb`: multinomial logit (softmax) choice probability.
* `CslibFrontier.InformationTheory.mnlMeasure`: discrete probability measure on `Fin K` induced by
  `mnlProb`.
* `CslibFrontier.InformationTheory.mnlLoss`: multinomial negative log-likelihood
  `log (∑ j, exp (v j)) - v y`.

## Main results

* `CslibFrontier.InformationTheory.mnlLoss_nonneg`,
  `CslibFrontier.InformationTheory.mnlLoss_le_of_osc_le`: uniform range bounds
  `0 ≤ mnlLoss v y ≤ log K + 2 B`.
* `CslibFrontier.InformationTheory.abs_mnlLoss_sub_le`,
  `CslibFrontier.InformationTheory.abs_mnlProb_sub_le`: `2`-Lipschitzness in supremum norm.
* `CslibFrontier.InformationTheory.mnlExcessLoss_eq_toReal_klDiv`,
  `CslibFrontier.InformationTheory.mnlExcessLoss_eq_zero_iff`: exact KL excess-risk identity and
  identifiability up to an additive constant.
* `CslibFrontier.InformationTheory.neg_log_sigmoid_eq_mnlLoss_two`: pairwise (`K = 2`) logistic
  Bradley–Terry / DPO loss equivalence.
-/

public section

open MeasureTheory Real Finset
open scoped ENNReal

namespace CslibFrontier.InformationTheory

section MultinomialLogit

variable {K : ℕ}

/-- Multinomial logit (softmax) choice probability of index `k : Fin K` under score vector
`v : Fin K → ℝ`. -/
noncomputable def mnlProb (v : Fin K → ℝ) (k : Fin K) : ℝ :=
  Real.exp (v k) / ∑ j : Fin K, Real.exp (v j)

/-- Discrete measure on `Fin K` with mass `mnlProb v k` at each `k : Fin K`. -/
noncomputable def mnlMeasure (v : Fin K → ℝ) : Measure (Fin K) :=
  ∑ k : Fin K, ENNReal.ofReal (mnlProb v k) • Measure.dirac k

/-- Multinomial negative log-likelihood (log-loss) `log (∑ j, exp (v j)) - v y`. -/
noncomputable def mnlLoss (v : Fin K → ℝ) (y : Fin K) : ℝ :=
  Real.log (∑ j : Fin K, Real.exp (v j)) - v y

private lemma sum_exp_pos [NeZero K] (v : Fin K → ℝ) : 0 < ∑ j : Fin K, Real.exp (v j) :=
  Finset.sum_pos (fun j _ ↦ Real.exp_pos (v j)) Finset.univ_nonempty

/-- Every MNL choice probability is strictly positive when `K > 0`. -/
theorem mnlProb_pos [NeZero K] (v : Fin K → ℝ) (k : Fin K) : 0 < mnlProb v k :=
  div_pos (Real.exp_pos (v k)) (sum_exp_pos v)

/-- Every MNL choice probability is at most `1`. -/
theorem mnlProb_le_one (v : Fin K → ℝ) (k : Fin K) : mnlProb v k ≤ 1 := by
  by_cases hK : K = 0
  · subst hK; exact Fin.elim0 k
  · have : NeZero K := ⟨hK⟩
    rw [mnlProb, div_le_one (sum_exp_pos v)]
    exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos (v j)).le) (Finset.mem_univ k)

/-- The MNL choice probabilities sum to `1` when `K > 0`. -/
@[simp]
theorem sum_mnlProb [NeZero K] (v : Fin K → ℝ) : ∑ k : Fin K, mnlProb v k = 1 := by
  simp only [mnlProb, ← Finset.sum_div]
  exact div_self (sum_exp_pos v).ne'

/-- Subtracting an index-independent constant leaves MNL probabilities unchanged. -/
@[simp]
theorem mnlProb_sub_const (v : Fin K → ℝ) (c : ℝ) (k : Fin K) :
    mnlProb (fun j ↦ v j - c) k = mnlProb v k := by
  by_cases hK : K = 0
  · subst hK; exact Fin.elim0 k
  · have : NeZero K := ⟨hK⟩
    simp only [mnlProb, Real.exp_sub, ← Finset.sum_div]
    have hpos : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
    rw [div_div_div_cancel_right₀ hpos]

/-- Subtracting an index-independent constant leaves the MNL log-loss unchanged. -/
@[simp]
theorem mnlLoss_sub_const [NeZero K] (v : Fin K → ℝ) (c : ℝ) (y : Fin K) :
    mnlLoss (fun j ↦ v j - c) y = mnlLoss v y := by
  simp only [mnlLoss, Real.exp_sub, ← Finset.sum_div,
    Real.log_div (sum_exp_pos v).ne' (Real.exp_pos c).ne', Real.log_exp]
  ring

/-- Exact negative-log-probability identity `mnlLoss v y = -log (mnlProb v y)`. -/
theorem mnlLoss_eq_neg_log_mnlProb [NeZero K] (v : Fin K → ℝ) (y : Fin K) :
    mnlLoss v y = -Real.log (mnlProb v y) := by
  rw [mnlProb, Real.log_div (Real.exp_pos (v y)).ne' (sum_exp_pos v).ne', Real.log_exp, mnlLoss]
  ring

/-- Exact exponential identity `exp (-mnlLoss v y) = mnlProb v y`. -/
theorem exp_neg_mnlLoss [NeZero K] (v : Fin K → ℝ) (y : Fin K) :
    Real.exp (-mnlLoss v y) = mnlProb v y := by
  rw [mnlLoss_eq_neg_log_mnlProb, neg_neg, Real.exp_log (mnlProb_pos v y)]

/-- Nonnegativity of the MNL negative log-likelihood. -/
theorem mnlLoss_nonneg (v : Fin K → ℝ) (y : Fin K) : 0 ≤ mnlLoss v y := by
  by_cases hK : K = 0
  · subst hK; exact Fin.elim0 y
  · have : NeZero K := ⟨hK⟩
    rw [mnlLoss_eq_neg_log_mnlProb, neg_nonneg]
    exact Real.log_nonpos (mnlProb_pos v y).le (mnlProb_le_one v y)

/-- Upper bound `mnlLoss v y ≤ log K + 2 B` whenever `v` has pairwise oscillation at most `2 B`. -/
theorem mnlLoss_le_of_osc_le [NeZero K] {v : Fin K → ℝ} {B : ℝ}
    (hosc : ∀ j k : Fin K, v j - v k ≤ 2 * B) (y : Fin K) :
    mnlLoss v y ≤ Real.log K + 2 * B := by
  have hsum : ∑ j : Fin K, Real.exp (v j) ≤ (K : ℝ) * Real.exp (v y + 2 * B) := by
    calc ∑ j : Fin K, Real.exp (v j)
        ≤ ∑ _j : Fin K, Real.exp (v y + 2 * B) :=
          Finset.sum_le_sum fun j _ ↦ Real.exp_le_exp.mpr (by linarith [hosc j y])
      _ = (K : ℝ) * Real.exp (v y + 2 * B) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr (NeZero.pos K)
  have hlog := Real.log_le_log (sum_exp_pos v) hsum
  rw [Real.log_mul hKpos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [mnlLoss]
  linarith

private lemma log_sum_exp_sub_le [NeZero K] (v v' : Fin K → ℝ) :
    Real.log (∑ j : Fin K, Real.exp (v j)) - Real.log (∑ j : Fin K, Real.exp (v' j)) ≤
      ‖v - v'‖ := by
  have hsum : ∑ j : Fin K, Real.exp (v j) ≤
      Real.exp ‖v - v'‖ * ∑ j : Fin K, Real.exp (v' j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hj : |v j - v' j| ≤ ‖v - v'‖ := by
      have := norm_le_pi_norm (v - v') j
      simpa [Real.norm_eq_abs] using this
    linarith [(abs_le.mp hj).2]
  have hlog := Real.log_le_log (sum_exp_pos v) hsum
  rw [Real.log_mul (Real.exp_pos _).ne' (sum_exp_pos v').ne', Real.log_exp] at hlog
  linarith

/-- `1`-Lipschitzness of the log-sum-exp functional in the supremum norm `‖v - v'‖`. -/
theorem abs_log_sum_exp_sub_le [NeZero K] (v v' : Fin K → ℝ) :
    |Real.log (∑ j : Fin K, Real.exp (v j)) - Real.log (∑ j : Fin K, Real.exp (v' j))| ≤
      ‖v - v'‖ := by
  refine abs_le.mpr ⟨?_, log_sum_exp_sub_le v v'⟩
  have h := log_sum_exp_sub_le v' v
  rw [norm_sub_rev] at h
  linarith

/-- `2`-Lipschitzness of the MNL negative log-likelihood in the supremum norm `‖v - v'‖`. -/
theorem abs_mnlLoss_sub_le [NeZero K] (v v' : Fin K → ℝ) (y : Fin K) :
    |mnlLoss v y - mnlLoss v' y| ≤ 2 * ‖v - v'‖ := by
  have hsplit : mnlLoss v y - mnlLoss v' y =
      (Real.log (∑ j : Fin K, Real.exp (v j)) - Real.log (∑ j : Fin K, Real.exp (v' j))) -
      (v y - v' y) := by
    simp only [mnlLoss]; ring
  rw [hsplit]
  have h1 := abs_log_sum_exp_sub_le v v'
  have h2 : |v y - v' y| ≤ ‖v - v'‖ := by
    have := norm_le_pi_norm (v - v') y
    simpa [Real.norm_eq_abs] using this
  calc |(Real.log (∑ j : Fin K, Real.exp (v j)) - Real.log (∑ j : Fin K, Real.exp (v' j))) -
          (v y - v' y)|
      ≤ |Real.log (∑ j : Fin K, Real.exp (v j)) - Real.log (∑ j : Fin K, Real.exp (v' j))| +
        |v y - v' y| := abs_sub _ _
    _ ≤ ‖v - v'‖ + ‖v - v'‖ := add_le_add h1 h2
    _ = 2 * ‖v - v'‖ := by ring

/-- `2`-Lipschitzness of MNL choice probabilities `v ↦ mnlProb v k` in the supremum norm. -/
theorem abs_mnlProb_sub_le [NeZero K] (v v' : Fin K → ℝ) (k : Fin K) :
    |mnlProb v k - mnlProb v' k| ≤ 2 * ‖v - v'‖ := by
  rw [← exp_neg_mnlLoss v k, ← exp_neg_mnlLoss v' k]
  have h1 : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ b →
      Real.exp (-a) - Real.exp (-b) ≤ b - a := by
    intro a b ha _ hab
    have hmul : Real.exp (-a) - Real.exp (-b) =
        Real.exp (-b) * (Real.exp (b - a) - 1) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 2; ring
    have h_exp_sub : Real.exp (b - a) - 1 ≤ (b - a) * Real.exp (b - a) := by
      have := Real.add_one_le_exp (-(b - a))
      have hpos : 0 < Real.exp (b - a) := Real.exp_pos _
      have hmul' := mul_le_mul_of_nonneg_right this hpos.le
      rw [add_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul'
      linarith
    have hstep : Real.exp (-b) * (Real.exp (b - a) - 1) ≤
        Real.exp (-b) * ((b - a) * Real.exp (b - a)) :=
      mul_le_mul_of_nonneg_left h_exp_sub (Real.exp_pos _).le
    have hcancel : Real.exp (-b) * ((b - a) * Real.exp (b - a)) =
        (b - a) * Real.exp (-a) := by
      calc Real.exp (-b) * ((b - a) * Real.exp (b - a))
          = (b - a) * (Real.exp (-b) * Real.exp (b - a)) := by ring
        _ = (b - a) * Real.exp (-b + (b - a)) := by rw [← Real.exp_add]
        _ = (b - a) * Real.exp (-a) := by congr 2; ring
    have hle1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc Real.exp (-a) - Real.exp (-b)
        ≤ (b - a) * Real.exp (-a) := by rwa [hmul, ← hcancel]
      _ ≤ (b - a) * 1 := mul_le_mul_of_nonneg_left hle1 (sub_nonneg.mpr hab)
      _ = b - a := mul_one _
  have habs : |Real.exp (-mnlLoss v k) - Real.exp (-mnlLoss v' k)| ≤
      |mnlLoss v k - mnlLoss v' k| := by
    rcases le_total (mnlLoss v k) (mnlLoss v' k) with h | h
    · have hge : Real.exp (-mnlLoss v' k) ≤ Real.exp (-mnlLoss v k) :=
        Real.exp_le_exp.mpr (neg_le_neg h)
      rw [abs_of_nonneg (sub_nonneg.mpr hge), abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
      exact h1 _ _ (mnlLoss_nonneg v k) (mnlLoss_nonneg v' k) h
    · have hge : Real.exp (-mnlLoss v k) ≤ Real.exp (-mnlLoss v' k) :=
        Real.exp_le_exp.mpr (neg_le_neg h)
      rw [abs_of_nonpos (sub_nonpos.mpr hge), neg_sub, abs_of_nonneg (sub_nonneg.mpr h)]
      exact h1 _ _ (mnlLoss_nonneg v' k) (mnlLoss_nonneg v k) h
  exact habs.trans (abs_mnlLoss_sub_le v v' k)

private theorem finset_sum_measure_apply {ι : Type*} (s : Finset ι) (μ : ι → Measure (Fin K))
    (t : Set (Fin K)) : (∑ i ∈ s, μ i) t = ∑ i ∈ s, μ i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- `mnlMeasure v` is a probability measure on `Fin K` whenever `K > 0`. -/
instance instIsProbabilityMeasureMnlMeasure [NeZero K] (v : Fin K → ℝ) :
    IsProbabilityMeasure (mnlMeasure v) where
  measure_univ := by
    have hsum : (∑ k : Fin K, ENNReal.ofReal (mnlProb v k) • Measure.dirac k) Set.univ =
        ∑ k : Fin K, ENNReal.ofReal (mnlProb v k) * Measure.dirac k Set.univ := by
      rw [finset_sum_measure_apply]
      simp
    rw [mnlMeasure, hsum]
    simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ (mnlProb_pos v k).le), sum_mnlProb,
      ENNReal.ofReal_one]

@[simp]
theorem mnlMeasure_singleton (v : Fin K → ℝ) (k : Fin K) :
    mnlMeasure v {k} = ENNReal.ofReal (mnlProb v k) := by
  classical
  have hsum : (∑ j : Fin K, ENNReal.ofReal (mnlProb v j) • Measure.dirac j) {k} =
      ∑ j : Fin K, ENNReal.ofReal (mnlProb v j) * Measure.dirac j {k} := by
    rw [finset_sum_measure_apply]
    simp
  rw [mnlMeasure, hsum, Finset.sum_eq_single k]
  · simp [Measure.dirac_apply' _ (MeasurableSet.singleton k)]
  · intro j _ hjk
    simp [Measure.dirac_apply' _ (MeasurableSet.singleton k), hjk.symm]
  · intro hk; exact absurd (Finset.mem_univ k) hk

/-- Evaluation of `mnlMeasure v` on any set `s : Set (Fin K)`. -/
theorem mnlMeasure_apply (v : Fin K → ℝ) (s : Set (Fin K)) :
    mnlMeasure v s = ∑ k : Fin K, s.indicator (fun j ↦ ENNReal.ofReal (mnlProb v j)) k := by
  have hsum : (∑ j : Fin K, ENNReal.ofReal (mnlProb v j) • Measure.dirac j) s =
      ∑ j : Fin K, ENNReal.ofReal (mnlProb v j) * Measure.dirac j s := by
    rw [finset_sum_measure_apply]
    simp
  rw [mnlMeasure, hsum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete (s := s))]
  by_cases hks : k ∈ s <;> simp [hks]

/-- Continuity of `v ↦ mnlProb v k`. -/
@[fun_prop]
theorem continuous_mnlProb (k : Fin K) : Continuous (fun v : Fin K → ℝ ↦ mnlProb v k) := by
  by_cases hK : K = 0
  · subst hK; exact Fin.elim0 k
  · have : NeZero K := ⟨hK⟩
    rw [Metric.continuous_iff]
    intro v ε hε
    refine ⟨ε / 3, by positivity, fun v' hv' ↦ ?_⟩
    rw [Real.dist_eq]
    rw [dist_eq_norm] at hv'
    exact (abs_mnlProb_sub_le v' v k).trans_lt (by linarith)

/-- Continuity of `v ↦ mnlLoss v y`. -/
@[fun_prop]
theorem continuous_mnlLoss (y : Fin K) : Continuous (fun v : Fin K → ℝ ↦ mnlLoss v y) := by
  by_cases hK : K = 0
  · subst hK; exact Fin.elim0 y
  · have : NeZero K := ⟨hK⟩
    rw [Metric.continuous_iff]
    intro v ε hε
    refine ⟨ε / 3, by positivity, fun v' hv' ↦ ?_⟩
    rw [Real.dist_eq]
    rw [dist_eq_norm] at hv'
    exact (abs_mnlLoss_sub_le v' v y).trans_lt (by linarith)

/-- For any `v, v' : Fin K → ℝ`, `mnlMeasure v` is absolutely continuous with respect to
`mnlMeasure v'`. -/
theorem mnlMeasure_absolutelyContinuous [NeZero K] (v v' : Fin K → ℝ) :
    mnlMeasure v ≪ mnlMeasure v' := by
  refine Measure.AbsolutelyContinuous.mk fun s _ hs ↦ ?_
  have hs_empty : s = ∅ := by
    by_contra hne
    obtain ⟨k, hk⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hpos : (0 : ℝ≥0∞) < mnlMeasure v' {k} := by
      rw [mnlMeasure_singleton, ENNReal.ofReal_pos]
      exact mnlProb_pos v' k
    have hle : mnlMeasure v' {k} ≤ mnlMeasure v' s :=
      measure_mono (Set.singleton_subset_iff.mpr hk)
    rw [hs] at hle
    exact (lt_of_lt_of_le hpos hle).ne' rfl
  simp [hs_empty]

/-- Exact Radon–Nikodym derivative of `mnlMeasure vStar` with respect to `mnlMeasure v`. -/
theorem rnDeriv_mnlMeasure [NeZero K] (vStar v : Fin K → ℝ) (k : Fin K) :
    (mnlMeasure vStar).rnDeriv (mnlMeasure v) k =
      ENNReal.ofReal (mnlProb vStar k / mnlProb v k) := by
  have h_eq : mnlMeasure vStar =
      (mnlMeasure v).withDensity (fun j ↦ ENNReal.ofReal (mnlProb vStar j / mnlProb v j)) := by
    refine Measure.ext_of_singleton fun j ↦ ?_
    rw [withDensity_apply _ (MeasurableSet.singleton j), lintegral_singleton,
      mnlMeasure_singleton, mnlMeasure_singleton,
      ← ENNReal.ofReal_mul (div_nonneg (mnlProb_pos vStar j).le (mnlProb_pos v j).le),
      div_mul_cancel₀ _ (mnlProb_pos v j).ne']
  have hrn : ((mnlMeasure v).withDensity
      (fun j ↦ ENNReal.ofReal (mnlProb vStar j / mnlProb v j))).rnDeriv (mnlMeasure v) =ᵐ[
      mnlMeasure v] fun j ↦ ENNReal.ofReal (mnlProb vStar j / mnlProb v j) :=
    Measure.rnDeriv_withDensity (mnlMeasure v) (Measurable.of_discrete)
  have hsingle : ∀ j, mnlMeasure v {j} ≠ 0 := fun j ↦ by
    rw [mnlMeasure_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact mnlProb_pos v j
  rw [← h_eq] at hrn
  have hzero := ae_iff.mp hrn
  by_contra hne
  have hpos : (0 : ℝ≥0∞) < mnlMeasure v {k} := pos_iff_ne_zero.mpr (hsingle k)
  have hle : mnlMeasure v {k} ≤ mnlMeasure v {j | ¬(mnlMeasure vStar).rnDeriv (mnlMeasure v) j =
      ENNReal.ofReal (mnlProb vStar j / mnlProb v j)} :=
    measure_mono (Set.singleton_subset_iff.mpr hne)
  rw [hzero] at hle
  exact (lt_of_lt_of_le hpos hle).ne' rfl

/-- One-step expected excess MNL log-loss equals the Kullback–Leibler divergence
`InformationTheory.klDiv (mnlMeasure vStar) (mnlMeasure v)`. -/
theorem mnlExcessLoss_eq_toReal_klDiv [NeZero K] (vStar v : Fin K → ℝ) :
    ∑ k : Fin K, mnlProb vStar k * (mnlLoss v k - mnlLoss vStar k) =
      (InformationTheory.klDiv (mnlMeasure vStar) (mnlMeasure v)).toReal := by
  have hac := mnlMeasure_absolutelyContinuous vStar v
  have h_eq : mnlMeasure vStar Set.univ = mnlMeasure v Set.univ := by simp
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac h_eq]
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Measure.real, mnlMeasure_singleton, ENNReal.toReal_ofReal (mnlProb_pos vStar k).le,
    MeasureTheory.llr_def]
  dsimp only
  rw [rnDeriv_mnlMeasure,
    ENNReal.toReal_ofReal (div_nonneg (mnlProb_pos vStar k).le (mnlProb_pos v k).le),
    Real.log_div (mnlProb_pos vStar k).ne' (mnlProb_pos v k).ne',
    mnlLoss_eq_neg_log_mnlProb, mnlLoss_eq_neg_log_mnlProb, smul_eq_mul]
  ring

/-- In `ℝ≥0∞`, the KL divergence of two MNL choice models equals `ENNReal.ofReal` of the one-step
expected excess log-loss. -/
theorem klDiv_mnlMeasure_eq_ofReal [NeZero K] (vStar v : Fin K → ℝ) :
    InformationTheory.klDiv (mnlMeasure vStar) (mnlMeasure v) =
      ENNReal.ofReal (∑ k : Fin K, mnlProb vStar k * (mnlLoss v k - mnlLoss vStar k)) := by
  have hac := mnlMeasure_absolutelyContinuous vStar v
  have hne : InformationTheory.klDiv (mnlMeasure vStar) (mnlMeasure v) ≠ ∞ :=
    InformationTheory.klDiv_ne_top hac Integrable.of_finite
  rw [mnlExcessLoss_eq_toReal_klDiv, ENNReal.ofReal_toReal hne]

/-- Expected excess MNL log-loss is nonnegative. -/
theorem mnlExcessLoss_nonneg [NeZero K] (vStar v : Fin K → ℝ) :
    0 ≤ ∑ k : Fin K, mnlProb vStar k * (mnlLoss v k - mnlLoss vStar k) := by
  rw [mnlExcessLoss_eq_toReal_klDiv]
  exact ENNReal.toReal_nonneg

/-- Two MNL choice measures coincide iff their score vectors differ by an index-independent
constant. -/
theorem mnlMeasure_eq_iff [NeZero K] (vStar v : Fin K → ℝ) :
    mnlMeasure vStar = mnlMeasure v ↔ ∀ j k : Fin K, vStar j - vStar k = v j - v k := by
  constructor
  · intro h j k
    have hprob : ∀ i : Fin K, mnlProb vStar i = mnlProb v i := fun i ↦ by
      have hi : mnlMeasure vStar {i} = mnlMeasure v {i} := congrArg (fun μ ↦ μ {i}) h
      rw [mnlMeasure_singleton, mnlMeasure_singleton] at hi
      exact (ENNReal.ofReal_eq_ofReal_iff (mnlProb_pos vStar i).le (mnlProb_pos v i).le).mp hi
    have hlogj := congrArg Real.log (hprob j)
    have hlogk := congrArg Real.log (hprob k)
    rw [mnlProb, mnlProb, Real.log_div (Real.exp_pos _).ne' (sum_exp_pos _).ne',
      Real.log_div (Real.exp_pos _).ne' (sum_exp_pos _).ne',
      Real.log_exp, Real.log_exp] at hlogj hlogk
    linarith
  · intro h
    refine Measure.ext_of_singleton fun k ↦ ?_
    rw [mnlMeasure_singleton, mnlMeasure_singleton]
    congr 1
    have hdiff : ∀ j : Fin K, vStar j = v j + (vStar k - v k) := fun j ↦ by linarith [h j k]
    have hsub : (fun j : Fin K ↦ vStar j - (vStar k - v k)) = v := by
      funext j; linarith [hdiff j]
    rw [← mnlProb_sub_const vStar (vStar k - v k) k, hsub]

/-- Expected excess MNL log-loss vanishes iff the score vectors `vStar` and `v` differ by an
index-independent additive constant. -/
theorem mnlExcessLoss_eq_zero_iff [NeZero K] (vStar v : Fin K → ℝ) :
    ∑ k : Fin K, mnlProb vStar k * (mnlLoss v k - mnlLoss vStar k) = 0 ↔
      ∀ j k : Fin K, vStar j - vStar k = v j - v k := by
  rw [← mnlMeasure_eq_iff, ← InformationTheory.klDiv_eq_zero_iff, klDiv_mnlMeasure_eq_ofReal,
    ENNReal.ofReal_eq_zero]
  exact ⟨fun h ↦ le_of_eq h, fun h ↦ le_antisymm h (mnlExcessLoss_nonneg vStar v)⟩

/-- Pairwise (`K = 2`) equivalence between logistic Bradley–Terry / DPO loss
`-log (1 + exp (-(v y - v (1 - y))))⁻¹` and `mnlLoss v y`. -/
theorem neg_log_sigmoid_eq_mnlLoss_two (v : Fin 2 → ℝ) (y : Fin 2) :
    -Real.log (1 + Real.exp (-(v y - v (1 - y))))⁻¹ = mnlLoss v y := by
  rw [Real.log_inv, neg_neg, mnlLoss]
  have hsum : ∑ j : Fin 2, Real.exp (v j) = Real.exp (v y) + Real.exp (v (1 - y)) := by
    fin_cases y
    · simp [Fin.sum_univ_two]
    · simp [Fin.sum_univ_two, add_comm]
  rw [hsum]
  have hpos : 0 < Real.exp (v y) := Real.exp_pos _
  have hfac : Real.exp (v y) + Real.exp (v (1 - y)) =
      Real.exp (v y) * (1 + Real.exp (-(v y - v (1 - y)))) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    congr 2; ring
  rw [hfac, Real.log_mul hpos.ne' (by positivity), Real.log_exp]
  ring

end MultinomialLogit

end CslibFrontier.InformationTheory
