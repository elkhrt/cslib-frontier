/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Probability.PMF
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Discrete KL Divergence, Pinsker, Bretagnolle--Huber, and Hypergeometric Query Trees

This module proves discrete information-theoretic divergence inequalities on finite `PMF`s under
standard Lean axioms: the chi-squared upper bound on binary KL divergence, data processing, the
chain rule along monadic binds, tensorization on i.i.d. product samples, Pinsker's inequality, the
Bretagnolle--Huber inequality, and an adaptive decision-tree KL / Pinsker bound for distinguishing
uniform Boolean slices of prescribed Hamming weights.

## Main definitions

* `CslibFrontier.Probability.binaryKL`: binary Kullback--Leibler divergence
  `p log(p / q) + (1 - p) log((1 - p) / (1 - q))`.
* `CslibFrontier.Probability.pmfKL`: discrete Kullback--Leibler divergence on finite `PMF`s.
* `CslibFrontier.Probability.pmfTV`: total variation distance `(1 / 2) ∑ a, |μ a - ν a|` on finite
  `PMF`s.
* `CslibFrontier.Probability.iidSamples`: `s`-fold independent product `PMF` on `Fin s → α`.
* `CslibFrontier.Probability.QueryTree`: finite-depth adaptive oracle decision tree.
* `CslibFrontier.Probability.sliceFinset` and `CslibFrontier.Probability.uniformSlicePMF`: uniform
  distribution on Boolean strings `Fin m → Bool` of Hamming weight `k`.

## Main results

* `CslibFrontier.Probability.binaryKL_le_sq_div`: chi-squared upper bound
  `binaryKL p q ≤ (p - q) ^ 2 / (q * (1 - q))`.
* `CslibFrontier.Probability.pmfKL_map_le`, `CslibFrontier.Probability.pmfKL_bind_le`,
  `CslibFrontier.Probability.pmfKL_iidSamples_le`: data processing, chain rule, and i.i.d.
  tensorization
  for discrete KL divergence.
* `CslibFrontier.Probability.two_mul_pmfTV_sq_le_pmfKL` and
  `CslibFrontier.Probability.postprocess_iidSamples_pinsker`: Pinsker's inequality and its i.i.d.
  post-processing corollary.
* `CslibFrontier.Probability.bretagnolle_huber_pmf` and
  `CslibFrontier.Probability.postprocess_iidSamples_bretagnolle_huber`: Bretagnolle--Huber
  inequality
  `pmfTV μ ν ^ 2 ≤ 1 - exp (-pmfKL μ ν)` and its i.i.d. post-processing corollary.
* `CslibFrontier.Probability.queryTree_uniformSlice_kl_le` and
  `CslibFrontier.Probability.queryTree_uniformSlice_pinsker`: adaptive query-tree KL and Pinsker
  bounds
  for distinguishing uniform Boolean slices of different Hamming weights.

## Tags

Kullback-Leibler divergence, Pinsker inequality, Bretagnolle-Huber inequality, data processing,
query complexity, decision trees, hypergeometric distribution
-/

public section

namespace CslibFrontier.Probability

open Finset
open scoped ENNReal

section Helpers

variable {α β : Type*}

private lemma sum_toReal_eq_one [Fintype α] (μ : PMF α) :
    ∑ a : α, (μ a).toReal = 1 := by
  have hne : ∀ a ∈ (univ : Finset α), μ a ≠ ⊤ := fun a _ ↦ μ.apply_ne_top a
  rw [← ENNReal.toReal_sum hne, ← tsum_fintype (L := .unconditional _), μ.tsum_coe,
    ENNReal.toReal_one]

private lemma outerMeasure_toReal_eq_sum [Fintype α] (μ : PMF α) (S : Set α)
    [DecidablePred (· ∈ S)] :
    (μ.toOuterMeasure S).toReal =
      ∑ a : α, (μ a).toReal * if a ∈ S then (1 : ℝ) else 0 := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  have hne : ∀ a ∈ (univ : Finset α), Set.indicator S μ a ≠ ⊤ := by
    intro a _; by_cases ha : a ∈ S <;> simp [ha, μ.apply_ne_top a]
  rw [ENNReal.toReal_sum hne]
  exact sum_congr rfl fun a _ ↦ by by_cases ha : a ∈ S <;> simp [ha]

private lemma outerMeasure_ne_top (μ : PMF α) (S : Set α) :
    μ.toOuterMeasure S ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  calc
    μ.toOuterMeasure S ≤ μ.toOuterMeasure Set.univ := μ.toOuterMeasure.mono (Set.subset_univ S)
    _ = 1 := by simp [PMF.toOuterMeasure_apply, μ.tsum_coe]

private lemma bind_apply_toReal [Fintype α] (μ : PMF α) (κ : α → PMF β) (b : β) :
    ((μ.bind κ) b).toReal = ∑ a : α, (μ a).toReal * (κ a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype]
  have hne : ∀ a ∈ (univ : Finset α), μ a * κ a b ≠ ⊤ := fun a _ ↦
    ENNReal.mul_ne_top (μ.apply_ne_top a) ((κ a).apply_ne_top b)
  rw [ENNReal.toReal_sum hne]
  exact sum_congr rfl fun _ _ ↦ ENNReal.toReal_mul

private lemma map_apply_toReal [Fintype α] (μ : PMF α) (f : α → β) (b : β)
    [DecidablePred (fun a ↦ f a = b)] :
    ((μ.map f) b).toReal = ∑ a ∈ univ.filter (fun a ↦ f a = b), (μ a).toReal := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  have hne : ∀ a ∈ (univ : Finset α), (if b = f a then μ a else 0) ≠ ⊤ := by
    intro a _; split_ifs <;> simp [μ.apply_ne_top a]
  rw [ENNReal.toReal_sum hne, sum_filter]
  refine sum_congr rfl fun a _ ↦ ?_
  by_cases h : f a = b
  · simp [h]
  · have h' : b ≠ f a := fun h'' ↦ h h''.symm
    simp [h, h']

private lemma mul_log_div_ge_sub {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) :
    u - v ≤ u * Real.log (u / v) := by
  rcases eq_or_lt_of_le hu with rfl | hu_pos
  · simp [hv.le]
  · have hmul : u * Real.log (v / u) ≤ u * (v / u - 1) :=
      mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hv hu_pos)) hu_pos.le
    have hinv : Real.log (v / u) = -Real.log (u / v) := by rw [← Real.log_inv, inv_div]
    have hrhs : u * (v / u - 1) = v - u := by field_simp
    rw [hinv, hrhs] at hmul
    linarith

end Helpers

/-! ### Discrete KL divergence, Pinsker's inequality, and Bretagnolle--Huber inequality -/

/-- Binary Kullback--Leibler divergence `p log(p / q) + (1 - p) log((1 - p) / (1 - q))` in nats. -/
noncomputable def binaryKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Discrete Kullback--Leibler divergence `∑ a, μ(a) log(μ(a) / ν(a))` in nats. -/
noncomputable def pmfKL {α : Type*} [Fintype α] (μ ν : PMF α) : ℝ :=
  ∑ a : α, (μ a).toReal * Real.log ((μ a).toReal / (ν a).toReal)

/-- Discrete total variation distance `(1 / 2) ∑ a, |μ(a) - ν(a)|`. -/
noncomputable def pmfTV {α : Type*} [Fintype α] (μ ν : PMF α) : ℝ :=
  (∑ a : α, |(μ a).toReal - (ν a).toReal|) / 2

/-- Nonnegativity of binary KL divergence for `p ∈ [0, 1]` and `q ∈ (0, 1)`. -/
theorem binaryKL_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ binaryKL p q := by
  unfold binaryKL
  linarith [mul_log_div_ge_sub hp0 hq0,
    mul_log_div_ge_sub (by linarith : 0 ≤ 1 - p) (by linarith : 0 < 1 - q)]

/-- **Chi-squared upper bound on binary KL divergence**: for `p ∈ [0, 1]` and `q ∈ (0, 1)`,
`binaryKL p q ≤ (p - q) ^ 2 / (q * (1 - q))`. -/
theorem binaryKL_le_sq_div {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    binaryKL p q ≤ (p - q) ^ 2 / (q * (1 - q)) := by
  unfold binaryKL
  have ht1 : p * Real.log (p / q) ≤ p * (p / q - 1) := by
    rcases eq_or_lt_of_le hp0 with rfl | hp_pos
    · simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hp_pos hq0)) hp_pos.le
  have ht2 : (1 - p) * Real.log ((1 - p) / (1 - q)) ≤ (1 - p) * ((1 - p) / (1 - q) - 1) := by
    rcases eq_or_lt_of_le (sub_nonneg.mpr hp1) with h0 | hp_lt
    · rw [← h0]; simp
    · exact mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hp_lt (by linarith))) hp_lt.le
  have halg : p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) =
      (p - q) ^ 2 / (q * (1 - q)) := by
    have hqne : q ≠ 0 := hq0.ne'
    have hq1ne : 1 - q ≠ 0 := by linarith
    field_simp
    ring
  linarith

/-- Discrete KL divergence on `PMF Bool` coincides with `binaryKL`. -/
theorem pmfKL_bool_eq_binaryKL (p q : PMF Bool) :
    pmfKL p q = binaryKL (p true).toReal (q true).toReal := by
  unfold pmfKL binaryKL
  have hp : (p false).toReal = 1 - (p true).toReal := by
    have h := sum_toReal_eq_one p; simp only [Fintype.sum_bool] at h; linarith
  have hq : (q false).toReal = 1 - (q true).toReal := by
    have h := sum_toReal_eq_one q; simp only [Fintype.sum_bool] at h; linarith
  simp only [Fintype.sum_bool, hp, hq]

/-- Gibbs' inequality: `0 ≤ pmfKL μ ν` whenever `μ.support ⊆ ν.support`. -/
theorem pmfKL_nonneg {α : Type*} [Fintype α] {μ ν : PMF α} (hsupp : μ.support ⊆ ν.support) :
    0 ≤ pmfKL μ ν := by
  unfold pmfKL
  have hbound : ∑ a : α, ((μ a).toReal - (ν a).toReal) ≤
      ∑ a : α, (μ a).toReal * Real.log ((μ a).toReal / (ν a).toReal) := by
    refine sum_le_sum fun a _ ↦ ?_
    by_cases ha : a ∈ μ.support
    · exact mul_log_div_ge_sub ENNReal.toReal_nonneg
        (ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (hsupp ha)) (ν.apply_ne_top a))
    · have h0 : μ a = 0 := by simpa [PMF.mem_support_iff] using ha
      simp [h0, ENNReal.toReal_nonneg]
  rwa [sum_sub_distrib, sum_toReal_eq_one μ, sum_toReal_eq_one ν, sub_self] at hbound

/-- Event-probability difference is bounded by `pmfTV μ ν`. -/
theorem abs_toOuterMeasure_sub_le_pmfTV {α : Type*} [Fintype α] (μ ν : PMF α) (S : Set α) :
    |(μ.toOuterMeasure S).toReal - (ν.toOuterMeasure S).toReal| ≤ pmfTV μ ν := by
  classical
  have h1 : (μ.toOuterMeasure S).toReal - (ν.toOuterMeasure S).toReal =
      ∑ a ∈ univ.filter (· ∈ S), ((μ a).toReal - (ν a).toReal) := by
    rw [outerMeasure_toReal_eq_sum, outerMeasure_toReal_eq_sum, ← sum_sub_distrib, sum_filter]
    exact sum_congr rfl fun a _ ↦ by by_cases ha : a ∈ S <;> simp [ha]
  have htot : ∑ a : α, ((μ a).toReal - (ν a).toReal) = 0 := by
    rw [sum_sub_distrib, sum_toReal_eq_one μ, sum_toReal_eq_one ν, sub_self]
  have h2 : (μ.toOuterMeasure S).toReal - (ν.toOuterMeasure S).toReal =
      -(∑ a ∈ univ.filter (· ∉ S), ((μ a).toReal - (ν a).toReal)) := by
    have hsplit := sum_filter_add_sum_filter_not (univ : Finset α) (· ∈ S)
      (fun a ↦ (μ a).toReal - (ν a).toReal)
    linarith
  have hb1 : |(μ.toOuterMeasure S).toReal - (ν.toOuterMeasure S).toReal| ≤
      ∑ a ∈ univ.filter (· ∈ S), |(μ a).toReal - (ν a).toReal| := by
    rw [h1]; exact abs_sum_le_sum_abs _ _
  have hb2 : |(μ.toOuterMeasure S).toReal - (ν.toOuterMeasure S).toReal| ≤
      ∑ a ∈ univ.filter (· ∉ S), |(μ a).toReal - (ν a).toReal| := by
    rw [h2, abs_neg]; exact abs_sum_le_sum_abs _ _
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset α) (· ∈ S)
    (fun a ↦ |(μ a).toReal - (ν a).toReal|)
  unfold pmfTV
  linarith

/-- Data-processing inequality for `pmfTV` under `PMF.bind`. -/
theorem pmfTV_bind_le {α β : Type*} [Fintype α] [Fintype β] (μ ν : PMF α) (κ : α → PMF β) :
    pmfTV (μ.bind κ) (ν.bind κ) ≤ pmfTV μ ν := by
  unfold pmfTV
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  calc
    ∑ b : β, |((μ.bind κ) b).toReal - ((ν.bind κ) b).toReal|
      = ∑ b : β, |∑ a : α, ((μ a).toReal - (ν a).toReal) * (κ a b).toReal| := by
        refine sum_congr rfl fun b _ ↦ ?_
        rw [bind_apply_toReal, bind_apply_toReal, ← sum_sub_distrib]
        congr 1; exact sum_congr rfl fun _ _ ↦ by ring
    _ ≤ ∑ b : β, ∑ a : α, |(μ a).toReal - (ν a).toReal| * (κ a b).toReal := by
        refine sum_le_sum fun b _ ↦ (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact sum_congr rfl fun _ _ ↦ by rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = ∑ a : α, |(μ a).toReal - (ν a).toReal| * ∑ b : β, (κ a b).toReal := by
        rw [sum_comm]; exact sum_congr rfl fun _ _ ↦ (mul_sum _ _ _).symm
    _ = ∑ a : α, |(μ a).toReal - (ν a).toReal| :=
        sum_congr rfl fun a _ ↦ by rw [sum_toReal_eq_one (κ a), mul_one]

/-- Data-processing inequality for `pmfKL` under deterministic pushforward `PMF.map`. -/
theorem pmfKL_map_le {α β : Type*} [Fintype α] [Fintype β] {μ ν : PMF α}
    (hsupp : μ.support ⊆ ν.support) (f : α → β) :
    pmfKL (μ.map f) (ν.map f) ≤ pmfKL μ ν := by
  classical
  have hmap_supp : (μ.map f).support ⊆ (ν.map f).support := by
    intro b hb
    rw [PMF.mem_support_map_iff] at hb ⊢
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a, hsupp ha, rfl⟩
  unfold pmfKL
  rw [← sum_fiberwise_of_maps_to (g := f) (fun a _ ↦ mem_univ (f a))
    (fun a ↦ (μ a).toReal * Real.log ((μ a).toReal / (ν a).toReal))]
  refine sum_le_sum fun b _ ↦ ?_
  let Fb := univ.filter (fun a : α ↦ f a = b)
  have hμb : ((μ.map f) b).toReal = ∑ a ∈ Fb, (μ a).toReal := map_apply_toReal μ f b
  have hνb : ((ν.map f) b).toReal = ∑ a ∈ Fb, (ν a).toReal := map_apply_toReal ν f b
  by_cases hb : b ∈ (μ.map f).support
  · have hμb_pos : 0 < ((μ.map f) b).toReal :=
      ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hb) ((μ.map f).apply_ne_top b)
    have hνb_pos : 0 < ((ν.map f) b).toReal :=
      ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (hmap_supp hb)) ((ν.map f).apply_ne_top b)
    have hrew : (∑ a ∈ Fb, (μ a).toReal * Real.log ((μ a).toReal / (ν a).toReal)) -
        ((μ.map f) b).toReal * Real.log (((μ.map f) b).toReal / ((ν.map f) b).toReal) =
        ((μ.map f) b).toReal * ∑ a ∈ Fb, ((μ a).toReal / ((μ.map f) b).toReal) *
          Real.log (((μ a).toReal / ((μ.map f) b).toReal) /
            ((ν a).toReal / ((ν.map f) b).toReal)) := by
      rw [mul_sum]
      conv_lhs => rw [hμb, sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun a _ ↦ ?_
      by_cases ha : a ∈ μ.support
      · have hμa : 0 < (μ a).toReal :=
          ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp ha) (μ.apply_ne_top a)
        have hνa : 0 < (ν a).toReal :=
          ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (hsupp ha)) (ν.apply_ne_top a)
        have hmul : ((μ.map f) b).toReal * ((μ a).toReal / ((μ.map f) b).toReal) = (μ a).toReal :=
          mul_div_cancel₀ _ hμb_pos.ne'
        rw [← mul_assoc, hmul, ← mul_sub, ← hμb]
        congr 1
        rw [← Real.log_div (div_pos hμa hνa).ne' (div_pos hμb_pos hνb_pos).ne']
        congr 1
        field_simp
      · have h0 : μ a = 0 := by simpa [PMF.mem_support_iff] using ha
        simp [h0]
    have hge : 0 ≤ ∑ a ∈ Fb, ((μ a).toReal / ((μ.map f) b).toReal) *
        Real.log (((μ a).toReal / ((μ.map f) b).toReal) /
          ((ν a).toReal / ((ν.map f) b).toReal)) := by
      have hsub : ∑ a ∈ Fb,
            ((μ a).toReal / ((μ.map f) b).toReal - (ν a).toReal / ((ν.map f) b).toReal) ≤
          ∑ a ∈ Fb, ((μ a).toReal / ((μ.map f) b).toReal) *
            Real.log (((μ a).toReal / ((μ.map f) b).toReal) /
              ((ν a).toReal / ((ν.map f) b).toReal)) := by
        refine sum_le_sum fun a _ ↦ ?_
        by_cases ha : a ∈ μ.support
        · have hνa : 0 < (ν a).toReal :=
            ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (hsupp ha)) (ν.apply_ne_top a)
          exact mul_log_div_ge_sub (div_nonneg ENNReal.toReal_nonneg hμb_pos.le)
            (div_pos hνa hνb_pos)
        · have h0 : μ a = 0 := by simpa [PMF.mem_support_iff] using ha
          have hpos' : 0 ≤ (ν a).toReal / ((ν.map f) b).toReal :=
            div_nonneg ENNReal.toReal_nonneg hνb_pos.le
          simp only [h0, ENNReal.toReal_zero, zero_div, zero_sub, zero_mul]
          linarith
      rwa [sum_sub_distrib, ← sum_div, ← sum_div, ← hμb, ← hνb,
        div_self hμb_pos.ne', div_self hνb_pos.ne', sub_self] at hsub
    have hprod : 0 ≤ ((μ.map f) b).toReal * _ := mul_nonneg hμb_pos.le hge
    linarith
  · have h0 : (μ.map f) b = 0 := by
      rw [PMF.mem_support_iff, not_not] at hb; exact hb
    have hall : ∀ a ∈ Fb, μ a = 0 := by
      intro a ha
      by_contra hne
      exact hb ((PMF.mem_support_map_iff _ _ _).mpr
        ⟨a, (PMF.mem_support_iff _ _).mpr hne, (mem_filter.mp ha).2⟩)
    simp only [h0, ENNReal.toReal_zero, zero_mul]
    exact sum_nonneg fun a ha ↦ by simp [hall a ha]

/-- **Chain rule inequality for `pmfKL`** along monadic `PMF.bind`. -/
theorem pmfKL_bind_le {α β : Type*} [Fintype α] [Fintype β] {μ ν : PMF α}
    (hsupp : μ.support ⊆ ν.support) {f g : α → PMF β}
    (hfg : ∀ a ∈ μ.support, (f a).support ⊆ (g a).support) :
    pmfKL (μ.bind f) (ν.bind g) ≤
      pmfKL μ ν + ∑ a : α, (μ a).toReal * pmfKL (f a) (g a) := by
  let P : PMF (α × β) := μ.bind fun a ↦ (f a).bind fun b ↦ PMF.pure (a, b)
  let Q : PMF (α × β) := ν.bind fun a ↦ (g a).bind fun b ↦ PMF.pure (a, b)
  have hP_apply : ∀ a b, (P (a, b)).toReal = (μ a).toReal * (f a b).toReal := fun a b ↦ by
    dsimp only [P]
    rw [Cslib.Probability.PMF.bind_pair_apply, ENNReal.toReal_mul]
  have hQ_apply : ∀ a b, (Q (a, b)).toReal = (ν a).toReal * (g a b).toReal := fun a b ↦ by
    dsimp only [Q]
    rw [Cslib.Probability.PMF.bind_pair_apply, ENNReal.toReal_mul]
  have hPQ_supp : P.support ⊆ Q.support := by
    rintro ⟨a, b⟩ hab
    simp only [P, Q, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hab ⊢
    obtain ⟨a', ha', b', hb', h1, h2⟩ := hab
    exact ⟨a', hsupp ha', b', hfg a' ha' hb', h1, h2⟩
  have hmapP : P.map Prod.snd = μ.bind f := by
    simp [P, PMF.map_bind, PMF.pure_map]
  have hmapQ : Q.map Prod.snd = ν.bind g := by
    simp [Q, PMF.map_bind, PMF.pure_map]
  have hchain : pmfKL P Q = pmfKL μ ν + ∑ a : α, (μ a).toReal * pmfKL (f a) (g a) := by
    unfold pmfKL
    rw [Fintype.sum_prod_type]
    have hsplit : ∀ a : α,
        ∑ b : β, (P (a, b)).toReal * Real.log ((P (a, b)).toReal / (Q (a, b)).toReal) =
        (μ a).toReal * Real.log ((μ a).toReal / (ν a).toReal) +
          (μ a).toReal * ∑ b : β, (f a b).toReal * Real.log ((f a b).toReal / (g a b).toReal) := by
      intro a
      simp_rw [hP_apply, hQ_apply]
      by_cases ha : a ∈ μ.support
      · have hμa : 0 < (μ a).toReal :=
          ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp ha) (μ.apply_ne_top a)
        have hνa : 0 < (ν a).toReal :=
          ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (hsupp ha)) (ν.apply_ne_top a)
        have hfb_sum : ∑ b : β, (f a b).toReal = 1 := sum_toReal_eq_one (f a)
        conv_rhs =>
          rw [← mul_one ((μ a).toReal * Real.log ((μ a).toReal / (ν a).toReal)),
            ← hfb_sum, mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun b _ ↦ ?_
        by_cases hb : b ∈ (f a).support
        · have hfb : 0 < (f a b).toReal :=
            ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hb) ((f a).apply_ne_top b)
          have hgb : 0 < (g a b).toReal :=
            ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (hfg a ha hb)) ((g a).apply_ne_top b)
          rw [mul_div_mul_comm, Real.log_mul (div_pos hμa hνa).ne' (div_pos hfb hgb).ne']
          ring
        · have h0 : f a b = 0 := by simpa [PMF.mem_support_iff] using hb
          simp [h0]
      · have h0 : μ a = 0 := by simpa [PMF.mem_support_iff] using ha
        simp [h0]
    simp_rw [hsplit]
    exact sum_add_distrib
  rw [← hmapP, ← hmapQ, ← hchain]
  exact pmfKL_map_le hPQ_supp Prod.snd

/-- **Pinsker's inequality** for finite `PMF`s: `2 * pmfTV μ ν ^ 2 ≤ pmfKL μ ν` whenever
`μ.support ⊆ ν.support`. -/
theorem two_mul_pmfTV_sq_le_pmfKL {α : Type*} [Fintype α] {μ ν : PMF α}
    (hsupp : μ.support ⊆ ν.support) :
    2 * pmfTV μ ν ^ 2 ≤ pmfKL μ ν := by
  classical
  let f : α → Bool := fun a ↦ decide ((ν a).toReal < (μ a).toReal)
  let p : ℝ := ((μ.map f) true).toReal
  let q : ℝ := ((ν.map f) true).toReal
  have hp_eq : p = ∑ a ∈ univ.filter (fun a ↦ (ν a).toReal < (μ a).toReal), (μ a).toReal := by
    dsimp only [p, f]
    rw [map_apply_toReal]
    exact sum_congr (by ext a; simp) fun _ _ ↦ rfl
  have hq_eq : q = ∑ a ∈ univ.filter (fun a ↦ (ν a).toReal < (μ a).toReal), (ν a).toReal := by
    dsimp only [q, f]
    rw [map_apply_toReal]
    exact sum_congr (by ext a; simp) fun _ _ ↦ rfl
  have htv_eq : pmfTV μ ν = p - q := by
    have hpos : p - q =
        ∑ a ∈ univ.filter (fun a ↦ (ν a).toReal < (μ a).toReal),
          ((μ a).toReal - (ν a).toReal) := by
      rw [hp_eq, hq_eq, ← sum_sub_distrib]
    have htot : ∑ a : α, ((μ a).toReal - (ν a).toReal) = 0 := by
      rw [sum_sub_distrib, sum_toReal_eq_one μ, sum_toReal_eq_one ν, sub_self]
    have hsplit := sum_filter_add_sum_filter_not (univ : Finset α)
      (fun a ↦ (ν a).toReal < (μ a).toReal) (fun a ↦ (μ a).toReal - (ν a).toReal)
    have habs_split := sum_filter_add_sum_filter_not (univ : Finset α)
      (fun a ↦ (ν a).toReal < (μ a).toReal) (fun a ↦ |(μ a).toReal - (ν a).toReal|)
    have ha1 : ∑ a ∈ univ.filter (fun a ↦ (ν a).toReal < (μ a).toReal),
        |(μ a).toReal - (ν a).toReal| = p - q := by
      rw [hpos]; exact sum_congr rfl fun a ha ↦ abs_of_pos (sub_pos.mpr (mem_filter.mp ha).2)
    have ha2 : ∑ a ∈ univ.filter (fun a ↦ ¬(ν a).toReal < (μ a).toReal),
        |(μ a).toReal - (ν a).toReal| = p - q := by
      have hneg : ∑ a ∈ univ.filter (fun a ↦ ¬(ν a).toReal < (μ a).toReal),
          |(μ a).toReal - (ν a).toReal| =
          -(∑ a ∈ univ.filter (fun a ↦ ¬(ν a).toReal < (μ a).toReal),
            ((μ a).toReal - (ν a).toReal)) := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun a ha ↦
          abs_of_nonpos (sub_nonpos.mpr (not_lt.mp (mem_filter.mp ha).2))
      linarith
    unfold pmfTV
    linarith
  have hpq : q ≤ p := by
    rw [hp_eq, hq_eq]; exact sum_le_sum fun a ha ↦ le_of_lt (mem_filter.mp ha).2
  rcases eq_or_lt_of_le hpq with heq | hlt
  · rw [htv_eq, heq, sub_self]; simpa using pmfKL_nonneg hsupp
  · have hq_pos : 0 < q := by
      have hex : ∃ a ∈ univ.filter (fun a ↦ (ν a).toReal < (μ a).toReal), 0 < (μ a).toReal := by
        by_contra hall
        push Not at hall
        have hp0 : p ≤ 0 := by rw [hp_eq]; exact sum_nonpos fun a ha ↦ hall a ha
        have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
        linarith
      obtain ⟨a, ha, hμa⟩ := hex
      have hmem : a ∈ μ.support := by
        rw [PMF.mem_support_iff]; intro h0; simp [h0] at hμa
      have hνa : 0 < (ν a).toReal :=
        ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (hsupp hmem)) (ν.apply_ne_top a)
      rw [hq_eq]
      exact sum_pos' (fun _ _ ↦ ENNReal.toReal_nonneg) ⟨a, ha, hνa⟩
    have hp_le : p ≤ 1 := by
      have h := sum_toReal_eq_one (μ.map f)
      simp only [Fintype.sum_bool] at h
      have hf0 : 0 ≤ ((μ.map f) false).toReal := ENNReal.toReal_nonneg
      dsimp only [p]; linarith
    have hbin : 2 * (p - q) ^ 2 ≤ binaryKL p q := by
      let φ : ℝ → ℝ := fun t ↦ binaryKL p t - 2 * (p - t) ^ 2
      have hderiv : ∀ t ∈ Set.Icc q p, t < 1 →
          HasDerivAt φ ((t - p) * (1 / (t * (1 - t)) - 4)) t := by
        intro t ht ht1
        have ht_pos : 0 < t := lt_of_lt_of_le hq_pos ht.1
        have hp_pos : 0 < p := lt_trans hq_pos hlt
        have h1t_pos : 0 < 1 - t := by linarith
        have hd1 : HasDerivAt (fun u : ℝ ↦ p * Real.log (p / u)) (-p / t) t := by
          have hdu : HasDerivAt (fun u : ℝ ↦ p / u) (p * (-(t ^ 2)⁻¹)) t := by
            simpa [div_eq_mul_inv] using (hasDerivAt_inv ht_pos.ne').const_mul p
          convert (hdu.log (div_pos hp_pos ht_pos).ne').const_mul p using 1
          have htne : t ≠ 0 := ht_pos.ne'
          have hpne : p ≠ 0 := hp_pos.ne'
          field_simp
        have hd2 : HasDerivAt (fun u : ℝ ↦ (1 - p) * Real.log ((1 - p) / (1 - u)))
            ((1 - p) / (1 - t)) t := by
          rcases eq_or_lt_of_le hp_le with hpeq | hp_lt
          · have h1p : 1 - p = 0 := by linarith
            simp only [h1p, zero_mul, zero_div]
            exact hasDerivAt_const t 0
          · have h1p : 0 < 1 - p := by linarith
            have hsub : HasDerivAt (fun u : ℝ ↦ 1 - u) (-1) t := by
              convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id' t) using 1; ring
            have hinv : HasDerivAt (fun u : ℝ ↦ (1 - u)⁻¹) (((1 - t) ^ 2)⁻¹) t := by
              convert hsub.inv h1t_pos.ne' using 1
              ring
            have hdu : HasDerivAt (fun u : ℝ ↦ (1 - p) / (1 - u)) ((1 - p) / (1 - t) ^ 2) t := by
              simpa [div_eq_mul_inv] using hinv.const_mul (1 - p)
            convert (hdu.log (div_pos h1p h1t_pos).ne').const_mul (1 - p) using 1
            have h1tne : 1 - t ≠ 0 := h1t_pos.ne'
            have h1pne : 1 - p ≠ 0 := h1p.ne'
            field_simp
        have hd3 : HasDerivAt (fun u : ℝ ↦ 2 * (p - u) ^ 2) (-4 * (p - t)) t := by
          have hsub : HasDerivAt (fun u : ℝ ↦ p - u) (-1) t := by
            convert (hasDerivAt_const t p).sub (hasDerivAt_id' t) using 1; ring
          convert (hsub.pow 2).const_mul 2 using 1
          ring
        have hsum : HasDerivAt φ (-p / t + (1 - p) / (1 - t) - -4 * (p - t)) t :=
          (hd1.add hd2).sub hd3
        have hdeq : -p / t + (1 - p) / (1 - t) - -4 * (p - t) =
            (t - p) * (1 / (t * (1 - t)) - 4) := by
          have htne : t ≠ 0 := ht_pos.ne'
          have h1tne : 1 - t ≠ 0 := h1t_pos.ne'
          field_simp
          ring
        rwa [hdeq] at hsum
      have hanti : AntitoneOn φ (Set.Icc q p) := by
        refine antitoneOn_of_hasDerivWithinAt_nonpos
          (f' := fun t ↦ (t - p) * (1 / (t * (1 - t)) - 4)) (convex_Icc q p) ?_ ?_ ?_
        · intro t ht
          rcases eq_or_lt_of_le ht.2 with htp_eq | htp
          · rcases eq_or_lt_of_le hp_le with hpeq | hp_lt
            · have hφ1 : φ = fun u ↦ Real.log (1 / u) - 2 * (1 - u) ^ 2 := by
                ext u; simp [φ, binaryKL, hpeq]
              rw [hφ1]
              have ht_pos : 0 < t := lt_of_lt_of_le hq_pos ht.1
              have hc1 : ContinuousAt (fun u : ℝ ↦ Real.log (1 / u)) t :=
                (continuousAt_const.div continuousAt_id ht_pos.ne').log
                  (div_pos zero_lt_one ht_pos).ne'
              have hc2 : ContinuousAt (fun u : ℝ ↦ 2 * (1 - u) ^ 2) t := by fun_prop
              exact (hc1.sub hc2).continuousWithinAt
            · rw [← htp_eq] at hp_lt
              exact (hderiv t ht hp_lt).continuousAt.continuousWithinAt
          · exact (hderiv t ht (lt_of_lt_of_le htp hp_le)).continuousAt.continuousWithinAt
        · intro t ht
          have ht' : t ∈ Set.Ioo q p := by simpa [interior_Icc] using ht
          exact (hderiv t ⟨ht'.1.le, ht'.2.le⟩ (lt_of_lt_of_le ht'.2 hp_le)).hasDerivWithinAt
        · intro t ht
          have ht' : t ∈ Set.Ioo q p := by simpa [interior_Icc] using ht
          have ht_pos : 0 < t := lt_trans hq_pos ht'.1
          have ht_lt1 : t < 1 := lt_of_lt_of_le ht'.2 hp_le
          have hge4 : 4 ≤ 1 / (t * (1 - t)) := by
            rw [le_div_iff₀ (mul_pos ht_pos (by linarith))]
            nlinarith [sq_nonneg (t - 1 / 2)]
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith [ht'.2]) (by linarith)
      have hφp : φ p = 0 := by
        have hp_pos : 0 < p := lt_trans hq_pos hlt
        simp only [φ, binaryKL, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, mul_zero, sub_zero, div_self hp_pos.ne', Real.log_one, zero_add]
        rcases eq_or_lt_of_le hp_le with hpeq | hp_lt
        · simp [hpeq]
        · rw [div_self (by linarith : 1 - p ≠ 0), Real.log_one, mul_zero]
      have hle : φ p ≤ φ q := hanti ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt.le
      rw [hφp] at hle
      dsimp only [φ] at hle
      linarith
    calc
      2 * pmfTV μ ν ^ 2 = 2 * (p - q) ^ 2 := by rw [htv_eq]
      _ ≤ binaryKL p q := hbin
      _ = pmfKL (μ.map f) (ν.map f) := (pmfKL_bool_eq_binaryKL _ _).symm
      _ ≤ pmfKL μ ν := pmfKL_map_le hsupp f

/-- **Bretagnolle--Huber inequality** for finite `PMF`s: whenever `μ.support ⊆ ν.support`,
`pmfTV μ ν ^ 2 ≤ 1 - exp (-pmfKL μ ν)`. -/
theorem bretagnolle_huber_pmf {α : Type*} [Fintype α] {μ ν : PMF α}
    (hsupp : μ.support ⊆ ν.support) :
    pmfTV μ ν ^ 2 ≤ 1 - Real.exp (-pmfKL μ ν) := by
  classical
  let B : ℝ := ∑ a : α, Real.sqrt ((μ a).toReal * (ν a).toReal)
  have hcs : B ^ 2 ≤
      (∑ a : α, min (μ a).toReal (ν a).toReal) * (∑ a : α, max (μ a).toReal (ν a).toReal) := by
    have hrewrite : B = ∑ a : α,
        Real.sqrt (min (μ a).toReal (ν a).toReal) * Real.sqrt (max (μ a).toReal (ν a).toReal) := by
      refine sum_congr rfl fun a _ ↦ ?_
      rw [← Real.sqrt_mul (le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg), min_mul_max]
    rw [hrewrite]
    refine (sum_mul_sq_le_sq_mul_sq univ
      (fun a ↦ Real.sqrt (min (μ a).toReal (ν a).toReal))
      (fun a ↦ Real.sqrt (max (μ a).toReal (ν a).toReal))).trans (le_of_eq ?_)
    congr 1 <;> refine sum_congr rfl fun _ _ ↦ Real.sq_sqrt ?_
    · exact le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · exact le_max_of_le_left ENNReal.toReal_nonneg
  have hmin_sum : ∑ a : α, min (μ a).toReal (ν a).toReal = 1 - pmfTV μ ν := by
    have hpt : ∀ u v : ℝ, min u v = (u + v - |u - v|) / 2 := fun u v ↦ by
      rcases le_total u v with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    simp_rw [hpt, ← sum_div, sum_sub_distrib, sum_add_distrib, sum_toReal_eq_one]
    unfold pmfTV; ring
  have hmax_sum : ∑ a : α, max (μ a).toReal (ν a).toReal = 1 + pmfTV μ ν := by
    have hpt : ∀ u v : ℝ, max u v = (u + v + |u - v|) / 2 := fun u v ↦ by
      rcases le_total u v with h | h
      · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
      · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
    simp_rw [hpt, ← sum_div, sum_add_distrib, sum_toReal_eq_one]
    unfold pmfTV; ring
  rw [hmin_sum, hmax_sum] at hcs
  let S := univ.filter (fun a : α ↦ a ∈ μ.support)
  have hw_sum : ∑ a ∈ S, (μ a).toReal = 1 := by
    rw [← sum_toReal_eq_one μ]
    refine sum_subset (subset_univ S) fun a _ ha ↦ ?_
    simp only [S, mem_filter, mem_univ, true_and, PMF.mem_support_iff, not_not] at ha
    simp [ha]
  have hjensen := convexOn_exp.map_sum_le
    (t := S) (w := fun a ↦ (μ a).toReal)
    (p := fun a ↦ -(Real.log ((μ a).toReal / (ν a).toReal) / 2))
    (fun _ _ ↦ ENNReal.toReal_nonneg) hw_sum (fun _ _ ↦ Set.mem_univ _)
  have hlhs : Real.exp (∑ a ∈ S, (μ a).toReal • -(Real.log ((μ a).toReal / (ν a).toReal) / 2)) =
      Real.exp (-pmfKL μ ν / 2) := by
    congr 1
    have hkl : pmfKL μ ν = ∑ a ∈ S, (μ a).toReal * Real.log ((μ a).toReal / (ν a).toReal) := by
      unfold pmfKL
      refine (sum_subset (subset_univ S) fun a _ ha ↦ ?_).symm
      simp only [S, mem_filter, mem_univ, true_and, PMF.mem_support_iff, not_not] at ha
      simp [ha]
    rw [hkl, neg_div, sum_div, ← sum_neg_distrib]
    simp only [smul_eq_mul]
    exact sum_congr rfl fun _ _ ↦ by ring
  have hrhs : ∑ a ∈ S, (μ a).toReal • Real.exp (-(Real.log ((μ a).toReal / (ν a).toReal) / 2)) ≤
      B := by
    have heq : ∑ a ∈ S, (μ a).toReal • Real.exp (-(Real.log ((μ a).toReal / (ν a).toReal) / 2)) =
        ∑ a ∈ S, Real.sqrt ((μ a).toReal * (ν a).toReal) := by
      refine sum_congr rfl fun a ha ↦ ?_
      have hmem : a ∈ μ.support := (mem_filter.mp ha).2
      have hμa : 0 < (μ a).toReal :=
        ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hmem) (μ.apply_ne_top a)
      have hνa : 0 < (ν a).toReal :=
        ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (hsupp hmem)) (ν.apply_ne_top a)
      simp only [smul_eq_mul]
      have hlog : -(Real.log ((μ a).toReal / (ν a).toReal) / 2) =
          Real.log (Real.sqrt ((ν a).toReal / (μ a).toReal)) := by
        rw [Real.log_sqrt (div_pos hνa hμa).le, Real.log_div hνa.ne' hμa.ne',
          Real.log_div hμa.ne' hνa.ne']
        ring
      rw [hlog, Real.exp_log (Real.sqrt_pos.mpr (div_pos hνa hμa))]
      have hμ_sq : (μ a).toReal = Real.sqrt ((μ a).toReal ^ 2) := (Real.sqrt_sq hμa.le).symm
      calc
        (μ a).toReal * Real.sqrt ((ν a).toReal / (μ a).toReal)
          = Real.sqrt ((μ a).toReal ^ 2) * Real.sqrt ((ν a).toReal / (μ a).toReal) :=
              congrArg (· * _) hμ_sq
        _ = Real.sqrt ((μ a).toReal ^ 2 * ((ν a).toReal / (μ a).toReal)) :=
              (Real.sqrt_mul (sq_nonneg _) _).symm
        _ = Real.sqrt ((μ a).toReal * (ν a).toReal) := by
              congr 1
              have hne : (μ a).toReal ≠ 0 := hμa.ne'
              field_simp
    rw [heq]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ S) fun _ _ _ ↦ Real.sqrt_nonneg _
  rw [hlhs] at hjensen
  have hexp_le : Real.exp (-pmfKL μ ν / 2) ≤ B := hjensen.trans hrhs
  have hexp_sq : Real.exp (-pmfKL μ ν) ≤ B ^ 2 := by
    have hsq : Real.exp (-pmfKL μ ν / 2) ^ 2 = Real.exp (-pmfKL μ ν) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [← hsq]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hexp_le 2
  nlinarith

/-! ### Independent sample products and post-processing divergence bounds -/

/-- Canonical `s`-fold independent product `PMF` drawing `s` i.i.d. samples from `μ : PMF α`. -/
noncomputable def iidSamples {α : Type*} (μ : PMF α) : ∀ s : ℕ, PMF (Fin s → α)
  | 0 => PMF.pure Fin.elim0
  | s + 1 => (iidSamples μ s).bind fun h ↦ μ.map (Fin.snoc h)

/-- Base equation for `iidSamples` at `0` samples. -/
@[simp]
theorem iidSamples_zero {α : Type*} (μ : PMF α) :
    iidSamples μ 0 = PMF.pure Fin.elim0 := by
  unfold iidSamples; rfl

/-- Step equation for `iidSamples` at `s + 1` samples. -/
@[simp]
theorem iidSamples_succ {α : Type*} (μ : PMF α) (s : ℕ) :
    iidSamples μ (s + 1) = (iidSamples μ s).bind fun h ↦ μ.map (Fin.snoc h) := by
  rw [iidSamples]

/-- Support inclusion lifts to `iidSamples`. -/
theorem support_iidSamples_subset {α : Type*} {μ ν : PMF α} (hsupp : μ.support ⊆ ν.support)
    (s : ℕ) :
    (iidSamples μ s).support ⊆ (iidSamples ν s).support := by
  induction s with
  | zero => simp
  | succ k ih =>
    intro w hw
    simp only [iidSamples_succ, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hw ⊢
    obtain ⟨h, hh, a, ha, rfl⟩ := hw
    exact ⟨h, ih hh, a, hsupp ha, rfl⟩

/-- Tensorization inequality `pmfKL (iidSamples μ s) (iidSamples ν s) ≤ s * pmfKL μ ν`. -/
theorem pmfKL_iidSamples_le {α : Type*} [Fintype α] {μ ν : PMF α}
    (hsupp : μ.support ⊆ ν.support) (s : ℕ) :
    pmfKL (iidSamples μ s) (iidSamples ν s) ≤ (s : ℝ) * pmfKL μ ν := by
  induction s with
  | zero => simp [pmfKL]
  | succ k ih =>
    rw [iidSamples_succ, iidSamples_succ]
    let snocFn : (Fin k → α) → α → (Fin (k + 1) → α) := fun h a ↦ Fin.snoc (α := fun _ ↦ α) h a
    let fμ : (Fin k → α) → PMF (Fin (k + 1) → α) := fun h ↦ μ.map (snocFn h)
    let fν : (Fin k → α) → PMF (Fin (k + 1) → α) := fun h ↦ ν.map (snocFn h)
    have hfg : ∀ h ∈ (iidSamples μ k).support, (fμ h).support ⊆ (fν h).support := by
      intro h _ w hw
      dsimp only [fμ, fν] at hw ⊢
      rw [PMF.mem_support_map_iff] at hw ⊢
      obtain ⟨a, ha, hwa⟩ := hw
      exact ⟨a, hsupp ha, hwa⟩
    have h1 := pmfKL_bind_le (support_iidSamples_subset hsupp k) hfg
    have h2 : ∑ h : Fin k → α, ((iidSamples μ k) h).toReal * pmfKL (fμ h) (fν h) ≤
        pmfKL μ ν := by
      calc
        ∑ h : Fin k → α, ((iidSamples μ k) h).toReal * pmfKL (fμ h) (fν h)
          ≤ ∑ h : Fin k → α, ((iidSamples μ k) h).toReal * pmfKL μ ν :=
            sum_le_sum fun h _ ↦
              mul_le_mul_of_nonneg_left (pmfKL_map_le hsupp (snocFn h)) ENNReal.toReal_nonneg
        _ = pmfKL μ ν := by rw [← sum_mul, sum_toReal_eq_one, one_mul]
    have h3 : (k : ℝ) * pmfKL μ ν + pmfKL μ ν = ((k + 1 : ℕ) : ℝ) * pmfKL μ ν := by
      rw [Nat.cast_add, Nat.cast_one]; ring
    exact h1.trans (by linarith)

/-- Pinsker bound on any randomized post-processing `κ` of `s` i.i.d. samples. -/
theorem postprocess_iidSamples_pinsker {α β : Type*} [Fintype α] [Finite β] {μ ν : PMF α}
    (hsupp : μ.support ⊆ ν.support) (s : ℕ) (κ : (Fin s → α) → PMF β) (E : Set β) :
    2 * ((((iidSamples μ s).bind κ).toOuterMeasure E).toReal -
        (((iidSamples ν s).bind κ).toOuterMeasure E).toReal) ^ 2 ≤
      (s : ℝ) * pmfKL μ ν := by
  cases nonempty_fintype β
  have h1 : |(((iidSamples μ s).bind κ).toOuterMeasure E).toReal -
      (((iidSamples ν s).bind κ).toOuterMeasure E).toReal| ≤
      pmfTV (iidSamples μ s) (iidSamples ν s) :=
    (abs_toOuterMeasure_sub_le_pmfTV ((iidSamples μ s).bind κ) ((iidSamples ν s).bind κ) E).trans
      (pmfTV_bind_le (iidSamples μ s) (iidSamples ν s) κ)
  have hsq : ((((iidSamples μ s).bind κ).toOuterMeasure E).toReal -
      (((iidSamples ν s).bind κ).toOuterMeasure E).toReal) ^ 2 ≤
      pmfTV (iidSamples μ s) (iidSamples ν s) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  linarith [two_mul_pmfTV_sq_le_pmfKL (support_iidSamples_subset hsupp s),
    pmfKL_iidSamples_le hsupp s]

/-- Bretagnolle--Huber bound on any randomized post-processing `κ` of `s` i.i.d. samples. -/
theorem postprocess_iidSamples_bretagnolle_huber {α β : Type*} [Fintype α] [Finite β]
    {μ ν : PMF α} (hsupp : μ.support ⊆ ν.support) (s : ℕ) (κ : (Fin s → α) → PMF β) (E : Set β) :
    ((((iidSamples μ s).bind κ).toOuterMeasure E).toReal -
        (((iidSamples ν s).bind κ).toOuterMeasure E).toReal) ^ 2 ≤
      1 - Real.exp (-((s : ℝ) * pmfKL μ ν)) := by
  cases nonempty_fintype β
  have h1 : |(((iidSamples μ s).bind κ).toOuterMeasure E).toReal -
      (((iidSamples ν s).bind κ).toOuterMeasure E).toReal| ≤
      pmfTV (iidSamples μ s) (iidSamples ν s) :=
    (abs_toOuterMeasure_sub_le_pmfTV ((iidSamples μ s).bind κ) ((iidSamples ν s).bind κ) E).trans
      (pmfTV_bind_le (iidSamples μ s) (iidSamples ν s) κ)
  have hsq : ((((iidSamples μ s).bind κ).toOuterMeasure E).toReal -
      (((iidSamples ν s).bind κ).toOuterMeasure E).toReal) ^ 2 ≤
      pmfTV (iidSamples μ s) (iidSamples ν s) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hbh := bretagnolle_huber_pmf (support_iidSamples_subset hsupp s)
  have hexp : Real.exp (-((s : ℝ) * pmfKL μ ν)) ≤
      Real.exp (-pmfKL (iidSamples μ s) (iidSamples ν s)) :=
    Real.exp_le_exp.mpr (neg_le_neg (pmfKL_iidSamples_le hsupp s))
  linarith

/-! ### Adaptive query trees and hypergeometric slice divergence -/

/-- A finite-depth adaptive oracle decision tree querying coordinates in `ι`, receiving answers in
`α`, and outputting a value in `γ`. -/
inductive QueryTree (ι α γ : Type*) : Type _
  /-- Halt without further queries and output `out`. -/
  | leaf (out : γ) : QueryTree ι α γ
  /-- Query coordinate `idx` and branch on the returned answer in `α`. -/
  | query (idx : ι) (next : α → QueryTree ι α γ) : QueryTree ι α γ

/-- Evaluate an adaptive `QueryTree` against an oracle `x : ι → α`. -/
def QueryTree.eval {ι α γ : Type*} : QueryTree ι α γ → (ι → α) → γ
  | .leaf out, _ => out
  | .query idx next, x => (next (x idx)).eval x

/-- Evaluating a leaf returns its output. -/
@[simp]
theorem QueryTree.eval_leaf {ι α γ : Type*} (out : γ) (x : ι → α) :
    (QueryTree.leaf out : QueryTree ι α γ).eval x = out := by
  unfold eval; rfl

/-- Evaluating a query node inspects `x idx` and recurses into `next (x idx)`. -/
@[simp]
theorem QueryTree.eval_query {ι α γ : Type*} (idx : ι) (next : α → QueryTree ι α γ) (x : ι → α) :
    (QueryTree.query idx next).eval x = (next (x idx)).eval x := by
  rw [eval]

/-- Predicate asserting that `T` makes at most `q` oracle queries along every execution path. -/
@[expose]
def QueryTree.HasDepthAtMost {ι α γ : Type*} : QueryTree ι α γ → ℕ → Prop
  | .leaf _, _ => True
  | .query _ _, 0 => False
  | .query _ next, q + 1 => ∀ a : α, (next a).HasDepthAtMost q

/-- Finset of coordinates queried by `T` along its execution path on `x`. -/
def QueryTree.queriedSet {ι α γ : Type*} [DecidableEq ι] :
    QueryTree ι α γ → (ι → α) → Finset ι
  | .leaf _, _ => ∅
  | .query idx next, x => insert idx ((next (x idx)).queriedSet x)

/-- Along any execution path of a tree of depth at most `q`, at most `q` coordinates are queried. -/
theorem QueryTree.card_queriedSet_le {ι α γ : Type*} [DecidableEq ι] {T : QueryTree ι α γ}
    {q : ℕ} (hT : T.HasDepthAtMost q) (x : ι → α) :
    #(T.queriedSet x) ≤ q := by
  induction T generalizing q with
  | leaf _ => simp [queriedSet]
  | query idx next ih =>
    cases q with
    | zero => exact False.elim hT
    | succ q =>
      simp only [queriedSet]
      exact (card_insert_le _ _).trans (Nat.succ_le_succ (ih (x idx) (hT (x idx))))

/-- Two oracles agreeing on `T.queriedSet x` yield identical outputs under `T.eval`. -/
theorem QueryTree.eval_congr {ι α γ : Type*} [DecidableEq ι] (T : QueryTree ι α γ)
    {x y : ι → α} (hxy : ∀ i ∈ T.queriedSet x, x i = y i) :
    T.eval x = T.eval y := by
  induction T with
  | leaf _ => simp
  | query idx next ih =>
    simp only [eval_query]
    have hidx : x idx = y idx := hxy idx (by simp [queriedSet])
    rw [← hidx]
    exact ih (x idx) fun i hi ↦ hxy i (by simp [queriedSet, hi])

/-- Finset of Boolean strings `x : Fin m → Bool` of exact Hamming weight `k`. -/
@[expose] def sliceFinset (m k : ℕ) : Finset (Fin m → Bool) :=
  univ.filter fun x : Fin m → Bool ↦ #(univ.filter fun i : Fin m ↦ x i = true) = k

private lemma card_sliceFinset (m k : ℕ) : #(sliceFinset m k) = m.choose k := by
  unfold sliceFinset
  let e : (Fin m → Bool) ≃ Finset (Fin m) :=
    { toFun := fun x ↦ univ.filter fun i ↦ x i = true
      invFun := fun S i ↦ decide (i ∈ S)
      left_inv := fun x ↦ by funext i; cases h : x i <;> simp [h]
      right_inv := fun S ↦ by ext i; simp }
  rw [show #(univ.filter fun x : Fin m → Bool ↦
      #(univ.filter fun i : Fin m ↦ x i = true) = k) =
      #(powersetCard k (univ : Finset (Fin m))) from
    card_bij (fun x _ ↦ e x)
      (fun x hx ↦ mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hx).2⟩)
      (fun _ _ _ _ h ↦ e.injective h)
      (fun S hS ↦ ⟨e.symm S, by simp [e, (mem_powersetCard.mp hS).2], e.apply_symm_apply S⟩)]
  simp

/-- Nonemptiness of `sliceFinset m k` for `k ≤ m`. -/
theorem sliceFinset_nonempty {m k : ℕ} (hk : k ≤ m) : (sliceFinset m k).Nonempty := by
  rw [← card_pos, card_sliceFinset]; exact Nat.choose_pos hk

/-- Uniform `PMF` over all Boolean strings `x : Fin m → Bool` of Hamming weight `k ≤ m`. -/
@[expose] noncomputable def uniformSlicePMF (m k : ℕ) (hk : k ≤ m) : PMF (Fin m → Bool) :=
  Cslib.Probability.PMF.uniformOfFinset (sliceFinset m k) (sliceFinset_nonempty hk)

private def condSlice (m k : ℕ) (ones zeros : Finset (Fin m)) : Finset (Fin m → Bool) :=
  (sliceFinset m k).filter fun x ↦ (∀ i ∈ ones, x i = true) ∧ (∀ i ∈ zeros, x i = false)

private lemma card_condSlice {m k : ℕ} {ones zeros : Finset (Fin m)}
    (hdisj : Disjoint ones zeros) (hk : #ones ≤ k) :
    #(condSlice m k ones zeros) = (m - (#ones + #zeros)).choose (k - #ones) := by
  let rest : Finset (Fin m) := univ \ (ones ∪ zeros)
  have hcard_rest : #rest = m - (#ones + #zeros) := by
    rw [card_sdiff, inter_univ, card_union_of_disjoint hdisj, card_univ, Fintype.card_fin]
  rw [← hcard_rest, ← card_powersetCard]
  refine card_bij (fun x _ ↦ rest.filter fun i ↦ x i = true) ?_ ?_ ?_
  · intro x hx
    simp only [condSlice, sliceFinset, mem_filter, mem_univ, true_and] at hx
    obtain ⟨hwt, h1, h0⟩ := hx
    refine mem_powersetCard.mpr ⟨filter_subset _ _, ?_⟩
    have hpart : (univ.filter fun i : Fin m ↦ x i = true) =
        ones ∪ rest.filter (fun i ↦ x i = true) := by
      ext i
      simp only [rest, mem_filter, mem_univ, true_and, mem_union, mem_sdiff, not_or]
      constructor
      · intro hxi
        by_cases hi1 : i ∈ ones
        · exact Or.inl hi1
        · exact Or.inr ⟨⟨hi1, fun hi0 ↦ by have := h0 i hi0; simp [hxi] at this⟩, hxi⟩
      · rintro (hi1 | ⟨_, hxi⟩)
        · exact h1 i hi1
        · exact hxi
    have hd : Disjoint ones (rest.filter fun i ↦ x i = true) :=
      disjoint_left.mpr fun i hi1 hir ↦ by simp [rest, hi1] at hir
    have hc := congrArg card hpart
    rw [hwt, card_union_of_disjoint hd] at hc
    omega
  · intro x₁ hx₁ x₂ hx₂ heq
    simp only [condSlice, mem_filter] at hx₁ hx₂
    funext i
    by_cases hi1 : i ∈ ones
    · rw [hx₁.2.1 i hi1, hx₂.2.1 i hi1]
    · by_cases hi0 : i ∈ zeros
      · rw [hx₁.2.2 i hi0, hx₂.2.2 i hi0]
      · have hir : i ∈ rest := by simp [rest, hi1, hi0]
        have hiff : i ∈ rest.filter (fun j ↦ x₁ j = true) ↔
            i ∈ rest.filter (fun j ↦ x₂ j = true) := by rw [heq]
        simp only [mem_filter, hir, true_and] at hiff
        cases h1 : x₁ i <;> cases h2 : x₂ i <;> simp_all
  · intro S hS
    rw [mem_powersetCard] at hS
    let x : Fin m → Bool := fun i ↦ decide (i ∈ ones ∪ S)
    have hd : Disjoint ones S :=
      disjoint_left.mpr fun i hi1 hiS ↦ by have := hS.1 hiS; simp [rest, hi1] at this
    refine ⟨x, ?_, ?_⟩
    · simp only [condSlice, sliceFinset, mem_filter, mem_univ, true_and, x]
      refine ⟨?_, fun i hi ↦ by simp [hi], fun i hi ↦ ?_⟩
      · have hfilt : (univ.filter fun i : Fin m ↦ decide (i ∈ ones ∪ S) = true) = ones ∪ S := by
          ext i; simp
        rw [hfilt, card_union_of_disjoint hd, hS.2]; omega
      · simp only [decide_eq_false_iff_not, mem_union, not_or]
        exact ⟨disjoint_right.mp hdisj hi, fun hiS ↦ by have := hS.1 hiS; simp [rest, hi] at this⟩
    · ext i
      simp only [x, mem_filter, decide_eq_true_eq, mem_union]
      exact ⟨fun ⟨hir, h⟩ ↦ h.resolve_left fun hi1 ↦ by simp [rest, hi1] at hir,
        fun hiS ↦ ⟨hS.1 hiS, Or.inr hiS⟩⟩

private lemma pmf_map_congr {α β : Type*} (μ : PMF α) {f g : α → β}
    (h : ∀ a ∈ μ.support, f a = g a) : μ.map f = μ.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun a ↦ ?_
  by_cases ha : a ∈ μ.support
  · rw [h a ha]
  · have h0 : μ a = 0 := by simpa [PMF.mem_support_iff] using ha
    simp [h0]

private lemma condSlice_nonempty {m k : ℕ} (hkm : k ≤ m) {ones zeros : Finset (Fin m)}
    (hdisj : Disjoint ones zeros) (h1 : #ones ≤ k) (h0 : #zeros ≤ m - k) :
    (condSlice m k ones zeros).Nonempty := by
  rw [← card_pos, card_condSlice hdisj h1]
  exact Nat.choose_pos (by omega)

private lemma mem_support_unifFinset {α : Type*} (s : Finset α) (hs : s.Nonempty) (a : α) :
    a ∈ (Cslib.Probability.PMF.uniformOfFinset s hs).support ↔ a ∈ s := by
  rw [PMF.mem_support_iff, Cslib.Probability.PMF.uniformOfFinset_apply]
  by_cases ha : a ∈ s <;> simp [ha]

private lemma condSlice_split_coord {m k : ℕ} (hkm : k ≤ m) {ones zeros : Finset (Fin m)}
    (hdisj : Disjoint ones zeros) (h1 : #ones ≤ k) (h0 : #zeros ≤ m - k)
    {idx : Fin m} (hidx1 : idx ∉ ones) (hidx0 : idx ∉ zeros)
    (hpos : 0 < k - #ones) (hlt : k - #ones < m - (#ones + #zeros)) :
    let hne := condSlice_nonempty hkm hdisj h1 h0
    let μ := Cslib.Probability.PMF.uniformOfFinset (condSlice m k ones zeros) hne
    let bern := μ.map (fun x ↦ x idx)
    let hne_t := condSlice_nonempty hkm (disjoint_insert_left.mpr ⟨hidx0, hdisj⟩)
      (by rw [card_insert_of_notMem hidx1]; omega) h0
    let hne_f := condSlice_nonempty hkm (disjoint_insert_right.mpr ⟨hidx1, hdisj⟩) h1
      (by rw [card_insert_of_notMem hidx0]; omega)
    (bern true).toReal = ((k - #ones : ℕ) : ℝ) / ((m - (#ones + #zeros) : ℕ) : ℝ) ∧
      μ = bern.bind fun b ↦
        if b then
          Cslib.Probability.PMF.uniformOfFinset (condSlice m k (insert idx ones) zeros) hne_t
        else
          Cslib.Probability.PMF.uniformOfFinset (condSlice m k ones (insert idx zeros)) hne_f := by
  intro hne μ bern hne_t hne_f
  set N := m - (#ones + #zeros)
  set K := k - #ones
  have hN_pos : 0 < N := by omega
  have hct : #(condSlice m k (insert idx ones) zeros) = (N - 1).choose (K - 1) := by
    rw [card_condSlice (disjoint_insert_left.mpr ⟨hidx0, hdisj⟩)
      (by rw [card_insert_of_notMem hidx1]; omega), card_insert_of_notMem hidx1]
    congr 1; omega
  have hcf : #(condSlice m k ones (insert idx zeros)) = (N - 1).choose K := by
    rw [card_condSlice (disjoint_insert_right.mpr ⟨hidx1, hdisj⟩) h1,
      card_insert_of_notMem hidx0]
    congr 1
  have hc : #(condSlice m k ones zeros) = N.choose K := card_condSlice hdisj h1
  have hfilt_t : (condSlice m k ones zeros).filter (fun x ↦ x idx = true) =
      condSlice m k (insert idx ones) zeros := by
    ext x; simp only [condSlice, mem_filter, mem_insert, forall_eq_or_imp]; tauto
  have hfilt_f : (condSlice m k ones zeros).filter (fun x ↦ x idx = false) =
      condSlice m k ones (insert idx zeros) := by
    ext x; simp only [condSlice, mem_filter, mem_insert, forall_eq_or_imp]; tauto
  have hchoose_mul : (N - 1).choose (K - 1) * N = N.choose K * K := by
    have h := Nat.add_one_mul_choose_eq (N - 1) (K - 1)
    rw [show N - 1 + 1 = N by omega, show K - 1 + 1 = K by omega] at h
    linarith
  have hbern_val : ∀ b : Bool,
      bern b = (#((condSlice m k ones zeros).filter (fun x ↦ x idx = b)) : ℝ≥0∞) *
        ((#(condSlice m k ones zeros) : ℝ≥0∞))⁻¹ := by
    intro b
    classical
    dsimp only [bern, μ]
    rw [PMF.map_apply, tsum_fintype (L := .unconditional _)]
    simp only [Cslib.Probability.PMF.uniformOfFinset_apply]
    trans ∑ x : Fin m → Bool,
        if x ∈ (condSlice m k ones zeros).filter (fun x ↦ x idx = b) then
          ((#(condSlice m k ones zeros) : ℝ≥0∞))⁻¹ else 0
    · refine sum_congr rfl fun x _ ↦ ?_
      simp only [mem_filter]
      by_cases hx : x ∈ condSlice m k ones zeros <;> by_cases hb : x idx = b
      · simp [hx, hb]
      · have hb' : b ≠ x idx := fun h ↦ hb h.symm
        simp [hx, hb, hb']
      · simp [hx, hb]
      · simp [hx, hb]
    · rw [← sum_filter, sum_const, nsmul_eq_mul]
      congr 3; ext x; simp
  refine ⟨?_, ?_⟩
  · rw [hbern_val true, hfilt_t, hc, hct, ← div_eq_mul_inv, ENNReal.toReal_div,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    have hc_pos : (0 : ℝ) < (N.choose K : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hN_pos_r : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
    rw [div_eq_div_iff hc_pos.ne' hN_pos_r.ne', mul_comm (K : ℝ)]
    exact_mod_cast hchoose_mul
  · ext x
    rw [PMF.bind_apply, tsum_fintype (L := .unconditional _), Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true, hbern_val true, hbern_val false, hfilt_t, hfilt_f,
      μ, Cslib.Probability.PMF.uniformOfFinset_apply]
    have hct_ne0 : (#(condSlice m k (insert idx ones) zeros) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr hne_t.card_pos.ne'
    have hcf_ne0 : (#(condSlice m k ones (insert idx zeros)) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr hne_f.card_pos.ne'
    by_cases hx : x ∈ condSlice m k ones zeros
    · cases hb : x idx
      · have hxf : x ∈ condSlice m k ones (insert idx zeros) := by
          rw [← hfilt_f]; exact mem_filter.mpr ⟨hx, hb⟩
        have hxt : x ∉ condSlice m k (insert idx ones) zeros := by rw [← hfilt_t]; simp [hb]
        simp only [hx, ↓reduceIte, hxt, mul_zero, hxf, zero_add]
        rw [mul_comm (#(condSlice m k ones (insert idx zeros)) : ℝ≥0∞), mul_assoc,
          ENNReal.mul_inv_cancel hcf_ne0 (ENNReal.natCast_ne_top _), mul_one]
      · have hxt : x ∈ condSlice m k (insert idx ones) zeros := by
          rw [← hfilt_t]; exact mem_filter.mpr ⟨hx, hb⟩
        have hxf : x ∉ condSlice m k ones (insert idx zeros) := by rw [← hfilt_f]; simp [hb]
        simp only [hx, ↓reduceIte, hxt, hxf, mul_zero, add_zero]
        rw [mul_comm (#(condSlice m k (insert idx ones) zeros) : ℝ≥0∞), mul_assoc,
          ENNReal.mul_inv_cancel hct_ne0 (ENNReal.natCast_ne_top _), mul_one]
    · have hxt : x ∉ condSlice m k (insert idx ones) zeros := by rw [← hfilt_t]; simp [hx]
      have hxf : x ∉ condSlice m k ones (insert idx zeros) := by rw [← hfilt_f]; simp [hx]
      simp [hx, hxt, hxf]

private lemma queryTree_condSlice_kl_le {γ : Type*} [Fintype γ] {m k₁ k₂ q : ℕ}
    (hk₁ : k₁ ≤ m) (hk₂ : k₂ ≤ m) {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ t s : ℕ, t < q → s ≤ t →
      0 < k₁ - s ∧ k₁ - s < m - t ∧ 0 < k₂ - s ∧ k₂ - s < m - t ∧
      binaryKL (((k₁ - s : ℕ) : ℝ) / ((m - t : ℕ) : ℝ))
        (((k₂ - s : ℕ) : ℝ) / ((m - t : ℕ) : ℝ)) ≤ B) :
    ∀ (r : ℕ) (T : QueryTree (Fin m) Bool γ), T.HasDepthAtMost r →
      ∀ (ones zeros : Finset (Fin m)) (hdisj : Disjoint ones zeros),
        #ones + #zeros + r ≤ q →
        (h1a : #ones ≤ k₁) → (h0a : #zeros ≤ m - k₁) →
        (h1b : #ones ≤ k₂) → (h0b : #zeros ≤ m - k₂) →
        let μ₁ := Cslib.Probability.PMF.uniformOfFinset (condSlice m k₁ ones zeros)
          (condSlice_nonempty hk₁ hdisj h1a h0a)
        let μ₂ := Cslib.Probability.PMF.uniformOfFinset (condSlice m k₂ ones zeros)
          (condSlice_nonempty hk₂ hdisj h1b h0b)
        (μ₁.map T.eval).support ⊆ (μ₂.map T.eval).support ∧
          pmfKL (μ₁.map T.eval) (μ₂.map T.eval) ≤ (r : ℝ) * B
  | r, .leaf out, _, ones, zeros, hdisj, _, h1a, h0a, h1b, h0b => by
    intro μ₁ μ₂
    have hconst : ∀ ν : PMF (Fin m → Bool), ν.map (QueryTree.leaf out).eval = PMF.pure out := by
      intro ν; ext c
      rw [PMF.map_apply, PMF.pure_apply]
      by_cases hc : c = out
      · subst hc
        simp only [QueryTree.eval_leaf, ↓reduceIte]
        exact ν.tsum_coe
      · simp [hc]
    rw [hconst μ₁, hconst μ₂]
    refine ⟨Set.Subset.rfl, ?_⟩
    have h0 : pmfKL (PMF.pure out) (PMF.pure out) = 0 := by
      unfold pmfKL
      exact sum_eq_zero fun c _ ↦ by by_cases hc : c = out <;> simp [hc]
    rw [h0]; positivity
  | 0, .query _ _, hT, _, _, _, _, _, _, _, _ => False.elim hT
  | r + 1, .query idx next, hT, ones, zeros, hdisj, hqr, h1a, h0a, h1b, h0b => by
    intro μ₁ μ₂
    by_cases hidx1 : idx ∈ ones
    · have heq1 : μ₁.map (QueryTree.query idx next).eval = μ₁.map (next true).eval :=
        pmf_map_congr μ₁ fun x hx ↦ by
          have := (mem_filter.mp ((mem_support_unifFinset _ _ x).mp hx)).2.1 idx hidx1
          simp [this]
      have heq2 : μ₂.map (QueryTree.query idx next).eval = μ₂.map (next true).eval :=
        pmf_map_congr μ₂ fun x hx ↦ by
          have := (mem_filter.mp ((mem_support_unifFinset _ _ x).mp hx)).2.1 idx hidx1
          simp [this]
      rw [heq1, heq2]
      obtain ⟨hs, hkl⟩ := queryTree_condSlice_kl_le hk₁ hk₂ hB0 hbound r (next true) (hT true)
        ones zeros hdisj (by omega) h1a h0a h1b h0b
      exact ⟨hs, hkl.trans (by rw [Nat.cast_add, Nat.cast_one]; linarith)⟩
    · by_cases hidx0 : idx ∈ zeros
      · have heq1 : μ₁.map (QueryTree.query idx next).eval = μ₁.map (next false).eval :=
          pmf_map_congr μ₁ fun x hx ↦ by
            have := (mem_filter.mp ((mem_support_unifFinset _ _ x).mp hx)).2.2 idx hidx0
            simp [this]
        have heq2 : μ₂.map (QueryTree.query idx next).eval = μ₂.map (next false).eval :=
          pmf_map_congr μ₂ fun x hx ↦ by
            have := (mem_filter.mp ((mem_support_unifFinset _ _ x).mp hx)).2.2 idx hidx0
            simp [this]
        rw [heq1, heq2]
        obtain ⟨hs, hkl⟩ := queryTree_condSlice_kl_le hk₁ hk₂ hB0 hbound r (next false) (hT false)
          ones zeros hdisj (by omega) h1a h0a h1b h0b
        exact ⟨hs, hkl.trans (by rw [Nat.cast_add, Nat.cast_one]; linarith)⟩
      · obtain ⟨hp1a, hl1a, hp2a, hl2a, hbin⟩ :=
          hbound (#ones + #zeros) #ones (by omega) (by omega)
        obtain ⟨hbt1, hsp1⟩ := condSlice_split_coord hk₁ hdisj h1a h0a hidx1 hidx0 hp1a hl1a
        obtain ⟨hbt2, hsp2⟩ := condSlice_split_coord hk₂ hdisj h1b h0b hidx1 hidx0 hp2a hl2a
        let bern₁ := μ₁.map (fun x ↦ x idx)
        let bern₂ := μ₂.map (fun x ↦ x idx)
        have hd_t : Disjoint (insert idx ones) zeros := disjoint_insert_left.mpr ⟨hidx0, hdisj⟩
        have hd_f : Disjoint ones (insert idx zeros) := disjoint_insert_right.mpr ⟨hidx1, hdisj⟩
        have h1a_t : #(insert idx ones) ≤ k₁ := by rw [card_insert_of_notMem hidx1]; omega
        have h1b_t : #(insert idx ones) ≤ k₂ := by rw [card_insert_of_notMem hidx1]; omega
        have h0a_f : #(insert idx zeros) ≤ m - k₁ := by rw [card_insert_of_notMem hidx0]; omega
        have h0b_f : #(insert idx zeros) ≤ m - k₂ := by rw [card_insert_of_notMem hidx0]; omega
        let f₁ : Bool → PMF γ := fun b ↦
          if b then (Cslib.Probability.PMF.uniformOfFinset (condSlice m k₁ (insert idx ones) zeros)
              (condSlice_nonempty hk₁ hd_t h1a_t h0a)).map (next true).eval
          else (Cslib.Probability.PMF.uniformOfFinset (condSlice m k₁ ones (insert idx zeros))
              (condSlice_nonempty hk₁ hd_f h1a h0a_f)).map (next false).eval
        let f₂ : Bool → PMF γ := fun b ↦
          if b then (Cslib.Probability.PMF.uniformOfFinset (condSlice m k₂ (insert idx ones) zeros)
              (condSlice_nonempty hk₂ hd_t h1b_t h0b)).map (next true).eval
          else (Cslib.Probability.PMF.uniformOfFinset (condSlice m k₂ ones (insert idx zeros))
              (condSlice_nonempty hk₂ hd_f h1b h0b_f)).map (next false).eval
        have hbind1 : μ₁.map (QueryTree.query idx next).eval = bern₁.bind f₁ := by
          change (Cslib.Probability.PMF.uniformOfFinset (condSlice m k₁ ones zeros)
            (condSlice_nonempty hk₁ hdisj h1a h0a)).map (QueryTree.query idx next).eval = _
          rw [hsp1, PMF.map_bind]
          congr 1; funext b
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte, f₁]
            refine pmf_map_congr _ fun x hx ↦ ?_
            have := (mem_filter.mp ((mem_support_unifFinset _ _ x).mp hx)).2.2 idx
              (mem_insert_self idx zeros)
            simp [this]
          · simp only [↓reduceIte, f₁]
            refine pmf_map_congr _ fun x hx ↦ ?_
            have := (mem_filter.mp ((mem_support_unifFinset _ _ x).mp hx)).2.1 idx
              (mem_insert_self idx ones)
            simp [this]
        have hbind2 : μ₂.map (QueryTree.query idx next).eval = bern₂.bind f₂ := by
          change (Cslib.Probability.PMF.uniformOfFinset (condSlice m k₂ ones zeros)
            (condSlice_nonempty hk₂ hdisj h1b h0b)).map (QueryTree.query idx next).eval = _
          rw [hsp2, PMF.map_bind]
          congr 1; funext b
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte, f₂]
            refine pmf_map_congr _ fun x hx ↦ ?_
            have := (mem_filter.mp ((mem_support_unifFinset _ _ x).mp hx)).2.2 idx
              (mem_insert_self idx zeros)
            simp [this]
          · simp only [↓reduceIte, f₂]
            refine pmf_map_congr _ fun x hx ↦ ?_
            have := (mem_filter.mp ((mem_support_unifFinset _ _ x).mp hx)).2.1 idx
              (mem_insert_self idx ones)
            simp [this]
        have hq2_pos : 0 < (bern₂ true).toReal := by
          rw [hbt2]; exact div_pos (Nat.cast_pos.mpr hp2a) (Nat.cast_pos.mpr (by omega))
        have hq2_lt1 : (bern₂ true).toReal < 1 := by
          rw [hbt2, div_lt_one (Nat.cast_pos.mpr (by omega))]; exact_mod_cast hl2a
        have hbern_supp : bern₁.support ⊆ bern₂.support := by
          intro b _
          rw [PMF.mem_support_iff]
          cases b
          · have hsum := sum_toReal_eq_one bern₂
            simp only [Fintype.sum_bool] at hsum
            have hf_pos : 0 < (bern₂ false).toReal := by linarith
            intro h0; simp [h0] at hf_pos
          · intro h0; simp [h0] at hq2_pos
        obtain ⟨hs_t, hkl_t⟩ := queryTree_condSlice_kl_le hk₁ hk₂ hB0 hbound r (next true) (hT true)
          (insert idx ones) zeros hd_t (by rw [card_insert_of_notMem hidx1]; omega)
          h1a_t h0a h1b_t h0b
        obtain ⟨hs_f, hkl_f⟩ := queryTree_condSlice_kl_le hk₁ hk₂ hB0 hbound r (next false)
          (hT false) ones (insert idx zeros) hd_f (by rw [card_insert_of_notMem hidx0]; omega)
          h1a h0a_f h1b h0b_f
        have hf_supp : ∀ b : Bool, (f₁ b).support ⊆ (f₂ b).support := fun b ↦ by
          cases b <;> [exact hs_f; exact hs_t]
        have hf_kl : ∀ b : Bool, pmfKL (f₁ b) (f₂ b) ≤ (r : ℝ) * B := fun b ↦ by
          cases b <;> [exact hkl_f; exact hkl_t]
        rw [hbind1, hbind2]
        refine ⟨fun c hc ↦ ?_, ?_⟩
        · rw [PMF.mem_support_bind_iff] at hc ⊢
          obtain ⟨b, hb, hc'⟩ := hc
          exact ⟨b, hbern_supp hb, hf_supp b hc'⟩
        · calc
            pmfKL (bern₁.bind f₁) (bern₂.bind f₂)
              ≤ pmfKL bern₁ bern₂ + ∑ b : Bool, (bern₁ b).toReal * pmfKL (f₁ b) (f₂ b) :=
                pmfKL_bind_le hbern_supp (fun b _ ↦ hf_supp b)
            _ ≤ B + ∑ b : Bool, (bern₁ b).toReal * ((r : ℝ) * B) :=
                add_le_add (by rw [pmfKL_bool_eq_binaryKL, hbt1, hbt2]; exact hbin)
                  (sum_le_sum fun b _ ↦
                    mul_le_mul_of_nonneg_left (hf_kl b) ENNReal.toReal_nonneg)
            _ = B + (r : ℝ) * B := by rw [← sum_mul, sum_toReal_eq_one, one_mul]
            _ = ((r + 1 : ℕ) : ℝ) * B := by rw [Nat.cast_add, Nat.cast_one]; ring

/-- **Hypergeometric adaptive query-tree KL bound**: an adaptive decision tree `T` of depth at most
`q` distinguishing `uniformSlicePMF m k₁` from `uniformSlicePMF m k₂` incurs output KL divergence
at most `q * B` whenever all conditional hypergeometric step divergences are at most `B`. -/
theorem queryTree_uniformSlice_kl_le {γ : Type*} [Fintype γ] {m k₁ k₂ q : ℕ}
    (hk₁ : k₁ ≤ m) (hk₂ : k₂ ≤ m) {B : ℝ} (hB0 : 0 ≤ B)
    (T : QueryTree (Fin m) Bool γ) (hT : T.HasDepthAtMost q)
    (hbound : ∀ t s : ℕ, t < q → s ≤ t →
      0 < k₁ - s ∧ k₁ - s < m - t ∧ 0 < k₂ - s ∧ k₂ - s < m - t ∧
      binaryKL (((k₁ - s : ℕ) : ℝ) / ((m - t : ℕ) : ℝ))
        (((k₂ - s : ℕ) : ℝ) / ((m - t : ℕ) : ℝ)) ≤ B) :
    ((uniformSlicePMF m k₁ hk₁).map T.eval).support ⊆
        ((uniformSlicePMF m k₂ hk₂).map T.eval).support ∧
      pmfKL ((uniformSlicePMF m k₁ hk₁).map T.eval) ((uniformSlicePMF m k₂ hk₂).map T.eval) ≤
        (q : ℝ) * B := by
  have h1 : Cslib.Probability.PMF.uniformOfFinset (condSlice m k₁ ∅ ∅)
      (condSlice_nonempty hk₁ (disjoint_empty_left ∅) (by simp) (by simp)) =
      uniformSlicePMF m k₁ hk₁ := by
    ext x
    simp [uniformSlicePMF, Cslib.Probability.PMF.uniformOfFinset_apply, condSlice]
  have h2 : Cslib.Probability.PMF.uniformOfFinset (condSlice m k₂ ∅ ∅)
      (condSlice_nonempty hk₂ (disjoint_empty_left ∅) (by simp) (by simp)) =
      uniformSlicePMF m k₂ hk₂ := by
    ext x
    simp [uniformSlicePMF, Cslib.Probability.PMF.uniformOfFinset_apply, condSlice]
  have h := queryTree_condSlice_kl_le hk₁ hk₂ hB0 hbound q T hT ∅ ∅ (disjoint_empty_left ∅)
    (by simp) (by simp) (by simp) (by simp) (by simp)
  dsimp only at h
  rwa [h1, h2] at h

/-- **Hypergeometric adaptive query-tree Pinsker bound** for any randomized mixture `ν : PMF τ` of
deterministic decision trees of depth at most `q`. -/
theorem queryTree_uniformSlice_pinsker {τ γ : Type*} [Finite γ] {m k₁ k₂ q : ℕ}
    (hk₁ : k₁ ≤ m) (hk₂ : k₂ ≤ m) {B : ℝ} (hB0 : 0 ≤ B)
    (ν : PMF τ) (T : τ → QueryTree (Fin m) Bool γ) (hT : ∀ r ∈ ν.support, (T r).HasDepthAtMost q)
    (E : Set γ)
    (hbound : ∀ t s : ℕ, t < q → s ≤ t →
      0 < k₁ - s ∧ k₁ - s < m - t ∧ 0 < k₂ - s ∧ k₂ - s < m - t ∧
      binaryKL (((k₁ - s : ℕ) : ℝ) / ((m - t : ℕ) : ℝ))
        (((k₂ - s : ℕ) : ℝ) / ((m - t : ℕ) : ℝ)) ≤ B) :
    2 * (((ν.bind fun r ↦ (uniformSlicePMF m k₁ hk₁).map (T r).eval).toOuterMeasure E).toReal -
         ((ν.bind fun r ↦ (uniformSlicePMF m k₂ hk₂).map (T r).eval).toOuterMeasure E).toReal)
          ^ 2 ≤ (q : ℝ) * B := by
  cases nonempty_fintype γ
  set c : ℝ := Real.sqrt ((q : ℝ) * B / 2)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have htree : ∀ r ∈ ν.support,
      |(((uniformSlicePMF m k₁ hk₁).map (T r).eval).toOuterMeasure E).toReal -
        (((uniformSlicePMF m k₂ hk₂).map (T r).eval).toOuterMeasure E).toReal| ≤ c := by
    intro r hr
    obtain ⟨hsupp, hkl⟩ := queryTree_uniformSlice_kl_le hk₁ hk₂ hB0 (T r) (hT r hr) hbound
    have htv := abs_toOuterMeasure_sub_le_pmfTV
      ((uniformSlicePMF m k₁ hk₁).map (T r).eval)
      ((uniformSlicePMF m k₂ hk₂).map (T r).eval) E
    have hpin := two_mul_pmfTV_sq_le_pmfKL hsupp
    exact htv.trans (Real.le_sqrt_of_sq_le (by linarith))
  let M₁ := ν.bind fun r ↦ (uniformSlicePMF m k₁ hk₁).map (T r).eval
  let M₂ := ν.bind fun r ↦ (uniformSlicePMF m k₂ hk₂).map (T r).eval
  have hle_dir : ∀ (P Q : τ → PMF γ),
      (∀ r ∈ ν.support, ((P r).toOuterMeasure E).toReal ≤ ((Q r).toOuterMeasure E).toReal + c) →
      ((ν.bind P).toOuterMeasure E).toReal ≤ ((ν.bind Q).toOuterMeasure E).toReal + c := by
    intro P Q hPQ
    have hts : (ν.bind P).toOuterMeasure E ≤ (ν.bind Q).toOuterMeasure E + ENNReal.ofReal c := by
      rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
      have hc_tsum : ENNReal.ofReal c = ∑' r : τ, ν r * ENNReal.ofReal c := by
        rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
      rw [hc_tsum, ← tsum_add]
      refine CompleteLattice.summable.tsum_le_tsum (fun r ↦ ?_) CompleteLattice.summable
      by_cases hr : r ∈ ν.support
      · rw [← mul_add]
        refine mul_le_mul_right ?_ (ν r)
        rw [← ENNReal.ofReal_toReal (outerMeasure_ne_top (P r) E),
          ← ENNReal.ofReal_toReal (outerMeasure_ne_top (Q r) E),
          ← ENNReal.ofReal_add ENNReal.toReal_nonneg hc0]
        exact ENNReal.ofReal_le_ofReal (hPQ r hr)
      · have h0 : ν r = 0 := by simpa [PMF.mem_support_iff] using hr
        simp [h0]
    have hntP := outerMeasure_ne_top (ν.bind P) E
    have hntQ := outerMeasure_ne_top (ν.bind Q) E
    have hr := (ENNReal.toReal_le_toReal hntP
      (ENNReal.add_ne_top.mpr ⟨hntQ, ENNReal.ofReal_ne_top⟩)).mpr hts
    rwa [ENNReal.toReal_add hntQ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc0] at hr
  have habs : |(M₁.toOuterMeasure E).toReal - (M₂.toOuterMeasure E).toReal| ≤ c := by
    have h1 := hle_dir (fun r ↦ (uniformSlicePMF m k₁ hk₁).map (T r).eval)
      (fun r ↦ (uniformSlicePMF m k₂ hk₂).map (T r).eval)
      (fun r hr ↦ by linarith [(abs_le.mp (htree r hr)).2])
    have h2 := hle_dir (fun r ↦ (uniformSlicePMF m k₂ hk₂).map (T r).eval)
      (fun r ↦ (uniformSlicePMF m k₁ hk₁).map (T r).eval)
      (fun r hr ↦ by linarith [(abs_le.mp (htree r hr)).1])
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsq : ((M₁.toOuterMeasure E).toReal - (M₂.toOuterMeasure E).toReal) ^ 2 ≤
      (q : ℝ) * B / 2 := by
    rw [← sq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) habs 2).trans (le_of_eq (Real.sq_sqrt (by positivity)))
  linarith

end CslibFrontier.Probability
