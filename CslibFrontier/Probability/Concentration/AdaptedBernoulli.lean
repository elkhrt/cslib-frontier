/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Cslib.Probability.PMF
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Adapted Bernoulli Concentration and Sparse `t`-Independent Distributions

This module establishes exponential concentration bounds for adapted sequential Bernoulli processes
on discrete `PMF`s, together with Chebyshev concentration and Carathéodory sparsity for
`t`-independent distributions over finite function spaces, all under standard Lean axioms.

## Main definitions

* `CslibFrontier.Probability.seqRun`: distribution of length-`q` trajectories of an adapted `PMF`
  step
  kernel.
* `CslibFrontier.Probability.flagCount`: count of coordinates in a trajectory satisfying a Boolean
  flag.
* `CslibFrontier.Probability.IsTIndependentPMF`: `t`-independence of a `PMF` over `α → β`.

## Main results

* `CslibFrontier.Probability.bernstein_log_lower_bound` and
  `CslibFrontier.Probability.chernoff_log_lower_bound`: logarithmic lower bounds for Bernstein's and
  Chernoff's inequalities.
* `CslibFrontier.Probability.seqRun_flagCount_ge_le` and
  `CslibFrontier.Probability.seqRun_flagCount_gt_le`: Bernstein upper-tail inequality for adapted
  sequential Bernoulli processes.
* `CslibFrontier.Probability.seqRun_flagCount_le_le`: multiplicative Chernoff lower-tail
  inequality for
  adapted sequential Bernoulli processes.
* `CslibFrontier.Probability.IsTIndependentPMF.empirical_mean_chebyshev` and
  `CslibFrontier.Probability.IsTIndependentPMF.empirical_mean_chebyshev_gt`: Chebyshev tail bound
  for
  empirical means under `1`- and `2`-independence.
* `CslibFrontier.Probability.exists_isTIndependentPMF_card_le` and
  `CslibFrontier.Probability.exists_pairwiseIndependentPMF_card_le`: existence of sparse
  `t`-independent
  and pairwise-independent distributions via Carathéodory's convexity theorem.

## Tags

concentration inequalities, Bernstein inequality, Chernoff bound, pairwise independence,
Carathéodory theorem
-/

public section

namespace CslibFrontier.Probability

open Finset
open scoped ENNReal

/-! ### Finite `PMF` expectation helpers -/

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
    intro a _
    by_cases ha : a ∈ S <;> simp [ha, μ.apply_ne_top a]
  rw [ENNReal.toReal_sum hne]
  refine sum_congr rfl fun a _ ↦ ?_
  by_cases ha : a ∈ S <;> simp [ha]

private lemma outerMeasure_le_one (μ : PMF α) (S : Set α) :
    μ.toOuterMeasure S ≤ 1 := by
  calc
    μ.toOuterMeasure S ≤ μ.toOuterMeasure Set.univ := μ.toOuterMeasure.mono (Set.subset_univ S)
    _ = 1 := by simp [PMF.toOuterMeasure_apply, μ.tsum_coe]

private lemma outerMeasure_toReal_le_one (μ : PMF α) (S : Set α) :
    (μ.toOuterMeasure S).toReal ≤ 1 := by
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top (outerMeasure_le_one μ S))
    ENNReal.one_ne_top).mpr (outerMeasure_le_one μ S)

private lemma outerMeasure_toReal_mono (μ : PMF α) {S T : Set α} (hST : S ⊆ T) :
    (μ.toOuterMeasure S).toReal ≤ (μ.toOuterMeasure T).toReal :=
  (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top (outerMeasure_le_one μ S))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (outerMeasure_le_one μ T))).mpr
    (μ.toOuterMeasure.mono hST)

private lemma map_sum_toReal [Fintype α] [Fintype β] (μ : PMF α) (f : α → β) (g : β → ℝ) :
    ∑ b : β, ((μ.map f) b).toReal * g b = ∑ a : α, (μ a).toReal * g (f a) := by
  classical
  have hmap : ∀ b : β, ((μ.map f) b).toReal =
      ∑ a ∈ univ.filter (fun a ↦ f a = b), (μ a).toReal := by
    intro b
    rw [PMF.map_apply, tsum_fintype]
    have hne : ∀ a ∈ (univ : Finset α), (if b = f a then μ a else 0) ≠ ⊤ := by
      intro a _; split_ifs <;> simp [μ.apply_ne_top a]
    rw [ENNReal.toReal_sum hne, sum_filter]
    refine sum_congr rfl fun a _ ↦ ?_
    by_cases h : f a = b
    · simp [h]
    · have h' : b ≠ f a := fun h'' ↦ h h''.symm
      simp [h, h']
  simp_rw [hmap, sum_mul]
  rw [← sum_fiberwise_of_maps_to (g := f) (fun a _ ↦ mem_univ (f a))
    (fun a ↦ (μ a).toReal * g (f a))]
  refine sum_congr rfl fun b _ ↦ sum_congr rfl fun a ha ↦ ?_
  rw [(mem_filter.mp ha).2]

private lemma bind_apply_toReal [Fintype α] (μ : PMF α) (κ : α → PMF β) (b : β) :
    ((μ.bind κ) b).toReal = ∑ a : α, (μ a).toReal * (κ a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype]
  have hne : ∀ a ∈ (univ : Finset α), μ a * κ a b ≠ ⊤ := fun a _ ↦
    ENNReal.mul_ne_top (μ.apply_ne_top a) ((κ a).apply_ne_top b)
  rw [ENNReal.toReal_sum hne]
  exact sum_congr rfl fun a _ ↦ ENNReal.toReal_mul

private lemma bind_sum_toReal [Fintype α] [Fintype β] (μ : PMF α) (κ : α → PMF β) (g : β → ℝ) :
    ∑ b : β, ((μ.bind κ) b).toReal * g b =
      ∑ a : α, (μ a).toReal * ∑ b : β, (κ a b).toReal * g b := by
  simp_rw [bind_apply_toReal, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [mul_sum]
  exact sum_congr rfl fun b _ ↦ by ring

private lemma markov_toReal [Fintype α] (μ : PMF α) {g : α → ℝ}
    (hg : ∀ a ∈ μ.support, 0 ≤ g a) {c : ℝ} (hc : 0 < c) :
    (μ.toOuterMeasure {a | c ≤ g a}).toReal ≤ (∑ a : α, (μ a).toReal * g a) / c := by
  classical
  rw [le_div_iff₀ hc, outerMeasure_toReal_eq_sum, sum_mul]
  refine sum_le_sum fun a _ ↦ ?_
  by_cases hsupp : a ∈ μ.support
  · have hμ : 0 ≤ (μ a).toReal := ENNReal.toReal_nonneg
    by_cases ha : c ≤ g a
    · simp only [Set.mem_ofPred_eq, ha, ↓reduceIte, mul_one]
      exact mul_le_mul_of_nonneg_left ha hμ
    · simp only [Set.mem_ofPred_eq, ha, ↓reduceIte, mul_zero, zero_mul]
      exact mul_nonneg hμ (hg a hsupp)
  · have h0 : μ a = 0 := by simpa [PMF.mem_support_iff] using hsupp
    simp [h0]

end Helpers

/-! ### Logarithmic lower bounds for Bernstein and Chernoff inequalities -/

/-- The Bernstein--Bennett logarithmic inequality: for every `x ≥ 0`,
`x ^ 2 / (2 * (1 + x / 3)) ≤ (1 + x) * log (1 + x) - x`. -/
theorem bernstein_log_lower_bound {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / (2 * (1 + x / 3)) ≤ (1 + x) * Real.log (1 + x) - x := by
  let f : ℝ → ℝ := fun t ↦ (1 + t) * Real.log (1 + t) - t - t ^ 2 / (2 * (1 + t / 3))
  let g : ℝ → ℝ := fun t ↦ Real.log (1 + t) - (t + t ^ 2 / 6) / (1 + t / 3) ^ 2
  have hderiv_f : ∀ t ≥ (0 : ℝ), HasDerivAt f (g t) t := by
    intro t ht
    have h1 : 0 < 1 + t := by linarith
    have h3 : 2 * (1 + t / 3) ≠ 0 := by linarith
    have hd1 : HasDerivAt (fun u : ℝ ↦ 1 + u) 1 t := (hasDerivAt_id' t).const_add 1
    have hdlog : HasDerivAt (fun u : ℝ ↦ Real.log (1 + u)) ((1 + t)⁻¹) t := by
      convert hd1.log h1.ne' using 1
      ring
    have hdprod : HasDerivAt (fun u : ℝ ↦ (1 + u) * Real.log (1 + u))
        (Real.log (1 + t) + 1) t := by
      convert hd1.mul hdlog using 1
      have hne : 1 + t ≠ 0 := h1.ne'
      field_simp
    have hdnum : HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * t) t := by
      convert hasDerivAt_pow 2 t using 1
      ring
    have hdden : HasDerivAt (fun u : ℝ ↦ 2 * (1 + u / 3)) (2 / 3) t := by
      convert (((hasDerivAt_id' t).div_const (3 : ℝ)).const_add 1).const_mul (2 : ℝ) using 1
      ring
    convert (hdprod.sub (hasDerivAt_id' t)).sub (hdnum.div hdden h3) using 1
    dsimp only [g]
    have h3' : 1 + t / 3 ≠ 0 := by linarith
    field_simp
    ring
  have hderiv_g : ∀ t ≥ (0 : ℝ),
      HasDerivAt g ((t ^ 2 / 3 + t ^ 3 / 27) / ((1 + t) * (1 + t / 3) ^ 3)) t := by
    intro t ht
    have h1 : 0 < 1 + t := by linarith
    have h3 : 1 + t / 3 ≠ 0 := by linarith
    have hdlog : HasDerivAt (fun u : ℝ ↦ Real.log (1 + u)) ((1 + t)⁻¹) t := by
      convert ((hasDerivAt_id' t).const_add 1).log h1.ne' using 1
      ring
    have hdnum : HasDerivAt (fun u : ℝ ↦ u + u ^ 2 / 6) (1 + t / 3) t := by
      convert (hasDerivAt_id' t).add ((hasDerivAt_pow 2 t).div_const 6) using 1
      ring
    have hdden : HasDerivAt (fun u : ℝ ↦ (1 + u / 3) ^ 2) (2 * (1 + t / 3) / 3) t := by
      convert (((hasDerivAt_id' t).div_const 3).const_add 1).pow 2 using 1
      ring
    convert hdlog.sub (hdnum.div hdden (pow_ne_zero 2 h3)) using 1
    have h1' : 1 + t ≠ 0 := h1.ne'
    field_simp
    ring
  have hg_mono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t ↦ (t ^ 2 / 3 + t ^ 3 / 27) / ((1 + t) * (1 + t / 3) ^ 3))
      (convex_Ici 0) ?_ ?_ ?_
    · exact fun t ht ↦ (hderiv_g t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := le_of_lt (by simpa using ht)
      exact (hderiv_g t ht0).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := le_of_lt (by simpa using ht)
      positivity
  have hg_nonneg : ∀ t ≥ (0 : ℝ), 0 ≤ g t := by
    intro t ht
    have hg0 : g 0 = 0 := by simp [g]
    rw [← hg0]
    exact hg_mono (Set.mem_Ici.mpr le_rfl) ht ht
  have hf_mono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := g) (convex_Ici 0) ?_ ?_ ?_
    · exact fun t ht ↦ (hderiv_f t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hderiv_f t (le_of_lt (by simpa using ht))).hasDerivWithinAt
    · intro t ht
      exact hg_nonneg t (le_of_lt (by simpa using ht))
  have hf0 : f 0 = 0 := by simp [f]
  have hfx : 0 ≤ f x := by
    rw [← hf0]
    exact hf_mono (Set.mem_Ici.mpr le_rfl) hx hx
  dsimp only [f] at hfx
  linarith

/-- The multiplicative Chernoff lower-tail logarithmic inequality: for every `x ∈ [0, 1)`,
`x ^ 2 / 2 ≤ (1 - x) * log (1 - x) + x`. -/
theorem chernoff_log_lower_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x ^ 2 / 2 ≤ (1 - x) * Real.log (1 - x) + x := by
  let f : ℝ → ℝ := fun t ↦ (1 - t) * Real.log (1 - t) + t - t ^ 2 / 2
  let g : ℝ → ℝ := fun t ↦ -Real.log (1 - t) - t
  have hderiv_f : ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivAt f (g t) t := by
    intro t ht
    have h1 : 0 < 1 - t := by linarith [ht.2]
    have hd1 : HasDerivAt (fun u : ℝ ↦ 1 - u) (-1) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id' t) using 1
      ring
    have hdlog : HasDerivAt (fun u : ℝ ↦ Real.log (1 - u)) ((-1) / (1 - t)) t :=
      hd1.log h1.ne'
    have hdprod : HasDerivAt (fun u : ℝ ↦ (1 - u) * Real.log (1 - u))
        (-Real.log (1 - t) - 1) t := by
      convert hd1.mul hdlog using 1
      have hne : 1 - t ≠ 0 := h1.ne'
      field_simp
      ring
    have hdsq : HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2) t t := by
      convert (hasDerivAt_pow 2 t).div_const 2 using 1
      ring
    convert (hdprod.add (hasDerivAt_id' t)).sub hdsq using 1
    dsimp only [g]
    ring
  have hderiv_g : ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivAt g (t / (1 - t)) t := by
    intro t ht
    have h1 : 0 < 1 - t := by linarith [ht.2]
    have hd1 : HasDerivAt (fun u : ℝ ↦ 1 - u) (-1) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id' t) using 1
      ring
    have hdlog : HasDerivAt (fun u : ℝ ↦ -Real.log (1 - u)) (1 / (1 - t)) t := by
      convert (hd1.log h1.ne').neg using 1
      ring
    convert hdlog.sub (hasDerivAt_id' t) using 1
    have hne : 1 - t ≠ 0 := h1.ne'
    field_simp
    ring
  have hg_mono : MonotoneOn g (Set.Ico 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t ↦ t / (1 - t))
      (convex_Ico 0 1) ?_ ?_ ?_
    · exact fun t ht ↦ (hderiv_g t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ico] using ht
      exact (hderiv_g t ⟨ht'.1.le, ht'.2⟩).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ico] using ht
      exact div_nonneg ht'.1.le (by linarith [ht'.2])
  have hg_nonneg : ∀ t ∈ Set.Ico (0 : ℝ) 1, 0 ≤ g t := by
    intro t ht
    have hg0 : g 0 = 0 := by simp [g]
    rw [← hg0]
    exact hg_mono ⟨le_rfl, zero_lt_one⟩ ht ht.1
  have hf_mono : MonotoneOn f (Set.Ico 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := g) (convex_Ico 0 1) ?_ ?_ ?_
    · exact fun t ht ↦ (hderiv_f t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ico] using ht
      exact (hderiv_f t ⟨ht'.1.le, ht'.2⟩).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ico] using ht
      exact hg_nonneg t ⟨ht'.1.le, ht'.2⟩
  have hf0 : f 0 = 0 := by simp [f]
  have hfx : 0 ≤ f x := by
    rw [← hf0]
    exact hf_mono ⟨le_rfl, zero_lt_one⟩ ⟨hx0, hx1⟩ hx0
  dsimp only [f] at hfx
  linarith

/-! ### Adapted sequential Bernoulli concentration (Bernstein and Chernoff) -/

/-- Distribution of length-`q` trajectories generated by an adapted `PMF` step kernel `step`,
where at step `t` the law of the next outcome may depend arbitrarily on the prefix `Fin t → α`. -/
noncomputable def seqRun {α : Type*} (step : ∀ t : ℕ, (Fin t → α) → PMF α) :
    ∀ q : ℕ, PMF (Fin q → α)
  | 0 => PMF.pure Fin.elim0
  | q + 1 => (seqRun step q).bind fun h ↦ (step q h).map (Fin.snoc h)

/-- Base equation for `seqRun` at `0` steps. -/
@[simp]
theorem seqRun_zero {α : Type*} (step : ∀ t : ℕ, (Fin t → α) → PMF α) :
    seqRun step 0 = PMF.pure Fin.elim0 := by
  unfold seqRun; rfl

/-- Step equation for `seqRun` at `q + 1` steps. -/
@[simp]
theorem seqRun_succ {α : Type*} (step : ∀ t : ℕ, (Fin t → α) → PMF α) (q : ℕ) :
    seqRun step (q + 1) = (seqRun step q).bind fun h ↦ (step q h).map (Fin.snoc h) := by
  rw [seqRun]

/-- Number of coordinates in a length-`q` trajectory `h : Fin q → α` where `flag` holds. -/
def flagCount {α : Type*} (flag : α → Bool) {q : ℕ} (h : Fin q → α) : ℕ :=
  #(univ.filter fun t : Fin q ↦ flag (h t) = true)

@[simp]
theorem flagCount_zero {α : Type*} (flag : α → Bool) (h : Fin 0 → α) :
    flagCount flag h = 0 := by
  simp [flagCount]

/-- Appending `a` increments `flagCount` by `1` when `flag a = true` and by `0` otherwise. -/
@[simp]
theorem flagCount_snoc {α : Type*} (flag : α → Bool) {q : ℕ} (h : Fin q → α) (a : α) :
    flagCount flag (Fin.snoc h a) = flagCount flag h + if flag a = true then 1 else 0 := by
  unfold flagCount
  have hsum : ∀ {n : ℕ} (w : Fin n → α),
      #(univ.filter fun t : Fin n ↦ flag (w t) = true) =
        ∑ t : Fin n, if flag (w t) = true then 1 else 0 := fun w ↦ by simp [sum_boole]
  rw [hsum, hsum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

private lemma step_exp_factor {α : Type*} [Fintype α] (μ : PMF α) (flag : α → Bool)
    (base c : ℝ) :
    ∑ a : α, (μ a).toReal * Real.exp (c * ((base + if flag a = true then (1 : ℝ) else 0))) =
      Real.exp (c * base) *
        (1 + (μ.toOuterMeasure {a | flag a = true}).toReal * (Real.exp c - 1)) := by
  classical
  have hpr := outerMeasure_toReal_eq_sum μ {a | flag a = true}
  have htot := sum_toReal_eq_one μ
  have hlhs : ∑ a : α, (μ a).toReal *
        Real.exp (c * (base + if flag a = true then (1 : ℝ) else 0)) =
      Real.exp (c * base) *
        ∑ a : α, ((μ a).toReal +
          ((μ a).toReal * if a ∈ {a | flag a = true} then (1 : ℝ) else 0) *
            (Real.exp c - 1)) := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    by_cases hfa : flag a = true
    · rw [ite_eq_left_iff.mpr fun hn ↦ absurd hfa hn,
        ite_eq_left_iff.mpr fun hn : a ∉ {a | flag a = true} ↦ False.elim (hn hfa),
        mul_add, mul_one, Real.exp_add]
      ring
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hfa,
        ite_eq_right_iff.mpr fun h : a ∈ {a | flag a = true} ↦ absurd h hfa,
        add_zero, mul_zero, zero_mul, add_zero, mul_comm]
  rw [hlhs, sum_add_distrib, ← sum_mul, htot, ← hpr]

private lemma seqRun_mgf_upper {α : Type*} [Fintype α]
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (flag : α → Bool) {p lam : ℝ} (hlam : 0 < lam) :
    ∀ q : ℕ,
      (∀ t, t < q → ∀ h ∈ (seqRun step t).support,
        ((step t h).toOuterMeasure {a | flag a = true}).toReal ≤ p) →
      ∑ h : Fin q → α, ((seqRun step q) h).toReal * Real.exp (lam * (flagCount flag h : ℝ)) ≤
        Real.exp ((q : ℝ) * p * (Real.exp lam - 1))
  | 0, _ => by
    simp only [seqRun_zero, flagCount_zero, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one,
      zero_mul]
    exact le_of_eq (sum_toReal_eq_one _)
  | q + 1, hp => by
    have ih := seqRun_mgf_upper step flag hlam q (fun t ht ↦ hp t (Nat.lt_succ_of_lt ht))
    rw [seqRun_succ, bind_sum_toReal]
    have hstep : ∀ h ∈ (seqRun step q).support,
        ∑ w : Fin (q + 1) → α,
          (((step q h).map (Fin.snoc h)) w).toReal * Real.exp (lam * (flagCount flag w : ℝ)) ≤
          Real.exp (lam * (flagCount flag h : ℝ)) * Real.exp (p * (Real.exp lam - 1)) := by
      intro h hh
      rw [map_sum_toReal]
      have hcast : ∀ a : α, (flagCount flag (Fin.snoc h a) : ℝ) =
          (flagCount flag h : ℝ) + if flag a = true then (1 : ℝ) else 0 := by
        intro a; rw [flagCount_snoc]; cases flag a <;> simp
      simp_rw [hcast]
      rw [step_exp_factor]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hexp_pos : 0 ≤ Real.exp lam - 1 := by linarith [Real.one_le_exp hlam.le]
      have h1 : 1 + ((step q h).toOuterMeasure {a | flag a = true}).toReal * (Real.exp lam - 1) ≤
          p * (Real.exp lam - 1) + 1 := by
        linarith [mul_le_mul_of_nonneg_right (hp q (Nat.lt_succ_self q) h hh) hexp_pos]
      exact h1.trans (Real.add_one_le_exp (p * (Real.exp lam - 1)))
    calc
      ∑ h : Fin q → α, ((seqRun step q) h).toReal *
          ∑ w : Fin (q + 1) → α,
            (((step q h).map (Fin.snoc h)) w).toReal * Real.exp (lam * (flagCount flag w : ℝ))
        ≤ ∑ h : Fin q → α, ((seqRun step q) h).toReal *
            (Real.exp (lam * (flagCount flag h : ℝ)) * Real.exp (p * (Real.exp lam - 1))) := by
          refine sum_le_sum fun h _ ↦ ?_
          by_cases hh : h ∈ (seqRun step q).support
          · exact mul_le_mul_of_nonneg_left (hstep h hh) ENNReal.toReal_nonneg
          · have h0 : seqRun step q h = 0 := by simpa [PMF.mem_support_iff] using hh
            simp [h0]
      _ = (∑ h : Fin q → α, ((seqRun step q) h).toReal * Real.exp (lam * (flagCount flag h : ℝ))) *
            Real.exp (p * (Real.exp lam - 1)) := by
          rw [sum_mul]; exact sum_congr rfl fun _ _ ↦ by ring
      _ ≤ Real.exp ((q : ℝ) * p * (Real.exp lam - 1)) * Real.exp (p * (Real.exp lam - 1)) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = Real.exp (((q + 1 : ℕ) : ℝ) * p * (Real.exp lam - 1)) := by
          rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]; congr 1; ring

/-- **Adapted Bernstein upper-tail inequality**: if each step `t < q` of an adapted process on a
finite outcome space raises `flag` with conditional probability at most `p ≥ 0`, then for every
`τ > 0`, `Pr[flagCount ≥ q (p + τ)] ≤ exp (-q τ ^ 2 / (2 (p + τ / 3)))`. -/
theorem seqRun_flagCount_ge_le {α : Type*} [Finite α]
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (flag : α → Bool) {q : ℕ} {p τ : ℝ}
    (hp0 : 0 ≤ p) (hτ : 0 < τ)
    (hstep : ∀ t, t < q → ∀ h ∈ (seqRun step t).support,
      ((step t h).toOuterMeasure {a | flag a = true}).toReal ≤ p) :
    ((seqRun step q).toOuterMeasure {h | (q : ℝ) * (p + τ) ≤ (flagCount flag h : ℝ)}).toReal ≤
      Real.exp (-((q : ℝ) * τ ^ 2) / (2 * (p + τ / 3))) := by
  cases nonempty_fintype α
  have hmgf_bound : ∀ lam : ℝ, 0 < lam →
      ((seqRun step q).toOuterMeasure {h | (q : ℝ) * (p + τ) ≤ (flagCount flag h : ℝ)}).toReal ≤
        Real.exp ((q : ℝ) * p * (Real.exp lam - 1) - lam * ((q : ℝ) * (p + τ))) := by
    intro lam hlam
    have hset : {h : Fin q → α | (q : ℝ) * (p + τ) ≤ (flagCount flag h : ℝ)} ⊆
        {h : Fin q → α |
          Real.exp (lam * ((q : ℝ) * (p + τ))) ≤ Real.exp (lam * (flagCount flag h : ℝ))} :=
      fun _ hh ↦ Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hh hlam.le)
    calc
      ((seqRun step q).toOuterMeasure {h | (q : ℝ) * (p + τ) ≤ (flagCount flag h : ℝ)}).toReal
        ≤ ((seqRun step q).toOuterMeasure
            {h | Real.exp (lam * ((q : ℝ) * (p + τ))) ≤
              Real.exp (lam * (flagCount flag h : ℝ))}).toReal :=
          outerMeasure_toReal_mono _ hset
      _ ≤ (∑ h : Fin q → α, ((seqRun step q) h).toReal *
            Real.exp (lam * (flagCount flag h : ℝ))) /
            Real.exp (lam * ((q : ℝ) * (p + τ))) :=
          markov_toReal _ (fun _ _ ↦ (Real.exp_pos _).le) (Real.exp_pos _)
      _ ≤ Real.exp ((q : ℝ) * p * (Real.exp lam - 1)) /
            Real.exp (lam * ((q : ℝ) * (p + τ))) :=
          div_le_div_of_nonneg_right (seqRun_mgf_upper step flag hlam q hstep) (Real.exp_pos _).le
      _ = Real.exp ((q : ℝ) * p * (Real.exp lam - 1) - lam * ((q : ℝ) * (p + τ))) :=
          (Real.exp_sub _ _).symm
  rcases eq_or_lt_of_le hp0 with rfl | hp_pos
  · refine (hmgf_bound (3 / 2) (by norm_num)).trans (le_of_eq ?_)
    congr 1
    have hτne : τ ≠ 0 := hτ.ne'
    field_simp
    ring
  · set x : ℝ := τ / p
    have hx_pos : 0 < x := div_pos hτ hp_pos
    let lam : ℝ := Real.log (1 + x)
    have hlam_pos : 0 < lam := Real.log_pos (by linarith)
    refine (hmgf_bound lam hlam_pos).trans (Real.exp_le_exp.mpr ?_)
    have hexp : Real.exp lam - 1 = x := by
      simp only [lam]
      rw [Real.exp_log (by linarith)]
      ring
    rw [hexp]
    have hmul : (q : ℝ) * p * (x ^ 2 / (2 * (1 + x / 3))) ≤
        (q : ℝ) * p * ((1 + x) * lam - x) :=
      mul_le_mul_of_nonneg_left (bernstein_log_lower_bound hx_pos.le) (by positivity)
    have hτx : p * x = τ := mul_div_cancel₀ τ hp_pos.ne'
    have hiden1 : (q : ℝ) * p * x - lam * ((q : ℝ) * (p + τ)) =
        -((q : ℝ) * p * ((1 + x) * lam - x)) := by
      rw [← hτx]; ring
    have hiden2 : -((q : ℝ) * p * (x ^ 2 / (2 * (1 + x / 3)))) =
        -((q : ℝ) * τ ^ 2) / (2 * (p + τ / 3)) := by
      have hpne : p ≠ 0 := hp_pos.ne'
      have hd1 : 2 * (1 + x / 3) ≠ 0 := by positivity
      have hd2 : 2 * (p + τ / 3) ≠ 0 := by positivity
      rw [← hτx]
      field_simp
    rw [hiden1, ← hiden2]
    linarith

/-- Strict-threshold variant of `seqRun_flagCount_ge_le`. -/
theorem seqRun_flagCount_gt_le {α : Type*} [Finite α]
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (flag : α → Bool) {q : ℕ} {p τ : ℝ}
    (hp0 : 0 ≤ p) (hτ : 0 < τ)
    (hstep : ∀ t, t < q → ∀ h ∈ (seqRun step t).support,
      ((step t h).toOuterMeasure {a | flag a = true}).toReal ≤ p) :
    ((seqRun step q).toOuterMeasure {h | (q : ℝ) * (p + τ) < (flagCount flag h : ℝ)}).toReal ≤
      Real.exp (-((q : ℝ) * τ ^ 2) / (2 * (p + τ / 3))) := by
  refine (outerMeasure_toReal_mono (seqRun step q) ?_).trans
    (seqRun_flagCount_ge_le step flag hp0 hτ hstep)
  intro x hx
  rw [Set.mem_ofPred_eq] at hx ⊢
  exact le_of_lt hx

private lemma seqRun_mgf_lower {α : Type*} [Fintype α]
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (flag : α → Bool) {p lam : ℝ} (hlam : 0 < lam) :
    ∀ q : ℕ,
      (∀ t, t < q → ∀ h ∈ (seqRun step t).support,
        p ≤ ((step t h).toOuterMeasure {a | flag a = true}).toReal) →
      ∑ h : Fin q → α, ((seqRun step q) h).toReal * Real.exp (-lam * (flagCount flag h : ℝ)) ≤
        Real.exp (-((q : ℝ) * p * (1 - Real.exp (-lam))))
  | 0, _ => by
    simp only [seqRun_zero, flagCount_zero, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one,
      zero_mul, neg_zero]
    exact le_of_eq (sum_toReal_eq_one _)
  | q + 1, hp => by
    have ih := seqRun_mgf_lower step flag hlam q (fun t ht ↦ hp t (Nat.lt_succ_of_lt ht))
    rw [seqRun_succ, bind_sum_toReal]
    have hstep : ∀ h ∈ (seqRun step q).support,
        ∑ w : Fin (q + 1) → α,
          (((step q h).map (Fin.snoc h)) w).toReal * Real.exp (-lam * (flagCount flag w : ℝ)) ≤
          Real.exp (-lam * (flagCount flag h : ℝ)) * Real.exp (-(p * (1 - Real.exp (-lam)))) := by
      intro h hh
      rw [map_sum_toReal]
      have hcast : ∀ a : α, (flagCount flag (Fin.snoc h a) : ℝ) =
          (flagCount flag h : ℝ) + if flag a = true then (1 : ℝ) else 0 := by
        intro a; rw [flagCount_snoc]; cases flag a <;> simp
      simp_rw [hcast]
      rw [step_exp_factor]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hexp_pos : 0 ≤ 1 - Real.exp (-lam) := by
        linarith [Real.exp_le_one_iff.mpr (show -lam ≤ 0 by linarith)]
      have h1 : 1 + ((step q h).toOuterMeasure {a | flag a = true}).toReal *
            (Real.exp (-lam) - 1) ≤ -(p * (1 - Real.exp (-lam))) + 1 := by
        have hmul := mul_le_mul_of_nonneg_right (hp q (Nat.lt_succ_self q) h hh) hexp_pos
        linarith
      exact h1.trans (Real.add_one_le_exp (-(p * (1 - Real.exp (-lam)))))
    calc
      ∑ h : Fin q → α, ((seqRun step q) h).toReal *
          ∑ w : Fin (q + 1) → α,
            (((step q h).map (Fin.snoc h)) w).toReal * Real.exp (-lam * (flagCount flag w : ℝ))
        ≤ ∑ h : Fin q → α, ((seqRun step q) h).toReal *
            (Real.exp (-lam * (flagCount flag h : ℝ)) *
              Real.exp (-(p * (1 - Real.exp (-lam))))) := by
          refine sum_le_sum fun h _ ↦ ?_
          by_cases hh : h ∈ (seqRun step q).support
          · exact mul_le_mul_of_nonneg_left (hstep h hh) ENNReal.toReal_nonneg
          · have h0 : seqRun step q h = 0 := by simpa [PMF.mem_support_iff] using hh
            simp [h0]
      _ = (∑ h : Fin q → α,
            ((seqRun step q) h).toReal * Real.exp (-lam * (flagCount flag h : ℝ))) *
            Real.exp (-(p * (1 - Real.exp (-lam)))) := by
          rw [sum_mul]; exact sum_congr rfl fun _ _ ↦ by ring
      _ ≤ Real.exp (-((q : ℝ) * p * (1 - Real.exp (-lam)))) *
            Real.exp (-(p * (1 - Real.exp (-lam)))) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = Real.exp (-(((q + 1 : ℕ) : ℝ) * p * (1 - Real.exp (-lam)))) := by
          rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]; congr 1; ring

/-- **Adapted multiplicative Chernoff lower-tail inequality**: if each step `t < q` of an adapted
process on a finite outcome space raises `flag` with conditional probability at least `p > 0`, then
for every `τ ∈ [0, p]`, `Pr[flagCount ≤ q (p - τ)] ≤ exp (-q τ ^ 2 / (2 p))`. -/
theorem seqRun_flagCount_le_le {α : Type*} [Finite α]
    (step : ∀ t : ℕ, (Fin t → α) → PMF α) (flag : α → Bool) {q : ℕ} {p τ : ℝ}
    (hp : 0 < p) (hτ0 : 0 ≤ τ) (hτp : τ ≤ p)
    (hstep : ∀ t, t < q → ∀ h ∈ (seqRun step t).support,
      p ≤ ((step t h).toOuterMeasure {a | flag a = true}).toReal) :
    ((seqRun step q).toOuterMeasure {h | (flagCount flag h : ℝ) ≤ (q : ℝ) * (p - τ)}).toReal ≤
      Real.exp (-((q : ℝ) * τ ^ 2) / (2 * p)) := by
  cases nonempty_fintype α
  have hmgf_bound : ∀ lam : ℝ, 0 < lam →
      ((seqRun step q).toOuterMeasure {h | (flagCount flag h : ℝ) ≤ (q : ℝ) * (p - τ)}).toReal ≤
        Real.exp (lam * ((q : ℝ) * (p - τ)) - (q : ℝ) * p * (1 - Real.exp (-lam))) := by
    intro lam hlam
    have hset : {h : Fin q → α | (flagCount flag h : ℝ) ≤ (q : ℝ) * (p - τ)} ⊆
        {h : Fin q → α |
          Real.exp (-lam * ((q : ℝ) * (p - τ))) ≤ Real.exp (-lam * (flagCount flag h : ℝ))} := by
      intro h (hh : (flagCount flag h : ℝ) ≤ (q : ℝ) * (p - τ))
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc
      ((seqRun step q).toOuterMeasure {h | (flagCount flag h : ℝ) ≤ (q : ℝ) * (p - τ)}).toReal
        ≤ ((seqRun step q).toOuterMeasure
            {h | Real.exp (-lam * ((q : ℝ) * (p - τ))) ≤
              Real.exp (-lam * (flagCount flag h : ℝ))}).toReal :=
          outerMeasure_toReal_mono _ hset
      _ ≤ (∑ h : Fin q → α, ((seqRun step q) h).toReal *
            Real.exp (-lam * (flagCount flag h : ℝ))) /
            Real.exp (-lam * ((q : ℝ) * (p - τ))) :=
          markov_toReal _ (fun _ _ ↦ (Real.exp_pos _).le) (Real.exp_pos _)
      _ ≤ Real.exp (-((q : ℝ) * p * (1 - Real.exp (-lam)))) /
            Real.exp (-lam * ((q : ℝ) * (p - τ))) :=
          div_le_div_of_nonneg_right (seqRun_mgf_lower step flag hlam q hstep) (Real.exp_pos _).le
      _ = Real.exp (lam * ((q : ℝ) * (p - τ)) - (q : ℝ) * p * (1 - Real.exp (-lam))) := by
          rw [← Real.exp_sub]; congr 1; ring
  rcases eq_or_lt_of_le hτ0 with rfl | hτ_pos
  · simpa using outerMeasure_toReal_le_one (seqRun step q) _
  · rcases eq_or_lt_of_le hτp with htp_eq | hτ_lt
    · subst htp_eq
      refine (hmgf_bound 1 zero_lt_one).trans (Real.exp_le_exp.mpr ?_)
      have he : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (by norm_num : (0 : ℝ) < 2) h2
      have hq : 0 ≤ (q : ℝ) * τ := by positivity
      have hhalf : -((q : ℝ) * τ ^ 2) / (2 * τ) = -((q : ℝ) * τ * (1 / 2)) := by
        have hne : τ ≠ 0 := hτ_pos.ne'
        field_simp
      rw [sub_self, mul_zero, mul_zero, zero_sub, hhalf]
      nlinarith
    · set x : ℝ := τ / p
      have hx0 : 0 < x := div_pos hτ_pos hp
      have hx1 : x < 1 := (div_lt_one hp).mpr hτ_lt
      let lam : ℝ := -Real.log (1 - x)
      have hlam_pos : 0 < lam := neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
      refine (hmgf_bound lam hlam_pos).trans (Real.exp_le_exp.mpr ?_)
      have hexp : 1 - Real.exp (-lam) = x := by
        simp only [lam, neg_neg]
        rw [Real.exp_log (by linarith)]
        ring
      rw [hexp]
      have hmul : (q : ℝ) * p * (x ^ 2 / 2) ≤ (q : ℝ) * p * ((1 - x) * Real.log (1 - x) + x) :=
        mul_le_mul_of_nonneg_left (chernoff_log_lower_bound hx0.le hx1) (by positivity)
      have hτx : p * x = τ := mul_div_cancel₀ τ hp.ne'
      have hiden1 : lam * ((q : ℝ) * (p - τ)) - (q : ℝ) * p * x =
          -((q : ℝ) * p * ((1 - x) * Real.log (1 - x) + x)) := by
        simp only [lam]; rw [← hτx]; ring
      have hiden2 : -((q : ℝ) * p * (x ^ 2 / 2)) = -((q : ℝ) * τ ^ 2) / (2 * p) := by
        have hpne : p ≠ 0 := hp.ne'
        rw [← hτx]; field_simp
      rw [hiden1, ← hiden2]
      linarith

/-! ### `t`-independent distributions, Chebyshev concentration, and Carathéodory sparsity -/

/-- A probability distribution `μ : PMF (α → β)` over functions into a finite type `β` is
`t`-independent if for every injective `t`-tuple `a : Fin t ↪ α` and every output tuple
`b : Fin t → β`, `Pr_{h ~ μ}[∀ r, h (a r) = b r] = (1 / |β|) ^ t`. -/
def IsTIndependentPMF {α β : Type*} [Fintype β] (t : ℕ) (μ : PMF (α → β)) : Prop :=
  ∀ (a : Fin t ↪ α) (b : Fin t → β),
    (μ.toOuterMeasure {h | ∀ r : Fin t, h (a r) = b r}).toReal =
      (1 / (Fintype.card β : ℝ)) ^ t

/-- Characterization of `IsTIndependentPMF`. -/
theorem isTIndependentPMF_iff {α β : Type*} [Fintype β] (t : ℕ) (μ : PMF (α → β)) :
    IsTIndependentPMF t μ ↔
      ∀ (a : Fin t ↪ α) (b : Fin t → β),
        (μ.toOuterMeasure {h | ∀ r : Fin t, h (a r) = b r}).toReal =
          (1 / (Fintype.card β : ℝ)) ^ t :=
  Iff.rfl

/-- Downward monotonicity of `t`-independence whenever `t ≤ |α|`. -/
theorem IsTIndependentPMF.mono {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    {t t' : ℕ} {μ : PMF (α → β)} (hμ : IsTIndependentPMF t μ) (hle : t' ≤ t)
    (ht : t ≤ Fintype.card α) :
    IsTIndependentPMF t' μ := by
  classical
  have hstep : ∀ k : ℕ, k + 1 ≤ Fintype.card α → IsTIndependentPMF (k + 1) μ →
      IsTIndependentPMF k μ := by
    intro k hk hsucc a b
    let used : Finset α := univ.image a
    have hcard_used : #used = k := by
      rw [card_image_of_injective _ a.injective, card_univ, Fintype.card_fin]
    have hex : (univ \ used).Nonempty := by
      rw [← card_pos, card_sdiff, inter_univ, card_univ, hcard_used]; omega
    obtain ⟨x₀, hx₀⟩ := hex
    have hx₀_not : ∀ r : Fin k, a r ≠ x₀ := fun r hr ↦ by simp [used, ← hr] at hx₀
    let a' : Fin (k + 1) ↪ α :=
      ⟨Fin.snoc (α := fun _ ↦ α) a x₀, by
        intro i j
        refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j' ↦ ?_) j <;>
          intro hij
        · rfl
        · rw [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact absurd hij.symm (hx₀_not j')
        · rw [Fin.snoc_castSucc, Fin.snoc_last] at hij
          exact absurd hij (hx₀_not i')
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hij
          exact congrArg Fin.castSucc (a.injective hij)⟩
    have ha'_apply : ∀ r : Fin (k + 1), a' r = Fin.snoc (α := fun _ ↦ α) a x₀ r := fun _ ↦ rfl
    have hsum : (μ.toOuterMeasure {h | ∀ r : Fin k, h (a r) = b r}).toReal =
        ∑ y : β, (μ.toOuterMeasure
          {h | ∀ r : Fin (k + 1), h (a' r) = Fin.snoc (α := fun _ ↦ β) b y r}).toReal := by
      simp_rw [outerMeasure_toReal_eq_sum]
      rw [sum_comm]
      refine sum_congr rfl fun h _ ↦ ?_
      rw [← mul_sum]
      congr 1
      by_cases hh : ∀ r : Fin k, h (a r) = b r
      · have hlhs : (if h ∈ {h : α → β | ∀ r : Fin k, h (a r) = b r} then (1 : ℝ) else 0) = 1 :=
          ite_eq_left_iff.mpr fun hn ↦ absurd hh hn
        rw [hlhs, sum_eq_single (h x₀)]
        · have hall : ∀ r : Fin (k + 1),
              h (a' r) = Fin.snoc (α := fun _ ↦ β) b (h x₀) r := fun r ↦ by
            rw [ha'_apply]
            exact Fin.lastCases (by simp) (fun r' ↦ by simp [hh r']) r
          exact (ite_eq_left_iff.mpr fun hn ↦ absurd hall hn).symm
        · intro y _ hy
          refine ite_eq_right_iff.mpr fun hall ↦ False.elim (hy ?_)
          have hlast := hall (Fin.last k)
          rw [ha'_apply, Fin.snoc_last, Fin.snoc_last] at hlast
          exact hlast.symm
        · intro hmem; exact absurd (mem_univ _) hmem
      · have hlhs : (if h ∈ {h : α → β | ∀ r : Fin k, h (a r) = b r} then (1 : ℝ) else 0) = 0 :=
          ite_eq_right_iff.mpr fun hc ↦ absurd hc hh
        rw [hlhs]
        refine (sum_eq_zero fun y _ ↦
          ite_eq_right_iff.mpr fun hall ↦ False.elim (hh fun r ↦ ?_)).symm
        have hcs := hall r.castSucc
        rwa [ha'_apply, Fin.snoc_castSucc, Fin.snoc_castSucc] at hcs
    rw [hsum]
    simp_rw [hsucc a']
    rw [sum_const, card_univ, nsmul_eq_mul, pow_succ]
    have hcard_ne : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hrec : ∀ m : ℕ, t' + m ≤ Fintype.card α → IsTIndependentPMF (t' + m) μ →
      IsTIndependentPMF t' μ := by
    intro m
    induction m with
    | zero => intro _ h; simpa using h
    | succ m ih => intro hm h; exact ih (by omega) (hstep (t' + m) hm h)
  exact hrec d ht hμ

/-- Single-coordinate uniformity of a `t`-independent distribution (`1 ≤ t ≤ |α|`). -/
theorem IsTIndependentPMF.prob_apply_eq {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    {t : ℕ} {μ : PMF (α → β)} (hμ : IsTIndependentPMF t μ) (ht1 : 1 ≤ t)
    (ht : t ≤ Fintype.card α) (x : α) (y : β) :
    (μ.toOuterMeasure {h | h x = y}).toReal = 1 / (Fintype.card β : ℝ) := by
  let a : Fin 1 ↪ α := ⟨fun _ : Fin 1 ↦ x, fun i j _ ↦ Subsingleton.elim i j⟩
  have h1 := (hμ.mono ht1 ht) a (fun _ ↦ y)
  have hset : ({h : α → β | ∀ r : Fin 1, h (a r) = y} : Set (α → β)) = {h | h x = y} := by
    ext h; exact ⟨fun hh ↦ hh 0, fun hh _ ↦ hh⟩
  rwa [hset, pow_one] at h1

/-- Pairwise uniformity of a `2`-independent distribution on distinct coordinates. -/
theorem IsTIndependentPMF.prob_apply_eq_and {α β : Type*} [Fintype β]
    {μ : PMF (α → β)} (hμ : IsTIndependentPMF 2 μ) {x₁ x₂ : α} (hne : x₁ ≠ x₂) (y₁ y₂ : β) :
    (μ.toOuterMeasure {h | h x₁ = y₁ ∧ h x₂ = y₂}).toReal =
      1 / (Fintype.card β : ℝ) ^ 2 := by
  let a : Fin 2 ↪ α := ⟨![x₁, x₂], fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp_all⟩
  have h2 := hμ a ![y₁, y₂]
  have hset : ({h : α → β | ∀ r : Fin 2, h (a r) = ![y₁, y₂] r} : Set (α → β)) =
      {h | h x₁ = y₁ ∧ h x₂ = y₂} := by
    ext h; exact Fin.forall_fin_two
  rw [hset, one_div, inv_pow, ← one_div] at h2
  exact h2

/-- The uniform distribution on `α → β` is `t`-independent for every `t : ℕ`. -/
theorem isTIndependentPMF_uniformOfFintype (α β : Type*) [Fintype α] [DecidableEq α]
    [Fintype β] [Nonempty β] (t : ℕ) :
    IsTIndependentPMF t (Cslib.Probability.PMF.uniformOfFintype (α → β)) := by
  classical
  intro a b
  rw [outerMeasure_toReal_eq_sum]
  have hunif : ∀ h : α → β,
      (Cslib.Probability.PMF.uniformOfFintype (α → β) h).toReal =
        ((Fintype.card β : ℝ) ^ Fintype.card α)⁻¹ := fun h ↦ by
    rw [Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Fintype.card_fun, Nat.cast_pow]
  simp_rw [hunif, Set.mem_ofPred_eq, ← mul_sum]
  have hle : t ≤ Fintype.card α := by simpa using Fintype.card_le_of_injective a a.injective
  have hcnt : (∑ h : α → β, if ∀ r : Fin t, h (a r) = b r then (1 : ℝ) else 0) =
      (Fintype.card β : ℝ) ^ (Fintype.card α - t) := by
    rw [sum_boole]
    norm_cast
    let S : Finset α := univ.image a
    have hS : #S = t := by
      rw [card_image_of_injective _ a.injective, card_univ, Fintype.card_fin]
    let R : Finset α := univ \ S
    have hR : #R = Fintype.card α - t := by rw [card_sdiff, inter_univ, card_univ, hS]
    have hfun : #(univ : Finset (R → β)) = Fintype.card β ^ (Fintype.card α - t) := by
      rw [card_univ, Fintype.card_fun, Fintype.card_coe, hR]
    rw [← hfun]
    refine card_bij (fun h _ (x : R) ↦ h x.1) (fun _ _ ↦ mem_univ _) ?_ ?_
    · intro h₁ hh₁ h₂ hh₂ heq
      simp only [mem_filter, mem_univ, true_and] at hh₁ hh₂
      funext x
      by_cases hx : x ∈ S
      · obtain ⟨r, _, rfl⟩ := mem_image.mp hx
        rw [hh₁ r, hh₂ r]
      · exact congrFun heq ⟨x, by simp [R, hx]⟩
    · intro g _
      let h : α → β := fun x ↦
        if hx : ∃ r : Fin t, a r = x then b (Classical.choose hx)
        else g ⟨x, mem_sdiff.mpr ⟨mem_univ x, fun hm ↦ by
          obtain ⟨r, _, hr⟩ := mem_image.mp hm; exact hx ⟨r, hr⟩⟩⟩
      refine ⟨h, ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and, h]
        intro r
        have hex : ∃ r' : Fin t, a r' = a r := ⟨r, rfl⟩
        simp only [hex, ↓reduceDIte]
        exact congrArg b (a.injective (Classical.choose_spec hex))
      · funext ⟨x, hxR⟩
        have hnx : ¬∃ r : Fin t, a r = x := fun ⟨r, hr⟩ ↦
          (mem_sdiff.mp hxR).2 (mem_image.mpr ⟨r, mem_univ r, hr⟩)
        simp [h, hnx]
  have hβ_pos : (0 : ℝ) < (Fintype.card β : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hpow : (Fintype.card β : ℝ) ^ Fintype.card α =
      (Fintype.card β : ℝ) ^ (Fintype.card α - t) * (Fintype.card β : ℝ) ^ t := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hcnt, hpow, one_div, inv_pow]
  field_simp

/-- **Pairwise-independent Chebyshev concentration**: if `μ : PMF (α → β)` is `1`-independent and
`2`-independent on a nonempty finite domain `α`, and `f : β → [0, 1]`, then for every `τ > 0`,
`Pr_{h ~ μ}[τ ≤ |empMean h - avg|] ≤ 1 / (4 |α| τ ^ 2)`. -/
theorem IsTIndependentPMF.empirical_mean_chebyshev {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] {μ : PMF (α → β)} (hμ1 : IsTIndependentPMF 1 μ) (hμ2 : IsTIndependentPMF 2 μ)
    (hm : 0 < Fintype.card α) (f : β → ℝ) (hf : ∀ y : β, f y ∈ Set.Icc 0 1)
    {τ : ℝ} (hτ : 0 < τ) :
    let avg : ℝ := (∑ y : β, f y) / (Fintype.card β : ℝ)
    (μ.toOuterMeasure {h | τ ≤ |(∑ x : α, f (h x)) / (Fintype.card α : ℝ) - avg|}).toReal ≤
      1 / (4 * (Fintype.card α : ℝ) * τ ^ 2) := by
  classical
  intro avg
  have hm_r : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr hm
  have hn_r : (0 : ℝ) < (Fintype.card β : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hexp1 : ∀ (x : α) (g : β → ℝ),
      ∑ h : α → β, (μ h).toReal * g (h x) = (∑ y : β, g y) / (Fintype.card β : ℝ) := by
    intro x g
    rw [← sum_fiberwise_of_maps_to (g := fun h : α → β ↦ h x) (fun h _ ↦ mem_univ (h x))]
    have hfib : ∀ y : β,
        ∑ h ∈ univ.filter (fun h : α → β ↦ h x = y), (μ h).toReal * g (h x) =
          g y / (Fintype.card β : ℝ) := by
      intro y
      have hcongr : ∑ h ∈ univ.filter (fun h : α → β ↦ h x = y), (μ h).toReal * g (h x) =
          (∑ h ∈ univ.filter (fun h : α → β ↦ h x = y), (μ h).toReal) * g y := by
        rw [sum_mul]; exact sum_congr rfl fun h hh ↦ by rw [(mem_filter.mp hh).2]
      have hpr := hμ1.prob_apply_eq le_rfl hm x y
      have hpr' : (∑ h ∈ univ.filter (fun h : α → β ↦ h x = y), (μ h).toReal) =
          1 / (Fintype.card β : ℝ) := by
        rw [← hpr, outerMeasure_toReal_eq_sum, sum_filter]
        exact sum_congr rfl fun h _ ↦ by by_cases hh : h x = y <;> simp [Set.mem_ofPred_eq, hh]
      rw [hcongr, hpr', one_div, inv_mul_eq_div]
    simp_rw [hfib, ← sum_div]
  have hexp2 : ∀ {x₁ x₂ : α}, x₁ ≠ x₂ → ∀ g : β → ℝ,
      ∑ h : α → β, (μ h).toReal * (g (h x₁) * g (h x₂)) =
        ((∑ y : β, g y) / (Fintype.card β : ℝ)) ^ 2 := by
    intro x₁ x₂ hne g
    rw [← sum_fiberwise_of_maps_to (g := fun h : α → β ↦ (h x₁, h x₂))
      (fun h _ ↦ mem_univ (h x₁, h x₂))]
    have hfib : ∀ p : β × β,
        ∑ h ∈ univ.filter (fun h : α → β ↦ (h x₁, h x₂) = p),
          (μ h).toReal * (g (h x₁) * g (h x₂)) =
          (g p.1 * g p.2) / (Fintype.card β : ℝ) ^ 2 := by
      rintro ⟨y₁, y₂⟩
      have hcongr : ∑ h ∈ univ.filter (fun h : α → β ↦ (h x₁, h x₂) = (y₁, y₂)),
            (μ h).toReal * (g (h x₁) * g (h x₂)) =
          (∑ h ∈ univ.filter (fun h : α → β ↦ h x₁ = y₁ ∧ h x₂ = y₂), (μ h).toReal) *
            (g y₁ * g y₂) := by
        rw [sum_mul]
        refine sum_congr (by ext h; simp) fun h hh ↦ ?_
        rw [(mem_filter.mp hh).2.1, (mem_filter.mp hh).2.2]
      have hpr := hμ2.prob_apply_eq_and hne y₁ y₂
      have hpr' : (∑ h ∈ univ.filter (fun h : α → β ↦ h x₁ = y₁ ∧ h x₂ = y₂), (μ h).toReal) =
          1 / (Fintype.card β : ℝ) ^ 2 := by
        rw [← hpr, outerMeasure_toReal_eq_sum, sum_filter]
        exact sum_congr rfl fun h _ ↦ by
          by_cases hh : h x₁ = y₁ ∧ h x₂ = y₂ <;> simp [Set.mem_ofPred_eq, hh]
      rw [hcongr, hpr', one_div, inv_mul_eq_div]
    simp_rw [hfib, ← sum_div]
    rw [div_pow, Fintype.sum_prod_type]
    congr 1
    simp_rw [← mul_sum, ← sum_mul, sq]
  let g : β → ℝ := fun y ↦ f y - avg
  have hg_sum : ∑ y : β, g y = 0 := by
    simp only [g, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, avg]
    field_simp
    ring
  have hg_sq : (∑ y : β, g y ^ 2) / (Fintype.card β : ℝ) ≤ 1 / 4 := by
    have hsum_f : ∑ y : β, f y = (Fintype.card β : ℝ) * avg := by
      simp only [avg]; field_simp
    have hle : ∑ y : β, g y ^ 2 ≤ (Fintype.card β : ℝ) * (avg - avg ^ 2) := by
      have h1 : ∑ y : β, g y ^ 2 =
          (∑ y : β, f y ^ 2) - 2 * avg * (∑ y : β, f y) + (Fintype.card β : ℝ) * avg ^ 2 := by
        have hexp : ∀ y : β, g y ^ 2 = f y ^ 2 - 2 * avg * f y + avg ^ 2 := fun y ↦ by
          dsimp only [g]; ring
        simp_rw [hexp, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
          nsmul_eq_mul]
      have h2 : ∑ y : β, f y ^ 2 ≤ ∑ y : β, f y :=
        sum_le_sum fun y _ ↦ by nlinarith [(hf y).1, (hf y).2]
      rw [h1, hsum_f]
      nlinarith
    calc
      (∑ y : β, g y ^ 2) / (Fintype.card β : ℝ)
        ≤ ((Fintype.card β : ℝ) * (avg - avg ^ 2)) / (Fintype.card β : ℝ) :=
          div_le_div_of_nonneg_right hle hn_r.le
      _ = avg - avg ^ 2 := mul_div_cancel_left₀ _ hn_r.ne'
      _ ≤ 1 / 4 := by nlinarith [sq_nonneg (avg - 1 / 2)]
  have hvar : ∑ h : α → β, (μ h).toReal * (∑ x : α, g (h x)) ^ 2 ≤ (Fintype.card α : ℝ) / 4 := by
    have hexpand : ∑ h : α → β, (μ h).toReal * (∑ x : α, g (h x)) ^ 2 =
        ∑ x₁ : α, ∑ x₂ : α, ∑ h : α → β, (μ h).toReal * (g (h x₁) * g (h x₂)) := by
      simp_rw [sq, sum_mul, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ ↦ sum_comm
    rw [hexpand]
    calc
      ∑ x₁ : α, ∑ x₂ : α, ∑ h : α → β, (μ h).toReal * (g (h x₁) * g (h x₂))
        = ∑ x₁ : α, (∑ y : β, g y ^ 2) / (Fintype.card β : ℝ) := by
          refine sum_congr rfl fun x₁ _ ↦ ?_
          rw [sum_eq_single x₁]
          · simp_rw [← sq]; exact hexp1 x₁ (fun y ↦ g y ^ 2)
          · intro x₂ _ hne; rw [hexp2 hne.symm g, hg_sum, zero_div, zero_pow (by norm_num)]
          · intro hmem; exact absurd (mem_univ _) hmem
      _ ≤ ∑ _x₁ : α, (1 / 4 : ℝ) := sum_le_sum fun _ _ ↦ hg_sq
      _ = (Fintype.card α : ℝ) / 4 := by simp [div_eq_mul_inv]
  have hset : {h : α → β | τ ≤ |(∑ x : α, f (h x)) / (Fintype.card α : ℝ) - avg|} ⊆
      {h : α → β | ((Fintype.card α : ℝ) * τ) ^ 2 ≤ (∑ x : α, g (h x)) ^ 2} := by
    intro h (hh : τ ≤ |(∑ x : α, f (h x)) / (Fintype.card α : ℝ) - avg|)
    change ((Fintype.card α : ℝ) * τ) ^ 2 ≤ (∑ x : α, g (h x)) ^ 2
    have hdiv : ((∑ x : α, f (h x)) / (Fintype.card α : ℝ) - avg) * (Fintype.card α : ℝ) =
        ∑ x : α, g (h x) := by
      simp only [g, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
      field_simp
    have habs : (Fintype.card α : ℝ) * τ ≤ |∑ x : α, g (h x)| := by
      rw [← hdiv, abs_mul, abs_of_pos hm_r]; nlinarith
    rw [← sq_abs (∑ x : α, g (h x))]
    exact pow_le_pow_left₀ (by positivity) habs 2
  calc
    (μ.toOuterMeasure {h | τ ≤ |(∑ x : α, f (h x)) / (Fintype.card α : ℝ) - avg|}).toReal
      ≤ (μ.toOuterMeasure
          {h | ((Fintype.card α : ℝ) * τ) ^ 2 ≤ (∑ x : α, g (h x)) ^ 2}).toReal :=
        outerMeasure_toReal_mono μ hset
    _ ≤ (∑ h : α → β, (μ h).toReal * (∑ x : α, g (h x)) ^ 2) /
          ((Fintype.card α : ℝ) * τ) ^ 2 :=
        markov_toReal μ (fun _ _ ↦ sq_nonneg _) (by positivity)
    _ ≤ ((Fintype.card α : ℝ) / 4) / ((Fintype.card α : ℝ) * τ) ^ 2 :=
        div_le_div_of_nonneg_right hvar (by positivity)
    _ = 1 / (4 * (Fintype.card α : ℝ) * τ ^ 2) := by
        have hmne : (Fintype.card α : ℝ) ≠ 0 := hm_r.ne'
        have hτne : τ ≠ 0 := hτ.ne'
        field_simp

/-- Strict-threshold variant of `IsTIndependentPMF.empirical_mean_chebyshev`. -/
theorem IsTIndependentPMF.empirical_mean_chebyshev_gt {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] {μ : PMF (α → β)} (hμ1 : IsTIndependentPMF 1 μ) (hμ2 : IsTIndependentPMF 2 μ)
    (hm : 0 < Fintype.card α) (f : β → ℝ) (hf : ∀ y : β, f y ∈ Set.Icc 0 1)
    {τ : ℝ} (hτ : 0 < τ) :
    let avg : ℝ := (∑ y : β, f y) / (Fintype.card β : ℝ)
    (μ.toOuterMeasure {h | τ < |(∑ x : α, f (h x)) / (Fintype.card α : ℝ) - avg|}).toReal ≤
      1 / (4 * (Fintype.card α : ℝ) * τ ^ 2) := by
  refine (outerMeasure_toReal_mono μ ?_).trans (hμ1.empirical_mean_chebyshev hμ2 hm f hf hτ)
  intro h hh
  rw [Set.mem_ofPred_eq] at hh ⊢
  exact le_of_lt hh

/-- **Carathéodory sparse `t`-independent distribution theorem**: for any finite types `α, β` with
`β` nonempty and any `t : ℕ`, there exists a seed size `1 ≤ k ≤ |α| ^ t * |β| ^ t + 1`, a seed
distribution `ν : PMF (Fin k)`, and an evaluation map `eval : Fin k → α → β` such that
`ν.map eval` is `t`-independent. -/
theorem exists_isTIndependentPMF_card_le (α β : Type*) [Fintype α] [Fintype β] [Nonempty β]
    (t : ℕ) :
    ∃ (k : ℕ) (_ : 0 < k) (ν : PMF (Fin k)) (eval : Fin k → α → β),
      k ≤ Fintype.card α ^ t * Fintype.card β ^ t + 1 ∧
        IsTIndependentPMF t (ν.map eval) := by
  classical
  let V := {f : Fin t → α // Function.Injective f} × (Fin t → β)
  have hcard_emb : Fintype.card {f : Fin t → α // Function.Injective f} ≤ Fintype.card α ^ t :=
    (Fintype.card_subtype_le _).trans (by rw [Fintype.card_fun, Fintype.card_fin])
  have hcard_V : Fintype.card V ≤ Fintype.card α ^ t * Fintype.card β ^ t := by
    dsimp only [V]
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ hcard_emb
  let vec : (α → β) → (V → ℝ) := fun h p ↦ if ∀ r : Fin t, h (p.1.1 r) = p.2 r then 1 else 0
  let target : V → ℝ := fun _ ↦ (1 / (Fintype.card β : ℝ)) ^ t
  let unif := Cslib.Probability.PMF.uniformOfFintype (α → β)
  have hmem : target ∈ convexHull ℝ (Set.range vec) := by
    rw [mem_convexHull_iff]
    intro C hrange hconv
    have htarget_eq : ∑ h : α → β, (unif h).toReal • vec h = target := by
      funext ⟨a, b⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vec, target]
      rw [← isTIndependentPMF_uniformOfFintype α β t ⟨a.1, a.2⟩ b, outerMeasure_toReal_eq_sum]
      rfl
    rw [← htarget_eq]
    exact hconv.sum_mem (fun _ _ ↦ ENNReal.toReal_nonneg) (sum_toReal_eq_one unif)
      (fun h _ ↦ hrange (Set.mem_range_self h))
  obtain ⟨ι, hfin, z, w, hrange, haff, hw_pos, hw_sum, hw_eq⟩ :=
    eq_pos_convex_span_of_mem_convexHull hmem
  let _ : Fintype ι := hfin
  have hι_pos : 0 < Fintype.card ι := by
    by_contra h0
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by omega)
    simp at hw_sum
  have hι_le : Fintype.card ι ≤ Fintype.card V + 1 := by
    obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp hι_pos
    have hli : LinearIndependent ℝ (fun i : {x : ι // x ≠ i₀} ↦ z i -ᵥ z i₀) :=
      (affineIndependent_iff_linearIndependent_vsub ℝ z i₀).mp haff
    have hle := hli.fintype_card_le_finrank
    have hcne : Fintype.card {x : ι // x ≠ i₀} = Fintype.card ι - 1 := by simp
    rw [hcne, Module.finrank_fintype_fun_eq_card] at hle
    omega
  set k := Fintype.card ι
  let e : Fin k ≃ ι := (Fintype.equivFin ι).symm
  let eval : Fin k → α → β := fun i ↦ Classical.choose (hrange (Set.mem_range_self (e i)))
  have heval : ∀ i : Fin k, vec (eval i) = z (e i) := fun i ↦
    Classical.choose_spec (hrange (Set.mem_range_self (e i)))
  have hhasSum : HasSum (fun i : Fin k ↦ ENNReal.ofReal (w (e i))) 1 := by
    have hsum_e : ∑ i : Fin k, w (e i) = 1 := by rw [Equiv.sum_comp e w, hw_sum]
    have hsum_enn : ∑ i : Fin k, ENNReal.ofReal (w (e i)) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ (hw_pos (e i)).le, hsum_e, ENNReal.ofReal_one]
    rw [← hsum_enn]
    exact hasSum_fintype _
  let ν : PMF (Fin k) := ⟨fun i ↦ ENNReal.ofReal (w (e i)), hhasSum⟩
  refine ⟨k, hι_pos, ν, eval, hι_le.trans (Nat.add_le_add_right hcard_V 1), ?_⟩
  intro a b
  let aSub : {f : Fin t → α // Function.Injective f} := ⟨a, a.injective⟩
  rw [PMF.toOuterMeasure_map_apply, outerMeasure_toReal_eq_sum]
  have hν_real : ∀ i : Fin k, (ν i).toReal = w (e i) := fun i ↦
    ENNReal.toReal_ofReal (hw_pos (e i)).le
  calc
    ∑ i : Fin k, (ν i).toReal *
        (if i ∈ eval ⁻¹' {h : α → β | ∀ r : Fin t, h (a r) = b r} then (1 : ℝ) else 0)
      = ∑ i : Fin k, w (e i) * vec (eval i) (aSub, b) :=
        sum_congr rfl fun i _ ↦ by
          rw [hν_real i]
          congr 1
          by_cases hc : ∀ r : Fin t, eval i (a r) = b r
          · have h1 : (if i ∈ eval ⁻¹' {h : α → β | ∀ r : Fin t, h (a r) = b r}
                then (1 : ℝ) else 0) = 1 :=
              ite_eq_left_iff.mpr fun hn ↦ absurd hc hn
            have h2 : vec (eval i) (aSub, b) = 1 :=
              ite_eq_left_iff.mpr fun hn ↦ absurd hc hn
            exact h1.trans h2.symm
          · have h1 : (if i ∈ eval ⁻¹' {h : α → β | ∀ r : Fin t, h (a r) = b r}
                then (1 : ℝ) else 0) = 0 :=
              ite_eq_right_iff.mpr fun h ↦ absurd h hc
            have h2 : vec (eval i) (aSub, b) = 0 :=
              ite_eq_right_iff.mpr fun h ↦ absurd h hc
            exact h1.trans h2.symm
    _ = ∑ i : Fin k, w (e i) * z (e i) (aSub, b) :=
        sum_congr rfl fun i _ ↦ by rw [heval i]
    _ = ∑ j : ι, w j * z j (aSub, b) := Equiv.sum_comp e (fun j ↦ w j * z j (aSub, b))
    _ = (∑ j : ι, w j • z j) (aSub, b) := by simp [Finset.sum_apply]
    _ = target (aSub, b) := congrFun hw_eq (aSub, b)
    _ = (1 / (Fintype.card β : ℝ)) ^ t := rfl

/-- Simultaneous `1`- and `2`-independent distribution supported on `k` functions with
`1 ≤ k ≤ |α| ^ 2 * |β| ^ 2 + |β|` for all finite `α, β` (`Nonempty β`). -/
theorem exists_pairwiseIndependentPMF_card_le (α β : Type*) [Fintype α] [Fintype β] [Nonempty β] :
    ∃ (k : ℕ) (_ : 0 < k) (ν : PMF (Fin k)) (eval : Fin k → α → β),
      k ≤ Fintype.card α ^ 2 * Fintype.card β ^ 2 + Fintype.card β ∧
        IsTIndependentPMF 1 (ν.map eval) ∧ IsTIndependentPMF 2 (ν.map eval) := by
  classical
  by_cases h2 : 2 ≤ Fintype.card α
  · obtain ⟨k, hk, ν, eval, hle, hμ2⟩ := exists_isTIndependentPMF_card_le α β 2
    have hβ1 : 1 ≤ Fintype.card β := Fintype.card_pos
    exact ⟨k, hk, ν, eval, by omega, hμ2.mono (by omega) h2, hμ2⟩
  · by_cases h1 : Fintype.card α = 1
    · let k := Fintype.card β
      have : Nonempty (Fin k) := ⟨⟨0, Fintype.card_pos⟩⟩
      let e : Fin k ≃ β := (Fintype.equivFin β).symm
      let ν : PMF (Fin k) := Cslib.Probability.PMF.uniformOfFintype (Fin k)
      let eval : Fin k → α → β := fun i _ ↦ e i
      refine ⟨k, Fintype.card_pos, ν, eval, by dsimp [k]; omega, ?_, ?_⟩
      · intro a b
        rw [PMF.toOuterMeasure_map_apply, outerMeasure_toReal_eq_sum]
        simp only [ν, eval, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
          ENNReal.toReal_inv, ENNReal.toReal_natCast, Fin.forall_fin_one, Set.mem_preimage,
          Set.mem_ofPred_eq, pow_one]
        rw [sum_eq_single (e.symm (b 0))]
        · simp [k, one_div]
        · intro i _ hi
          have hne : e i ≠ b 0 := fun heq ↦ hi (by rw [← heq, e.symm_apply_apply])
          simp [hne]
        · intro hmem; exact absurd (mem_univ _) hmem
      · intro a
        have := Fintype.card_le_of_injective a a.injective
        simp [h1] at this
    · have h0 : Fintype.card α = 0 := by omega
      have hβ1 : 1 ≤ Fintype.card β := Fintype.card_pos
      refine ⟨1, Nat.one_pos, PMF.pure 0, fun _ _ ↦ Classical.arbitrary β, by omega, ?_, ?_⟩
      · intro a; have := Fintype.card_le_of_injective a a.injective; simp [h0] at this
      · intro a; have := Fintype.card_le_of_injective a a.injective; simp [h0] at this

end CslibFrontier.Probability
