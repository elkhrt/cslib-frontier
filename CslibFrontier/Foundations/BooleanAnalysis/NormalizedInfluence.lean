/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.FourierRestriction
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import CslibFrontier.Foundations.BooleanAnalysis.Noise
public import CslibFrontier.Foundations.BooleanAnalysis.SignApproximation
public import Mathlib.Logic.Function.DependsOn

import CslibFrontier.Foundations.BooleanAnalysis.Fibers
import CslibFrontier.Foundations.BooleanAnalysis.Variance
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalized Influences, Noise $L^1$ Contractivity, and Nearest Subset Juntas

This module develops normalized influences and subset projections for real-valued and Boolean
functions on the finite hypercube `ι → Bool` under standard Lean axioms.

Given a function `f : (ι → Bool) → ℝ` with Fourier coefficients `fourierCoeff f S`, the
*normalized influence* of coordinate `i` weights each non-empty Fourier mode
`S ∋ i` inversely by its degree `#S`, so that the total normalized influence across all
coordinates equals the variance of `f`. Generalizing from single coordinates to subsets
`U : Finset ι` weights each superset `S ⊇ U` inversely by `(#S).choose #U`, so that summing over
all subsets `U` of cardinality `κ` recovers the Fourier weight at and above level `κ`.

We also establish $L^1$-contractivity of the Bonami–Beckner noise operator `noiseOp ρ` for
`|ρ| ≤ 1` and show that among all Boolean juntas depending only on a coordinate subset `T`,
rounding the conditional expectation `subsetProjection T f` to its sign maximizes correlation
with `f`, achieving correlation `𝔼 x, |subsetProjection T f x|`.

## Main definitions

* `CslibFrontier.BooleanAnalysis.lowDegreeInfluence`: low-degree influence
  `∑_{S : i ∈ S ∧ #S ≤ k} f̂(S)²`.
* `CslibFrontier.BooleanAnalysis.normalizedInfluence`: coordinate normalized influence
  `∑_{S : i ∈ S} f̂(S)² / #S`.
* `CslibFrontier.BooleanAnalysis.lowDegreeNormalizedInfluence`: degree-truncated coordinate
  normalized influence `∑_{S : i ∈ S ∧ #S ≤ k} f̂(S)² / #S`.
* `CslibFrontier.BooleanAnalysis.setNormalizedInfluence`: subset normalized influence
  `∑_{S : U ⊆ S} f̂(S)² / (#S).choose #U`.
* `CslibFrontier.BooleanAnalysis.lowDegreeSetNormalizedInfluence`: degree-truncated subset
  normalized influence `∑_{S : U ⊆ S ∧ #S ≤ k} f̂(S)² / (#S).choose #U`.
* `CslibFrontier.BooleanAnalysis.subsetProjection`: conditional expectation
  `f^{⊆ T}(x) = 𝔼 z, f (T.piecewise x z)` onto coordinates in `T`.

## Main results

* `CslibFrontier.BooleanAnalysis.sum_normalizedInfluence_eq_variance`: the sum of coordinate
  normalized influences equals the variance `𝔼 x, (f x - 𝔼 y, f y) ^ 2`.
* `CslibFrontier.BooleanAnalysis.sum_fourierCoeff_sq_subset_le_sum_lowDegreeNormalizedInfluence`:
  for `#T ≤ k`, the non-empty Fourier mass supported inside `T` is bounded above by
  `∑ i ∈ T, lowDegreeNormalizedInfluence k i f`.
* `CslibFrontier.BooleanAnalysis.sum_setNormalizedInfluence_card_eq`: summing
  `setNormalizedInfluence U f` over `#U = κ` equals `∑_{S : κ ≤ #S} f̂(S)²`.
* `CslibFrontier.BooleanAnalysis.sum_fourierCoeff_sq_le_sum_lowDegreeSetNormalizedInfluence`:
  for `#V ≤ k`, the Fourier mass on `{S ⊆ V : κ ≤ #S}` is at most
  `∑_{U : U ⊆ V ∧ #U = κ} lowDegreeSetNormalizedInfluence k U f`.
* `CslibFrontier.BooleanAnalysis.expect_abs_noiseOp_le`: for `|ρ| ≤ 1`,
  `𝔼 x, |noiseOp ρ f x| ≤ 𝔼 x, |f x|`.
* `CslibFrontier.BooleanAnalysis.expect_mul_signVal_le_expect_abs_subsetProjection` and
  `CslibFrontier.BooleanAnalysis.expect_mul_signVal_signRound_subsetProjection`:
  `signRound (subsetProjection T f)` maximizes correlation with `f` over all Boolean `T`-juntas,
  with maximum correlation `𝔼 x, |subsetProjection T f x|`.
-/

public section

namespace CslibFrontier.BooleanAnalysis

open Cslib.BitString Finset
open scoped BigOperators

section Influences

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **low-degree influence** up to degree `k` of coordinate `i` on `f : (ι → Bool) → ℝ`,
defined as `∑_{S : i ∈ S ∧ #S ≤ k} f̂(S)²`. -/
noncomputable def lowDegreeInfluence (k : ℕ) (i : ι) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S with i ∈ S ∧ #S ≤ k, fourierCoeff f S ^ 2

/-- Low-degree influence is nonnegative. -/
theorem lowDegreeInfluence_nonneg (k : ℕ) (i : ι) (f : (ι → Bool) → ℝ) :
    0 ≤ lowDegreeInfluence k i f :=
  sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Low-degree influence is monotone in the degree cutoff `k`. -/
@[gcongr]
theorem lowDegreeInfluence_mono {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (i : ι) (f : (ι → Bool) → ℝ) :
    lowDegreeInfluence k₁ i f ≤ lowDegreeInfluence k₂ i f :=
  sum_le_sum_of_subset_of_nonneg
    (monotone_filter_right univ fun _ _ h ↦ ⟨h.1, h.2.trans hk⟩)
    fun _ _ _ ↦ sq_nonneg _

/-- Low-degree influence is at most the full coordinate influence. -/
theorem lowDegreeInfluence_le_influence (k : ℕ) (i : ι) (f : (ι → Bool) → ℝ) :
    lowDegreeInfluence k i f ≤ influence i f := by
  rw [lowDegreeInfluence, influence_eq_sum_fourierCoeff_sq]
  exact sum_le_sum_of_subset_of_nonneg
    (monotone_filter_right univ fun _ _ h ↦ h.1)
    fun _ _ _ ↦ sq_nonneg _

/-- Any partial sum of squared Fourier coefficients over sets containing `i` of cardinality at
most `k` is bounded above by `lowDegreeInfluence k i f`. -/
theorem sum_fourierCoeff_sq_le_lowDegreeInfluence {k : ℕ} {i : ι}
    {P : Finset (Finset ι)} (hP : ∀ S ∈ P, i ∈ S ∧ #S ≤ k) (f : (ι → Bool) → ℝ) :
    ∑ S ∈ P, fourierCoeff f S ^ 2 ≤ lowDegreeInfluence k i f := by
  rw [lowDegreeInfluence]
  exact sum_le_sum_of_subset_of_nonneg
    (fun S hS ↦ mem_filter.mpr ⟨mem_univ S, hP S hS⟩)
    fun _ _ _ ↦ sq_nonneg _

/-- Weighted Fourier lower bound in terms of `lowDegreeInfluence`: if `0 ≤ w #S` for all `#S ≥ 1`
and `c ≤ w #S` for all `1 ≤ #S ≤ k`, then
`c * lowDegreeInfluence k i f ≤ ∑_{S : i ∈ S} f̂(S)² * w #S`. -/
theorem mul_lowDegreeInfluence_le_sum {c : ℝ} {k : ℕ} {w : ℕ → ℝ}
    (hw_nonneg : ∀ s, 1 ≤ s → 0 ≤ w s)
    (hw_lb : ∀ s, 1 ≤ s → s ≤ k → c ≤ w s)
    (i : ι) (f : (ι → Bool) → ℝ) :
    c * lowDegreeInfluence k i f ≤
      ∑ S with i ∈ S, fourierCoeff f S ^ 2 * w #S := by
  rw [lowDegreeInfluence, mul_sum]
  calc ∑ S with i ∈ S ∧ #S ≤ k, c * fourierCoeff f S ^ 2
      ≤ ∑ S with i ∈ S ∧ #S ≤ k, fourierCoeff f S ^ 2 * w #S := by
        refine sum_le_sum fun S hS ↦ ?_
        obtain ⟨_, hiS, hSk⟩ := mem_filter.mp hS
        rw [mul_comm c]
        exact mul_le_mul_of_nonneg_left (hw_lb #S (card_pos.mpr ⟨i, hiS⟩) hSk) (sq_nonneg _)
    _ ≤ ∑ S with i ∈ S, fourierCoeff f S ^ 2 * w #S :=
        sum_le_sum_of_subset_of_nonneg (monotone_filter_right univ fun _ _ h ↦ h.1)
          fun S hS _ ↦ mul_nonneg (sq_nonneg _)
            (hw_nonneg #S (card_pos.mpr ⟨i, (mem_filter.mp hS).2⟩))

/-- Summing low-degree influences up to degree `k` across all coordinates gives at most
`k * 𝔼 x, f x ^ 2`. -/
theorem sum_lowDegreeInfluence_le_mul_expect_sq (k : ℕ) (f : (ι → Bool) → ℝ) :
    ∑ i : ι, lowDegreeInfluence k i f ≤ k * 𝔼 x, f x ^ 2 := by
  have hswap : ∑ i : ι, lowDegreeInfluence k i f =
      ∑ S with #S ≤ k, (#S : ℝ) * fourierCoeff f S ^ 2 := by
    simp only [lowDegreeInfluence]
    have h := sum_comm' (s := univ) (t := fun i ↦ univ.filter fun S ↦ i ∈ S ∧ #S ≤ k)
      (t' := univ.filter fun S ↦ #S ≤ k) (s' := fun S ↦ S)
      (f := fun _ S ↦ fourierCoeff f S ^ 2)
      (fun i S ↦ by simp [and_comm])
    rw [h]
    exact sum_congr rfl fun S _ ↦ by rw [sum_const, nsmul_eq_mul]
  rw [hswap, expect_sq_eq_sum_fourierCoeff_sq, mul_sum]
  calc ∑ S with #S ≤ k, (#S : ℝ) * fourierCoeff f S ^ 2
      ≤ ∑ S with #S ≤ k, (k : ℝ) * fourierCoeff f S ^ 2 := by
        refine sum_le_sum fun S hS ↦ ?_
        have hk : (#S : ℝ) ≤ k := Nat.cast_le.mpr (mem_filter.mp hS).2
        have hsq : 0 ≤ fourierCoeff f S ^ 2 := sq_nonneg _
        gcongr
    _ ≤ ∑ S, (k : ℝ) * fourierCoeff f S ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ by positivity

/-- The **normalized influence** of coordinate `i` on `f : (ι → Bool) → ℝ`,
defined as `∑_{S : i ∈ S} f̂(S)² / #S`.
-/
noncomputable def normalizedInfluence (i : ι) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S with i ∈ S, fourierCoeff f S ^ 2 / (#S : ℝ)

/-- Coordinate normalized influence is nonnegative. -/
theorem normalizedInfluence_nonneg (i : ι) (f : (ι → Bool) → ℝ) :
    0 ≤ normalizedInfluence i f :=
  sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Coordinate normalized influence is at most standard coordinate influence. -/
theorem normalizedInfluence_le_influence (i : ι) (f : (ι → Bool) → ℝ) :
    normalizedInfluence i f ≤ influence i f := by
  rw [normalizedInfluence, influence_eq_sum_fourierCoeff_sq]
  refine sum_le_sum fun S hS ↦ ?_
  have h1 : (1 : ℝ) ≤ #S := Nat.one_le_cast.mpr (card_pos.mpr ⟨i, (mem_filter.mp hS).2⟩)
  exact div_le_self (sq_nonneg _) h1

/-- **Total normalized influence equals variance**: summing `normalizedInfluence i f` over all
coordinates `i : ι` gives `𝔼 x, (f x - 𝔼 y, f y) ^ 2`. -/
theorem sum_normalizedInfluence_eq_variance (f : (ι → Bool) → ℝ) :
    ∑ i : ι, normalizedInfluence i f = 𝔼 x, (f x - 𝔼 y, f y) ^ 2 := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq]
  simp only [normalizedInfluence]
  have h := sum_comm' (s := univ) (t := fun i ↦ univ.filter (i ∈ ·))
    (t' := univ.filter (· ≠ ∅)) (s' := fun S ↦ S)
    (f := fun _ S ↦ fourierCoeff f S ^ 2 / (#S : ℝ))
    (fun i S ↦ by
      simp only [mem_univ, mem_filter, true_and]
      exact ⟨fun hi ↦ ⟨hi, ne_empty_of_mem hi⟩, fun h ↦ h.1⟩)
  rw [h]
  refine sum_congr rfl fun S hS ↦ ?_
  have hne : S.Nonempty := nonempty_iff_ne_empty.mpr (mem_filter.mp hS).2
  have hcard : (#S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hne.card_pos.ne'
  rw [sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hcard]

/-- The **low-degree normalized influence** up to degree `k` of coordinate `i` on `f`, defined
as `∑_{S : i ∈ S ∧ #S ≤ k} f̂(S)² / #S`. -/
noncomputable def lowDegreeNormalizedInfluence (k : ℕ) (i : ι) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S with i ∈ S ∧ #S ≤ k, fourierCoeff f S ^ 2 / (#S : ℝ)

/-- Low-degree normalized influence is nonnegative. -/
theorem lowDegreeNormalizedInfluence_nonneg (k : ℕ) (i : ι) (f : (ι → Bool) → ℝ) :
    0 ≤ lowDegreeNormalizedInfluence k i f :=
  sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Low-degree normalized influence is monotone in `k`. -/
@[gcongr]
theorem lowDegreeNormalizedInfluence_mono {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (i : ι)
    (f : (ι → Bool) → ℝ) :
    lowDegreeNormalizedInfluence k₁ i f ≤ lowDegreeNormalizedInfluence k₂ i f :=
  sum_le_sum_of_subset_of_nonneg
    (monotone_filter_right univ fun _ _ h ↦ ⟨h.1, h.2.trans hk⟩)
    fun _ _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Low-degree normalized influence is at most full normalized influence. -/
theorem lowDegreeNormalizedInfluence_le_normalizedInfluence (k : ℕ) (i : ι)
    (f : (ι → Bool) → ℝ) :
    lowDegreeNormalizedInfluence k i f ≤ normalizedInfluence i f :=
  sum_le_sum_of_subset_of_nonneg
    (monotone_filter_right univ fun _ _ h ↦ h.1)
    fun _ _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Weighted Fourier lower bound in terms of `lowDegreeNormalizedInfluence`. -/
theorem mul_lowDegreeNormalizedInfluence_le_sum {c : ℝ} {k : ℕ} {w : ℕ → ℝ}
    (hw_nonneg : ∀ s, 1 ≤ s → 0 ≤ w s)
    (hw_lb : ∀ s, 1 ≤ s → s ≤ k → c / (s : ℝ) ≤ w s)
    (i : ι) (f : (ι → Bool) → ℝ) :
    c * lowDegreeNormalizedInfluence k i f ≤
      ∑ S with i ∈ S, fourierCoeff f S ^ 2 * w #S := by
  rw [lowDegreeNormalizedInfluence, mul_sum]
  calc ∑ S with i ∈ S ∧ #S ≤ k, c * (fourierCoeff f S ^ 2 / (#S : ℝ))
      ≤ ∑ S with i ∈ S ∧ #S ≤ k, fourierCoeff f S ^ 2 * w #S := by
        refine sum_le_sum fun S hS ↦ ?_
        obtain ⟨_, hiS, hSk⟩ := mem_filter.mp hS
        have hs1 : 1 ≤ #S := card_pos.mpr ⟨i, hiS⟩
        calc c * (fourierCoeff f S ^ 2 / (#S : ℝ))
            = fourierCoeff f S ^ 2 * (c / (#S : ℝ)) := by ring
          _ ≤ fourierCoeff f S ^ 2 * w #S :=
              mul_le_mul_of_nonneg_left (hw_lb #S hs1 hSk) (sq_nonneg _)
    _ ≤ ∑ S with i ∈ S, fourierCoeff f S ^ 2 * w #S :=
        sum_le_sum_of_subset_of_nonneg (monotone_filter_right univ fun _ _ h ↦ h.1)
          fun S hS _ ↦ mul_nonneg (sq_nonneg _)
            (hw_nonneg #S (card_pos.mpr ⟨i, (mem_filter.mp hS).2⟩))

/-- Weighted Fourier upper bound in terms of `normalizedInfluence`. -/
theorem sum_le_mul_normalizedInfluence {C : ℝ} {w : ℕ → ℝ}
    (hw_ub : ∀ s, 1 ≤ s → w s ≤ C / (s : ℝ))
    (i : ι) (f : (ι → Bool) → ℝ) :
    ∑ S with i ∈ S, fourierCoeff f S ^ 2 * w #S ≤ C * normalizedInfluence i f := by
  rw [normalizedInfluence, mul_sum]
  refine sum_le_sum fun S hS ↦ ?_
  have hs1 : 1 ≤ #S := card_pos.mpr ⟨i, (mem_filter.mp hS).2⟩
  calc fourierCoeff f S ^ 2 * w #S
      ≤ fourierCoeff f S ^ 2 * (C / (#S : ℝ)) :=
        mul_le_mul_of_nonneg_left (hw_ub #S hs1) (sq_nonneg _)
    _ = C * (fourierCoeff f S ^ 2 / (#S : ℝ)) := by ring

/-- For any subset `T : Finset ι` of size `#T ≤ k`, the non-empty Fourier mass of `f` supported
within `T` is bounded above by `∑ i ∈ T, lowDegreeNormalizedInfluence k i f`. -/
theorem sum_fourierCoeff_sq_subset_le_sum_lowDegreeNormalizedInfluence
    {k : ℕ} {T : Finset ι} (hT : #T ≤ k) (f : (ι → Bool) → ℝ) :
    ∑ S with S.Nonempty ∧ S ⊆ T, fourierCoeff f S ^ 2 ≤
      ∑ i ∈ T, lowDegreeNormalizedInfluence k i f := by
  have hident : ∑ S with S.Nonempty ∧ S ⊆ T, fourierCoeff f S ^ 2 =
      ∑ i ∈ T, ∑ S with S ⊆ T ∧ i ∈ S, fourierCoeff f S ^ 2 / (#S : ℝ) := by
    have h := sum_comm' (s := T) (t := fun i ↦ univ.filter fun S ↦ S ⊆ T ∧ i ∈ S)
      (t' := univ.filter fun S ↦ S.Nonempty ∧ S ⊆ T) (s' := fun S ↦ S)
      (f := fun _ S ↦ fourierCoeff f S ^ 2 / (#S : ℝ))
      (fun i S ↦ by
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun ⟨_, hST, hiS⟩ ↦ ⟨hiS, ⟨i, hiS⟩, hST⟩,
          fun ⟨hiS, _, hST⟩ ↦ ⟨hST hiS, hST, hiS⟩⟩)
    rw [h]
    refine sum_congr rfl fun S hS ↦ ?_
    have hne : (#S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (mem_filter.mp hS).2.1.card_pos.ne'
    rw [sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hne]
  rw [hident]
  refine sum_le_sum fun i _ ↦ ?_
  rw [lowDegreeNormalizedInfluence]
  refine sum_le_sum_of_subset_of_nonneg (fun S hS ↦ ?_)
    fun _ _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨_, hST, hiS⟩ := mem_filter.mp hS
  exact mem_filter.mpr ⟨mem_univ S, hiS, (card_le_card hST).trans hT⟩

/-- The **subset normalized influence** of `U : Finset ι` on `f : (ι → Bool) → ℝ`, defined as
`∑_{S : U ⊆ S} f̂(S)² / (#S).choose #U`. -/
noncomputable def setNormalizedInfluence (U : Finset ι) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S with U ⊆ S, fourierCoeff f S ^ 2 / ((#S).choose #U : ℝ)

/-- Subset normalized influence is nonnegative. -/
theorem setNormalizedInfluence_nonneg (U : Finset ι) (f : (ι → Bool) → ℝ) :
    0 ≤ setNormalizedInfluence U f :=
  sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- On a singleton `{i}`, subset normalized influence agrees with coordinate normalized
influence. -/
@[simp]
theorem setNormalizedInfluence_singleton (i : ι) (f : (ι → Bool) → ℝ) :
    setNormalizedInfluence {i} f = normalizedInfluence i f := by
  simp only [setNormalizedInfluence, normalizedInfluence, singleton_subset_iff, card_singleton,
    Nat.choose_one_right]

/-- Summing `setNormalizedInfluence U f` over all subsets `U` of cardinality `κ` yields the
Fourier weight of `f` at and above level `κ`. -/
theorem sum_setNormalizedInfluence_card_eq (κ : ℕ) (f : (ι → Bool) → ℝ) :
    ∑ U with #U = κ, setNormalizedInfluence U f = ∑ S with κ ≤ #S, fourierCoeff f S ^ 2 := by
  simp only [setNormalizedInfluence]
  have h := sum_comm' (s := univ.filter fun U : Finset ι ↦ #U = κ)
    (t := fun U ↦ univ.filter (U ⊆ ·))
    (t' := univ.filter fun S : Finset ι ↦ κ ≤ #S)
    (s' := fun S ↦ S.powersetCard κ)
    (f := fun _ S ↦ fourierCoeff f S ^ 2 / ((#S).choose κ : ℝ))
    (fun U S ↦ by
      simp only [mem_filter, mem_univ, true_and, mem_powersetCard]
      exact ⟨fun ⟨hU, hUS⟩ ↦ ⟨⟨hUS, hU⟩, hU ▸ card_le_card hUS⟩,
        fun ⟨⟨hUS, hU⟩, _⟩ ↦ ⟨hU, hUS⟩⟩)
  have hcongr : (∑ U with #U = κ, ∑ S with U ⊆ S, fourierCoeff f S ^ 2 / ((#S).choose #U : ℝ)) =
      ∑ U with #U = κ, ∑ S with U ⊆ S, fourierCoeff f S ^ 2 / ((#S).choose κ : ℝ) := by
    refine sum_congr rfl fun U hU ↦ ?_
    rw [(mem_filter.mp hU).2]
  rw [hcongr, h]
  refine sum_congr rfl fun S hS ↦ ?_
  have hpos : 0 < (#S).choose κ := Nat.choose_pos (mem_filter.mp hS).2
  have hne : ((#S).choose κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  rw [sum_const, card_powersetCard, nsmul_eq_mul, mul_div_cancel₀ _ hne]

/-- The **low-degree subset normalized influence** up to degree `k` of `U : Finset ι` on `f`,
defined as `∑_{S : U ⊆ S ∧ #S ≤ k} f̂(S)² / (#S).choose #U`. -/
@[expose] noncomputable def lowDegreeSetNormalizedInfluence (k : ℕ) (U : Finset ι)
    (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S with U ⊆ S ∧ #S ≤ k, fourierCoeff f S ^ 2 / ((#S).choose #U : ℝ)

/-- Low-degree subset normalized influence is nonnegative. -/
theorem lowDegreeSetNormalizedInfluence_nonneg (k : ℕ) (U : Finset ι) (f : (ι → Bool) → ℝ) :
    0 ≤ lowDegreeSetNormalizedInfluence k U f :=
  sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Low-degree subset normalized influence is monotone in `k`. -/
@[gcongr]
theorem lowDegreeSetNormalizedInfluence_mono {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (U : Finset ι)
    (f : (ι → Bool) → ℝ) :
    lowDegreeSetNormalizedInfluence k₁ U f ≤ lowDegreeSetNormalizedInfluence k₂ U f :=
  sum_le_sum_of_subset_of_nonneg
    (monotone_filter_right univ fun _ _ h ↦ ⟨h.1, h.2.trans hk⟩)
    fun _ _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Low-degree subset normalized influence is at most full subset normalized influence. -/
theorem lowDegreeSetNormalizedInfluence_le_setNormalizedInfluence (k : ℕ) (U : Finset ι)
    (f : (ι → Bool) → ℝ) :
    lowDegreeSetNormalizedInfluence k U f ≤ setNormalizedInfluence U f :=
  sum_le_sum_of_subset_of_nonneg
    (monotone_filter_right univ fun _ _ h ↦ h.1)
    fun _ _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- On a singleton `{i}`, low-degree subset normalized influence agrees with low-degree
coordinate normalized influence. -/
@[simp]
theorem lowDegreeSetNormalizedInfluence_singleton (k : ℕ) (i : ι) (f : (ι → Bool) → ℝ) :
    lowDegreeSetNormalizedInfluence k {i} f = lowDegreeNormalizedInfluence k i f := by
  simp only [lowDegreeSetNormalizedInfluence, lowDegreeNormalizedInfluence, singleton_subset_iff,
    card_singleton, Nat.choose_one_right]

/-- Weighted Fourier lower bound in terms of `lowDegreeSetNormalizedInfluence`. -/
theorem mul_lowDegreeSetNormalizedInfluence_le_sum {c : ℝ} {k : ℕ} {U : Finset ι} {w : ℕ → ℝ}
    (hw_nonneg : ∀ s, #U ≤ s → 0 ≤ w s)
    (hw_lb : ∀ s, #U ≤ s → s ≤ k → c ≤ w s)
    (f : (ι → Bool) → ℝ) :
    c * lowDegreeSetNormalizedInfluence k U f ≤
      ∑ S with U ⊆ S, (fourierCoeff f S ^ 2 / ((#S).choose #U : ℝ)) * w #S := by
  rw [lowDegreeSetNormalizedInfluence, mul_sum]
  calc ∑ S with U ⊆ S ∧ #S ≤ k, c * (fourierCoeff f S ^ 2 / ((#S).choose #U : ℝ))
      ≤ ∑ S with U ⊆ S ∧ #S ≤ k,
          (fourierCoeff f S ^ 2 / ((#S).choose #U : ℝ)) * w #S := by
        refine sum_le_sum fun S hS ↦ ?_
        obtain ⟨_, hUS, hSk⟩ := mem_filter.mp hS
        rw [mul_comm c]
        exact mul_le_mul_of_nonneg_left (hw_lb #S (card_le_card hUS) hSk)
          (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ ≤ ∑ S with U ⊆ S, (fourierCoeff f S ^ 2 / ((#S).choose #U : ℝ)) * w #S :=
        sum_le_sum_of_subset_of_nonneg (monotone_filter_right univ fun _ _ h ↦ h.1)
          fun S hS _ ↦ mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
            (hw_nonneg #S (card_le_card (mem_filter.mp hS).2))

/-- Weighted Fourier upper bound in terms of `setNormalizedInfluence`. -/
theorem sum_le_mul_setNormalizedInfluence {C : ℝ} {U : Finset ι} {w : ℕ → ℝ}
    (hw_ub : ∀ s, #U ≤ s → w s ≤ C)
    (f : (ι → Bool) → ℝ) :
    ∑ S with U ⊆ S, (fourierCoeff f S ^ 2 / ((#S).choose #U : ℝ)) * w #S ≤
      C * setNormalizedInfluence U f := by
  rw [setNormalizedInfluence, mul_sum]
  refine sum_le_sum fun S hS ↦ ?_
  rw [mul_comm C]
  exact mul_le_mul_of_nonneg_left (hw_ub #S (card_le_card (mem_filter.mp hS).2))
    (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- For any subset `V : Finset ι` of size `#V ≤ k`, the Fourier mass of `f` on subsets
`S ⊆ V` of size `κ ≤ #S` is at most
`∑_{U : U ⊆ V ∧ #U = κ} lowDegreeSetNormalizedInfluence k U f`. -/
theorem sum_fourierCoeff_sq_le_sum_lowDegreeSetNormalizedInfluence
    {k κ : ℕ} {V : Finset ι} (hV : #V ≤ k) (f : (ι → Bool) → ℝ) :
    ∑ S with S ⊆ V ∧ κ ≤ #S, fourierCoeff f S ^ 2 ≤
      ∑ U with U ⊆ V ∧ #U = κ, lowDegreeSetNormalizedInfluence k U f := by
  have hident : ∑ S with S ⊆ V ∧ κ ≤ #S, fourierCoeff f S ^ 2 =
      ∑ U with U ⊆ V ∧ #U = κ,
        ∑ S with U ⊆ S ∧ S ⊆ V, fourierCoeff f S ^ 2 / ((#S).choose κ : ℝ) := by
    have h := sum_comm' (s := univ.filter fun U : Finset ι ↦ U ⊆ V ∧ #U = κ)
      (t := fun U ↦ univ.filter fun S ↦ U ⊆ S ∧ S ⊆ V)
      (t' := univ.filter fun S : Finset ι ↦ S ⊆ V ∧ κ ≤ #S)
      (s' := fun S ↦ S.powersetCard κ)
      (f := fun _ S ↦ fourierCoeff f S ^ 2 / ((#S).choose κ : ℝ))
      (fun U S ↦ by
        simp only [mem_filter, mem_univ, true_and, mem_powersetCard]
        exact ⟨fun ⟨⟨_, hU⟩, hUS, hSV⟩ ↦ ⟨⟨hUS, hU⟩, hSV, hU ▸ card_le_card hUS⟩,
          fun ⟨⟨hUS, hU⟩, hSV, _⟩ ↦ ⟨⟨hUS.trans hSV, hU⟩, hUS, hSV⟩⟩)
    rw [h]
    refine sum_congr rfl fun S hS ↦ ?_
    have hpos : 0 < (#S).choose κ := Nat.choose_pos (mem_filter.mp hS).2.2
    have hne : ((#S).choose κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    rw [sum_const, card_powersetCard, nsmul_eq_mul, mul_div_cancel₀ _ hne]
  rw [hident]
  refine sum_le_sum fun U hU ↦ ?_
  have hUcard : #U = κ := (mem_filter.mp hU).2.2
  rw [lowDegreeSetNormalizedInfluence, hUcard]
  refine sum_le_sum_of_subset_of_nonneg (fun S hS ↦ ?_)
    fun _ _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨_, hUS, hSV⟩ := mem_filter.mp hS
  exact mem_filter.mpr ⟨mem_univ S, hUS, (card_le_card hSV).trans hV⟩

/-! ### Noise $L^1$ Contractivity and Nearest Subset Juntas -/

/-- **$L^1$-contractivity of the Bonami–Beckner noise operator**: for `|ρ| ≤ 1`,
`𝔼 x, |noiseOp ρ f x| ≤ 𝔼 x, |f x|`. -/
theorem expect_abs_noiseOp_le {ρ : ℝ} (hρ : |ρ| ≤ 1) (f : (ι → Bool) → ℝ) :
    𝔼 x, |noiseOp ρ f x| ≤ 𝔼 x, |f x| := by
  obtain ⟨hρ1, hρ2⟩ := abs_le.mp hρ
  have hpt (x : ι → Bool) : |noiseOp ρ f x| ≤ noiseOp ρ (fun y ↦ |f y|) x := by
    have hle : noiseOp ρ f x ≤ noiseOp ρ (fun y ↦ |f y|) x := by
      have hsub := noiseOp_nonneg hρ1 hρ2 (g := fun y ↦ |f y| - f y)
        (fun y ↦ sub_nonneg.mpr (le_abs_self _)) x
      rw [noiseOp_sub] at hsub
      linarith
    have hge : -(noiseOp ρ (fun y ↦ |f y|) x) ≤ noiseOp ρ f x := by
      have hadd := noiseOp_nonneg hρ1 hρ2 (g := fun y ↦ |f y| + f y)
        (fun y ↦ by linarith [neg_abs_le (f y)]) x
      rw [noiseOp_add] at hadd
      linarith
    exact abs_le.mpr ⟨hge, hle⟩
  calc 𝔼 x, |noiseOp ρ f x|
      ≤ 𝔼 x, noiseOp ρ (fun y ↦ |f y|) x := expect_le_expect fun x _ ↦ hpt x
    _ = fourierCoeff (noiseOp ρ fun y ↦ |f y|) ∅ := (fourierCoeff_empty _).symm
    _ = 𝔼 x, |f x| := by
      rw [fourierCoeff_noiseOp, card_empty, pow_zero, one_mul, fourierCoeff_empty]

/-- The **projection** (conditional expectation) of `f : (ι → Bool) → ℝ` onto the coordinates
in `T : Finset ι`, defined as `f^{⊆ T}(x) = 𝔼 z, f (T.piecewise x z)`. -/
@[expose] noncomputable def subsetProjection (T : Finset ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    ℝ :=
  𝔼 z, f (T.piecewise x z)

/-- `subsetProjection T f` depends only on the coordinates in `T`. -/
theorem dependsOn_subsetProjection (T : Finset ι) (f : (ι → Bool) → ℝ) :
    DependsOn (subsetProjection T f) (T : Set ι) := fun _ _ hxy ↦
  expect_congr rfl fun z _ ↦ by
    rw [T.piecewise_congr (fun i hi ↦ hxy i (mem_coe.mpr hi)) fun _ _ ↦ rfl]

/-- Conditional expectation onto `T` preserves uniform pointwise bounds `|f x| ≤ B`. -/
theorem abs_subsetProjection_le {B : ℝ} {f : (ι → Bool) → ℝ} (hf : ∀ x, |f x| ≤ B)
    (T : Finset ι) (x : ι → Bool) :
    |subsetProjection T f x| ≤ B := by
  rw [subsetProjection]
  calc |𝔼 z, f (T.piecewise x z)|
      ≤ 𝔼 z, |f (T.piecewise x z)| := abs_expect_le _ _
    _ ≤ 𝔼 _z : ι → Bool, B := expect_le_expect fun z _ ↦ hf (T.piecewise x z)
    _ = B := expect_const univ_nonempty B

/-- If `f` already depends only on `T`, `subsetProjection T f` equals `f`. -/
theorem subsetProjection_eq_self_of_dependsOn {T : Finset ι} {f : (ι → Bool) → ℝ}
    (hf : DependsOn f (T : Set ι)) :
    subsetProjection T f = f := by
  ext x
  rw [subsetProjection]
  have hconst (z : ι → Bool) : f (T.piecewise x z) = f x :=
    hf fun i hi ↦ T.piecewise_eq_of_mem x z (mem_coe.mp hi)
  simp [hconst]

/-- The Fourier coefficients of `subsetProjection T f` keep `S ⊆ T` and vanish elsewhere. -/
theorem fourierCoeff_subsetProjection (T : Finset ι) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (subsetProjection T f) S = if S ⊆ T then fourierCoeff f S else 0 :=
  fourierCoeff_expect_piecewise f T S

/-- `subsetProjection T f` equals the partial Fourier expansion of `f` supported inside `T`. -/
theorem subsetProjection_eq_sum_fourierCoeff (T : Finset ι) (f : (ι → Bool) → ℝ)
    (x : ι → Bool) :
    subsetProjection T f x = ∑ S with S ⊆ T, fourierCoeff f S * chi ℝ S x :=
  expect_piecewise_eq_sum f T x

/-- Rounding `subsetProjection T f` to its sign produces a Boolean junta on `T`. -/
theorem dependsOn_signRound_subsetProjection (T : Finset ι) (f : (ι → Bool) → ℝ) :
    DependsOn (signRound (subsetProjection T f)) (T : Set ι) := fun x y hxy ↦ by
  simp only [signRound_apply, dependsOn_subsetProjection T f hxy]

omit [Fintype ι] [DecidableEq ι] in
/-- Multiplying a real number `r` by the sign of its `signRound` bit recovers `|r|`. -/
theorem mul_signVal_signRound (g : (ι → Bool) → ℝ) (x : ι → Bool) :
    g x * signVal (signRound g x) = |g x| := by
  rw [signRound_apply]
  by_cases h : g x < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.mp h)]

/-- Resampling coordinates outside `T` preserves uniform expectation over `ι → Bool`. -/
theorem expect_expect_piecewise_eq (T : Finset ι) (φ : (ι → Bool) → ℝ) :
    (𝔼 x, 𝔼 z, φ (T.piecewise x z)) = 𝔼 x, φ x := by
  rw [← expect_projectionAverage φ fun i ↦ decide (i ∈ T)]
  refine expect_congr rfl fun x _ ↦ ?_
  rw [projectionAverage_eq_expect_piecewise]
  refine expect_congr rfl fun z _ ↦ congrArg φ (funext fun i ↦ ?_)
  by_cases hi : i ∈ T <;> simp [hi]

/-- For any `T`-junta `g`, `𝔼 x, f x * g x` equals `𝔼 x, subsetProjection T f x * g x`. -/
theorem expect_mul_eq_expect_subsetProjection_mul_of_dependsOn {T : Finset ι}
    (f : (ι → Bool) → ℝ) {g : (ι → Bool) → ℝ} (hg : DependsOn g (T : Set ι)) :
    (𝔼 x, f x * g x) = 𝔼 x, subsetProjection T f x * g x := by
  rw [← expect_expect_piecewise_eq T fun x ↦ f x * g x]
  refine expect_congr rfl fun x _ ↦ ?_
  have hgT (z : ι → Bool) : g (T.piecewise x z) = g x :=
    hg fun i hi ↦ T.piecewise_eq_of_mem x z (mem_coe.mp hi)
  simp only [hgT, ← expect_mul, subsetProjection]

/-- **Maximum junta correlation bound**: every Boolean `T`-junta `g` has correlation with `f`
at most `𝔼 x, |subsetProjection T f x|`. -/
theorem expect_mul_signVal_le_expect_abs_subsetProjection {T : Finset ι}
    (f : (ι → Bool) → ℝ) {g : (ι → Bool) → Bool} (hg : DependsOn g (T : Set ι)) :
    𝔼 x, f x * signVal (g x) ≤ 𝔼 x, |subsetProjection T f x| := by
  have hg' : DependsOn (fun x ↦ signVal (g x)) (T : Set ι) :=
    fun x y hxy ↦ congrArg signVal (hg hxy)
  rw [expect_mul_eq_expect_subsetProjection_mul_of_dependsOn f hg']
  refine expect_le_expect fun x _ ↦ ?_
  rw [mul_comm]
  exact signVal_mul_le_abs (g x) (subsetProjection T f x)

/-- **Nearest `T`-junta correlation identity**: `signRound (subsetProjection T f)` achieves
correlation `𝔼 x, |subsetProjection T f x|` with `f`. -/
theorem expect_mul_signVal_signRound_subsetProjection (T : Finset ι) (f : (ι → Bool) → ℝ) :
    𝔼 x, f x * signVal (signRound (subsetProjection T f) x) =
      𝔼 x, |subsetProjection T f x| := by
  have hg' : DependsOn (fun x ↦ signVal (signRound (subsetProjection T f) x))
      (T : Set ι) :=
    fun x y hxy ↦ congrArg signVal (dependsOn_signRound_subsetProjection T f hxy)
  rw [expect_mul_eq_expect_subsetProjection_mul_of_dependsOn f hg']
  exact expect_congr rfl fun x _ ↦ mul_signVal_signRound (subsetProjection T f) x

end Influences

end CslibFrontier.BooleanAnalysis
