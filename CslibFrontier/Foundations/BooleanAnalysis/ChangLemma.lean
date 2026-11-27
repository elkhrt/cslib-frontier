/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Foundations.BooleanAnalysis.FourierMeasures

import CslibFrontier.Foundations.BooleanAnalysis.FourierBitVal
import CslibFrontier.Foundations.BooleanAnalysis.LevelK
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Chang's Lemma for Boolean Functions

This module proves Chang's lemma for Boolean functions `f : (ι → Bool) → Bool` over
any finite index type `ι` under standard Lean axioms, in both its dimension-upper-bound form
`dim(𝒮_t(f)) ≤ (8 ln 2) t^2 δ(f)^2 log₂(1 / δ(f))` and its equivalent weight-lower-bound form
`δ(f) ≥ C √d / (t √(log₂(t^2 / d)))` for small weight `δ(f) < c`, together with the monotonicity of
`η ↦ η log₂(1 / η)` on `(0, 1 / e]` used to pass between the two formulations.

## Main results

* `CslibFrontier.BooleanFunction.parityDim_largeSpectrum_le`: sharp dimension form of Chang's lemma,
  `dim(𝒮_t(f)) ≤ 8 t^2 δ(f)^2 ln(1 / δ(f))`.
* `CslibFrontier.BooleanFunction.parityDim_largeSpectrum_le_logb`: base-2 logarithm form,
  `dim(𝒮_t(f)) ≤ (8 ln 2) t^2 δ(f)^2 log₂(1 / δ(f))`.
* `CslibFrontier.BooleanFunction.monotoneOn_mul_logb_inv`: `η ↦ η log₂(1 / η)` is monotone
  non-decreasing
  on `(0, e⁻¹]`.
* `CslibFrontier.BooleanFunction.weight_bound_of_dim_bound`: derivation of the weight-lower-bound
  form
  of Chang's lemma from any dimension-upper-bound constant `C₁ > 0`.
* `CslibFrontier.BooleanFunction.dim_bound_of_weight_bound`: converse derivation of the
  dimension-upper-bound form from the weight-lower-bound form.
* `CslibFrontier.BooleanFunction.chang_boolWeight_lower_bound`: unconditional weight-lower-bound
  form of
  Chang's lemma on arbitrary finite Boolean cubes.
-/

public section

namespace CslibFrontier.BooleanFunction

open Cslib Cslib.BitString Finset Real
open scoped BigOperators

section MonotoneHelper

/-- The function `η ↦ η * ln(1 / η)` is monotone non-decreasing on `(0, e⁻¹]`. -/
theorem monotoneOn_mul_log_inv :
    MonotoneOn (fun η : ℝ ↦ η * Real.log (1 / η)) (Set.Ioc 0 (Real.exp (-1))) := by
  let g : ℝ → ℝ := fun η ↦ -η * Real.log η
  have hgeq : ∀ η : ℝ, η * Real.log (1 / η) = g η := fun η ↦ by
    simp [g, Real.log_inv]
  have hdiff : ∀ η ∈ Set.Ioc (0 : ℝ) (Real.exp (-1)),
      HasDerivAt g (-Real.log η - 1) η := by
    intro η hη
    have h1 : HasDerivAt (fun x : ℝ ↦ -x) (-1) η := (hasDerivAt_id η).neg
    have h2 : HasDerivAt Real.log η⁻¹ η := Real.hasDerivAt_log hη.1.ne'
    convert h1.mul h2 using 1
    have hne : η ≠ 0 := hη.1.ne'
    field_simp
    ring
  have hcont : ContinuousOn g (Set.Ioc 0 (Real.exp (-1))) :=
    fun η hη ↦ (hdiff η hη).continuousAt.continuousWithinAt
  have hderiv_nn : ∀ η ∈ interior (Set.Ioc (0 : ℝ) (Real.exp (-1))), 0 ≤ deriv g η := by
    intro η hη
    rw [interior_Ioc] at hη
    rw [(hdiff η ⟨hη.1, hη.2.le⟩).deriv]
    have hlog : Real.log η < -1 := by
      calc Real.log η < Real.log (Real.exp (-1)) := Real.log_lt_log hη.1 hη.2
        _ = -1 := Real.log_exp (-1)
    linarith
  have hmono : MonotoneOn g (Set.Ioc 0 (Real.exp (-1))) :=
    monotoneOn_of_deriv_nonneg (convex_Ioc 0 (Real.exp (-1))) hcont
      (fun η hη ↦ by
        rw [interior_Ioc] at hη
        exact (hdiff η ⟨hη.1, hη.2.le⟩).differentiableAt.differentiableWithinAt)
      hderiv_nn
  intro a ha b hb hab
  dsimp only
  rw [hgeq a, hgeq b]
  exact hmono ha hb hab

/-- The function `η ↦ η * log₂(1 / η)` is monotone non-decreasing on `(0, 1 / e]`. -/
theorem monotoneOn_mul_logb_inv :
    MonotoneOn (fun η : ℝ ↦ η * Real.logb 2 (1 / η)) (Set.Ioc 0 (1 / Real.exp 1)) := by
  have hexp : (1 / Real.exp 1 : ℝ) = Real.exp (-1) := by rw [Real.exp_neg, one_div]
  rw [hexp]
  intro a ha b hb hab
  have h := monotoneOn_mul_log_inv ha hb hab
  simp only [Real.logb]
  have hpos : 0 < (Real.log 2)⁻¹ := inv_pos.2 (Real.log_pos (by norm_num))
  calc a * (Real.log (1 / a) / Real.log 2)
      = (a * Real.log (1 / a)) * (Real.log 2)⁻¹ := by ring
    _ ≤ (b * Real.log (1 / b)) * (Real.log 2)⁻¹ := mul_le_mul_of_nonneg_right h hpos.le
    _ = b * (Real.log (1 / b) / Real.log 2) := by ring

/-- Elementary inequality `ln x ≤ 2 √x` for `x > 0`, bounding `ln` by `√`. -/
private theorem log_le_sqrt_mul_two {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 := Real.log_le_sub_one_of_pos hs
  have hlog : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  linarith

end MonotoneHelper

section ChangLemma

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Parseval bound on the dimension of any threshold spectrum: `dim(𝒮_t(f)) ≤ t^2`. -/
theorem parityDim_largeSpectrum_le_sq (f : (ι → Bool) → Bool) {t : ℝ} (ht : 0 < t) :
    (parityDim (largeSpectrum f t) : ℝ) ≤ t ^ 2 := by
  have hdim : (parityDim (largeSpectrum f t) : ℝ) ≤ #(largeSpectrum f t) := by
    exact_mod_cast parityDim_le_card (largeSpectrum f t)
  have hsum : (#(largeSpectrum f t) : ℝ) * (1 / t) ^ 2 ≤ 1 := by
    calc (#(largeSpectrum f t) : ℝ) * (1 / t) ^ 2
        = ∑ _ ∈ largeSpectrum f t, (1 / t) ^ 2 := by simp
      _ ≤ ∑ S ∈ largeSpectrum f t, boolFourierCoeff f S ^ 2 := by
          refine sum_le_sum fun S hS ↦ ?_
          rw [← sq_abs (boolFourierCoeff f S)]
          exact pow_le_pow_left₀ (by positivity) (mem_largeSpectrum.1 hS) 2
      _ ≤ ∑ S : Finset ι, boolFourierCoeff f S ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _
      _ = 1 := sum_boolFourierCoeff_sq f
  have hcard : (#(largeSpectrum f t) : ℝ) ≤ t ^ 2 := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    have : (#(largeSpectrum f t) : ℝ) / t ^ 2 ≤ 1 := by
      simpa [one_div, inv_pow, div_eq_mul_inv] using hsum
    exact (div_le_one ht2).1 this
  exact hdim.trans hcard

/-- If `dim(𝒮_t(f)) ≥ 1` for `t > 0`, then `0 < δ(f) < 1`. -/
theorem boolWeight_pos_and_lt_one_of_parityDim_largeSpectrum_pos
    {f : (ι → Bool) → Bool} {t : ℝ} (ht : 0 < t)
    (hd : 1 ≤ parityDim (largeSpectrum f t)) :
    0 < boolWeight f ∧ boolWeight f < 1 := by
  have hsub := largeSpectrum_subset_boolSupport (f := f) ht
  constructor
  · rcases (boolWeight_nonneg f).eq_or_lt with h0 | hp
    · exfalso
      have hfeq : f = fun _ ↦ false := funext (boolWeight_eq_zero_iff.1 h0.symm)
      rw [hfeq, boolSupport_const] at hsub
      rw [hfeq, parityDim_eq_zero_iff.2 hsub] at hd
      omega
    · exact hp
  · rcases (boolWeight_le_one f).eq_or_lt with h1 | hlt
    · exfalso
      have hfeq : f = fun _ ↦ true := funext (boolWeight_eq_one_iff.1 h1)
      rw [hfeq, boolSupport_const] at hsub
      rw [hfeq, parityDim_eq_zero_iff.2 hsub] at hd
      omega
    · exact hlt

/-- **Chang's lemma (natural-logarithm dimension form)**: for every Boolean function
`f : (ι → Bool) → Bool` and every threshold `t > 0`,
`dim(𝒮_t(f)) ≤ 8 * t^2 * δ(f)^2 * ln(1 / δ(f))`. -/
theorem parityDim_largeSpectrum_le (f : (ι → Bool) → Bool) {t : ℝ} (ht : 0 < t) :
    (parityDim (largeSpectrum f t) : ℝ) ≤
      8 * t ^ 2 * boolWeight f ^ 2 * Real.log (1 / boolWeight f) := by
  by_cases hd0 : parityDim (largeSpectrum f t) = 0
  · rw [hd0, Nat.cast_zero]
    have hδ0 := boolWeight_nonneg f
    have hδ1 := boolWeight_le_one f
    rcases hδ0.eq_or_lt with h0 | hpos
    · simp [← h0]
    · have hlog : 0 ≤ Real.log (1 / boolWeight f) :=
        Real.log_nonneg (one_le_one_div hpos hδ1)
      positivity
  obtain ⟨ℬ, hℬ_sub, hℬ_card, _, hℬ_li⟩ := exists_basis_subset_of_parityDim (largeSpectrum f t)
  obtain ⟨B, emb, hB_eq, _⟩ := exists_linearEquiv_extending_finset hℬ_li
  let h : (ι → Bool) → Bool := fourierBasisChange B f
  let A : Set (ι → Bool) := {x | h x = true}
  have hind : A.indicator (1 : (ι → Bool) → ℝ) = fun x ↦ bitVal ℝ (h x) := by
    ext x
    by_cases hx : h x = true
    · simp [A, hx, bitVal]
    · have hf : h x = false := Bool.eq_false_iff.2 hx
      simp [A, hf, bitVal]
  have hexp : 𝔼 x : ι → Bool, A.indicator (1 : (ι → Bool) → ℝ) x = boolWeight f := by
    rw [hind, ← boolWeight_eq_expect_bitVal, boolWeight_fourierBasisChange]
  have hlvl := levelWeight_one_indicator_le A
  rw [levelWeight_one, hexp] at hlvl
  have hsum_lb : (#ℬ : ℝ) * (1 / (2 * t)) ^ 2 ≤
      ∑ i : ι, fourierCoeff (A.indicator 1) {i} ^ 2 := by
    rw [hind]
    calc (#ℬ : ℝ) * (1 / (2 * t)) ^ 2
        = ∑ _ : ℬ, (1 / (2 * t)) ^ 2 := by simp
      _ ≤ ∑ S : ℬ, fourierCoeff (fun x ↦ bitVal ℝ (h x)) {emb S} ^ 2 := by
          refine sum_le_sum fun S _ ↦ ?_
          rw [fourierCoeff_bitVal_of_nonempty h (singleton_nonempty (emb S))]
          have hcoeff : boolFourierCoeff h {emb S} = boolFourierCoeff f S.1 := by
            rw [boolFourierCoeff_fourierBasisChange, hB_eq S]
            exact congr_arg (boolFourierCoeff f) (parityVecEquiv.symm_apply_apply S.1)
          change (1 / (2 * t)) ^ 2 ≤ (-boolFourierCoeff h {emb S} / 2) ^ 2
          rw [hcoeff]
          have hge : 1 / t ≤ |boolFourierCoeff f S.1| := mem_largeSpectrum.1 (hℬ_sub S.2)
          have hge2 : 1 / (2 * t) ≤ |boolFourierCoeff f S.1| / 2 := by
            have : 1 / (2 * t) = (1 / t) / 2 := by ring
            rw [this]
            linarith
          have hsq : (-boolFourierCoeff f S.1 / 2) ^ 2 = (|boolFourierCoeff f S.1| / 2) ^ 2 := by
            rw [div_pow, div_pow, neg_sq, sq_abs]
          rw [hsq]
          exact pow_le_pow_left₀ (by positivity) hge2 2
      _ = ∑ i ∈ univ.map emb, fourierCoeff (fun x ↦ bitVal ℝ (h x)) {i} ^ 2 :=
          (sum_map univ emb fun i ↦ fourierCoeff (fun x ↦ bitVal ℝ (h x)) {i} ^ 2).symm
      _ ≤ ∑ i : ι, fourierCoeff (fun x ↦ bitVal ℝ (h x)) {i} ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _
  rw [hℬ_card] at hsum_lb
  have hcomb : (parityDim (largeSpectrum f t) : ℝ) / (4 * t ^ 2) ≤
      2 * boolWeight f ^ 2 * Real.log (1 / boolWeight f) := by
    have hlhs : (parityDim (largeSpectrum f t) : ℝ) * (1 / (2 * t)) ^ 2 =
        (parityDim (largeSpectrum f t) : ℝ) / (4 * t ^ 2) := by ring
    rw [← hlhs]
    simpa only [one_div] using hsum_lb.trans hlvl
  have h4t : 0 < 4 * t ^ 2 := by positivity
  have := (div_le_iff₀ h4t).1 hcomb
  linarith

/-- **Chang's lemma (base-2 logarithm dimension form)**: for every Boolean function
`f : (ι → Bool) → Bool` and every threshold `t > 0`,
`dim(𝒮_t(f)) ≤ (8 * ln 2) * t^2 * δ(f)^2 * log₂(1 / δ(f))`. -/
theorem parityDim_largeSpectrum_le_logb (f : (ι → Bool) → Bool) {t : ℝ} (ht : 0 < t) :
    (parityDim (largeSpectrum f t) : ℝ) ≤
      (8 * Real.log 2) * t ^ 2 * boolWeight f ^ 2 * Real.logb 2 (1 / boolWeight f) := by
  have h := parityDim_largeSpectrum_le f ht
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hrhs : (8 * Real.log 2) * t ^ 2 * boolWeight f ^ 2 * Real.logb 2 (1 / boolWeight f) =
      8 * t ^ 2 * boolWeight f ^ 2 * Real.log (1 / boolWeight f) := by
    rw [Real.logb]
    field_simp
  rwa [hrhs]

end ChangLemma

section ChangEquivalence

/-- From any universal dimension bound `d ≤ C₁ * t^2 * δ(f)^2 * log₂(1 / δ(f))` (for `d > 1`),
one derives a universal threshold `c > 0` and lower-bound constant `C₂ > 0` such that whenever
`d = dim(𝒮_t(f)) > 1` and `δ(f) < c`, `1 < t^2 / d` and
`C₂ * √d / (t * √(log₂(t^2 / d))) ≤ δ(f)`. -/
theorem weight_bound_of_dim_bound
    (hdim : ∃ C₁ > (0 : ℝ), ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (f : (ι → Bool) → Bool) (t : ℝ), 0 < t → 1 < parityDim (largeSpectrum f t) →
      (parityDim (largeSpectrum f t) : ℝ) ≤
        C₁ * t ^ 2 * boolWeight f ^ 2 * Real.logb 2 (1 / boolWeight f)) :
    ∃ c > (0 : ℝ), ∃ C₂ > (0 : ℝ), ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (f : (ι → Bool) → Bool) (t : ℝ), 0 < t → 1 < parityDim (largeSpectrum f t) →
      boolWeight f < c →
      1 < t ^ 2 / (parityDim (largeSpectrum f t) : ℝ) ∧
        C₂ * (Real.sqrt (parityDim (largeSpectrum f t)) /
          (t * Real.sqrt (Real.logb 2 (t ^ 2 / parityDim (largeSpectrum f t))))) ≤
          boolWeight f := by
  obtain ⟨C₁, hC₁, hbound⟩ := hdim
  let M : ℝ := max C₁ 2
  have hM2 : 2 ≤ M := le_max_right _ _
  have hM_pos : 0 < M := by positivity
  have hMC : C₁ ≤ M := le_max_left _ _
  let c : ℝ := min (1 / 16) (1 / (4 * M))
  have hc_pos : 0 < c := by positivity
  refine ⟨c, hc_pos, 1 / Real.sqrt (2 * M), by positivity, ?_⟩
  intro ι _ _ f t ht hd hδc
  set d : ℕ := parityDim (largeSpectrum f t)
  set δ : ℝ := boolWeight f
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hraw := hbound ι f t ht hd
  have hδ_pos : 0 < δ := by
    rcases (boolWeight_nonneg f).eq_or_lt with h0 | hp
    · exfalso
      have : (d : ℝ) ≤ 0 := by simpa [d, δ, ← h0] using hraw
      linarith
    · exact hp
  have hδ_lt_16 : δ < 1 / 16 := lt_of_lt_of_le hδc (min_le_left _ _)
  have hδ_lt_M : δ < 1 / (4 * M) := lt_of_lt_of_le hδc (min_le_right _ _)
  have hinv_gt1 : 1 < 1 / δ := by rw [one_lt_div hδ_pos]; linarith
  have hlog_pos : 0 < Real.logb 2 (1 / δ) := Real.logb_pos (by norm_num) hinv_gt1
  have hd_le_M : (d : ℝ) ≤ M * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by
    have : C₁ * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) ≤
        M * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by
      gcongr
    exact hraw.trans this
  -- Bound δ * log₂(1/δ) ≤ 2 * √δ / ln 2 ≤ 4 * √δ:
  have hlog_le_sqrt : δ * Real.logb 2 (1 / δ) ≤ 4 * Real.sqrt δ := by
    rw [Real.logb]
    have h1 := log_le_sqrt_mul_two (one_div_pos.2 hδ_pos)
    rw [one_div, Real.sqrt_inv] at h1
    have hln2 : (1 / 2 : ℝ) < Real.log 2 := by
      have h1 : (2 : ℝ)⁻¹ < Real.exp (-1 / 2) := by
        linarith [Real.add_one_lt_exp (show (-1 / 2 : ℝ) ≠ 0 by norm_num)]
      have h2 : Real.exp (1 / 2) < 2 := by
        rw [show (1 / 2 : ℝ) = -(-1 / 2) by ring, Real.exp_neg]
        exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).2 h1
      rwa [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
    have h2 : Real.log δ⁻¹ / Real.log 2 ≤ 4 * (Real.sqrt δ)⁻¹ := by
      rw [div_le_iff₀ (Real.log_pos (by norm_num))]
      have hln : 0 ≤ (Real.sqrt δ)⁻¹ := by positivity
      calc Real.log δ⁻¹ ≤ 2 * (Real.sqrt δ)⁻¹ := h1
        _ = 4 * (Real.sqrt δ)⁻¹ * (1 / 2) := by ring
        _ ≤ 4 * (Real.sqrt δ)⁻¹ * Real.log 2 :=
            mul_le_mul_of_nonneg_left hln2.le (by positivity)
    calc δ * (Real.log (1 / δ) / Real.log 2)
        ≤ δ * (4 * (Real.sqrt δ)⁻¹) := by
          rw [one_div]; exact mul_le_mul_of_nonneg_left h2 hδ_pos.le
      _ = (Real.sqrt δ * Real.sqrt δ) * (4 * (Real.sqrt δ)⁻¹) := by
          rw [Real.mul_self_sqrt hδ_pos.le]
      _ = 4 * Real.sqrt δ := by
          have hs : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.2 hδ_pos).ne'
          field_simp
  -- Therefore M * δ^2 * log₂(1/δ) = (M * δ) * (δ * log₂(1/δ)) < (1/4) * (4 * (1/4)) = 1/4 < 1/2!
  have hMδ : M * δ < 1 / 4 := by
    have := (lt_div_iff₀ (by positivity : 0 < 4 * M)).1 hδ_lt_M
    linarith
  have hsqrtδ : Real.sqrt δ < 1 / 4 := by
    calc Real.sqrt δ < Real.sqrt (1 / 16) := Real.sqrt_lt_sqrt hδ_pos.le hδ_lt_16
      _ = 1 / 4 := by
          rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hprod_small : M * δ * (δ * Real.logb 2 (1 / δ)) ≤ 1 / 4 := by
    have h4 : δ * Real.logb 2 (1 / δ) ≤ 1 := by linarith
    calc M * δ * (δ * Real.logb 2 (1 / δ))
        ≤ (1 / 4) * 1 := mul_le_mul hMδ.le h4 (by positivity) (by norm_num)
      _ = 1 / 4 := by ring
  -- Also t^2 / d ≥ 1 / (M * δ^2 * log₂(1/δ)) ≥ 1 / (M * δ * 1) = 1 / (M * δ) and also ≥ 1 / √δ:
  have hprod_le_inv : M * δ ^ 2 * Real.logb 2 (1 / δ) ≤ Real.sqrt δ := by
    calc M * δ ^ 2 * Real.logb 2 (1 / δ)
        = (M * δ) * (δ * Real.logb 2 (1 / δ)) := by ring
      _ ≤ (1 / 4) * (4 * Real.sqrt δ) :=
          mul_le_mul hMδ.le hlog_le_sqrt (by positivity) (by norm_num)
      _ = Real.sqrt δ := by ring
  have hprod_pos : 0 < M * δ ^ 2 * Real.logb 2 (1 / δ) := by positivity
  have hratio_ge : 1 / Real.sqrt δ ≤ t ^ 2 / (d : ℝ) := by
    have h1 : (d : ℝ) ≤ t ^ 2 * Real.sqrt δ := by
      calc (d : ℝ) ≤ t ^ 2 * (M * δ ^ 2 * Real.logb 2 (1 / δ)) := by linarith
        _ ≤ t ^ 2 * Real.sqrt δ := mul_le_mul_of_nonneg_left hprod_le_inv (sq_nonneg t)
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 hδ_pos) hd_pos, one_mul]
    linarith
  have hratio_gt1 : 1 < t ^ 2 / (d : ℝ) := by
    have : (4 : ℝ) < 1 / Real.sqrt δ := by
      rw [lt_div_iff₀ (Real.sqrt_pos.2 hδ_pos)]
      linarith
    linarith
  have hlog_ratio : (1 / 2) * Real.logb 2 (1 / δ) ≤ Real.logb 2 (t ^ 2 / (d : ℝ)) := by
    have hsqrt_inv : Real.logb 2 (1 / Real.sqrt δ) = (1 / 2) * Real.logb 2 (1 / δ) := by
      simp only [Real.logb, one_div, Real.log_inv, Real.log_sqrt hδ_pos.le]
      ring
    rw [← hsqrt_inv]
    exact Real.logb_le_logb_of_le (by norm_num) (by positivity) hratio_ge
  refine ⟨hratio_gt1, ?_⟩
  have hlog_r_pos : 0 < Real.logb 2 (t ^ 2 / (d : ℝ)) :=
    Real.logb_pos (by norm_num) hratio_gt1
  have hsq_bound : (d : ℝ) / (t ^ 2 * Real.logb 2 (t ^ 2 / (d : ℝ))) ≤ 2 * M * δ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    calc (d : ℝ) ≤ (2 * M * δ ^ 2 * t ^ 2) * ((1 / 2) * Real.logb 2 (1 / δ)) := by linarith
      _ ≤ (2 * M * δ ^ 2 * t ^ 2) * Real.logb 2 (t ^ 2 / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog_ratio (by positivity)
      _ = 2 * M * δ ^ 2 * (t ^ 2 * Real.logb 2 (t ^ 2 / (d : ℝ))) := by ring
  have hsq_lhs : (1 / Real.sqrt (2 * M) *
      (Real.sqrt d / (t * Real.sqrt (Real.logb 2 (t ^ 2 / (d : ℝ)))))) ^ 2 ≤ δ ^ 2 := by
    rw [mul_pow, div_pow, div_pow, mul_pow, one_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt hd_pos.le, Real.sq_sqrt hlog_r_pos.le]
    have h2M : 0 < 2 * M := by positivity
    rw [one_div, inv_mul_le_iff₀ h2M]
    exact hsq_bound
  exact le_of_sq_le_sq hsq_lhs hδ_pos.le

/-- Converse equivalence: from any universal weight-lower-bound form of Chang's lemma, one derives
the universal dimension upper bound `d ≤ C₁ * t^2 * δ(f)^2 * log₂(1 / δ(f))` for all `d > 1`. -/
theorem dim_bound_of_weight_bound
    (hwt : ∃ c > (0 : ℝ), ∃ C₂ > (0 : ℝ), ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (f : (ι → Bool) → Bool) (t : ℝ), 0 < t → 1 < parityDim (largeSpectrum f t) →
      boolWeight f < c →
      C₂ * (Real.sqrt (parityDim (largeSpectrum f t)) /
        (t * Real.sqrt (Real.logb 2 (t ^ 2 / parityDim (largeSpectrum f t))))) ≤
        boolWeight f) :
    ∃ C₁ > (0 : ℝ), ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (f : (ι → Bool) → Bool) (t : ℝ), 0 < t → 1 < parityDim (largeSpectrum f t) →
      (parityDim (largeSpectrum f t) : ℝ) ≤
        C₁ * t ^ 2 * boolWeight f ^ 2 * Real.logb 2 (1 / boolWeight f) := by
  obtain ⟨c, hc, C₂, hC₂, hlb⟩ := hwt
  let c₀ : ℝ := min c (1 / 2)
  have hc₀_pos : 0 < c₀ := lt_min hc (by norm_num)
  have hc₀_le_c : c₀ ≤ c := min_le_left _ _
  have hc₀_le_half : c₀ ≤ 1 / 2 := min_le_right _ _
  have hc₀2_lt_1 : c₀ ^ 2 < 1 := by nlinarith
  have hc₀2_pos : 0 < c₀ ^ 2 := sq_pos_of_pos hc₀_pos
  have hc₀2_le_e : c₀ ^ 2 ≤ 1 / Real.exp 1 := by
    have he : Real.exp 1 < 4 := by
      have h1 : (2 : ℝ)⁻¹ < Real.exp (-1 / 2) := by
        linarith [Real.add_one_lt_exp (show (-1 / 2 : ℝ) ≠ 0 by norm_num)]
      have h2 : Real.exp (1 / 2) < 2 := by
        rw [show (1 / 2 : ℝ) = -(-1 / 2) by ring, Real.exp_neg]
        exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).2 h1
      calc Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by rw [← Real.exp_add]; norm_num
        _ < 2 * 2 := mul_lt_mul'' h2 h2 (Real.exp_nonneg _) (Real.exp_nonneg _)
        _ = 4 := by norm_num
    have h4 : c₀ ^ 2 ≤ 1 / 4 := by nlinarith
    have hinv : (1 / 4 : ℝ) ≤ 1 / Real.exp 1 :=
      one_div_le_one_div_of_le (Real.exp_pos 1) he.le
    exact h4.trans hinv
  have hlog_c₀ : 0 < c₀ ^ 2 * Real.logb 2 (1 / c₀ ^ 2) :=
    mul_pos hc₀2_pos (Real.logb_pos (by norm_num) (by rw [one_lt_div hc₀2_pos]; exact hc₀2_lt_1))
  let C_mid : ℝ := 2 / (c₀ ^ 2 * Real.logb 2 (1 / c₀ ^ 2))
  let C_low : ℝ := 2 * max (1 / C₂ ^ 2) (1 / min (C₂ ^ 2) 1)
  let C_hi : ℝ := 8 * Real.log 2
  let C₁ : ℝ := max (max C_mid C_low) C_hi
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le (by dsimp [C_hi]; positivity) (le_max_right _ _)
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro ι _ _ f t ht hd
  set d : ℕ := parityDim (largeSpectrum f t)
  set δ : ℝ := boolWeight f
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd_le_t2 : (d : ℝ) ≤ t ^ 2 := parityDim_largeSpectrum_le_sq f ht
  by_cases hδ_half : 1 / 2 < δ
  · -- Case δ > 1/2: Parseval on non-empty sets gives d / t^2 ≤ 4 δ (1 - δ) and ln(1/δ) ≥ 1 - δ.
    have hδ_lt1 : δ < 1 := by
      rcases (boolWeight_le_one f).eq_or_lt with h1 | hlt
      · exfalso
        have hfeq : f = fun _ ↦ true := funext (boolWeight_eq_one_iff.1 h1)
        have hsub := largeSpectrum_subset_boolSupport (f := f) ht
        rw [hfeq, boolSupport_const] at hsub
        have : d = 0 := by
          change parityDim (largeSpectrum f t) = 0
          rw [hfeq]
          exact parityDim_eq_zero_iff.2 hsub
        omega
      · exact hlt
    obtain ⟨ℬ, hℬ_sub, hℬ_card, _, hℬ_li⟩ := exists_basis_subset_of_parityDim (largeSpectrum f t)
    have hne : ∅ ∉ ℬ := empty_notMem_of_linearIndependent hℬ_li
    have hparseval : (d : ℝ) * (1 / t) ^ 2 ≤ 4 * δ * (1 - δ) := by
      have hd_eq : d = #ℬ := hℬ_card.symm
      have hsum_ne : ∑ S : Finset ι with S ≠ ∅, boolFourierCoeff f S ^ 2 = 4 * δ * (1 - δ) :=
        sum_nonempty_boolFourierCoeff_sq f
      rw [hd_eq, ← hsum_ne]
      calc (#ℬ : ℝ) * (1 / t) ^ 2
          = ∑ _ ∈ ℬ, (1 / t) ^ 2 := by simp
        _ ≤ ∑ S ∈ ℬ, boolFourierCoeff f S ^ 2 := by
            refine sum_le_sum fun S hS ↦ ?_
            rw [← sq_abs (boolFourierCoeff f S)]
            exact pow_le_pow_left₀ (by positivity) (mem_largeSpectrum.1 (hℬ_sub hS)) 2
        _ ≤ ∑ S : Finset ι with S ≠ ∅, boolFourierCoeff f S ^ 2 := by
            refine sum_le_sum_of_subset_of_nonneg (fun S hS ↦ ?_) fun _ _ _ ↦ sq_nonneg _
            simp only [mem_filter, mem_univ, true_and]
            rintro rfl
            exact hne hS
    have h1sub : 1 - δ ≤ Real.log (1 / δ) := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < δ)
      rw [one_div, Real.log_inv]
      linarith
    have hd_le : (d : ℝ) ≤ (8 * Real.log 2) * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by
      have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
      have h1 : (d : ℝ) ≤ t ^ 2 * (4 * δ * (1 - δ)) := by
        have hdiv : (d : ℝ) / t ^ 2 ≤ 4 * δ * (1 - δ) := by
          simpa [one_div, inv_pow, div_eq_mul_inv] using hparseval
        linarith [(div_le_iff₀ ht2).1 hdiv]
      have h2 : 4 * δ * (1 - δ) ≤ 8 * δ ^ 2 * Real.log (1 / δ) := by
        calc 4 * δ * (1 - δ) ≤ 8 * δ ^ 2 * (1 - δ) := by nlinarith
          _ ≤ 8 * δ ^ 2 * Real.log (1 / δ) :=
              mul_le_mul_of_nonneg_left h1sub (by positivity)
      have h3 : (d : ℝ) ≤ 8 * t ^ 2 * δ ^ 2 * Real.log (1 / δ) := by nlinarith
      have hrw : (8 * Real.log 2) * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) =
          8 * t ^ 2 * δ ^ 2 * Real.log (1 / δ) := by
        rw [Real.logb]
        have hln2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
        field_simp
      rw [hrw]
      exact h3
    have hChi_le : C_hi ≤ C₁ := le_max_right _ _
    have hlog_nn : 0 ≤ Real.logb 2 (1 / δ) :=
      Real.logb_nonneg (by norm_num) (one_le_one_div (by linarith) hδ_lt1.le)
    calc (d : ℝ) ≤ C_hi * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := hd_le
      _ ≤ C₁ * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by gcongr
  · push Not at hδ_half
    by_cases hδ_c₀ : c₀ ≤ δ
    · -- Case 1: c₀ ≤ δ ≤ 1/2.
      have hδ2_mem : δ ^ 2 ∈ Set.Ioc (0 : ℝ) (1 / Real.exp 1) := by
        refine ⟨sq_pos_of_pos (lt_of_lt_of_le hc₀_pos hδ_c₀), ?_⟩
        have h1 : (2 : ℝ)⁻¹ < Real.exp (-1 / 2) := by
          linarith [Real.add_one_lt_exp (show (-1 / 2 : ℝ) ≠ 0 by norm_num)]
        have h2 : Real.exp (1 / 2) < 2 := by
          rw [show (1 / 2 : ℝ) = -(-1 / 2) by ring, Real.exp_neg]
          exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).2 h1
        have he : Real.exp 1 < 4 := by
          calc Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
                rw [← Real.exp_add]; norm_num
            _ < 2 * 2 := mul_lt_mul'' h2 h2 (Real.exp_nonneg _) (Real.exp_nonneg _)
            _ = 4 := by norm_num
        exact (show δ ^ 2 ≤ 1 / 4 by nlinarith).trans
          (one_div_le_one_div_of_le (Real.exp_pos 1) he.le)
      have hc₀2_mem : c₀ ^ 2 ∈ Set.Ioc (0 : ℝ) (1 / Real.exp 1) := ⟨hc₀2_pos, hc₀2_le_e⟩
      have hmono := monotoneOn_mul_logb_inv hc₀2_mem hδ2_mem
        (sq_le_sq' (by linarith) hδ_c₀)
      have hlogsq : Real.logb 2 (1 / δ ^ 2) = 2 * Real.logb 2 (1 / δ) := by
        rw [one_div, one_div, Real.logb_inv, Real.logb_inv, Real.logb_pow]
        ring
      have hCmid_le : C_mid ≤ C₁ := (le_max_left _ _).trans (le_max_left _ _)
      have hδ_pos : 0 < δ := lt_of_lt_of_le hc₀_pos hδ_c₀
      have hlog_nn : 0 ≤ Real.logb 2 (1 / δ) :=
        Real.logb_nonneg (by norm_num) (one_le_one_div hδ_pos (by linarith))
      calc (d : ℝ) ≤ t ^ 2 := hd_le_t2
        _ = (C_mid / 2) * t ^ 2 * (c₀ ^ 2 * Real.logb 2 (1 / c₀ ^ 2)) := by
            dsimp [C_mid]
            have hc₀ne : c₀ ≠ 0 := hc₀_pos.ne'
            have hlne : Real.logb 2 (1 / c₀ ^ 2) ≠ 0 := right_ne_zero_of_mul hlog_c₀.ne'
            field_simp
        _ ≤ (C_mid / 2) * t ^ 2 * (δ ^ 2 * Real.logb 2 (1 / δ ^ 2)) :=
            mul_le_mul_of_nonneg_left hmono (by dsimp [C_mid]; positivity)
        _ = C_mid * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by rw [hlogsq]; ring
        _ ≤ C₁ * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by gcongr
    · -- Case 2: 0 ≤ δ < c₀ ≤ min(c, 1/2).
      push Not at hδ_c₀
      have hδ_lt_c : δ < c := lt_of_lt_of_le hδ_c₀ hc₀_le_c
      have hw := hlb ι f t ht hd hδ_lt_c
      have hratio_ge1 : 1 ≤ t ^ 2 / (d : ℝ) := (one_le_div hd_pos).2 hd_le_t2
      have hClow_le : C_low ≤ C₁ := (le_max_right _ _).trans (le_max_left _ _)
      have hδ_pos : 0 < δ := by
        rcases (boolWeight_nonneg f).eq_or_lt with h0 | hp
        · exfalso
          have hfeq : f = fun _ ↦ false := funext (boolWeight_eq_zero_iff.1 h0.symm)
          have hsub := largeSpectrum_subset_boolSupport (f := f) ht
          rw [hfeq, boolSupport_const] at hsub
          have : d = 0 := by
            change parityDim (largeSpectrum f t) = 0
            rw [hfeq]
            exact parityDim_eq_zero_iff.2 hsub
          omega
        · exact hp
      have hlogδ_ge1 : 1 ≤ Real.logb 2 (1 / δ) := by
        calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
          _ ≤ Real.logb 2 (1 / δ) :=
              Real.logb_le_logb_of_le (by norm_num) (by norm_num)
                (by rw [le_div_iff₀ hδ_pos]; linarith)
      have hlogr_pos : 0 < Real.logb 2 (t ^ 2 / (d : ℝ)) := by
        by_contra hle
        push Not at hle
        have heq : t ^ 2 / (d : ℝ) = 1 := by
          apply le_antisymm _ hratio_ge1
          by_contra hgt
          push Not at hgt
          linarith [Real.logb_pos (by norm_num : (1 : ℝ) < 2) hgt]
        -- If t^2 = d, parseval forces supp(f) = ℬ linearly independent, contradicting |supp| ≥ 4;
        -- easier: t^2 = d implies d = #𝒮_t and ∑_{S ∈ 𝒮_t} f̂(S)^2 = 1 so ∅ ∉ supp(f) and δ = 1/2 ≥
        -- c₀!
        have ht2_eq : t ^ 2 = d := (div_eq_one_iff_eq hd_pos.ne').1 heq
        have hcard_eq : #(largeSpectrum f t) = d := by
          refine le_antisymm ?_ (parityDim_le_card _)
          have hsum : (#(largeSpectrum f t) : ℝ) * (1 / t) ^ 2 ≤ 1 := by
            calc (#(largeSpectrum f t) : ℝ) * (1 / t) ^ 2
                = ∑ _ ∈ largeSpectrum f t, (1 / t) ^ 2 := by simp
              _ ≤ ∑ S ∈ largeSpectrum f t, boolFourierCoeff f S ^ 2 :=
                  sum_le_sum fun S hS ↦ by
                    rw [← sq_abs (boolFourierCoeff f S)]
                    exact pow_le_pow_left₀ (by positivity) (mem_largeSpectrum.1 hS) 2
              _ ≤ 1 := (sum_le_sum_of_subset_of_nonneg (subset_univ _)
                  fun _ _ _ ↦ sq_nonneg _).trans_eq (sum_boolFourierCoeff_sq f)
          have : (#(largeSpectrum f t) : ℝ) ≤ d := by
            rw [← ht2_eq]
            exact (div_le_one (sq_pos_of_pos ht)).1
              (by simpa [one_div, inv_pow, div_eq_mul_inv] using hsum)
          exact_mod_cast this
        obtain ⟨ℬ, hℬ_sub, hℬ_card, _, hℬ_li⟩ :=
          exists_basis_subset_of_parityDim (largeSpectrum f t)
        have hℬ_eq : ℬ = largeSpectrum f t := eq_of_subset_of_card_le hℬ_sub (by omega)
        have h0_not : (∅ : Finset ι) ∉ largeSpectrum f t :=
          hℬ_eq ▸ empty_notMem_of_linearIndependent hℬ_li
        have h0_zero : boolFourierCoeff f ∅ = 0 := by
          have hsum1 : ∑ S ∈ largeSpectrum f t, boolFourierCoeff f S ^ 2 = 1 := by
            apply le_antisymm
            · exact (sum_le_sum_of_subset_of_nonneg (subset_univ _)
                fun _ _ _ ↦ sq_nonneg _).trans_eq (sum_boolFourierCoeff_sq f)
            · calc (1 : ℝ) = (d : ℝ) / t ^ 2 := by rw [ht2_eq, div_self hd_pos.ne']
                _ = ∑ _ ∈ largeSpectrum f t, (1 / t) ^ 2 := by
                    simp [hcard_eq, inv_pow, div_eq_mul_inv]
                _ ≤ ∑ S ∈ largeSpectrum f t, boolFourierCoeff f S ^ 2 :=
                    sum_le_sum fun S hS ↦ by
                      rw [← sq_abs (boolFourierCoeff f S)]
                      exact pow_le_pow_left₀ (by positivity) (mem_largeSpectrum.1 hS) 2
          have hrest : ∑ S ∈ univ \ largeSpectrum f t, boolFourierCoeff f S ^ 2 = 0 := by
            have := sum_sdiff (subset_univ (largeSpectrum f t))
              (f := fun S ↦ boolFourierCoeff f S ^ 2)
            rw [sum_boolFourierCoeff_sq f, hsum1] at this
            linarith
          have h0sq : boolFourierCoeff f ∅ ^ 2 = 0 :=
            le_antisymm
              ((single_le_sum (fun _ _ ↦ sq_nonneg _)
                (mem_sdiff.2 ⟨mem_univ _, h0_not⟩)).trans_eq hrest)
              (sq_nonneg _)
          exact sq_eq_zero_iff.1 h0sq
        rw [boolFourierCoeff_empty] at h0_zero
        linarith
      have hsq_wt : C₂ ^ 2 * ((d : ℝ) / (t ^ 2 * Real.logb 2 (t ^ 2 / (d : ℝ)))) ≤ δ ^ 2 := by
        change C₂ * (Real.sqrt d / (t * Real.sqrt (Real.logb 2 (t ^ 2 / d)))) ≤ δ at hw
        have := pow_le_pow_left₀ (by positivity) hw 2
        simpa [mul_pow, div_pow, Real.sq_sqrt hd_pos.le, Real.sq_sqrt hlogr_pos.le] using this
      by_cases hr2 : t ^ 2 / (d : ℝ) < 2
      · have hlogr_le1 : Real.logb 2 (t ^ 2 / (d : ℝ)) ≤ 1 := by
          calc Real.logb 2 (t ^ 2 / (d : ℝ)) ≤ Real.logb 2 2 :=
                Real.logb_le_logb_of_le (by norm_num) (by positivity) hr2.le
            _ = 1 := Real.logb_self_eq_one (by norm_num)
        have hd_le : (d : ℝ) ≤ (1 / C₂ ^ 2) * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by
          have h1 : (d : ℝ) ≤ (1 / C₂ ^ 2) * δ ^ 2 * (t ^ 2 * Real.logb 2 (t ^ 2 / (d : ℝ))) := by
            have h2 := (div_le_iff₀ (by positivity :
              0 < t ^ 2 * Real.logb 2 (t ^ 2 / (d : ℝ)))).1
              ((le_div_iff₀' (sq_pos_of_pos hC₂)).2 hsq_wt)
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h2
          calc (d : ℝ) ≤ (1 / C₂ ^ 2) * t ^ 2 * δ ^ 2 * 1 := by nlinarith [sq_pos_of_pos hC₂]
            _ ≤ (1 / C₂ ^ 2) * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) :=
                mul_le_mul_of_nonneg_left hlogδ_ge1 (by positivity)
        have hle_C₁ : 1 / C₂ ^ 2 ≤ C₁ := by
          have : 1 / C₂ ^ 2 ≤ C_low := by
            dsimp [C_low]
            linarith [le_max_left (1 / C₂ ^ 2) (1 / min (C₂ ^ 2) 1),
              show 0 < 1 / C₂ ^ 2 by positivity]
          exact this.trans hClow_le
        calc (d : ℝ) ≤ (1 / C₂ ^ 2) * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := hd_le
          _ ≤ C₁ * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by gcongr
      · push Not at hr2
        have hlogr_ge1 : 1 ≤ Real.logb 2 (t ^ 2 / (d : ℝ)) := by
          calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
            _ ≤ Real.logb 2 (t ^ 2 / (d : ℝ)) :=
                Real.logb_le_logb_of_le (by norm_num) (by norm_num) hr2
        let α : ℝ := min (C₂ ^ 2) 1
        have hα_pos : 0 < α := lt_min (sq_pos_of_pos hC₂) zero_lt_one
        have hα_le1 : α ≤ 1 := min_le_right _ _
        have hα_leC : α ≤ C₂ ^ 2 := min_le_left _ _
        let η₀ : ℝ := α * ((d : ℝ) / (t ^ 2 * Real.logb 2 (t ^ 2 / (d : ℝ))))
        have hη₀_le : η₀ ≤ δ ^ 2 :=
          (mul_le_mul_of_nonneg_right hα_leC (by positivity)).trans hsq_wt
        have hη₀_pos : 0 < η₀ := by positivity
        have hδ2_le_e : δ ^ 2 ≤ 1 / Real.exp 1 := by
          have h1 : (2 : ℝ)⁻¹ < Real.exp (-1 / 2) := by
            linarith [Real.add_one_lt_exp (show (-1 / 2 : ℝ) ≠ 0 by norm_num)]
          have h2 : Real.exp (1 / 2) < 2 := by
            rw [show (1 / 2 : ℝ) = -(-1 / 2) by ring, Real.exp_neg]
            exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).2 h1
          have he : Real.exp 1 < 4 := by
            calc Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
                  rw [← Real.exp_add]; norm_num
              _ < 2 * 2 := mul_lt_mul'' h2 h2 (Real.exp_nonneg _) (Real.exp_nonneg _)
              _ = 4 := by norm_num
          exact (show δ ^ 2 ≤ 1 / 4 by nlinarith).trans
            (one_div_le_one_div_of_le (Real.exp_pos 1) he.le)
        have hmono := monotoneOn_mul_logb_inv ⟨hη₀_pos, hη₀_le.trans hδ2_le_e⟩
          ⟨sq_pos_of_pos hδ_pos, hδ2_le_e⟩ hη₀_le
        have hinv_ge : t ^ 2 / (d : ℝ) ≤ 1 / η₀ := by
          dsimp [η₀]
          rw [le_div_iff₀ hη₀_pos]
          have : (t ^ 2 / (d : ℝ)) * (α * ((d : ℝ) / (t ^ 2 * Real.logb 2 (t ^ 2 / (d : ℝ))))) =
              α / Real.logb 2 (t ^ 2 / (d : ℝ)) := by
            have ht2ne : t ^ 2 ≠ 0 := (sq_pos_of_pos ht).ne'
            have hdne : (d : ℝ) ≠ 0 := hd_pos.ne'
            have hlne : Real.logb 2 (t ^ 2 / (d : ℝ)) ≠ 0 := hlogr_pos.ne'
            field_simp
          rw [this, div_le_one hlogr_pos]
          exact hα_le1.trans hlogr_ge1
        have hlog_inv : Real.logb 2 (t ^ 2 / (d : ℝ)) ≤ Real.logb 2 (1 / η₀) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hinv_ge
        have hprod : α * (d : ℝ) / t ^ 2 ≤ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by
          have hlogsq : δ ^ 2 * Real.logb 2 (1 / δ ^ 2) = 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by
            rw [one_div, one_div, Real.logb_inv, Real.logb_inv, Real.logb_pow]
            ring
          rw [← hlogsq]
          refine le_trans ?_ hmono
          calc α * (d : ℝ) / t ^ 2 = η₀ * Real.logb 2 (t ^ 2 / (d : ℝ)) := by
                dsimp [η₀]
                have hlne := hlogr_pos.ne'
                field_simp
            _ ≤ η₀ * Real.logb 2 (1 / η₀) := mul_le_mul_of_nonneg_left hlog_inv hη₀_pos.le
        have hd_le : (d : ℝ) ≤ (2 / α) * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by
          have h1 := (div_le_iff₀ (sq_pos_of_pos ht)).1 hprod
          have h2 : (d : ℝ) ≤ (1 / α) * (2 * δ ^ 2 * Real.logb 2 (1 / δ) * t ^ 2) := by
            rw [one_div, le_inv_mul_iff₀ hα_pos]
            exact h1
          calc (d : ℝ) ≤ (1 / α) * (2 * δ ^ 2 * Real.logb 2 (1 / δ) * t ^ 2) := h2
            _ = (2 / α) * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by ring
        have h2α_le : 2 / α ≤ C₁ := by
          have : 2 / α ≤ C_low := by
            have hmx : 1 / α ≤ max (1 / C₂ ^ 2) (1 / α) := le_max_right _ _
            change 2 / α ≤ 2 * max (1 / C₂ ^ 2) (1 / α)
            calc 2 / α = 2 * (1 / α) := by ring
              _ ≤ 2 * max (1 / C₂ ^ 2) (1 / α) := by linarith
          exact this.trans hClow_le
        calc (d : ℝ) ≤ (2 / α) * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := hd_le
          _ ≤ C₁ * t ^ 2 * δ ^ 2 * Real.logb 2 (1 / δ) := by gcongr

/-- **Chang's lemma (weight lower-bound form)**: there exist universal constants `c > 0` and
`C > 0` such that for every finite type `ι`, every Boolean function `f : (ι → Bool) → Bool`, and
every `t > 0`, if `d = dim(𝒮_t(f)) > 1` and `δ(f) < c`, then `1 < t^2 / d` and
`C * √d / (t * √(log₂(t^2 / d))) ≤ δ(f)`. -/
theorem chang_boolWeight_lower_bound :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (f : (ι → Bool) → Bool) (t : ℝ), 0 < t → 1 < parityDim (largeSpectrum f t) →
      boolWeight f < c →
      1 < t ^ 2 / (parityDim (largeSpectrum f t) : ℝ) ∧
        C * (Real.sqrt (parityDim (largeSpectrum f t)) /
          (t * Real.sqrt (Real.logb 2 (t ^ 2 / parityDim (largeSpectrum f t))))) ≤
          boolWeight f :=
  weight_bound_of_dim_bound
    ⟨8 * Real.log 2, by positivity, fun _ _ _ f _ ht _ ↦ parityDim_largeSpectrum_le_logb f ht⟩

end ChangEquivalence

end CslibFrontier.BooleanFunction
