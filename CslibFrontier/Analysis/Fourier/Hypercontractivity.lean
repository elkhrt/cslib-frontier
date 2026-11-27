/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import CslibFrontier.Analysis.Fourier.EfronStein
public import CslibFrontier.Analysis.Fourier.FiniteProduct

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hypercontractivity over Finite Weighted Product Spaces

This module proves `(2, q)`-hypercontractivity for low-degree functions on finite weighted
product probability spaces `(ι → A, ν^⊗ι)` under standard Lean axioms.

## Main definitions

* `CslibFrontier.Analysis.Fourier.hypercontractivityRho`: explicit noise parameter `ρ(k, α) > 0`
  for `(2, 2k)`-hypercontractivity on finite probability spaces with minimum atom mass `α`.
* `CslibFrontier.Analysis.Fourier.hypercontractivityConst`: explicit constant `C(q, α) > 0` for
  degree-`d` `(2, q)`-hypercontractivity.

## Main results

* `CslibFrontier.Analysis.Fourier.singleSite_hypercontractivity_even`: single-coordinate `(2, 2k,
  ρ)`
  hypercontractivity `E_ν[‖c + ρ g‖^{2k}] ≤ (‖c‖² + E_ν[‖g‖²])^k`.
* `CslibFrontier.Analysis.Fourier.noiseOp_hypercontractivity_even`: tensorized `(2, 2k, ρ)`
  hypercontractivity `‖T_ρ f‖_{2k} ≤ ‖f‖₂` on `(ι → A, ν^⊗ι)`.
* `CslibFrontier.Analysis.Fourier.hypercontractivity_of_deg`: for every `q ≥ 2`, `α > 0`, and
  degree-`d` function `f`, `‖f‖_q ≤ C(q, α)^d ‖f‖₂`.
-/

public section

open Finset BigOperators

namespace CslibFrontier.Analysis.Fourier

section SingleSite

/-- Explicit noise parameter `ρ = √α / (16 * 4^k)` ensuring single-site `(2, 2k)`
hypercontractivity on any finite probability space with atom weights `≥ α`. -/
@[expose] noncomputable def hypercontractivityRho (k : ℕ) (α : ℝ) : ℝ :=
  Real.sqrt α / (16 * (4 : ℝ) ^ k)

lemma hypercontractivityRho_eq_div (k : ℕ) (α : ℝ) :
    hypercontractivityRho k α = Real.sqrt α / (16 * (4 : ℝ) ^ k) :=
  rfl

/-- Explicit hypercontractivity constant `C(q, α) = (hypercontractivityRho ⌈q/2⌉₊ α)⁻¹`. -/
@[expose] noncomputable def hypercontractivityConst (q α : ℝ) : ℝ :=
  (hypercontractivityRho (Nat.ceil (q / 2)) α)⁻¹

private lemma atom_lb_le_one {A : Type*} (ν : PMF A) {α : ℝ}
    (hmin : ∀ a ∈ ν.support, α ≤ (ν a).toReal) : α ≤ 1 := by
  obtain ⟨a₀, ha₀⟩ := ν.support_nonempty
  exact (hmin a₀ ha₀).trans
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one ν a₀))

lemma hypercontractivityRho_pos (k : ℕ) {α : ℝ} (hα : 0 < α) :
    0 < hypercontractivityRho k α := by
  unfold hypercontractivityRho
  positivity

lemma hypercontractivityRho_le_one (k : ℕ) {α : ℝ} (_hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    hypercontractivityRho k α ≤ 1 := by
  unfold hypercontractivityRho
  have hsq : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
  have hden : (1 : ℝ) ≤ 16 * (4 : ℝ) ^ k := by
    have : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    linarith
  exact (div_le_one (by positivity)).mpr (hsq.trans hden)

lemma hypercontractivityConst_pos (q : ℝ) {α : ℝ} (hα : 0 < α) :
    0 < hypercontractivityConst q α :=
  inv_pos.mpr (hypercontractivityRho_pos _ hα)

/-- Elementary domination: for `a, σ ≥ 0` and `2 ≤ j ≤ 2k` (`k ≥ 2`),
`a^{2k - j} σ^j ≤ a^{2k - 2} σ^2 + σ^{2k}`. -/
private lemma pow_dom_two_or_top {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 ≤ σ) {k j : ℕ}
    (hj2 : 2 ≤ j) (hjk : j ≤ 2 * k) :
    a ^ (2 * k - j) * σ ^ j ≤ a ^ (2 * k - 2) * σ ^ 2 + σ ^ (2 * k) := by
  rcases le_total σ a with h | h
  · have h1 : a ^ (2 * k - j) * σ ^ j ≤ a ^ (2 * k - 2) * σ ^ 2 := by
      have heq : σ ^ j = σ ^ (j - 2) * σ ^ 2 := by
        rw [← pow_add, Nat.sub_add_cancel hj2]
      have haeq : a ^ (2 * k - 2) = a ^ (2 * k - j) * a ^ (j - 2) := by
        rw [← pow_add]
        congr 1; omega
      rw [heq, haeq]
      have hpow : σ ^ (j - 2) ≤ a ^ (j - 2) := pow_le_pow_left₀ hσ h (j - 2)
      calc a ^ (2 * k - j) * (σ ^ (j - 2) * σ ^ 2)
          ≤ a ^ (2 * k - j) * (a ^ (j - 2) * σ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hpow (pow_nonneg hσ 2))
              (pow_nonneg ha (2 * k - j))
        _ = a ^ (2 * k - j) * a ^ (j - 2) * σ ^ 2 := by ring
    linarith [pow_nonneg hσ (2 * k)]
  · have h2 : a ^ (2 * k - j) * σ ^ j ≤ σ ^ (2 * k) := by
      have hpow : a ^ (2 * k - j) ≤ σ ^ (2 * k - j) := pow_le_pow_left₀ ha h (2 * k - j)
      calc a ^ (2 * k - j) * σ ^ j
          ≤ σ ^ (2 * k - j) * σ ^ j :=
            mul_le_mul_of_nonneg_right hpow (pow_nonneg hσ j)
        _ = σ ^ (2 * k) := by rw [← pow_add, Nat.sub_add_cancel hjk]
    linarith [mul_nonneg (pow_nonneg ha (2 * k - 2)) (pow_nonneg hσ 2)]

/-- Single-site `(2, 2k, ρ)`-hypercontractivity: for any finite probability space `(A, ν)` with
`∀ a, α ≤ (ν a).toReal`, `0 < α ≤ 1`, `k ≥ 1`, `ρ = hypercontractivityRho k α`, and any
`c : ℂ`, `g : A → ℂ` with `∑ a, ν(a) g(a) = 0`:
`∑ a, ν(a) ‖c + ρ g(a)‖^{2k} ≤ (‖c‖² + ∑ a, ν(a) ‖g(a)‖²)^k`. -/
theorem singleSite_hypercontractivity_even {A : Type*} [Fintype A] (ν : PMF A)
    {α : ℝ} (hα0 : 0 < α) (hmin : ∀ a ∈ ν.support, α ≤ (ν a).toReal)
    {k : ℕ} (hk : 1 ≤ k) (c : ℂ) (g : A → ℂ)
    (hg0 : ∑ a : A, ((ν a).toReal : ℂ) * g a = 0) :
    ∑ a : A, (ν a).toReal * ‖c + (hypercontractivityRho k α : ℂ) * g a‖ ^ (2 * k) ≤
      (‖c‖ ^ 2 + ∑ a : A, (ν a).toReal * ‖g a‖ ^ 2) ^ k := by
  have hα1 : α ≤ 1 := atom_lb_le_one ν hmin
  set ρ := hypercontractivityRho k α
  have hρ0 : 0 ≤ ρ := (hypercontractivityRho_pos k hα0).le
  have hρ1 : ρ ≤ 1 := hypercontractivityRho_le_one k hα0.le hα1
  set a_norm := ‖c‖
  set σsq := ∑ a : A, (ν a).toReal * ‖g a‖ ^ 2
  have hσsq : 0 ≤ σsq := Finset.sum_nonneg fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  set σ := Real.sqrt σsq
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ_sq : σ ^ 2 = σsq := Real.sq_sqrt hσsq
  have ha_norm0 : 0 ≤ a_norm := norm_nonneg c
  -- Pointwise bound: `‖g a‖ ≤ σ / √α` for every `a ∈ ν.support`.
  have hg_sup : ∀ a ∈ ν.support, ‖g a‖ ≤ σ / Real.sqrt α := by
    intro a ha
    have h1 : α * ‖g a‖ ^ 2 ≤ σsq := by
      calc α * ‖g a‖ ^ 2 ≤ (ν a).toReal * ‖g a‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hmin a ha) (sq_nonneg _)
        _ ≤ σsq := by
            dsimp only [σsq]
            exact Finset.single_le_sum (f := fun b : A ↦ (ν b).toReal * ‖g b‖ ^ 2)
              (fun b _ ↦ mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) (Finset.mem_univ a)
    have hsq : ‖g a‖ ^ 2 ≤ (σ / Real.sqrt α) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hα0.le, hσ_sq]
      exact (le_div_iff₀ hα0).mpr (by linarith)
    exact (abs_le_of_sq_le_sq' (by nlinarith [hsq, norm_nonneg (g a)]) (by positivity)).2
  -- Moment bound: `E[‖g‖^m] ≤ σ^m / (√α)^{m-2}` for all `m ≥ 2`.
  have hmom : ∀ m : ℕ, 2 ≤ m →
      ∑ a : A, (ν a).toReal * ‖g a‖ ^ m ≤ σ ^ m / (Real.sqrt α) ^ (m - 2) := by
    intro m hm
    have hpt : ∀ a : A, (ν a).toReal * ‖g a‖ ^ m ≤
        (ν a).toReal * ‖g a‖ ^ 2 * (σ / Real.sqrt α) ^ (m - 2) := by
      intro a
      by_cases ha : a ∈ ν.support
      · have hpow : ‖g a‖ ^ m = ‖g a‖ ^ 2 * ‖g a‖ ^ (m - 2) := by
          rw [← pow_add, Nat.add_sub_cancel' hm]
        rw [hpow, ← mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
        exact pow_le_pow_left₀ (norm_nonneg _) (hg_sup a ha) (m - 2)
      · have h0 : (ν a).toReal = 0 := by
          rw [PMF.mem_support_iff, not_not] at ha; simp [ha]
        simp [h0]
    calc ∑ a : A, (ν a).toReal * ‖g a‖ ^ m
        ≤ ∑ a : A, (ν a).toReal * ‖g a‖ ^ 2 * (σ / Real.sqrt α) ^ (m - 2) :=
          Finset.sum_le_sum fun a _ ↦ hpt a
      _ = σsq * (σ / Real.sqrt α) ^ (m - 2) := by rw [← Finset.sum_mul]
      _ = σ ^ m / (Real.sqrt α) ^ (m - 2) := by
          rw [← hσ_sq, div_pow, mul_div_assoc', ← pow_add, Nat.add_sub_cancel' hm]
  -- Expand `‖c + ρ g a‖^{2k} = (A² + u a)^k` where `u a = 2 ρ Re(conj c * g a) + ρ² ‖g a‖²`.
  let u : A → ℝ := fun a ↦ 2 * ρ * (starRingEnd ℂ c * g a).re + ρ ^ 2 * ‖g a‖ ^ 2
  have hnorm_sq : ∀ a : A, ‖c + (ρ : ℂ) * g a‖ ^ 2 = a_norm ^ 2 + u a := by
    intro a
    simp only [u, a_norm]
    have h0 : ‖c + (ρ : ℂ) * g a‖ ^ 2 = Complex.normSq (c + (ρ : ℂ) * g a) :=
      (Complex.normSq_eq_norm_sq _).symm
    rw [h0, Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    have hre' : (c * starRingEnd ℂ ((ρ : ℂ) * g a)).re = ρ * (starRingEnd ℂ c * g a).re := by
      have : c * starRingEnd ℂ ((ρ : ℂ) * g a) =
          (ρ : ℂ) * starRingEnd ℂ (starRingEnd ℂ c * g a) := by simp; ring
      rw [this, Complex.re_ofReal_mul, Complex.conj_re]
    rw [hre']
    ring
  -- Mean of `u`: `E[u] = ρ² σ²`.
  have hu_mean : ∑ a : A, (ν a).toReal * u a = ρ ^ 2 * σsq := by
    have hre0 : ∑ a : A, (ν a).toReal * (starRingEnd ℂ c * g a).re = 0 := by
      have hc0 : ∑ a : A, ((ν a).toReal : ℂ) * (starRingEnd ℂ c * g a) = 0 := by
        have : (∑ a : A, ((ν a).toReal : ℂ) * (starRingEnd ℂ c * g a)) =
            starRingEnd ℂ c * ∑ a : A, ((ν a).toReal : ℂ) * g a := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ ↦ ?_; ring
        rw [this, hg0, mul_zero]
      have h := congr_arg Complex.re hc0
      simp only [Complex.re_sum, Complex.zero_re] at h
      simpa [Complex.re_ofReal_mul] using h
    simp only [u, mul_add, Finset.sum_add_distrib]
    rw [show (∑ a : A, (ν a).toReal * (2 * ρ * (starRingEnd ℂ c * g a).re)) =
        2 * ρ * ∑ a : A, (ν a).toReal * (starRingEnd ℂ c * g a).re by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ ↦ ?_; ring]
    rw [hre0, mul_zero, zero_add]
    rw [show (∑ a : A, (ν a).toReal * (ρ ^ 2 * ‖g a‖ ^ 2)) =
        ρ ^ 2 * ∑ a : A, (ν a).toReal * ‖g a‖ ^ 2 by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ ↦ ?_; ring]
  -- Case `k = 1`: immediate!
  rcases eq_or_lt_of_le hk with rfl | hk2
  · simp only [Nat.mul_one, pow_one]
    simp_rw [hnorm_sq, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pmf_toReal,
      one_mul]
    rw [hu_mean]
    have : ρ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  -- Case `k ≥ 2`: expand `(A² + u a)^k` via binomial theorem!
  have hLHS : ∑ a : A, (ν a).toReal * ‖c + (ρ : ℂ) * g a‖ ^ (2 * k) =
      a_norm ^ (2 * k) + (k : ℝ) * a_norm ^ (2 * k - 2) * (ρ ^ 2 * σsq) +
        ∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j),
          ((k.choose j : ℝ) * a_norm ^ (2 * k - 2 * j)) *
            ∑ a : A, (ν a).toReal * u a ^ j := by
    have hpow : ∀ a : A, ‖c + (ρ : ℂ) * g a‖ ^ (2 * k) = (u a + a_norm ^ 2) ^ k := fun a ↦ by
      rw [pow_mul, hnorm_sq, add_comm]
    simp_rw [hpow, add_pow, Finset.mul_sum]
    rw [Finset.sum_comm]
    -- Split off `j = 0` and `j = 1` from `range (k + 1)`.
    have hsplit : Finset.range (k + 1) =
        {0, 1} ∪ (Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j) := by
      ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_filter]
      omega
    have hdisj : Disjoint ({0, 1} : Finset ℕ) ((Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j)) := by
      rw [Finset.disjoint_left]; intro j hj1 hj2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj1
      simp only [Finset.mem_filter] at hj2; omega
    conv_lhs => rw [hsplit, Finset.sum_union hdisj]
    have h01 : (∑ j ∈ ({0, 1} : Finset ℕ), ∑ a : A,
        (ν a).toReal * (u a ^ j * (a_norm ^ 2) ^ (k - j) * (k.choose j : ℝ))) =
        a_norm ^ (2 * k) + (k : ℝ) * a_norm ^ (2 * k - 2) * (ρ ^ 2 * σsq) := by
      rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
      simp only [Nat.sub_zero, pow_zero, one_mul, mul_one, Nat.choose_zero_right, Nat.cast_one,
        pow_one, Nat.choose_one_right]
      congr 1
      · rw [← Finset.sum_mul, sum_pmf_toReal, one_mul, ← pow_mul]
      · rw [← hu_mean, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [← pow_mul, show 2 * (k - 1) = 2 * k - 2 by omega]; ring
    rw [h01]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← pow_mul, show 2 * (k - j) = 2 * k - 2 * j by omega]; ring
  rw [hLHS]
  -- Bound each `j ≥ 2` moment of `u`:
  -- `|u a| ≤ 2 ρ A ‖g a‖ + ρ² ‖g a‖²`, hence `|u a|^j ≤ 2^j ((2 ρ A ‖g a‖)^j + (ρ² ‖g a‖²)^j)`.
  have hu_bound : ∀ j : ℕ, 2 ≤ j → j ≤ k →
      a_norm ^ (2 * k - 2 * j) * ∑ a : A, (ν a).toReal * u a ^ j ≤
        (a_norm ^ (2 * k - 2) * σsq + σsq ^ k) * (ρ ^ 2 / α * (2 * (4 : ℝ) ^ j)) := by
    intro j hj2 hjk
    have hpt : ∀ a : A, u a ^ j ≤
        (2 : ℝ) ^ j * ((2 * ρ * a_norm * ‖g a‖) ^ j + (ρ ^ 2 * ‖g a‖ ^ 2) ^ j) := by
      intro a
      have hub : |u a| ≤ 2 * ρ * a_norm * ‖g a‖ + ρ ^ 2 * ‖g a‖ ^ 2 := by
        have hre_le : |(starRingEnd ℂ c * g a).re| ≤ a_norm * ‖g a‖ := by
          calc |(starRingEnd ℂ c * g a).re| ≤ ‖starRingEnd ℂ c * g a‖ := Complex.abs_re_le_norm _
            _ = a_norm * ‖g a‖ := by rw [norm_mul, Complex.norm_conj]
        have h1 : |u a| ≤ |2 * ρ * (starRingEnd ℂ c * g a).re| + |ρ ^ 2 * ‖g a‖ ^ 2| :=
          abs_add_le _ _
        refine h1.trans ?_
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ρ),
          abs_of_nonneg (by positivity : 0 ≤ ρ ^ 2 * ‖g a‖ ^ 2)]
        nlinarith
      have hmax : (2 * ρ * a_norm * ‖g a‖ + ρ ^ 2 * ‖g a‖ ^ 2) ^ j ≤
          (2 : ℝ) ^ j * ((2 * ρ * a_norm * ‖g a‖) ^ j + (ρ ^ 2 * ‖g a‖ ^ 2) ^ j) := by
        set x := 2 * ρ * a_norm * ‖g a‖
        set y := ρ ^ 2 * ‖g a‖ ^ 2
        have hx : 0 ≤ x := by positivity
        have hy : 0 ≤ y := by positivity
        have hxy : x + y ≤ 2 * max x y := by
          have := le_max_left x y; have := le_max_right x y; linarith
        calc (x + y) ^ j ≤ (2 * max x y) ^ j := pow_le_pow_left₀ (by positivity) hxy j
          _ = 2 ^ j * (max x y) ^ j := mul_pow _ _ _
          _ ≤ 2 ^ j * (x ^ j + y ^ j) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rcases max_cases x y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
              · linarith [pow_nonneg hy j]
              · linarith [pow_nonneg hx j]
      calc u a ^ j ≤ |u a| ^ j := le_trans (le_abs_self _) (by rw [← abs_pow])
        _ ≤ (2 * ρ * a_norm * ‖g a‖ + ρ ^ 2 * ‖g a‖ ^ 2) ^ j :=
          pow_le_pow_left₀ (abs_nonneg _) hub j
        _ ≤ _ := hmax
    have hsum_u : ∑ a : A, (ν a).toReal * u a ^ j ≤
        (2 : ℝ) ^ j * ((2 * ρ * a_norm) ^ j * (σ ^ j / (Real.sqrt α) ^ (j - 2)) +
          (ρ ^ 2) ^ j * (σ ^ (2 * j) / (Real.sqrt α) ^ (2 * j - 2))) := by
      calc ∑ a : A, (ν a).toReal * u a ^ j
          ≤ ∑ a : A, (ν a).toReal *
              ((2 : ℝ) ^ j * ((2 * ρ * a_norm * ‖g a‖) ^ j + (ρ ^ 2 * ‖g a‖ ^ 2) ^ j)) :=
            Finset.sum_le_sum fun a _ ↦
              mul_le_mul_of_nonneg_left (hpt a) ENNReal.toReal_nonneg
        _ = (2 : ℝ) ^ j * ((2 * ρ * a_norm) ^ j * (∑ a : A, (ν a).toReal * ‖g a‖ ^ j) +
              (ρ ^ 2) ^ j * (∑ a : A, (ν a).toReal * ‖g a‖ ^ (2 * j))) := by
            simp_rw [mul_pow, mul_add, ← pow_mul, Finset.sum_add_distrib, Finset.mul_sum]
            congr 1 <;> refine Finset.sum_congr rfl fun a _ ↦ by ring
        _ ≤ (2 : ℝ) ^ j * ((2 * ρ * a_norm) ^ j * (σ ^ j / (Real.sqrt α) ^ (j - 2)) +
              (ρ ^ 2) ^ j * (σ ^ (2 * j) / (Real.sqrt α) ^ (2 * j - 2))) := by
            gcongr
            · exact hmom j hj2
            · exact hmom (2 * j) (by omega)
    have hA_term : a_norm ^ (2 * k - 2 * j) * ((2 * ρ * a_norm) ^ j * (σ ^ j / (Real.sqrt α) ^ (j -
      2))) ≤
        (a_norm ^ (2 * k - 2) * σsq + σsq ^ k) * ((2 * ρ) ^ j / (Real.sqrt α) ^ (j - 2)) := by
      have hpowA : a_norm ^ (2 * k - 2 * j) * ((2 * ρ * a_norm) ^ j * (σ ^ j / (Real.sqrt α) ^ (j -
        2))) =
          (a_norm ^ (2 * k - j) * σ ^ j) * ((2 * ρ) ^ j / (Real.sqrt α) ^ (j - 2)) := by
        rw [mul_pow]
        have hcomb : a_norm ^ (2 * k - 2 * j) * ((2 * ρ) ^ j * a_norm ^ j) =
            (2 * ρ) ^ j * a_norm ^ (2 * k - j) := by
          rw [show a_norm ^ (2 * k - 2 * j) * ((2 * ρ) ^ j * a_norm ^ j) =
              (2 * ρ) ^ j * (a_norm ^ (2 * k - 2 * j) * a_norm ^ j) by ring, ← pow_add]
          congr 2; omega
        calc a_norm ^ (2 * k - 2 * j) * ((2 * ρ) ^ j * a_norm ^ j * (σ ^ j / Real.sqrt α ^ (j - 2)))
            = (a_norm ^ (2 * k - 2 * j) * ((2 * ρ) ^ j * a_norm ^ j)) *
                (σ ^ j / Real.sqrt α ^ (j - 2)) := by ring
          _ = ((2 * ρ) ^ j * a_norm ^ (2 * k - j)) * (σ ^ j / Real.sqrt α ^ (j - 2)) := by
                rw [hcomb]
          _ = (a_norm ^ (2 * k - j) * σ ^ j) * ((2 * ρ) ^ j / Real.sqrt α ^ (j - 2)) := by ring
      rw [hpowA]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hdom := pow_dom_two_or_top ha_norm0 hσ0 hj2 (by omega : j ≤ 2 * k)
      rwa [show σ ^ (2 * k) = σsq ^ k by rw [pow_mul, hσ_sq], hσ_sq] at hdom
    have hB_term : a_norm ^ (2 * k - 2 * j) *
        ((ρ ^ 2) ^ j * (σ ^ (2 * j) / (Real.sqrt α) ^ (2 * j - 2))) ≤
        (a_norm ^ (2 * k - 2) * σsq + σsq ^ k) * ((ρ ^ 2) ^ j / (Real.sqrt α) ^ (2 * j - 2)) := by
      have hpowB : a_norm ^ (2 * k - 2 * j) *
          ((ρ ^ 2) ^ j * (σ ^ (2 * j) / (Real.sqrt α) ^ (2 * j - 2))) =
          (a_norm ^ (2 * k - 2 * j) * σ ^ (2 * j)) * ((ρ ^ 2) ^ j / (Real.sqrt α) ^ (2 * j -
            2)) := by
        ring
      rw [hpowB]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hdom := pow_dom_two_or_top ha_norm0 hσ0 (by omega : 2 ≤ 2 * j) (by omega : 2 * j ≤ 2 * k)
      rwa [show σ ^ (2 * k) = σsq ^ k by rw [pow_mul, hσ_sq], hσ_sq] at hdom
    -- Compare coefficients: `2^j * ((2ρ)^j / √α^{j-2} + ρ^{2j} / √α^{2j-2}) ≤ ρ² / α * (2 * 4^j)`.
    have hcoeff : (2 : ℝ) ^ j * ((2 * ρ) ^ j / (Real.sqrt α) ^ (j - 2) +
        (ρ ^ 2) ^ j / (Real.sqrt α) ^ (2 * j - 2)) ≤ ρ ^ 2 / α * (2 * (4 : ℝ) ^ j) := by
      have hρ_le_sqα : ρ ≤ Real.sqrt α := by
        unfold ρ hypercontractivityRho
        have hden : (1 : ℝ) ≤ 16 * (4 : ℝ) ^ k := by
          have : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num); linarith
        exact div_le_self (Real.sqrt_nonneg α) hden
      have hratio1 : (ρ / Real.sqrt α) ^ (j - 2) ≤ 1 :=
        pow_le_one₀ (by positivity) ((div_le_one (Real.sqrt_pos.mpr hα0)).mpr hρ_le_sqα)
      have hratio2 : (ρ / Real.sqrt α) ^ (2 * j - 2) ≤ 1 :=
        pow_le_one₀ (by positivity) ((div_le_one (Real.sqrt_pos.mpr hα0)).mpr hρ_le_sqα)
      have ht1 : (2 * ρ) ^ j / (Real.sqrt α) ^ (j - 2) ≤ (2 : ℝ) ^ j * (ρ ^ 2 / α) := by
        rw [mul_pow]
        have h1 : ρ ^ j / (Real.sqrt α) ^ (j - 2) = ρ ^ 2 * (ρ / Real.sqrt α) ^ (j - 2) := by
          rw [div_pow, mul_div_assoc', ← pow_add, Nat.add_sub_cancel' hj2]
        rw [mul_div_assoc, h1]
        have h2 : ρ ^ 2 * (ρ / Real.sqrt α) ^ (j - 2) ≤ ρ ^ 2 / α := by
          have hαinv : (1 : ℝ) ≤ α⁻¹ := (one_le_inv₀ hα0).mpr hα1
          calc ρ ^ 2 * (ρ / Real.sqrt α) ^ (j - 2) ≤ ρ ^ 2 * 1 := by gcongr
            _ = ρ ^ 2 := mul_one _
            _ ≤ ρ ^ 2 * α⁻¹ := by nlinarith [sq_nonneg ρ]
            _ = ρ ^ 2 / α := by rw [div_eq_mul_inv]
        gcongr
      have ht2 : (ρ ^ 2) ^ j / (Real.sqrt α) ^ (2 * j - 2) ≤ ρ ^ 2 / α := by
        rw [← pow_mul]
        have h1 : ρ ^ (2 * j) / (Real.sqrt α) ^ (2 * j - 2) =
            ρ ^ 2 * (ρ / Real.sqrt α) ^ (2 * j - 2) := by
          rw [div_pow, mul_div_assoc', ← pow_add, Nat.add_sub_cancel' (by omega)]
        rw [h1]
        have hαinv : (1 : ℝ) ≤ α⁻¹ := (one_le_inv₀ hα0).mpr hα1
        calc ρ ^ 2 * (ρ / Real.sqrt α) ^ (2 * j - 2) ≤ ρ ^ 2 * 1 := by gcongr
          _ = ρ ^ 2 := mul_one _
          _ ≤ ρ ^ 2 * α⁻¹ := by nlinarith [sq_nonneg ρ]
          _ = ρ ^ 2 / α := by rw [div_eq_mul_inv]
      have h4 : (2 : ℝ) ^ j * ((2 : ℝ) ^ j + 1) ≤ 2 * (4 : ℝ) ^ j := by
        have h21 : (2 : ℝ) ^ j + 1 ≤ (2 : ℝ) ^ j + (2 : ℝ) ^ j := by
          have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num); linarith
        have h2j : (2 : ℝ) ^ j * ((2 : ℝ) ^ j + (2 : ℝ) ^ j) = 2 * (4 : ℝ) ^ j := by
          rw [show (4 : ℝ) ^ j = (2 : ℝ) ^ j * (2 : ℝ) ^ j by
            rw [← mul_pow]; norm_num]; ring
        calc (2 : ℝ) ^ j * ((2 : ℝ) ^ j + 1) ≤ (2 : ℝ) ^ j * ((2 : ℝ) ^ j + (2 : ℝ) ^ j) := by
              gcongr
          _ = 2 * (4 : ℝ) ^ j := h2j
      calc (2 : ℝ) ^ j * ((2 * ρ) ^ j / (Real.sqrt α) ^ (j - 2) +
            (ρ ^ 2) ^ j / (Real.sqrt α) ^ (2 * j - 2))
          ≤ (2 : ℝ) ^ j * ((2 : ℝ) ^ j * (ρ ^ 2 / α) + ρ ^ 2 / α) := by gcongr
        _ = (ρ ^ 2 / α) * ((2 : ℝ) ^ j * ((2 : ℝ) ^ j + 1)) := by ring
        _ ≤ (ρ ^ 2 / α) * (2 * (4 : ℝ) ^ j) := by gcongr
    calc a_norm ^ (2 * k - 2 * j) * ∑ a : A, (ν a).toReal * u a ^ j
        ≤ a_norm ^ (2 * k - 2 * j) * ((2 : ℝ) ^ j *
            ((2 * ρ * a_norm) ^ j * (σ ^ j / (Real.sqrt α) ^ (j - 2)) +
              (ρ ^ 2) ^ j * (σ ^ (2 * j) / (Real.sqrt α) ^ (2 * j - 2)))) :=
          mul_le_mul_of_nonneg_left hsum_u (pow_nonneg ha_norm0 _)
      _ = (2 : ℝ) ^ j *
            (a_norm ^ (2 * k - 2 * j) * ((2 * ρ * a_norm) ^ j * (σ ^ j / (Real.sqrt α) ^ (j - 2))) +
              a_norm ^ (2 * k - 2 * j) * ((ρ ^ 2) ^ j * (σ ^ (2 * j) / (Real.sqrt α) ^ (2 * j -
                2)))) := by
          ring
      _ ≤ (2 : ℝ) ^ j *
            ((a_norm ^ (2 * k - 2) * σsq + σsq ^ k) * ((2 * ρ) ^ j / (Real.sqrt α) ^ (j - 2)) +
              (a_norm ^ (2 * k - 2) * σsq + σsq ^ k) *
                ((ρ ^ 2) ^ j / (Real.sqrt α) ^ (2 * j - 2))) := by
          gcongr
      _ = (a_norm ^ (2 * k - 2) * σsq + σsq ^ k) * ((2 : ℝ) ^ j *
            ((2 * ρ) ^ j / (Real.sqrt α) ^ (j - 2) +
              (ρ ^ 2) ^ j / (Real.sqrt α) ^ (2 * j - 2))) := by ring
      _ ≤ (a_norm ^ (2 * k - 2) * σsq + σsq ^ k) * (ρ ^ 2 / α * (2 * (4 : ℝ) ^ j)) := by gcongr
  -- Sum over `2 ≤ j ≤ k`: total tail coefficient is at most `1/2`.
  have htail_sum : ∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j),
      ((k.choose j : ℝ) * a_norm ^ (2 * k - 2 * j)) * ∑ a : A, (ν a).toReal * u a ^ j ≤
      (1 / 2 : ℝ) * (a_norm ^ (2 * k - 2) * σsq + σsq ^ k) := by
    calc ∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j),
          ((k.choose j : ℝ) * a_norm ^ (2 * k - 2 * j)) * ∑ a : A, (ν a).toReal * u a ^ j
        = ∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j),
          (k.choose j : ℝ) * (a_norm ^ (2 * k - 2 * j) * ∑ a : A, (ν a).toReal * u a ^ j) := by
          refine Finset.sum_congr rfl fun j _ ↦ by ring
      _ ≤ ∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j),
          (k.choose j : ℝ) *
            ((a_norm ^ (2 * k - 2) * σsq + σsq ^ k) * (ρ ^ 2 / α * (2 * (4 : ℝ) ^ j))) := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          exact mul_le_mul_of_nonneg_left (hu_bound j hj.2 (by omega)) (Nat.cast_nonneg _)
      _ ≤ ∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j),
          (k.choose j : ℝ) *
            ((a_norm ^ (2 * k - 2) * σsq + σsq ^ k) * (ρ ^ 2 / α * (2 * (4 : ℝ) ^ k))) := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          have hpow4 : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
          gcongr
      _ = ((∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j), (k.choose j : ℝ)) *
            (ρ ^ 2 / α * (2 * (4 : ℝ) ^ k))) * (a_norm ^ (2 * k - 2) * σsq + σsq ^ k) := by
          rw [← Finset.sum_mul]; ring
      _ ≤ (1 / 2 : ℝ) * (a_norm ^ (2 * k - 2) * σsq + σsq ^ k) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hch : ∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j), (k.choose j : ℝ) ≤
              (2 : ℝ) ^ k := by
            calc ∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ 2 ≤ j), (k.choose j : ℝ)
                ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                    fun _ _ _ ↦ Nat.cast_nonneg _
              _ = (2 : ℝ) ^ k := by exact_mod_cast Nat.sum_range_choose k
          have h8 : (2 : ℝ) ^ k * (ρ ^ 2 / α * (2 * (4 : ℝ) ^ k)) ≤ (1 / 2 : ℝ) := by
            unfold ρ hypercontractivityRho
            rw [div_pow, Real.sq_sqrt hα0.le, mul_pow]
            have h4sq : ((4 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k * (4 : ℝ) ^ k := sq _
            have h24 : (2 : ℝ) ^ k ≤ (4 : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
            have h4pos : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
            have hαne : α ≠ 0 := ne_of_gt hα0
            have hsimp : (2 : ℝ) ^ k * (α / ((16 : ℝ) ^ 2 * ((4 : ℝ) ^ k) ^ 2) / α *
                (2 * (4 : ℝ) ^ k)) = (2 : ℝ) ^ k / (128 * (4 : ℝ) ^ k) := by
              field_simp [hαne, ne_of_gt h4pos]
              ring
            rw [hsimp, div_le_iff₀ (by positivity)]
            linarith
          have hnonneg : 0 ≤ ρ ^ 2 / α * (2 * (4 : ℝ) ^ k) := by positivity
          exact (mul_le_mul_of_nonneg_right hch hnonneg).trans h8
  -- Compare with `(A² + σsq)^k ≥ A^{2k} + k A^{2k - 2} σsq + σsq^k`.
  have hRHS : a_norm ^ (2 * k) + (k : ℝ) * a_norm ^ (2 * k - 2) * σsq + σsq ^ k ≤
    (a_norm ^ 2 + σsq) ^ k := by
    conv_rhs => rw [add_comm, add_pow]
    have hsub : ({0, 1, k} : Finset ℕ) ⊆ Finset.range (k + 1) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_range]
      omega
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity)
    rw [Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega : (1 : ℕ) ≠ k)]
    simp only [Nat.sub_zero, pow_zero, one_mul, mul_one, Nat.choose_zero_right, Nat.cast_one,
      pow_one, Nat.choose_one_right, Nat.sub_self, Nat.choose_self]
    rw [← pow_mul, ← pow_mul, show 2 * (k - 1) = 2 * k - 2 by omega]
    ring_nf; linarith
  have hρ_half : ρ ^ 2 ≤ (1 / 2 : ℝ) := by
    have h1 : ρ ≤ 1 / 16 := by
      unfold ρ hypercontractivityRho
      have hsq : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
      have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      calc Real.sqrt α / (16 * (4 : ℝ) ^ k) ≤ 1 / (16 * 1) := by gcongr
        _ = 1 / 16 := by ring
    nlinarith
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hcoef : (k : ℝ) * ρ ^ 2 + (1 / 2 : ℝ) ≤ (k : ℝ) := by nlinarith
  have hterm1 : ((k : ℝ) * ρ ^ 2 + (1 / 2 : ℝ)) * (a_norm ^ (2 * k - 2) * σsq) ≤
      (k : ℝ) * (a_norm ^ (2 * k - 2) * σsq) :=
    mul_le_mul_of_nonneg_right hcoef (mul_nonneg (pow_nonneg ha_norm0 _) hσsq)
  linarith [pow_nonneg hσsq k]

/-- Minkowski inequality in `L^k` for a finite nonnegative weighted sum:
`(∑ x, w x * (∑ a, p a * h a x)^k)^{1/k} ≤ ∑ a, p a * (∑ x, w x * (h a x)^k)^{1/k}`. -/
private lemma minkowski_weighted_pow {α β : Type*} [Fintype α] [Fintype β]
    {k : ℕ} (hk : 1 ≤ k) {p : α → ℝ} (hp : ∀ a, 0 ≤ p a)
    {w : β → ℝ} (hw : ∀ x, 0 ≤ w x) {h : α → β → ℝ} (hh : ∀ a x, 0 ≤ h a x) :
    (∑ x : β, w x * (∑ a : α, p a * h a x) ^ k) ^ ((1 : ℝ) / k) ≤
      ∑ a : α, p a * (∑ x : β, w x * (h a x) ^ k) ^ ((1 : ℝ) / k) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  let : Fact (1 ≤ (k : ENNReal)) := ⟨by exact_mod_cast hk⟩
  let v : α → PiLp (k : ENNReal) (fun _ : β ↦ ℝ) :=
    fun a ↦ WithLp.toLp (k : ENNReal) (fun x ↦ p a * (w x) ^ ((1 : ℝ) / k) * h a x)
  have hnorm : ∀ u : PiLp (k : ENNReal) (fun _ : β ↦ ℝ),
      ‖u‖ = (∑ x : β, |u x| ^ k) ^ ((1 : ℝ) / k) := fun u ↦ by
    rw [PiLp.norm_eq_sum (by exact_mod_cast hk_pos)]
    simp
  have hv_norm : ∀ a : α, ‖v a‖ = p a * (∑ x : β, w x * (h a x) ^ k) ^ ((1 : ℝ) / k) := by
    intro a
    rw [hnorm]
    have hsum : ∑ x : β, |v a x| ^ k = p a ^ k * ∑ x : β, w x * (h a x) ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hnn : 0 ≤ p a * (w x) ^ ((1 : ℝ) / k) * h a x :=
        mul_nonneg (mul_nonneg (hp a) (Real.rpow_nonneg (hw x) _)) (hh a x)
      simp only [v, abs_of_nonneg hnn]
      rw [mul_pow, mul_pow, ← Real.rpow_natCast ((w x) ^ _), ← Real.rpow_mul (hw x)]
      simp only [one_div_mul_cancel (ne_of_gt hk_pos), Real.rpow_one]
      ring
    rw [hsum, Real.mul_rpow (pow_nonneg (hp a) k)
      (Finset.sum_nonneg fun x _ ↦ mul_nonneg (hw x) (pow_nonneg (hh a x) k)),
      ← Real.rpow_natCast (p a), ← Real.rpow_mul (hp a), mul_one_div_cancel (ne_of_gt hk_pos),
      Real.rpow_one]
  have hsum_norm : ‖∑ a : α, v a‖ =
      (∑ x : β, w x * (∑ a : α, p a * h a x) ^ k) ^ ((1 : ℝ) / k) := by
    rw [hnorm]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hval : (∑ a : α, v a) x = (w x) ^ ((1 : ℝ) / k) * ∑ a : α, p a * h a x := by
      rw [Finset.mul_sum]
      simp only [WithLp.ofLp_sum, Finset.sum_apply, v]
      refine Finset.sum_congr rfl fun a _ ↦ by ring
    rw [hval]
    have hnn : 0 ≤ (w x) ^ ((1 : ℝ) / k) * ∑ a : α, p a * h a x :=
      mul_nonneg (Real.rpow_nonneg (hw x) _)
        (Finset.sum_nonneg fun a _ ↦ mul_nonneg (hp a) (hh a x))
    rw [abs_of_nonneg hnn, mul_pow, ← Real.rpow_natCast ((w x) ^ _), ← Real.rpow_mul (hw x),
      one_div_mul_cancel (ne_of_gt hk_pos), Real.rpow_one]
  calc (∑ x : β, w x * (∑ a : α, p a * h a x) ^ k) ^ ((1 : ℝ) / k)
      = ‖∑ a : α, v a‖ := hsum_norm.symm
    _ ≤ ∑ a : α, ‖v a‖ := norm_sum_le _ _
    _ = ∑ a : α, p a * (∑ x : β, w x * (h a x) ^ k) ^ ((1 : ℝ) / k) :=
        Finset.sum_congr rfl fun a _ ↦ hv_norm a

end SingleSite

section Tensorization

variable {A : Type*} [Fintype A]

/-- Factoring the noise operator `T_ρ` on `Fin (n + 1) → A` as `T_ρ^{(1)} ∘ T_ρ^{(n)}`. -/
private lemma noiseOp_fin_succ (ν : PMF A) (ρ : ℝ) (n : ℕ) (f : (Fin (n + 1) → A) → ℂ)
    (x : Fin (n + 1) → A) :
    noiseOp ν ρ f x =
      (ρ : ℂ) * noiseOp ν ρ (fun y : Fin n → A ↦ f (Fin.cons (x 0) y)) (Fin.tail x) +
        ((1 - ρ : ℝ) : ℂ) * ∑ a : A, ((ν a).toReal : ℂ) *
          noiseOp ν ρ (fun y : Fin n → A ↦ f (Fin.cons a y)) (Fin.tail x) := by
  let emb : Fin n ↪ Fin (n + 1) := ⟨Fin.succ, Fin.succ_injective n⟩
  let e : Bool × Finset (Fin n) ≃ Finset (Fin (n + 1)) :=
    { toFun := fun p ↦ if p.1 then insert 0 (p.2.map emb) else p.2.map emb
      invFun := fun I ↦ (0 ∈ I, I.preimage Fin.succ (Fin.succ_injective n).injOn)
      left_inv := fun ⟨b, J⟩ ↦ by
        cases b <;> ext <;> simp [emb, Fin.succ_ne_zero]
      right_inv := fun I ↦ by
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · by_cases h0 : (0 : Fin (n + 1)) ∈ I <;> simp [h0, emb, Fin.succ_ne_zero]
        · by_cases h0 : (0 : Fin (n + 1)) ∈ I <;> simp [h0, emb, Fin.succ_ne_zero] }
  have hprob_false : ∀ J : Finset (Fin n),
      subsetProb (1 - ρ) (e (false, J)) = ρ * subsetProb (1 - ρ) J := by
    intro J
    simp only [e, Equiv.coe_fn_mk, subsetProb_eq_mul_pow, Bool.false_eq_true, ↓reduceIte,
      Finset.card_map, Fintype.card_fin]
    have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
    have hexp : n + 1 - J.card = (n - J.card) + 1 := by omega
    rw [hexp, pow_succ, sub_sub_cancel]; ring
  have hprob_true : ∀ J : Finset (Fin n),
      subsetProb (1 - ρ) (e (true, J)) = (1 - ρ) * subsetProb (1 - ρ) J := by
    intro J
    have h0 : (0 : Fin (n + 1)) ∉ J.map emb := by simp [emb, Fin.succ_ne_zero]
    simp only [e, Equiv.coe_fn_mk, subsetProb_eq_mul_pow, ↓reduceIte,
      Finset.card_insert_of_notMem h0, Finset.card_map, Fintype.card_fin]
    have hexp : n + 1 - (J.card + 1) = n - J.card := by omega
    rw [hexp, pow_succ]; ring
  have hres_false : ∀ (J : Finset (Fin n)),
      subsetResampleOp ν (e (false, J)) f x =
        subsetResampleOp ν J (fun y ↦ f (Fin.cons (x 0) y)) (Fin.tail x) := by
    intro J
    rw [subsetResampleOp_eq_sum, subsetResampleOp_eq_sum]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) ↦ A))]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have h1 : ∀ (y : Fin n → A) (a : A),
        splice (e (false, J)) x (Fin.cons a y) = Fin.cons (x 0) (splice J (Fin.tail x) y) := by
      intro y a; ext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [e, emb, splice_eq_ite, Fin.succ_ne_zero]
      · by_cases hj : j ∈ J <;> simp [e, emb, splice_eq_ite, hj, Fin.tail_def]
    simp_rw [Fin.consEquiv_apply, h1]
    have hw : (∑ a : A, ((ν a).toReal : ℂ)) = 1 := by exact_mod_cast sum_pmf_toReal ν
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hfactor : ∀ a : A, (piWeight ν (Fin.cons a y) : ℂ) =
        ((ν a).toReal : ℂ) * (piWeight ν y : ℂ) := fun a ↦ by
      simp [piWeight_fin_cons]
    simp_rw [hfactor, ← Finset.sum_mul, hw, one_mul]
  have hres_true : ∀ (J : Finset (Fin n)),
      subsetResampleOp ν (e (true, J)) f x =
        ∑ a : A, ((ν a).toReal : ℂ) *
          subsetResampleOp ν J (fun y ↦ f (Fin.cons a y)) (Fin.tail x) := by
    intro J
    rw [subsetResampleOp_eq_sum]
    simp_rw [subsetResampleOp_eq_sum]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) ↦ A))]
    rw [Fintype.sum_prod_type]
    have h1 : ∀ (a : A) (y : Fin n → A),
        splice (e (true, J)) x (Fin.cons a y) = Fin.cons a (splice J (Fin.tail x) y) := by
      intro a y; ext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [e, emb, splice_eq_ite]
      · by_cases hj : j ∈ J <;> simp [e, emb, splice_eq_ite, hj, Fin.tail_def]
    simp_rw [Fin.consEquiv_apply, h1]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    simp [piWeight_fin_cons, mul_assoc]
  rw [noiseOp_eq_sum_subsetProb, noiseOp_eq_sum_subsetProb]
  simp_rw [noiseOp_eq_sum_subsetProb]
  rw [← Equiv.sum_comp e]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp_rw [hprob_true, hprob_false, hres_true, hres_false, Complex.ofReal_mul, mul_assoc,
    ← Finset.mul_sum]
  rw [add_comm]
  congr 1
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  refine Finset.sum_congr rfl fun J _ ↦ by ring

/-- Tensorized `(2, 2k, ρ)`-hypercontractivity for the noise operator on `Fin n → A`. -/
private theorem noiseOp_hypercontractivity_fin (ν : PMF A)
    {α : ℝ} (hα0 : 0 < α) (hmin : ∀ a ∈ ν.support, α ≤ (ν a).toReal)
    {k : ℕ} (hk : 1 ≤ k) :
    ∀ (n : ℕ) (f : (Fin n → A) → ℂ),
      (piExpectReal ν (fun x ↦ ‖noiseOp ν (hypercontractivityRho k α) f x‖ ^ (2 * k))) ^
          ((1 : ℝ) / k) ≤
        l2NormSq ν f := by
  have hα1 : α ≤ 1 := atom_lb_le_one ν hmin
  set ρ := hypercontractivityRho k α
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  intro n
  induction n with
  | zero =>
    intro f
    have hconst : ∀ x : Fin 0 → A, noiseOp ν ρ f x = f Fin.elim0 := fun x ↦ by
      have hx : x = Fin.elim0 := Subsingleton.elim _ _
      subst hx
      rw [noiseOp_eq_sum_subsetProb]
      simp_rw [subsetResampleOp_eq_sum]
      have hI : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
        rw [Finset.univ_unique]
        congr 1
      rw [hI, Finset.sum_singleton]
      simp only [subsetProb_eq_mul_pow, Finset.card_empty, Fintype.card_fin, Nat.sub_zero, pow_zero,
        mul_one, Complex.ofReal_one, one_mul, Subsingleton.elim (splice _ _ _) Fin.elim0,
        ← Finset.sum_mul]
      have h1 : (∑ y : Fin 0 → A, (piWeight ν y : ℂ)) = 1 := by exact_mod_cast sum_piWeight ν
      rw [h1, one_mul]
    have hL : piExpectReal ν (fun x ↦ ‖noiseOp ν ρ f x‖ ^ (2 * k)) = ‖f Fin.elim0‖ ^ (2 * k) := by
      simp_rw [hconst]; exact piExpectReal_const ν _
    have hR : l2NormSq ν f = ‖f Fin.elim0‖ ^ 2 := by
      rw [l2NormSq_eq_piExpectReal]
      have : (fun x : Fin 0 → A ↦ ‖f x‖ ^ 2) = fun _ ↦ ‖f Fin.elim0‖ ^ 2 := by
        ext x; rw [Subsingleton.elim x Fin.elim0]
      rw [this, piExpectReal_const]
    rw [hL, hR, pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (sq_nonneg _),
      mul_one_div_cancel (ne_of_gt hk_pos), Real.rpow_one]
  | succ n ih =>
    intro f
    -- Apply single-site hypercontractivity in `x 0`, then Minkowski in `Fin.tail x`, then `ih`!
    let g : A → (Fin n → A) → ℂ := fun a y ↦ noiseOp ν ρ (fun z ↦ f (Fin.cons a z)) y
    have h1site : ∀ y : Fin n → A,
        (∑ a : A, (ν a).toReal * ‖noiseOp ν ρ f (Fin.cons a y)‖ ^ (2 * k)) ^ ((1 : ℝ) / k) ≤
          ∑ a : A, (ν a).toReal * ‖g a y‖ ^ 2 := by
      intro y
      let c : ℂ := ∑ a : A, ((ν a).toReal : ℂ) * g a y
      let h : A → ℂ := fun a ↦ g a y - c
      have hh0 : ∑ a : A, ((ν a).toReal : ℂ) * h a = 0 := by
        simp only [h, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        have h1 : (∑ a : A, ((ν a).toReal : ℂ)) = 1 := by exact_mod_cast sum_pmf_toReal ν
        rw [h1, one_mul]; exact sub_self _
      have hss := singleSite_hypercontractivity_even ν hα0 hmin hk c h hh0
      have hval : ∀ a : A, noiseOp ν ρ f (Fin.cons a y) = c + (ρ : ℂ) * h a := by
        intro a
        rw [noiseOp_fin_succ]
        simp only [Fin.cons_zero, Fin.tail_cons, c, h, g, Complex.ofReal_sub, Complex.ofReal_one]
        ring
      simp_rw [hval]
      have hrhs : ‖c‖ ^ 2 + ∑ a : A, (ν a).toReal * ‖h a‖ ^ 2 =
          ∑ a : A, (ν a).toReal * ‖g a y‖ ^ 2 := by
        have hc : (∑ a : A, ((ν a).toReal : ℂ) * ((‖g a y‖ ^ 2 : ℝ) : ℂ)) =
            ((‖c‖ ^ 2 : ℝ) : ℂ) + ∑ a : A, ((ν a).toReal : ℂ) * ((‖h a‖ ^ 2 : ℝ) : ℂ) := by
          have hg_eq : ∀ a, g a y = c + h a := fun a ↦ by simp [h]
          have hnorm : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := fun z ↦ by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          simp_rw [hnorm, hg_eq, map_add, mul_add, add_mul, mul_add, Finset.sum_add_distrib]
          have h1 : (∑ a : A, ((ν a).toReal : ℂ) * (c * (starRingEnd ℂ) c)) =
              c * (starRingEnd ℂ) c := by
            rw [← Finset.sum_mul]
            have hw : (∑ a : A, ((ν a).toReal : ℂ)) = 1 := by exact_mod_cast sum_pmf_toReal ν
            rw [hw, one_mul]
          have h2 : (∑ a : A, ((ν a).toReal : ℂ) * (c * (starRingEnd ℂ) (h a))) = 0 := by
            have : (∑ a : A, ((ν a).toReal : ℂ) * (c * (starRingEnd ℂ) (h a))) =
                c * starRingEnd ℂ (∑ a : A, ((ν a).toReal : ℂ) * h a) := by
              rw [map_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ ↦ ?_
              simp [Complex.conj_ofReal]; ring
            rw [this, hh0, map_zero, mul_zero]
          have h3 : (∑ a : A, ((ν a).toReal : ℂ) * (h a * (starRingEnd ℂ) c)) = 0 := by
            have : (∑ a : A, ((ν a).toReal : ℂ) * (h a * (starRingEnd ℂ) c)) =
                (∑ a : A, ((ν a).toReal : ℂ) * h a) * starRingEnd ℂ c := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun a _ ↦ ?_; ring
            rw [this, hh0, zero_mul]
          rw [h1, h2, h3]; ring
        have hre := congr_arg Complex.re hc
        simp only [Complex.re_sum, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul] at hre
        exact hre.symm
      rw [← hrhs]
      have hnn : 0 ≤ ‖c‖ ^ 2 + ∑ a : A, (ν a).toReal * ‖h a‖ ^ 2 :=
        add_nonneg (sq_nonneg _)
          (Finset.sum_nonneg fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
      calc (∑ a : A, (ν a).toReal * ‖c + (ρ : ℂ) * h a‖ ^ (2 * k)) ^ ((1 : ℝ) / k)
          ≤ ((‖c‖ ^ 2 + ∑ a : A, (ν a).toReal * ‖h a‖ ^ 2) ^ k) ^ ((1 : ℝ) / k) :=
            Real.rpow_le_rpow
              (Finset.sum_nonneg fun _ _ ↦
                mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (norm_nonneg _) _))
              hss (by positivity)
        _ = ‖c‖ ^ 2 + ∑ a : A, (ν a).toReal * ‖h a‖ ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hnn, mul_one_div_cancel (ne_of_gt hk_pos),
              Real.rpow_one]
    -- Factor `piExpectReal` over `Fin (n + 1) → A` into `a : A` and `y : Fin n → A`!
    have hfactor : ∀ F : (Fin (n + 1) → A) → ℝ,
        piExpectReal ν F =
          ∑ y : Fin n → A, piWeight ν y * ∑ a : A, (ν a).toReal * F (Fin.cons a y) := by
      intro F
      rw [piExpectReal_eq_sum]
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) ↦ A))]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      simp only [Fin.consEquiv_apply, piWeight_fin_cons]
      ring
    rw [hfactor]
    have hstep1 :
        (∑ y : Fin n → A, piWeight ν y *
            ∑ a : A, (ν a).toReal * ‖noiseOp ν ρ f (Fin.cons a y)‖ ^ (2 * k)) ^
          ((1 : ℝ) / k) ≤
        (∑ y : Fin n → A, piWeight ν y * (∑ a : A, (ν a).toReal * ‖g a y‖ ^ 2) ^ k) ^
          ((1 : ℝ) / k) := by
      refine Real.rpow_le_rpow
        (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (piWeight_nonneg ν _)
          (Finset.sum_nonneg fun _ _ ↦
            mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (norm_nonneg _) _)))
        (Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left ?_ (piWeight_nonneg ν y))
        (by positivity)
      have h1 := h1site y
      have hnn1 : 0 ≤ ∑ a : A, (ν a).toReal * ‖noiseOp ν ρ f (Fin.cons a y)‖ ^ (2 * k) :=
        Finset.sum_nonneg fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (norm_nonneg _) _)
      calc ∑ a : A, (ν a).toReal * ‖noiseOp ν ρ f (Fin.cons a y)‖ ^ (2 * k)
          = ((∑ a : A, (ν a).toReal * ‖noiseOp ν ρ f (Fin.cons a y)‖ ^ (2 * k)) ^
              ((1 : ℝ) / k)) ^ k := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hnn1, one_div_mul_cancel (ne_of_gt hk_pos),
              Real.rpow_one]
        _ ≤ (∑ a : A, (ν a).toReal * ‖g a y‖ ^ 2) ^ k :=
            pow_le_pow_left₀ (Real.rpow_nonneg hnn1 _) h1 k
    have hstep2 :
        (∑ y : Fin n → A, piWeight ν y * (∑ a : A, (ν a).toReal * ‖g a y‖ ^ 2) ^ k) ^
          ((1 : ℝ) / k) ≤
        ∑ a : A, (ν a).toReal *
          (∑ y : Fin n → A, piWeight ν y * (‖g a y‖ ^ 2) ^ k) ^ ((1 : ℝ) / k) :=
      minkowski_weighted_pow hk (fun _ ↦ ENNReal.toReal_nonneg) (piWeight_nonneg ν)
        (fun _ _ ↦ sq_nonneg _)
    have hstep3 :
        ∑ a : A, (ν a).toReal *
          (∑ y : Fin n → A, piWeight ν y * (‖g a y‖ ^ 2) ^ k) ^ ((1 : ℝ) / k) ≤
        ∑ a : A, (ν a).toReal * l2NormSq ν (fun y ↦ f (Fin.cons a y)) := by
      refine Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      have hih := ih (fun y ↦ f (Fin.cons a y))
      simpa only [g, piExpectReal_eq_sum, pow_mul] using hih
    calc (∑ y : Fin n → A, piWeight ν y * ∑ a : A, (ν a).toReal *
            ‖noiseOp ν ρ f (Fin.cons a y)‖ ^ (2 * k)) ^ ((1 : ℝ) / k)
        ≤ _ := hstep1
      _ ≤ _ := hstep2
      _ ≤ ∑ a : A, (ν a).toReal * l2NormSq ν (fun y ↦ f (Fin.cons a y)) := hstep3
      _ = l2NormSq ν f := by
          rw [l2NormSq_eq_piExpectReal, hfactor]
          simp_rw [l2NormSq_eq_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          refine Finset.sum_congr rfl fun a _ ↦ by ring

/-- Tensorized `(2, 2k, ρ)`-hypercontractivity: `‖T_ρ f‖_{2k} ≤ ‖f‖₂` on `(ι → A, ν^⊗ι)`. -/
theorem noiseOp_hypercontractivity_even {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : PMF A)
    {α : ℝ} (hα0 : 0 < α) (hmin : ∀ a ∈ ν.support, α ≤ (ν a).toReal)
    {k : ℕ} (hk : 1 ≤ k) (f : (ι → A) → ℂ) :
    lpNorm ν (2 * k : ℝ) (noiseOp ν (hypercontractivityRho k α) f) ≤ l2Norm ν f := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let ePi : (ι → A) ≃ (Fin (Fintype.card ι) → A) := Equiv.arrowCongr e (Equiv.refl A)
  have hfin := noiseOp_hypercontractivity_fin ν hα0 hmin hk (Fintype.card ι) (f ∘ ePi.symm)
  have hL : piExpectReal ν (fun x ↦ ‖noiseOp ν (hypercontractivityRho k α) f x‖ ^ (2 * k)) =
      piExpectReal ν
        (fun y ↦ ‖noiseOp ν (hypercontractivityRho k α) (f ∘ ePi.symm) y‖ ^ (2 * k)) := by
    have hwt : ∀ y : Fin (Fintype.card ι) → A, piWeight ν (ePi.symm y) = piWeight ν y := fun y ↦ by
      rw [piWeight_eq_prod, piWeight_eq_prod]
      exact Fintype.prod_equiv e (fun i ↦ (ν (ePi.symm y i)).toReal) (fun j ↦ (ν (y j)).toReal)
        fun i ↦ by simp [ePi]
    have hnoise : ∀ y : Fin (Fintype.card ι) → A,
        noiseOp ν (hypercontractivityRho k α) (f ∘ ePi.symm) y =
          noiseOp ν (hypercontractivityRho k α) f (ePi.symm y) := by
      intro y
      rw [noiseOp_eq_sum_subsetProb, noiseOp_eq_sum_subsetProb]
      let eSet : Finset ι ≃ Finset (Fin (Fintype.card ι)) := Equiv.finsetCongr e
      rw [← Equiv.sum_comp eSet]
      refine Finset.sum_congr rfl fun I _ ↦ ?_
      have hcard : (eSet I).card = I.card := Finset.card_map _
      have hprob : subsetProb (1 - hypercontractivityRho k α) (eSet I) =
          subsetProb (1 - hypercontractivityRho k α) I := by
        simp [subsetProb_eq_mul_pow, hcard, Fintype.card_fin]
      rw [hprob]
      congr 1
      rw [subsetResampleOp_eq_sum, subsetResampleOp_eq_sum]
      rw [← Equiv.sum_comp ePi]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      have hw : piWeight ν (ePi z) = piWeight ν z := by
        simpa using (hwt (ePi z)).symm
      rw [hw]
      congr 1
      change f (ePi.symm (splice (eSet I) y (ePi z))) = f (splice I (ePi.symm y) z)
      congr 1
      ext i
      by_cases hi : i ∈ I <;> simp [eSet, ePi, splice_eq_ite, hi]
    rw [piExpectReal_eq_sum, piExpectReal_eq_sum, ← Equiv.sum_comp ePi.symm]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [hwt y, hnoise y]
  have hR : l2NormSq ν (f ∘ ePi.symm) = l2NormSq ν f := by
    rw [l2NormSq_eq_sum, l2NormSq_eq_sum, ← Equiv.sum_comp ePi.symm]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hwt : piWeight ν (ePi.symm y) = piWeight ν y := by
      rw [piWeight_eq_prod, piWeight_eq_prod]
      exact Fintype.prod_equiv e (fun i ↦ (ν (ePi.symm y i)).toReal) (fun j ↦ (ν (y j)).toReal)
        fun i ↦ by simp [ePi]
    rw [hwt]; rfl
  rw [hR] at hfin
  rw [lpNorm_eq_rpow, l2Norm_eq_sqrt]
  rw [show (1 : ℝ) / (2 * (k : ℝ)) = ((1 : ℝ) / (k : ℝ)) * (1 / 2 : ℝ) by ring,
    Real.rpow_mul (piExpectReal_nonneg ν fun _ ↦ by positivity),
    ← Real.sqrt_eq_rpow]
  have h2k : ∀ x, ‖noiseOp ν (hypercontractivityRho k α) f x‖ ^ (2 * (k : ℝ)) =
      ‖noiseOp ν (hypercontractivityRho k α) f x‖ ^ (2 * k) := fun x ↦ by
    rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  simp_rw [h2k]
  rw [hL]
  exact Real.sqrt_le_sqrt hfin

/-- Monotonicity of `L^q` norms on probability spaces: `‖f‖_q ≤ ‖f‖_r` for `0 < q ≤ r`. -/
theorem lpNorm_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : PMF A) {q r : ℝ} (hq : 0 < q)
    (hqr : q ≤ r) (f : (ι → A) → ℂ) : lpNorm ν q f ≤ lpNorm ν r f := by
  have hr : 0 < r := hq.trans_le hqr
  have h1 : 1 ≤ r / q := (one_le_div hq).mpr hqr
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ ↦ t ^ (r / q)) :=
    convexOn_rpow h1
  have hjen := hconv.map_sum_le (t := Finset.univ) (w := piWeight ν)
    (p := fun x : ι → A ↦ ‖f x‖ ^ q)
    (fun x _ ↦ piWeight_nonneg ν x) (sum_piWeight ν)
    (fun x _ ↦ Real.rpow_nonneg (norm_nonneg _) q)
  simp only [smul_eq_mul] at hjen
  have hpow : ∀ x : ι → A, (‖f x‖ ^ q) ^ (r / q) = ‖f x‖ ^ r := fun x ↦ by
    rw [← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ (ne_of_gt hq)]
  simp_rw [hpow] at hjen
  rw [lpNorm_eq_rpow, lpNorm_eq_rpow]
  have hnn : 0 ≤ piExpectReal ν (fun x ↦ ‖f x‖ ^ q) :=
    piExpectReal_nonneg ν fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hle : (piExpectReal ν (fun x ↦ ‖f x‖ ^ q) ^ (r / q)) ^ (1 / r) ≤
      (piExpectReal ν (fun x ↦ ‖f x‖ ^ r)) ^ (1 / r) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hjen (by positivity)
  rwa [← Real.rpow_mul hnn, show r / q * (1 / r) = 1 / q by field_simp [ne_of_gt hr]] at hle

/-- **Hypercontractivity for low-degree functions**:
for any finite probability space `(A, ν)` with minimum atom probability `α > 0`, any `q ≥ 2`,
any degree `d`, and any `f ∈ degSubspace d` on `(ι → A, ν^⊗ι)`:
`‖f‖_q ≤ (hypercontractivityConst q α)^d * ‖f‖₂`.
-/
theorem hypercontractivity_of_deg {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : PMF A)
    {α : ℝ} (hα0 : 0 < α) (hmin : ∀ a ∈ ν.support, α ≤ (ν a).toReal)
    {q : ℝ} (hq : 2 ≤ q) {d : ℕ} {f : (ι → A) → ℂ} (hf : f ∈ degSubspace d) :
    lpNorm ν q f ≤ (hypercontractivityConst q α) ^ d * l2Norm ν f := by
  have hα1 : α ≤ 1 := atom_lb_le_one ν hmin
  set k := Nat.ceil (q / 2)
  have hk : 1 ≤ k := Nat.ceil_pos.mpr (by linarith)
  have hq2k : q ≤ (2 * k : ℝ) := by
    have h := Nat.le_ceil (q / 2); linarith
  set ρ := hypercontractivityRho k α
  have hρ0 : 0 < ρ := hypercontractivityRho_pos k hα0
  have hρ1 : ρ ≤ 1 := hypercontractivityRho_le_one k hα0.le hα1
  let g : (ι → A) → ℂ := fun x ↦
    ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
      ((ρ⁻¹ ^ S.card : ℝ) : ℂ) * efronProj ν S f x
  have hTg : noiseOp ν ρ g = f := by
    ext x
    change noiseOp ν ρ (fun y ↦ ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
      ((ρ⁻¹ ^ S.card : ℝ) : ℂ) * efronProj ν S f y) x = f x
    rw [noiseOp_sum]
    have h1 : ∀ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
        noiseOp ν ρ (fun y ↦ ((ρ⁻¹ ^ S.card : ℝ) : ℂ) * efronProj ν S f y) x =
          efronProj ν S f x := by
      intro S _
      rw [noiseOp_smul, noiseOp_efronProj]
      have hmul : ((ρ⁻¹ ^ S.card : ℝ) : ℂ) * (ρ ^ S.card : ℂ) = 1 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hρ0),
          one_pow, Complex.ofReal_one]
      dsimp only
      rw [← mul_assoc, hmul, one_mul]
    dsimp only
    rw [Finset.sum_congr rfl h1]
    exact congr_fun (eq_degPart_of_mem_degSubspace ν hf) x
  have hg_norm : l2Norm ν g ≤ (ρ⁻¹) ^ d * l2Norm ν f := by
    rw [l2Norm_eq_sqrt, l2Norm_eq_sqrt]
    rw [← Real.sqrt_sq (pow_nonneg (inv_nonneg.mpr hρ0.le) d),
      ← Real.sqrt_mul (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    have hgsq : l2NormSq ν g =
        ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
          (ρ⁻¹ ^ S.card) ^ 2 * l2NormSq ν (efronProj ν S f) := by
      have h := l2NormSq_sum_of_pairwise_orth ν
        (Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d))
        (fun S y ↦ ((ρ⁻¹ ^ S.card : ℝ) : ℂ) * efronProj ν S f y)
        (fun S _ T _ hST ↦ by
          rw [piInner_smul_left, piInner_smul_right, piInner_efronProj_eq_zero ν hST,
            mul_zero, mul_zero])
      rw [h]
      refine Finset.sum_congr rfl fun S _ ↦ ?_
      rw [l2NormSq_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hgsq, parseval_efronProj ν f]
    have hρinv : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ0).mpr hρ1
    calc ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
            (ρ⁻¹ ^ S.card) ^ 2 * l2NormSq ν (efronProj ν S f)
        ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
            (ρ⁻¹ ^ d) ^ 2 * l2NormSq ν (efronProj ν S f) := by
          refine Finset.sum_le_sum fun S hS ↦ ?_
          have hdS : S.card ≤ d := (Finset.mem_filter.mp hS).2
          have hpow : ρ⁻¹ ^ S.card ≤ ρ⁻¹ ^ d := pow_le_pow_right₀ hρinv hdS
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hpow 2) (l2NormSq_nonneg ν _)
      _ = (ρ⁻¹ ^ d) ^ 2 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι ↦ S.card ≤ d),
            l2NormSq ν (efronProj ν S f) := by rw [← Finset.mul_sum]
      _ ≤ (ρ⁻¹ ^ d) ^ 2 * ∑ S : Finset ι, l2NormSq ν (efronProj ν S f) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ ↦ l2NormSq_nonneg ν _) (sq_nonneg _)
  calc lpNorm ν q f
      ≤ lpNorm ν (2 * k : ℝ) f := lpNorm_mono ν (by linarith) hq2k f
    _ = lpNorm ν (2 * k : ℝ) (noiseOp ν ρ g) := by rw [hTg]
    _ ≤ l2Norm ν g := noiseOp_hypercontractivity_even ν hα0 hmin hk g
    _ ≤ (hypercontractivityConst q α) ^ d * l2Norm ν f := hg_norm

end Tensorization

end CslibFrontier.Analysis.Fourier
