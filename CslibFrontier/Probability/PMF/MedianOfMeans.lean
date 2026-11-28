/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init

public import CslibFrontier.Foundations.Data.Finset.Median
public import CslibFrontier.Probability.Concentration
public import CslibFrontier.Probability.Product
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Median-of-Means and Median Amplification on Finite PMFs

This module develops finite-`PMF` expectation, variance, Markov and Chebyshev inequalities,
the Hoeffding-based median-of-means concentration inequality, and the median-amplification
bound under standard Lean axioms.

## Main definitions

- `Cslib.Probability.PMF.pmfExpect`: expectation of a real-valued function under
  a finite `PMF`.
- `Cslib.Probability.PMF.pmfVariance`: variance of a real-valued function under
  a finite `PMF`.
- `Cslib.Probability.PMF.medianOfMeansEst`: the median of `γ` disjoint batch means
  of size `β`.

## Main results

- `Cslib.Probability.PMF.pmf_markov_le`: Markov's inequality for finite `PMF`s.
- `Cslib.Probability.PMF.pmf_chebyshev_le`: Chebyshev's inequality for finite `PMF`s.
- `Cslib.Probability.PMF.pmfVariance_pi_mean`: the average of `β` i.i.d. samples
  divides the variance by `β`.
- `Cslib.Probability.PMF.pmf_medianOfMeans_le`: for `2 * σ² ≤ ε² * β`, the
  median-of-means estimator deviates by at least `ε` with probability at most
  `exp (-(γ / 2) * (1 - 2 * σ² / (ε² * β)) ^ 2)`.
- `Cslib.Probability.PMF.pmf_median_amplification_le`: if each independent trial
  fails with probability at most `1 / 4`, the median of `ξ` trials fails with probability at most
  `exp (-(ξ / 8))`.
-/

public section

namespace Cslib.Probability.PMF

open scoped BigOperators

universe u v

variable {α : Type u} [Fintype α]

/-- Expectation of a real-valued random variable under a finite `PMF`. -/
noncomputable def pmfExpect (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a : α, (p a).toReal * f a

/-- Variance of a real-valued random variable under a finite `PMF`. -/
noncomputable def pmfVariance (p : PMF α) (f : α → ℝ) : ℝ :=
  pmfExpect p fun a => (f a - pmfExpect p f) ^ 2

@[simp]
theorem pmfExpect_const (p : PMF α) (c : ℝ) : pmfExpect p (fun _ => c) = c := by
  simp [pmfExpect, ← Finset.sum_mul, Cslib.Probability.PMF.sum_toReal]

theorem pmfExpect_zero (p : PMF α) : pmfExpect p (fun _ => 0) = 0 :=
  pmfExpect_const p 0

@[simp]
theorem pmfExpect_pure (a : α) (f : α → ℝ) : pmfExpect (PMF.pure a) f = f a := by
  classical
  simp [pmfExpect, PMF.pure_apply, apply_ite ENNReal.toReal]

theorem pmfExpect_bool (p : PMF Bool) (f : Bool → ℝ) :
    pmfExpect p f = (p true).toReal * f true + (p false).toReal * f false := by
  simp [pmfExpect]

theorem pmfExpect_map {β : Type u} [Fintype β] (p : PMF α) (g : α → β) (f : β → ℝ) :
    pmfExpect (p.map g) f = pmfExpect p (f ∘ g) := by
  classical
  simp only [pmfExpect, PMF.map_apply, tsum_fintype, Function.comp_apply]
  have h1 (y : β) : (∑ x : α, if y = g x then p x else 0).toReal * f y =
      ∑ x : α, if y = g x then (p x).toReal * f (g x) else 0 := by
    rw [ENNReal.toReal_sum fun _ _ => by split_ifs <;> simp [PMF.apply_ne_top], Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hy : y = g x
    · subst hy; simp
    · simp [hy]
  simp_rw [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => by simp [Finset.sum_ite_eq']

theorem pmfExpect_bind {β : Type u} [Fintype β] (p : PMF α) (K : α → PMF β) (f : β → ℝ) :
    pmfExpect (p.bind K) f = ∑ x : α, (p x).toReal * pmfExpect (K x) f := by
  simp only [pmfExpect, PMF.bind_apply, tsum_fintype]
  have h1 (y : β) : (∑ x : α, p x * K x y).toReal * f y =
      ∑ x : α, (p x).toReal * ((K x y).toReal * f y) := by
    rw [ENNReal.toReal_sum fun _ _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => by rw [ENNReal.toReal_mul, mul_assoc]
  simp_rw [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum ..).symm

theorem pmfExpect_pi_coord {ι : Type v} [Fintype ι] [DecidableEq ι]
    {β : ι → Type u} [∀ i, Fintype (β i)] (P : ∀ i, PMF (β i)) (i₀ : ι) (f : β i₀ → ℝ) :
    pmfExpect (pi P) (fun g => f (g i₀)) = pmfExpect (P i₀) f := by
  simp only [pmfExpect]
  let h : ∀ i, β i → ℝ := fun i x => if eq : i = i₀ then f (eq ▸ x) else 1
  have hrew : ∀ g : ∀ i, β i, (pi P g).toReal * f (g i₀) =
      ∏ i, (P i (g i)).toReal * h i (g i) := fun g => by
    rw [pi_apply, ENNReal.toReal_prod, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single i₀]
    · simp [h]
    · intro i _ hi; simp [h, hi]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  simp_rw [hrew]
  rw [← Fintype.prod_sum (fun i x => (P i x).toReal * h i x)]
  have hterm (i : ι) : (∑ x : β i, (P i x).toReal * h i x) =
      if i = i₀ then ∑ x : β i₀, (P i₀ x).toReal * f x else 1 := by
    by_cases hi : i = i₀
    · subst hi; simp [h]
    · simp only [h, hi, ↓reduceDIte, ↓reduceIte, mul_one]; exact sum_toReal _
  simp_rw [hterm]
  simp

omit [Fintype α] in
/-- Any event has finite (at most `1`) probability under a `PMF`. -/
theorem pmf_toOuterMeasure_ne_top (p : PMF α) (s : Set α) : p.toOuterMeasure s ≠ ⊤ := by
  have h1 : p.toOuterMeasure Set.univ = 1 := by
    rw [PMF.toOuterMeasure_apply]
    simp [p.tsum_coe]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (h1 ▸ p.toOuterMeasure.mono (Set.subset_univ s))

/-- Probability of an event under a finite `PMF` as a real number. -/
theorem pmf_toOuterMeasure_toReal_eq_sum (p : PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    (p.toOuterMeasure s).toReal = ∑ a : α, if a ∈ s then (p a).toReal else 0 := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype,
    ENNReal.toReal_sum fun a _ => by
      by_cases ha : a ∈ s
      · simp [Set.indicator, ha, p.apply_ne_top a]
      · simp [Set.indicator, ha]]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

theorem pmfExpect_ite_eq_prob (p : PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    pmfExpect p (fun a => if a ∈ s then (1 : ℝ) else 0) = (p.toOuterMeasure s).toReal := by
  rw [pmfExpect, pmf_toOuterMeasure_toReal_eq_sum]
  refine Finset.sum_congr rfl fun a _ => by split_ifs <;> simp

theorem pmfExpect_add (p : PMF α) (f g : α → ℝ) :
    pmfExpect p (fun a => f a + g a) = pmfExpect p f + pmfExpect p g := by
  simp only [pmfExpect, mul_add, Finset.sum_add_distrib]

theorem pmfExpect_sub (p : PMF α) (f g : α → ℝ) :
    pmfExpect p (fun a => f a - g a) = pmfExpect p f - pmfExpect p g := by
  simp only [pmfExpect, mul_sub, Finset.sum_sub_distrib]

theorem pmfExpect_const_mul (p : PMF α) (c : ℝ) (f : α → ℝ) :
    pmfExpect p (fun a => c * f a) = c * pmfExpect p f := by
  simp only [pmfExpect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => by ring

theorem pmfExpect_sum {ι : Type*} (s : Finset ι) (p : PMF α) (f : ι → α → ℝ) :
    pmfExpect p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, pmfExpect p (f i) := by
  simp only [pmfExpect, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem pmfExpect_nonneg {p : PMF α} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ pmfExpect p f := by
  exact Finset.sum_nonneg fun a _ => mul_nonneg ENNReal.toReal_nonneg (hf a)

@[gcongr]
theorem pmfExpect_mono {p : PMF α} {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    pmfExpect p f ≤ pmfExpect p g := by
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg

@[simp]
theorem pmfVariance_const (p : PMF α) (c : ℝ) : pmfVariance p (fun _ => c) = 0 := by
  simp [pmfVariance, pmfExpect_const]

theorem pmfVariance_bool (p : PMF Bool) (f : Bool → ℝ) :
    pmfVariance p f =
      (p true).toReal * (f true - pmfExpect p f) ^ 2 +
      (p false).toReal * (f false - pmfExpect p f) ^ 2 := by
  simp [pmfVariance, pmfExpect_bool]

theorem pmfVariance_nonneg (p : PMF α) (f : α → ℝ) : 0 ≤ pmfVariance p f := by
  exact pmfExpect_nonneg fun _ => sq_nonneg _

theorem pmfVariance_eq_expect_sq_sub (p : PMF α) (f : α → ℝ) :
    pmfVariance p f = pmfExpect p (fun a => f a ^ 2) - (pmfExpect p f) ^ 2 := by
  have h1 : pmfExpect p (fun a => (f a - pmfExpect p f) ^ 2) =
      pmfExpect p (fun a => f a ^ 2 - 2 * pmfExpect p f * f a + (pmfExpect p f) ^ 2) := by
    refine Finset.sum_congr rfl fun a _ => by ring
  rw [pmfVariance, h1, pmfExpect_add, pmfExpect_sub, pmfExpect_const_mul, pmfExpect_const]
  ring

theorem pmfVariance_le_expect_sq (p : PMF α) (f : α → ℝ) :
    pmfVariance p f ≤ pmfExpect p (fun a => f a ^ 2) := by
  rw [pmfVariance_eq_expect_sq_sub]
  nlinarith [sq_nonneg (pmfExpect p f)]

/-- **Markov's inequality** for a nonnegative function under a finite `PMF`. -/
theorem pmf_markov_le (p : PMF α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) {t : ℝ} (ht : 0 < t) :
    (p.toOuterMeasure {a | t ≤ f a}).toReal ≤ pmfExpect p f / t := by
  classical
  rw [pmf_toOuterMeasure_toReal_eq_sum, le_div_iff₀ ht, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : t ≤ f a
  · simp only [Set.mem_ofPred_eq, ha, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left ha ENNReal.toReal_nonneg
  · simp only [Set.mem_ofPred_eq, ha, ↓reduceIte, zero_mul]
    exact mul_nonneg ENNReal.toReal_nonneg (hf a)

/-- **Chebyshev's inequality** for a finite `PMF`. -/
theorem pmf_chebyshev_le (p : PMF α) (f : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (p.toOuterMeasure {a | ε ≤ |f a - pmfExpect p f|}).toReal ≤ pmfVariance p f / ε ^ 2 := by
  have hsq : {a : α | ε ≤ |f a - pmfExpect p f|} =
      {a : α | ε ^ 2 ≤ (f a - pmfExpect p f) ^ 2} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      have := mul_self_le_mul_self (le_of_lt hε) h
      simpa [sq, sq_abs] using this
    · intro h
      have h1 : |f a - pmfExpect p f| ^ 2 = (f a - pmfExpect p f) ^ 2 := sq_abs _
      rw [← h1] at h
      nlinarith [abs_nonneg (f a - pmfExpect p f)]
  rw [hsq]
  exact pmf_markov_le p (fun _ => sq_nonneg _) (sq_pos_of_pos hε)

/-- Expectation of the empirical mean of `β` i.i.d. samples equals the common mean. -/
theorem pmfExpect_pi_mean {β : ℕ} (hβ : 0 < β) (p : PMF α) (f : α → ℝ) :
    pmfExpect (pi fun _ : Fin β => p) (fun ω => (∑ j : Fin β, f (ω j)) / β) =
      pmfExpect p f := by
  have hβR : (β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hβ)
  have h1 : pmfExpect (pi fun _ : Fin β => p) (fun ω => (∑ j : Fin β, f (ω j)) / β) =
      (∑ j : Fin β, pmfExpect (pi fun _ : Fin β => p) (fun ω => f (ω j))) / β := by
    simp_rw [div_eq_mul_inv, mul_comm _ ((β : ℝ)⁻¹)]
    rw [pmfExpect_const_mul, pmfExpect_sum, mul_comm]
  rw [h1]
  have hcoord (j : Fin β) :
      pmfExpect (pi fun _ : Fin β => p) (fun ω => f (ω j)) = pmfExpect p f :=
    pmfExpect_pi_coord (fun _ : Fin β => p) j f
  simp_rw [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hβR]

/-- Variance of the empirical mean of `β` i.i.d. samples equals `Var / β`. -/
theorem pmfVariance_pi_mean {β : ℕ} (hβ : 0 < β) (p : PMF α) (f : α → ℝ) :
    pmfVariance (pi fun _ : Fin β => p) (fun ω => (∑ j : Fin β, f (ω j)) / β) =
      pmfVariance p f / β := by
  classical
  have hβR : (β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hβ)
  rw [pmfVariance, pmfExpect_pi_mean hβ]
  set μ := pmfExpect p f
  have hsub (ω : Fin β → α) :
      ((∑ j : Fin β, f (ω j)) / β - μ) ^ 2 =
        (∑ j : Fin β, ∑ k : Fin β, (f (ω j) - μ) * (f (ω k) - μ)) / (β : ℝ) ^ 2 := by
    have hnum : (∑ j : Fin β, f (ω j)) / β - μ = (∑ j : Fin β, (f (ω j) - μ)) / β := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [hβR]
    rw [hnum, div_pow, sq, Finset.sum_mul_sum]
  simp_rw [hsub, div_eq_mul_inv, mul_comm _ (((β : ℝ) ^ 2)⁻¹)]
  rw [pmfExpect_const_mul, pmfExpect_sum]
  have hinner (j : Fin β) :
      pmfExpect (pi fun _ : Fin β => p) (fun ω => ∑ k : Fin β, (f (ω j) - μ) * (f (ω k) - μ)) =
        pmfVariance p f := by
    rw [pmfExpect_sum]
    have hdiag :
        pmfExpect (pi fun _ : Fin β => p) (fun ω => (f (ω j) - μ) * (f (ω j) - μ)) =
          pmfVariance p f := by
      simp_rw [← sq]
      exact pmfExpect_pi_coord (fun _ : Fin β => p) j (fun a => (f a - μ) ^ 2)
    have hoff (k : Fin β) (hk : k ≠ j) :
        pmfExpect (pi fun _ : Fin β => p) (fun ω => (f (ω j) - μ) * (f (ω k) - μ)) = 0 := by
      -- Factor out the product of two distinct coordinates in `pi`.
      have hfactor : ∀ (g₁ g₂ : α → ℝ),
          pmfExpect (pi fun _ : Fin β => p) (fun ω => g₁ (ω j) * g₂ (ω k)) =
            pmfExpect p g₁ * pmfExpect p g₂ := by
        intro g₁ g₂
        have h1 : pmfExpect (pi fun _ : Fin β => p) (fun ω => g₁ (ω j) * g₂ (ω k)) =
            ∑ ω : Fin β → α,
              (∏ i : Fin β, (p (ω i)).toReal) * (g₁ (ω j) * g₂ (ω k)) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [pi_apply, ENNReal.toReal_prod]
        rw [h1]
        have h2 : ∀ ω : Fin β → α,
            (∏ i : Fin β, (p (ω i)).toReal) * (g₁ (ω j) * g₂ (ω k)) =
              ∏ i : Fin β,
                (p (ω i)).toReal * (if i = j then g₁ (ω i) else 1) *
                  (if i = k then g₂ (ω i) else 1) := by
          intro ω
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte, mul_assoc]
        simp_rw [h2]
        rw [← Fintype.prod_sum (fun (i : Fin β) (a : α) =>
          (p a).toReal * (if i = j then g₁ a else 1) * (if i = k then g₂ a else 1))]
        have hprod :
            (∏ i : Fin β, ∑ a : α, (p a).toReal * (if i = j then g₁ a else 1) *
              (if i = k then g₂ a else 1)) =
              pmfExpect p g₁ * pmfExpect p g₂ := by
          have hterm (i : Fin β) :
              (∑ a : α, (p a).toReal * (if i = j then g₁ a else 1) *
                (if i = k then g₂ a else 1)) =
                if i = j then pmfExpect p g₁ else if i = k then pmfExpect p g₂ else 1 := by
            by_cases hij : i = j
            · subst hij
              simp [Ne.symm hk, pmfExpect]
            · by_cases hik : i = k
              · subst hik
                simp [hij, pmfExpect]
              · simp [hij, hik, Cslib.Probability.PMF.sum_toReal]
          simp_rw [hterm]
          rw [Finset.prod_ite, Finset.filter_eq']
          simp only [Finset.mem_univ, ↓reduceIte, Finset.prod_singleton]
          have hsub_prod :
              (∏ x ∈ Finset.univ.filter (fun i : Fin β => i ≠ j),
                if x = k then pmfExpect p g₂ else 1) = pmfExpect p g₂ := by
            rw [Finset.prod_ite_eq']
            simp [hk]
          rw [hsub_prod]
        exact hprod
      rw [hfactor (fun a => f a - μ) (fun a => f a - μ)]
      have hz : pmfExpect p (fun a => f a - μ) = 0 := by
        rw [pmfExpect_sub, pmfExpect_const, sub_self]
      rw [hz, zero_mul]
    rw [Finset.sum_eq_single j]
    · exact hdiag
    · intro k _ hk; exact hoff k hk
    · intro h; exact absurd (Finset.mem_univ j) h
  simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hβR]

omit [Fintype α] in
/-- The median-of-means estimator grouping `β * γ` samples into `γ` disjoint batches of size `β`. -/
noncomputable def medianOfMeansEst {β γ : ℕ} (f : α → ℝ) (ω : Fin γ → Fin β → α) : ℝ :=
  Cslib.median fun i : Fin γ => (∑ j : Fin β, f (ω i j)) / β

omit [Fintype α] in
@[simp]
theorem medianOfMeansEst_singleton_batch {γ : ℕ} (f : α → ℝ) (ω : Fin γ → Fin 1 → α) :
    medianOfMeansEst f ω = Cslib.median fun i : Fin γ => f (ω i 0) := by
  simp [medianOfMeansEst]

/-- **Median-of-means concentration inequality** (sharp Hoeffding bound):
if `β, γ > 0`, `ε > 0`, and `2 * σ² ≤ ε² * β`, then the median of `γ` disjoint batch means of
size `β` deviates from the mean `μ` by at least `ε` with probability at most
`exp (-(γ / 2) * (1 - 2 * σ² / (ε² * β)) ^ 2)`. -/
theorem pmf_medianOfMeans_le {β γ : ℕ} (hβ : 0 < β) (hγ : 0 < γ)
    (p : PMF α) (f : α → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hvar : 2 * pmfVariance p f ≤ ε ^ 2 * β) :
    ((pi fun _ : Fin γ => pi fun _ : Fin β => p).toOuterMeasure
      {ω | ε ≤ |medianOfMeansEst f ω - pmfExpect p f|}).toReal ≤
        Real.exp (-((γ : ℝ) / 2) * (1 - 2 * pmfVariance p f / (ε ^ 2 * β)) ^ 2) := by
  classical
  set μ := pmfExpect p f
  set σ2 := pmfVariance p f
  set q : PMF (Fin β → α) := pi fun _ : Fin β => p
  let mean (u : Fin β → α) : ℝ := (∑ j : Fin β, f (u j)) / β
  let score (u : Fin β → α) : ℝ := if ε ≤ |mean u - μ| then 1 else 0
  have hγR : (0 : ℝ) < γ := Nat.cast_pos.mpr hγ
  have hq_bad : (q.toOuterMeasure {u | ε ≤ |mean u - μ|}).toReal ≤ σ2 / (ε ^ 2 * β) := by
    have hc := pmf_chebyshev_le q mean hε
    rwa [pmfExpect_pi_mean hβ, pmfVariance_pi_mean hβ, div_div, mul_comm (β : ℝ)] at hc
  have hscore_mean : ∑ u, (q u).toReal * score u ≤ σ2 / (ε ^ 2 * β) := by
    have heq : ∑ u, (q u).toReal * score u = (q.toOuterMeasure {u | ε ≤ |mean u - μ|}).toReal := by
      rw [pmf_toOuterMeasure_toReal_eq_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      dsimp only [score]
      by_cases h : ε ≤ |mean u - μ| <;> simp [h]
    rw [heq]
    exact hq_bad
  -- If `|medianOfMeansEst f ω - μ| ≥ ε`, then at least `γ / 2` batch means have `|mean - μ| ≥ ε`.
  have hsub : {ω : Fin γ → Fin β → α | ε ≤ |medianOfMeansEst f ω - μ|} ⊆
      {ω | (∑ _i : Fin γ, ∑ u, (q u).toReal * score u) +
        (Fintype.card (Fin γ) : ℝ) * (1 / 2 - σ2 / (ε ^ 2 * β)) ≤
        ∑ i : Fin γ, score (ω i)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hhalf : (γ : ℝ) / 2 ≤ ∑ i : Fin γ, score (ω i) := by
      by_contra hlt
      push Not at hlt
      have hcard_bad : (Finset.univ.filter fun i : Fin γ => ε ≤ |mean (ω i) - μ|).card * 2 < γ := by
        have hsum_eq : ∑ i : Fin γ, score (ω i) =
            ((Finset.univ.filter fun i : Fin γ => ε ≤ |mean (ω i) - μ|).card : ℝ) := by
          simp [score, Finset.sum_boole]
        rw [hsum_eq] at hlt
        have hlt2 : ((Finset.univ.filter fun i : Fin γ => ε ≤
          |mean (ω i) - μ|).card : ℝ) * 2 < γ := by
          linarith
        exact_mod_cast hlt2
      -- Then strictly more than half of the batch means satisfy `|mean (ω i) - μ| < ε`.
      let good := Finset.univ.filter fun i : Fin γ => |mean (ω i) - μ| < ε
      have hgood_card : γ < 2 * good.card := by
        have hdisj := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin γ)))
          (fun i => ε ≤ |mean (ω i) - μ|)
        have hcompl : (Finset.univ.filter fun i : Fin γ => ¬ε ≤ |mean (ω i) - μ|) = good := by
          ext i; simp [good, not_le]
        rw [hcompl, Finset.card_univ, Fintype.card_fin] at hdisj
        omega
      have hgood_ne : good.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image good (fun i => |mean (ω i) - μ|) hgood_ne
      set t₀ := |mean (ω i₀) - μ|
      have ht₀ : t₀ < ε := (Finset.mem_filter.mp hi₀).2
      have hmaj : Fintype.card (Fin γ) < 2 * (Finset.univ.filter fun i : Fin γ => |mean (ω i) - μ| ≤
        t₀).card := by
        rw [Fintype.card_fin]
        have hle_c : good.card ≤ (Finset.univ.filter fun i : Fin γ => |mean (ω i) - μ| ≤ t₀).card :=
          Finset.card_le_card fun i hi =>
            Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmax i hi⟩
        omega
      have hmed := Cslib.abs_median_sub_le (v := fun i => mean (ω i)) hmaj
      exact not_lt_of_ge (hω.trans hmed) ht₀
    have hmean_sum : (∑ _i : Fin γ, ∑ u, (q u).toReal * score u) ≤ γ * (σ2 / (ε ^ 2 * β)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left hscore_mean (le_of_lt hγR)
    simp only [Fintype.card_fin]
    linarith
  have hmargin : 0 ≤ (1 / 2 : ℝ) - σ2 / (ε ^ 2 * β) := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    linarith
  have hhoeff := Cslib.Probability.PMF.pi_sum_ge_mean_add_card_mul (fun _ : Fin γ => q)
    (fun _ u => score u) (fun _ u _ => by dsimp only [score]; split_ifs <;> simp) hmargin
  have hmono :
      ((pi fun _ : Fin γ => q).toOuterMeasure {ω | ε ≤ |medianOfMeansEst f ω - μ|}).toReal ≤
        ((pi fun _ : Fin γ => q).toOuterMeasure
          {ω | (∑ _i : Fin γ, ∑ u, (q u).toReal * score u) +
            (Fintype.card (Fin γ) : ℝ) * (1 / 2 - σ2 / (ε ^ 2 * β)) ≤
            ∑ i : Fin γ, score (ω i)}).toReal :=
    ENNReal.toReal_mono (pmf_toOuterMeasure_ne_top _ _)
      ((pi fun _ : Fin γ => q).toOuterMeasure.mono hsub)
  refine hmono.trans (hhoeff.trans_eq ?_)
  congr 1
  simp only [Fintype.card_fin]
  ring

omit [Fintype α] in
/-- **Median amplification bound**: if each of `ξ` independent trials lands in `[a, b]` with
probability at least `3 / 4` (failure probability at most `1 / 4`), then the median of the `ξ`
trials fails to lie in `[a, b]` with probability at most `exp (-(ξ / 8))`. -/
theorem pmf_median_amplification_le [Finite α] {ξ : ℕ} (p : PMF α) (f : α → ℝ) (a b : ℝ)
    (hfail : (p.toOuterMeasure {x | f x < a ∨ b < f x}).toReal ≤ 1 / 4) :
    ((pi fun _ : Fin ξ => p).toOuterMeasure
      {ω | Cslib.median (fun i : Fin ξ => f (ω i)) < a ∨
        b < Cslib.median (fun i : Fin ξ => f (ω i))}).toReal ≤
        Real.exp (-((ξ : ℝ) / 8)) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  let score (x : α) : ℝ := if f x < a ∨ b < f x then 1 else 0
  have hscore_mean : ∑ x : α, (p x).toReal * score x ≤ 1 / 4 := by
    have heq : ∑ x : α, (p x).toReal * score x =
        (p.toOuterMeasure {x | f x < a ∨ b < f x}).toReal := by
      rw [pmf_toOuterMeasure_toReal_eq_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      dsimp only [score]
      by_cases h : f x < a ∨ b < f x <;> simp [h]
    rw [heq]
    exact hfail
  have hsub : {ω : Fin ξ → α | Cslib.median (fun i => f (ω i)) < a ∨
        b < Cslib.median (fun i => f (ω i))} ⊆
      {ω | (∑ _i : Fin ξ, ∑ x, (p x).toReal * score x) +
        (Fintype.card (Fin ξ) : ℝ) * (1 / 4) ≤ ∑ i : Fin ξ, score (ω i)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hhalf : (ξ : ℝ) / 2 ≤ ∑ i : Fin ξ, score (ω i) := by
      by_contra hlt
      push Not at hlt
      have hcard_bad : (Finset.univ.filter fun i : Fin ξ => f (ω i) < a ∨
        b < f (ω i)).card * 2 < ξ := by
        have hsum_eq : ∑ i : Fin ξ, score (ω i) =
            ((Finset.univ.filter fun i : Fin ξ => f (ω i) < a ∨ b < f (ω i)).card : ℝ) := by
          simp [score, Finset.sum_boole]
        rw [hsum_eq] at hlt
        have hlt2 : ((Finset.univ.filter fun i : Fin ξ => f (ω i) < a ∨
          b < f (ω i)).card : ℝ) * 2 < ξ := by
          linarith
        exact_mod_cast hlt2
      have hgood : ξ < 2 * (Finset.univ.filter fun i : Fin ξ => a ≤ f (ω i) ∧
        f (ω i) ≤ b).card := by
        have hdisj := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin ξ)))
          (fun i => f (ω i) < a ∨ b < f (ω i))
        have hcompl : (Finset.univ.filter fun i : Fin ξ => ¬(f (ω i) < a ∨ b < f (ω i))) =
            Finset.univ.filter fun i : Fin ξ => a ≤ f (ω i) ∧ f (ω i) ≤ b := by
          ext i; simp [not_or, not_lt]
        rw [hcompl, Finset.card_univ, Fintype.card_fin] at hdisj
        omega
      have hlo : Fintype.card (Fin ξ) < 2 * (Finset.univ.filter fun i : Fin ξ => a ≤
        f (ω i)).card := by
        rw [Fintype.card_fin]
        have := Finset.card_le_card (s :=
          Finset.univ.filter fun i : Fin ξ => a ≤ f (ω i) ∧ f (ω i) ≤ b)
          (t := Finset.univ.filter fun i : Fin ξ => a ≤ f (ω i))
          fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.1⟩
        omega
      have hhi : Fintype.card (Fin ξ) < 2 * (Finset.univ.filter fun i : Fin ξ => f (ω i) ≤
        b).card := by
        rw [Fintype.card_fin]
        have := Finset.card_le_card (s :=
          Finset.univ.filter fun i : Fin ξ => a ≤ f (ω i) ∧ f (ω i) ≤ b)
          (t := Finset.univ.filter fun i : Fin ξ => f (ω i) ≤ b)
          fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.2⟩
        omega
      have h1 := Cslib.le_median hlo
      have h2 := Cslib.median_le hhi
      rcases hω with hlt_a | hgt_b <;> linarith
    have hmean_sum : (∑ _i : Fin ξ, ∑ x, (p x).toReal * score x) ≤ ξ * (1 / 4) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left hscore_mean (Nat.cast_nonneg ξ)
    simp only [Fintype.card_fin]
    linarith
  have hhoeff := Cslib.Probability.PMF.pi_sum_ge_mean_add_card_mul (fun _ : Fin ξ => p)
    (fun _ x => score x) (fun _ x _ => by dsimp only [score]; split_ifs <;> simp)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hmono := ENNReal.toReal_mono (pmf_toOuterMeasure_ne_top _ _)
    ((pi fun _ : Fin ξ => p).toOuterMeasure.mono hsub)
  refine hmono.trans (hhoeff.trans_eq ?_)
  congr 1
  simp only [Fintype.card_fin]
  ring

end Cslib.Probability.PMF
