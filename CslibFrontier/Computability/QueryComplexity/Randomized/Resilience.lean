/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Randomized.DistributionalDepth

import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Probability.Chernoff
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Chernoff bounds, the Resilience Lemma, and advantage depth amplification

This module proves:

- multiplicative
 Chernoff
 bounds for sums of independent `[0, 1]`-valued random variables and their transfer under MGF
 domination.
- expected total
 hardcore density equals `δ * k`.
- convex domination of `Dens_H(ℓ)` by `Bin(k, δ)`.
- lower and upper
 Chernoff concentration of `Dens_H(ℓ)` around `δ * k`.
- depth amplification for expected total hardcore advantage via random-block restriction.
-/

public section

namespace CslibFrontier.Computability.QueryComplexity.DirectSum

open Cslib Convexity Finset
open scoped BigOperators ENNReal NNReal

/-! ### -domination transfer -/

/-- Lower-tail Markov bound via moment generating function for `lam ≤ 0`. -/
theorem prob_le_of_mgf {α : Type*} [Fintype α] (p : PMF α) (Y : α → ℝ)
    {lam t : ℝ} (hlam : lam ≤ 0) :
    (∑ a, (p a).toReal * if Y a ≤ t then 1 else 0) ≤
      Real.exp (-lam * t) * ∑ a, (p a).toReal * Real.exp (lam * Y a) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [← mul_assoc, mul_comm (Real.exp (-lam * t)), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  split_ifs with h
  · have hmul : -lam * t + lam * Y a ≥ 0 := by nlinarith
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (-lam * t + lam * Y a) := Real.exp_le_exp.mpr hmul
      _ = Real.exp (-lam * t) * Real.exp (lam * Y a) := Real.exp_add _ _
  · positivity

/-- Upper-tail Markov bound via moment generating function for `0 ≤ lam`. -/
theorem prob_ge_of_mgf {α : Type*} [Fintype α] (p : PMF α) (Y : α → ℝ)
    {lam t : ℝ} (hlam : 0 ≤ lam) :
    (∑ a, (p a).toReal * if t ≤ Y a then 1 else 0) ≤
      Real.exp (-lam * t) * ∑ a, (p a).toReal * Real.exp (lam * Y a) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [← mul_assoc, mul_comm (Real.exp (-lam * t)), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  split_ifs with h
  · have hmul : -lam * t + lam * Y a ≥ 0 := by nlinarith
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (-lam * t + lam * Y a) := Real.exp_le_exp.mpr hmul
      _ = Real.exp (-lam * t) * Real.exp (lam * Y a) := Real.exp_add _ _
  · positivity

/-- Exact MGF of `Bin(k, δ)` (represented by `berSumPMF (fun _ ↦ δ)`). -/
theorem mgf_binomial {k : ℕ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (lam : ℝ) :
    (∑ z : Fin k → Bool,
      (berSumPMF (fun _ : Fin k ↦ δ) z).toReal * Real.exp (lam * (trueCount z : ℝ))) =
      (1 + δ * (Real.exp lam - 1)) ^ k := by
  induction k with
  | zero =>
    simp [berSumPMF_eq_pi, trueCount_eq_card_filter, Cslib.Probability.PMF.pi_apply]
  | succ k ih =>
    simp only [berSumPMF_eq_pi, Cslib.Probability.PMF.pi_fin_succ]
    rw [Cslib.Probability.PMF.sum_bind_mul, Fintype.sum_bool,
      bernoulliPMF_apply_true hδ0 hδ1, bernoulliPMF_apply_false hδ0 hδ1]
    have hstep (b : Bool) :
        (∑ z : Fin k → Bool,
          (berSumPMF (fun _ : Fin k ↦ δ) z).toReal *
            Real.exp (lam * (trueCount (Fin.cons b z) : ℝ))) =
        Real.exp (lam * (if b then 1 else 0)) * (1 + δ * (Real.exp lam - 1)) ^ k := by
      have htc : ∀ z : Fin k → Bool,
          (trueCount (Fin.cons b z) : ℝ) = (if b then 1 else 0) + (trueCount z : ℝ) := by
        intro z
        have := trueCount_fin_succ (Fin.cons b z)
        simp only [Fin.cons_zero, Fin.tail_cons] at this
        rw [this]
        cases b <;> simp
      calc (∑ z : Fin k → Bool,
            (berSumPMF (fun _ : Fin k ↦ δ) z).toReal *
              Real.exp (lam * (trueCount (Fin.cons b z) : ℝ)))
          = ∑ z : Fin k → Bool,
              Real.exp (lam * (if b then 1 else 0)) *
                ((berSumPMF (fun _ : Fin k ↦ δ) z).toReal * Real.exp (lam * (trueCount z : ℝ)))
                  := by
            refine Finset.sum_congr rfl fun z _ ↦ ?_
            rw [htc z, mul_add, Real.exp_add]
            ring
        _ = Real.exp (lam * (if b then 1 else 0)) * (1 + δ * (Real.exp lam - 1)) ^ k := by
            rw [← Finset.mul_sum, ih]
    have ht : (∑ y : Fin (k + 1) → Bool,
        (((berSumPMF (fun _ : Fin k ↦ δ)).map (Fin.cons true)) y).toReal *
          Real.exp (lam * (trueCount y : ℝ))) =
        Real.exp lam * (1 + δ * (Real.exp lam - 1)) ^ k := by
      rw [Cslib.Probability.PMF.sum_map_mul]
      simpa using hstep true
    have hf : (∑ y : Fin (k + 1) → Bool,
        (((berSumPMF (fun _ : Fin k ↦ δ)).map (Fin.cons false)) y).toReal *
          Real.exp (lam * (trueCount y : ℝ))) =
        (1 + δ * (Real.exp lam - 1)) ^ k := by
      rw [Cslib.Probability.PMF.sum_map_mul]
      simpa using hstep false
    change δ * _ + (1 - δ) * _ = _
    rw [← berSumPMF_eq_pi, ht, hf, pow_succ']
    ring

/-- MGF upper bound `E[exp(lam * Z)] ≤ exp(μ * (exp lam - 1))` for independent `[0,1]`-valued
variables. -/
theorem mgf_pi_sum_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc (0 : ℝ) 1) (lam : ℝ) :
    (∑ ω : ∀ i, α i,
      (Cslib.Probability.PMF.pi p ω).toReal * Real.exp (lam * ∑ i, score i (ω i))) ≤
      Real.exp ((∑ i, ∑ a, (p i a).toReal * score i a) * (Real.exp lam - 1)) := by
  let _ : ∀ i, MeasurableSpace (α i) := fun _ ↦ ⊤
  have _ : ∀ i, MeasurableSingletonClass (α i) := fun _ ↦ ⟨fun _ ↦ trivial⟩
  have h := Cslib.Probability.PMF.mgf_pi_sum_le p score hscore lam
  simpa only [ProbabilityTheory.mgf, PMF.integral_eq_sum, smul_eq_mul] using h

/-- any random variable `Y` whose MGF is dominated by that of a sum `Z`
of independent `[0,1]`-valued variables with mean `μ` satisfies
`Pr[Y ≤ t] ≤ exp(-(μ - t)^2 / (2 * μ))` for every `t ≤ μ` (and `0 < μ`). -/
theorem fact_chernoff_lower_of_mgf_le {α : Type*} [Fintype α] (q : PMF α) (Y : α → ℝ)
    {μ t : ℝ} (hμ : 0 < μ) (ht : t ≤ μ)
    (hmgf : ∀ lam : ℝ,
      (∑ a, (q a).toReal * Real.exp (lam * Y a)) ≤ Real.exp (μ * (Real.exp lam - 1))) :
    (∑ a, (q a).toReal * if Y a ≤ t then 1 else 0) ≤
      Real.exp (-((μ - t) ^ 2 / (2 * μ))) := by
  set u : ℝ := (μ - t) / μ
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr ht) hμ.le
  refine (prob_le_of_mgf q Y (lam := -u) (neg_nonpos.mpr hu)).trans ?_
  refine (mul_le_mul_of_nonneg_left (hmgf (-u)) (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hexp := Real.exp_neg_le_one_sub_add_sq_div_two hu
  have h1 : -(-u) * t + μ * (Real.exp (-u) - 1) ≤ u * t + μ * (-u + u ^ 2 / 2) := by
    nlinarith
  have h2 : u * t + μ * (-u + u ^ 2 / 2) = -((μ - t) ^ 2 / (2 * μ)) := by
    simp only [u]
    field_simp
    ring
  linarith

/-- any random variable `Y` whose MGF is dominated by `exp(μ(e^λ - 1))`
satisfies `Pr[Y ≥ 2μ] ≤ exp(-μ / 3)` for every `0 ≤ μ`. -/
theorem fact_chernoff_upper_of_mgf_le {α : Type*} [Fintype α] (q : PMF α) (Y : α → ℝ)
    {μ : ℝ} (hμ : 0 ≤ μ)
    (hmgf : ∀ lam : ℝ,
      (∑ a, (q a).toReal * Real.exp (lam * Y a)) ≤ Real.exp (μ * (Real.exp lam - 1))) :
    (∑ a, (q a).toReal * if 2 * μ ≤ Y a then 1 else 0) ≤ Real.exp (-(μ / 3)) := by
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
    norm_num at this
    linarith
  refine (prob_ge_of_mgf q Y (lam := Real.log 2) (Real.log_nonneg (by norm_num))).trans ?_
  refine (mul_le_mul_of_nonneg_left (hmgf (Real.log 2)) (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, Real.exp_log (by norm_num)]
  refine Real.exp_le_exp.mpr ?_
  nlinarith

/-- lower and upper tail bounds. -/
theorem fact_chernoff {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc (0 : ℝ) 1) :
    let μ := ∑ i, ∑ a, (p i a).toReal * score i a
    (∀ {t : ℝ}, 0 < μ → t ≤ μ →
      (∑ ω, (Cslib.Probability.PMF.pi p ω).toReal * if ∑ i, score i (ω i) ≤ t then 1 else 0) ≤
        Real.exp (-((μ - t) ^ 2 / (2 * μ)))) ∧
    (∑ ω, (Cslib.Probability.PMF.pi p ω).toReal * if 2 * μ ≤ ∑ i, score i (ω i) then 1 else 0) ≤
      Real.exp (-(μ / 3)) := by
  intro μ
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun a _ ↦ by
    by_cases ha : a ∈ (p i).support
    · exact mul_nonneg ENNReal.toReal_nonneg (hscore i a ha).1
    · rw [(PMF.apply_eq_zero_iff _ _).mpr ha, ENNReal.toReal_zero, zero_mul]
  exact ⟨fun hμ ht ↦ fact_chernoff_lower_of_mgf_le _ _ hμ ht (mgf_pi_sum_le_exp p score hscore),
    fact_chernoff_upper_of_mgf_le _ _ hμ0 (mgf_pi_sum_le_exp p score hscore)⟩

/-! ### -/

/-- If `H` has density `δ` w.r.t. `μ`, then $\mathbb{E}_{\ell \sim
\mu^k(T)}[\mathrm{Dens}_H(\ell)] =
 \delta k$. -/
theorem claim_expected_total_hardcore_density {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) {H : (Fin n → Bool) → ℝ} {δ : ℝ}
    (hδ : (∑ x : Fin n → Bool, (μ x).toReal * H x) = δ)
    (T : RandomizedDecisionTree (Fin k × Fin n) β) :
    leafExpect μ T (hardcoreDensity μ H) = δ * (k : ℝ) := by
  classical
  have hdet (t : DecisionTree (Fin k × Fin n) β) :
      (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
        hardcoreDensity μ H t (pathBlock t X)) = δ * (k : ℝ) := by
    simp only [hardcoreDensity_eq_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hardcoreDensityAt_eq_sum]
    calc (∑ i : Fin k, ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
          ∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal * H (Y i))
        = ∑ i : Fin k, ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal * H (X i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact sum_leafCondPMF_eq μ t (fun _ Y ↦ H (Y i))
      _ = ∑ _i : Fin k, δ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [prodPMF_eq_pi, Cslib.Probability.PMF.sum_pi_mul_eval, hδ]
      _ = δ * (k : ℝ) := by simp [mul_comm]
  simp only [leafExpect_eq_sum, hdet]
  rw [← Finsupp.sum_mul, T.total, one_mul]

/-! ### -/

/-- for every tree `T`, hardcore measure `H` of density `δ`, and
convex function `Φ : ℝ → ℝ`,
$\mathbb{E}_{\ell \sim \mu^k(T)}[\Phi(\mathrm{Dens}_H(\ell))] \le
 \mathbb{E}_{z \sim \mathrm{Bin}(k, \delta)}[\Phi(z)]$. -/
theorem lem_resilience_general {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) {H : (Fin n → Bool) → ℝ}
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ Set.univ Φ)
    (T : RandomizedDecisionTree (Fin k × Fin n) β) :
    let δ := ∑ x : Fin n → Bool, (μ x).toReal * H x
    leafExpect μ T (fun t ℓ ↦ Φ (hardcoreDensity μ H t ℓ)) ≤
      ∑ z : Fin k → Bool, (berSumPMF (fun _ : Fin k ↦ δ) z).toReal * Φ (trueCount z : ℝ) := by
  classical
  intro δ
  let kernel : (Fin k → Fin n → Bool) → PMF (Fin k → Bool) :=
    fun Y ↦ Cslib.Probability.PMF.pi (fun i : Fin k ↦ bernoulliPMF (H (Y i)))
  have hbind : (prodPMF μ k).bind kernel = berSumPMF (fun _ : Fin k ↦ δ) := by
    rw [prodPMF_eq_pi, berSumPMF_eq_pi]
    dsimp only [kernel]
    rw [← Cslib.Probability.PMF.pi_bind (fun _ : Fin k ↦ μ) (fun _ x ↦ bernoulliPMF (H x))]
    congr 1
    funext _
    ext b
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    rw [Cslib.Probability.PMF.bind_apply_toReal]
    have hδ0 : 0 ≤ δ := Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg (hH x).1
    have hδ1 : δ ≤ 1 := Cslib.Probability.PMF.sum_mul_le μ H 1 fun x ↦ (hH x).2
    cases b
    · rw [bernoulliPMF_apply_false hδ0 hδ1]
      calc (∑ x : Fin n → Bool, (μ x).toReal * (bernoulliPMF (H x) false).toReal)
          = ∑ x : Fin n → Bool, (μ x).toReal * (1 - H x) :=
            Finset.sum_congr rfl fun x _ ↦ by
              rw [bernoulliPMF_apply_false (hH x).1 (hH x).2]
        _ = 1 - δ := by
            simp only [mul_sub, mul_one, Finset.sum_sub_distrib,
              Cslib.Probability.PMF.sum_toReal, δ]
    · rw [bernoulliPMF_apply_true hδ0 hδ1]
      exact Finset.sum_congr rfl fun x _ ↦ by
        rw [bernoulliPMF_apply_true (hH x).1 (hH x).2]
  have hdet (t : DecisionTree (Fin k × Fin n) β) :
      (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
        Φ (hardcoreDensity μ H t (pathBlock t X))) ≤
      ∑ z : Fin k → Bool, (berSumPMF (fun _ : Fin k ↦ δ) z).toReal * Φ (trueCount z : ℝ) := by
    have hjensen (ℓ : List Bool) :
        Φ (hardcoreDensity μ H t ℓ) ≤
          ∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t ℓ Y).toReal *
            ∑ z : Fin k → Bool, (kernel Y z).toReal * Φ (trueCount z : ℝ) := by
      let w : (Fin k → Fin n → Bool) × (Fin k → Bool) → ℝ :=
        fun p ↦ (leafCondPMF μ t ℓ p.1).toReal * (kernel p.1 p.2).toReal
      have hw0 : ∀ p ∈ (Finset.univ : Finset ((Fin k → Fin n → Bool) × (Fin k → Bool))),
          0 ≤ w p := fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have hw1 : ∑ p : (Fin k → Fin n → Bool) × (Fin k → Bool), w p = 1 := by
        rw [Fintype.sum_prod_type]
        simp only [w, ← Finset.mul_sum, Cslib.Probability.PMF.sum_toReal, mul_one]
      have harg : (∑ p : (Fin k → Fin n → Bool) × (Fin k → Bool),
            w p * (trueCount p.2 : ℝ)) = hardcoreDensity μ H t ℓ := by
        rw [Fintype.sum_prod_type]
        have hmeanY (Y : Fin k → Fin n → Bool) :
            (∑ z : Fin k → Bool, (kernel Y z).toReal * (trueCount z : ℝ)) =
              ∑ i : Fin k, H (Y i) := by
          have htc : ∀ z : Fin k → Bool,
              (trueCount z : ℝ) = ∑ i : Fin k, if z i = true then (1 : ℝ) else 0 :=
            trueCount_cast_eq_sum
          simp_rw [htc]
          dsimp only [kernel]
          rw [Cslib.Probability.PMF.sum_pi_mul_sum (fun i : Fin k ↦ bernoulliPMF (H (Y i)))
            (fun _ b ↦ if b = true then (1 : ℝ) else 0)]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Fintype.sum_bool, bernoulliPMF_apply_true (hH (Y i)).1 (hH (Y i)).2]
          simp
        calc (∑ Y : Fin k → Fin n → Bool, ∑ z : Fin k → Bool,
              (leafCondPMF μ t ℓ Y).toReal * (kernel Y z).toReal * (trueCount z : ℝ))
            = ∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t ℓ Y).toReal *
                ∑ z : Fin k → Bool, (kernel Y z).toReal * (trueCount z : ℝ) := by
              refine Finset.sum_congr rfl fun Y _ ↦ ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun z _ ↦ by ring
          _ = ∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t ℓ Y).toReal * ∑ i : Fin k, H (Y i) := by
              refine Finset.sum_congr rfl fun Y _ ↦ by rw [hmeanY Y]
          _ = hardcoreDensity μ H t ℓ := by
              simp only [hardcoreDensity_eq_sum, hardcoreDensityAt_eq_sum, Finset.mul_sum]
              rw [Finset.sum_comm]
      have hconv := hΦ.map_sum_le hw0 hw1 (fun p _ ↦ Set.mem_univ (trueCount p.2 : ℝ))
      simp only [smul_eq_mul] at hconv
      rw [harg] at hconv
      refine hconv.trans_eq ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun Y _ ↦ ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ ↦ by ring
    calc (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
          Φ (hardcoreDensity μ H t (pathBlock t X)))
        ≤ ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
            ∑ Y : Fin k → Fin n → Bool, (leafCondPMF μ t (pathBlock t X) Y).toReal *
              ∑ z : Fin k → Bool, (kernel Y z).toReal * Φ (trueCount z : ℝ) :=
          Finset.sum_le_sum fun X _ ↦ mul_le_mul_of_nonneg_left (hjensen _) ENNReal.toReal_nonneg
      _ = ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
            ∑ z : Fin k → Bool, (kernel X z).toReal * Φ (trueCount z : ℝ) :=
          sum_leafCondPMF_eq μ t
            (fun _ Y ↦ ∑ z : Fin k → Bool, (kernel Y z).toReal * Φ (trueCount z : ℝ))
      _ = ∑ z : Fin k → Bool, ((prodPMF μ k).bind kernel z).toReal * Φ (trueCount z : ℝ) :=
          (Cslib.Probability.PMF.sum_bind_mul (prodPMF μ k) kernel _).symm
      _ = ∑ z : Fin k → Bool, (berSumPMF (fun _ : Fin k ↦ δ) z).toReal * Φ (trueCount z : ℝ) := by
          rw [hbind]
  calc leafExpect μ T (fun t ℓ ↦ Φ (hardcoreDensity μ H t ℓ))
      ≤ T.weights.sum fun _ w ↦ w *
          ∑ z : Fin k → Bool, (berSumPMF (fun _ : Fin k ↦ δ) z).toReal * Φ (trueCount z : ℝ) := by
        rw [leafExpect_eq_sum]
        exact Finset.sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left (hdet t) (T.weights_nonneg t)
    _ = ∑ z : Fin k → Bool, (berSumPMF (fun _ : Fin k ↦ δ) z).toReal * Φ (trueCount z : ℝ) := by
        rw [← Finsupp.sum_mul, T.total, one_mul]

/-- For any hardcore measure `H` of density `δ` w.r.t. `μ` and any tree `T`:
- $\Pr_{\ell \sim \mu^k(T)}[\mathrm{Dens}_H(\ell) \le \delta k / 2] \le e^{-\delta k / 8}$,
- $\Pr_{\ell \sim \mu^k(T)}[\mathrm{Dens}_H(\ell) \ge 2 \delta k] \le e^{-\delta k / 3}$. -/
theorem lem_resilience {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) {H : (Fin n → Bool) → ℝ}
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) 1)
    (T : RandomizedDecisionTree (Fin k × Fin n) β) :
    let δ := ∑ x : Fin n → Bool, (μ x).toReal * H x
    leafExpect μ T (fun t ℓ ↦ if hardcoreDensity μ H t ℓ ≤ δ * k / 2 then 1 else 0) ≤
        Real.exp (-(δ * k / 8)) ∧
      leafExpect μ T (fun t ℓ ↦ if 2 * (δ * k) ≤ hardcoreDensity μ H t ℓ then 1 else 0) ≤
        Real.exp (-(δ * k / 3)) := by
  classical
  intro δ
  have hδ0 : 0 ≤ δ := Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg (hH x).1
  have hδ1 : δ ≤ 1 := Cslib.Probability.PMF.sum_mul_le μ H 1 fun x ↦ (hH x).2
  have hmgf_dom : ∀ (t : DecisionTree (Fin k × Fin n) β) (lam : ℝ),
      (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
        Real.exp (lam * hardcoreDensity μ H t (pathBlock t X))) ≤
      Real.exp ((δ * k) * (Real.exp lam - 1)) := by
    intro t lam
    have hconv : ConvexOn ℝ Set.univ (fun z : ℝ ↦ Real.exp (lam * z)) :=
      convexOn_exp.comp_linearMap (LinearMap.mulLeft ℝ lam)
    have hres := lem_resilience_general μ hH hconv (StdSimplex.single t)
    rw [leafExpect_single] at hres
    refine hres.trans ?_
    rw [mgf_binomial hδ0 hδ1 lam]
    have h1 : 0 ≤ 1 + δ * (Real.exp lam - 1) := by
      have hexp : 0 ≤ Real.exp lam := (Real.exp_pos lam).le
      nlinarith
    have h2 : 1 + δ * (Real.exp lam - 1) ≤ Real.exp (δ * (Real.exp lam - 1)) := by
      linarith [Real.add_one_le_exp (δ * (Real.exp lam - 1))]
    calc (1 + δ * (Real.exp lam - 1)) ^ k
        ≤ (Real.exp (δ * (Real.exp lam - 1))) ^ k := pow_le_pow_left₀ h1 h2 k
      _ = Real.exp ((δ * k) * (Real.exp lam - 1)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  constructor
  · rcases eq_or_lt_of_le (mul_nonneg hδ0 (Nat.cast_nonneg k)) with h0 | hpos
    · rw [← h0]
      simp only [zero_div, neg_zero, Real.exp_zero]
      calc leafExpect μ T (fun t ℓ ↦ if hardcoreDensity μ H t ℓ ≤ 0 then 1 else 0)
          ≤ T.weights.sum fun _ w ↦ w * 1 := by
            rw [leafExpect_eq_sum]
            refine Finset.sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left ?_ (T.weights_nonneg t)
            exact Cslib.Probability.PMF.sum_mul_le (prodPMF μ k) _ 1 fun _ ↦ by
              split_ifs <;> norm_num
        _ = 1 := by simp [T.total]
    · have hdet (t : DecisionTree (Fin k × Fin n) β) :
          (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
            if hardcoreDensity μ H t (pathBlock t X) ≤ δ * k / 2 then 1 else 0) ≤
          Real.exp (-(δ * k / 8)) := by
        have hc := fact_chernoff_lower_of_mgf_le (prodPMF μ k)
          (fun X ↦ hardcoreDensity μ H t (pathBlock t X)) hpos
          (show δ * (k : ℝ) / 2 ≤ δ * k by linarith) (hmgf_dom t)
        refine hc.trans_eq ?_
        congr 1
        field_simp
        ring
      calc leafExpect μ T (fun t ℓ ↦ if hardcoreDensity μ H t ℓ ≤ δ * k / 2 then 1 else 0)
          ≤ T.weights.sum fun _ w ↦ w * Real.exp (-(δ * k / 8)) := by
            rw [leafExpect_eq_sum]
            exact Finset.sum_le_sum fun t _ ↦
              mul_le_mul_of_nonneg_left (hdet t) (T.weights_nonneg t)
        _ = Real.exp (-(δ * k / 8)) := by rw [← Finsupp.sum_mul, T.total, one_mul]
  · have hdet (t : DecisionTree (Fin k × Fin n) β) :
        (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
          if 2 * (δ * k) ≤ hardcoreDensity μ H t (pathBlock t X) then 1 else 0) ≤
        Real.exp (-(δ * k / 3)) :=
      fact_chernoff_upper_of_mgf_le (prodPMF μ k)
        (fun X ↦ hardcoreDensity μ H t (pathBlock t X)) (by positivity) (hmgf_dom t)
    calc leafExpect μ T (fun t ℓ ↦ if 2 * (δ * k) ≤ hardcoreDensity μ H t ℓ then 1 else 0)
        ≤ T.weights.sum fun _ w ↦ w * Real.exp (-(δ * k / 3)) := by
          rw [leafExpect_eq_sum]
          exact Finset.sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left (hdet t) (T.weights_nonneg t)
      _ = Real.exp (-(δ * k / 3)) := by rw [← Finsupp.sum_mul, T.total, one_mul]

/-! ### -/

/-- Flip leaf labels at `(t, ℓ, i)` whenever the conditional correlation in block `i` is negative,
eliminating the absolute value in `hardcoreAdvantageAt` without changing tree structure. -/
private noncomputable def orientTreeAux {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (tOrig : DecisionTree (Fin k × Fin n) (Fin k → Bool)) :
    List Bool → DecisionTree (Fin k × Fin n) (Fin k → Bool) →
      DecisionTree (Fin k × Fin n) (Fin k → Bool)
  | revPath, .leaf y =>
    .leaf fun i ↦
      if 0 ≤ ∑ X : Fin k → Fin n → Bool,
          (leafCondPMF μ tOrig revPath.reverse X).toReal *
            (signBool (f (X i)) * signBool (y i) * H (X i))
      then y i else !(y i)
  | revPath, .node q t₀ t₁ =>
    .node q (orientTreeAux μ f H tOrig (false :: revPath) t₀)
      (orientTreeAux μ f H tOrig (true :: revPath) t₁)

private noncomputable def orientTree {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool)) :
    DecisionTree (Fin k × Fin n) (Fin k → Bool) :=
  orientTreeAux μ f H t [] t

private theorem cost_orientTreeAux {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (tOrig : DecisionTree (Fin k × Fin n) (Fin k → Bool))
    (revPath : List Bool) (t : DecisionTree (Fin k × Fin n) (Fin k → Bool))
    (x : Fin k × Fin n → Bool) :
    (orientTreeAux μ f H tOrig revPath t).cost x = t.cost x := by
  induction t generalizing revPath with
  | leaf _ => rfl
  | node q t₀ t₁ ih₀ ih₁ =>
    simp only [orientTreeAux, DecisionTree.cost_node]
    cases x q <;> simp [ih₀, ih₁]

private theorem eval_orientTreeAux {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (tOrig : DecisionTree (Fin k × Fin n) (Fin k → Bool))
    (revPath : List Bool) (t : DecisionTree (Fin k × Fin n) (Fin k → Bool))
    (X : Fin k → Fin n → Bool) (i : Fin k) :
    evalBlock (orientTreeAux μ f H tOrig revPath t) X i =
      if 0 ≤ ∑ Y : Fin k → Fin n → Bool,
          (leafCondPMF μ tOrig (revPath.reverse ++ pathBlock t X) Y).toReal *
            (signBool (f (Y i)) * signBool (evalBlock t X i) * H (Y i))
      then evalBlock t X i else !(evalBlock t X i) := by
  induction t generalizing revPath with
  | leaf y =>
    simp [orientTreeAux]
  | node q t₀ t₁ ih₀ ih₁ =>
    simp only [orientTreeAux, evalBlock_node, pathBlock_node]
    rcases Bool.eq_false_or_eq_true (X q.1 q.2) with h | h <;> simp only [h, Bool.cond_false,
      Bool.cond_true]
    · simpa [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih₁ (true :: revPath)
    · simpa [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih₀ (false :: revPath)

/-- Extract a `PMF` over the finite support of a `StdSimplex`. -/
private noncomputable def supportPMFRes {α : Type*} (T : StdSimplex ℝ α) :
    PMF {a // a ∈ T.weights.support} :=
  PMF.ofFintype (fun s ↦ ENNReal.ofReal (T.weights s.1)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ ↦ T.weights_nonneg s.1)]
    have hsum : (∑ s : {a // a ∈ T.weights.support}, T.weights s.1) = 1 := by
      rw [Finset.sum_coe_sort T.weights.support (fun a ↦ T.weights a)]
      exact T.total
    rw [hsum, ENNReal.ofReal_one])

private theorem supportPMFRes_toReal {α : Type*} (T : StdSimplex ℝ α)
    (s : {a // a ∈ T.weights.support}) :
    (supportPMFRes T s).toReal = T.weights s.1 :=
  ENNReal.toReal_ofReal (T.weights_nonneg s.1)

private theorem mem_support_leafCondPMF_path_eq {n k : ℕ} {β : Type*}
    (μ : PMF (Fin n → Bool)) (t : DecisionTree (Fin k × Fin n) β)
    {X Y : Fin k → Fin n → Bool} (hX : prodPMF μ k X ≠ 0)
    (hY : Y ∈ (leafCondPMF μ t (pathBlock t X)).support) :
    pathBlock t Y = pathBlock t X := by
  classical
  rw [leafCondPMF_eq] at hY
  have hmapfst : (((prodPMF μ k).map fun Z ↦ (pathBlock t Z, Z)).map Prod.fst) =
      (prodPMF μ k).map (pathBlock t) := by
    rw [PMF.map_comp]; rfl
  have hsupp : pathBlock t X ∈
      (((prodPMF μ k).map fun Z ↦ (pathBlock t Z, Z)).map Prod.fst).support := by
    rw [hmapfst]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨X, (PMF.mem_support_iff _ _).mpr hX, rfl⟩
  have hjoint := (Cslib.Probability.PMF.mem_support_conditionalSnd_iff _ _ hsupp Y).mp hY
  obtain ⟨Z, _, hZ⟩ := (PMF.mem_support_map_iff _ _ _).mp hjoint
  have hZY : Z = Y := congrArg Prod.snd hZ
  have hZp : pathBlock t Z = pathBlock t X := congrArg Prod.fst hZ
  rwa [hZY] at hZp

private theorem signBool_eval_orientTree {n k : ℕ} (μ : PMF (Fin n → Bool))
    (f : (Fin n → Bool) → Bool) (H : (Fin n → Bool) → ℝ)
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool))
    {X : Fin k → Fin n → Bool} (hX : prodPMF μ k X ≠ 0) (i : Fin k) :
    (∑ Y : Fin k → Fin n → Bool,
      (leafCondPMF μ t (pathBlock t X) Y).toReal *
        (signBool (f (Y i)) * signBool (evalBlock (orientTree μ f H t) Y i) * H (Y i))) =
      hardcoreAdvantageAt μ f H t (pathBlock t X) i := by
  classical
  set c : ℝ := ∑ Y : Fin k → Fin n → Bool,
    (leafCondPMF μ t (pathBlock t X) Y).toReal *
      (signBool (f (Y i)) * signBool (evalBlock t Y i) * H (Y i))
  have hpt : ∀ Y : Fin k → Fin n → Bool,
      (leafCondPMF μ t (pathBlock t X) Y).toReal *
        (signBool (f (Y i)) * signBool (evalBlock (orientTree μ f H t) Y i) * H (Y i)) =
      (if 0 ≤ c then 1 else -1) *
        ((leafCondPMF μ t (pathBlock t X) Y).toReal *
          (signBool (f (Y i)) * signBool (evalBlock t Y i) * H (Y i))) := by
    intro Y
    by_cases hY : Y ∈ (leafCondPMF μ t (pathBlock t X)).support
    · have hpath : pathBlock t Y = pathBlock t X := mem_support_leafCondPMF_path_eq μ t hX hY
      have hev_t : evalBlock t Y = evalBlock t X :=
        DecisionTree.eval_eq_of_path_eq t hpath
      have hsign : signBool (evalBlock (orientTree μ f H t) Y i) =
          (if 0 ≤ c then 1 else -1) * signBool (evalBlock t Y i) := by
        have horient := eval_orientTreeAux μ f H t [] t Y i
        simp only [List.reverse_nil, List.nil_append] at horient
        change evalBlock (orientTree μ f H t) Y i = _ at horient
        have hc_eq : (∑ Z : Fin k → Fin n → Bool,
            (leafCondPMF μ t (pathBlock t Y) Z).toReal *
              (signBool (f (Z i)) * signBool (evalBlock t Y i) * H (Z i))) = c := by
          rw [hpath]
          refine Finset.sum_congr rfl fun Z _ ↦ ?_
          by_cases hZ : Z ∈ (leafCondPMF μ t (pathBlock t X)).support
          · have hZp := mem_support_leafCondPMF_path_eq μ t hX hZ
            have hZev : evalBlock t Z = evalBlock t Y :=
              DecisionTree.eval_eq_of_path_eq t (hZp.trans hpath.symm)
            rw [hZev]
          · have hZ0 : leafCondPMF μ t (pathBlock t X) Z = 0 :=
              (PMF.apply_eq_zero_iff _ _).mpr hZ
            simp [hZ0]
        rw [horient]
        by_cases hc : 0 ≤ c
        · simp [hc_eq, hc]
        · simp [hc_eq, hc]
      rw [hsign]
      ring
    · have hY0 : leafCondPMF μ t (pathBlock t X) Y = 0 := (PMF.apply_eq_zero_iff _ _).mpr hY
      simp [hY0]
  simp_rw [hpt, ← Finset.mul_sum]
  rw [hardcoreAdvantageAt_eq_abs]
  change (if 0 ≤ c then 1 else -1) * c = |c|
  split_ifs with hc
  · rw [one_mul, abs_of_nonneg hc]
  · rw [neg_one_mul, abs_of_neg (lt_of_not_ge hc)]

/-- Restrict a block tree `t` to block `i` by fixing all other blocks `j ≠ i` to `X j`. -/
private def restrictBlock {n k : ℕ}
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool))
    (i : Fin k) (X : Fin k → Fin n → Bool) : DecisionTree (Fin n) Bool :=
  match t with
  | .leaf y => .leaf (y i)
  | .node q t₀ t₁ =>
    if q.1 = i then
      .node q.2 (restrictBlock t₀ i X) (restrictBlock t₁ i X)
    else
      cond (X q.1 q.2) (restrictBlock t₁ i X) (restrictBlock t₀ i X)

private theorem eval_restrictBlock {n k : ℕ}
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool))
    (i : Fin k) (X : Fin k → Fin n → Bool) (x : Fin n → Bool) :
    (restrictBlock t i X).eval x = evalBlock t (Function.update X i x) i := by
  induction t with
  | leaf y => rfl
  | node q t₀ t₁ ih₀ ih₁ =>
    rcases q with ⟨j, m⟩
    simp only [restrictBlock, evalBlock_node]
    by_cases hji : j = i
    · subst hji
      simp only [ite_true, DecisionTree.eval_node, Function.update_self]
      cases x m <;> simp [ih₀, ih₁]
    · simp only [hji, ite_false, Function.update_of_ne hji]
      cases X j m <;> simp [ih₀, ih₁]

private theorem cost_restrictBlock {n k : ℕ}
    (t : DecisionTree (Fin k × Fin n) (Fin k → Bool))
    (i : Fin k) (X : Fin k → Fin n → Bool) (x : Fin n → Bool) :
    (restrictBlock t i X).cost x =
      t.weightedCost (fun q ↦ if q.1 = i then 1 else 0)
        (Function.uncurry (Function.update X i x)) := by
  induction t with
  | leaf y => rfl
  | node q t₀ t₁ ih₀ ih₁ =>
    rcases q with ⟨j, m⟩
    simp only [restrictBlock, DecisionTree.weightedCost_node, Function.uncurry_apply_pair]
    by_cases hji : j = i
    · subst hji
      simp only [ite_true, DecisionTree.cost_node, Function.update_self]
      cases x m
      · exact congrArg (· + 1) ih₀
      · exact congrArg (· + 1) ih₁
    · simp only [hji, ite_false, Function.update_of_ne hji, add_zero]
      cases X j m
      · exact ih₀
      · exact ih₁

private theorem sum_weightedCost_block {n k : ℕ} {β : Type*}
    (t : DecisionTree (Fin k × Fin n) β) (y : Fin k × Fin n → Bool) :
    (∑ i : Fin k, t.weightedCost (fun q ↦ if q.1 = i then 1 else 0) y) = t.cost y := by
  induction t with
  | leaf _ => simp
  | node q t₀ t₁ ih₀ ih₁ =>
    simp only [DecisionTree.weightedCost_node, DecisionTree.cost_node, Finset.sum_add_distrib]
    have h1 : (∑ i : Fin k, if q.1 = i then (1 : ℕ) else 0) = 1 := by
      simp
    rw [h1]
    cases y q <;> simp [ih₀, ih₁]

/-- Replacing block `i` of a product draw by an independent draw from `μ`
preserves `prodPMF μ k`. -/
private theorem prodPMF_update_sum {n k : ℕ} (μ : PMF (Fin n → Bool)) (i : Fin k)
    (F : (Fin k → Fin n → Bool) → ℝ) :
    (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
      ∑ x : Fin n → Bool, (μ x).toReal * F (Function.update X i x)) =
      ∑ Y : Fin k → Fin n → Bool, (prodPMF μ k Y).toReal * F Y := by
  classical
  let swap : (Fin k → Fin n → Bool) × (Fin n → Bool) →
      (Fin k → Fin n → Bool) × (Fin n → Bool) :=
    fun p ↦ (Function.update p.1 i p.2, p.1 i)
  have hswap : Function.Involutive swap := by
    rintro ⟨X, x⟩
    ext j m
    · by_cases hji : j = i
      · subst hji; simp [swap]
      · simp [swap, hji]
    · simp [swap]
  have hweight : ∀ p : (Fin k → Fin n → Bool) × (Fin n → Bool),
      (prodPMF μ k p.1).toReal * (μ p.2).toReal =
        (prodPMF μ k (swap p).1).toReal * (μ (swap p).2).toReal := by
    rintro ⟨X, x⟩
    simp only [swap, prodPMF_apply, ENNReal.toReal_prod]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
    have hrest : (∏ j ∈ Finset.univ.erase i, (μ (Function.update X i x j)).toReal) =
        ∏ j ∈ Finset.univ.erase i, (μ (X j)).toReal :=
      Finset.prod_congr rfl fun j hj ↦ by rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rw [hrest]
    ring
  calc (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
        ∑ x : Fin n → Bool, (μ x).toReal * F (Function.update X i x))
      = ∑ p : (Fin k → Fin n → Bool) × (Fin n → Bool),
          (prodPMF μ k p.1).toReal * (μ p.2).toReal * F (Function.update p.1 i p.2) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun X _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ ↦ by ring
    _ = ∑ p : (Fin k → Fin n → Bool) × (Fin n → Bool),
          (prodPMF μ k (swap p).1).toReal * (μ (swap p).2).toReal * F (swap p).1 := by
        refine Finset.sum_congr rfl fun p _ ↦ by rw [hweight p]
    _ = ∑ q : (Fin k → Fin n → Bool) × (Fin n → Bool),
          (prodPMF μ k q.1).toReal * (μ q.2).toReal * F q.1 :=
        Equiv.sum_comp hswap.toPerm fun q ↦
          (prodPMF μ k q.1).toReal * (μ q.2).toReal * F q.1
    _ = ∑ Y : Fin k → Fin n → Bool, (prodPMF μ k Y).toReal * F Y := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun Y _ ↦ ?_
        simp only [mul_assoc]
        rw [← Finset.mul_sum, ← Finset.sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]

/-- If `H` is a `(γ, d)`-hardcore measure for `f` of density `δ` w.r.t. `μ` and `T` has expected
depth
at most `d * k` w.r.t. `μ^k`, then
$\mathbb{E}_{\ell \sim \mu^k(T)}[\mathrm{Adv}_H(\ell)] \le
 \gamma \cdot \mathbb{E}_{\ell \sim \mu^k(T)}[\mathrm{Dens}_H(\ell)] = \gamma \delta k$. -/
theorem lem_expected_total_hardcore_advantage {n k : ℕ}
    (μ : PMF (Fin n → Bool)) (f : (Fin n → Bool) → Bool)
    {H : (Fin n → Bool) → ℝ} {γ d δ : ℝ}
    (hH : IsHardcoreMeasure μ f γ d δ H)
    (T : RandomizedDecisionTree (Fin k × Fin n) (Fin k → Bool))
    (hdepth : randProdExpectedDepth μ T ≤ d * (k : ℝ)) :
    leafExpect μ T (hardcoreAdvantage μ f H) ≤
      γ * leafExpect μ T (hardcoreDensity μ H) := by
  classical
  rw [claim_expected_total_hardcore_density μ hH.density T]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [leafExpect_eq_sum]
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let qTree : PMF {t // t ∈ T.weights.support} := supportPMFRes T
  let qAll : PMF ({t // t ∈ T.weights.support} × Fin k × (Fin k → Fin n → Bool)) :=
    qTree.bind fun t ↦
      (Cslib.Probability.PMF.uniformOfFintype (Fin k)).bind fun i ↦
        (prodPMF μ k).map fun X ↦ (t, i, X)
  let Tsmall : RandomizedDecisionTree (Fin n) Bool :=
    (Cslib.Probability.PMF.toStdSimplex qAll).map
      (fun p ↦ restrictBlock (orientTree μ f H p.1.1) p.2.1 p.2.2)
  have hTsmall_depth : randExpectedDepthTree μ Tsmall ≤ d := by
    have heq : randExpectedDepthTree μ Tsmall = randProdExpectedDepth μ T / (k : ℝ) := by
      rw [randExpectedDepthTree_eq_sum]
      dsimp only [Tsmall]
      rw [StdSimplex.weights_map,
        Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
        Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
      simp only [Cslib.Probability.PMF.weights_toStdSimplex, detExpectedDepth_eq_sum,
        qAll, Cslib.Probability.PMF.sum_bind_mul, Cslib.Probability.PMF.sum_map_mul,
        Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        Fintype.card_fin]
      have hinner (t : {t // t ∈ T.weights.support}) :
          (∑ i : Fin k, (k : ℝ)⁻¹ * ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
            ∑ x : Fin n → Bool, (μ x).toReal *
              ((restrictBlock (orientTree μ f H t.1) i X).cost x : ℝ)) =
            detProdExpectedDepth μ t.1 / (k : ℝ) := by
        rw [← Finset.mul_sum, detProdExpectedDepth_eq_sum]
        have hsum : (∑ i : Fin k, ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
            ∑ x : Fin n → Bool, (μ x).toReal *
              ((restrictBlock (orientTree μ f H t.1) i X).cost x : ℝ)) =
            ∑ Y : Fin k → Fin n → Bool, (prodPMF μ k Y).toReal * (costBlock t.1 Y : ℝ) := by
          have hstep (i : Fin k) :
              (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
                ∑ x : Fin n → Bool, (μ x).toReal *
                  ((restrictBlock (orientTree μ f H t.1) i X).cost x : ℝ)) =
                ∑ Y : Fin k → Fin n → Bool, (prodPMF μ k Y).toReal *
                  ((orientTree μ f H t.1).weightedCost (fun q ↦ if q.1 = i then 1 else 0)
                    (Function.uncurry Y) : ℝ) := by
            simp_rw [cost_restrictBlock]
            exact prodPMF_update_sum μ i fun Y ↦
              ((orientTree μ f H t.1).weightedCost (fun q ↦ if q.1 = i then 1 else 0)
                (Function.uncurry Y) : ℝ)
          simp_rw [hstep]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun Y _ ↦ ?_
          rw [← Finset.mul_sum]
          congr 1
          have := sum_weightedCost_block (orientTree μ f H t.1) (Function.uncurry Y)
          have hcost_eq : (orientTree μ f H t.1).cost (Function.uncurry Y) = costBlock t.1 Y :=
            cost_orientTreeAux μ f H t.1 [] t.1 (Function.uncurry Y)
          rw [← hcost_eq, ← this, Nat.cast_sum]
        rw [hsum, inv_mul_eq_div]
      simp_rw [hinner]
      simp only [qTree, supportPMFRes_toReal, randProdExpectedDepth_eq_sum, Finsupp.sum,
        Finset.sum_div, ← mul_div_assoc]
      exact Finset.sum_coe_sort T.weights.support
        (fun t ↦ T.weights t * detProdExpectedDepth μ t / (k : ℝ))
    rw [heq, div_le_iff₀ hkR]
    exact hdepth
  have hTsmall_corr :
      (Tsmall.weights.sum fun t w ↦
        w * ∑ x : Fin n → Bool, (μ x).toReal * (signBool (f x) * signBool (t.eval x) * H x)) =
      leafExpect μ T (hardcoreAdvantage μ f H) / (k : ℝ) := by
    dsimp only [Tsmall]
    rw [StdSimplex.weights_map,
      Finsupp.sum_mapDomain_index (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
      Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
    simp only [Cslib.Probability.PMF.weights_toStdSimplex,
      qAll, Cslib.Probability.PMF.sum_bind_mul, Cslib.Probability.PMF.sum_map_mul,
      Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Fintype.card_fin]
    have hinner (t : {t // t ∈ T.weights.support}) :
        (∑ i : Fin k, (k : ℝ)⁻¹ * ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
          ∑ x : Fin n → Bool, (μ x).toReal *
            (signBool (f x) * signBool ((restrictBlock (orientTree μ f H t.1) i X).eval x) * H x)) =
          (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
            hardcoreAdvantage μ f H t.1 (pathBlock t.1 X)) / (k : ℝ) := by
      rw [← Finset.mul_sum, inv_mul_eq_div]
      congr 1
      have hstep (i : Fin k) :
          (∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
            ∑ x : Fin n → Bool, (μ x).toReal *
              (signBool (f x) *
                signBool ((restrictBlock (orientTree μ f H t.1) i X).eval x) * H x)) =
            ∑ Y : Fin k → Fin n → Bool, (prodPMF μ k Y).toReal *
              (signBool (f (Y i)) *
                signBool (evalBlock (orientTree μ f H t.1) Y i) * H (Y i)) := by
        have := prodPMF_update_sum μ i fun Y ↦
          signBool (f (Y i)) * signBool (evalBlock (orientTree μ f H t.1) Y i) * H (Y i)
        refine (Finset.sum_congr rfl fun X _ ↦
          congrArg _ (Finset.sum_congr rfl fun x _ ↦ ?_)).trans this
        rw [eval_restrictBlock, Function.update_self]
      simp_rw [hstep]
      have hcond (i : Fin k) :
          (∑ Y : Fin k → Fin n → Bool, (prodPMF μ k Y).toReal *
            (signBool (f (Y i)) *
              signBool (evalBlock (orientTree μ f H t.1) Y i) * H (Y i))) =
            ∑ X : Fin k → Fin n → Bool, (prodPMF μ k X).toReal *
              hardcoreAdvantageAt μ f H t.1 (pathBlock t.1 X) i := by
        rw [← sum_leafCondPMF_eq μ t.1
          (fun _ Y ↦ signBool (f (Y i)) *
            signBool (evalBlock (orientTree μ f H t.1) Y i) * H (Y i))]
        refine Finset.sum_congr rfl fun X _ ↦ ?_
        by_cases hX : prodPMF μ k X = 0
        · simp [hX]
        · congr 1
          exact signBool_eval_orientTree μ f H t.1 hX i
      simp_rw [hcond]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun X _ ↦ ?_
      rw [← Finset.mul_sum, hardcoreAdvantage_eq_sum]
    simp_rw [hinner]
    simp only [qTree, supportPMFRes_toReal, leafExpect_eq_sum, Finsupp.sum, Finset.sum_div,
      mul_div_assoc]
    exact Finset.sum_coe_sort T.weights.support (fun t ↦
      T.weights t * ∑ X : Fin k → Fin n → Bool,
        (prodPMF μ k X).toReal * (hardcoreAdvantage μ f H t (pathBlock t X) / (k : ℝ)))
  have hcorr := hH.correlation_le Tsmall hTsmall_depth
  rw [hTsmall_corr, div_le_iff₀ hkR] at hcorr
  linarith

end CslibFrontier.Computability.QueryComplexity.DirectSum

end
