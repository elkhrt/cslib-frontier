/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Mathlib.Analysis.Real.Sqrt
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree.Dual

import CslibFrontier.Computability.QueryComplexity.NisanSzegedy
import CslibFrontier.Computability.QueryComplexity.Threshold
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Approximate Degree of the Two-Level AND–OR Tree

This module proves the Bun–Thaler / Sherstov approximate degree lower bound
$\widetilde{\deg}_{1/3}(\mathrm{AND}_m \circ \mathrm{OR}_n^m) \ge \frac{1}{12}\sqrt{mn}$ via
dual-polynomial composition exploiting the exact one-sided error of the inner $\mathrm{OR}_n$ dual.

## Main results

* `CslibFrontier.QueryComplexity.andOr_signApproxDegree_lower`:
  $\frac{1}{12}\sqrt{mn} \le \widetilde{\deg}_{1/3}(\mathrm{AND}_m \circ \mathrm{OR}_n^m)$ for
  all $m, n \ge 1$.
-/

public section

open scoped NNReal BigOperators
open Finset Cslib Cslib.BitString Cslib.QueryComplexity

namespace CslibFrontier.QueryComplexity


/-- **Approximate degree of the two-level AND–OR tree**:
for all `m, n ≥ 1`, `signApproxDegree (1 / 3) (blockComp (threshold m m) (threshold n 1)) ≥
  (1 / 12) * √(m * n)`.
-/
theorem andOr_signApproxDegree_lower {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (1 / 12 : ℝ) * Real.sqrt ((m : ℝ) * (n : ℝ)) ≤
      (signApproxDegree (1 / 3) (blockComp (threshold m m) (threshold n 1)) : ℝ) := by
  -- Inner dual `φ` for `apdeg_{15/16}(OR_n) > d₁`.
  set D₁ := signApproxDegree (15 / 16) (threshold n 1)
  have hns1 := one_sub_two_mul_mul_blockSensitivity_le
    (ε := Real.toNNReal ((15 / 16 : ℝ) / 2)) (threshold n 1)
  rw [blockSensitivity_threshold_one_right,
    ← signApproxDegree_eq_approxDegree (by norm_num : (0 : ℝ) ≤ 15 / 16),
    Real.coe_toNNReal _ (by positivity)] at hns1
  have hD1_sq : (n : ℝ) ≤ 32 * (D₁ : ℝ) ^ 2 := by
    linarith
  have hD1_pos : 1 ≤ D₁ := by
    by_contra h0
    have hD10 : D₁ = 0 := by omega
    rw [hD10, Nat.cast_zero] at hD1_sq
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set d₁ := D₁ - 1
  have hd1_lt : d₁ < signApproxDegree (15 / 16) (threshold n 1) := by omega
  obtain ⟨φ, hφ_phd, hφ_norm, hφ_corr⟩ :=
    (lt_signApproxDegree_iff (by norm_num : (0 : ℝ) ≤ 15 / 16) (threshold n 1)).mp hd1_lt
  -- Outer dual `ψ` for `apdeg_{1/2}(AND_m) > d₂`.
  set D₂ := signApproxDegree (1 / 2) (threshold m m)
  have hns2 := one_sub_two_mul_mul_blockSensitivity_le
    (ε := Real.toNNReal ((1 / 2 : ℝ) / 2)) (threshold m 1)
  rw [blockSensitivity_threshold_one_right,
    ← signApproxDegree_eq_approxDegree (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← signApproxDegree_and_eq_or (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Real.coe_toNNReal _ (by positivity)] at hns2
  have hD2_sq : (m : ℝ) ≤ 4 * (D₂ : ℝ) ^ 2 := by
    linarith
  have hD2_pos : 1 ≤ D₂ := by
    by_contra h0
    have hD20 : D₂ = 0 := by omega
    rw [hD20, Nat.cast_zero] at hD2_sq
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set d₂ := D₂ - 1
  have hd2_lt : d₂ < signApproxDegree (1 / 2) (threshold m m) := by omega
  obtain ⟨ψ, hψ_phd, hψ_norm, hψ_corr⟩ :=
    (lt_signApproxDegree_iff (by norm_num : (0 : ℝ) ≤ 1 / 2) (threshold m m)).mp hd2_lt
  -- Composed dual `Φ(x) = 2^m * ψ(signBool ∘ φ^m(x)) * ∏_i |φ(x_i)|`.
  let blk : BitString (m * n) → Fin m → BitString n :=
    fun x i j => x (finProdFinEquiv (i, j))
  let blockEquiv : BitString (m * n) ≃ (Fin m → BitString n) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.curry (Fin m) (Fin n) Bool)
  have hblockEquiv_apply : ∀ x, blockEquiv x = blk x := by
    intro x; funext i j; simp [blockEquiv, blk]
  let Φ : BitString (m * n) → ℝ := fun x =>
    (2 : ℝ) ^ m * ψ (fun i => signBool (φ (blk x i))) * ∏ i : Fin m, |φ (blk x i)|
  -- 1. `l1Norm Φ = 1`.
  have hΦ_norm : l1Norm Φ = 1 := by
    rw [l1Norm_eq_sum]
    rw [Fintype.sum_equiv blockEquiv _ (fun y : Fin m → BitString n =>
      |(2 : ℝ) ^ m * ψ (fun i => signBool (φ (y i))) * (∏ i : Fin m, |φ (y i)|)|)
      (fun x => by simp [Φ, hblockEquiv_apply])]
    have hsum_z : ∀ z : BitString m,
        ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
          (2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)| = 1 := by
      intro z
      rw [← Finset.mul_sum]
      have hprod : ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
          ∏ i : Fin m, |φ (y i)| = ∏ i : Fin m, (∑ v with signBool (φ v) = z i, |φ v|) := by
        rw [Finset.sum_filter]
        have hstep : ∀ y : Fin m → BitString n,
            (if (fun i => signBool (φ (y i))) = z then ∏ i : Fin m, |φ (y i)| else 0) =
              ∏ i : Fin m, (if signBool (φ (y i)) = z i then |φ (y i)| else 0) := by
          intro y
          split_ifs with hy
          · exact Finset.prod_congr rfl fun i _ => by simp [congr_fun hy i]
          · have hex : ∃ i, signBool (φ (y i)) ≠ z i := by
              by_contra hall; push Not at hall; exact hy (funext hall)
            obtain ⟨i₀, hi₀⟩ := hex
            exact (Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])).symm
        simp_rw [hstep]
        rw [← Fintype.prod_sum fun (i : Fin m) (v : BitString n) =>
          if signBool (φ v) = z i then |φ v| else 0]
        simp only [← Finset.sum_filter]
      rw [hprod]
      have hhalf : ∀ i : Fin m, ∑ v with signBool (φ v) = z i, |φ v| = 1 / 2 :=
        fun i => sum_abs_eq_half_of_pureHighDegree hφ_phd hφ_norm (z i)
      simp only [hhalf, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring_nf
      rw [← mul_pow]; norm_num
    have hfiber : ∑ y : Fin m → BitString n,
        |(2 : ℝ) ^ m * ψ (fun i => signBool (φ (y i))) * (∏ i : Fin m, |φ (y i)|)| =
        ∑ z : BitString m, ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
          |ψ z| * ((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g :=
        fun y : Fin m → BitString n => fun i => signBool (φ (y i)))
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y hy => ?_
      have hz := (Finset.mem_filter.mp hy).2
      rw [hz, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ m),
        abs_of_nonneg (Finset.prod_nonneg fun i _ => abs_nonneg (φ (y i)))]
      ring
    rw [hfiber]
    have hsimp : ∀ z : BitString m,
        ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
          |ψ z| * ((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) = |ψ z| := by
      intro z
      rw [← Finset.mul_sum, hsum_z z, mul_one]
    simp_rw [hsimp]
    rw [← l1Norm_eq_sum]
    exact hψ_norm
  -- 2. `PureHighDegree Φ (D₂ * D₁ - 1)`.
  have hΦ_phd : PureHighDegree Φ (D₂ * D₁ - 1) := by
    rw [pureHighDegree_iff_fourierCoeff]
    intro U hU
    rw [fourierCoeff_eq_sum]
    suffices h0 : ∑ x : BitString (m * n), Φ x * chi ℝ U x = 0 by rw [h0, zero_div]
    let Ublk : Fin m → Finset (Fin n) := fun i =>
      Finset.univ.filter fun j => finProdFinEquiv (i, j) ∈ U
    have hUcard : ∑ i : Fin m, #(Ublk i) = #U := by
      have hcard_eq : (Finset.univ.filter fun p : Fin m × Fin n => finProdFinEquiv p ∈ U).card =
          #U := by
        refine Finset.card_bij (fun p _ => finProdFinEquiv p)
          (fun p hp => (Finset.mem_filter.mp hp).2)
          (fun _ _ _ _ h => finProdFinEquiv.injective h)
          (fun k hk => ⟨finProdFinEquiv.symm k,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              rw [finProdFinEquiv.apply_symm_apply]; exact hk⟩,
            finProdFinEquiv.apply_symm_apply k⟩)
      rw [← hcard_eq, Finset.card_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.card_filter]
    have hchi_split : ∀ x : BitString (m * n),
        chi ℝ U x = ∏ i : Fin m, chi ℝ (Ublk i) (blk x i) := by
      intro x
      rw [chi_eq_prod_univ]
      rw [Fintype.prod_equiv finProdFinEquiv.symm _
        (fun p : Fin m × Fin n =>
          if finProdFinEquiv p ∈ U then (-1 : ℝ) ^ (x (finProdFinEquiv p)).toNat else 1)
        (fun k => by rw [finProdFinEquiv.apply_symm_apply])]
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [chi_eq_prod_univ]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [Ublk, blk]
    rw [Fintype.sum_equiv blockEquiv _ (fun y : Fin m → BitString n =>
      ((2 : ℝ) ^ m * ψ (fun i => signBool (φ (y i))) * ∏ i : Fin m, |φ (y i)|) *
        ∏ i : Fin m, chi ℝ (Ublk i) (y i))
      (fun x => by simp [Φ, hchi_split, hblockEquiv_apply])]
    have hexpand : ∀ y : Fin m → BitString n,
        ((2 : ℝ) ^ m * ψ (fun i => signBool (φ (y i))) * ∏ i : Fin m, |φ (y i)|) *
          ∏ i : Fin m, chi ℝ (Ublk i) (y i) =
        ∑ S : Finset (Fin m), (2 : ℝ) ^ m * fourierCoeff ψ S *
          ∏ i : Fin m, ((if i ∈ S then φ (y i) else |φ (y i)|) * chi ℝ (Ublk i) (y i)) := by
      intro y
      have hψ_exp := (sum_fourierCoeff_mul_chi ψ (fun i => signBool (φ (y i)))).symm
      rw [hψ_exp, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [chi_eq_prod_signVal]
      have hprod_comb : (∏ i ∈ S, signVal (signBool (φ (y i)))) * (∏ i : Fin m, |φ (y i)|) =
          ∏ i : Fin m, (if i ∈ S then φ (y i) else |φ (y i)|) := by
        conv_lhs =>
          rw [← Finset.univ_inter S,
            ← Finset.prod_ite_mem Finset.univ S (fun i => signVal (signBool (φ (y i))))]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases hi : i ∈ S
        · simp only [hi, ↓reduceIte]; rw [mul_comm, mul_signVal_signBool]
        · simp [hi]
      have hprod_mul : (∏ i : Fin m, (if i ∈ S then φ (y i) else |φ (y i)|)) *
          (∏ i : Fin m, chi ℝ (Ublk i) (y i)) =
          ∏ i : Fin m, ((if i ∈ S then φ (y i) else |φ (y i)|) * chi ℝ (Ublk i) (y i)) := by
        rw [← Finset.prod_mul_distrib]
      calc (2 : ℝ) ^ m * (fourierCoeff ψ S * ∏ i ∈ S, signVal (signBool (φ (y i)))) *
            (∏ i : Fin m, |φ (y i)|) * (∏ i : Fin m, chi ℝ (Ublk i) (y i))
          = (2 : ℝ) ^ m * fourierCoeff ψ S *
            ((∏ i ∈ S, signVal (signBool (φ (y i)))) * (∏ i : Fin m, |φ (y i)|)) *
            (∏ i : Fin m, chi ℝ (Ublk i) (y i)) := by ring
        _ = (2 : ℝ) ^ m * fourierCoeff ψ S *
            ((∏ i : Fin m, (if i ∈ S then φ (y i) else |φ (y i)|)) *
              (∏ i : Fin m, chi ℝ (Ublk i) (y i))) := by rw [hprod_comb]; ring
        _ = _ := by rw [hprod_mul]
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [← Finset.mul_sum]
    by_cases hS : #S ≤ d₂
    · have h0 := (pureHighDegree_iff_fourierCoeff ψ d₂).mp hψ_phd S hS
      simp [h0]
    · have hSge : D₂ ≤ #S := by omega
      have hexists : ∃ i ∈ S, #(Ublk i) ≤ d₁ := by
        by_contra hall
        push Not at hall
        have hsum_ge : D₂ * D₁ ≤ ∑ i ∈ S, #(Ublk i) := by
          calc D₂ * D₁ ≤ #S * D₁ := Nat.mul_le_mul_right D₁ hSge
            _ = ∑ _i ∈ S, D₁ := by simp
            _ ≤ ∑ i ∈ S, #(Ublk i) := Finset.sum_le_sum fun i hi => by have := hall i hi; omega
        have hle_tot : ∑ i ∈ S, #(Ublk i) ≤ #U := by
          rw [← hUcard]
          exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
        have h1 : 1 ≤ D₂ * D₁ := Nat.mul_pos hD2_pos hD1_pos
        omega
      obtain ⟨i₀, hi₀S, hi₀U⟩ := hexists
      have hfactor0 : ∑ v : BitString n,
          (if i₀ ∈ S then φ v else |φ v|) * chi ℝ (Ublk i₀) v = 0 := by
        simp only [hi₀S, ↓reduceIte]
        have h0 := (pureHighDegree_iff_fourierCoeff φ d₁).mp hφ_phd (Ublk i₀) hi₀U
        rw [fourierCoeff_eq_sum] at h0
        exact (div_eq_zero_iff.mp h0).resolve_right (by positivity)
      have hprod_sum : ∑ y : Fin m → BitString n,
          ∏ i : Fin m, ((if i ∈ S then φ (y i) else |φ (y i)|) * chi ℝ (Ublk i) (y i)) =
          ∏ i : Fin m, ∑ v : BitString n,
            ((if i ∈ S then φ v else |φ v|) * chi ℝ (Ublk i) v) :=
        (Fintype.prod_sum fun (i : Fin m) (v : BitString n) =>
          (if i ∈ S then φ v else |φ v|) * chi ℝ (Ublk i) v).symm
      have hzero_prod : ∏ i : Fin m, ∑ v : BitString n,
          ((if i ∈ S then φ v else |φ v|) * chi ℝ (Ublk i) v) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) hfactor0
      rw [hprod_sum, hzero_prod, mul_zero]
  -- 3. Correlation `⟨Φ, AND_m ∘ OR_n^m⟩ > 1 / 3`.
  have hΦ_corr :
      (1 / 3 : ℝ) <
        innerSum Φ (fun x => signVal (blockComp (threshold m m) (threshold n 1) x)) := by
    have hφ_err_pos : ∑ v : BitString n with signBool (φ v) = false ∧ threshold n 1 v = true,
        |φ v| < 1 / 32 := by
      have hx0_eq : ∀ v : BitString n, threshold n 1 v = false ↔ v = fun _ => false := by
        intro v
        rw [threshold_apply, decide_eq_false_iff_not, not_le, Nat.lt_one_iff]
        constructor
        · intro hw
          funext j
          by_contra hj
          have hmem : j ∈ Finset.univ.filter (fun i => v i = true) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.eq_true_of_not_eq_false hj⟩
          have : 1 ≤ weight v := Finset.card_pos.mpr ⟨j, hmem⟩
          omega
        · rintro rfl; simp [weight]
      have hcorr_split : innerSum φ (fun v => signVal (threshold n 1 v)) =
          2 * φ (fun _ => false) := by
        have hsum0 : ∑ v : BitString n, φ v = 0 := pureHighDegree_sum_eq_zero hφ_phd
        have h1 : innerSum φ (fun v => signVal (threshold n 1 v)) + ∑ v, φ v =
            ∑ v, φ v * (signVal (threshold n 1 v) + 1) := by
          simp only [innerSum_eq_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun v _ => by ring
        rw [hsum0, add_zero] at h1
        rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : Fin n => false))]
        have hrest0 : ∑ v ∈ Finset.univ.erase (fun _ : Fin n => false),
            φ v * (signVal (threshold n 1 v) + 1) = 0 := by
          refine Finset.sum_eq_zero fun v hv => ?_
          have hne := Finset.ne_of_mem_erase hv
          have ht : threshold n 1 v = true := by
            cases htv : threshold n 1 v
            · exact absurd ((hx0_eq v).mp htv) hne
            · rfl
          rw [ht, signVal_true]; ring
        have ht0 : threshold n 1 (fun _ => false) = false := (hx0_eq _).mpr rfl
        rw [hrest0, add_zero, ht0, signVal_false]; ring
      have hφ0_gt : (15 / 32 : ℝ) < φ (fun _ => false) := by linarith
      have hφ0_sb : signBool (φ (fun _ => false)) = false :=
        signBool_of_nonneg (by linarith)
      have hhalf := sum_abs_eq_half_of_pureHighDegree hφ_phd hφ_norm false
      have hmem0 : (fun _ : Fin n => false) ∈
          Finset.univ.filter (fun v => signBool (φ v) = false) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ0_sb⟩
      rw [← Finset.add_sum_erase _ _ hmem0, abs_of_pos (by linarith)] at hhalf
      have hsub : (Finset.univ.filter fun v => signBool (φ v) = false ∧ threshold n 1 v = true) ⊆
          (Finset.univ.filter fun v => signBool (φ v) = false).erase (fun _ => false) := by
        intro v hv
        obtain ⟨hsb, ht⟩ := (Finset.mem_filter.mp hv).2
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsb⟩⟩
        intro heq; subst heq; rw [(hx0_eq _).mpr rfl] at ht; exact Bool.false_ne_true ht
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => abs_nonneg (φ v))
      linarith
    have hφ_err_neg : ∀ v : BitString n, signBool (φ v) = true → threshold n 1 v = true := by
      intro v hsb
      have hneg : φ v < 0 := by rw [signBool_eq_decide, decide_eq_true_eq] at hsb; exact hsb
      cases htv : threshold n 1 v
      · exfalso
        have hv0 : v = fun _ => false := by
          rw [threshold_apply, decide_eq_false_iff_not, not_le, Nat.lt_one_iff] at htv
          funext j
          by_contra hj
          have : 1 ≤ weight v := Finset.card_pos.mpr
            ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.eq_true_of_not_eq_false hj⟩⟩
          omega
        subst hv0
        have hsum0 : ∑ w : BitString n, φ w = 0 := pureHighDegree_sum_eq_zero hφ_phd
        have h1 : innerSum φ (fun w => signVal (threshold n 1 w)) + ∑ w, φ w =
            ∑ w, φ w * (signVal (threshold n 1 w) + 1) := by
          simp only [innerSum_eq_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => by ring
        rw [hsum0, add_zero] at h1
        rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : Fin n => false))] at hφ_corr
        have hrest0 : ∑ w ∈ Finset.univ.erase (fun _ : Fin n => false),
            φ w * (signVal (threshold n 1 w) + 1) = 0 := by
          refine Finset.sum_eq_zero fun w hw => ?_
          have hne := Finset.ne_of_mem_erase hw
          have ht : threshold n 1 w = true := by
            by_contra hnot
            have hwf := Bool.eq_false_iff.mpr hnot
            rw [threshold_apply, decide_eq_false_iff_not, not_le, Nat.lt_one_iff] at hwf
            apply hne; funext j; by_contra hj
            have : 1 ≤ weight w := Finset.card_pos.mpr
              ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.eq_true_of_not_eq_false hj⟩⟩
            omega
          rw [ht, signVal_true]; ring
        rw [hrest0, add_zero, htv, signVal_false] at hφ_corr
        linarith
      · rfl
    -- Now compute `innerSum Φ F` fiberwise over `z = signBool ∘ φ^m(y)`.
    rw [innerSum_eq_sum]
    rw [Fintype.sum_equiv blockEquiv _ (fun y : Fin m → BitString n =>
      ((2 : ℝ) ^ m * ψ (fun i => signBool (φ (y i))) * ∏ i : Fin m, |φ (y i)|) *
        signVal (threshold m m (fun i => threshold n 1 (y i))))
      (fun x => by simp [Φ, blockComp_apply, hblockEquiv_apply, blk])]
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun y : Fin m → BitString n => fun i => signBool (φ (y i)))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have hfiber_bound : ∀ z : BitString m,
        ψ z * signVal (threshold m m z) - (1 / 8 : ℝ) * |ψ z| ≤
          ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
            ((2 : ℝ) ^ m * ψ (fun i => signBool (φ (y i))) * ∏ i : Fin m, |φ (y i)|) *
              signVal (threshold m m (fun i => threshold n 1 (y i))) := by
      intro z
      have hsum_z : ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
          (2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)| = 1 := by
        rw [← Finset.mul_sum]
        have hprod : ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
            ∏ i : Fin m, |φ (y i)| = ∏ i : Fin m, (∑ v with signBool (φ v) = z i, |φ v|) := by
          rw [Finset.sum_filter]
          have hstep : ∀ y : Fin m → BitString n,
              (if (fun i => signBool (φ (y i))) = z then ∏ i : Fin m, |φ (y i)| else 0) =
                ∏ i : Fin m, (if signBool (φ (y i)) = z i then |φ (y i)| else 0) := by
            intro y
            split_ifs with hy
            · exact Finset.prod_congr rfl fun i _ => by simp [congr_fun hy i]
            · have hex : ∃ i, signBool (φ (y i)) ≠ z i := by
                by_contra hall; push Not at hall; exact hy (funext hall)
              obtain ⟨i₀, hi₀⟩ := hex
              exact (Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])).symm
          simp_rw [hstep]
          rw [← Fintype.prod_sum fun (i : Fin m) (v : BitString n) =>
            if signBool (φ v) = z i then |φ v| else 0]
          simp only [← Finset.sum_filter]
        rw [hprod]
        simp_rw [sum_abs_eq_half_of_pureHighDegree hφ_phd hφ_norm]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring_nf; rw [← mul_pow]; norm_num
      have hrewrite : ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
          ((2 : ℝ) ^ m * ψ (fun i => signBool (φ (y i))) * ∏ i : Fin m, |φ (y i)|) *
            signVal (threshold m m (fun i => threshold n 1 (y i))) =
          ψ z * signVal (threshold m m z) +
            ψ z * ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
              ((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) *
                (signVal (threshold m m (fun i => threshold n 1 (y i))) -
                  signVal (threshold m m z)) := by
        rw [Finset.mul_sum]
        have hterm1 : ψ z * signVal (threshold m m z) =
            ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
              ((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) * (ψ z * signVal (threshold m m z)) := by
          rw [← Finset.sum_mul, hsum_z, one_mul]
        rw [hterm1, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [(Finset.mem_filter.mp hy).2]; ring
      rw [hrewrite]
      -- Bound the error term by `(1 / 8) * |ψ z|`.
      by_cases hz : threshold m m z = true
      · -- `z = allTrue`: every `y` in the fiber has `threshold n 1 (y i) = true`, so error is `0`!
        have hzero : ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
            ((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) *
              (signVal (threshold m m (fun i => threshold n 1 (y i))) -
                signVal (threshold m m z)) = 0 := by
          refine Finset.sum_eq_zero fun y hy => ?_
          have hyz := (Finset.mem_filter.mp hy).2
          have hall_true : ∀ i : Fin m, z i = true := by
            rw [threshold_apply, decide_eq_true_eq] at hz
            have hcard : #{i : Fin m | z i = true} = m :=
              le_antisymm ((Finset.card_le_univ _).trans_eq (Fintype.card_fin m)) hz
            have hfull := Finset.eq_univ_of_card _ (hcard.trans (Fintype.card_fin m).symm)
            intro i; simpa using Finset.ext_iff.mp hfull i
          have hy_true : (fun i => threshold n 1 (y i)) = z := by
            funext i
            rw [hall_true i]
            exact hφ_err_neg (y i) (by rw [← hall_true i, ← congr_fun hyz i])
          rw [hy_true, sub_self, mul_zero]
        rw [hzero, mul_zero, add_zero]
        linarith [abs_nonneg (ψ z)]
      · -- `z ≠ allTrue`: pick `i₀` with `z i₀ = false`.
        have hzf : threshold m m z = false := Bool.eq_false_iff.mpr hz
        have hex : ∃ i₀ : Fin m, z i₀ = false := by
          by_contra hall
          push Not at hall
          have hallt : ∀ i : Fin m, z i = true := fun i => Bool.eq_true_of_not_eq_false (hall i)
          have hwt : weight z = m := by
            have : (Finset.univ.filter fun i : Fin m => z i = true) = Finset.univ := by
              ext i; simp [hallt]
            rw [weight, this, Finset.card_univ, Fintype.card_fin]
          rw [threshold_apply, hwt] at hzf; simp at hzf
        obtain ⟨i₀, hi₀⟩ := hex
        have herr_le : |∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
            ((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) *
              (signVal (threshold m m (fun i => threshold n 1 (y i))) -
                signVal (threshold m m z))| ≤ 1 / 8 := by
          calc |∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
                ((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) *
                  (signVal (threshold m m (fun i => threshold n 1 (y i))) -
                    signVal (threshold m m z))|
              ≤ ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
                  |((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) *
                    (signVal (threshold m m (fun i => threshold n 1 (y i))) -
                      signVal (threshold m m z))| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z ∧
                  threshold n 1 (y i₀) = true,
                  2 * ((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) := by
                rw [Finset.sum_filter, Finset.sum_filter]
                refine Finset.sum_le_sum fun y _ => ?_
                by_cases hy : (fun i => signBool (φ (y i))) = z
                · simp only [hy, true_and, ↓reduceIte]
                  rw [abs_mul, abs_of_nonneg (mul_nonneg (by positivity)
                    (Finset.prod_nonneg fun i _ => abs_nonneg (φ (y i))))]
                  by_cases hy0 : threshold n 1 (y i₀) = true
                  · simp only [hy0, ↓reduceIte]
                    have habs : |signVal (threshold m m (fun i => threshold n 1 (y i))) -
                        signVal (threshold m m z)| ≤ 2 := by
                      cases threshold m m (fun i => threshold n 1 (y i)) <;>
                        cases threshold m m z <;> norm_num
                    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ m)
                      (Finset.prod_nonneg (s := Finset.univ) fun i _ => abs_nonneg (φ (y i)))]
                  · have hyf : threshold n 1 (y i₀) = false := Bool.eq_false_iff.mpr hy0
                    have hmf : threshold m m (fun i => threshold n 1 (y i)) = false := by
                      rw [threshold_apply, decide_eq_false_iff_not, not_le]
                      have hlt : weight (fun i => threshold n 1 (y i)) < m := by
                        have hss : (Finset.univ.filter fun i : Fin m =>
                            threshold n 1 (y i) = true) ⊂ Finset.univ :=
                          Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun heq => by
                            have := Finset.ext_iff.mp heq i₀; simp [hyf] at this⟩
                        simpa [weight, Fintype.card_fin] using Finset.card_lt_card hss
                      exact hlt
                    rw [hmf, hzf, sub_self, abs_zero, mul_zero]
                    simp [hy0]
                · simp [hy]
            _ = 2 * (2 : ℝ) ^ m * (∑ v with signBool (φ v) = false ∧
              threshold n 1 v = true, |φ v|) *
                  ∏ i ∈ Finset.univ.erase i₀, (∑ v with signBool (φ v) = z i, |φ v|) := by
                have hprod_split : ∑ y : Fin m → BitString n with
                    (fun i => signBool (φ (y i))) = z ∧ threshold n 1 (y i₀) = true,
                    ∏ i : Fin m, |φ (y i)| =
                    (∑ v with signBool (φ v) = false ∧ threshold n 1 v = true, |φ v|) *
                    ∏ i ∈ Finset.univ.erase i₀, (∑ v with signBool (φ v) = z i, |φ v|) := by
                  let f : Fin m → BitString n → ℝ := fun i v =>
                    if i = i₀ then
                      (if signBool (φ v) = false ∧ threshold n 1 v = true then |φ v| else 0)
                    else
                      (if signBool (φ v) = z i then |φ v| else 0)
                  have hprod_eq : (∑ v with signBool (φ v) = false ∧
                    threshold n 1 v = true, |φ v|) *
                      ∏ i ∈ Finset.univ.erase i₀, (∑ v with signBool (φ v) = z i, |φ v|) =
                      ∏ i : Fin m, ∑ v : BitString n, f i v := by
                    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
                    have hf0 : ∑ v : BitString n, f i₀ v =
                        ∑ v with signBool (φ v) = false ∧ threshold n 1 v = true, |φ v| := by
                      simp [f, Finset.sum_filter]
                    rw [hf0]
                    congr 1
                    refine Finset.prod_congr rfl fun i hi => ?_
                    simp [f, Finset.ne_of_mem_erase hi, Finset.sum_filter]
                  rw [hprod_eq, Fintype.prod_sum, Finset.sum_filter]
                  refine Finset.sum_congr rfl fun y _ => ?_
                  split_ifs with hy
                  · refine Finset.prod_congr rfl fun i _ => ?_
                    by_cases hi : i = i₀
                    · subst hi; simp [f, (congr_fun hy.1 i).trans hi₀, hy.2]
                    · simp [f, hi, congr_fun hy.1 i]
                  · symm
                    by_cases hy0 : threshold n 1 (y i₀) = true
                    · have hex : ∃ i, signBool (φ (y i)) ≠ z i := by
                        by_contra hall; push Not at hall; exact hy ⟨funext hall, hy0⟩
                      obtain ⟨i, hi⟩ := hex
                      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
                      by_cases hii : i = i₀
                      · subst hii; simp [f, hi₀ ▸ hi]
                      · simp [f, hii, hi]
                    · refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
                      simp [f, hy0]
                simp_rw [show ∀ y : Fin m → BitString n,
                  2 * ((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) =
                    (2 * (2 : ℝ) ^ m) * ∏ i : Fin m, |φ (y i)| by intro y; ring]
                rw [← Finset.mul_sum, hprod_split]; ring
            _ ≤ 1 / 8 := by
                simp_rw [sum_abs_eq_half_of_pureHighDegree hφ_phd hφ_norm]
                rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
                  Finset.card_univ, Fintype.card_fin]
                have h2pow : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (m - 1) = 2 := by
                  have hm1 : m = (m - 1) + 1 := by omega
                  calc (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (m - 1)
                      = (2 : ℝ) ^ ((m - 1) + 1) * (1 / 2 : ℝ) ^ (m - 1) := by rw [← hm1]
                    _ = 2 * ((2 : ℝ) * (1 / 2 : ℝ)) ^ (m - 1) := by rw [pow_succ, mul_pow]; ring
                    _ = 2 := by norm_num
                have hcalc : 2 * (2 : ℝ) ^ m *
                    (∑ v with signBool (φ v) = false ∧ threshold n 1 v = true, |φ v|) *
                    (1 / 2 : ℝ) ^ (m - 1) =
                    4 * (∑ v with signBool (φ v) = false ∧ threshold n 1 v = true, |φ v|) := by
                  calc _ = 2 * ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (m - 1)) *
                        (∑ v with signBool (φ v) = false ∧ threshold n 1 v = true, |φ v|) := by ring
                    _ = _ := by rw [h2pow]; ring
                rw [hcalc]
                linarith
        have hterm_ge : -((1 / 8 : ℝ) * |ψ z|) ≤
            ψ z * ∑ y : Fin m → BitString n with (fun i => signBool (φ (y i))) = z,
              ((2 : ℝ) ^ m * ∏ i : Fin m, |φ (y i)|) *
                (signVal (threshold m m (fun i => threshold n 1 (y i))) -
                  signVal (threshold m m z)) := by
          refine neg_le_of_abs_le ?_
          rw [abs_mul, mul_comm (1 / 8 : ℝ)]
          exact mul_le_mul_of_nonneg_left herr_le (abs_nonneg (ψ z))
        linarith
    calc (1 / 3 : ℝ) < (1 / 2 : ℝ) - (1 / 8 : ℝ) * 1 := by norm_num
      _ < innerSum ψ (fun z => signVal (threshold m m z)) - (1 / 8 : ℝ) * l1Norm ψ := by
          rw [hψ_norm]; linarith
      _ = ∑ z : BitString m, (ψ z * signVal (threshold m m z) - (1 / 8 : ℝ) * |ψ z|) := by
          simp only [innerSum_eq_sum, l1Norm_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum fun z _ => hfiber_bound z
  have hlt : D₂ * D₁ - 1 < signApproxDegree (1 / 3) (blockComp (threshold m m) (threshold n 1)) :=
    (lt_signApproxDegree_iff (by norm_num) _).mpr ⟨Φ, hΦ_phd, hΦ_norm, hΦ_corr⟩
  have hge_nat : D₂ * D₁ ≤
    signApproxDegree (1 / 3) (blockComp (threshold m m) (threshold n 1)) := by
    have : 1 ≤ D₂ * D₁ := Nat.mul_pos hD2_pos hD1_pos
    omega
  have hge_r : (D₂ : ℝ) * (D₁ : ℝ) ≤
      (signApproxDegree (1 / 3) (blockComp (threshold m m) (threshold n 1)) : ℝ) := by
    exact_mod_cast hge_nat
  have hsq : ((1 / 12 : ℝ) * Real.sqrt ((m : ℝ) * (n : ℝ))) ^ 2 ≤ ((D₂ : ℝ) * (D₁ : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), mul_pow]
    have : (m : ℝ) * (n : ℝ) ≤ 128 * ((D₂ : ℝ) ^ 2 * (D₁ : ℝ) ^ 2) := by
      have := mul_le_mul hD2_sq hD1_sq (Nat.cast_nonneg n) (by positivity)
      linarith
    nlinarith
  have hsqrt_le : (1 / 12 : ℝ) * Real.sqrt ((m : ℝ) * (n : ℝ)) ≤ (D₂ : ℝ) * (D₁ : ℝ) := by
    nlinarith [Real.sqrt_nonneg ((m : ℝ) * (n : ℝ)),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) D₂) (Nat.cast_nonneg (α := ℝ) D₁)]
  linarith

end CslibFrontier.QueryComplexity
