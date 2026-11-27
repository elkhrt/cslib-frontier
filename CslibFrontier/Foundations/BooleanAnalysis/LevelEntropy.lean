/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.EdgeIsoperimetry
public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Minimum distance of low-sensitivity functions and degree-weight Shannon entropy

Two structural inequalities for Boolean functions on the Hamming cube `ι → Bool`, derived from the
edge-isoperimetric inequality and Fourier degree weights:

* **Minimum Hamming distance under bounded sensitivity**
  (`Cslib.BitString.two_pow_sub_two_mul_le_hammingDist`): if `f₁` and `f₂` are distinct Boolean
  functions on `ι → Bool` and at every point `x` each flips on at most `s` coordinate neighbours,
  then `hammingDist f₁ f₂ ≥ 2 ^ (|ι| - 2 s)`. On the disagreement set `A = {x | f₁ x ≠ f₂ x}`,
  every vertex has at most `2 s` edges leaving `A`, so at least `|ι| - 2 s` edges stay inside `A`;
  combining with `Cslib.BitString.sum_card_filter_update_mem_le` yields `|ι| - 2 s ≤ log₂ |A|`.
* **Shannon entropy vs. square-root sum**
  (`Cslib.BitString.sum_mul_logb_inv_le_two_mul_logb_sum_sqrt`): for nonnegative weights
  `(p_i)_{i ∈ S}` with total mass `P = ∑_{i ∈ S} p_i`,
  `∑_{i ∈ S} p_i log₂ (1 / p_i) ≤ 2 P log₂ (∑_{i ∈ S} √p_i) + 2 P log₂ (1 / P)`.
* **Total influence from degree weights** (`Cslib.BitString.sum_mul_levelWeight_eq_totalInfluence`):
  `∑_{k = 0}^{|ι|} k W^k[f] = I[f]`.
* **Degree-weight Shannon entropy bound**
  (`Cslib.BitString.sum_levelWeight_mul_logb_inv_le_three_mul_totalInfluence`): for every Boolean
  function `f : (ι → Bool) → Bool` read as signs `F x = signVal (f x)`, the Shannon entropy of its
  degree-weight distribution `(W^k[F])_{k = 0}^{|ι|}` is at most `3 I[F]`. Splitting off the
  degree-zero weight `W^0[F] = 1 - q` decomposes the sum into binary entropy `H₂(q)` (at most
  `2 I[F]` by Poincaré and edge isoperimetry) plus a conditional positive-degree entropy bounded by
  `I[F]` via comparison with the geometric weights `2^{-k}`.

## Main results

* `Cslib.BitString.two_pow_sub_two_mul_le_hammingDist`: minimum Hamming distance between distinct
  low-sensitivity Boolean functions.
* `Cslib.BitString.sum_mul_logb_inv_le_two_mul_logb_sum_sqrt`: entropy upper bound in terms of
  `∑ √p_i`.
* `Cslib.BitString.sum_mul_levelWeight_eq_totalInfluence`: `∑ k W^k[f] = totalInfluence f`.
* `Cslib.BitString.sum_levelWeight_mul_logb_inv_le_three_mul_totalInfluence`: degree-weight entropy
  is at most three times total influence.
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

private theorem log_le_sub_one_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1 :=
  (Real.log_le_iff_le_exp hx).mpr (by linarith [Real.add_one_le_exp (x - 1)])

private theorem two_thirds_lt_log_two : (2 : ℝ) / 3 < Real.log 2 := by
  have hexp_lb : (1 / 2 : ℝ) < Real.exp (-2 / 3) := by
    have h1 : (23 / 24 : ℝ) ≤ Real.exp (-1 / 24) := by
      linarith [Real.add_one_le_exp (-1 / 24)]
    calc
      (1 / 2 : ℝ) < (23 / 24 : ℝ) ^ 16 := by norm_num
      _ ≤ (Real.exp (-1 / 24)) ^ 16 := pow_le_pow_left₀ (by norm_num) h1 16
      _ = Real.exp (-2 / 3) := by rw [← Real.exp_nat_mul]; norm_num
  have hexp_ub : Real.exp (2 / 3) < 2 := by
    have hinv : (Real.exp (-2 / 3))⁻¹ < (1 / 2 : ℝ)⁻¹ :=
      inv_strictAnti₀ (by norm_num) hexp_lb
    rw [← Real.exp_neg, neg_div, neg_neg] at hinv
    linarith
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp_ub

/-- **Minimum distance under bounded pointwise sensitivity**: if `f₁ ≠ f₂` are distinct Boolean
functions on `ι → Bool` such that at every input `x` each function changes value along at most `s`
coordinates, then `(2 : ℝ) ^ (|ι| - 2 s) ≤ hammingDist f₁ f₂`. -/
theorem two_pow_sub_two_mul_le_hammingDist {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} {f₁ f₂ : (ι → Bool) → Bool}
    (hf₁ : ∀ x, #{i : ι | f₁ (update x i (!x i)) ≠ f₁ x} ≤ s)
    (hf₂ : ∀ x, #{i : ι | f₂ (update x i (!x i)) ≠ f₂ x} ≤ s)
    (hne : f₁ ≠ f₂) :
    (2 : ℝ) ^ ((Fintype.card ι : ℝ) - 2 * (s : ℝ)) ≤ (hammingDist f₁ f₂ : ℝ) := by
  let A : Finset (ι → Bool) := univ.filter fun x => f₁ x ≠ f₂ x
  have hA_card : #A = hammingDist f₁ f₂ := rfl
  have hdist_pos : 0 < hammingDist f₁ f₂ := hammingDist_pos.mpr hne
  have hA_pos : (0 : ℝ) < #A := by rw [hA_card]; exact_mod_cast hdist_pos
  rw [← hA_card]
  set n := Fintype.card ι
  by_cases hsn : n ≤ 2 * s
  · have hexp : (n : ℝ) - 2 * (s : ℝ) ≤ 0 := by
      have : (n : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast hsn
      linarith
    calc
      (2 : ℝ) ^ ((n : ℝ) - 2 * (s : ℝ)) ≤ (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two hexp
      _ = 1 := Real.rpow_zero 2
      _ ≤ (#A : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hdist_pos
  · push Not at hsn
    have hdeg_in : ∀ x ∈ A,
        ((n - 2 * s : ℕ) : ℝ) ≤ #{i : ι | update x i (!x i) ∈ A} := by
      intro x hx
      have hx_ne : f₁ x ≠ f₂ x := (mem_filter.mp hx).2
      let outSet : Finset ι := univ.filter fun i => update x i (!x i) ∉ A
      let S₁ : Finset ι := univ.filter fun i => f₁ (update x i (!x i)) ≠ f₁ x
      let S₂ : Finset ι := univ.filter fun i => f₂ (update x i (!x i)) ≠ f₂ x
      have hout_sub : outSet ⊆ S₁ ∪ S₂ := by
        intro i hi
        have hnotA : update x i (!x i) ∉ A := (mem_filter.mp hi).2
        have heq_nb : f₁ (update x i (!x i)) = f₂ (update x i (!x i)) := by
          by_contra hne_nb
          exact hnotA (mem_filter.mpr ⟨mem_univ _, hne_nb⟩)
        rw [mem_union]
        by_contra hboth
        push Not at hboth
        simp only [S₁, S₂, mem_filter, mem_univ, true_and, not_not] at hboth
        exact hx_ne (hboth.1.symm.trans (heq_nb.trans hboth.2))
      have hout_le : #outSet ≤ 2 * s := by
        calc
          #outSet ≤ #(S₁ ∪ S₂) := card_le_card hout_sub
          _ ≤ #S₁ + #S₂ := card_union_le _ _
          _ ≤ s + s := Nat.add_le_add (hf₁ x) (hf₂ x)
          _ = 2 * s := by omega
      have hpart := card_filter_add_card_filter_not (s := (univ : Finset ι))
        fun i : ι => update x i (!x i) ∈ A
      rw [card_univ] at hpart
      have hin_ge : n - 2 * s ≤ #{i : ι | update x i (!x i) ∈ A} := by
        change #{i : ι | update x i (!x i) ∈ A} + #outSet = n at hpart
        omega
      exact_mod_cast hin_ge
    have hsum_lb : (#A : ℝ) * ((n : ℝ) - 2 * (s : ℝ)) ≤
        ∑ x ∈ A, (#{i : ι | update x i (!x i) ∈ A} : ℝ) := by
      have hcast_sub : ((n - 2 * s : ℕ) : ℝ) = (n : ℝ) - 2 * (s : ℝ) := by
        rw [Nat.cast_sub hsn.le]; push_cast; ring
      calc
        (#A : ℝ) * ((n : ℝ) - 2 * (s : ℝ)) = ∑ _x ∈ A, ((n - 2 * s : ℕ) : ℝ) := by
          rw [sum_const, nsmul_eq_mul, hcast_sub]
        _ ≤ ∑ x ∈ A, (#{i : ι | update x i (!x i) ∈ A} : ℝ) := sum_le_sum hdeg_in
    have hlog_ge : (n : ℝ) - 2 * (s : ℝ) ≤ Real.logb 2 (#A : ℝ) :=
      le_of_mul_le_mul_left (hsum_lb.trans (sum_card_filter_update_mem_le A)) hA_pos
    calc
      (2 : ℝ) ^ ((n : ℝ) - 2 * (s : ℝ)) ≤ (2 : ℝ) ^ Real.logb 2 (#A : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two hlog_ge
      _ = (#A : ℝ) := Real.rpow_logb two_pos (by norm_num) hA_pos

/-- **Entropy vs. square-root sum**: for nonnegative real numbers `(p i)_{i ∈ S}` with total sum
`P = ∑ i ∈ S, p i`,
`∑ i ∈ S, p i * log₂ (1 / p i) ≤ 2 * P * log₂ (∑ i ∈ S, √(p i)) + 2 * P * log₂ (1 / P)`. -/
theorem sum_mul_logb_inv_le_two_mul_logb_sum_sqrt {α : Type*} (S : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i) :
    (∑ i ∈ S, p i * Real.logb 2 (1 / p i)) ≤
      2 * (∑ i ∈ S, p i) * Real.logb 2 (∑ i ∈ S, Real.sqrt (p i)) +
        2 * (∑ i ∈ S, p i) * Real.logb 2 (1 / ∑ i ∈ S, p i) := by
  set P := ∑ i ∈ S, p i
  set M := ∑ i ∈ S, Real.sqrt (p i)
  have hP_nonneg : 0 ≤ P := sum_nonneg hp
  rcases hP_nonneg.eq_or_lt with hP0 | hP_pos
  · have hall0 : ∀ i ∈ S, p i = 0 := (sum_eq_zero_iff_of_nonneg hp).mp hP0.symm
    have hlhs : (∑ i ∈ S, p i * Real.logb 2 (1 / p i)) = 0 :=
      sum_eq_zero fun i hi => by simp [hall0 i hi]
    rw [hlhs, ← hP0]
    simp
  · obtain ⟨i₀, hi₀S, hi₀_pos⟩ : ∃ i ∈ S, 0 < p i := by
      by_contra hall
      push Not at hall
      have h0 : P = 0 := sum_eq_zero fun i hi => le_antisymm (hall i hi) (hp i hi)
      linarith
    have hM_pos : 0 < M :=
      lt_of_lt_of_le (Real.sqrt_pos.mpr hi₀_pos)
        (single_le_sum (fun i _ => Real.sqrt_nonneg (p i)) hi₀S)
    have hterm : ∀ i ∈ S,
        p i * Real.log (1 / p i) - 2 * p i * Real.log M - 2 * p i * Real.log (1 / P) ≤
          2 * (Real.sqrt (p i) / M * P - p i) := by
      intro i hi
      rcases (hp i hi).eq_or_lt with hpi0 | hpi_pos
      · simp [← hpi0]
      · have hsqrt_pos : 0 < Real.sqrt (p i) := Real.sqrt_pos.mpr hpi_pos
        have hgibbs := log_le_sub_one_pos (show 0 < Real.sqrt (p i) * P / (M * p i) by positivity)
        have hmul := mul_le_mul_of_nonneg_left hgibbs (by positivity : 0 ≤ 2 * p i)
        have hlog_id :
            2 * p i * Real.log (Real.sqrt (p i) * P / (M * p i)) =
              p i * Real.log (1 / p i) - 2 * p i * Real.log M - 2 * p i * Real.log (1 / P) := by
          have hsq : Real.sqrt (p i) * Real.sqrt (p i) = p i := Real.mul_self_sqrt hpi_pos.le
          have harg : Real.sqrt (p i) * P / (M * p i) = P / (M * Real.sqrt (p i)) := by
            rw [div_eq_div_iff (by positivity) (by positivity)]
            calc
              Real.sqrt (p i) * P * (M * Real.sqrt (p i)) =
                  P * M * (Real.sqrt (p i) * Real.sqrt (p i)) := by ring
              _ = P * (M * p i) := by rw [hsq]; ring
          rw [harg, Real.log_div hP_pos.ne' (by positivity),
            Real.log_mul hM_pos.ne' hsqrt_pos.ne', Real.log_sqrt hpi_pos.le,
            one_div, Real.log_inv, one_div, Real.log_inv]
          ring
        have hrhs_id :
            2 * p i * (Real.sqrt (p i) * P / (M * p i) - 1) =
              2 * (Real.sqrt (p i) / M * P - p i) := by
          field_simp
        linarith
    have hsum_le := sum_le_sum hterm
    simp only [sum_sub_distrib, ← sum_mul] at hsum_le
    have h2P : ∑ i ∈ S, 2 * p i = 2 * P := (mul_sum S p 2).symm
    have hrhs_zero : (∑ i ∈ S, 2 * (Real.sqrt (p i) / M * P - p i)) = 0 := by
      simp only [← mul_sum, sum_sub_distrib, div_mul_eq_mul_div, ← sum_div, ← sum_mul]
      change 2 * (M * P / M - P) = 0
      rw [mul_div_cancel_left₀ P hM_pos.ne', sub_self, mul_zero]
    rw [h2P, hrhs_zero] at hsum_le
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hdiv := div_le_div_of_nonneg_right hsum_le hlog2_pos.le
    simp only [zero_div, sub_div] at hdiv
    simp only [Real.logb, ← mul_div_assoc, ← sum_div]
    linarith

/-- **Total influence by degree**:
`∑ k ∈ range (|ι| + 1), k * levelWeight k f = totalInfluence f`. -/
theorem sum_mul_levelWeight_eq_totalInfluence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) :
    ∑ k ∈ range (Fintype.card ι + 1), (k : ℝ) * levelWeight k f = totalInfluence f := by
  rw [totalInfluence_eq_sum_card_mul_fourierCoeff_sq,
    ← sum_fiberwise_of_maps_to (g := card) (t := range (Fintype.card ι + 1))
      fun S _ => mem_range.mpr (Nat.lt_succ_of_le (card_le_univ S))]
  refine sum_congr rfl fun k _ => ?_
  rw [levelWeight, mul_sum]
  exact sum_congr rfl fun S hS => by rw [(mem_filter.mp hS).2]

/-- **Degree-weight Shannon entropy bound**: for every Boolean function `f : (ι → Bool) → Bool`
read as signs `F x = signVal (f x)`,
`∑ k ∈ range (|ι| + 1), W^k[F] * log₂ (1 / W^k[F]) ≤ 3 * totalInfluence F`. -/
theorem sum_levelWeight_mul_logb_inv_le_three_mul_totalInfluence
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) :
    (∑ k ∈ range (Fintype.card ι + 1),
        levelWeight k (fun x => signVal (f x)) *
          Real.logb 2 (1 / levelWeight k (fun x => signVal (f x)))) ≤
      3 * totalInfluence (fun x => signVal (f x)) := by
  set n := Fintype.card ι
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set W : ℕ → ℝ := fun k => levelWeight k F
  set I : ℝ := totalInfluence F
  change (∑ k ∈ range (n + 1), W k * Real.logb 2 (1 / W k)) ≤ 3 * I
  have hW_nonneg : ∀ k, 0 ≤ W k := fun k => levelWeight_nonneg k F
  have hsum_W : ∑ k ∈ range (n + 1), W k = 1 := sum_levelWeight_signVal f
  have hsum_kW : ∑ k ∈ range (n + 1), (k : ℝ) * W k = I := sum_mul_levelWeight_eq_totalInfluence F
  have hrange_split :
      ∀ g : ℕ → ℝ, ∑ k ∈ range (n + 1), g k = g 0 + ∑ k ∈ Icc 1 n, g k := by
    intro g
    have hdisj : Disjoint ({0} : Finset ℕ) (Icc 1 n) := by simp
    have hunion : ({0} : Finset ℕ) ∪ Icc 1 n = range (n + 1) := by
      ext k; simp only [mem_union, mem_singleton, mem_Icc, mem_range]; omega
    rw [← hunion, sum_union hdisj, sum_singleton]
  set q : ℝ := ∑ k ∈ Icc 1 n, W k
  have hW0_add_q : W 0 + q = 1 := by rw [← hrange_split W, hsum_W]
  have hq_nonneg : 0 ≤ q := sum_nonneg fun k _ => hW_nonneg k
  have hI_eq_sum : I = ∑ k ∈ Icc 1 n, (k : ℝ) * W k := by
    rw [← hsum_kW, hrange_split]; simp
  have hq_le_I : q ≤ I := by
    rw [hI_eq_sum]
    exact sum_le_sum fun k hk =>
      le_mul_of_one_le_left (hW_nonneg k) (by exact_mod_cast (mem_Icc.mp hk).1)
  rcases hq_nonneg.eq_or_lt with hq0 | hq_pos
  · have hall0 : ∀ k ∈ Icc 1 n, W k = 0 :=
      (sum_eq_zero_iff_of_nonneg fun k _ => hW_nonneg k).mp hq0.symm
    have hW0_one : W 0 = 1 := by linarith
    rw [hrange_split]
    have htail0 : (∑ k ∈ Icc 1 n, W k * Real.logb 2 (1 / W k)) = 0 :=
      sum_eq_zero fun k hk => by simp [hall0 k hk]
    rw [htail0, hW0_one]
    simp only [div_self one_ne_zero, Real.logb_one, mul_zero, add_zero]
    exact mul_nonneg (by norm_num) (totalInfluence_nonneg F)
  · have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hsplit_sum :
        (∑ k ∈ range (n + 1), W k * Real.logb 2 (1 / W k)) =
          (W 0 * Real.logb 2 (1 / W 0) + q * Real.logb 2 (1 / q)) +
            ∑ k ∈ Icc 1 n, W k * Real.logb 2 (q / W k) := by
      rw [hrange_split, add_assoc]
      congr 1
      rw [sum_mul, ← sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      rcases (hW_nonneg k).eq_or_lt with hWk0 | hWk_pos
      · simp [← hWk0]
      · rw [← mul_add, ← Real.logb_mul (by positivity) (by positivity)]
        congr 2; field_simp
    have hB_le_I : (∑ k ∈ Icc 1 n, W k * Real.logb 2 (q / W k)) ≤ I := by
      have hterm : ∀ k ∈ Icc 1 n,
          W k * Real.log (q / W k) - (k : ℝ) * W k * Real.log 2 ≤
            q * (1 / 2 : ℝ) ^ k - W k := by
        intro k _
        rcases (hW_nonneg k).eq_or_lt with hWk0 | hWk_pos
        · rw [← hWk0]; simp only [zero_mul, mul_zero, sub_zero]; positivity
        · have hmul := mul_le_mul_of_nonneg_left
            (log_le_sub_one_pos (show 0 < q * (1 / 2 : ℝ) ^ k / W k by positivity)) hWk_pos.le
          have hlog_rew :
              W k * Real.log (q * (1 / 2 : ℝ) ^ k / W k) =
                W k * Real.log (q / W k) - (k : ℝ) * W k * Real.log 2 := by
            rw [mul_div_right_comm, Real.log_mul (by positivity) (by positivity), Real.log_pow,
              one_div, Real.log_inv]
            ring
          have hrhs_rew : W k * (q * (1 / 2 : ℝ) ^ k / W k - 1) = q * (1 / 2 : ℝ) ^ k - W k := by
            field_simp
          linarith
      have hgeom_le : ∑ k ∈ Icc 1 n, (1 / 2 : ℝ) ^ k ≤ 1 := by
        have htelesc : ∀ m : ℕ, ∑ k ∈ Icc 1 m, (1 / 2 : ℝ) ^ k = 1 - (1 / 2 : ℝ) ^ m := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            have hdisj : Disjoint (Icc 1 m) {m + 1} := by simp
            have hunion : Icc 1 m ∪ {m + 1} = Icc 1 (m + 1) := by
              ext k; simp only [mem_union, mem_Icc, mem_singleton]; omega
            rw [← hunion, sum_union hdisj, sum_singleton, ihm, pow_succ]; ring
        rw [htelesc n]
        linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
      have hsum_le := sum_le_sum hterm
      simp only [sum_sub_distrib, ← sum_mul, ← mul_sum] at hsum_le
      have hrhs_nonpos : q * ∑ k ∈ Icc 1 n, (1 / 2 : ℝ) ^ k - q ≤ 0 := by nlinarith
      rw [← hI_eq_sum] at hsum_le
      have hdiv := div_le_div_of_nonneg_right (hsum_le.trans hrhs_nonpos) hlog2_pos.le
      rw [zero_div, sub_div, mul_div_cancel_right₀ I hlog2_pos.ne'] at hdiv
      simp only [Real.logb, ← mul_div_assoc, ← sum_div]
      linarith
    set H2 := W 0 * Real.logb 2 (1 / W 0) + q * Real.logb 2 (1 / q)
    have hH2_le_one : H2 ≤ 1 := by
      rcases (hW_nonneg 0).eq_or_lt with hW0_zero | hW0_pos
      · have hq1 : q = 1 := by linarith
        simp [H2, ← hW0_zero, hq1]
      · have h1 := mul_le_mul_of_nonneg_left
          (log_le_sub_one_pos (show 0 < (1 / 2 : ℝ) / W 0 by positivity)) hW0_pos.le
        have h2 := mul_le_mul_of_nonneg_left
          (log_le_sub_one_pos (show 0 < (1 / 2 : ℝ) / q by positivity)) hq_pos.le
        have hl1 : W 0 * Real.log ((1 / 2 : ℝ) / W 0) =
            W 0 * Real.log (1 / W 0) - W 0 * Real.log 2 := by
          rw [div_eq_mul_one_div, Real.log_mul (by norm_num) (by positivity), one_div,
            Real.log_inv]; ring
        have hl2 : q * Real.log ((1 / 2 : ℝ) / q) =
            q * Real.log (1 / q) - q * Real.log 2 := by
          rw [div_eq_mul_one_div, Real.log_mul (by norm_num) (by positivity), one_div,
            Real.log_inv]; ring
        have hr1 : W 0 * ((1 / 2 : ℝ) / W 0 - 1) = 1 / 2 - W 0 := by field_simp
        have hr2 : q * ((1 / 2 : ℝ) / q - 1) = 1 / 2 - q := by field_simp
        have hsum_log : W 0 * Real.log 2 + q * Real.log 2 = Real.log 2 := by
          rw [← add_mul, hW0_add_q, one_mul]
        have hcomb : W 0 * Real.log (1 / W 0) + q * Real.log (1 / q) ≤ Real.log 2 := by linarith
        have hdiv := div_le_div_of_nonneg_right hcomb hlog2_pos.le
        rw [add_div, div_self hlog2_pos.ne'] at hdiv
        dsimp [H2]
        simp only [Real.logb, ← mul_div_assoc]
        exact hdiv
    let p_t : ℝ := (hammingDist f (fun _ => false) : ℝ) / (2 : ℝ) ^ n
    let p_f : ℝ := (hammingDist f (fun _ => true) : ℝ) / (2 : ℝ) ^ n
    let α : ℝ := min p_t p_f
    have hpt_add_pf : p_t + p_f = 1 := by
      dsimp [p_t, p_f]
      rw [← add_div, div_eq_one_iff_eq (by positivity)]
      have hcard_eq :
          hammingDist f (fun _ => false) + hammingDist f (fun _ => true) = 2 ^ n := by
        rw [hammingDist, hammingDist]
        have heq_not :
            ({x : ι → Bool | f x ≠ true} : Finset (ι → Bool)) =
              ({x : ι → Bool | ¬f x ≠ false} : Finset (ι → Bool)) := by
          ext x; cases f x <;> simp
        rw [heq_not]
        simpa [n] using card_filter_add_card_filter_not (s := univ) fun x : ι → Bool => f x ≠ false
      exact_mod_cast hcard_eq
    have hexpect_F : (𝔼 x : ι → Bool, F x) = p_f - p_t := by
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Fintype.card_bool,
        Nat.cast_pow, Nat.cast_ofNat]
      dsimp [p_t, p_f, F, n]
      rw [← sub_div]; congr 1
      rw [hammingDist, hammingDist]
      have hsign_split : ∀ x : ι → Bool,
          signVal (f x) =
            (if f x ≠ true then (1 : ℝ) else 0) - (if f x ≠ false then (1 : ℝ) else 0) := by
        intro x; cases f x <;> simp [signVal]
      simp_rw [hsign_split, sum_sub_distrib, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hq_eq_alpha : q = 4 * α * (1 - α) := by
      have hW0_eq : W 0 = (p_f - p_t) ^ 2 := by dsimp [W]; rw [levelWeight_zero, hexpect_F]
      have hq_prod : q = 4 * p_t * p_f := by
        calc q = 1 - W 0 := by linarith
          _ = (p_t + p_f) ^ 2 - (p_f - p_t) ^ 2 := by rw [hpt_add_pf, hW0_eq]; ring
          _ = 4 * p_t * p_f := by ring
      rcases min_choice p_t p_f with hmin | hmin
      · calc
          q = 4 * p_t * p_f := hq_prod
          _ = 4 * p_t * (1 - p_t) := by rw [show p_f = 1 - p_t by linarith]
          _ = 4 * α * (1 - α) := by dsimp [α]; rw [hmin]
      · calc
          q = 4 * p_t * p_f := hq_prod
          _ = 4 * (1 - p_f) * p_f := by rw [show p_t = 1 - p_f by linarith]
          _ = 4 * p_f * (1 - p_f) := by ring
          _ = 4 * α * (1 - α) := by dsimp [α]; rw [hmin]
    have hα_le_half : α ≤ 1 / 2 := by
      linarith [min_le_left p_t p_f, min_le_right p_t p_f]
    have hα_pos : 0 < α := by
      have hα_nonneg : 0 ≤ α := le_min (by positivity) (by positivity)
      rcases hα_nonneg.eq_or_lt with hα0 | hpos
      · exfalso; rw [← hα0] at hq_eq_alpha; linarith
      · exact hpos
    have hisop : 2 * α * Real.logb 2 (1 / α) ≤ I := by
      simpa [p_t, p_f, α, one_div, I, F, n] using two_mul_min_mul_logb_inv_le_totalInfluence f
    have hH2_le_2I : H2 ≤ 2 * I := by
      by_cases hq_half : 1 / 2 ≤ q
      · linarith [hH2_le_one, hq_le_I]
      · push Not at hq_half
        by_cases hα_eighth : 1 / 8 ≤ α
        · have hα_lt_quarter : α < 1 / 4 := by
            by_contra hge; push Not at hge; nlinarith [hq_eq_alpha, hα_le_half]
          have h4_le_inv : 4 ≤ 1 / α := by rw [le_div_iff₀ hα_pos]; linarith
          have hlog_ge2 : 2 ≤ Real.logb 2 (1 / α) := by
            calc (2 : ℝ) = Real.logb 2 ((2 : ℝ) ^ 2) := by
                  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two]; ring
              _ ≤ Real.logb 2 (1 / α) :=
                Real.logb_le_logb_of_le one_lt_two (by norm_num) (by norm_num at *; linarith)
          linarith [hH2_le_one, show 1 ≤ 2 * I by nlinarith [hisop]]
        · push Not at hα_eighth
          have hW0_pos : 0 < W 0 := by linarith
          have hq_le_4α : q ≤ 4 * α := by nlinarith [hq_eq_alpha, hα_pos]
          have hq_ge_72α : (7 / 2 : ℝ) * α ≤ q := by nlinarith [hq_eq_alpha, hα_pos, hα_eighth]
          have hW0_term : W 0 * Real.logb 2 (1 / W 0) ≤ 4 * α / Real.log 2 := by
            have h1 : W 0 * Real.log (1 / W 0) ≤ q := by
              have hg := mul_le_mul_of_nonneg_left
                (log_le_sub_one_pos (show 0 < 1 / W 0 by positivity)) hW0_pos.le
              have hr : W 0 * (1 / W 0 - 1) = q := by
                have : W 0 * (1 / W 0 - 1) = 1 - W 0 := by field_simp
                linarith
              linarith
            calc W 0 * Real.logb 2 (1 / W 0) = W 0 * Real.log (1 / W 0) / Real.log 2 := by
                  rw [Real.logb, mul_div_assoc]
              _ ≤ q / Real.log 2 := div_le_div_of_nonneg_right h1 hlog2_pos.le
              _ ≤ 4 * α / Real.log 2 := div_le_div_of_nonneg_right hq_le_4α hlog2_pos.le
          have hlog72 : (3 / 2 : ℝ) ≤ Real.logb 2 (7 / 2) := by
            rw [Real.le_logb_iff_rpow_le one_lt_two (by norm_num)]
            have hsq : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 ≤ (7 / 2 : ℝ) ^ 2 := by
              have h23 : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
                rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul two_pos.le]; norm_num
              rw [h23]; norm_num
            nlinarith [Real.rpow_nonneg two_pos.le (3 / 2 : ℝ)]
          have hq_term : q * Real.logb 2 (1 / q) ≤ 4 * α * (Real.logb 2 (1 / α) - 3 / 2) := by
            have hinv_q_gt1 : 1 ≤ 1 / q := by rw [le_div_iff₀ hq_pos]; linarith
            have hlog_inv_q_nonneg : 0 ≤ Real.logb 2 (1 / q) :=
              Real.logb_nonneg one_lt_two hinv_q_gt1
            have hinv_le : 1 / q ≤ (2 / 7 : ℝ) * (1 / α) := by
              rw [div_le_iff₀ hq_pos]
              have hprod : (2 / 7 : ℝ) * (1 / α) * ((7 / 2 : ℝ) * α) = 1 := by field_simp
              calc (1 : ℝ) = (2 / 7 : ℝ) * (1 / α) * ((7 / 2 : ℝ) * α) := hprod.symm
                _ ≤ (2 / 7 : ℝ) * (1 / α) * q :=
                    mul_le_mul_of_nonneg_left hq_ge_72α (by positivity)
            have hlog_le : Real.logb 2 (1 / q) ≤ Real.logb 2 (1 / α) - 3 / 2 := by
              calc Real.logb 2 (1 / q) ≤ Real.logb 2 ((2 / 7 : ℝ) * (1 / α)) :=
                    Real.logb_le_logb_of_le one_lt_two (by positivity) hinv_le
                _ = Real.logb 2 (2 / 7) + Real.logb 2 (1 / α) :=
                    Real.logb_mul (by norm_num) (by positivity)
                _ = -Real.logb 2 (7 / 2) + Real.logb 2 (1 / α) := by
                    rw [show (2 / 7 : ℝ) = (7 / 2 : ℝ)⁻¹ by norm_num, Real.logb_inv]
                _ ≤ Real.logb 2 (1 / α) - 3 / 2 := by linarith
            calc q * Real.logb 2 (1 / q) ≤ 4 * α * Real.logb 2 (1 / q) :=
                  mul_le_mul_of_nonneg_right hq_le_4α hlog_inv_q_nonneg
              _ ≤ 4 * α * (Real.logb 2 (1 / α) - 3 / 2) :=
                  mul_le_mul_of_nonneg_left hlog_le (by positivity)
          have h4_div_log2 : 4 / Real.log 2 < 6 := by
            rw [div_lt_iff₀ hlog2_pos]; linarith [two_thirds_lt_log_two]
          have h4α_div_log2 : 4 * α / Real.log 2 ≤ 6 * α := by
            have := mul_le_mul_of_nonneg_left h4_div_log2.le hα_pos.le
            linarith [show 4 * α / Real.log 2 = α * (4 / Real.log 2) by ring]
          calc H2 = W 0 * Real.logb 2 (1 / W 0) + q * Real.logb 2 (1 / q) := rfl
            _ ≤ 4 * α / Real.log 2 + 4 * α * (Real.logb 2 (1 / α) - 3 / 2) :=
                add_le_add hW0_term hq_term
            _ ≤ 6 * α + (4 * α * Real.logb 2 (1 / α) - 6 * α) := by linarith [h4α_div_log2]
            _ = 4 * α * Real.logb 2 (1 / α) := by ring
            _ ≤ 2 * I := by linarith [hisop]
    rw [hsplit_sum]
    linarith

end Cslib.BitString
