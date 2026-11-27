/-
Copyright (c) 2026 The Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Cslib contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree
public import CslibFrontier.Probability.Minimax.Value
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs

import CslibFrontier.Foundations.BooleanAnalysis.Symmetrization
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Error Amplification and `[0, 1]`-Boundedness for Approximate Degree

Univariate majority amplification polynomials convert any real polynomial approximating
a Boolean function within constant error `1 / 3` into:
1. A polynomial bounded in `[0, 1]` on the Boolean cube `{0, 1}^n` of degree at most
   `13 · adeg_{1/3}(f)` (`exists_mem_lowDegree_Icc_of_approxDegree`).
2. An `δ`-approximating polynomial bounded in `[0, 1]` of degree `13 · (2 r + 1) · adeg_{1/3}(f)`
   whenever `(1 / 3) · (8 / 9)^r ≤ δ` (`approxDegree_amplify_le`).

We also record the skew-symmetric zero-sum minimax value theorem (`isMinimaxValue_zero_of_skew`):
every finite matrix game satisfying `M i j + M j i = 0` over a linearly ordered field has minimax
value `0`.

## Main definitions

* `CslibFrontier.QueryComplexity.majorityAmpPoly`: univariate `(2 r + 1)`-coin majority polynomial
  `∑_{k = r + 1}^{2 r + 1} ((2 r + 1).choose k) X^k (1 - X)^(2 r + 1 - k)`.

## Main results

* `CslibFrontier.QueryComplexity.abs_eval_majorityAmpPoly_sub_bitVal_le`:
  `|(majorityAmpPoly r).eval x - bitVal ℝ b| ≤ ε · (4 ε (1 - ε))^r` for `x ∈ [0, 1]` within
  `ε ≤ 1 / 2` of `bitVal ℝ b`.
* `CslibFrontier.QueryComplexity.exists_mem_lowDegree_Icc_of_approxDegree`: every Boolean function
  `f` admits a `[0, 1]`-valued `(1 / 3)`-approximating polynomial of degree `≤ 13 · adeg_{1/3}(f)`.
* `CslibFrontier.QueryComplexity.approxDegree_amplify_le`:
  `adeg_δ(f) ≤ 13 · (2 r + 1) · adeg_{1/3}(f)` whenever `(1 / 3) · (8 / 9)^r ≤ δ`.
* `CslibFrontier.QueryComplexity.isMinimaxValue_zero_of_skew`: a skew-symmetric finite matrix game
  has minimax value `0`.
-/

public section

open Finset Polynomial
open scoped BigOperators NNReal

namespace CslibFrontier.QueryComplexity

/-- Univariate majority-of-`(2 r + 1)`-coins amplification polynomial
`A_r(X) = ∑_{k = r + 1}^{2 r + 1} ((2 r + 1).choose k) X^k (1 - X)^(2 r + 1 - k)`. -/
noncomputable def majorityAmpPoly (r : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.Icc (r + 1) (2 * r + 1),
    C ((Nat.choose (2 * r + 1) k : ℕ) : ℝ) * X ^ k * (1 - X) ^ (2 * r + 1 - k)

/-- `(majorityAmpPoly r).eval x` equals the binomial tail sum. -/
theorem eval_majorityAmpPoly (r : ℕ) (x : ℝ) :
    (majorityAmpPoly r).eval x =
      ∑ k ∈ Finset.Icc (r + 1) (2 * r + 1),
        ((Nat.choose (2 * r + 1) k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (2 * r + 1 - k) := by
  simp [majorityAmpPoly, Polynomial.eval_finsetSum]

/-- `majorityAmpPoly r` has degree at most `2 r + 1`. -/
theorem natDegree_majorityAmpPoly_le (r : ℕ) : (majorityAmpPoly r).natDegree ≤ 2 * r + 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hk2 : k ≤ 2 * r + 1 := (Finset.mem_Icc.mp hk).2
  have h1 : (C ((Nat.choose (2 * r + 1) k : ℕ) : ℝ) * X ^ k).natDegree ≤ k :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have h1X : (1 - X : ℝ[X]).natDegree ≤ 1 :=
    Polynomial.natDegree_sub_le_of_le
      (show (1 : ℝ[X]).natDegree ≤ 1 by rw [Polynomial.natDegree_one]; decide)
      Polynomial.natDegree_X_le
  have h2 : ((1 - X : ℝ[X]) ^ (2 * r + 1 - k)).natDegree ≤ 2 * r + 1 - k :=
    Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (2 * r + 1 - k) h1X)
  exact Polynomial.natDegree_mul_le.trans (by omega)

private lemma sum_choose_binomial_one (r : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (2 * r + 2),
      ((Nat.choose (2 * r + 1) k : ℕ) : ℝ) * t ^ k * (1 - t) ^ (2 * r + 1 - k) = 1 := by
  have h := add_pow t (1 - t) (2 * r + 1)
  rw [add_sub_cancel, one_pow] at h
  conv_rhs => rw [h]
  rw [show 2 * r + 1 + 1 = 2 * r + 2 by omega]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Reflection symmetry `A_r(1 - x) = 1 - A_r(x)`. -/
theorem eval_majorityAmpPoly_one_sub (r : ℕ) (x : ℝ) :
    (majorityAmpPoly r).eval (1 - x) = 1 - (majorityAmpPoly r).eval x := by
  rw [eval_majorityAmpPoly, eval_majorityAmpPoly]
  have hfull := sum_choose_binomial_one r x
  have hsplit :
      Finset.range (2 * r + 2) =
        Finset.range (r + 1) ∪ Finset.Icc (r + 1) (2 * r + 1) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.range (r + 1)) (Finset.Icc (r + 1) (2 * r + 1)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have := Finset.mem_range.mp hk1
    have := (Finset.mem_Icc.mp hk2).1
    omega
  rw [hsplit, Finset.sum_union hdisj] at hfull
  have hsymm :
      ∑ k ∈ Finset.Icc (r + 1) (2 * r + 1),
          ((Nat.choose (2 * r + 1) k : ℕ) : ℝ) * (1 - x) ^ k * (1 - (1 - x)) ^ (2 * r + 1 - k) =
        ∑ j ∈ Finset.range (r + 1),
          ((Nat.choose (2 * r + 1) j : ℕ) : ℝ) * x ^ j * (1 - x) ^ (2 * r + 1 - j) := by
    refine Finset.sum_bij (fun k _ => 2 * r + 1 - k)
      (fun k hk => by
        have := Finset.mem_Icc.mp hk
        rw [Finset.mem_range]
        omega)
      (fun k₁ hk₁ k₂ hk₂ _ => by
        have := (Finset.mem_Icc.mp hk₁).2
        have := (Finset.mem_Icc.mp hk₂).2
        omega)
      (fun j hj => by
        have := Finset.mem_range.mp hj
        exact ⟨2 * r + 1 - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩)
      fun k hk => ?_
    have hk2 : k ≤ 2 * r + 1 := (Finset.mem_Icc.mp hk).2
    rw [Nat.choose_symm hk2, show 2 * r + 1 - (2 * r + 1 - k) = k by omega, sub_sub_cancel]
    ring
  linarith

/-- `majorityAmpPoly r` maps `[0, 1]` into `[0, 1]`. -/
theorem eval_majorityAmpPoly_mem_Icc (r : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (majorityAmpPoly r).eval x ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ x := hx.1
  have h1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hnonneg : 0 ≤ (majorityAmpPoly r).eval x := by
    rw [eval_majorityAmpPoly]
    exact Finset.sum_nonneg fun k _ => by positivity
  have hle : (majorityAmpPoly r).eval x ≤ 1 := by
    calc
      (majorityAmpPoly r).eval x
        = ∑ k ∈ Finset.Icc (r + 1) (2 * r + 1),
            ((Nat.choose (2 * r + 1) k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (2 * r + 1 - k) :=
          eval_majorityAmpPoly r x
      _ ≤ ∑ k ∈ Finset.range (2 * r + 2),
            ((Nat.choose (2 * r + 1) k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (2 * r + 1 - k) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => by positivity
          rw [Finset.mem_range]
          have := (Finset.mem_Icc.mp hk).2
          omega
      _ = 1 := sum_choose_binomial_one r x
  exact ⟨hnonneg, hle⟩

private lemma sum_choose_upper_half (r : ℕ) :
    ∑ k ∈ Finset.Icc (r + 1) (2 * r + 1), ((Nat.choose (2 * r + 1) k : ℕ) : ℝ) = 4 ^ r := by
  have h2 := Nat.sum_range_choose (2 * r + 1)
  have hsplit :
      Finset.range (2 * r + 2) =
        Finset.range (r + 1) ∪ Finset.Icc (r + 1) (2 * r + 1) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.range (r + 1)) (Finset.Icc (r + 1) (2 * r + 1)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have := Finset.mem_range.mp hk1
    have := (Finset.mem_Icc.mp hk2).1
    omega
  rw [show 2 * r + 1 + 1 = 2 * r + 2 by omega, hsplit, Finset.sum_union hdisj] at h2
  have hsymm :
      ∑ j ∈ Finset.range (r + 1), (2 * r + 1).choose j =
        ∑ k ∈ Finset.Icc (r + 1) (2 * r + 1), (2 * r + 1).choose k := by
    refine Finset.sum_bij (fun j _ => 2 * r + 1 - j)
      (fun j hj => by
        have := Finset.mem_range.mp hj
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun j₁ hj₁ j₂ hj₂ _ => by
        have := Finset.mem_range.mp hj₁
        have := Finset.mem_range.mp hj₂
        omega)
      (fun k hk => by
        have := Finset.mem_Icc.mp hk
        exact ⟨2 * r + 1 - k, Finset.mem_range.mpr (by omega), by omega⟩)
      fun j hj => ?_
    have hj' : j ≤ 2 * r + 1 := by
      have := Finset.mem_range.mp hj
      omega
    exact (Nat.choose_symm hj').symm
  rw [hsymm] at h2
  have hpow : 2 ^ (2 * r + 1) = 2 * 4 ^ r := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [hpow] at h2
  have hnat : ∑ k ∈ Finset.Icc (r + 1) (2 * r + 1), (2 * r + 1).choose k = 4 ^ r := by omega
  exact_mod_cast hnat

private lemma eval_majorityAmpPoly_le_of_le_half (r : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    (majorityAmpPoly r).eval t ≤ t * (4 * t * (1 - t)) ^ r := by
  have h1t : t ≤ 1 - t := by linarith
  have h1t0 : 0 ≤ 1 - t := by linarith
  rw [eval_majorityAmpPoly]
  calc
    ∑ k ∈ Finset.Icc (r + 1) (2 * r + 1),
        ((Nat.choose (2 * r + 1) k : ℕ) : ℝ) * t ^ k * (1 - t) ^ (2 * r + 1 - k)
      ≤ ∑ k ∈ Finset.Icc (r + 1) (2 * r + 1),
          ((Nat.choose (2 * r + 1) k : ℕ) : ℝ) * (t * (t * (1 - t)) ^ r) := by
        refine Finset.sum_le_sum fun k hk => ?_
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        set j := k - (r + 1)
        have hj_le : j ≤ r := by omega
        have hk_eq : k = r + 1 + j := by omega
        have hsub_eq : 2 * r + 1 - k = r - j := by omega
        have hj_pow : t ^ j ≤ (1 - t) ^ j := pow_le_pow_left₀ ht0 h1t j
        have hterm :
            t ^ k * (1 - t) ^ (2 * r + 1 - k) ≤ t * (t * (1 - t)) ^ r := by
          rw [hsub_eq, hk_eq]
          calc
            t ^ (r + 1 + j) * (1 - t) ^ (r - j)
              = t * t ^ r * (t ^ j * (1 - t) ^ (r - j)) := by ring
            _ ≤ t * t ^ r * ((1 - t) ^ j * (1 - t) ^ (r - j)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hj_pow (by positivity)) (by positivity)
            _ = t * t ^ r * (1 - t) ^ r := by rw [← pow_add, Nat.add_sub_of_le hj_le]
            _ = t * (t * (1 - t)) ^ r := by rw [mul_pow]; ring
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = (∑ k ∈ Finset.Icc (r + 1) (2 * r + 1), ((Nat.choose (2 * r + 1) k : ℕ) : ℝ)) *
          (t * (t * (1 - t)) ^ r) := (Finset.sum_mul _ _ _).symm
    _ = t * (4 * t * (1 - t)) ^ r := by
        rw [sum_choose_upper_half, mul_pow, mul_pow]
        ring

/-- Binomial-majority tail bound: for `t ∈ [0, 1]` within `ε ≤ 1 / 2` of `bitVal ℝ b`,
`|(majorityAmpPoly r).eval t - bitVal ℝ b| ≤ ε · (4 ε (1 - ε))^r`. -/
theorem abs_eval_majorityAmpPoly_sub_bitVal_le (r : ℕ) {t : ℝ} {b : Bool} {ε : ℝ}
    (htI : t ∈ Set.Icc (0 : ℝ) 1) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (ht : |t - Cslib.BitString.bitVal ℝ b| ≤ ε) :
    |(majorityAmpPoly r).eval t - Cslib.BitString.bitVal ℝ b| ≤
      ε * (4 * ε * (1 - ε)) ^ r := by
  have hmono_quad {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 2) :
      4 * u * (1 - u) ≤ 4 * v * (1 - v) := by
    nlinarith
  cases b
  · simp only [Cslib.BitString.bitVal_false, sub_zero] at ht ⊢
    have ht_le : t ≤ ε := (le_abs_self t).trans ht
    have hbase0 : 0 ≤ 4 * t * (1 - t) := by nlinarith [htI.1, htI.2]
    rw [abs_of_nonneg (eval_majorityAmpPoly_mem_Icc r htI).1]
    calc
      (majorityAmpPoly r).eval t ≤ t * (4 * t * (1 - t)) ^ r :=
        eval_majorityAmpPoly_le_of_le_half r htI.1 (ht_le.trans hε)
      _ ≤ ε * (4 * ε * (1 - ε)) ^ r :=
        mul_le_mul ht_le
          (pow_le_pow_left₀ hbase0 (hmono_quad htI.1 ht_le hε) r)
          (pow_nonneg hbase0 r) hε0
  · simp only [Cslib.BitString.bitVal_true] at ht ⊢
    have h1t_le : 1 - t ≤ ε := by linarith [(abs_le.mp ht).1]
    have h1tI : 1 - t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [htI.2], by linarith [htI.1]⟩
    have hbase1 : 0 ≤ 4 * (1 - t) * (1 - (1 - t)) := by nlinarith [h1tI.1, h1tI.2]
    have hsub : (majorityAmpPoly r).eval t - 1 = -(majorityAmpPoly r).eval (1 - t) := by
      linarith [eval_majorityAmpPoly_one_sub r t]
    rw [hsub, abs_neg, abs_of_nonneg (eval_majorityAmpPoly_mem_Icc r h1tI).1]
    calc
      (majorityAmpPoly r).eval (1 - t)
        ≤ (1 - t) * (4 * (1 - t) * (1 - (1 - t))) ^ r :=
          eval_majorityAmpPoly_le_of_le_half r h1tI.1 (h1t_le.trans hε)
      _ ≤ ε * (4 * ε * (1 - ε)) ^ r :=
        mul_le_mul h1t_le
          (pow_le_pow_left₀ hbase1 (hmono_quad h1tI.1 h1t_le hε) r)
          (pow_nonneg hbase1 r) hε0

private lemma poly_comp_mem_lowDegree {ι : Type*} {d D : ℕ} {Q : ℝ[X]} (hQ : Q.natDegree ≤ d)
    {p : (ι → Bool) → ℝ} (hp : p ∈ Cslib.BitString.lowDegree ℝ ι D) :
    (fun x => Q.eval (p x)) ∈ Cslib.BitString.lowDegree ℝ ι (d * D) := by
  have hsum_fn : (fun x => Q.eval (p x)) =
      ∑ k ∈ Finset.range (d + 1), fun x => Q.coeff k * p x ^ k := by
    funext x
    conv_lhs => rw [Q.as_sum_range' (d + 1) (Nat.lt_succ_of_le hQ)]
    simp [Polynomial.eval_finsetSum]
  rw [hsum_fn]
  refine Submodule.sum_mem (Cslib.BitString.lowDegree ℝ ι (d * D)) fun k hk => ?_
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hpow : (fun x => p x ^ k) ∈ Cslib.BitString.lowDegree ℝ ι (d * D) :=
    Cslib.BitString.lowDegree_mono (Nat.mul_le_mul_right D hk_le)
      (Cslib.BitString.pow_mem_lowDegree hp k)
  exact (show Q.coeff k • (fun x => p x ^ k) = fun x => Q.coeff k * p x ^ k from rfl) ▸
    Submodule.smul_mem _ (Q.coeff k) hpow

/-- Every Boolean function `f : BitString n → Bool` admits a `[0, 1]`-valued `(1 / 3)`-approximating
real polynomial on `{0, 1}^n` of degree at most `13 · adeg_{1/3}(f)`. -/
theorem exists_mem_lowDegree_Icc_of_approxDegree {n : ℕ} (f : Cslib.BooleanFunction n) :
    ∃ p ∈ Cslib.BitString.lowDegree ℝ (Fin n)
        (13 * Cslib.QueryComplexity.approxDegree (1 / 3) f),
      (∀ x, p x ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ x, |p x - Cslib.BitString.bitVal ℝ (f x)| ≤ (1 / 3 : ℝ) := by
  obtain ⟨p, hp, hpf⟩ :=
    Cslib.QueryComplexity.exists_mem_lowDegree_approxDegree (ε := 1 / 3) (f := f)
  set D := Cslib.QueryComplexity.approxDegree (1 / 3) f
  let ptilde : Cslib.BitString n → ℝ := fun x => (3 / 5 : ℝ) * p x + 1 / 5
  have hpt_deg : ptilde ∈ Cslib.BitString.lowDegree ℝ (Fin n) D := by
    change (3 / 5 : ℝ) • p + (fun _ => (1 / 5 : ℝ)) ∈ _
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hp)
      (Cslib.BitString.const_mem_lowDegree D _)
  have h13 : ((1 / 3 : ℝ≥0) : ℝ) = 1 / 3 := by norm_num
  have hptI (x : Cslib.BitString n) : ptilde x ∈ Set.Icc (0 : ℝ) 1 := by
    have hpx := abs_le.mp (h13 ▸ hpf x)
    cases hfx : f x
    · simp only [hfx, Cslib.BitString.bitVal_false, sub_zero] at hpx
      exact ⟨by dsimp [ptilde]; linarith, by dsimp [ptilde]; linarith⟩
    · simp only [hfx, Cslib.BitString.bitVal_true] at hpx
      exact ⟨by dsimp [ptilde]; linarith, by dsimp [ptilde]; linarith⟩
  have hpt_err (x : Cslib.BitString n) :
      |ptilde x - Cslib.BitString.bitVal ℝ (f x)| ≤ 2 / 5 := by
    have hpx := abs_le.mp (h13 ▸ hpf x)
    rw [abs_le]
    cases hfx : f x
    · simp only [hfx, Cslib.BitString.bitVal_false, sub_zero] at hpx ⊢
      exact ⟨by dsimp [ptilde]; linarith, by dsimp [ptilde]; linarith⟩
    · simp only [hfx, Cslib.BitString.bitVal_true] at hpx ⊢
      exact ⟨by dsimp [ptilde]; linarith, by dsimp [ptilde]; linarith⟩
  refine ⟨fun x => (majorityAmpPoly 6).eval (ptilde x),
    poly_comp_mem_lowDegree (natDegree_majorityAmpPoly_le 6) hpt_deg,
    fun x => eval_majorityAmpPoly_mem_Icc 6 (hptI x), fun x => ?_⟩
  have h := abs_eval_majorityAmpPoly_sub_bitVal_le 6 (hptI x) (ε := 2 / 5) (by norm_num)
    (by norm_num) (hpt_err x)
  have hnum : (2 / 5 : ℝ) * (4 * (2 / 5 : ℝ) * (1 - 2 / 5)) ^ 6 ≤ 1 / 3 := by norm_num
  exact h.trans hnum

/-- Error amplification for approximate degree: if `(1 / 3) · (8 / 9)^r ≤ δ`, then
`adeg_δ(f) ≤ 13 · (2 r + 1) · adeg_{1/3}(f)`. -/
theorem approxDegree_amplify_le {n : ℕ} (f : Cslib.BooleanFunction n) (r : ℕ) {δ : ℝ≥0}
    (hδ : (1 / 3 : ℝ) * (8 / 9 : ℝ) ^ r ≤ δ) :
    Cslib.QueryComplexity.approxDegree δ f ≤
      13 * (2 * r + 1) * Cslib.QueryComplexity.approxDegree (1 / 3) f := by
  obtain ⟨p, hp, hpI, hpf⟩ := exists_mem_lowDegree_Icc_of_approxDegree f
  have hdeg : (fun x => (majorityAmpPoly r).eval (p x)) ∈
      Cslib.BitString.lowDegree ℝ (Fin n)
        (13 * (2 * r + 1) * Cslib.QueryComplexity.approxDegree (1 / 3) f) := by
    have hcomp := poly_comp_mem_lowDegree (natDegree_majorityAmpPoly_le r) hp
    exact (show (2 * r + 1) * (13 * Cslib.QueryComplexity.approxDegree (1 / 3) f) =
      13 * (2 * r + 1) * Cslib.QueryComplexity.approxDegree (1 / 3) f by ring) ▸ hcomp
  refine Cslib.QueryComplexity.approxDegree_le_of_mem_lowDegree hdeg fun x => ?_
  have h := abs_eval_majorityAmpPoly_sub_bitVal_le r (hpI x) (ε := 1 / 3) (by norm_num)
    (by norm_num) (hpf x)
  rw [show (4 * (1 / 3 : ℝ) * (1 - 1 / 3)) = 8 / 9 by norm_num] at h
  exact h.trans hδ

/-- Every finite zero-sum matrix game over a linearly ordered field satisfying skew-symmetry
`M j i = -M i j` has minimax value `0`. -/
theorem isMinimaxValue_zero_of_skew {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Type*} [Fintype A] [Nonempty A] (M : A → A → K) (hskew : ∀ i j, M j i = -M i j) :
    Cslib.Probability.IsMinimaxValue M 0 := by
  obtain ⟨v, ⟨p, hp⟩, q, hq⟩ := Cslib.Probability.exists_isMinimaxValue M
  have hneg : Cslib.Probability.IsMinimaxValue M (-v) := by
    refine ⟨⟨q, fun j => ?_⟩, p, fun i => ?_⟩
    · have h1 := hq j
      have hsum : ∑ i : A, q.weights i * M i j = -(∑ i : A, q.weights i * M j i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [hskew j i]; ring
      linarith
    · have h1 := hp i
      have hsum : ∑ j : A, p.weights j * M i j = -(∑ j : A, p.weights j * M j i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [hskew i j]; ring
      linarith
  have hv0 : v = 0 := by
    have heq := Cslib.Probability.IsMinimaxValue.unique ⟨⟨p, hp⟩, q, hq⟩ hneg
    have htwo : v + v = 0 := by linarith
    have h2pos : (0 : K) < 2 := zero_lt_two
    have hmul : (2 : K) * v = 0 := by rw [two_mul]; exact htwo
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt h2pos)
  exact hv0 ▸ ⟨⟨p, hp⟩, q, hq⟩

end CslibFrontier.QueryComplexity
