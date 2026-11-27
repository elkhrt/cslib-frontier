/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.ReadOnce
public import CslibFrontier.Foundations.BooleanAnalysis.Bernoulli
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
public import CslibFrontier.Foundations.BooleanAnalysis.Monotone
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Coin Problem, Level-`k` Fourier Growth, and Restriction-Closed Coin Bounds

This module develops general Boolean-analytic machinery for the `ε`-biased coin problem on the
hypercube (`Cslib.BitString.bernoulliAverage ((1 - ε) / 2)`), level-`k` Fourier `ℓ₁` growth,
the Chattopadhyay–Hatami–Hosseini–Lovett / Tal (CHHL/Tal) random-restriction decomposition,
Tal's restriction-closed coin theorem, and unconditional coin and level-`1` Fourier bounds for
width-`2` read-once branching programs (`Cslib.BranchingPrograms.ReadOnceProgram`).

## Main definitions

* `CslibFrontier.BooleanAnalysis.biasedExpect`, `CslibFrontier.BooleanAnalysis.coinAdvantage`:
  `ε`-biased product expectation and distinguishing advantage against the uniform measure.
* `CslibFrontier.BooleanAnalysis.levelL1Norm`, `CslibFrontier.BooleanAnalysis.HasFourierGrowth`:
  level-`k` Fourier `ℓ₁` norms and class Fourier growth.
* `CslibFrontier.BooleanAnalysis.chhlCoordWeight`,
  `CslibFrontier.BooleanAnalysis.chhlRestrictionWeight`: CHHL/Tal random-restriction weights.
* `CslibFrontier.BooleanAnalysis.ComputableByReadOnceBP`: unordered width-`w` read-once branching
  program sign computability.

## Main results

* `CslibFrontier.BooleanAnalysis.biasedExpect_eq_sum_fourierCoeff`: Fourier polynomial expansion of
  `biasedExpect ε f`.
* `CslibFrontier.BooleanAnalysis.abs_div_biasedExpect_sub_sum_singleton_le_high_var`: effective
  low-bias difference-quotient error bound in terms of degree-`≥ 2` Fourier variance.
* `CslibFrontier.BooleanAnalysis.biasedExpect_add_eq_sum_chhlRestriction`,
  `CslibFrontier.BooleanAnalysis.tal_coin_bound_of_restriction_closed`: CHHL/Tal restriction
  identity and Tal's logarithmic coin theorem for restriction-closed classes.
* `CslibFrontier.BooleanAnalysis.readOnceBP_coin_bound_two`,
  `CslibFrontier.BooleanAnalysis.levelOneNorm_le_two_of_computableByReadOnceBP_two`: sharp `2 |ε|`
  coin bound and `levelL1Norm 1 f ≤ 2` bound for width-`2` read-once branching programs.
-/

public section

namespace CslibFrontier.BooleanAnalysis

open Cslib Cslib.BitString Cslib.BranchingPrograms Finset
open scoped BigOperators

section BiasedExpectAndGrowth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Product coin weight placing `(1 + ε) / 2` on `false` (`+1`) and `(1 - ε) / 2` on `true` (`-1`).
-/
noncomputable def biasedCoinWeight (ε : ℝ) (x : ι → Bool) : ℝ :=
  bernoulliWeight ((1 - ε) / 2) x

omit [DecidableEq ι] in
/-- Product formula for `biasedCoinWeight`. -/
theorem biasedCoinWeight_eq_prod (ε : ℝ) (x : ι → Bool) :
    biasedCoinWeight ε x = ∏ i : ι, (1 + ε * signVal (x i)) / 2 := by
  rw [biasedCoinWeight, bernoulliWeight]
  refine prod_congr rfl fun i _ ↦ ?_
  cases x i <;> simp <;> ring

/-- Expectation under the `ε`-biased product coin distribution. -/
noncomputable def biasedExpect (ε : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  bernoulliAverage ((1 - ε) / 2) f

private lemma biasedExpect_eq_sum (ε : ℝ) (f : (ι → Bool) → ℝ) :
    biasedExpect ε f = ∑ x : ι → Bool, biasedCoinWeight ε x * f x := by
  rw [biasedExpect, bernoulliAverage]
  rfl

/-- Distinguishing advantage `|biasedExpect ε f - 𝔼 x, f x|` in the `ε`-coin problem. -/
noncomputable def coinAdvantage (ε : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  |biasedExpect ε f - 𝔼 x, f x|

/-- The level-`k` Fourier `ℓ₁` norm `∑_{|S| = k} |fourierCoeff f S|`. -/
noncomputable def levelL1Norm (k : ℕ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ S with #S = k, |fourierCoeff f S|

/-- A class `ℱ` has Fourier growth at most `t` if `levelL1Norm k f ≤ t ^ k` for all `k` and
`f ∈ ℱ`. -/
def HasFourierGrowth (ℱ : Set ((ι → Bool) → ℝ)) (t : ℝ) : Prop :=
  ∀ k : ℕ, ∀ f ∈ ℱ, levelL1Norm k f ≤ t ^ k

@[simp]
theorem biasedExpect_zero (f : (ι → Bool) → ℝ) : biasedExpect 0 f = 𝔼 x, f x := by
  rw [biasedExpect, show ((1 : ℝ) - 0) / 2 = 1 / 2 by ring, bernoulliAverage_one_half]

@[simp]
theorem biasedExpect_const (ε c : ℝ) : biasedExpect ε (fun _ : ι → Bool ↦ c) = c := by
  exact bernoulliAverage_const _ c

@[simp]
theorem biasedExpect_chi (ε : ℝ) (S : Finset ι) : biasedExpect ε (chi ℝ S) = ε ^ #S := by
  rw [biasedExpect, bernoulliAverage_chi, show 1 - 2 * ((1 - ε) / 2) = ε by ring]

/-- Fourier polynomial expansion of `biasedExpect ε f`. -/
theorem biasedExpect_eq_sum_fourierCoeff (ε : ℝ) (f : (ι → Bool) → ℝ) :
    biasedExpect ε f = ∑ S : Finset ι, fourierCoeff f S * ε ^ #S := by
  conv_lhs => rw [funext fun x ↦ (sum_fourierCoeff_mul_chi f x).symm]
  rw [biasedExpect, bernoulliAverage_sum]
  exact sum_congr rfl fun S _ ↦ by
    rw [bernoulliAverage_const_mul, ← biasedExpect, biasedExpect_chi]

/-- Sign-reversal symmetry `biasedExpect (-ε) f = biasedExpect ε (fun x ↦ f (x + fun _ ↦ true))`. -/
theorem biasedExpect_neg_eq_comp_not (ε : ℝ) (f : (ι → Bool) → ℝ) :
    biasedExpect (-ε) f = biasedExpect ε (fun x ↦ f (x + fun _ ↦ true)) := by
  rw [biasedExpect, biasedExpect, show (1 - -ε) / 2 = 1 - (1 - ε) / 2 by ring,
    bernoulliAverage_one_sub]
  refine congrArg (bernoulliAverage ((1 - ε) / 2))
    (funext fun x ↦ congrArg f (funext fun i ↦ ?_))
  simp [Pi.add_apply, Bool.add_eq_xor]

/-- Cauchy–Schwarz bound relating `levelL1Norm k f` to `levelWeight k f`. -/
theorem levelL1Norm_le_sqrt_choose_mul_sqrt_levelWeight (k : ℕ) (f : (ι → Bool) → ℝ) :
    levelL1Norm k f ≤
      Real.sqrt ((Fintype.card ι).choose k) * Real.sqrt (levelWeight k f) := by
  let s : Finset (Finset ι) := univ.filter fun S ↦ #S = k
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ ↦ (1 : ℝ)) (fun S ↦ |fourierCoeff f S|)
  have hcard : (#s : ℝ) = (Fintype.card ι).choose k := by
    have hs : s = univ.powersetCard k := by ext S; simp [s]
    rw [hs, card_powersetCard, card_univ]
  simpa [s, levelL1Norm, levelWeight, hcard, sq_abs] using hcs

private lemma one_add_pow_sub_le_sq :
    ∀ (m : ℕ) {x : ℝ}, 0 ≤ x → (m : ℝ) * x ≤ 1 →
      (1 + x) ^ m - (1 + (m : ℝ) * x) ≤ ((m : ℝ) * x) ^ 2
  | 0, _, _, _ => by simp
  | m + 1, x, hx0, hmx => by
    have hm_le : (m : ℝ) * x ≤ 1 := by push_cast at hmx; nlinarith
    have ih := one_add_pow_sub_le_sq m hx0 hm_le
    have hmul : (1 + x) ^ (m + 1) ≤ (1 + (m : ℝ) * x + ((m : ℝ) * x) ^ 2) * (1 + x) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hcubic : ((m : ℝ) * x) * ((m : ℝ) * x ^ 2) ≤ 1 * ((m : ℝ) * x ^ 2) :=
      mul_le_mul_of_nonneg_right hm_le (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg x))
    push_cast
    nlinarith [sq_nonneg x]

private lemma sum_Icc_two_choose_mul_pow (m : ℕ) (x : ℝ) :
    (∑ k ∈ Icc 2 m, (m.choose k : ℝ) * x ^ k) = (1 + x) ^ m - (1 + (m : ℝ) * x) := by
  rcases m with _ | _ | m
  · simp
  · simp
  · have hbinom := add_pow x 1 (m + 2)
    have hsimp : (∑ k ∈ range (m + 2 + 1), x ^ k * 1 ^ (m + 2 - k) * ((m + 2).choose k : ℝ)) =
        1 + ((m + 2 : ℕ) : ℝ) * x + ∑ k ∈ Icc 2 (m + 2), ((m + 2).choose k : ℝ) * x ^ k := by
      have hsplit : range (m + 2 + 1) = insert 0 (insert 1 (Icc 2 (m + 2))) := by
        ext k; simp only [mem_range, mem_insert, mem_Icc]; omega
      rw [hsplit, sum_insert (by simp), sum_insert (by simp)]
      simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, pow_one,
        Nat.choose_one_right]
      have htail : (∑ k ∈ Icc 2 (m + 2), x ^ k * ((m + 2).choose k : ℝ)) =
          ∑ k ∈ Icc 2 (m + 2), ((m + 2).choose k : ℝ) * x ^ k :=
        sum_congr rfl fun _ _ ↦ mul_comm _ _
      rw [htail]
      ring
    rw [add_comm x 1] at hbinom
    linarith

/-- **Effective low-bias difference-quotient error bound**: for `ε ≠ 0` with `|ι| * ε ^ 2 ≤ 1`,
`|(biasedExpect ε f - 𝔼 x, f x) / ε - ∑ i, f̂({i})| ≤ |ε| * |ι| * √(Var[f] - ∑ i, f̂({i})^2)`. -/
theorem abs_div_biasedExpect_sub_sum_singleton_le_high_var {ε : ℝ} (hε0 : ε ≠ 0)
    (hε : (Fintype.card ι : ℝ) * ε ^ 2 ≤ 1) (f : (ι → Bool) → ℝ) :
    |(biasedExpect ε f - 𝔼 x, f x) / ε - ∑ i : ι, fourierCoeff f {i}| ≤
      |ε| * (Fintype.card ι : ℝ) *
        Real.sqrt ((𝔼 x, (f x - 𝔼 y, f y) ^ 2) - ∑ i : ι, fourierCoeff f {i} ^ 2) := by
  let n := Fintype.card ι
  have hsing : ∀ g : Finset ι → ℝ, (∑ i : ι, g {i}) = ∑ S with #S = 1, g S := fun g ↦ by
    refine sum_nbij (fun i ↦ ({i} : Finset ι)) (fun i _ ↦ by simp)
      (fun _ _ _ _ hij ↦ singleton_injective hij) (fun S hS ↦ ?_) (fun _ _ ↦ rfl)
    obtain ⟨i, hi⟩ := card_eq_one.mp (mem_filter.mp hS).2
    exact ⟨i, mem_univ i, hi.symm⟩
  have hrem : biasedExpect ε f - (𝔼 x, f x) - ε * ∑ i : ι, fourierCoeff f {i} =
      ∑ k ∈ Icc 2 n, ε ^ k * ∑ S with #S = k, fourierCoeff f S := by
    rw [biasedExpect_eq_sum_fourierCoeff,
      ← add_sum_erase univ (fun S ↦ fourierCoeff f S * ε ^ #S) (mem_univ ∅)]
    simp only [card_empty, pow_zero, mul_one, fourierCoeff_empty, add_sub_cancel_left]
    have herase : univ.erase (∅ : Finset ι) =
        univ.filter (fun S : Finset ι ↦ #S = 1) ∪
          univ.filter (fun S : Finset ι ↦ 2 ≤ #S) := by
      ext S
      by_cases hS : S = ∅
      · simp [hS]
      · have hpos : 1 ≤ #S := Nat.succ_le_of_lt (card_pos.mpr (nonempty_iff_ne_empty.mpr hS))
        simp only [mem_erase, mem_univ, and_true, true_and, mem_union, mem_filter]
        exact ⟨fun _ ↦ (eq_or_lt_of_le hpos).imp Eq.symm Nat.succ_le_of_lt, fun _ ↦ hS⟩
    have hdisj : Disjoint (univ.filter fun S : Finset ι ↦ #S = 1)
        (univ.filter fun S : Finset ι ↦ 2 ≤ #S) := by
      rw [disjoint_filter]; intro _ _ h1 h2; omega
    rw [herase, sum_union hdisj, hsing (fun S ↦ fourierCoeff f S), mul_sum]
    have h1 : (∑ S : Finset ι with #S = 1, fourierCoeff f S * ε ^ #S) =
        ∑ S : Finset ι with #S = 1, ε * fourierCoeff f S :=
      sum_congr rfl fun S hS ↦ by rw [(mem_filter.mp hS).2, pow_one, mul_comm]
    rw [h1, add_sub_cancel_left]
    have hmap : ∀ S ∈ univ.filter (fun S : Finset ι ↦ 2 ≤ #S), #S ∈ Icc 2 n := fun S hS ↦
      mem_Icc.mpr ⟨(mem_filter.mp hS).2, card_le_univ S⟩
    rw [← sum_fiberwise_of_maps_to hmap]
    refine sum_congr rfl fun k hk ↦ ?_
    have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
    have hfilt : (univ.filter (fun S : Finset ι ↦ 2 ≤ #S)).filter (fun S ↦ #S = k) =
        univ.filter (fun S : Finset ι ↦ #S = k) := by
      ext S; simp only [mem_filter, mem_univ, true_and]; omega
    rw [hfilt, mul_sum]
    exact sum_congr rfl fun S hS ↦ by rw [(mem_filter.mp hS).2, mul_comm]
  have h1 : |∑ k ∈ Icc 2 n, ε ^ k * ∑ S with #S = k, fourierCoeff f S| ≤
      ∑ k ∈ Icc 2 n, (|ε| ^ k * Real.sqrt (n.choose k)) * Real.sqrt (levelWeight k f) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦ ?_)
    rw [abs_mul, abs_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((abs_sum_le_sum_abs _ _).trans (levelL1Norm_le_sqrt_choose_mul_sqrt_levelWeight k f))
      (pow_nonneg (abs_nonneg ε) k)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Icc 2 n)
    (fun k ↦ |ε| ^ k * Real.sqrt (n.choose k)) (fun k ↦ Real.sqrt (levelWeight k f))
  have ha : (∑ k ∈ Icc 2 n, (|ε| ^ k * Real.sqrt (n.choose k)) ^ 2) =
      (1 + ε ^ 2) ^ n - (1 + (n : ℝ) * ε ^ 2) := by
    rw [← sum_Icc_two_choose_mul_pow n (ε ^ 2)]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← pow_mul, mul_comm k 2, pow_mul, sq_abs,
      mul_comm]
  have hb : (∑ k ∈ Icc 2 n, Real.sqrt (levelWeight k f) ^ 2) =
      (𝔼 x, (f x - 𝔼 y, f y) ^ 2) - ∑ i : ι, fourierCoeff f {i} ^ 2 := by
    have hsq : ∀ k ∈ Icc 2 n, Real.sqrt (levelWeight k f) ^ 2 = levelWeight k f :=
      fun k _ ↦ Real.sq_sqrt (levelWeight_nonneg k f)
    rw [sum_congr rfl hsq, expect_sub_expect_sq_eq_sum_fourierCoeff_sq,
      hsing (fun S ↦ fourierCoeff f S ^ 2)]
    have hpart : univ.filter (fun S : Finset ι ↦ S ≠ ∅) =
        univ.filter (fun S : Finset ι ↦ #S = 1) ∪
          univ.filter (fun S : Finset ι ↦ 2 ≤ #S) := by
      ext S
      by_cases hS : S = ∅
      · simp [hS]
      · have hpos : 1 ≤ #S := Nat.succ_le_of_lt (card_pos.mpr (nonempty_iff_ne_empty.mpr hS))
        simp only [mem_filter, mem_union, mem_univ, true_and]
        exact ⟨fun _ ↦ (eq_or_lt_of_le hpos).imp Eq.symm Nat.succ_le_of_lt, fun _ ↦ hS⟩
    have hdisj : Disjoint (univ.filter fun S : Finset ι ↦ #S = 1)
        (univ.filter fun S : Finset ι ↦ 2 ≤ #S) := by
      rw [disjoint_filter]; intro _ _ h1 h2; omega
    rw [hpart, sum_union hdisj, add_sub_cancel_left]
    simp only [levelWeight]
    have hmap : ∀ S ∈ univ.filter (fun S : Finset ι ↦ 2 ≤ #S), #S ∈ Icc 2 n := fun S hS ↦
      mem_Icc.mpr ⟨(mem_filter.mp hS).2, card_le_univ S⟩
    rw [← sum_fiberwise_of_maps_to hmap]
    refine sum_congr rfl fun k hk ↦ sum_congr ?_ fun _ _ ↦ rfl
    have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
    ext S; simp only [mem_filter, mem_univ, true_and]; omega
  have hsqrt_a : Real.sqrt ((1 + ε ^ 2) ^ n - (1 + (n : ℝ) * ε ^ 2)) ≤ (n : ℝ) * ε ^ 2 :=
    (Real.sqrt_le_sqrt (one_add_pow_sub_le_sq n (sq_nonneg ε) hε)).trans_eq
      (Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg ε)))
  rw [ha, hb] at hcs
  have hundiv : |biasedExpect ε f - (𝔼 x, f x) - ε * ∑ i : ι, fourierCoeff f {i}| ≤
      (n : ℝ) * ε ^ 2 *
        Real.sqrt ((𝔼 x, (f x - 𝔼 y, f y) ^ 2) - ∑ i : ι, fourierCoeff f {i} ^ 2) := by
    rw [hrem]
    exact h1.trans (hcs.trans (mul_le_mul_of_nonneg_right hsqrt_a (Real.sqrt_nonneg _)))
  have habs_pos : 0 < |ε| := abs_pos.mpr hε0
  have hdiv : (biasedExpect ε f - 𝔼 x, f x) / ε - ∑ i : ι, fourierCoeff f {i} =
      (biasedExpect ε f - (𝔼 x, f x) - ε * ∑ i : ι, fourierCoeff f {i}) / ε := by
    field_simp [hε0]
  rw [hdiv, abs_div, div_le_iff₀ habs_pos]
  refine hundiv.trans_eq ?_
  rw [show ε ^ 2 = |ε| * |ε| by rw [← sq_abs, sq]]
  ring

end BiasedExpectAndGrowth

/-! ### CHHL/Tal Random-Restriction Decomposition and Tal's Coin Theorem -/

section TalCoinTheorem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Single-coordinate CHHL/Tal restriction weight at bias `ε₀`. -/
noncomputable def chhlCoordWeight (ε₀ : ℝ) (o : Option Bool) : ℝ :=
  if 0 ≤ ε₀ then
    match o with
    | some false => ε₀
    | none => 1 - ε₀
    | some true => 0
  else
    match o with
    | some true => -ε₀
    | none => 1 + ε₀
    | some false => 0

omit [DecidableEq ι] in
/-- Product CHHL/Tal restriction distribution weight on `PartialAssignment ι`. -/
noncomputable def chhlRestrictionWeight (ε₀ : ℝ) (ρ : PartialAssignment ι) : ℝ :=
  ∏ i : ι, chhlCoordWeight ε₀ (ρ i)

omit [DecidableEq ι] in
theorem chhlRestrictionWeight_nonneg {ε₀ : ℝ} (hε₀ : |ε₀| ≤ 1) (ρ : PartialAssignment ι) :
    0 ≤ chhlRestrictionWeight ε₀ ρ := by
  refine prod_nonneg fun i _ ↦ ?_
  have hbd := abs_le.mp hε₀
  rw [chhlCoordWeight.eq_def]
  split_ifs with h0 <;> cases ρ i with
  | none => linarith
  | some b => cases b <;> linarith

theorem sum_chhlRestrictionWeight_eq_one (ε₀ : ℝ) :
    ∑ ρ : PartialAssignment ι, chhlRestrictionWeight ε₀ ρ = 1 := by
  simp_rw [chhlRestrictionWeight]
  rw [← Fintype.prod_sum]
  refine prod_eq_one fun _ _ ↦ ?_
  rw [Fintype.sum_option, Fintype.sum_bool]
  by_cases h0 : 0 ≤ ε₀ <;> simp [chhlCoordWeight.eq_def, h0]

private lemma chhl_coord_sum_eq {ε₀ : ℝ} (hε₀ : |ε₀| < 1) (ε : ℝ) (c : Bool) :
    (∑ o : Option Bool, ∑ b : Bool, chhlCoordWeight ε₀ o *
        ((1 + (ε / (1 - |ε₀|)) * signVal b) / 2) * (if o.getD b = c then 1 else 0)) =
      (1 + (ε₀ + ε) * signVal c) / 2 := by
  have hne : 1 - |ε₀| ≠ 0 := sub_ne_zero.mpr hε₀.ne'
  rw [Fintype.sum_option]
  simp_rw [Fintype.sum_bool]
  by_cases h0 : 0 ≤ ε₀
  · have hne' : 1 - ε₀ ≠ 0 := by rwa [abs_of_nonneg h0] at hne
    cases c <;> simp [chhlCoordWeight.eq_def, h0, abs_of_nonneg h0] <;> field_simp [hne'] <;> ring
  · have hne' : 1 + ε₀ ≠ 0 := fun h ↦ hne (by rw [abs_of_neg (lt_of_not_ge h0)]; linarith)
    cases c <;> simp [chhlCoordWeight.eq_def, h0, abs_of_neg (lt_of_not_ge h0)] <;>
      field_simp [hne'] <;> ring

private lemma sum_chhl_coin_eq {ε₀ : ℝ} (hε₀ : |ε₀| < 1) (ε : ℝ) (z : ι → Bool) :
    (∑ ρ : PartialAssignment ι, ∑ x : ι → Bool,
      if ρ.fill x = z then
        chhlRestrictionWeight ε₀ ρ * biasedCoinWeight (ε / (1 - |ε₀|)) x
      else 0) = biasedCoinWeight (ε₀ + ε) z := by
  set ε' : ℝ := ε / (1 - |ε₀|)
  let F : ι → Option Bool → Bool → ℝ := fun i o b ↦
    chhlCoordWeight ε₀ o * ((1 + ε' * signVal b) / 2) * (if o.getD b = z i then 1 else 0)
  have hind : ∀ (ρ : PartialAssignment ι) (x : ι → Bool),
      (if ρ.fill x = z then chhlRestrictionWeight ε₀ ρ * biasedCoinWeight ε' x else 0) =
      ∏ i : ι, F i (ρ i) (x i) := fun ρ x ↦ by
    have hprod_ind : (if ρ.fill x = z then (1 : ℝ) else 0) =
        ∏ i : ι, if (ρ i).getD (x i) = z i then 1 else 0 := by
      by_cases hz : ρ.fill x = z
      · simp only [hz, ↓reduceIte]
        exact (prod_eq_one fun i _ ↦ by simp [← hz, PartialAssignment.fill]).symm
      · have hex : ∃ i : ι, (ρ i).getD (x i) ≠ z i := by
          by_contra! hall; exact hz (funext hall)
        obtain ⟨i, hi⟩ := hex
        simp only [hz, ↓reduceIte]
        exact (prod_eq_zero (mem_univ i) (by simp [hi])).symm
    have hmul : chhlRestrictionWeight ε₀ ρ * biasedCoinWeight ε' x *
        (if ρ.fill x = z then (1 : ℝ) else 0) = ∏ i : ι, F i (ρ i) (x i) := by
      rw [hprod_ind, chhlRestrictionWeight, biasedCoinWeight_eq_prod,
        ← prod_mul_distrib, ← prod_mul_distrib]
    by_cases hz : ρ.fill x = z <;> simp only [hz, ↓reduceIte, mul_one, mul_zero] at hmul ⊢ <;>
      exact hmul
  simp_rw [hind]
  let e : (ι → Option Bool × Bool) ≃ PartialAssignment ι × (ι → Bool) :=
    ⟨fun g ↦ (fun i ↦ (g i).1, fun i ↦ (g i).2), fun p i ↦ (p.1 i, p.2 i),
      fun _ ↦ funext fun _ ↦ Prod.ext rfl rfl, fun _ ↦ Prod.ext rfl rfl⟩
  have hreidx : (∑ ρ : PartialAssignment ι, ∑ x : ι → Bool, ∏ i : ι, F i (ρ i) (x i)) =
      ∑ g : (ι → Option Bool × Bool), ∏ i : ι, F i (g i).1 (g i).2 := by
    rw [(Fintype.sum_prod_type fun p : PartialAssignment ι × (ι → Bool) ↦
      ∏ i : ι, F i (p.1 i) (p.2 i)).symm]
    exact (e.sum_comp fun p ↦ ∏ i : ι, F i (p.1 i) (p.2 i)).symm
  rw [hreidx, (Fintype.prod_sum fun i (p : Option Bool × Bool) ↦ F i p.1 p.2).symm,
    biasedCoinWeight_eq_prod]
  exact prod_congr rfl fun i _ ↦ by
    rw [Fintype.sum_prod_type]
    exact chhl_coord_sum_eq hε₀ ε (z i)

/-- **CHHL/Tal restriction decomposition**: for `|ε₀| < 1` and any `ε : ℝ`,
`biasedExpect (ε₀ + ε) f` equals
`∑ ρ, chhlRestrictionWeight ε₀ ρ * biasedExpect (ε / (1 - |ε₀|)) (f ∘ ρ.fill)`.
-/
theorem biasedExpect_add_eq_sum_chhlRestriction {ε₀ : ℝ} (hε₀ : |ε₀| < 1) (ε : ℝ)
    (f : (ι → Bool) → ℝ) :
    biasedExpect (ε₀ + ε) f =
      ∑ ρ : PartialAssignment ι,
        chhlRestrictionWeight ε₀ ρ * biasedExpect (ε / (1 - |ε₀|)) (f ∘ ρ.fill) := by
  have hpoint : ∀ (ρ : PartialAssignment ι) (x : ι → Bool),
      chhlRestrictionWeight ε₀ ρ * (biasedCoinWeight (ε / (1 - |ε₀|)) x * f (ρ.fill x)) =
      ∑ z : ι → Bool, (if ρ.fill x = z then
        chhlRestrictionWeight ε₀ ρ * biasedCoinWeight (ε / (1 - |ε₀|)) x else 0) * f z := by
    intro ρ x
    symm
    rw [sum_eq_single (ρ.fill x)]
    · simp [mul_assoc]
    · intro z _ hne; simp [hne.symm]
    · exact fun h ↦ absurd (mem_univ _) h
  symm
  simp_rw [biasedExpect_eq_sum, Function.comp_apply, mul_sum, hpoint]
  rw [sum_comm]
  conv_lhs => arg 2; ext x; rw [sum_comm]
  rw [sum_comm]
  conv_lhs => arg 2; ext z; rw [sum_comm]
  simp_rw [← sum_mul, sum_chhl_coin_eq hε₀ ε]

private lemma hasDerivAt_biasedExpect_zero (f : (ι → Bool) → ℝ) :
    HasDerivAt (fun δ ↦ biasedExpect δ f) (∑ i : ι, fourierCoeff f {i}) 0 := by
  have hsing : (∑ i : ι, fourierCoeff f {i}) = ∑ S : Finset ι with #S = 1, fourierCoeff f S := by
    refine sum_nbij (fun i ↦ ({i} : Finset ι)) (fun i _ ↦ by simp)
      (fun _ _ _ _ hij ↦ singleton_injective hij) (fun S hS ↦ ?_) (fun _ _ ↦ rfl)
    obtain ⟨i, hi⟩ := card_eq_one.mp (mem_filter.mp hS).2
    exact ⟨i, mem_univ i, hi.symm⟩
  have hfun : (fun δ ↦ biasedExpect δ f) = fun δ ↦ ∑ S : Finset ι, fourierCoeff f S * δ ^ #S :=
    funext fun δ ↦ biasedExpect_eq_sum_fourierCoeff δ f
  rw [hfun, hsing, sum_filter]
  refine HasDerivAt.fun_sum fun S _ ↦ ?_
  rcases Nat.eq_zero_or_pos #S with h0 | hpos
  · simp only [h0, pow_zero, mul_one, zero_ne_one, ↓reduceIte]
    exact hasDerivAt_const 0 (fourierCoeff f S)
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with h1 | hgt
    · simp only [← h1, pow_one, ↓reduceIte]
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (fourierCoeff f S)
    · have hne1 : #S ≠ 1 := by omega
      have hne0 : #S - 1 ≠ 0 := by omega
      simp only [hne1, ↓reduceIte]
      simpa [zero_pow hne0] using (hasDerivAt_pow #S (0 : ℝ)).const_mul (fourierCoeff f S)

private lemma hasDerivAt_biasedExpect_eq_chhl {ε₀ : ℝ} (hε₀ : |ε₀| < 1) (f : (ι → Bool) → ℝ) :
    HasDerivAt (fun x ↦ biasedExpect x f)
      ((1 - |ε₀|)⁻¹ * ∑ ρ : PartialAssignment ι,
        chhlRestrictionWeight ε₀ ρ * ∑ i : ι, fourierCoeff (f ∘ ρ.fill) {i}) ε₀ := by
  let d : ℝ := (1 - |ε₀|)⁻¹ * ∑ ρ : PartialAssignment ι,
    chhlRestrictionWeight ε₀ ρ * ∑ i : ι, fourierCoeff (f ∘ ρ.fill) {i}
  let φ : ℝ → ℝ := fun u ↦ biasedExpect (ε₀ + u) f
  have hφ : HasDerivAt φ d 0 := by
    have hφ_eq : φ = fun u ↦ ∑ ρ : PartialAssignment ι,
        chhlRestrictionWeight ε₀ ρ * biasedExpect (u / (1 - |ε₀|)) (f ∘ ρ.fill) :=
      funext fun u ↦ biasedExpect_add_eq_sum_chhlRestriction hε₀ u f
    rw [hφ_eq]
    have hsum : HasDerivAt
        (fun u ↦ ∑ ρ : PartialAssignment ι,
          chhlRestrictionWeight ε₀ ρ * biasedExpect (u / (1 - |ε₀|)) (f ∘ ρ.fill))
        (∑ ρ : PartialAssignment ι, chhlRestrictionWeight ε₀ ρ *
          ((∑ i : ι, fourierCoeff (f ∘ ρ.fill) {i}) * (1 - |ε₀|)⁻¹)) 0 := by
      refine HasDerivAt.fun_sum fun ρ _ ↦ ?_
      have hlin : HasDerivAt (fun u : ℝ ↦ u / (1 - |ε₀|)) (1 - |ε₀|)⁻¹ 0 := by
        simpa [div_eq_mul_inv] using (hasDerivAt_id (0 : ℝ)).mul_const (1 - |ε₀|)⁻¹
      have h0 : (0 : ℝ) / (1 - |ε₀|) = 0 := zero_div _
      exact ((h0 ▸ hasDerivAt_biasedExpect_zero (f ∘ ρ.fill)).comp (0 : ℝ) hlin).const_mul _
    convert hsum using 1
    simp only [d, mul_sum]
    refine sum_congr rfl fun ρ _ ↦ ?_
    rw [sum_mul, mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
  have hshift : HasDerivAt (fun x : ℝ ↦ x - ε₀) 1 ε₀ := by
    simpa [sub_eq_add_neg] using (hasDerivAt_id ε₀).add_const (-ε₀)
  have hφ0 : HasDerivAt φ d (ε₀ - ε₀) := (sub_self ε₀).symm ▸ hφ
  have hcomp : HasDerivAt (φ ∘ fun x : ℝ ↦ x - ε₀) (d * 1) ε₀ :=
    HasDerivAt.comp (𝕜 := ℝ) ε₀ hφ0 hshift
  have hfeq : (φ ∘ fun x : ℝ ↦ x - ε₀) = fun x ↦ biasedExpect x f := funext fun x ↦ by simp [φ]
  rwa [hfeq, mul_one] at hcomp

/-- **Tal's restriction-closed coin theorem**: if `ℱ` is closed under `g ∘ ρ.fill` and satisfies
`|∑ i, fourierCoeff g {i}| ≤ t` for all `g ∈ ℱ`, then every `f ∈ ℱ` and `|ε| < 1` satisfy
`coinAdvantage ε f ≤ Real.log (1 / (1 - |ε|)) * t`. -/
theorem tal_coin_bound_of_restriction_closed {ℱ : Set ((ι → Bool) → ℝ)}
    (hrest : ∀ g ∈ ℱ, ∀ ρ : PartialAssignment ι, g ∘ ρ.fill ∈ ℱ)
    {t : ℝ} (ht : ∀ g ∈ ℱ, |∑ i : ι, fourierCoeff g {i}| ≤ t)
    {f : (ι → Bool) → ℝ} (hf : f ∈ ℱ) {ε : ℝ} (hε : |ε| < 1) :
    coinAdvantage ε f ≤ Real.log (1 / (1 - |ε|)) * t := by
  have haux : ∀ {s b : ℝ}, |s| = 1 → 0 ≤ b → b < 1 →
      |biasedExpect (s * b) f - 𝔼 x, f x| ≤ Real.log (1 / (1 - b)) * t := by
    intro s b hs hb0 hb1
    let G : ℝ → ℝ := fun u ↦ biasedExpect (s * u) f - 𝔼 x, f x
    let G' : ℝ → ℝ := fun u ↦
      ((1 - |s * u|)⁻¹ * ∑ ρ : PartialAssignment ι,
        chhlRestrictionWeight (s * u) ρ * ∑ i : ι, fourierCoeff (f ∘ ρ.fill) {i}) * s
    let B : ℝ → ℝ := fun u ↦ Real.log (1 / (1 - u)) * t
    have hG_deriv : ∀ u ∈ Set.Icc (0 : ℝ) b, HasDerivAt G (G' u) u := fun u hu ↦ by
      have hsu : |s * u| < 1 := by
        rw [abs_mul, hs, one_mul, abs_of_nonneg hu.1]
        exact hu.2.trans_lt hb1
      exact ((hasDerivAt_biasedExpect_eq_chhl hsu f).comp u
        (by simpa using (hasDerivAt_id u).const_mul s)).sub_const (𝔼 x, f x)
    have hB_deriv : ∀ u ∈ Set.Icc (0 : ℝ) b, HasDerivAt B (t / (1 - u)) u := fun u hu ↦ by
      have hne : 1 - u ≠ 0 := by linarith [hu.2, hb1]
      have hsub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) u := by
        simpa [sub_eq_add_neg] using (hasDerivAt_id u).neg.const_add (1 : ℝ)
      have hlog : HasDerivAt (fun x : ℝ ↦ Real.log (1 - x)) (-(1 - u)⁻¹) u := by
        simpa [Function.comp_def, div_eq_mul_inv] using (Real.hasDerivAt_log hne).comp u hsub
      have hfun : B = fun x ↦ -Real.log (1 - x) * t :=
        funext fun _ ↦ by dsimp [B]; rw [one_div, Real.log_inv]
      rw [hfun]
      convert hlog.neg.mul_const t using 1
      ring
    have hle := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      (f := G) (f' := G') (B := B) (B' := fun u ↦ t / (1 - u)) (a := 0) (b := b)
      (fun u hu ↦ (hG_deriv u hu).continuousAt.continuousWithinAt)
      (fun u hu ↦ (hG_deriv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
      (by simp [G, B])
      (fun u hu ↦ (hB_deriv u hu).continuousAt.continuousWithinAt)
      (fun u hu ↦ (hB_deriv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
      (fun u hu ↦ by
        have hsu : |s * u| = u := by rw [abs_mul, hs, one_mul, abs_of_nonneg hu.1]
        have hpos : 0 < 1 - u := by linarith [hu.2, hb1]
        dsimp only [G']
        rw [Real.norm_eq_abs, abs_mul, hs, mul_one, hsu, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
        have hsum : |∑ ρ : PartialAssignment ι,
            chhlRestrictionWeight (s * u) ρ * ∑ i : ι, fourierCoeff (f ∘ ρ.fill) {i}| ≤ t := by
          refine (abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ ρ : PartialAssignment ι,
                |chhlRestrictionWeight (s * u) ρ * ∑ i : ι, fourierCoeff (f ∘ ρ.fill) {i}|
              ≤ ∑ ρ : PartialAssignment ι, chhlRestrictionWeight (s * u) ρ * t :=
                sum_le_sum fun ρ _ ↦ by
                  have hw := chhlRestrictionWeight_nonneg (hsu.symm ▸ (hu.2.trans hb1).le) ρ
                  rw [abs_mul, abs_of_nonneg hw]
                  exact mul_le_mul_of_nonneg_left (ht _ (hrest f hf ρ)) hw
            _ = t := by rw [← sum_mul, sum_chhlRestrictionWeight_eq_one, one_mul]
        calc (1 - u)⁻¹ * |∑ ρ : PartialAssignment ι,
              chhlRestrictionWeight (s * u) ρ * ∑ i : ι, fourierCoeff (f ∘ ρ.fill) {i}|
            ≤ (1 - u)⁻¹ * t := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpos.le)
          _ = t / (1 - u) := by ring)
      ⟨hb0, le_rfl⟩
    simpa [G, B, Real.norm_eq_abs] using hle
  rw [coinAdvantage]
  by_cases h0 : 0 ≤ ε
  · simpa [abs_of_nonneg h0] using haux (s := 1) (b := ε) (by norm_num) h0
      (by rwa [abs_of_nonneg h0] at hε)
  · have habs : |ε| = -ε := abs_of_neg (lt_of_not_ge h0)
    simpa [habs] using haux (s := -1) (b := -ε) (by norm_num) (by linarith) (habs ▸ hε)

end TalCoinTheorem

/-! ### Width-`2` Read-Once Branching Program Coin and Level-`1` Bounds -/

section WidthTwoROBP

/-- Unordered width-`w` read-once branching program sign computability. -/
def ComputableByReadOnceBP {n : ℕ} (w : ℕ) (f : (Fin n → Bool) → ℝ) : Prop :=
  ∃ (π : Equiv.Perm (Fin n)) (P : ReadOnceProgram n (Fin w) Bool),
    ∀ x : Fin n → Bool, signVal (P.eval (x ∘ π)) = f x

theorem ComputableByReadOnceBP.comp_add {n w : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ComputableByReadOnceBP w f) (σ : Fin n → Bool) :
    ComputableByReadOnceBP w (fun x ↦ f (x + σ)) := by
  obtain ⟨π, P, hP⟩ := hf
  let P' : ReadOnceProgram n (Fin w) Bool :=
    ⟨P.start, fun i s b ↦ P.step i s (b ^^ σ (π i)), P.accept⟩
  refine ⟨π, P', fun x ↦ ?_⟩
  have hstate : P'.finalState (x ∘ π) = P.finalState ((x + σ) ∘ π) := by
    simp only [P', ReadOnceProgram.finalState, Function.comp_apply, Pi.add_apply, Bool.add_eq_xor]
  rw [ReadOnceProgram.eval, hstate]
  exact hP (x + σ)

private lemma biasedExpect_mul_coord_of_update_inv {n : ℕ} (ε : ℝ) (i₀ : Fin n)
    {g : (Fin n → Bool) → ℝ} (hg : ∀ x, g (Function.update x i₀ (!x i₀)) = g x)
    (h : Bool → ℝ) :
    biasedExpect ε (fun x ↦ g x * h (x i₀)) =
      (((1 + ε) / 2) * h false + ((1 - ε) / 2) * h true) * biasedExpect ε g := by
  set c : ℝ := ((1 + ε) / 2) * h false + ((1 - ε) / 2) * h true
  let flip : (Fin n → Bool) ≃ (Fin n → Bool) :=
    ⟨fun x ↦ Function.update x i₀ (!x i₀), fun x ↦ Function.update x i₀ (!x i₀),
      fun x ↦ by ext j; by_cases hj : j = i₀ <;> simp [hj],
      fun x ↦ by ext j; by_cases hj : j = i₀ <;> simp [hj]⟩
  let wrest : (Fin n → Bool) → ℝ := fun x ↦ ∏ j ∈ univ.erase i₀, (1 + ε * signVal (x j)) / 2
  have hwfactor : ∀ x : Fin n → Bool,
      biasedCoinWeight ε x = ((1 + ε * signVal (x i₀)) / 2) * wrest x := fun x ↦ by
    rw [biasedCoinWeight_eq_prod]
    exact (mul_prod_erase univ _ (mem_univ i₀)).symm
  have hwrest_flip : ∀ x : Fin n → Bool, wrest (flip x) = wrest x := fun x ↦
    prod_congr rfl fun j hj ↦ by simp [flip, (mem_erase.mp hj).1]
  have hpair : ∀ x : Fin n → Bool,
      biasedCoinWeight ε x * (g x * h (x i₀)) +
        biasedCoinWeight ε (flip x) * (g (flip x) * h (flip x i₀)) =
      c * (biasedCoinWeight ε x * g x + biasedCoinWeight ε (flip x) * g (flip x)) := fun x ↦ by
    have hg_flip : g (flip x) = g x := hg x
    have hflip_at : flip x i₀ = !x i₀ := by simp [flip]
    rw [hwfactor x, hwfactor (flip x), hwrest_flip x, hg_flip, hflip_at]
    cases x i₀ <;> norm_num [c, signVal] <;> ring
  have hsumL := flip.sum_comp (fun x ↦ biasedCoinWeight ε x * (g x * h (x i₀)))
  have hsumR := flip.sum_comp (fun x ↦ biasedCoinWeight ε x * g x)
  have h2 := sum_congr (s₁ := univ) (s₂ := univ) rfl fun x _ ↦ hpair x
  simp only [sum_add_distrib, ← mul_sum] at h2
  rw [hsumL, hsumR, mul_add] at h2
  rw [biasedExpect_eq_sum, biasedExpect_eq_sum]
  linarith [h2]

private def prefixState {n w : ℕ} (π : Equiv.Perm (Fin n)) (P : ReadOnceProgram n (Fin w) Bool)
    (x : Fin n → Bool) (k : ℕ) (hk : k ≤ n) : Fin w :=
  Fin.foldl k (fun q (j : Fin k) ↦ P.step (j.castLE hk) q (x (π (j.castLE hk)))) P.start

private lemma prefixState_succ {n w : ℕ} (π : Equiv.Perm (Fin n))
    (P : ReadOnceProgram n (Fin w) Bool) (x : Fin n → Bool) {m : ℕ} (hm : m + 1 ≤ n) :
    prefixState π P x (m + 1) hm =
      P.step ⟨m, hm⟩ (prefixState π P x m (Nat.le_of_succ_le hm)) (x (π ⟨m, hm⟩)) := by
  rw [prefixState, Fin.foldl_succ_last]
  rfl

private lemma prefixState_update_ge {n w : ℕ} (π : Equiv.Perm (Fin n))
    (P : ReadOnceProgram n (Fin w) Bool) (x : Fin n → Bool) {k m : ℕ} (hk : k ≤ m) (hm : m < n)
    (b : Bool) :
    prefixState π P (Function.update x (π ⟨m, hm⟩) b) k (hk.trans hm.le) =
      prefixState π P x k (hk.trans hm.le) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    have hjm : j < m := Nat.lt_of_succ_le hk
    have hne : π ⟨j, hjm.trans hm⟩ ≠ π ⟨m, hm⟩ := fun heq ↦ by
      have hval : j = m := congrArg Fin.val (π.injective heq)
      omega
    rw [prefixState_succ, prefixState_succ, ih hjm.le, Function.update_of_ne hne]

private def stepZeroInd (a b : Fin 2) (bit : Bool) : ℝ :=
  if (if bit then b else a) = 0 then 1 else 0

private lemma width_two_markov_step {p q ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hε0 : 0 ≤ ε) (hd : |p - q| ≤ ε) (a0 b0 a1 b1 : Fin 2) :
    |((((1 + ε) / 2) * stepZeroInd a0 b0 false + ((1 - ε) / 2) * stepZeroInd a0 b0 true) * p +
      (((1 + ε) / 2) * stepZeroInd a1 b1 false + ((1 - ε) / 2) * stepZeroInd a1 b1 true) *
        (1 - p)) -
      (((stepZeroInd a0 b0 false + stepZeroInd a0 b0 true) / 2) * q +
        ((stepZeroInd a1 b1 false + stepZeroInd a1 b1 true) / 2) * (1 - q))| ≤ ε := by
  have hd' := abs_le.mp hd
  have hmul0 : 0 ≤ ε * p := mul_nonneg hε0 hp0
  have hmul1 : ε * p ≤ ε := mul_le_of_le_one_right hε0 hp1
  rw [abs_le]
  fin_cases a0 <;> fin_cases b0 <;> fin_cases a1 <;> fin_cases b1 <;>
    norm_num [stepZeroInd] <;> (try constructor) <;> linarith

private lemma width_two_state_zero_diff_le {n : ℕ} (π : Equiv.Perm (Fin n))
    (P : ReadOnceProgram n (Fin 2) Bool) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (k : ℕ)
    (hk : k ≤ n) :
    |biasedExpect ε (fun x ↦ if prefixState π P x k hk = 0 then (1 : ℝ) else 0) -
      biasedExpect 0 (fun x ↦ if prefixState π P x k hk = 0 then (1 : ℝ) else 0)| ≤ ε := by
  induction k with
  | zero =>
    have hconst : (fun x : Fin n → Bool ↦ if prefixState π P x 0 hk = 0 then (1 : ℝ) else 0) =
        fun _ ↦ if P.start = 0 then 1 else 0 := funext fun _ ↦ rfl
    rw [hconst, biasedExpect_const, biasedExpect_const, sub_self, abs_zero]
    exact hε0
  | succ m ih =>
    have hm : m < n := hk
    let ind : (Fin n → Bool) → ℝ := fun x ↦ if prefixState π P x m hm.le = 0 then 1 else 0
    have hp0 : 0 ≤ biasedExpect ε ind := by
      simpa only [biasedExpect, bernoulliAverage_const] using
        bernoulliAverage_mono (p := (1 - ε) / 2) (by linarith) (by linarith) (f := fun _ ↦ 0)
          fun x ↦ by dsimp [ind]; split_ifs <;> norm_num
    have hp1 : biasedExpect ε ind ≤ 1 := by
      simpa only [biasedExpect, bernoulliAverage_const] using
        bernoulliAverage_mono (p := (1 - ε) / 2) (by linarith) (by linarith) (g := fun _ ↦ 1)
          fun x ↦ by dsimp [ind]; split_ifs <;> norm_num
    let a0 := P.step ⟨m, hm⟩ 0 false
    let b0 := P.step ⟨m, hm⟩ 0 true
    let a1 := P.step ⟨m, hm⟩ 1 false
    let b1 := P.step ⟨m, hm⟩ 1 true
    let c0 : Bool → ℝ := stepZeroInd a0 b0
    let c1 : Bool → ℝ := stepZeroInd a1 b1
    have hpt : ∀ x : Fin n → Bool,
        (if prefixState π P x (m + 1) hk = 0 then (1 : ℝ) else 0) =
          ind x * c0 (x (π ⟨m, hm⟩)) + (1 - ind x) * c1 (x (π ⟨m, hm⟩)) := fun x ↦ by
      rw [prefixState_succ]
      rcases Fin.exists_fin_two.mp ⟨prefixState π P x m hm.le, rfl⟩ with hq | hq
      · rw [show ind x = 1 from ite_eq_left hq, hq]
        cases x (π ⟨m, hm⟩) <;> simp [c0, stepZeroInd, a0, b0]
      · rw [show ind x = 0 from ite_eq_right (by rw [hq]; decide), hq]
        cases x (π ⟨m, hm⟩) <;> simp [c1, stepZeroInd, a1, b1]
    have hinv0 : ∀ x : Fin n → Bool,
        ind (Function.update x (π ⟨m, hm⟩) (!x (π ⟨m, hm⟩))) = ind x := fun x ↦ by
      dsimp [ind]
      rw [prefixState_update_ge π P x le_rfl hm]
    have hinv1 : ∀ x : Fin n → Bool,
        1 - ind (Function.update x (π ⟨m, hm⟩) (!x (π ⟨m, hm⟩))) = 1 - ind x :=
      fun x ↦ by rw [hinv0 x]
    have hexp : ∀ δ : ℝ,
        biasedExpect δ (fun x ↦ if prefixState π P x (m + 1) hk = 0 then (1 : ℝ) else 0) =
          (((1 + δ) / 2) * c0 false + ((1 - δ) / 2) * c0 true) * biasedExpect δ ind +
            (((1 + δ) / 2) * c1 false + ((1 - δ) / 2) * c1 true) * (1 - biasedExpect δ ind) :=
      fun δ ↦ by
        have hsub : biasedExpect δ (fun x ↦ 1 - ind x) = 1 - biasedExpect δ ind := by
          rw [biasedExpect, bernoulliAverage_sub, bernoulliAverage_const, ← biasedExpect]
        rw [congrArg (biasedExpect δ) (funext hpt), biasedExpect, bernoulliAverage_add,
          ← biasedExpect, ← biasedExpect,
          biasedExpect_mul_coord_of_update_inv δ (π ⟨m, hm⟩) hinv0 c0,
          biasedExpect_mul_coord_of_update_inv δ (π ⟨m, hm⟩) hinv1 c1, hsub]
    rw [hexp ε, hexp 0,
      show ((1 + (0 : ℝ)) / 2) * c0 false + ((1 - (0 : ℝ)) / 2) * c0 true =
        (c0 false + c0 true) / 2 by ring,
      show ((1 + (0 : ℝ)) / 2) * c1 false + ((1 - (0 : ℝ)) / 2) * c1 true =
        (c1 false + c1 true) / 2 by ring]
    exact width_two_markov_step hp0 hp1 hε0 (ih hm.le) a0 b0 a1 b1

/-- **Width-`2` ROBP coin theorem**: every `f` computable in sign semantics by a width-`2` read-once
branching program satisfies `coinAdvantage ε f ≤ 2 * |ε|` for all `|ε| ≤ 1`. -/
theorem readOnceBP_coin_bound_two {n : ℕ} {ε : ℝ} {f : (Fin n → Bool) → ℝ}
    (hε : |ε| ≤ 1) (hf : ComputableByReadOnceBP 2 f) :
    coinAdvantage ε f ≤ 2 * |ε| := by
  have hnonneg : ∀ {δ : ℝ} {g : (Fin n → Bool) → ℝ}, 0 ≤ δ → δ ≤ 1 →
      ComputableByReadOnceBP 2 g → |biasedExpect δ g - 𝔼 x, g x| ≤ 2 * δ := by
    intro δ g hδ0 hδ1 ⟨π, P, hP⟩
    let ind : (Fin n → Bool) → ℝ := fun x ↦ if prefixState π P x n le_rfl = 0 then 1 else 0
    have hpt : ∀ x : Fin n → Bool,
        g x = (signVal (P.accept 0) - signVal (P.accept 1)) * ind x + signVal (P.accept 1) :=
      fun x ↦ by
        rw [← hP x, ReadOnceProgram.eval]
        change signVal (P.accept (prefixState π P x n le_rfl)) = _
        rcases Fin.exists_fin_two.mp ⟨prefixState π P x n le_rfl, rfl⟩ with hq | hq
        · rw [hq, show ind x = 1 from ite_eq_left hq]; ring
        · rw [hq, show ind x = 0 from ite_eq_right (by rw [hq]; decide)]; ring
    let dacc := signVal (P.accept 0) - signVal (P.accept 1)
    have hexp : ∀ η : ℝ, biasedExpect η g = dacc * biasedExpect η ind + signVal (P.accept 1) :=
      fun η ↦ by
        rw [congrArg (biasedExpect η) (funext hpt), biasedExpect, bernoulliAverage_add,
          bernoulliAverage_const_mul, bernoulliAverage_const, ← biasedExpect]
    rw [← biasedExpect_zero g, hexp δ, hexp 0,
      show dacc * biasedExpect δ ind + signVal (P.accept 1) -
        (dacc * biasedExpect 0 ind + signVal (P.accept 1)) =
        dacc * (biasedExpect δ ind - biasedExpect 0 ind) by ring, abs_mul]
    have habs_acc : |dacc| ≤ 2 := by
      dsimp only [dacc]
      cases P.accept 0 <;> cases P.accept 1 <;> norm_num
    exact mul_le_mul habs_acc (width_two_state_zero_diff_le π P hδ0 hδ1 n le_rfl) (abs_nonneg _)
      zero_le_two
  rw [coinAdvantage]
  by_cases hε0 : 0 ≤ ε
  · rw [abs_of_nonneg hε0]
    exact hnonneg hε0 (abs_le.mp hε).2 hf
  · have hexp_add : (𝔼 x : Fin n → Bool, f (x + fun _ ↦ true)) = 𝔼 x, f x := by
      rw [← fourierCoeff_empty (fun x ↦ f (x + fun _ ↦ true)), fourierCoeff_comp_add, chi_empty,
        one_mul, fourierCoeff_empty]
    rw [abs_of_neg (lt_of_not_ge hε0), ← neg_neg ε, biasedExpect_neg_eq_comp_not (-ε) f, neg_neg,
      ← hexp_add]
    exact hnonneg (by linarith) (by linarith [(abs_le.mp hε).1]) (hf.comp_add (fun _ ↦ true))

/-- **Width-`2` ROBP level-`1` Fourier bound**: any `f` computable in sign semantics by a width-`2`
read-once branching program satisfies `levelL1Norm 1 f ≤ 2`. -/
theorem levelOneNorm_le_two_of_computableByReadOnceBP_two {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ComputableByReadOnceBP 2 f) : levelL1Norm 1 f ≤ 2 := by
  let σ : Fin n → Bool := fun i ↦ decide (fourierCoeff f {i} < 0)
  let g := fun x : Fin n → Bool ↦ f (x + σ)
  have hg : ComputableByReadOnceBP 2 g := hf.comp_add σ
  have hσ : ∀ i : Fin n, fourierCoeff g {i} = |fourierCoeff f {i}| := fun i ↦ by
    dsimp [g, σ]
    rw [fourierCoeff_comp_add, chi_singleton]
    by_cases hneg : fourierCoeff f {i} < 0
    · simp [hneg, abs_of_neg hneg]
    · simp [hneg, abs_of_nonneg (le_of_not_gt hneg)]
  have hg_bdd : ∀ x : Fin n → Bool, |g x| ≤ 1 := fun x ↦ by
    obtain ⟨π, P, hP⟩ := hg
    rw [← hP x, abs_signVal]
  have hl1 : ∑ i : Fin n, fourierCoeff g {i} = levelL1Norm 1 f := by
    rw [levelL1Norm]
    refine sum_nbij (fun i : Fin n ↦ ({i} : Finset (Fin n))) (fun i _ ↦ by simp)
      (fun _ _ _ _ hij ↦ singleton_injective hij) (fun S hS ↦ ?_) (fun i _ ↦ hσ i)
    obtain ⟨i, hi⟩ := card_eq_one.mp (mem_filter.mp hS).2
    exact ⟨i, mem_univ i, hi.symm⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [← hl1]
    simp
  · by_contra! hgt
    let δ := levelL1Norm 1 f - 2
    have hδ : 0 < δ := sub_pos.mpr hgt
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    let ε := min (1 / (n : ℝ)) (δ / (2 * (n : ℝ)))
    have hε0 : 0 < ε := lt_min (by positivity) (div_pos hδ (by positivity))
    have hε_inv : ε ≤ 1 / (n : ℝ) := min_le_left _ _
    have hε1 : |ε| ≤ 1 := by
      rw [abs_of_pos hε0]
      exact hε_inv.trans (div_le_one_of_le₀ (Nat.one_le_cast.mpr hn) hn_pos.le)
    have hsq : (Fintype.card (Fin n) : ℝ) * ε ^ 2 ≤ 1 := by
      rw [Fintype.card_fin]
      have hmul : (n : ℝ) * ε ≤ 1 := by
        calc (n : ℝ) * ε ≤ (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hε_inv hn_pos.le
          _ = 1 := by field_simp [hn_pos.ne']
      have hε_le1 : ε ≤ 1 := (abs_le.mp hε1).2
      nlinarith
    have hvar :
        Real.sqrt ((𝔼 x, (g x - 𝔼 y, g y) ^ 2) - ∑ i : Fin n, fourierCoeff g {i} ^ 2) ≤ 1 := by
      refine (Real.sqrt_le_sqrt ?_).trans_eq Real.sqrt_one
      have hsum0 : 0 ≤ ∑ i : Fin n, fourierCoeff g {i} ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
      have hexp2 : 𝔼 x, g x ^ 2 ≤ 1 := by
        refine (expect_le_expect fun x _ ↦ ?_).trans_eq (expect_const univ_nonempty 1)
        rw [← sq_abs (g x)]
        exact (pow_le_pow_left₀ (abs_nonneg _) (hg_bdd x) 2).trans_eq (one_pow 2)
      have hv : 𝔼 x, (g x - 𝔼 y, g y) ^ 2 ≤ 1 := by
        have hpt : (fun x ↦ (g x - 𝔼 y, g y) ^ 2) =
            fun x ↦ g x ^ 2 - 2 * (𝔼 y, g y) * g x + (𝔼 y, g y) ^ 2 := funext fun _ ↦ by ring
        rw [hpt, expect_add_distrib, expect_sub_distrib, ← mul_expect, expect_const univ_nonempty]
        linarith [sq_nonneg (𝔼 y, g y)]
      linarith
    have herr := (abs_div_biasedExpect_sub_sum_singleton_le_high_var hε0.ne' hsq g).trans
      ((mul_le_mul_of_nonneg_left hvar (by positivity)).trans_eq (mul_one _))
    rw [Fintype.card_fin, abs_of_pos hε0, hl1] at herr
    have hcoin := readOnceBP_coin_bound_two hε1 hg
    rw [coinAdvantage, abs_of_pos hε0] at hcoin
    have hquot : |(biasedExpect ε g - 𝔼 x, g x) / ε| ≤ 2 := by
      rw [abs_div, abs_of_pos hε0, div_le_iff₀ hε0]
      exact hcoin
    have htri : levelL1Norm 1 f ≤ 2 + ε * (n : ℝ) := by
      linarith [(abs_le.mp herr).1, le_abs_self ((biasedExpect ε g - 𝔼 x, g x) / ε)]
    have hεn : ε * (n : ℝ) ≤ δ / 2 := by
      calc ε * (n : ℝ) ≤ (δ / (2 * (n : ℝ))) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hn_pos.le
        _ = δ / 2 := by field_simp [hn_pos.ne']
    linarith

end WidthTwoROBP

end CslibFrontier.BooleanAnalysis
