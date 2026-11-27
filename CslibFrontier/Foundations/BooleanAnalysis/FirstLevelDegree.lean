/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Foundations.BooleanAnalysis.FourierMeasures

import CslibFrontier.Foundations.BooleanAnalysis.LowDegreePhase
import CslibFrontier.Foundations.Data.BitString.Weight
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Level-1 Fourier Growth of Low-Degree `𝔽₂`-Polynomials

This module proves the level-1 Fourier growth inequality of Chattopadhyay, Hatami, Lovett, and Tal
 and its Boolean-weight-sensitive refinement under standard Lean axioms:

* for every Boolean function `f : (ι → Bool) → Bool`,
  `∑ i : ι, |f̂({i})| ≤ 4 * deg_{𝔽₂}(f)`;
* for every Boolean function `f : (ι → Bool) → Bool`,
  `∑ i : ι, |f̂({i})| ≤ 32 * δ(f) * deg_{𝔽₂}(f)`;
* by invariance of `deg_{𝔽₂}(f)` and `δ(f)` under invertible Fourier basis changes, both bounds hold
  for the sum `∑ S ∈ ℬ, |f̂(S)|` over any `𝔽₂`-linearly independent family `ℬ` of characters, and in
  particular yield `∑ S ∈ ℬ, |f̂(S)| ≤ 4 log₂ k(f)` and `∑ S ∈ ℬ, |f̂(S)| ≤ 32 δ(f) log₂ k(f)` when
  `k(f) > 1`.

## Main results

* `CslibFrontier.BooleanFunction.sum_abs_boolFourierCoeff_singleton_le_four_mul_f2Degree`:
  `∑ i, |f̂({i})| ≤ 4 * deg_{𝔽₂}(f)`.
* `CslibFrontier.BooleanFunction.sum_abs_boolFourierCoeff_linearIndep_le_four_mul_f2Degree`:
  basis generalization `∑ S ∈ ℬ, |f̂(S)| ≤ 4 * deg_{𝔽₂}(f)`.
* `CslibFrontier.BooleanFunction.sum_abs_boolFourierCoeff_linearIndep_le_four_mul_logb`:
  `∑ S ∈ ℬ, |f̂(S)| ≤ 4 * log₂ k(f)` for `k(f) > 1`.
* `CslibFrontier.BooleanFunction.sum_abs_boolFourierCoeff_singleton_le_mul_weight_f2Degree`:
  `∑ i, |f̂({i})| ≤ 32 * δ(f) * deg_{𝔽₂}(f)`.
* `CslibFrontier.BooleanFunction.sum_abs_boolFourierCoeff_linearIndep_le_mul_weight_f2Degree`:
  `∑ S ∈ ℬ, |f̂(S)| ≤ 32 * δ(f) * deg_{𝔽₂}(f)`.
* `CslibFrontier.BooleanFunction.sum_abs_boolFourierCoeff_linearIndep_le_mul_weight_logb`:
  `∑ S ∈ ℬ, |f̂(S)| ≤ 32 * δ(f) * log₂ k(f)` for `k(f) > 1`.
-/

public section

namespace CslibFrontier.BooleanFunction

open Cslib Cslib.BitString Finset
open scoped BigOperators

section LowWeightInterpolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def trueSet (x : ι → Bool) : Finset ι :=
  univ.filter fun i ↦ x i = true

omit [DecidableEq ι] in
private theorem card_trueSet (x : ι → Bool) : #(trueSet x) = weight x :=
  rfl

omit [DecidableEq ι] in
private theorem trueSet_injective : Function.Injective (trueSet (ι := ι)) := by
  intro x y h
  ext i
  have hi := Finset.ext_iff.1 h i
  simp only [trueSet, mem_filter, mem_univ, true_and] at hi
  cases hx : x i <;> cases hy : y i <;> simp_all

omit [DecidableEq ι] in
private theorem weight_not_add_weight (x : ι → Bool) :
    weight (fun i ↦ !x i) + weight x = Fintype.card ι := by
  have hpart := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i ↦ x i = true)
  have heq : (univ.filter fun i : ι ↦ (!x i) = true) = (univ.filter fun i : ι ↦ ¬x i = true) := by
    ext i; simp
  change #(univ.filter fun i : ι ↦ (!x i) = true) + #(univ.filter fun i : ι ↦ x i = true) = _
  rw [heq, add_comm, hpart, card_univ]

/-- Point indicator on `{x : weight x ≤ H}`: for any `S : Finset ι` with `#S ≤ H`, there is a
polynomial `q ∈ lowDegree (ZMod 2) ι H` satisfying `q x = if trueSet x = S then 1 else 0` for all
`x` with `weight x ≤ H`. -/
private theorem exists_lowWeight_indicator (H : ℕ) (S : Finset ι) (hS : #S ≤ H) :
    ∃ q ∈ lowDegree (ZMod 2) ι H, ∀ x : ι → Bool, weight x ≤ H →
      q x = if trueSet x = S then 1 else 0 := by
  suffices hgen : ∀ r : ℕ, ∀ T : Finset ι, #T ≤ H → H - #T ≤ r →
      ∃ q ∈ lowDegree (ZMod 2) ι H, ∀ x : ι → Bool, weight x ≤ H →
        q x = if trueSet x = T then 1 else 0 from
    hgen (H - #S) S hS le_rfl
  intro r
  induction r with
  | zero =>
    intro T hT hr
    have hcard : #T = H := by omega
    refine ⟨monomial (ZMod 2) T, monomial_mem_lowDegree hT, fun x hx ↦ ?_⟩
    rw [monomial_apply]
    have hiff : (∀ i ∈ T, x i = true) ↔ trueSet x = T := by
      constructor
      · intro hall
        have hsub : T ⊆ trueSet x := fun i hi ↦ mem_filter.2 ⟨mem_univ i, hall i hi⟩
        exact (eq_of_subset_of_card_le hsub (by rw [card_trueSet, hcard]; exact hx)).symm
      · rintro rfl i hi
        exact (mem_filter.1 hi).2
    by_cases h : trueSet x = T <;> simp [hiff, h]
  | succ r ih =>
    intro T hT hr
    by_cases hle : H - #T ≤ r
    · exact ih T hT hle
    let supers : Finset (Finset ι) := univ.filter fun U ↦ T ⊂ U ∧ #U ≤ H
    have hsup : ∀ U : supers, ∃ qU ∈ lowDegree (ZMod 2) ι H,
        ∀ x : ι → Bool, weight x ≤ H → qU x = if trueSet x = U.1 then 1 else 0 := by
      intro U
      obtain ⟨hTU, hUH⟩ := (mem_filter.1 U.2).2
      have hlt : #T < #U.1 := card_lt_card hTU
      exact ih U.1 hUH (by omega)
    choose qU hqU_mem hqU_val using hsup
    refine ⟨monomial (ZMod 2) T - ∑ U : supers, qU U,
      Submodule.sub_mem _ (monomial_mem_lowDegree hT) (Submodule.sum_mem _ fun U _ ↦ hqU_mem U),
      fun x hx ↦ ?_⟩
    simp only [Pi.sub_apply, Finset.sum_apply, monomial_apply]
    have hsum_val : (∑ U : supers, qU U x) = if T ⊂ trueSet x then 1 else 0 := by
      simp_rw [hqU_val _ x hx]
      by_cases hss : T ⊂ trueSet x
      · have hmem : trueSet x ∈ supers := mem_filter.2 ⟨mem_univ _, hss, hx⟩
        rw [ite_eq_left hss]
        refine (sum_eq_single ⟨trueSet x, hmem⟩
          (fun U _ hne ↦ ite_eq_right fun heq ↦ hne (Subtype.ext heq.symm))
            (by simp)).trans (ite_eq_left rfl)
      · rw [ite_eq_right hss]
        exact sum_eq_zero fun U _ ↦
          ite_eq_right fun heq ↦ hss (by rw [heq]; exact (mem_filter.1 U.2).2.1)
    rw [hsum_val]
    have hsub_iff : (∀ i ∈ T, x i = true) ↔ T ⊆ trueSet x := by
      simp [trueSet, subset_iff]
    by_cases heq : trueSet x = T
    · have hsub : ∀ i ∈ T, x i = true := hsub_iff.2 (by rw [heq])
      have hnss : ¬T ⊂ trueSet x := by simp [heq]
      rw [ite_eq_left hsub, ite_eq_right hnss, ite_eq_left heq, sub_zero]
    · by_cases hsub : T ⊆ trueSet x
      · have hall : ∀ i ∈ T, x i = true := hsub_iff.2 hsub
        have hss : T ⊂ trueSet x := Finset.ssubset_iff_subset_ne.2 ⟨hsub, Ne.symm heq⟩
        rw [ite_eq_left hall, ite_eq_left hss, ite_eq_right heq, sub_self]
      · have hnall : ¬∀ i ∈ T, x i = true := mt hsub_iff.1 hsub
        have hnss : ¬T ⊂ trueSet x := fun h ↦ hsub h.subset
        rw [ite_eq_right hnall, ite_eq_right hnss, ite_eq_right heq, sub_zero]

omit [DecidableEq ι] in
/-- Every `𝔽₂`-valued function agrees on `{x : weight x ≤ H}` with a polynomial in
`lowDegree (ZMod 2) ι H`. -/
private theorem exists_mem_lowDegree_agree_of_weight_le (H : ℕ) (g : (ι → Bool) → ZMod 2) :
    ∃ q ∈ lowDegree (ZMod 2) ι H, ∀ x : ι → Bool, weight x ≤ H → q x = g x := by
  classical
  let lowPts : Finset (ι → Bool) := univ.filter fun y ↦ weight y ≤ H
  have hind : ∀ y : lowPts, ∃ qy ∈ lowDegree (ZMod 2) ι H,
      ∀ x : ι → Bool, weight x ≤ H → qy x = if x = y.1 then 1 else 0 := by
    intro y
    have hy : #(trueSet y.1) ≤ H := (mem_filter.1 y.2).2
    obtain ⟨qy, hqy_mem, hqy_val⟩ := exists_lowWeight_indicator H (trueSet y.1) hy
    refine ⟨qy, hqy_mem, fun x hx ↦ ?_⟩
    rw [hqy_val x hx]
    simp [trueSet_injective.eq_iff]
  choose qy hqy_mem hqy_val using hind
  refine ⟨∑ y : lowPts, g y.1 • qy y,
    Submodule.sum_mem _ fun y _ ↦ Submodule.smul_mem _ _ (hqy_mem y),
    fun x hx ↦ ?_⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hqy_val _ x hx]
  have hxmem : x ∈ lowPts := mem_filter.2 ⟨mem_univ x, hx⟩
  refine (sum_eq_single ⟨x, hxmem⟩
    (fun y _ hne ↦ by simp [show x ≠ y.1 from fun h ↦ hne (Subtype.ext h.symm)])
    (by simp)).trans ?_
  simp

omit [DecidableEq ι] in
/-- Every `𝔽₂`-valued function agrees on `{x : |ι| ≤ weight x + H}` with a polynomial in
`lowDegree (ZMod 2) ι H`. -/
private theorem exists_mem_lowDegree_agree_of_le_weight (H : ℕ) (g : (ι → Bool) → ZMod 2) :
    ∃ q ∈ lowDegree (ZMod 2) ι H,
      ∀ x : ι → Bool, Fintype.card ι ≤ weight x + H → q x = g x := by
  obtain ⟨q₀, hq₀_mem, hq₀_val⟩ :=
    exists_mem_lowDegree_agree_of_weight_le H (fun x ↦ g fun i ↦ !x i)
  refine ⟨fun x ↦ q₀ fun i ↦ !x i, comp_not_mem_lowDegree hq₀_mem, fun x hx ↦ ?_⟩
  have hwt := weight_not_add_weight x
  dsimp only
  rw [hq₀_val (fun i ↦ !x i) (by omega)]
  congr 1
  ext i
  simp

omit [Fintype ι] [DecidableEq ι] in
/-- Coordinatewise XOR flipping `x ↦ fun i ↦ x i ^^ a i` preserves `lowDegree (ZMod 2) ι D`. -/
private theorem comp_xor_mem_lowDegree {D : ℕ} {p : (ι → Bool) → ZMod 2}
    (hp : p ∈ lowDegree (ZMod 2) ι D) (a : ι → Bool) :
    (fun x ↦ p (x + a)) ∈ lowDegree (ZMod 2) ι D := by
  classical
  refine Submodule.span_induction ?_ (Submodule.zero_mem _)
    (fun _ _ _ _ hf hg ↦ Submodule.add_mem _ hf hg)
    (fun c _ _ hf ↦ Submodule.smul_mem _ c hf) hp
  rintro _ ⟨S, hS, rfl⟩
  have hfun : (fun x : ι → Bool ↦ monomial (ZMod 2) S (x + a)) =
      ∑ T ∈ S.powerset, monomial (ZMod 2) (S \ T) a • monomial (ZMod 2) T := by
    ext x
    have hprod : ∀ (U : Finset ι) (y : ι → Bool),
        monomial (ZMod 2) U y = ∏ i ∈ U, bitVal (ZMod 2) (y i) := fun U y ↦ by
      rw [monomial_apply]
      by_cases hall : ∀ i ∈ U, y i = true
      · rw [ite_eq_left hall]
        symm
        exact prod_eq_one fun i hi ↦ by simp [hall i hi, bitVal]
      · rw [ite_eq_right hall]
        push Not at hall
        obtain ⟨i, hi, hne⟩ := hall
        symm
        exact prod_eq_zero hi (by cases hy : y i <;> simp_all [bitVal])
    have hbit : ∀ i : ι,
        bitVal (ZMod 2) ((x + a) i) = bitVal (ZMod 2) (x i) + bitVal (ZMod 2) (a i) := fun i ↦ by
      change bitVal (ZMod 2) (x i ^^ a i) = _
      cases x i <;> cases a i <;> decide
    rw [hprod, prod_congr rfl fun i _ ↦ hbit i, prod_add, Finset.sum_apply]
    refine sum_congr rfl fun T _ ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul, hprod, hprod, mul_comm]
  rw [hfun]
  refine Submodule.sum_mem _ fun T hT ↦ Submodule.smul_mem _ _ (monomial_mem_lowDegree ?_)
  exact (card_le_card (mem_powerset.1 hT)).trans hS

/-- **Chattopadhyay–Hatami–Lovett–Tal** on even-dimensional cubes (`|ι| = 2 m`):
`∑ i, |f̂({i})| ≤ 4 * deg_{𝔽₂}(f)`.
-/
private theorem sum_abs_singleton_le_four_mul_f2Degree_even {m : ℕ}
    (hcard : Fintype.card ι = 2 * m) (f : (ι → Bool) → Bool) :
    ∑ i : ι, |boolFourierCoeff f {i}| ≤ 4 * (f2Degree f : ℝ) := by
  -- Flip input coordinates where f̂({i}) < 0 so every singleton coefficient is nonnegative.
  let a : ι → Bool := fun i ↦ decide (boolFourierCoeff f {i} < 0)
  let g : (ι → Bool) → Bool := fun x ↦ f (x + a)
  set d : ℕ := f2Degree f
  let p : (ι → Bool) → ZMod 2 := fun x ↦ bitVal (ZMod 2) (g x)
  have hp_deg : p ∈ lowDegree (ZMod 2) ι d :=
    comp_xor_mem_lowDegree (mem_lowDegree_totalDegree fun x ↦ bitVal (ZMod 2) (f x)) a
  have hsum_eq : ∑ i : ι, |boolFourierCoeff f {i}| = ∑ i : ι, boolFourierCoeff g {i} := by
    refine sum_congr rfl fun i _ ↦ ?_
    have hcomp := fourierCoeff_comp_add (fun x ↦ signVal (f x)) a {i}
    rw [chi_singleton] at hcomp
    change |boolFourierCoeff f {i}| = fourierCoeff (fun x ↦ signVal (f (x + a))) {i}
    rw [hcomp]
    change |boolFourierCoeff f {i}| = signVal (a i) * boolFourierCoeff f {i}
    by_cases hneg : boolFourierCoeff f {i} < 0
    · have hai : a i = true := decide_eq_true hneg
      rw [hai, abs_of_neg hneg]
      simp [signVal]
    · have hai : a i = false := decide_eq_false hneg
      rw [hai, abs_of_nonneg (le_of_not_gt hneg)]
      simp [signVal]
  -- Decompose ∑ i, signVal (x i) = 2 (m - weight x) = 2 ∑_{t=1}^m T_t(x).
  let Tfun : ℕ → (ι → Bool) → ℝ := fun t x ↦
    if weight x + t ≤ m then 1 else if m + t ≤ weight x then -1 else 0
  have hsign_sum : ∀ x : ι → Bool,
      ∑ i : ι, signVal (x i) = 2 * ∑ t ∈ Icc 1 m, Tfun t x := by
    intro x
    have h1 : ∑ i : ι, signVal (x i) = (2 * m : ℝ) - 2 * (weight x : ℝ) := by
      simp_rw [signVal_eq_one_sub_two_mul_bitVal, sum_sub_distrib, ← mul_sum]
      have hwt : ∑ i : ι, bitVal ℝ (x i) = (weight x : ℝ) := by
        change ∑ i : ι, bitVal ℝ (x i) = (#{i : ι | x i = true} : ℝ)
        rw [card_filter, Nat.cast_sum]
        refine sum_congr rfl fun i _ ↦ by cases x i <;> simp [bitVal]
      simp [hcard, hwt]
    have hwt_le : weight x ≤ 2 * m := hcard ▸ card_filter_le univ _
    rw [h1]
    by_cases hxm : weight x ≤ m
    · have ht_sum : ∑ t ∈ Icc 1 m, Tfun t x = ((m - weight x : ℕ) : ℝ) := by
        have hunion : Icc 1 (m - weight x) ∪ Icc (m - weight x + 1) m = Icc 1 m := by
          ext t; simp only [mem_union, mem_Icc]; omega
        have hdisj : Disjoint (Icc 1 (m - weight x)) (Icc (m - weight x + 1) m) := by
          rw [disjoint_left]; intro t h1 h2; simp only [mem_Icc] at h1 h2; omega
        calc ∑ t ∈ Icc 1 m, Tfun t x
            = ∑ t ∈ Icc 1 (m - weight x), Tfun t x +
              ∑ t ∈ Icc (m - weight x + 1) m, Tfun t x := by
              rw [← hunion, sum_union hdisj]
          _ = ∑ t ∈ Icc 1 (m - weight x), (1 : ℝ) +
              ∑ t ∈ Icc (m - weight x + 1) m, (0 : ℝ) := by
              congr 1
              · refine sum_congr rfl fun t ht ↦ ?_
                simp only [mem_Icc] at ht
                simp [Tfun, show weight x + t ≤ m by omega]
              · refine sum_congr rfl fun t ht ↦ ?_
                simp only [mem_Icc] at ht
                simp [Tfun, show ¬weight x + t ≤ m by omega, show ¬m + t ≤ weight x by omega]
          _ = ((m - weight x : ℕ) : ℝ) := by simp
      rw [ht_sum, Nat.cast_sub hxm]
      ring
    · have hgt : m < weight x := by omega
      have ht_sum : ∑ t ∈ Icc 1 m, Tfun t x = -((weight x - m : ℕ) : ℝ) := by
        have hunion : Icc 1 (weight x - m) ∪ Icc (weight x - m + 1) m = Icc 1 m := by
          ext t; simp only [mem_union, mem_Icc]; omega
        have hdisj : Disjoint (Icc 1 (weight x - m)) (Icc (weight x - m + 1) m) := by
          rw [disjoint_left]; intro t h1 h2; simp only [mem_Icc] at h1 h2; omega
        rw [← hunion, sum_union hdisj]
        have hs1 : ∑ t ∈ Icc 1 (weight x - m), Tfun t x = -((weight x - m : ℕ) : ℝ) := by
          have : ∀ t ∈ Icc 1 (weight x - m), Tfun t x = -1 := fun t ht ↦ by
            simp only [mem_Icc] at ht
            simp [Tfun, show ¬weight x + t ≤ m by omega, show m + t ≤ weight x by omega]
          rw [sum_congr rfl this]
          simp
        have hs2 : ∑ t ∈ Icc (weight x - m + 1) m, Tfun t x = 0 :=
          sum_eq_zero fun t ht ↦ by
            simp only [mem_Icc] at ht
            simp [Tfun, show ¬weight x + t ≤ m by omega, show ¬m + t ≤ weight x by omega]
        rw [hs1, hs2, add_zero]
      rw [ht_sum, Nat.cast_sub hgt.le]
      ring
  -- Bound each slice t ∈ Icc 1 m via Smolensky dimension counting
  -- (`card_le_of_forall_exists_agree`)!
  have hslice : ∀ t ∈ Icc 1 m,
      (∑ x : ι → Bool, signVal (g x) * Tfun t x) ≤
        2 * (#{S : Finset ι | m - t < #S ∧ #S ≤ m - t + d} : ℝ) := by
    intro t ht
    have ht1 : 1 ≤ t := (mem_Icc.1 ht).1
    have htm : t ≤ m := (mem_Icc.1 ht).2
    let Ulow : Finset (ι → Bool) := univ.filter fun x ↦ weight x ≤ m - t
    let Uhi : Finset (ι → Bool) := univ.filter fun x ↦ m + t ≤ weight x
    have hUdisj : Disjoint Ulow Uhi := by
      rw [disjoint_left]; intro x h1 h2
      simp only [Ulow, Uhi, mem_filter] at h1 h2; omega
    let At : Finset (ι → Bool) :=
      (Ulow.filter fun x ↦ g x = false) ∪ (Uhi.filter fun x ↦ g x = true)
    have hAt_card : #At ≤ #{S : Finset ι | #S ≤ m - t + d} := by
      refine card_le_of_forall_exists_agree (F := ZMod 2) At fun φ ↦ ?_
      obtain ⟨q₁, hq₁_mem, hq₁_val⟩ := exists_mem_lowDegree_agree_of_weight_le (m - t) φ
      obtain ⟨q₂, hq₂_mem, hq₂_val⟩ := exists_mem_lowDegree_agree_of_le_weight (m - t) φ
      let q : (ι → Bool) → ZMod 2 := (1 - p) * q₁ + p * q₂
      have hq_mem : q ∈ lowDegree (ZMod 2) ι (m - t + d) := by
        have h1 : (1 - p) * q₁ ∈ lowDegree (ZMod 2) ι (d + (m - t)) :=
          mul_mem_lowDegree (one_sub_mem_lowDegree hp_deg) hq₁_mem
        have h2 : p * q₂ ∈ lowDegree (ZMod 2) ι (d + (m - t)) :=
          mul_mem_lowDegree hp_deg hq₂_mem
        rw [add_comm (m - t) d]
        exact Submodule.add_mem _ h1 h2
      refine ⟨q, hq_mem, fun x hx ↦ ?_⟩
      rcases mem_union.1 hx with hlow | hhi
      · obtain ⟨hxU, hxg⟩ := mem_filter.1 hlow
        have hp0 : p x = 0 := by simp [p, hxg, bitVal]
        have hwt : weight x ≤ m - t := (mem_filter.1 hxU).2
        simp [q, hp0, hq₁_val x hwt]
      · obtain ⟨hxU, hxg⟩ := mem_filter.1 hhi
        have hp1 : p x = 1 := by simp [p, hxg, bitVal]
        have hwt : m + t ≤ weight x := (mem_filter.1 hxU).2
        simp [q, hp1, hq₂_val x (by omega)]
    have hsum_At : (∑ x : ι → Bool, signVal (g x) * Tfun t x) =
        2 * (#At : ℝ) - (#(Ulow ∪ Uhi) : ℝ) := by
      have hsub : ∑ x : ι → Bool, signVal (g x) * Tfun t x =
          ∑ x ∈ Ulow ∪ Uhi, signVal (g x) * Tfun t x := by
        symm
        refine sum_subset (subset_univ _) fun x _ hnot ↦ ?_
        simp only [mem_union, Ulow, Uhi, mem_filter, mem_univ, true_and, not_or] at hnot
        simp [Tfun, show ¬weight x + t ≤ m by omega, show ¬m + t ≤ weight x by omega]
      rw [hsub]
      have hterm : ∀ x ∈ Ulow ∪ Uhi,
          signVal (g x) * Tfun t x = (if x ∈ At then (2 : ℝ) else 0) - 1 := by
        intro x hx
        rcases mem_union.1 hx with hl | hh
        · have hwt : weight x ≤ m - t := (mem_filter.1 hl).2
          have hT : Tfun t x = 1 := by simp [Tfun, show weight x + t ≤ m by omega]
          have hnh : x ∉ Uhi := disjoint_left.1 hUdisj hl
          rw [hT, mul_one]
          cases hgx : g x
          · simp [At, hl, hnh, hgx, signVal]; norm_num
          · simp [At, hl, hnh, hgx, signVal]
        · have hwt : m + t ≤ weight x := (mem_filter.1 hh).2
          have hT : Tfun t x = -1 := by
            simp [Tfun, show ¬weight x + t ≤ m by omega, hwt]
          have hnl : x ∉ Ulow := disjoint_right.1 hUdisj hh
          rw [hT]
          cases hgx : g x
          · simp [At, hh, hnl, hgx, signVal]
          · simp [At, hh, hnl, hgx, signVal]; norm_num
      rw [sum_congr rfl hterm, sum_sub_distrib]
      have hAt_sub : At ⊆ Ulow ∪ Uhi :=
        union_subset_union (filter_subset _ _) (filter_subset _ _)
      have hcnt : (∑ x ∈ Ulow ∪ Uhi, if x ∈ At then (2 : ℝ) else 0) = 2 * (#At : ℝ) := by
        rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 hAt_sub]
        simp [mul_comm]
      rw [hcnt]
      simp
    have hU_card : #(Ulow ∪ Uhi) = 2 * #{S : Finset ι | #S ≤ m - t} := by
      rw [card_union_of_disjoint hUdisj, two_mul]
      have hcl : #Ulow = #{S : Finset ι | #S ≤ m - t} := by
        refine card_bij (fun x _ ↦ trueSet x)
          (fun x hx ↦ mem_filter.2 ⟨mem_univ _, (mem_filter.1 hx).2⟩)
          (fun _ _ _ _ h ↦ trueSet_injective h)
          fun S hS ↦ ⟨fun i ↦ decide (i ∈ S),
            mem_filter.2 ⟨mem_univ _, by
              have : trueSet (fun i ↦ decide (i ∈ S)) = S := by ext i; simp [trueSet]
              change #(trueSet (fun i ↦ decide (i ∈ S))) ≤ m - t
              rw [this]; exact (mem_filter.1 hS).2⟩,
            by ext i; simp [trueSet]⟩
      have hch : #Uhi = #Ulow := by
        refine card_bij (fun x _ ↦ fun i ↦ !x i)
          (fun x hx ↦ by
            have hwx : m + t ≤ weight x := (mem_filter.1 hx).2
            have hwt : weight (fun i ↦ !x i) + weight x = 2 * m := by
              rw [weight_not_add_weight, hcard]
            exact mem_filter.2 ⟨mem_univ _, by omega⟩)
          (fun x₁ _ x₂ _ h ↦ by
            ext i; have := congr_fun h i; simpa using this)
          fun y hy ↦ ⟨fun i ↦ !y i, by
            have hwy : weight y ≤ m - t := (mem_filter.1 hy).2
            have hwt : weight (fun i ↦ !y i) + weight y = 2 * m := by
              rw [weight_not_add_weight, hcard]
            exact mem_filter.2 ⟨mem_univ _, by omega⟩, by ext i; simp⟩
      rw [hch, hcl]
    have hsplit_S : #{S : Finset ι | #S ≤ m - t + d} =
        #{S : Finset ι | #S ≤ m - t} + #{S : Finset ι | m - t < #S ∧ #S ≤ m - t + d} := by
      rw [← card_union_of_disjoint (by
        rw [disjoint_left]; intro S h1 h2; simp only [mem_filter] at h1 h2; omega)]
      congr 1
      ext S
      simp only [mem_filter, mem_union, mem_univ, true_and]
      omega
    rw [hsum_At, hU_card]
    have hAt_r : (#At : ℝ) ≤
        (#{S : Finset ι | #S ≤ m - t} : ℝ) +
          (#{S : Finset ι | m - t < #S ∧ #S ≤ m - t + d} : ℝ) := by
      exact_mod_cast hAt_card.trans_eq hsplit_S
    push_cast
    linarith
  -- Sum over t ∈ Icc 1 m and double-count over S : Finset ι: each S appears for at most d values of
  -- t!
  have hdouble : ∑ t ∈ Icc 1 m, #{S : Finset ι | m - t < #S ∧ #S ≤ m - t + d} ≤
      d * 2 ^ Fintype.card ι := by
    calc ∑ t ∈ Icc 1 m, #{S : Finset ι | m - t < #S ∧ #S ≤ m - t + d}
        = ∑ t ∈ Icc 1 m, ∑ S : Finset ι,
            if m - t < #S ∧ #S ≤ m - t + d then 1 else 0 := by
          refine sum_congr rfl fun t _ ↦ by rw [sum_boole, Nat.cast_id]
      _ = ∑ S : Finset ι, ∑ t ∈ Icc 1 m,
            if m - t < #S ∧ #S ≤ m - t + d then 1 else 0 := sum_comm
      _ ≤ ∑ _ : Finset ι, d := by
          refine sum_le_sum fun S _ ↦ ?_
          rw [sum_boole]
          have hsub : {t ∈ Icc 1 m | m - t < #S ∧ #S ≤ m - t + d} ⊆
              Ico (m + 1 - #S) (m + 1 - #S + d) := by
            intro t ht
            simp only [mem_filter, mem_Icc, mem_Ico] at ht ⊢
            omega
          exact (card_le_card hsub).trans (by simp)
      _ = d * 2 ^ Fintype.card ι := by simp [mul_comm]
  rw [hsum_eq]
  change ∑ i : ι, fourierCoeff (fun x ↦ signVal (g x)) {i} ≤ 4 * (d : ℝ)
  have hsum_fc : ∑ i : ι, fourierCoeff (fun x ↦ signVal (g x)) {i} =
      𝔼 x : ι → Bool, signVal (g x) * ∑ i : ι, signVal (x i) := by
    simp_rw [fourierCoeff, chi_singleton, mul_sum]
    exact (expect_sum_comm _ _ _).symm
  rw [hsum_fc]
  simp_rw [hsign_sum]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_le_iff₀ (by positivity)]
  have hexpand : (∑ x : ι → Bool, signVal (g x) * (2 * ∑ t ∈ Icc 1 m, Tfun t x)) =
      2 * ∑ t ∈ Icc 1 m, ∑ x : ι → Bool, signVal (g x) * Tfun t x := by
    calc ∑ x : ι → Bool, signVal (g x) * (2 * ∑ t ∈ Icc 1 m, Tfun t x)
        = 2 * ∑ x : ι → Bool, ∑ t ∈ Icc 1 m, signVal (g x) * Tfun t x := by
          rw [mul_sum]
          refine sum_congr rfl fun x _ ↦ by
            rw [← mul_assoc, mul_comm (signVal (g x)) 2, mul_assoc, mul_sum, mul_sum]
      _ = 2 * ∑ t ∈ Icc 1 m, ∑ x : ι → Bool, signVal (g x) * Tfun t x := by
          rw [sum_comm]
  rw [hexpand]
  have hsum_le : ∑ t ∈ Icc 1 m, ∑ x : ι → Bool, signVal (g x) * Tfun t x ≤
      2 * ((d : ℝ) * (2 : ℝ) ^ Fintype.card ι) := by
    calc ∑ t ∈ Icc 1 m, ∑ x : ι → Bool, signVal (g x) * Tfun t x
        ≤ ∑ t ∈ Icc 1 m, 2 * (#{S : Finset ι | m - t < #S ∧ #S ≤ m - t + d} : ℝ) :=
          sum_le_sum hslice
      _ = 2 * ∑ t ∈ Icc 1 m, (#{S : Finset ι | m - t < #S ∧ #S ≤ m - t + d} : ℝ) :=
          (mul_sum ..).symm
      _ ≤ 2 * ((d : ℝ) * (2 : ℝ) ^ Fintype.card ι) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact_mod_cast hdouble
  linarith

/-- Every Boolean function `f : (ι → Bool) → Bool`,
`∑ i : ι, |f̂({i})| ≤ 4 * deg_{𝔽₂}(f)`.
-/
theorem sum_abs_boolFourierCoeff_singleton_le_four_mul_f2Degree
    (f : (ι → Bool) → Bool) :
    ∑ i : ι, |boolFourierCoeff f {i}| ≤ 4 * (f2Degree f : ℝ) := by
  rcases Nat.even_or_odd (Fintype.card ι) with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact sum_abs_singleton_le_four_mul_f2Degree_even (show Fintype.card ι = 2 * m by omega) f
  · -- Odd |ι| = 2 m + 1: add one dummy variable via Option ι (|Option ι| = 2 (m + 1)).
    let f' : (Option ι → Bool) → Bool := fun y ↦ f (fun i ↦ y (some i))
    have hcard' : Fintype.card (Option ι) = 2 * (m + 1) := by
      rw [Fintype.card_option, hm]; ring
    have hdeg_le : f2Degree f' ≤ f2Degree f := by
      rw [f2Degree, totalDegree_le_iff_mem_lowDegree]
      let A : (Option ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
        { toFun := fun v i ↦ v (some i)
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      have hfeq : (fun y : Option ι → Bool ↦ bitVal (ZMod 2) (f' y)) =
          fun y ↦ bitVal (ZMod 2) (f (applyF2Linear A y)) := by
        ext y
        congr 1
        apply congr_arg f
        ext j
        simp [applyF2Linear_apply, A]
      rw [hfeq]
      exact mem_lowDegree_comp_applyF2Linear A (mem_lowDegree_totalDegree _)
    have hfc_some : ∀ i : ι, boolFourierCoeff f' {some i} = boolFourierCoeff f {i} := by
      intro i
      let A : (Option ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
        { toFun := fun v j ↦ v (some j)
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      have hfeq : f' = fun y ↦ f (applyF2Linear A y) := by
        ext y; apply congr_arg f; ext j; simp [applyF2Linear_apply, A]
      rw [hfeq, boolFourierCoeff_comp_applyF2Linear A f {some i}]
      have hdual : ∀ S : Finset ι, dualParitySet A S = {some i} ↔ S = {i} := by
        intro S; constructor
        · intro h; ext j
          have hj := congr_fun (congr_arg parityVec h) (some j)
          rw [parityVec_dualParitySet, transposeF2Linear_apply] at hj
          simp only [A, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, Option.some.injEq,
            parityVec_apply, mem_singleton] at hj ⊢
          have hsum : (∑ k : ι, (if k ∈ S then (1 : ZMod 2) else 0) * if k = j then 1 else 0) =
              if j ∈ S then 1 else 0 := by simp
          rw [hsum] at hj
          by_cases h1 : j ∈ S <;> by_cases h2 : j = i <;> simp_all
        · rintro rfl
          apply parityVec_injective; ext o
          rw [parityVec_dualParitySet, transposeF2Linear_apply]
          cases o with
          | none => simp [A, parityVec_apply]
          | some j => simp [A, Pi.single_apply, parityVec_apply, eq_comm]
      simp_rw [hdual]
      simp only [filter_eq', mem_univ, ↓reduceIte, sum_singleton]
    have hsum_le : ∑ i : ι, |boolFourierCoeff f {i}| ≤
        ∑ o : Option ι, |boolFourierCoeff f' {o}| := by
      rw [Fintype.sum_option]
      have : ∑ i : ι, |boolFourierCoeff f' {some i}| = ∑ i : ι, |boolFourierCoeff f {i}| :=
        sum_congr rfl fun i _ ↦ by rw [hfc_some]
      linarith [abs_nonneg (boolFourierCoeff f' {none})]
    calc ∑ i : ι, |boolFourierCoeff f {i}|
        ≤ ∑ o : Option ι, |boolFourierCoeff f' {o}| := hsum_le
      _ ≤ 4 * (f2Degree f' : ℝ) := sum_abs_singleton_le_four_mul_f2Degree_even hcard' f'
      _ ≤ 4 * (f2Degree f : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact_mod_cast hdeg_le

/-- Basis generalization of Chattopadhyay–Hatami–Lovett–Tal : for any `𝔽₂`-linearly
independent family `ℬ` of character indices, `∑ S ∈ ℬ, |f̂(S)| ≤ 4 * deg_{𝔽₂}(f)`.
-/
theorem sum_abs_boolFourierCoeff_linearIndep_le_four_mul_f2Degree
    (f : (ι → Bool) → Bool) {ℬ : Finset (Finset ι)}
    (hli : LinearIndependent (ZMod 2) (fun S : ℬ ↦ parityVec S.1)) :
    ∑ S ∈ ℬ, |boolFourierCoeff f S| ≤ 4 * (f2Degree f : ℝ) := by
  obtain ⟨B, emb, hB, _⟩ := exists_linearEquiv_extending_finset hli
  let h := fourierBasisChange B f
  calc ∑ S ∈ ℬ, |boolFourierCoeff f S|
      = ∑ S : ℬ, |boolFourierCoeff f S.1| := (sum_attach ℬ _).symm
    _ = ∑ S : ℬ, |boolFourierCoeff h {emb S}| := by
        refine sum_congr rfl fun S _ ↦ ?_
        rw [boolFourierCoeff_fourierBasisChange, hB S]
        exact congr_arg (fun T ↦ |boolFourierCoeff f T|) (parityVecEquiv.symm_apply_apply S.1).symm
    _ = ∑ i ∈ univ.map emb, |boolFourierCoeff h {i}| :=
        (sum_map univ emb fun i ↦ |boolFourierCoeff h {i}|).symm
    _ ≤ ∑ i : ι, |boolFourierCoeff h {i}| :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ abs_nonneg _
    _ ≤ 4 * (f2Degree h : ℝ) := sum_abs_boolFourierCoeff_singleton_le_four_mul_f2Degree h
    _ = 4 * (f2Degree f : ℝ) := by rw [f2Degree_fourierBasisChange]

/-- For every Boolean function with `k(f) > 1` and every `𝔽₂`-linearly independent family `ℬ`,
`∑ S ∈ ℬ, |f̂(S)| ≤ 4 * log₂ k(f)`. -/
theorem sum_abs_boolFourierCoeff_linearIndep_le_four_mul_logb
    {f : (ι → Bool) → Bool} (hk : 1 < boolSparsity f) {ℬ : Finset (Finset ι)}
    (hli : LinearIndependent (ZMod 2) (fun S : ℬ ↦ parityVec S.1)) :
    ∑ S ∈ ℬ, |boolFourierCoeff f S| ≤ 4 * Real.logb 2 (boolSparsity f) :=
  (sum_abs_boolFourierCoeff_linearIndep_le_four_mul_f2Degree f hli).trans
    (mul_le_mul_of_nonneg_left (f2Degree_le_logb_boolSparsity hk) (by norm_num))

end LowWeightInterpolation

section WeightedRefinement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Elementary inequality `1 / 4 ≤ (1 - x) ^ n` when `0 < x ≤ 1 / 2` and `(n : ℝ) ≤ 1 / x`. -/
private theorem quarter_le_one_sub_pow {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) {n : ℕ}
    (hn : (n : ℝ) ≤ 1 / x) :
    (1 / 4 : ℝ) ≤ (1 - x) ^ n := by
  have h1x : 0 < 1 - x := by linarith
  -- Concavity of log gives log(1 - x) ≥ -2 * log 2 * x on [0, 1/2]!
  have hlog : -(2 * Real.log 2) * x ≤ Real.log (1 - x) := by
    have hconc := strictConcaveOn_log_Ioi.concaveOn
    have ha : (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have hb : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have hcomb := hconc.2 ha hb (show (0 : ℝ) ≤ 2 * x by linarith)
      (show (0 : ℝ) ≤ 1 - 2 * x by linarith) (by ring)
    have hpt : (2 * x) • (1 / 2 : ℝ) + (1 - 2 * x) • (1 : ℝ) = 1 - x := by
      simp [smul_eq_mul]; ring
    rw [hpt, Real.log_one, smul_zero, add_zero, smul_eq_mul,
      show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]] at hcomb
    linarith
  have hn_log : Real.log (1 / 4 : ℝ) ≤ (n : ℝ) * Real.log (1 - x) := by
    have hlog_neg : Real.log (1 - x) ≤ 0 := Real.log_nonpos h1x.le (by linarith)
    calc Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
          rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
          ring
      _ = (1 / x) * (-(2 * Real.log 2) * x) := by field_simp
      _ ≤ (1 / x) * Real.log (1 - x) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (n : ℝ) * Real.log (1 - x) := mul_le_mul_of_nonpos_right hn hlog_neg
  rw [← Real.log_pow] at hn_log
  exact (Real.log_le_log_iff (by norm_num) (pow_pos h1x n)).1 hn_log

/-- **Weighted level-1 Fourier growth inequality**: for every Boolean function
`f : (ι → Bool) → Bool`, `∑ i : ι, |f̂({i})| ≤ 32 * δ(f) * deg_{𝔽₂}(f)`. -/
theorem sum_abs_boolFourierCoeff_singleton_le_mul_weight_f2Degree
    (f : (ι → Bool) → Bool) :
    ∑ i : ι, |boolFourierCoeff f {i}| ≤ 32 * boolWeight f * (f2Degree f : ℝ) := by
  set δ := boolWeight f
  set d := f2Degree f
  rcases (boolWeight_nonneg f).eq_or_lt with h0 | hδ_pos
  · have hconst := boolWeight_eq_zero_iff.1 h0.symm
    have hfeq : f = fun _ ↦ false := funext hconst
    have hδ0 : δ = 0 := h0.symm
    rw [hδ0, hfeq]
    simp [boolFourierCoeff_const]
  by_cases hδ_ge : 1 / 4 ≤ δ
  · calc ∑ i : ι, |boolFourierCoeff f {i}|
        ≤ 4 * (d : ℝ) := sum_abs_boolFourierCoeff_singleton_le_four_mul_f2Degree f
      _ ≤ 32 * δ * (d : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  push Not at hδ_ge
  -- XOR t = 1 + ⌊1 / (2 δ)⌋ disjoint copies of f on Fin t × ι.
  let m : ℕ := Nat.floor (1 / (2 * δ))
  let t : ℕ := m + 1
  have hm_le : (m : ℝ) ≤ 1 / (2 * δ) := Nat.floor_le (by positivity)
  have ht_gt : 1 / (2 * δ) < (t : ℝ) := by exact_mod_cast Nat.lt_floor_add_one (1 / (2 * δ))
  let F : ((Fin t × ι) → Bool) → Bool :=
    fun X ↦ parityOn univ fun r : Fin t ↦ f (fun i ↦ X (r, i))
  have hF_sign : ∀ X : (Fin t × ι) → Bool,
      signVal (F X) = ∏ r : Fin t, signVal (f fun i ↦ X (r, i)) := by
    intro X
    unfold F
    rw [← chi_eq_signVal_parityOn, chi_eq_prod_signVal]
  have hF_deg : f2Degree F ≤ d := by
    rw [f2Degree, totalDegree_le_iff_mem_lowDegree]
    have hfun : (fun X : (Fin t × ι) → Bool ↦ bitVal (ZMod 2) (F X)) =
        ∑ r : Fin t, fun X ↦ bitVal (ZMod 2) (f fun i ↦ X (r, i)) := by
      ext X
      simp only [F, Finset.sum_apply, ← boolToZModVal_eq_bitVal, boolToZModVal_parityOn]
    rw [hfun]
    refine Submodule.sum_mem _ fun r _ ↦ ?_
    let Ar : ((Fin t × ι) → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
      { toFun := fun v i ↦ v (r, i)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hcomp : (fun X : (Fin t × ι) → Bool ↦ bitVal (ZMod 2) (f fun i ↦ X (r, i))) =
        fun X ↦ bitVal (ZMod 2) (f (applyF2Linear Ar X)) := by
      ext X
      congr 1
      apply congr_arg f
      ext i
      simp [applyF2Linear_apply, Ar]
    rw [hcomp]
    exact mem_lowDegree_comp_applyF2Linear Ar (mem_lowDegree_totalDegree _)
  have hF_singleton : ∀ (r : Fin t) (i : ι),
      boolFourierCoeff F {(r, i)} = (1 - 2 * δ) ^ m * boolFourierCoeff f {i} := by
    intro r₀ i₀
    let blockEquiv : (Fin t → ι → Bool) ≃ ((Fin t × ι) → Bool) :=
      { toFun := fun Y p ↦ Y p.1 p.2
        invFun := fun X r i ↦ X (r, i)
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [boolFourierCoeff_eq_sum]
    rw [← Equiv.sum_comp blockEquiv]
    have hterm : ∀ Y : Fin t → ι → Bool,
        signVal (F (blockEquiv Y)) * chi ℝ {(r₀, i₀)} (blockEquiv Y) =
          ∏ r : Fin t, (signVal (f (Y r)) * if r = r₀ then chi ℝ {i₀} (Y r) else 1) := by
      intro Y
      rw [hF_sign, prod_mul_distrib]
      congr 1
      rw [chi_singleton]
      change signVal (Y r₀ i₀) = _
      symm
      refine (prod_eq_single r₀ (fun r _ hne ↦ ite_eq_right hne) (by simp)).trans ?_
      rw [ite_eq_left rfl, chi_singleton]
    simp_rw [hterm]
    rw [← Fintype.prod_sum (f := fun (r : Fin t) (y : ι → Bool) ↦
      signVal (f y) * if r = r₀ then chi ℝ {i₀} y else 1)]
    have hcard_prod : (2 : ℝ) ^ Fintype.card (Fin t × ι) =
        ∏ _ : Fin t, (2 : ℝ) ^ Fintype.card ι := by
      rw [prod_const, card_univ, ← pow_mul, Fintype.card_prod, mul_comm]
    rw [hcard_prod, ← prod_div_distrib]
    have hfac : ∀ r : Fin t,
        (∑ y : ι → Bool, signVal (f y) * if r = r₀ then chi ℝ {i₀} y else 1) /
          (2 : ℝ) ^ Fintype.card ι =
          if r = r₀ then boolFourierCoeff f {i₀} else 1 - 2 * δ := by
      intro r
      split_ifs with hr
      · rw [← boolFourierCoeff_eq_sum]
      · have heq : (∑ y : ι → Bool, signVal (f y) * 1) =
            ∑ y : ι → Bool, signVal (f y) * chi ℝ (∅ : Finset ι) y :=
          sum_congr rfl fun y _ ↦ by rw [chi_empty]
        rw [heq, ← boolFourierCoeff_eq_sum, boolFourierCoeff_empty]
    simp_rw [hfac]
    rw [← mul_prod_erase univ _ (mem_univ r₀), ite_eq_left rfl]
    have her : ∏ r ∈ univ.erase r₀, (if r = r₀ then boolFourierCoeff f {i₀} else 1 - 2 * δ) =
        (1 - 2 * δ) ^ m := by
      have : ∀ r ∈ univ.erase r₀,
          (if r = r₀ then boolFourierCoeff f {i₀} else 1 - 2 * δ) = 1 - 2 * δ :=
        fun r hr ↦ ite_eq_right (ne_of_mem_erase hr)
      rw [prod_congr rfl this, prod_const, card_erase_of_mem (mem_univ r₀), card_univ,
        Fintype.card_fin]
      simp [t]
    rw [her, mul_comm]
  have h12δ_pos : 0 < 1 - 2 * δ := by linarith
  have hpow_ge : (1 / 4 : ℝ) ≤ (1 - 2 * δ) ^ m :=
    quarter_le_one_sub_pow (by linarith) (by linarith) hm_le
  have hF_sum : (1 / (8 * δ)) * ∑ i : ι, |boolFourierCoeff f {i}| ≤
      ∑ p : Fin t × ι, |boolFourierCoeff F {p}| := by
    rw [Fintype.sum_prod_type]
    simp_rw [hF_singleton, abs_mul, abs_of_pos (pow_pos h12δ_pos m), ← mul_sum, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ ↦ abs_nonneg _)
    calc 1 / (8 * δ) = (1 / 4) * (1 / (2 * δ)) := by ring
      _ ≤ (1 - 2 * δ) ^ m * (t : ℝ) :=
          mul_le_mul hpow_ge ht_gt.le (by positivity) (by positivity)
  have hchlt : ∑ p : Fin t × ι, |boolFourierCoeff F {p}| ≤ 4 * (d : ℝ) :=
    (sum_abs_boolFourierCoeff_singleton_le_four_mul_f2Degree F).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hF_deg) (by norm_num))
  have hcomb := hF_sum.trans hchlt
  have h8δ : 0 < 8 * δ := by positivity
  have := (div_le_iff₀ h8δ).1 (by simpa [div_eq_inv_mul, one_div] using hcomb)
  linarith

/-- Weighted level-1 bound along any `𝔽₂`-linearly independent family `ℬ` of character indices:
`∑ S ∈ ℬ, |f̂(S)| ≤ 32 * δ(f) * deg_{𝔽₂}(f)`. -/
theorem sum_abs_boolFourierCoeff_linearIndep_le_mul_weight_f2Degree
    (f : (ι → Bool) → Bool) {ℬ : Finset (Finset ι)}
    (hli : LinearIndependent (ZMod 2) (fun S : ℬ ↦ parityVec S.1)) :
    ∑ S ∈ ℬ, |boolFourierCoeff f S| ≤ 32 * boolWeight f * (f2Degree f : ℝ) := by
  obtain ⟨B, emb, hB, _⟩ := exists_linearEquiv_extending_finset hli
  let h := fourierBasisChange B f
  calc ∑ S ∈ ℬ, |boolFourierCoeff f S|
      = ∑ S : ℬ, |boolFourierCoeff f S.1| := (sum_attach ℬ _).symm
    _ = ∑ S : ℬ, |boolFourierCoeff h {emb S}| :=
        sum_congr rfl fun S _ ↦ by
          rw [boolFourierCoeff_fourierBasisChange, hB S]
          exact congr_arg (fun T ↦ |boolFourierCoeff f T|)
            (parityVecEquiv.symm_apply_apply S.1).symm
    _ = ∑ i ∈ univ.map emb, |boolFourierCoeff h {i}| :=
        (sum_map univ emb fun i ↦ |boolFourierCoeff h {i}|).symm
    _ ≤ ∑ i : ι, |boolFourierCoeff h {i}| :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ abs_nonneg _
    _ ≤ 32 * boolWeight h * (f2Degree h : ℝ) :=
        sum_abs_boolFourierCoeff_singleton_le_mul_weight_f2Degree h
    _ = 32 * boolWeight f * (f2Degree f : ℝ) := by
        rw [boolWeight_fourierBasisChange, f2Degree_fourierBasisChange]

/-- Weighted level-1 bound in terms of Fourier sparsity: for every Boolean function with `k(f) > 1`
and every `𝔽₂`-linearly independent family `ℬ`,
`∑ S ∈ ℬ, |f̂(S)| ≤ 32 * δ(f) * log₂ k(f)`. -/
theorem sum_abs_boolFourierCoeff_linearIndep_le_mul_weight_logb
    {f : (ι → Bool) → Bool} (hk : 1 < boolSparsity f) {ℬ : Finset (Finset ι)}
    (hli : LinearIndependent (ZMod 2) (fun S : ℬ ↦ parityVec S.1)) :
    ∑ S ∈ ℬ, |boolFourierCoeff f S| ≤
      32 * boolWeight f * Real.logb 2 (boolSparsity f) :=
  (sum_abs_boolFourierCoeff_linearIndep_le_mul_weight_f2Degree f hli).trans
    (mul_le_mul_of_nonneg_left (f2Degree_le_logb_boolSparsity hk)
      (mul_nonneg (by norm_num) (boolWeight_nonneg f)))

end WeightedRefinement

end CslibFrontier.BooleanFunction
