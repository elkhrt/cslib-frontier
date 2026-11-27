/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted Linear Threshold Functions, Chow Parameters, and Monarchy Predicates

Weighted linear threshold Boolean functions (LTFs), balanced zero-threshold linear threshold
functions, degree-`1` Walsh–Fourier Chow parameters, and presidential (monarchy / weak monarchy)
threshold predicates over the Boolean hypercube `Cslib.BitString k`.

Under the sign encoding `Cslib.BitString.signVal : Bool → ℝ` (`false ↦ 1`, `true ↦ -1`) and `{0, 1}`
encoding `Cslib.BitString.bitVal ℝ : Bool → ℝ` (`true ↦ 1`, `false ↦ 0`), a weighted linear
threshold function evaluates `posSign (∑ i, w i * signVal (x i) + θ)`. When `θ = 0` and the linear
form never vanishes on the hypercube, the predicate is *balanced*: it flips under bitwise negation
and satisfies `randomSatProb f = 1 / 2`.

## Main definitions

* `CslibFrontier.BooleanAnalysis.posSign`: strict positive threshold `z ↦ decide (0 < z)`.
* `CslibFrontier.BooleanAnalysis.linearThreshold`: weighted linear threshold Boolean function.
* `CslibFrontier.BooleanAnalysis.IsLTF`, `CslibFrontier.BooleanAnalysis.IsBalancedLTF`: linear
  threshold and balanced zero-threshold linear threshold predicates.
* `CslibFrontier.BooleanAnalysis.randomSatProb`: uniform satisfaction density on `BitString k`.
* `CslibFrontier.BooleanAnalysis.boolFourierCoeff`, `CslibFrontier.BooleanAnalysis.chowCoeff`:
  Walsh–Fourier coefficients of `bitVal ℝ ∘ f` and degree-`1` Chow parameters.
* `CslibFrontier.BooleanAnalysis.IsChowDefinedLTF`, `CslibFrontier.BooleanAnalysis.chowMargin`:
  zero-threshold LTFs defined by their degree-`1` Chow parameters and minimum positive Chow margin.
* `CslibFrontier.BooleanAnalysis.weakMonarchy`, `CslibFrontier.BooleanAnalysis.monarchy`: weak
  monarchy and pure monarchy predicates.
* `CslibFrontier.BooleanAnalysis.relabelLiterals`: coordinate permutation and literal negation on
  `BooleanFunction k`.

## Main results

* `CslibFrontier.BooleanAnalysis.IsBalancedLTF.eval_not`,
  `CslibFrontier.BooleanAnalysis.IsBalancedLTF.randomSatProb_eq_one_half`: antipodal negation
  symmetry and uniform density `1 / 2` for balanced LTFs.
* `CslibFrontier.BooleanAnalysis.randomSatProb_eq_boolFourierCoeff_empty`,
  `CslibFrontier.BooleanAnalysis.abs_boolFourierCoeff_le_boolFourierCoeff_empty`,
  `CslibFrontier.BooleanAnalysis.sum_chowCoeff_mul_signVal_bounds`: Fourier bounds for `{0, 1}`
  Boolean predicates.
* `CslibFrontier.BooleanAnalysis.chowMargin_pos_of_isChowDefinedLTF`,
  `CslibFrontier.BooleanAnalysis.pos_chowMargin_add_randomSatProb_mul_card`: positivity of the Chow
  margin on satisfiable Chow-defined LTFs.
* `CslibFrontier.BooleanAnalysis.isBalancedLTF_weakMonarchy`,
  `CslibFrontier.BooleanAnalysis.isBalancedLTF_monarchy`: parity criterion for balanced weak
  monarchy and pure monarchy predicates.
* `CslibFrontier.BooleanAnalysis.balancedLTF_le_four_classification`: every balanced LTF on at most
  `4` variables is equivalent under literal negation and coordinate permutation either to a
  Chow-defined LTF (dictator or `3`-majority) or to `monarchy 4`.
-/

public section

namespace CslibFrontier.BooleanAnalysis

open Finset
open Cslib.BitString
open scoped BigOperators

/-! ### 1. Strict positive sign and weighted linear threshold functions -/

/-- Strict positive threshold indicator `z ↦ decide (0 < z)`. -/
@[expose] noncomputable def posSign (z : ℝ) : Bool :=
  decide (0 < z)

@[simp]
theorem posSign_eq_true_iff {z : ℝ} : posSign z = true ↔ 0 < z := by
  simp only [posSign, decide_eq_true_eq]

@[simp]
theorem posSign_eq_false_iff {z : ℝ} : posSign z = false ↔ z ≤ 0 := by
  simp only [posSign, decide_eq_false_iff_not, not_lt]

theorem bitVal_posSign (z : ℝ) : bitVal ℝ (posSign z) = if 0 < z then 1 else 0 := by
  by_cases hz : 0 < z <;> simp only [posSign, hz, decide_true, decide_false, bitVal_true,
    bitVal_false, ↓reduceIte]

theorem posSign_mul_pos {c z : ℝ} (hc : 0 < c) : posSign (c * z) = posSign z := by
  rw [Bool.eq_iff_iff, posSign_eq_true_iff, posSign_eq_true_iff]
  exact mul_pos_iff_of_pos_left hc

theorem posSign_neg_of_ne_zero {z : ℝ} (hz : z ≠ 0) : posSign (-z) = !posSign z := by
  rcases lt_or_gt_of_ne hz with hlt | hgt
  · have hpos : 0 < -z := neg_pos.mpr hlt
    simp only [posSign_eq_true_iff.mpr hpos, posSign_eq_false_iff.mpr hlt.le, Bool.not_false]
  · have hneg : -z ≤ 0 := neg_nonpos.mpr hgt.le
    simp only [posSign_eq_false_iff.mpr hneg, posSign_eq_true_iff.mpr hgt, Bool.not_true]

/-- Weighted linear threshold Boolean function `x ↦ posSign (∑ i, w i * signVal (x i) + θ)`. -/
@[expose] noncomputable def linearThreshold {k : ℕ} (w : Fin k → ℝ) (θ : ℝ) :
    Cslib.BooleanFunction k :=
  fun x ↦ posSign (∑ i, w i * signVal (x i) + θ)

theorem linearThreshold_eq_true_iff {k : ℕ} {w : Fin k → ℝ} {θ : ℝ} {x : Cslib.BitString k} :
    linearThreshold w θ x = true ↔ 0 < ∑ i, w i * signVal (x i) + θ := by
  simp only [linearThreshold, posSign_eq_true_iff]

theorem linearThreshold_zero_eq_true_iff {k : ℕ} {w : Fin k → ℝ} {x : Cslib.BitString k} :
    linearThreshold w 0 x = true ↔ 0 < ∑ i, w i * signVal (x i) := by
  simp only [linearThreshold, add_zero, posSign_eq_true_iff]

theorem linearThreshold_zero_apply {k : ℕ} (w : Fin k → ℝ) (x : Cslib.BitString k) :
    linearThreshold w 0 x = posSign (∑ i, w i * signVal (x i)) := by
  simp only [linearThreshold, add_zero]

theorem linearThreshold_smul_pos {k : ℕ} {c : ℝ} (hc : 0 < c) (w : Fin k → ℝ) (θ : ℝ) :
    linearThreshold (fun i ↦ c * w i) (c * θ) = linearThreshold w θ := by
  funext x
  simp only [linearThreshold]
  have hsum : (∑ i, c * w i * signVal (x i) + c * θ) = c * (∑ i, w i * signVal (x i) + θ) := by
    rw [mul_add, mul_sum]
    refine congrArg (· + c * θ) (sum_congr rfl fun i _ ↦ ?_)
    ring
  rw [hsum, posSign_mul_pos hc]

/-- Predicate asserting that `f` is a weighted linear threshold Boolean function. -/
@[expose] def IsLTF {k : ℕ} (f : Cslib.BooleanFunction k) : Prop :=
  ∃ (w : Fin k → ℝ) (θ : ℝ), f = linearThreshold w θ

/-- Predicate asserting that `f` is a zero-threshold linear threshold function whose linear form
never vanishes on `BitString k`. -/
@[expose] def IsBalancedLTF {k : ℕ} (f : Cslib.BooleanFunction k) : Prop :=
  ∃ w : Fin k → ℝ, (∀ x : Cslib.BitString k, ∑ i, w i * signVal (x i) ≠ 0) ∧
    f = linearThreshold w 0

theorem IsBalancedLTF.isLTF {k : ℕ} {f : Cslib.BooleanFunction k} (hf : IsBalancedLTF f) :
    IsLTF f := by
  rcases hf with ⟨w, _, rfl⟩
  exact ⟨w, 0, rfl⟩

theorem IsBalancedLTF.arity_pos {k : ℕ} {f : Cslib.BooleanFunction k} (hf : IsBalancedLTF f) :
    0 < k := by
  rcases hf with ⟨w, hw, _⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exfalso
    exact hw Fin.elim0 (by simp)
  · exact hk

theorem IsBalancedLTF.eval_not {k : ℕ} {f : Cslib.BooleanFunction k} (hf : IsBalancedLTF f)
    (x : Cslib.BitString k) : f (fun i ↦ !x i) = !f x := by
  rcases hf with ⟨w, hw, rfl⟩
  rw [linearThreshold_zero_apply, linearThreshold_zero_apply]
  have hneg : (∑ i, w i * signVal (!x i)) = -(∑ i, w i * signVal (x i)) := by
    simp only [signVal_not, mul_neg, sum_neg_distrib]
  rw [hneg, posSign_neg_of_ne_zero (hw x)]

theorem IsBalancedLTF.bitVal_not {k : ℕ} {f : Cslib.BooleanFunction k} (hf : IsBalancedLTF f)
    (x : Cslib.BitString k) : bitVal ℝ (f (fun i ↦ !x i)) = 1 - bitVal ℝ (f x) := by
  rw [hf.eval_not x, Cslib.BitString.bitVal_not]

/-! ### 2. Uniform satisfaction density, Fourier coefficients, and Chow parameters -/

/-- Uniform satisfaction density `2⁻ᵏ |{x : f x = true}|`. -/
@[expose] noncomputable def randomSatProb {k : ℕ} (f : Cslib.BooleanFunction k) : ℝ :=
  ((univ.filter fun x : Cslib.BitString k ↦ f x = true).card : ℝ) / 2 ^ k

/-- Walsh–Fourier coefficient of `bitVal ℝ ∘ f`. -/
@[expose] noncomputable def boolFourierCoeff {k : ℕ} (f : Cslib.BooleanFunction k)
    (S : Finset (Fin k)) : ℝ :=
  Cslib.BitString.fourierCoeff (fun x ↦ bitVal ℝ (f x)) S

/-- Degree-`1` Chow parameter `boolFourierCoeff f {i}`. -/
@[expose] noncomputable def chowCoeff {k : ℕ} (f : Cslib.BooleanFunction k) (i : Fin k) : ℝ :=
  boolFourierCoeff f {i}

theorem sum_boolFourierCoeff_mul_chi {k : ℕ} (f : Cslib.BooleanFunction k)
    (x : Cslib.BitString k) :
    ∑ S : Finset (Fin k), boolFourierCoeff f S * chi ℝ S x = bitVal ℝ (f x) :=
  sum_fourierCoeff_mul_chi (fun y ↦ bitVal ℝ (f y)) x

theorem randomSatProb_eq_boolFourierCoeff_empty {k : ℕ} (f : Cslib.BooleanFunction k) :
    randomSatProb f = boolFourierCoeff f ∅ := by
  rw [boolFourierCoeff, fourierCoeff_eq_sum, Fintype.card_fin, randomSatProb]
  congr 1
  simp only [chi_empty, mul_one, bitVal, sum_boole]

theorem randomSatProb_eq_expect {k : ℕ} (f : Cslib.BooleanFunction k) :
    randomSatProb f = 𝔼 x : Cslib.BitString k, bitVal ℝ (f x) := by
  rw [randomSatProb_eq_boolFourierCoeff_empty, boolFourierCoeff, fourierCoeff_empty]

theorem randomSatProb_nonneg {k : ℕ} (f : Cslib.BooleanFunction k) : 0 ≤ randomSatProb f := by
  rw [randomSatProb]
  positivity

theorem randomSatProb_le_one {k : ℕ} (f : Cslib.BooleanFunction k) : randomSatProb f ≤ 1 := by
  rw [randomSatProb, div_le_one (by positivity)]
  have hcard : (univ.filter fun x : Cslib.BitString k ↦ f x = true).card ≤
      (univ : Finset (Cslib.BitString k)).card := card_filter_le _ _
  have huniv : (univ : Finset (Cslib.BitString k)).card = 2 ^ k := by
    rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact_mod_cast hcard.trans_eq huniv

theorem randomSatProb_linearThreshold_zero_le_one_half {k : ℕ} (w : Fin k → ℝ) :
    randomSatProb (linearThreshold w 0) ≤ 1 / 2 := by
  let S := univ.filter fun x : Cslib.BitString k ↦ linearThreshold w 0 x = true
  let T := univ.filter fun x : Cslib.BitString k ↦ ¬linearThreshold w 0 x = true
  have hpart : S.card + T.card = 2 ^ k := by
    simpa only [S, T, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
      card_filter_add_card_filter_not (s := (univ : Finset (Cslib.BitString k)))
        (fun x ↦ linearThreshold w 0 x = true)
  have hinj : S.card ≤ T.card := by
    refine card_le_card_of_injOn (fun x i ↦ !x i) (fun x hx ↦ ?_) (fun x _ y _ hxy ↦ ?_)
    · have hxS : linearThreshold w 0 x = true := (mem_filter.mp hx).2
      have hpos : 0 < ∑ i, w i * signVal (x i) := linearThreshold_zero_eq_true_iff.mp hxS
      have hneg : ∑ i, w i * signVal (!x i) ≤ 0 := by
        simp only [signVal_not, mul_neg, sum_neg_distrib, Left.neg_nonpos_iff]
        exact hpos.le
      exact mem_filter.mpr ⟨mem_univ _, by
        rw [linearThreshold_zero_eq_true_iff]
        linarith⟩
    · funext i
      exact Bool.not_inj (congrFun hxy i)
  rw [randomSatProb, div_le_iff₀ (by positivity)]
  have h2 : (2 : ℝ) * (S.card : ℝ) ≤ 2 ^ k := by exact_mod_cast (by omega : 2 * S.card ≤ 2 ^ k)
  change (S.card : ℝ) ≤ 1 / 2 * 2 ^ k
  linarith

theorem IsBalancedLTF.randomSatProb_eq_one_half {k : ℕ} {f : Cslib.BooleanFunction k}
    (hf : IsBalancedLTF f) : randomSatProb f = 1 / 2 := by
  let S := univ.filter fun x : Cslib.BitString k ↦ f x = true
  let T := univ.filter fun x : Cslib.BitString k ↦ ¬f x = true
  have hpart : S.card + T.card = 2 ^ k := by
    simpa only [S, T, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
      card_filter_add_card_filter_not (s := (univ : Finset (Cslib.BitString k)))
        (fun x ↦ f x = true)
  have hbij : S.card = T.card := by
    refine card_bij (fun x _ i ↦ !x i) (fun x hx ↦ ?_) (fun x _ y _ hxy ↦ ?_) (fun y hy ↦ ?_)
    · have hxS : f x = true := (mem_filter.mp hx).2
      exact mem_filter.mpr ⟨mem_univ _, by rw [hf.eval_not, hxS]; simp⟩
    · funext i
      exact Bool.not_inj (congrFun hxy i)
    · refine ⟨fun i ↦ !y i, ?_, funext fun i ↦ Bool.not_not (y i)⟩
      have hyT : ¬f y = true := (mem_filter.mp hy).2
      have hyF : f y = false := Bool.eq_false_iff.mpr hyT
      exact mem_filter.mpr ⟨mem_univ _, by rw [hf.eval_not, hyF]; simp⟩
  rw [randomSatProb, div_eq_iff (by positivity)]
  have h2 : (2 : ℝ) * (S.card : ℝ) = 2 ^ k := by exact_mod_cast (by omega : 2 * S.card = 2 ^ k)
  change (S.card : ℝ) = 1 / 2 * 2 ^ k
  linarith

theorem abs_boolFourierCoeff_le_boolFourierCoeff_empty {k : ℕ} (f : Cslib.BooleanFunction k)
    (S : Finset (Fin k)) : |boolFourierCoeff f S| ≤ boolFourierCoeff f ∅ := by
  rw [boolFourierCoeff, boolFourierCoeff, fourierCoeff_empty]
  refine (abs_fourierCoeff_le_expect_abs _ S).trans_eq ?_
  refine congrArg (univ.expect ·) (funext fun x ↦ abs_of_nonneg ?_)
  cases f x <;> norm_num

theorem abs_sum_chowCoeff_mul_signVal_le {k : ℕ} (f : Cslib.BooleanFunction k)
    (x : Cslib.BitString k) :
    |∑ i : Fin k, chowCoeff f i * signVal (x i)| ≤ boolFourierCoeff f ∅ * k := by
  calc
    |∑ i : Fin k, chowCoeff f i * signVal (x i)|
      ≤ ∑ i : Fin k, |chowCoeff f i * signVal (x i)| := abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin k, |chowCoeff f i| := by
        refine sum_congr rfl fun i _ ↦ ?_
        rw [abs_mul, abs_signVal, mul_one]
    _ ≤ ∑ _i : Fin k, boolFourierCoeff f ∅ :=
        sum_le_sum fun i _ ↦ abs_boolFourierCoeff_le_boolFourierCoeff_empty f {i}
    _ = boolFourierCoeff f ∅ * k := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

theorem sum_chowCoeff_mul_signVal_bounds {k : ℕ} (f : Cslib.BooleanFunction k)
    (x : Cslib.BitString k) :
    -(boolFourierCoeff f ∅ * k) ≤ ∑ i : Fin k, chowCoeff f i * signVal (x i) ∧
      ∑ i : Fin k, chowCoeff f i * signVal (x i) ≤ boolFourierCoeff f ∅ * k :=
  abs_le.mp (abs_sum_chowCoeff_mul_signVal_le f x)

/-! ### 3. Chow-defined LTFs and Chow margin -/

/-- Zero-threshold LTF defined by its degree-`1` Chow parameters. -/
@[expose] def IsChowDefinedLTF {k : ℕ} (f : Cslib.BooleanFunction k) : Prop :=
  ∀ x : Cslib.BitString k, f x = posSign (∑ i : Fin k, chowCoeff f i * signVal (x i))

/-- Minimum Chow linear form over satisfying inputs (`0` when unsatisfiable). -/
@[expose] noncomputable def chowMargin {k : ℕ} (f : Cslib.BooleanFunction k) : ℝ :=
  if h : (univ.filter fun x : Cslib.BitString k ↦ f x = true).Nonempty then
    (univ.filter fun x : Cslib.BitString k ↦ f x = true).inf' h
      (fun x ↦ ∑ i : Fin k, chowCoeff f i * signVal (x i))
  else 0

theorem exists_eq_true_and_sum_eq_chowMargin {k : ℕ} {f : Cslib.BooleanFunction k}
    (hsat : ∃ x, f x = true) :
    ∃ x : Cslib.BitString k, f x = true ∧
      ∑ i : Fin k, chowCoeff f i * signVal (x i) = chowMargin f := by
  rcases hsat with ⟨x₀, hx₀⟩
  have hne : (univ.filter fun y : Cslib.BitString k ↦ f y = true).Nonempty :=
    ⟨x₀, mem_filter.mpr ⟨mem_univ x₀, hx₀⟩⟩
  obtain ⟨x, hxmem, hxeq⟩ := exists_mem_eq_inf' hne
    (fun y ↦ ∑ i : Fin k, chowCoeff f i * signVal (y i))
  refine ⟨x, (mem_filter.mp hxmem).2, ?_⟩
  rw [chowMargin, dite_eq_left hne, hxeq]

theorem chowMargin_pos_of_isChowDefinedLTF {k : ℕ} {f : Cslib.BooleanFunction k}
    (hf : IsChowDefinedLTF f) (hsat : ∃ x, f x = true) : 0 < chowMargin f := by
  obtain ⟨x, hx, hsum⟩ := exists_eq_true_and_sum_eq_chowMargin hsat
  rw [← hsum]
  exact posSign_eq_true_iff.mp ((hf x).symm.trans hx)

theorem pos_chowMargin_add_randomSatProb_mul_card {k : ℕ} {f : Cslib.BooleanFunction k}
    (hk : 0 < k) (hsat : ∃ x, f x = true) :
    0 < chowMargin f + randomSatProb f * k := by
  obtain ⟨x, hx, hsum⟩ := exists_eq_true_and_sum_eq_chowMargin hsat
  rw [← hsum]
  have hrewrite : (∑ i : Fin k, chowCoeff f i * signVal (x i)) + randomSatProb f * k =
      ∑ i : Fin k, (chowCoeff f i * signVal (x i) + randomSatProb f) := by
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm (k : ℝ)]
  rw [hrewrite]
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, mem_univ _⟩
  refine sum_pos (fun i _ ↦ ?_) hne
  rw [chowCoeff, boolFourierCoeff, fourierCoeff_eq_sum, randomSatProb_eq_boolFourierCoeff_empty,
    boolFourierCoeff, fourierCoeff_eq_sum, Fintype.card_fin]
  have hcomb : (∑ y : Cslib.BitString k, bitVal ℝ (f y) * chi ℝ {i} y) / 2 ^ k * signVal (x i) +
      (∑ y : Cslib.BitString k, bitVal ℝ (f y) * chi ℝ ∅ y) / 2 ^ k =
      (∑ y : Cslib.BitString k,
        bitVal ℝ (f y) * (signVal (y i) * signVal (x i) + 1)) / 2 ^ k := by
    rw [div_mul_eq_mul_div, ← add_div]
    congr 1
    rw [sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [chi_singleton, chi_empty]
    ring
  rw [hcomb]
  refine div_pos ?_ (by positivity)
  refine sum_pos' (fun y _ ↦ ?_) ⟨x, mem_univ x, ?_⟩
  · refine mul_nonneg (by cases f y <;> norm_num) ?_
    cases y i <;> cases x i <;> norm_num
  · rw [hx, bitVal_true, signVal_mul_self]
    norm_num

/-! ### 4. Monarchy, weak monarchy, and low-arity balanced LTF classification -/

/-- Weight vector `(j, 1, …, 1)` of a presidential / weak monarchy predicate. -/
@[expose] def weakMonarchyWeights (k : ℕ) (j : ℤ) (i : Fin k) : ℝ :=
  if (i : ℕ) = 0 then (j : ℝ) else 1

/-- Weak monarchy predicate with leading weight `j` and unit remaining weights. -/
@[expose] noncomputable def weakMonarchy (k : ℕ) (j : ℤ) : Cslib.BooleanFunction k :=
  linearThreshold (weakMonarchyWeights k j) 0

/-- Pure monarchy predicate with leading weight `k - 2` and unit remaining weights. -/
@[expose] noncomputable def monarchy (k : ℕ) : Cslib.BooleanFunction k :=
  weakMonarchy k ((k : ℤ) - 2)

theorem sum_weakMonarchyWeights {k : ℕ} (hk : 1 ≤ k) (j : ℤ) (x : Cslib.BitString k) :
    ∑ i : Fin k, weakMonarchyWeights k j i * signVal (x i) =
      (j : ℝ) * signVal (x ⟨0, hk⟩) +
        ∑ i ∈ univ.erase ⟨0, hk⟩, signVal (x i) := by
  rw [← add_sum_erase _ _ (mem_univ ⟨0, hk⟩)]
  simp only [weakMonarchyWeights, ↓reduceIte]
  refine congrArg ((j : ℝ) * signVal (x ⟨0, hk⟩) + ·) (sum_congr rfl fun i hi ↦ ?_)
  have hne : (i : ℕ) ≠ 0 := fun h0 ↦ (ne_of_mem_erase hi) (Fin.ext h0)
  simp only [hne, ↓reduceIte, one_mul]

private theorem sum_mod_two_of_forall_mod_two_eq_one {α : Type*} (s : Finset α)
    (g : α → ℤ) (hg : ∀ a ∈ s, g a % 2 = 1) : (∑ a ∈ s, g a) % 2 = (s.card : ℤ) % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    have hga : g a % 2 = 1 := hg a (mem_insert_self a s)
    have hgs : (∑ x ∈ s, g x) % 2 = (s.card : ℤ) % 2 := ih fun x hx ↦ hg x (mem_insert_of_mem hx)
    omega

theorem isBalancedLTF_weakMonarchy {k : ℕ} {j : ℤ} (hk : 1 ≤ k) (heven : Even ((k : ℤ) + j)) :
    IsBalancedLTF (weakMonarchy k j) := by
  refine ⟨weakMonarchyWeights k j, fun x ↦ ?_, rfl⟩
  rw [sum_weakMonarchyWeights hk j x]
  let zBit (b : Bool) : ℤ := if b then -1 else 1
  have hzCast (b : Bool) : signVal b = (zBit b : ℝ) := by
    cases b <;> simp [zBit]
  have hzMod (b : Bool) : zBit b % 2 = 1 := by
    cases b <;> decide
  set Z : ℤ := j * zBit (x ⟨0, hk⟩) + ∑ i ∈ univ.erase (⟨0, hk⟩ : Fin k), zBit (x i)
  have hcast : (j : ℝ) * signVal (x ⟨0, hk⟩) + ∑ i ∈ univ.erase ⟨0, hk⟩, signVal (x i) =
      (Z : ℝ) := by
    simp only [Z, hzCast, Int.cast_add, Int.cast_mul, Int.cast_sum]
  rw [hcast]
  intro h0
  have hZ0 : Z = 0 := Int.cast_eq_zero.mp h0
  have hcard : (univ.erase (⟨0, hk⟩ : Fin k)).card = k - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have hsumMod :
      (∑ i ∈ univ.erase (⟨0, hk⟩ : Fin k), zBit (x i)) % 2 = ((k - 1 : ℕ) : ℤ) % 2 := by
    rw [sum_mod_two_of_forall_mod_two_eq_one _ _ (fun i _ ↦ hzMod (x i)), hcard]
  have hjMod : (j * zBit (x ⟨0, hk⟩)) % 2 = j % 2 := by
    rw [Int.mul_emod, hzMod, mul_one, Int.emod_emod]
  rcases heven with ⟨r, hr⟩
  have hodd : Z % 2 = 1 := by
    dsimp only [Z]
    rw [Int.add_emod, hjMod, hsumMod, ← Int.add_emod]
    omega
  omega

theorem isBalancedLTF_monarchy {k : ℕ} (hk : 2 ≤ k) : IsBalancedLTF (monarchy k) := by
  refine isBalancedLTF_weakMonarchy (by omega) ?_
  exact ⟨(k : ℤ) - 1, by ring⟩

/-- Coordinate permutation and literal negation on `BooleanFunction k`. -/
@[expose] def relabelLiterals {k : ℕ} (b : Cslib.BitString k) (π : Equiv.Perm (Fin k))
    (f : Cslib.BooleanFunction k) : Cslib.BooleanFunction k :=
  fun x ↦ f (fun i ↦ b i ^^ x (π i))

theorem relabelLiterals_symm {k : ℕ} (b : Cslib.BitString k) (π : Equiv.Perm (Fin k))
    (f : Cslib.BooleanFunction k) :
    relabelLiterals (fun j ↦ b (π.symm j)) π.symm (relabelLiterals b π f) = f := by
  funext x
  simp only [relabelLiterals, Equiv.symm_apply_apply, ← Bool.xor_assoc,
    Bool.xor_self, Bool.false_xor]

/-- Dictator on coordinate `0` (`x ↦ !x 0`). -/
@[expose] def dictatorZero (k : ℕ) (hk : 0 < k) : Cslib.BooleanFunction k :=
  fun x ↦ !x ⟨0, hk⟩

theorem isChowDefinedLTF_dictatorZero {k : ℕ} (hk : 0 < k) :
    IsChowDefinedLTF (dictatorZero k hk) := by
  let i₀ : Fin k := ⟨0, hk⟩
  have hval : (fun x : Cslib.BitString k ↦ bitVal ℝ (dictatorZero k hk x)) =
      fun x ↦ (1 / 2 : ℝ) * chi ℝ ∅ x + (1 / 2 : ℝ) * chi ℝ {i₀} x := by
    funext x
    simp only [dictatorZero, chi_empty, chi_singleton, mul_one]
    cases x i₀ <;> norm_num
  have hchow (i : Fin k) : chowCoeff (dictatorZero k hk) i = if i = i₀ then 1 / 2 else 0 := by
    rw [chowCoeff, boolFourierCoeff, hval, fourierCoeff_add, fourierCoeff_const_mul,
      fourierCoeff_const_mul, fourierCoeff_chi, fourierCoeff_chi]
    have hempty : (∅ : Finset (Fin k)) ≠ {i} := Finset.empty_ne_singleton (a := i)
    have hsing : ({i₀} : Finset (Fin k)) = {i} ↔ i = i₀ := by
      rw [Finset.singleton_inj, eq_comm]
    simp only [hempty, ↓reduceIte, mul_zero, zero_add, hsing, mul_ite, mul_one]
  intro x
  simp only [hchow, ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [posSign_mul_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  cases h : x i₀ <;> simp [dictatorZero, i₀, h, posSign]

/-- Strict majority on the first `3` coordinates. -/
@[expose] noncomputable def majorityFirstThree (k : ℕ) (hk : 3 ≤ k) : Cslib.BooleanFunction k :=
  fun x ↦ posSign (signVal (x ⟨0, by omega⟩) + signVal (x ⟨1, by omega⟩) +
    signVal (x ⟨2, by omega⟩))

theorem isChowDefinedLTF_majorityFirstThree {k : ℕ} (hk : 3 ≤ k) :
    IsChowDefinedLTF (majorityFirstThree k hk) := by
  let i₀ : Fin k := ⟨0, by omega⟩
  let i₁ : Fin k := ⟨1, by omega⟩
  let i₂ : Fin k := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h ↦ by have := congrArg Fin.val h; dsimp [i₀, i₁] at this; omega
  have h02 : i₀ ≠ i₂ := fun h ↦ by have := congrArg Fin.val h; dsimp [i₀, i₂] at this; omega
  have h12 : i₁ ≠ i₂ := fun h ↦ by have := congrArg Fin.val h; dsimp [i₁, i₂] at this; omega
  have hval : (fun x : Cslib.BitString k ↦ bitVal ℝ (majorityFirstThree k hk x)) =
      fun x ↦ (1 / 2 : ℝ) * chi ℝ ∅ x + (1 / 4 : ℝ) * chi ℝ {i₀} x +
        (1 / 4 : ℝ) * chi ℝ {i₁} x + (1 / 4 : ℝ) * chi ℝ {i₂} x +
        (-1 / 4 : ℝ) * chi ℝ ({i₀, i₁, i₂} : Finset (Fin k)) x := by
    funext x
    have hprod : chi ℝ ({i₀, i₁, i₂} : Finset (Fin k)) x =
        signVal (x i₀) * (signVal (x i₁) * signVal (x i₂)) := by
      rw [chi_eq_prod_signVal, prod_insert (by simp [h01, h02]),
        prod_insert (by simp [h12]), prod_singleton]
    simp only [majorityFirstThree, i₀, i₁, i₂] at hprod ⊢
    rw [hprod, chi_empty, chi_singleton, chi_singleton, chi_singleton, bitVal_posSign]
    cases x i₀ <;> cases x i₁ <;> cases x i₂ <;> norm_num
  have hcard3 : ({i₀, i₁, i₂} : Finset (Fin k)).card = 3 := by
    rw [card_insert_of_notMem (by simp [h01, h02]), card_insert_of_notMem (by simp [h12]),
      card_singleton]
  have hchow (i : Fin k) : chowCoeff (majorityFirstThree k hk) i =
      if i = i₀ ∨ i = i₁ ∨ i = i₂ then 1 / 4 else 0 := by
    rw [chowCoeff, boolFourierCoeff, hval]
    repeat rw [fourierCoeff_add]
    repeat rw [fourierCoeff_const_mul]
    repeat rw [fourierCoeff_chi]
    have hne0 : (∅ : Finset (Fin k)) ≠ {i} := Finset.empty_ne_singleton (a := i)
    have hne3 : ({i₀, i₁, i₂} : Finset (Fin k)) ≠ {i} := fun heq ↦ by
      have hc := congrArg Finset.card heq
      rw [hcard3, card_singleton] at hc
      omega
    simp only [hne0, hne3, ↓reduceIte, mul_zero, zero_add, add_zero, Finset.singleton_inj]
    by_cases h0 : i = i₀
    · subst h0; simp [h01, h02, Ne.symm h01, Ne.symm h02]
    · by_cases h1 : i = i₁
      · subst h1; simp [h01, h12, Ne.symm h01, Ne.symm h12]
      · by_cases h2 : i = i₂
        · subst h2; simp [h02, h12, Ne.symm h02, Ne.symm h12]
        · simp [h0, h1, h2, Ne.symm h0, Ne.symm h1, Ne.symm h2]
  intro x
  have hsum : ∑ i : Fin k, chowCoeff (majorityFirstThree k hk) i * signVal (x i) =
      (1 / 4 : ℝ) * (signVal (x i₀) + signVal (x i₁) + signVal (x i₂)) := by
    simp_rw [hchow]
    have hfilter : (univ.filter fun i : Fin k ↦ i = i₀ ∨ i = i₁ ∨ i = i₂) = {i₀, i₁, i₂} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    rw [show (∑ i : Fin k, (if i = i₀ ∨ i = i₁ ∨ i = i₂ then (1 / 4 : ℝ) else 0) * signVal (x i)) =
        ∑ i ∈ univ.filter (fun i : Fin k ↦ i = i₀ ∨ i = i₁ ∨ i = i₂),
          (1 / 4 : ℝ) * signVal (x i) by
      rw [sum_filter]
      exact sum_congr rfl fun i _ ↦ by split_ifs <;> ring]
    rw [hfilter, sum_insert (by simp [h01, h02]), sum_insert (by simp [h12]), sum_singleton]
    ring
  rw [hsum, posSign_mul_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  rfl

/-- Every balanced LTF on `k ≤ 4` variables is equivalent via literal negation and coordinate
permutation either to a Chow-defined LTF or, at `k = 4`, to `monarchy 4`. -/
theorem balancedLTF_le_four_classification {k : ℕ} (hk : k ≤ 4) {f : Cslib.BooleanFunction k}
    (hf : IsBalancedLTF f) :
    ∃ (b : Cslib.BitString k) (π : Equiv.Perm (Fin k)),
      IsChowDefinedLTF (relabelLiterals b π f) ∨
        ∃ h4 : k = 4, relabelLiterals b π f = h4 ▸ monarchy 4 := by
  have hkpos : 0 < k := hf.arity_pos
  rcases hf with ⟨w, hw, rfl⟩
  let σ : Equiv.Perm (Fin k) := Tuple.sortDesc (fun i ↦ |w i|)
  let b : Cslib.BitString k := fun i ↦ decide (w i < 0)
  let u : Fin k → ℝ := fun j ↦ |w (σ j)|
  have hu_anti : Antitone u := Tuple.antitone_sortDesc (fun i ↦ |w i|)
  have hu_nonneg (j : Fin k) : 0 ≤ u j := abs_nonneg _
  have hsum_eq (y : Cslib.BitString k) :
      ∑ i, w i * signVal (b i ^^ y (σ.symm i)) = ∑ j, u j * signVal (y j) := by
    rw [← Equiv.sum_comp σ]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [Equiv.symm_apply_apply, signVal_xor, u, b]
    by_cases hneg : w (σ j) < 0
    · simp only [hneg, decide_true, signVal_true, abs_of_neg hneg]
      ring
    · simp only [hneg, decide_false, signVal_false, abs_of_nonneg (not_lt.mp hneg)]
      ring
  have hrel : relabelLiterals b σ.symm (linearThreshold w 0) = linearThreshold u 0 := by
    funext y
    simp only [relabelLiterals, linearThreshold_zero_apply, hsum_eq y]
  have hu_ne (y : Cslib.BitString k) : ∑ j, u j * signVal (y j) ≠ 0 := by
    intro h0
    exact hw (fun i ↦ b i ^^ y (σ.symm i)) ((hsum_eq y).trans h0)
  refine ⟨b, σ.symm, ?_⟩
  rw [hrel]
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl
  · left
    have hu0 : 0 < u 0 := lt_of_le_of_ne (hu_nonneg 0) (Ne.symm fun h0 ↦
      hu_ne (fun _ ↦ false) (by rw [Fin.sum_univ_one]; simp [h0]))
    have heq : linearThreshold u 0 = dictatorZero 1 (by omega) := by
      funext y
      rw [linearThreshold_zero_apply, Fin.sum_univ_one, posSign_mul_pos hu0]
      cases h : y 0 <;> simp [dictatorZero, h, posSign]
    rw [heq]
    exact isChowDefinedLTF_dictatorZero (by omega)
  · left
    have hge : u 1 ≤ u 0 := hu_anti (by decide : (0 : Fin 2) ≤ 1)
    have hne : u 0 - u 1 ≠ 0 := by
      intro h0
      refine hu_ne (fun i ↦ if i = 0 then false else true) ?_
      rw [Fin.sum_univ_two]
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [↓reduceIte, h10, signVal_false, signVal_true]
      linarith
    have hgt : u 1 < u 0 := lt_of_le_of_ne hge fun h ↦ hne (by linarith)
    have heq : linearThreshold u 0 = dictatorZero 2 (by omega) := by
      funext y
      rw [linearThreshold_zero_apply, Fin.sum_univ_two]
      change posSign (u 0 * signVal (y 0) + u 1 * signVal (y 1)) = !y 0
      cases hy0 : y 0 <;> cases y 1 <;>
        simp only [signVal_false, signVal_true, Bool.not_false, Bool.not_true,
          posSign_eq_true_iff, posSign_eq_false_iff] <;>
        linarith [hu_nonneg 1]
    rw [heq]
    exact isChowDefinedLTF_dictatorZero (by omega)
  · left
    have h01 : u 1 ≤ u 0 := hu_anti (by decide : (0 : Fin 3) ≤ 1)
    have h12 : u 2 ≤ u 1 := hu_anti (by decide : (1 : Fin 3) ≤ 2)
    have h2 : 0 ≤ u 2 := hu_nonneg 2
    have hne : u 0 - u 1 - u 2 ≠ 0 := by
      intro h0
      exact hu_ne (fun i ↦ if i = 0 then false else true) (by
        rw [Fin.sum_univ_three]
        simp only [↓reduceIte, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
          signVal_false, signVal_true]
        linarith)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have heq : linearThreshold u 0 = majorityFirstThree 3 (by omega) := by
        funext y
        rw [linearThreshold_zero_apply, Fin.sum_univ_three]
        change posSign (u 0 * signVal (y 0) + u 1 * signVal (y 1) + u 2 * signVal (y 2)) =
          posSign (signVal (y 0) + signVal (y 1) + signVal (y 2))
        rw [Bool.eq_iff_iff, posSign_eq_true_iff, posSign_eq_true_iff]
        cases y 0 <;> cases y 1 <;> cases y 2 <;>
          simp only [signVal_false, signVal_true] <;>
          constructor <;> intro h <;> linarith
      rw [heq]
      exact isChowDefinedLTF_majorityFirstThree (by omega)
    · have heq : linearThreshold u 0 = dictatorZero 3 (by omega) := by
        funext y
        rw [linearThreshold_zero_apply, Fin.sum_univ_three]
        change posSign (u 0 * signVal (y 0) + u 1 * signVal (y 1) + u 2 * signVal (y 2)) = !y 0
        cases hy0 : y 0 <;> cases y 1 <;> cases y 2 <;>
          simp only [signVal_false, signVal_true, Bool.not_false, Bool.not_true,
            posSign_eq_true_iff, posSign_eq_false_iff] <;>
          linarith
      rw [heq]
      exact isChowDefinedLTF_dictatorZero (by omega)
  · have h01 : u 1 ≤ u 0 := hu_anti (by decide : (0 : Fin 4) ≤ 1)
    have h12 : u 2 ≤ u 1 := hu_anti (by decide : (1 : Fin 4) ≤ 2)
    have h23 : u 3 ≤ u 2 := hu_anti (by decide : (2 : Fin 4) ≤ 3)
    have h3 : 0 ≤ u 3 := hu_nonneg 3
    have hneA : u 0 - u 1 - u 2 - u 3 ≠ 0 := by
      intro h0
      exact hu_ne (fun i ↦ if i = 0 then false else true) (by
        rw [Fin.sum_univ_four]
        simp only [↓reduceIte, show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
          show (3 : Fin 4) ≠ 0 by decide, signVal_false, signVal_true]
        linarith)
    have hneB : u 0 - u 1 - u 2 + u 3 ≠ 0 := by
      intro h0
      exact hu_ne (fun i ↦ if i = 0 ∨ i = 3 then false else true) (by
        rw [Fin.sum_univ_four]
        have hf0 : (if (0 : Fin 4) = 0 ∨ (0 : Fin 4) = 3 then false else true) = false := by decide
        have hf1 : (if (1 : Fin 4) = 0 ∨ (1 : Fin 4) = 3 then false else true) = true := by decide
        have hf2 : (if (2 : Fin 4) = 0 ∨ (2 : Fin 4) = 3 then false else true) = true := by decide
        have hf3 : (if (3 : Fin 4) = 0 ∨ (3 : Fin 4) = 3 then false else true) = false := by decide
        rw [hf0, hf1, hf2, hf3]
        simp only [signVal_false, signVal_true]
        linarith)
    rcases lt_or_gt_of_ne hneA with hltA | hgtA
    · rcases lt_or_gt_of_ne hneB with hltB | hgtB
      · left
        have heq : linearThreshold u 0 = majorityFirstThree 4 (by omega) := by
          funext y
          rw [linearThreshold_zero_apply, Fin.sum_univ_four]
          change posSign (u 0 * signVal (y 0) + u 1 * signVal (y 1) + u 2 * signVal (y 2) +
              u 3 * signVal (y 3)) =
            posSign (signVal (y 0) + signVal (y 1) + signVal (y 2))
          rw [Bool.eq_iff_iff, posSign_eq_true_iff, posSign_eq_true_iff]
          cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;>
            simp only [signVal_false, signVal_true] <;>
            constructor <;> intro h <;> linarith
        rw [heq]
        exact isChowDefinedLTF_majorityFirstThree (by omega)
      · right
        refine ⟨rfl, ?_⟩
        funext y
        dsimp only
        rw [linearThreshold_zero_apply, monarchy, weakMonarchy, linearThreshold_zero_apply,
          Fin.sum_univ_four, Fin.sum_univ_four]
        have hw0 : weakMonarchyWeights 4 (((4 : ℕ) : ℤ) - 2) 0 = 2 := by
          simp [weakMonarchyWeights]
        have hw1 : weakMonarchyWeights 4 (((4 : ℕ) : ℤ) - 2) 1 = 1 := by
          simp [weakMonarchyWeights]
        have hw2 : weakMonarchyWeights 4 (((4 : ℕ) : ℤ) - 2) 2 = 1 := by
          simp [weakMonarchyWeights]
        have hw3 : weakMonarchyWeights 4 (((4 : ℕ) : ℤ) - 2) 3 = 1 := by
          simp [weakMonarchyWeights]
        rw [hw0, hw1, hw2, hw3, Bool.eq_iff_iff, posSign_eq_true_iff, posSign_eq_true_iff]
        cases y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;>
          simp only [signVal_false, signVal_true] <;>
          constructor <;> intro h <;> linarith
    · left
      have heq : linearThreshold u 0 = dictatorZero 4 (by omega) := by
        funext y
        rw [linearThreshold_zero_apply, Fin.sum_univ_four]
        change posSign (u 0 * signVal (y 0) + u 1 * signVal (y 1) + u 2 * signVal (y 2) +
            u 3 * signVal (y 3)) = !y 0
        cases hy0 : y 0 <;> cases y 1 <;> cases y 2 <;> cases y 3 <;>
          simp only [signVal_false, signVal_true, Bool.not_false, Bool.not_true,
            posSign_eq_true_iff, posSign_eq_false_iff] <;>
          linarith
      rw [heq]
      exact isChowDefinedLTF_dictatorZero (by omega)

end CslibFrontier.BooleanAnalysis
