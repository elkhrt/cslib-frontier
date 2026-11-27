/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Basic.Real.Basic
public import CslibFrontier.Computability.QueryComplexity.Quantum.ExactComposition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact Quantum Query Complexity of Symmetric Functions

This module formalizes symmetric functions on `BitString n`, the `MOD_m^n`, `EXACT_k^n`, and
`EXACT_{k,l}^n` families, majority indices, and the foundational exact quantum query complexity
results used across symmetric query complexity under standard Lean axioms:

* Arithmetic identity `⌈n (1 - 1/m)⌉ = n - ⌊n / m⌋`.
* The `MOD_m^n` lower bound `Q_E(MOD_m^n) ≥ ⌈n (1 - 1/m)⌉` for `1 < m ≤ n`
.
* The exact characterization `Q_E(EXACT_k^n) = max k (n - k)`,
  proved via the 1-query linear-isometry pair-finder subroutine `readoutSpecInMod_aisPairFinder`.
* The `EXACT_{k,l}^n` lower bound `Q_E(EXACT_{k,l}^n) ≥ max (n - k) l - 1` and the 3-query
  exact algorithm for `EXACT_{1,4}^5` with a majority-index witness
.

## Main definitions

* `CslibFrontier.Quantum.lcmModulus`: `lcm {1..., n}`, providing a single positive modulus
  divisible by every `m ∈ {1..., n}`.
* `CslibFrontier.Quantum.IsSymmetricFun`, `CslibFrontier.Quantum.univariateOf`: symmetric
  functions on `BitString n` and their univariate representation.
* `CslibFrontier.Quantum.modFun`, `CslibFrontier.Quantum.exactFun`,
  `CslibFrontier.Quantum.exactPairFun`: the functions `MOD_m^n`, `EXACT_k^n`, and
  `EXACT_{k,l}^n`.
* `CslibFrontier.Quantum.IsMajorityIndex`: majority-index predicate for strings with
  `2 * weight x ≠ n`.

## Main results

* `CslibFrontier.Quantum.exactQuantumQueryComplexity_mod_ge`:
  `⌈n (1 - 1/m)⌉ ≤ Q_E(MOD_m^n)`.
* `CslibFrontier.Quantum.exactQuantumQueryComplexity_exact_eq`:
  `Q_E(EXACT_k^n) = max k (n - k)`.
* `CslibFrontier.Quantum.exactQuantumQueryComplexity_exactPair_ge`:
  `max (n - k) l - 1 ≤ Q_E(EXACT_{k,l}^n)`.
* `CslibFrontier.Quantum.readoutSpecInMod_exactOneFourFive`: 3-query exact algorithm for
  `EXACT_{1,4}^5` returning a majority index whenever `weight x ∈ {1, 4}`.
-/

public section

namespace CslibFrontier.Quantum

open Cslib Cslib.BitString Cslib.Quantum Finset

/-! ### Common modulus, Hamming-weight helpers, and symmetric function families -/

section Definitions

/-- Least common multiple of `{1, ..., n}` (`1` for `n = 0`). -/
def lcmModulus : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmModulus n) (n + 1)

theorem lcmModulus_pos (n : ℕ) : 0 < lcmModulus n := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih => exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero ih.ne' (Nat.succ_ne_zero n))

instance instNeZeroLcmModulus (n : ℕ) : NeZero (lcmModulus n) :=
  ⟨(lcmModulus_pos n).ne'⟩

theorem dvd_lcmModulus {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : m ∣ lcmModulus n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · exact Nat.dvd_lcm_right _ _
    · exact (ih (Nat.le_of_lt_succ hlt)).trans (Nat.dvd_lcm_left _ _)

theorem lcmModulus_dvd_of_le {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : lcmModulus n₁ ∣ lcmModulus n₂ := by
  induction n₂, h using Nat.le_induction with
  | base => exact dvd_refl _
  | succ k _ ih => exact ih.trans (Nat.dvd_lcm_left _ _)

/-- Canonical `n`-bit string whose first `k` coordinates are `true` (weight `min k n`). -/
def prefixString (n k : ℕ) : BitString n := fun i => decide (i.1 < k)

@[simp]
theorem weight_prefixString (n k : ℕ) : weight (prefixString n k) = min k n := by
  unfold weight prefixString
  rw [← Finset.card_fin (min k n)]
  exact Finset.card_bij
    (fun (i : Fin n) (hi : i ∈ Finset.univ.filter (fun i : Fin n => decide (i.1 < k) = true)) =>
      (⟨i.1, lt_min (decide_eq_true_eq.mp (Finset.mem_filter.mp hi).2) i.2⟩ : Fin (min k n)))
    (fun _ _ => mem_univ _)
    (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun j _ => ⟨⟨j.1, lt_of_lt_of_le j.2 (Nat.min_le_right k n)⟩,
      Finset.mem_filter.mpr ⟨mem_univ _,
        decide_eq_true (lt_of_lt_of_le j.2 (Nat.min_le_left k n))⟩,
      Fin.ext rfl⟩)

/-- Reindexing coordinates by an equivalence preserves Hamming weight. -/
theorem weight_comp_equiv {n m : ℕ} (e : Fin n ≃ Fin m) (x : BitString m) :
    weight (x ∘ e) = weight x := by
  unfold weight
  exact Finset.card_bij (fun i _ => e i)
    (fun i hi => by simpa using hi)
    (fun _ _ _ _ h => e.injective h)
    (fun j hj => ⟨e.symm j, by simpa using hj, by simp⟩)

/-- Weight of a string after deleting coordinate `i₀` via `Fin.succAbove`. -/
theorem weight_eq_weight_succAbove_add {n : ℕ} (i₀ : Fin (n + 1)) (x : BitString (n + 1)) :
    weight x = weight (x ∘ i₀.succAbove) + (if x i₀ then 1 else 0) := by
  unfold weight
  have hpart : (Finset.univ.filter (fun i : Fin (n + 1) => x i = true)).card =
      ((Finset.univ.filter (fun i : Fin (n + 1) => x i = true)).erase i₀).card +
        (if x i₀ then 1 else 0) := by
    by_cases hx : x i₀ = true
    · have hmem : i₀ ∈ Finset.univ.filter (fun i : Fin (n + 1) => x i = true) :=
        Finset.mem_filter.mpr ⟨mem_univ _, hx⟩
      simp only [hx, ↓reduceIte]
      exact (Finset.card_erase_add_one hmem).symm
    · have hnot : i₀ ∉ Finset.univ.filter (fun i : Fin (n + 1) => x i = true) := by
        simp [hx]
      simp [hx, hnot]
  rw [hpart]
  congr 1
  symm
  refine Finset.card_bij (fun j _ => i₀.succAbove j)
    (fun j hj => Finset.mem_erase.mpr ⟨i₀.succAbove_ne j,
      Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp hj).2⟩⟩)
    (fun _ _ _ _ h => i₀.succAbove_right_injective h)
    (fun i hi => ?_)
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hi
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hne
  exact ⟨j, Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp hmem).2⟩, rfl⟩

/-- Weight of a concatenation of a `k`-bit string and an `r`-bit string. -/
theorem weight_concat {k r : ℕ} (y : BitString k) (z : BitString r) :
    weight (fun i : Fin (k + r) => if hi : i.1 < k then y ⟨i.1, hi⟩ else z ⟨i.1 - k, by omega⟩) =
      weight y + weight z := by
  let x : BitString (k + r) :=
    fun i => if hi : i.1 < k then y ⟨i.1, hi⟩ else z ⟨i.1 - k, by omega⟩
  have hsplit : (Finset.univ.filter (fun i : Fin (k + r) => x i = true)).card =
      (Finset.univ.filter (fun i : Fin (k + r) => i.1 < k ∧ x i = true)).card +
        (Finset.univ.filter (fun i : Fin (k + r) => ¬ i.1 < k ∧ x i = true)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_filter]; intro i _ h1 h2; exact h2.1 h1.1
  change (Finset.univ.filter (fun i : Fin (k + r) => x i = true)).card = weight y + weight z
  rw [hsplit]
  congr 1
  · refine Finset.card_bij
      (fun i hi => (⟨i.1, (Finset.mem_filter.mp hi).2.1⟩ : Fin k))
      (fun i hi => by
        have h := (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr ⟨mem_univ _, by simpa [x, h.1] using h.2⟩)
      (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
      (fun j hj => ⟨⟨j.1, by omega⟩,
        Finset.mem_filter.mpr ⟨mem_univ _, j.2, by
          simpa [x, j.2] using (Finset.mem_filter.mp hj).2⟩,
        Fin.ext rfl⟩)
  · refine Finset.card_bij
      (fun i hi => (⟨i.1 - k, by have := (Finset.mem_filter.mp hi).2.1; omega⟩ : Fin r))
      (fun i hi => by
        have h := (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr ⟨mem_univ _, by simpa [x, h.1] using h.2⟩)
      (fun i₁ hi₁ i₂ hi₂ h => by
        have h1 := (Finset.mem_filter.mp hi₁).2.1
        have h2 := (Finset.mem_filter.mp hi₂).2.1
        have hv : i₁.1 - k = i₂.1 - k := congrArg Fin.val h
        exact Fin.ext (by omega))
      (fun j hj => ⟨⟨k + j.1, by omega⟩,
        Finset.mem_filter.mpr ⟨mem_univ _, by dsimp only; omega, by
          have hnot : ¬ k + j.1 < k := by omega
          simpa [x, hnot] using (Finset.mem_filter.mp hj).2⟩,
        Fin.ext (by dsimp; omega)⟩)

/-- A function `f : BitString n → X` is symmetric if it depends only on the Hamming weight. -/
@[expose]
def IsSymmetricFun {n : ℕ} {X : Type*} (f : BitString n → X) : Prop :=
  ∀ x y : BitString n, weight x = weight y → f x = f y

/-- Univariate representation `F : ℕ → X` of `f : BitString n → X`, defined by
`F k = f (prefixString n k)`. For symmetric `f`, `F (weight x) = f x` for all `x`. -/
def univariateOf {n : ℕ} {X : Type*} (f : BitString n → X) (k : ℕ) : X :=
  f (prefixString n k)

@[simp]
theorem univariateOf_weight {n : ℕ} {X : Type*} {f : BitString n → X}
    (hf : IsSymmetricFun f) (x : BitString n) :
    univariateOf f (weight x) = f x :=
  hf _ _ (by rw [weight_prefixString, Nat.min_eq_left (weight_le_length x)])

/-- The modular Hamming-weight function `MOD_m^n(x) = |x| mod m` with output in `ZMod m`. -/
def modFun (n m : ℕ) (x : BitString n) : ZMod m :=
  (weight x : ZMod m)

theorem modFun_apply (n m : ℕ) (x : BitString n) : modFun n m x = (weight x : ZMod m) := by
  unfold modFun; rfl

theorem isSymmetricFun_modFun (n m : ℕ) : IsSymmetricFun (modFun n m) := fun _ _ h => by
  simp [modFun, h]

@[simp]
theorem univariateOf_modFun (n m k : ℕ) :
    univariateOf (modFun n m) k = ((min k n : ℕ) : ZMod m) := by
  rw [univariateOf, modFun, weight_prefixString]

/-- The exact-weight Boolean function `EXACT_k^n(x) = decide (|x| = k)`. -/
def exactFun (n k : ℕ) (x : BitString n) : Bool :=
  decide (weight x = k)

theorem exactFun_apply (n k : ℕ) (x : BitString n) :
    exactFun n k x = decide (weight x = k) := by
  unfold exactFun; rfl

@[simp]
theorem exactFun_eq_true {n k : ℕ} {x : BitString n} :
    exactFun n k x = true ↔ weight x = k := by
  simp [exactFun]

/-- The two-weight Boolean function `EXACT_{k,l}^n(x) = decide (|x| = k ∨ |x| = l)`. -/
def exactPairFun (n k l : ℕ) (x : BitString n) : Bool :=
  decide (weight x = k ∨ weight x = l)

theorem exactPairFun_apply (n k l : ℕ) (x : BitString n) :
    exactPairFun n k l x = decide (weight x = k ∨ weight x = l) := by
  unfold exactPairFun; rfl

/-- `i : Fin n` is a majority index of `x : BitString n` if either `|x| > n / 2` and `x i = true`,
or `|x| < n / 2` and `x i = false`. -/
@[expose]
def IsMajorityIndex {n : ℕ} (x : BitString n) (i : Fin n) : Prop :=
  (n < 2 * weight x ∧ x i = true) ∨ (2 * weight x < n ∧ x i = false)

theorem isMajorityIndex_iff {n : ℕ} (x : BitString n) (i : Fin n) :
    IsMajorityIndex x i ↔ (n < 2 * weight x ∧ x i = true) ∨ (2 * weight x < n ∧ x i = false) :=
  Iff.rfl

end Definitions

/-! ### Arithmetic identity and exact query lower bounds -/

section LowerBounds

/-- Arithmetic identity `⌈n (1 - 1 / m)⌉ = n - ⌊n / m⌋` for positive `m`. -/
theorem nat_ceil_one_sub_inv_eq {n m : ℕ} (hm : 0 < m) :
    Nat.ceil ((n : ℝ) * (1 - 1 / (m : ℝ))) = n - n / m := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hle : (n : ℝ) * (1 - 1 / (m : ℝ)) ≤ ((n - n / m : ℕ) : ℝ) := by
    have hdiv_le : n / m ≤ n := Nat.div_le_self n m
    rw [Nat.cast_sub hdiv_le]
    have hdm : ((n / m : ℕ) : ℝ) * (m : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self n m
    have h1 : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / (m : ℝ) := (le_div_iff₀ hmR).mpr hdm
    linarith [show (n : ℝ) * (1 - 1 / (m : ℝ)) = (n : ℝ) - (n : ℝ) / (m : ℝ) by ring]
  rcases Nat.eq_zero_or_pos (n - n / m) with hc0 | hcpos
  · rw [hc0]
    exact Nat.ceil_eq_zero.mpr (by simpa [hc0] using hle)
  · rw [Nat.ceil_eq_iff (Nat.ne_of_gt hcpos)]
    refine ⟨?_, hle⟩
    have hsub : ((n - n / m - 1 : ℕ) : ℝ) = (n : ℝ) - ((n / m : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n - n / m), Nat.cast_sub (Nat.div_le_self n m),
        Nat.cast_one]
    rw [hsub]
    have hlt_dm : (n : ℝ) < (((n / m : ℕ) + 1 : ℕ) : ℝ) * (m : ℝ) := by
      exact_mod_cast (by
        have h := Nat.lt_div_mul_add (a := n) hm
        linarith : n < (n / m + 1) * m)
    have h2 : (n : ℝ) / (m : ℝ) < ((n / m : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hmR]
      simpa [Nat.cast_add, Nat.cast_one] using hlt_dm
    linarith [show (n : ℝ) * (1 - 1 / (m : ℝ)) = (n : ℝ) - (n : ℝ) / (m : ℝ) by ring]

/-- **Lower bound for `MOD_m^n`**:
for `1 < m ≤ n`, `Q_E(MOD_m^n) ≥ ⌈n (1 - 1 / m)⌉`.
-/
theorem exactQuantumQueryComplexity_mod_ge {n m : ℕ} [NeZero m] (hm : 1 < m) (hmn : m ≤ n) :
    Nat.ceil ((n : ℝ) * (1 - 1 / (m : ℝ))) ≤ exactQuantumQueryComplexity (modFun n m) := by
  have hm0 : 0 < m := by omega
  have : NeZero n := ⟨by omega⟩
  rw [nat_ceil_one_sub_inv_eq hm0]
  refine le_exactQuantumQueryComplexity ⟨n, exactQuantumComputableIn_full _⟩ fun T hT => ?_
  let R : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k % m ≠ 0)
  have hcard : R.card = n - n / m := by
    let M : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k % m = 0)
    have hsplit : R.card + M.card = n + 1 := by
      rw [← Finset.card_union_of_disjoint]
      · have hu : R ∪ M = Finset.range (n + 1) := by
          ext k; simp only [R, M, Finset.mem_union, Finset.mem_filter]; tauto
        rw [hu, Finset.card_range]
      · rw [Finset.disjoint_filter]; intro k _ h1 h2; exact h1 h2
    have hM_eq : M = (Finset.range (n / m + 1)).image (fun q => q * m) := by
      ext k
      simp only [M, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hk, hmod⟩
        refine ⟨k / m, ?_, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)⟩
        have : k / m ≤ n / m := Nat.div_le_div_right (Nat.le_of_lt_succ hk)
        omega
      · rintro ⟨q, hq, rfl⟩
        refine ⟨?_, Nat.mul_mod_left q m⟩
        have hqm : q * m ≤ (n / m) * m := Nat.mul_le_mul_right m (Nat.le_of_lt_succ hq)
        have hdm : (n / m) * m ≤ n := Nat.div_mul_le_self n m
        omega
    have hM_card : M.card = n / m + 1 := by
      rw [hM_eq, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hm0 h),
        Finset.card_range]
    omega
  rw [← hcard]
  refine card_le_of_exact_weight_zero hT R (fun k hk => by
    have := (Finset.mem_filter.mp hk).1; rw [Finset.mem_range] at this; omega) fun k hk x hx => ?_
  have hmod : k % m ≠ 0 := (Finset.mem_filter.mp hk).2
  change (weight x : ZMod m) ≠ (weight (fun _ : Fin n => false) : ZMod m)
  rw [hx, show weight (fun _ : Fin n => false) = 0 by simp [weight], Nat.cast_zero]
  intro h0
  exact hmod (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff k m).mp h0))

/-- Subcube map fixing the first `k` coordinates to `true` (when `k ≤ n`). -/
private def prefixTrueMap {n : ℕ} (k : ℕ) (hk : k ≤ n) : BitString (n - k) → BitString n :=
  fun z i => if hi : i.1 < k then true else z ⟨i.1 - k, by omega⟩

private theorem weight_prefixTrueMap {n k : ℕ} (hk : k ≤ n) (z : BitString (n - k)) :
    weight (prefixTrueMap k hk z) = k + weight z := by
  let e : Fin (k + (n - k)) ≃ Fin n := finCongr (Nat.add_sub_of_le hk)
  have hcomp : prefixTrueMap k hk z ∘ e =
      fun i : Fin (k + (n - k)) => if hi : i.1 < k then true else z ⟨i.1 - k, by omega⟩ := by
    funext i; rfl
  rw [← weight_comp_equiv e, hcomp, weight_concat (fun _ : Fin k => true) z]
  simp [weight]

private theorem prefixTrueMap_lowDegree {n k : ℕ} (hk : k ≤ n) (i : Fin n) :
    (fun z : BitString (n - k) => bitVal ℂ (prefixTrueMap k hk z i)) ∈
      lowDegree ℂ (Fin (n - k)) 1 := by
  unfold prefixTrueMap
  by_cases hi : i.1 < k
  · simp only [hi, ↓reduceDIte]; exact const_mem_lowDegree 1 _
  · simp only [hi, ↓reduceDIte]; exact bitVal_mem_lowDegree _

/-- Subcube map fixing coordinates `≥ l` to `false`. -/
private def suffixFalseMap {n : ℕ} (l : ℕ) : BitString l → BitString n :=
  fun z i => if hi : i.1 < l then z ⟨i.1, hi⟩ else false

private theorem weight_suffixFalseMap {n l : ℕ} (hl : l ≤ n) (z : BitString l) :
    weight (suffixFalseMap (n := n) l z) = weight z := by
  let e : Fin (l + (n - l)) ≃ Fin n := finCongr (Nat.add_sub_of_le hl)
  have hcomp : suffixFalseMap l z ∘ e =
      fun i : Fin (l + (n - l)) => if hi : i.1 < l then z ⟨i.1, hi⟩ else false := by
    funext i; rfl
  rw [← weight_comp_equiv e, hcomp, weight_concat z (fun _ : Fin (n - l) => false)]
  simp [weight]

private theorem suffixFalseMap_lowDegree {n l : ℕ} (i : Fin n) :
    (fun z : BitString l => bitVal ℂ (suffixFalseMap l z i)) ∈ lowDegree ℂ (Fin l) 1 := by
  unfold suffixFalseMap
  by_cases hi : i.1 < l
  · simp only [hi, ↓reduceDIte]; exact bitVal_mem_lowDegree _
  · simp only [hi, ↓reduceDIte]; exact const_mem_lowDegree 1 _

/-- **Lower bound for `EXACT_k^n`**:
`Q_E(EXACT_k^n) ≥ max k (n - k)` for `0 ≤ k ≤ n` (`n ≥ 1`).
-/
theorem exactQuantumQueryComplexity_exact_ge {n k : ℕ} [NeZero n] (hk : k ≤ n) :
    max k (n - k) ≤ exactQuantumQueryComplexity (exactFun n k) := by
  refine le_exactQuantumQueryComplexity ⟨n, exactQuantumComputableIn_full _⟩ fun T hT => ?_
  refine max_le ?_ ?_
  · have hcard : (Finset.range k).card = k := Finset.card_range k
    rw [← hcard]
    refine card_le_of_exact_subcube_top hT (suffixFalseMap k) suffixFalseMap_lowDegree
      (Finset.range k) (fun w hw => by rw [Finset.mem_range] at hw; omega) fun w hw z hz => ?_
    have hlt : w < k := Finset.mem_range.mp hw
    have htop : weight (suffixFalseMap (n := n) k (fun _ => true)) = k := by
      rw [weight_suffixFalseMap hk]; simp [weight]
    have hcur : weight (suffixFalseMap (n := n) k z) = w := by
      rw [weight_suffixFalseMap hk, hz]
    simp [exactFun, htop, hcur, hlt.ne]
  · let R : Finset ℕ := (Finset.range (n - k + 1)).erase 0
    have hcard : R.card = n - k := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.succ_pos _)), Finset.card_range]
      omega
    rw [← hcard]
    refine card_le_of_exact_subcube_zero hT (prefixTrueMap k hk) (prefixTrueMap_lowDegree hk)
      R (fun w hw => by
        have := Finset.mem_range.mp (Finset.mem_of_mem_erase hw); omega) fun w hw z hz => ?_
    have hne : w ≠ 0 := (Finset.mem_erase.mp hw).1
    have h0 : weight (prefixTrueMap k hk (fun _ => false)) = k := by
      rw [weight_prefixTrueMap]; simp [weight]
    have hcur : weight (prefixTrueMap k hk z) = k + w := by
      rw [weight_prefixTrueMap, hz]
    simp [exactFun, h0, hcur, hne]

/-- **Lower bound for `EXACT_{k,l}^n`**:
`Q_E(EXACT_{k,l}^n) ≥ max (n - k) l - 1` for `0 ≤ k < l ≤ n` (`n ≥ 1`).
-/
theorem exactQuantumQueryComplexity_exactPair_ge {n k l : ℕ} [NeZero n]
    (hkl : k < l) (hln : l ≤ n) :
    max (n - k) l - 1 ≤ exactQuantumQueryComplexity (exactPairFun n k l) := by
  have hkn : k ≤ n := le_trans (le_of_lt hkl) hln
  refine le_exactQuantumQueryComplexity ⟨n, exactQuantumComputableIn_full _⟩ fun T hT => ?_
  have h1 : n - k - 1 ≤ T := by
    let R : Finset ℕ := ((Finset.range (n - k + 1)).erase 0).erase (l - k)
    have hcard : R.card = n - k - 1 := by
      have hmem1 : l - k ∈ (Finset.range (n - k + 1)).erase 0 :=
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
      rw [Finset.card_erase_of_mem hmem1,
        Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.succ_pos _)), Finset.card_range]
      omega
    rw [← hcard]
    refine card_le_of_exact_subcube_zero hT (prefixTrueMap k hkn) (prefixTrueMap_lowDegree hkn) R
      (fun w hw => by
        have := Finset.mem_range.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))
        omega)
      fun w hw z hz => ?_
    have hnelk : w ≠ l - k := (Finset.mem_erase.mp hw).1
    have hne0 : w ≠ 0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1
    have h0 : weight (prefixTrueMap k hkn (fun _ => false)) = k := by
      rw [weight_prefixTrueMap]; simp [weight]
    have hcur : weight (prefixTrueMap k hkn z) = k + w := by
      rw [weight_prefixTrueMap, hz]
    simp only [exactPairFun, h0, hcur, true_or, decide_true, ne_eq, decide_eq_true_eq, not_or]
    omega
  have h2 : l - 1 ≤ T := by
    let R : Finset ℕ := (Finset.range l).erase k
    have hcard : R.card = l - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hkl), Finset.card_range]
    rw [← hcard]
    refine card_le_of_exact_subcube_top hT (suffixFalseMap l) suffixFalseMap_lowDegree
      R (fun w hw => by
        have := Finset.mem_range.mp (Finset.mem_of_mem_erase hw); omega) fun w hw z hz => ?_
    have hnek : w ≠ k := (Finset.mem_erase.mp hw).1
    have hlt : w < l := Finset.mem_range.mp (Finset.mem_of_mem_erase hw)
    have htop : weight (suffixFalseMap (n := n) l (fun _ => true)) = l := by
      rw [weight_suffixFalseMap hln]; simp [weight]
    have hcur : weight (suffixFalseMap (n := n) l z) = w := by
      rw [weight_suffixFalseMap hln, hz]
    simp only [exactPairFun, htop, hcur, or_true, decide_true, ne_eq, decide_eq_true_eq, not_or]
    exact ⟨hnek, hlt.ne⟩
  omega

end LowerBounds

/-! ### AIS13 1-query pair-finder and exact algorithm for `EXACT_k^n` -/

section AIS13

/-- Virtual `true`-padding of `x : BitString n` by `padLen` coordinates. -/
def virtPad {n : ℕ} (padLen : ℕ) (x : BitString n) : BitString (n + padLen) :=
  fun j => if hj : j.1 < n then x ⟨j.1, hj⟩ else true

theorem weight_virtPad {n : ℕ} (padLen : ℕ) (x : BitString n) :
    weight (virtPad padLen x) = weight x + padLen := by
  have h := weight_concat x (fun _ : Fin padLen => true)
  simpa [virtPad, weight] using h

/-- **AIS13 1-query pair-finder subroutine** (`d = 2`): given `x : BitString n` (`n ≥ 1`) and
`padLen : ℕ`, let `y = virtPad padLen x : BitString (n + padLen)`. In `1` query, outputs either
`none` (guaranteed `2 * weight y ≠ n + padLen`) or `some (i, j)` (guaranteed `y i ≠ y j`). -/
theorem readoutSpecInMod_aisPairFinder (n padLen : ℕ) [NeZero n] :
    ReadoutSpecInMod (n := n) 2
      (fun (x : BitString n) (a : Option (Fin (n + padLen) × Fin (n + padLen))) =>
        match a with
        | none => 2 * weight (virtPad padLen x) ≠ n + padLen
        | some (i, j) => virtPad padLen x i ≠ virtPad padLen x j) 1 := by
  classical
  let m : ℕ := n + padLen
  have hm : 0 < m := Nat.add_pos_left (NeZero.pos n) padLen
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  let W : Type := Option (Fin m × Fin m)
  let i₀ : Fin n := ⟨0, NeZero.pos n⟩
  let cm : ℂ := (((Real.sqrt m)⁻¹ : ℝ) : ℂ)
  let c2m : ℂ := (((Real.sqrt (2 * m))⁻¹ : ℝ) : ℂ)
  let iso : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ W :=
    { toFun := fun v => WithLp.toLp 2 fun w =>
        match w with
        | none => cm * ∑ j : Fin m, v.ofLp j
        | some (i, j) => c2m * (v.ofLp i - v.ofLp j)
      map_add' := fun v₁ v₂ => by
        ext w; rcases w with _ | ⟨i, j⟩
        · change cm * ∑ j : Fin m, (v₁.ofLp j + v₂.ofLp j) =
            cm * ∑ j : Fin m, v₁.ofLp j + cm * ∑ j : Fin m, v₂.ofLp j
          rw [Finset.sum_add_distrib]; ring
        · simp only [PiLp.add_apply]; ring
      map_smul' := fun r v => by
        ext w; rcases w with _ | ⟨i, j⟩
        · simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]; ring
        · simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
      norm_map' := fun v => by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_option,
          Fintype.sum_prod_type]
        change ‖cm * ∑ j : Fin m, v.ofLp j‖ ^ 2 +
            ∑ i : Fin m, ∑ j : Fin m, ‖c2m * (v.ofLp i - v.ofLp j)‖ ^ 2 =
          ∑ j : Fin m, ‖v.ofLp j‖ ^ 2
        have hdiff : ∀ a b : ℂ,
            ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - (a * star b + star a * b).re := fun a b => by
          have h : ((a - b) * star (a - b)).re =
              (a * star a + b * star b - (a * star b + star a * b)).re := by
            congr 1; rw [star_sub]; ring
          have hmul : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := fun z => by
            rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
          rw [← hmul (a - b), h, Complex.sub_re, Complex.add_re, hmul a, hmul b]
        have hcm : ‖cm‖ ^ 2 = (m : ℝ)⁻¹ := by
          simp [cm, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hmR.le]
        have hc2m : ‖c2m‖ ^ 2 = (2 * (m : ℝ))⁻¹ := by
          have h2m : (0 : ℝ) ≤ 2 * (m : ℝ) := by positivity
          change ‖(((Real.sqrt (2 * (m : ℝ)))⁻¹ : ℝ) : ℂ)‖ ^ 2 = (2 * (m : ℝ))⁻¹
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt h2m]
        have hnorm1 : ‖cm * ∑ j : Fin m, v.ofLp j‖ ^ 2 =
            (m : ℝ)⁻¹ * ‖∑ j : Fin m, v.ofLp j‖ ^ 2 := by
          rw [norm_mul, mul_pow, hcm]
        have hnorm2 : ∀ i j : Fin m, ‖c2m * (v.ofLp i - v.ofLp j)‖ ^ 2 =
            (2 * (m : ℝ))⁻¹ * ‖v.ofLp i - v.ofLp j‖ ^ 2 := fun i j => by
          rw [norm_mul, mul_pow, hc2m]
        simp_rw [hnorm1, hnorm2]
        have hsum_diff : ∑ i : Fin m, ∑ j : Fin m, ‖v.ofLp i - v.ofLp j‖ ^ 2 =
            2 * (m : ℝ) * (∑ j : Fin m, ‖v.ofLp j‖ ^ 2) -
              2 * ‖∑ j : Fin m, v.ofLp j‖ ^ 2 := by
          simp_rw [hdiff, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
          have hcross : ∑ i : Fin m, ∑ j : Fin m,
              (v.ofLp i * star (v.ofLp j) + star (v.ofLp i) * v.ofLp j).re =
              2 * ‖∑ j : Fin m, v.ofLp j‖ ^ 2 := by
            simp_rw [← Complex.re_sum]
            set S : ℂ := ∑ j : Fin m, v.ofLp j
            have halg : ∑ i : Fin m, ∑ j : Fin m,
                (v.ofLp i * star (v.ofLp j) + star (v.ofLp i) * v.ofLp j) =
                S * star S + star S * S := by
              simp only [S, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, star_sum]
              congr 1 <;> exact Finset.sum_comm
            rw [halg, Complex.add_re, mul_comm (star S) S, Complex.star_def, Complex.mul_conj',
              ← Complex.ofReal_pow, Complex.ofReal_re]
            ring
          rw [hcross]
          ring
        simp_rw [← Finset.mul_sum]
        rw [hsum_diff]
        field_simp [hmR.ne']
        ring }
  let embM : Fin m ↪ Fin n × ZMod 2 × W :=
    ⟨fun j => if hj : j.1 < n then (⟨j.1, hj⟩, (1 : ZMod 2), none)
      else (i₀, (0 : ZMod 2), some (j, j)),
      fun j₁ j₂ h => by
        by_cases h1 : j₁.1 < n <;> by_cases h2 : j₂.1 < n
        · simp only [h1, h2, ↓reduceDIte, Prod.mk.injEq] at h
          exact Fin.ext (by simpa using congrArg Fin.val h.1)
        · simp only [h1, h2, ↓reduceDIte, Prod.mk.injEq] at h
          exact absurd h.2.1 one_ne_zero
        · simp only [h1, h2, ↓reduceDIte, Prod.mk.injEq] at h
          exact absurd h.2.1.symm one_ne_zero
        · simp only [h1, h2, ↓reduceDIte, Prod.mk.injEq] at h
          exact (Prod.mk.inj (Option.some.inj h.2.2)).1⟩
  let embOut : W ↪ Fin n × ZMod 2 × W :=
    ⟨fun w => (i₀, (0 : ZMod 2), w), fun _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).2⟩
  let L : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] ValueState (Fin n) (ZMod 2) W :=
    (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embOut).comp iso
  obtain ⟨Uiso, hUiso⟩ := exists_unitary_extension_of_linearIsometry embM L
  let initVec : EuclideanSpace ℂ (Fin m) :=
    WithLp.toLp 2 fun j : Fin m => if j.1 < n then cm else -cm
  have hnorm_initVec : ‖initVec‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.norm_sq_eq, one_pow]
    have hcm : ‖cm‖ ^ 2 = (m : ℝ)⁻¹ := by
      simp [cm, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hmR.le]
    have hterm : ∀ j : Fin m, ‖initVec.ofLp j‖ ^ 2 = (m : ℝ)⁻¹ := fun j => by
      by_cases hj : j.1 < n <;> simp [initVec, hj, hcm]
    simp [hterm, hmR.ne']
  let initState : ValueState (Fin n) (ZMod 2) W :=
    LinearIsometry.piLpExtendByZero 2 ℂ ℂ embM initVec
  let eAns : (Fin n × ZMod 2 × W) ≃ (Fin n × W) × ZMod 2 :=
    { toFun := fun (i, b, w) => ((i, w), b)
      invFun := fun ((i, w), b) => (i, b, w)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  let F2 := fiberUnitary eAns (fun _ => qftEquiv 2)
  let A : ReadoutAlgorithm n 2 W W 1 :=
    { init := initState
      norm_init := by rw [LinearIsometry.norm_map, hnorm_initVec]
      unitary := fun t => if t = 0 then F2.symm else F2.trans Uiso
      readout := fun (_, _, w) => w }
  refine ⟨W, inferInstance, A, fun x ⟨i, b, w⟩ hspec => ?_⟩
  have hchar1 : ZMod.stdAddChar (1 : ZMod 2) = -1 := by
    change ZMod.stdAddChar ((1 : ℤ) : ZMod 2) = -1
    rw [ZMod.stdAddChar_coe]
    have harg : (2 * Real.pi * Complex.I * (1 : ℤ) / (2 : ℕ) : ℂ) = Real.pi * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_pi_mul_I]
  have hOhat : ∀ (ψ : ValueState (Fin n) (ZMod 2) W) (i' : Fin n) (b' : ZMod 2) (w' : W),
      (F2 (modAddOracle 2 x (F2.symm ψ))).ofLp (i', b', w') =
        (if x i' then ZMod.stdAddChar b' else 1) * ψ.ofLp (i', b', w') := fun ψ i' b' w' => by
    rw [fiberUnitary_apply]
    change (qftEquiv 2 (WithLp.toLp 2 fun a =>
        (modAddOracle 2 x (F2.symm ψ)).ofLp (i', a, w'))).ofLp b' = _
    have hslice : (WithLp.toLp 2 fun a : ZMod 2 =>
        (modAddOracle 2 x (F2.symm ψ)).ofLp (i', a, w')) =
        modAddStep 2 (x i') ((qftEquiv 2).symm (WithLp.toLp 2 fun a => ψ.ofLp (i', a, w'))) := by
      ext a
      rw [WithLp.ofLp_toLp, modAddOracle_apply, modAddStep_apply, fiberUnitary_symm_apply]
      rfl
    rw [hslice, qft_modAddStep_qft_symm]
  let v_x : EuclideanSpace ℂ (Fin m) :=
    WithLp.toLp 2 fun j : Fin m => (if virtPad padLen x j then -1 else 1) * cm
  have hψ1 : F2 (modAddOracle 2 x (F2.symm initState)) =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ embM v_x := by
    ext ⟨i', b', w'⟩
    rw [hOhat]
    by_cases hmem : (i', b', w') ∈ Set.range embM
    · obtain ⟨j, hj⟩ := hmem
      rw [← hj]
      change _ * (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embM initVec).ofLp (embM j) =
        (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embM v_x).ofLp (embM j)
      have he1 : (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embM initVec).ofLp (embM j) =
          initVec.ofLp j := by
        change Function.extend embM initVec.ofLp 0 (embM j) = initVec.ofLp j
        exact embM.injective.extend_apply _ _ _
      have he2 : (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embM v_x).ofLp (embM j) = v_x.ofLp j := by
        change Function.extend embM v_x.ofLp 0 (embM j) = v_x.ofLp j
        exact embM.injective.extend_apply _ _ _
      rw [he1, he2]
      by_cases hjn : j.1 < n
      · have hjeq : embM j = (⟨j.1, hjn⟩, (1 : ZMod 2), none) := by
          change (if hj' : j.1 < n then (⟨j.1, hj'⟩, (1 : ZMod 2), none)
            else (i₀, (0 : ZMod 2), some (j, j))) = _
          simp [hjn]
        rw [hjeq] at hj
        have hi' : i' = ⟨j.1, hjn⟩ := (Prod.mk.inj hj).1.symm
        have hb' : b' = 1 := (Prod.mk.inj (Prod.mk.inj hj).2).1.symm
        rw [hi', hb']
        change (if x ⟨j.1, hjn⟩ then ZMod.stdAddChar (1 : ZMod 2) else 1) *
            (if j.1 < n then cm else -cm) =
          (if (if hj' : j.1 < n then x ⟨j.1, hj'⟩ else true) then -1 else 1) * cm
        simp only [hjn, ↓reduceDIte, ↓reduceIte]
        cases x ⟨j.1, hjn⟩ <;> simp [hchar1]
      · have hjeq : embM j = (i₀, (0 : ZMod 2), some (j, j)) := by
          change (if hj' : j.1 < n then (⟨j.1, hj'⟩, (1 : ZMod 2), none)
            else (i₀, (0 : ZMod 2), some (j, j))) = _
          simp [hjn]
        rw [hjeq] at hj
        have hb' : b' = 0 := (Prod.mk.inj (Prod.mk.inj hj).2).1.symm
        rw [hb']
        change (if x i' then ZMod.stdAddChar (0 : ZMod 2) else 1) *
            (if j.1 < n then cm else -cm) =
          (if (if hj' : j.1 < n then x ⟨j.1, hj'⟩ else true) then -1 else 1) * cm
        simp [hjn]
    · rw [LinearIsometry.piLpExtendByZero_apply_eq_zero hmem,
        LinearIsometry.piLpExtendByZero_apply_eq_zero hmem, mul_zero]
  have hU_ext : ∀ v : EuclideanSpace ℂ (Fin m),
      Uiso (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embM v) = L v := fun v => by
    have hsum_ofLp : ∀ {ι : Type} [Fintype ι] (s : Finset (Fin m))
        (g : Fin m → EuclideanSpace ℂ ι) (p : ι),
        (∑ j ∈ s, g j).ofLp p = ∑ j ∈ s, (g j).ofLp p := fun s g p => by
      induction s using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, PiLp.add_apply, ih]
    have hv : LinearIsometry.piLpExtendByZero 2 ℂ ℂ embM v =
        ∑ j : Fin m, v.ofLp j • ket (embM j) := by
      ext p
      rw [hsum_ofLp (ι := Fin n × ZMod 2 × W) Finset.univ]
      simp only [PiLp.smul_apply, smul_eq_mul, ket_apply]
      by_cases hp : p ∈ Set.range embM
      · obtain ⟨j, rfl⟩ := hp
        change Function.extend embM v.ofLp 0 (embM j) = _
        rw [embM.injective.extend_apply, Finset.sum_eq_single_of_mem j (mem_univ _)]
        · simp
        · intro k _ hk; simp [hk.symm]
      · rw [LinearIsometry.piLpExtendByZero_apply_eq_zero hp]
        symm
        refine Finset.sum_eq_zero fun j _ => ?_
        have hne : embM j ≠ p := fun h => hp ⟨j, h⟩
        simp [hne.symm]
    have hv' : v = ∑ j : Fin m, v.ofLp j • ket j := by
      ext j
      rw [hsum_ofLp (ι := Fin m) Finset.univ]
      simp [ket_apply]
    rw [hv, map_sum]
    simp_rw [map_smul, hUiso]
    conv_rhs => rw [hv']
    rw [map_sum]
    simp_rw [map_smul]
  have hfinal : A.finalState x = L v_x := by
    rw [ReadoutAlgorithm.finalState_eq_runValue]
    rw [runValue_modAddStep_succ, runValue_modAddStep_zero]
    simp only [A, Nat.add_one_ne_zero, ↓reduceIte, LinearIsometryEquiv.trans_apply]
    rw [hψ1, hU_ext]
  rw [hfinal]
  change (LinearIsometry.piLpExtendByZero 2 ℂ ℂ embOut (iso v_x)).ofLp (i, b, w) = 0
  by_cases hout : (i, b, w) = embOut w
  · rw [hout]
    change Function.extend embOut (iso v_x).ofLp 0 (embOut w) = 0
    rw [embOut.injective.extend_apply]
    rcases w with _ | ⟨u, v⟩
    · have h2w : 2 * weight (virtPad padLen x) = m := by
        simpa [A] using hspec
      change cm * ∑ j : Fin m, v_x.ofLp j = 0
      have hsum0 : ∑ j : Fin m, v_x.ofLp j = 0 := by
        have hsplit : ∑ j : Fin m, v_x.ofLp j =
            (∑ j ∈ Finset.univ.filter (fun j : Fin m => virtPad padLen x j = true), (-cm)) +
              (∑ j ∈ Finset.univ.filter (fun j : Fin m => virtPad padLen x j ≠ true), cm) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun j : Fin m => virtPad padLen x j = true)]
          congr 1
          · refine sum_congr rfl fun j hj => ?_
            simp [v_x, (Finset.mem_filter.mp hj).2]
          · refine sum_congr rfl fun j hj => ?_
            have hfalse : virtPad padLen x j = false :=
              Bool.eq_false_iff.mpr (Finset.mem_filter.mp hj).2
            simp [v_x, hfalse]
        rw [hsplit]
        have hc1 : (Finset.univ.filter (fun j : Fin m => virtPad padLen x j = true)).card =
            weight (virtPad padLen x) := rfl
        have hc2 : (Finset.univ.filter (fun j : Fin m => virtPad padLen x j ≠ true)).card =
            m - weight (virtPad padLen x) := by
          have hs : (Finset.univ.filter (fun j : Fin m => virtPad padLen x j = true)).card +
              (Finset.univ.filter (fun j : Fin m => virtPad padLen x j ≠ true)).card = m := by
            rw [← Finset.card_union_of_disjoint]
            · have hu : Finset.univ.filter (fun j : Fin m => virtPad padLen x j = true) ∪
                  Finset.univ.filter (fun j : Fin m => virtPad padLen x j ≠ true) =
                    Finset.univ := by
                ext j; simp only [Finset.mem_union, Finset.mem_filter, mem_univ, true_and]; tauto
              rw [hu, Finset.card_univ, Fintype.card_fin]
            · rw [Finset.disjoint_filter]; intro j _ h1 h2; exact h2 h1
          omega
        simp only [Finset.sum_const, hc1, hc2, nsmul_eq_mul]
        have heq_card : m - weight (virtPad padLen x) = weight (virtPad padLen x) := by omega
        rw [heq_card]
        ring
      rw [hsum0, mul_zero]
    · have heq : virtPad padLen x u = virtPad padLen x v := by
        simpa [A] using hspec
      change c2m * (v_x.ofLp u - v_x.ofLp v) = 0
      simp [v_x, heq]
  · have hnot : (i, b, w) ∉ Set.range embOut := by
      rintro ⟨w', hw'⟩
      have hw : w' = w := (Prod.mk.inj (Prod.mk.inj hw').2).2
      exact hout (hw ▸ hw'.symm)
    exact LinearIsometry.piLpExtendByZero_apply_eq_zero hnot _

/-- ** upper bound**:
`EXACT_k^n` is computable in `max k (n - k)` queries at modulus `d =
  2` (for `0 ≤ k ≤ n`, `n ≥ 1`).
-/
theorem readoutComputableInMod_exact {n k : ℕ} [NeZero n] (hk : k ≤ n) :
    ReadoutComputableInMod 2 (exactFun n k) (max k (n - k)) := by
  suffices h : ∀ (n : ℕ) [NeZero n] (k : ℕ), k ≤ n → 2 * k ≤ n →
      ReadoutComputableInMod 2 (exactFun n k) (n - k) by
    by_cases h2k : 2 * k ≤ n
    · rw [max_eq_right (by omega : k ≤ n - k)]
      exact h n k hk h2k
    · rw [max_eq_left (by omega : n - k ≤ k)]
      have hcomp := (h n (n - k) (by omega) (by omega)).compNot
      have hEq : (fun x : BitString n => exactFun n (n - k) (fun i => !x i)) = exactFun n k := by
        funext x
        have hwn : weight (fun i : Fin n => !x i) = n - weight x := by
          simpa using weight_not x
        have hwx : weight x ≤ n := weight_le_length x
        simp only [exactFun, hwn]
        exact decide_eq_decide.mpr (by omega)
      rw [show n - (n - k) = k by omega] at hcomp
      rwa [hEq] at hcomp
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro _ k hk h2k
    by_cases hk0 : k = 0
    · subst hk0
      simpa using readoutComputableInMod_full (exactFun n 0)
    have hTpos : 1 ≤ n - k := by omega
    let padLen : ℕ := n - 2 * k
    have hpair := readoutSpecInMod_aisPairFinder n padLen
    have hstep : ReadoutComputableInMod 2 (exactFun n k) (1 + (n - k - 1)) := by
      refine hpair.bind_fun fun a => ?_
      rcases a with _ | ⟨i, j⟩
      · exact ((readoutComputableInMod_const false).pad (Nat.zero_le _)).weaken
          fun x b hfalse hspec => by
            rw [hfalse]
            have hne : weight x ≠ k := by
              rw [weight_virtPad] at hspec; omega
            simp [exactFun, hne]
      · by_cases hi : i.1 < n
        · by_cases hj : j.1 < n
          · by_cases hij : (⟨i.1, hi⟩ : Fin n) = ⟨j.1, hj⟩
            · exact ((readoutComputableInMod_const false).pad (Nat.zero_le _)).weaken
                fun x _ _ hspec => by
                  exfalso; apply hspec
                  simp [virtPad, hi, hj, hij]
            · by_cases hn2 : n = 2
              · subst hn2
                have hk1 : k = 1 := by omega
                subst hk1
                exact (readoutComputableInMod_const true).weaken fun x b hb hspec => by
                  rw [hb]
                  have hi0 : (⟨i.1, hi⟩ : Fin 2) ≠ ⟨j.1, hj⟩ := hij
                  have hxij : x ⟨i.1, hi⟩ ≠ x ⟨j.1, hj⟩ := by
                    simpa [virtPad, hi, hj] using hspec
                  have hw1 : weight x = 1 := by
                    have hsum := weight_eq_weight_succAbove_add ⟨i.1, hi⟩ x
                    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Ne.symm hi0)
                    have hj0 : j' = 0 := Subsingleton.elim _ _
                    subst hj0
                    have hw1' : weight (x ∘ (⟨i.1, hi⟩ : Fin 2).succAbove) =
                        if x ⟨j.1, hj⟩ then 1 else 0 := by
                      rw [← hj']
                      have hs : weight (x ∘ (⟨i.1, hi⟩ : Fin 2).succAbove) =
                          ∑ t : Fin 1, if x ((⟨i.1, hi⟩ : Fin 2).succAbove t) then 1 else 0 := by
                        simp [weight, Finset.sum_boole]
                      rw [hs, Fintype.sum_unique]
                      rfl
                    rw [hw1'] at hsum
                    cases hx1 : x ⟨i.1, hi⟩ <;> cases hx2 : x ⟨j.1, hj⟩ <;> simp_all
                  simp [exactFun, hw1]
              · have hn3 : 3 ≤ n := by omega
                obtain ⟨n', hn'⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
                subst hn'
                have hne_n' : NeZero n' := ⟨by omega⟩
                have hne_n'1 : NeZero (n' + 1) := ⟨by omega⟩
                let i₁ : Fin (n' + 2) := ⟨i.1, hi⟩
                let j₁ : Fin (n' + 2) := ⟨j.1, hj⟩
                obtain ⟨j₂, hj₂⟩ := Fin.exists_succAbove_eq (show j₁ ≠ i₁ from Ne.symm hij)
                let emb : Fin n' ↪ Fin (n' + 2) := j₂.succAboveEmb.trans i₁.succAboveEmb
                have hrec := (ih n' (by omega) (k - 1) (by omega) (by omega)).subinstance emb
                have hpad : n' - (k - 1) = n' + 2 - k - 1 := by omega
                rw [hpad] at hrec
                exact hrec.weaken fun x b hb hspec => by
                  rw [hb]
                  have hxij : x i₁ ≠ x j₁ := by simpa [virtPad, hi, hj] using hspec
                  have hw : weight x = weight (x ∘ emb) + 1 := by
                    have h1 := weight_eq_weight_succAbove_add i₁ x
                    have h2 := weight_eq_weight_succAbove_add j₂ (x ∘ i₁.succAbove)
                    have hcomp : (x ∘ i₁.succAbove) ∘ j₂.succAbove = x ∘ emb := rfl
                    have hj2v : (x ∘ i₁.succAbove) j₂ = x j₁ := by
                      change x (i₁.succAbove j₂) = x j₁; rw [hj₂]
                    rw [h2, hcomp, hj2v] at h1
                    cases hxi : x i₁ <;> cases hxj : x j₁ <;> simp_all
                  simp only [exactFun, hw]
                  exact decide_eq_decide.mpr (by omega)
          · obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
            subst hn'
            have hpad_pos : 0 < padLen := by omega
            have h2kn' : 2 * k ≤ n' := by omega
            have hne_n' : NeZero n' := ⟨by omega⟩
            let i₁ : Fin (n' + 1) := ⟨i.1, hi⟩
            have hrec := (ih n' (by omega) k (by omega) h2kn').subinstance i₁.succAboveEmb
            have hpad : n' - k = n' + 1 - k - 1 := by omega
            rw [hpad] at hrec
            exact hrec.weaken fun x b hb hspec => by
              rw [hb]
              have hxi : x i₁ = false := by
                have : x i₁ ≠ true := by simpa [virtPad, hi, hj] using hspec
                exact Bool.eq_false_iff.mpr this
              have hw : weight x = weight (x ∘ i₁.succAbove) := by
                have h1 := weight_eq_weight_succAbove_add i₁ x
                simpa [hxi] using h1
              simp only [exactFun, hw]; rfl
        · by_cases hj : j.1 < n
          · obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
            subst hn'
            have h2kn' : 2 * k ≤ n' := by omega
            have hne_n' : NeZero n' := ⟨by omega⟩
            let j₁ : Fin (n' + 1) := ⟨j.1, hj⟩
            have hrec := (ih n' (by omega) k (by omega) h2kn').subinstance j₁.succAboveEmb
            have hpad : n' - k = n' + 1 - k - 1 := by omega
            rw [hpad] at hrec
            exact hrec.weaken fun x b hb hspec => by
              rw [hb]
              have hxj : x j₁ = false := by
                have : true ≠ x j₁ := by simpa [virtPad, hi, hj] using hspec
                exact Bool.eq_false_iff.mpr this.symm
              have hw : weight x = weight (x ∘ j₁.succAbove) := by
                have h1 := weight_eq_weight_succAbove_add j₁ x
                simpa [hxj] using h1
              simp only [exactFun, hw]; rfl
          · exact ((readoutComputableInMod_const false).pad (Nat.zero_le _)).weaken
              fun x _ _ hspec => by
                exfalso; apply hspec
                simp [virtPad, hi, hj]
    rwa [show 1 + (n - k - 1) = n - k by omega] at hstep

/-- **Exact quantum query complexity of `EXACT_k^n`**:
`Q_E(EXACT_k^n) = max k (n - k)` for `0 ≤ k ≤ n` (`n ≥ 1`).
-/
theorem exactQuantumQueryComplexity_exact_eq {n k : ℕ} [NeZero n] (hk : k ≤ n) :
    exactQuantumQueryComplexity (exactFun n k) = max k (n - k) :=
  le_antisymm
    (exactQuantumQueryComplexity_le (readoutComputableInMod_exact hk).toComputable)
    (exactQuantumQueryComplexity_exact_ge hk)

end AIS13

/-! ### AIN17 3-query algorithm for `EXACT_{1,4}^5` with majority index -/

section AIN17

/-- Complementary pair of indices in `Fin 4 \ {u, v}` for distinct `u, v : Fin 4`. -/
private def otherPair (u v : Fin 4) : Fin 4 × Fin 4 :=
  let l := (List.finRange 4).filter (fun k => k != u && k != v)
  (l.getD 0 0, l.getD 1 1)

private theorem otherPair_spec : ∀ u v : Fin 4, u ≠ v →
    (otherPair u v).1 ≠ (otherPair u v).2 ∧
    (otherPair u v).1 ≠ u ∧ (otherPair u v).1 ≠ v ∧
    (otherPair u v).2 ≠ u ∧ (otherPair u v).2 ≠ v := by
  decide

private theorem weight_fin4_sum (z : BitString 4) (u v p q : Fin 4)
    (huv : u ≠ v) (hpq : p ≠ q) (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) :
    weight z = (if z u then 1 else 0) + (if z v then 1 else 0) +
      (if z p then 1 else 0) + (if z q then 1 else 0) := by
  have huniv : ({u, v, p, q} : Finset (Fin 4)) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_insert_of_notMem (by simp [huv, hpu.symm, hqu.symm]),
      Finset.card_insert_of_notMem (by simp [hpv.symm, hqv.symm]),
      Finset.card_insert_of_notMem (by simp [hpq]), Finset.card_singleton, Fintype.card_fin]
  have hw : weight z = ∑ i : Fin 4, if z i then 1 else 0 := by
    simp [weight, Finset.sum_boole]
  rw [hw, ← huniv,
    Finset.sum_insert (by simp [huv, hpu.symm, hqu.symm]),
    Finset.sum_insert (by simp [hpv.symm, hqv.symm]),
    Finset.sum_insert (by simp [hpq]), Finset.sum_singleton]
  ring

private theorem weight_fin5_sum (x : BitString 5) :
    weight x = (if x 0 then 1 else 0) + (if x 1 then 1 else 0) +
      (if x 2 then 1 else 0) + (if x 3 then 1 else 0) + (if x 4 then 1 else 0) := by
  have hw : weight x = ∑ i : Fin 5, if x i then 1 else 0 := by
    simp [weight, Finset.sum_boole]
  rw [hw, Fin.sum_univ_five]

/-- **AIN17 3-query algorithm for `EXACT_{1,4}^5` with majority index** (`d = 2`):
in `3` queries, outputs `some i` with `|x| ∈ {1, 4}` and `IsMajorityIndex x i`, or `none` with
`|x| ∉ {1, 4}`. -/
theorem readoutSpecInMod_exactOneFourFive :
    ReadoutSpecInMod (n := 5) 2
      (fun (x : BitString 5) (a : Option (Fin 5)) =>
        match a with
        | none => ¬ (weight x = 1 ∨ weight x = 4)
        | some i => (weight x = 1 ∨ weight x = 4) ∧ IsMajorityIndex x i) 3 := by
  let h01 := readoutComputableInMod_xor_of_two_dvd (n := 5) (d := 2) dvd_rfl 0 1
  have hstep : ReadoutSpecInMod (n := 5) 2
      (fun (x : BitString 5) (a : Option (Fin 5)) =>
        match a with
        | none => ¬ (weight x = 1 ∨ weight x = 4)
        | some i => (weight x = 1 ∨ weight x = 4) ∧ IsMajorityIndex x i) (1 + 2) := by
    refine ReadoutSpecInMod.bind h01
      (spec₂ := fun (_ : Bool) (x : BitString 5) (a : Option (Fin 5)) =>
        match a with
        | none => ¬ (weight x = 1 ∨ weight x = 4)
        | some i => (weight x = 1 ∨ weight x = 4) ∧ IsMajorityIndex x i)
      (fun b01 => ?_) (fun _ _ _ _ h => h)
    cases b01
    · -- Case `x 0 = x 1`: run `aisPairFinder` on `z = (!x 0, x 2, x 3, x 4)` (1 query)
      let emb4 : Fin 4 ↪ Fin 5 := (1 : Fin 5).succAboveEmb
      let mask : BitString 4 := fun j => decide (j.1 = 0)
      have hpair := ((readoutSpecInMod_aisPairFinder 4 0).compXorMask mask).subinstance emb4
      have hsub : ReadoutSpecInMod (n := 5) 2
          (fun (x : BitString 5) (a : Option (Fin 5)) =>
            false = (x 0 != x 1) →
              match a with
              | none => ¬ (weight x = 1 ∨ weight x = 4)
              | some i => (weight x = 1 ∨ weight x = 4) ∧ IsMajorityIndex x i) (1 + 1) := by
        refine hpair.bind (fun p => ?_) (fun _ _ _ _ h => h)
        rcases p with _ | ⟨u, v⟩
        · exact ((readoutComputableInMod_const (none : Option (Fin 5))).pad (Nat.zero_le 1)).weaken
            fun x b hbn hspec hx01 => by
              rw [hbn]
              have hz2 : 2 * weight (fun j : Fin 4 => xor (x (emb4 j)) (mask j)) ≠ 4 := by
                have hs : 2 * weight (virtPad 0 fun i => (x ∘ emb4) i ^^ mask i) ≠ 4 + 0 := hspec
                rw [weight_virtPad] at hs
                simpa using hs
              have hwx := weight_fin5_sum x
              have hwz := weight_fin4_sum (fun j : Fin 4 => xor (x (emb4 j)) (mask j)) 0 1 2 3
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              have hx01' : x 0 = x 1 := by cases h0 : x 0 <;> cases h1 : x 1 <;> simp_all
              have he0 : emb4 0 = 0 := by decide
              have he1 : emb4 1 = 2 := by decide
              have he2 : emb4 2 = 3 := by decide
              have he3 : emb4 3 = 4 := by decide
              have hwz' : weight (fun j : Fin 4 => xor (x (emb4 j)) (mask j)) =
                  (if (!x 1) then 1 else 0) + (if x 2 then 1 else 0) +
                    (if x 3 then 1 else 0) + (if x 4 then 1 else 0) := by
                simpa [he0, he1, he2, he3, mask, hx01'] using hwz
              have hle3 : (if x 2 then 1 else 0) + (if x 3 then 1 else 0) +
                  (if x 4 then 1 else 0) ≤ 3 := by
                cases x 2 <;> cases x 3 <;> cases x 4 <;> decide
              rw [hx01'] at hwx
              cases hx1 : x 1
              · simp only [hx1, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hwx hwz'
                omega
              · simp only [hx1, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at hwx hwz'
                omega
        · by_cases huv : u = v
          · exact ((readoutComputableInMod_const (none : Option (Fin 5))).pad
              (Nat.zero_le 1)).weaken fun x _ _ hspec _ => by
                exfalso; apply hspec; simp [virtPad, huv]
          · let p := (otherPair u v).1
            let q := (otherPair u v).2
            have ⟨hpq, hpu, hpv, hqu, hqv⟩ := otherPair_spec u v huv
            let flip : Bool := xor (mask p) (mask q)
            have hxor := (readoutComputableInMod_xor_of_two_dvd (n := 5) (d := 2) dvd_rfl
              (emb4 p) (emb4 q)).map fun b =>
                if xor b flip then (some (0 : Fin 5)) else none
            exact hxor.weaken fun x b hb hspec hx01 => by
              rw [hb]
              dsimp only [Function.comp_apply]
              have hx01' : x 0 = x 1 := by cases h0 : x 0 <;> cases h1 : x 1 <;> simp_all
              let z : BitString 4 := fun j => xor (x (emb4 j)) (mask j)
              have hzu : z u ≠ z v := by simpa [virtPad, z] using hspec
              have hwx := weight_fin5_sum x
              have hwz := weight_fin4_sum z 0 1 2 3
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              have hwz' := weight_fin4_sum z u v p q huv hpq hpu hpv hqu hqv
              have hzp : xor (x (emb4 p) != x (emb4 q)) flip = (z p != z q) := by
                simp only [z, flip]
                cases x (emb4 p) <;> cases x (emb4 q) <;> cases mask p <;> cases mask q <;> rfl
              rw [hzp]
              have he0 : emb4 0 = 0 := by decide
              have he1 : emb4 1 = 2 := by decide
              have he2 : emb4 2 = 3 := by decide
              have he3 : emb4 3 = 4 := by decide
              have hwz_exp : weight z = (if (!x 1) then 1 else 0) + (if x 2 then 1 else 0) +
                  (if x 3 then 1 else 0) + (if x 4 then 1 else 0) := by
                simpa [z, he0, he1, he2, he3, mask, hx01'] using hwz
              have hiff : weight x = 1 ∨ weight x = 4 ↔ z p ≠ z q := by
                have h2 : weight z = 2 ↔ z p ≠ z q := by
                  have hzu_sum : (if z u then 1 else 0) + (if z v then 1 else 0) = 1 := by
                    cases hzu1 : z u <;> cases hzv1 : z v <;> simp_all
                  cases hzp1 : z p <;> cases hzq1 : z q <;> simp [hwz', hzu_sum, hzp1, hzq1]
                rw [← h2]
                rw [hx01'] at hwx
                have hle3 : (if x 2 then 1 else 0) + (if x 3 then 1 else 0) +
                    (if x 4 then 1 else 0) ≤ 3 := by
                  cases x 2 <;> cases x 3 <;> cases x 4 <;> decide
                cases hx1 : x 1
                · simp only [hx1, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hwx hwz_exp
                  omega
                · simp only [hx1, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at hwx hwz_exp
                  omega
              by_cases hzpq : z p ≠ z q
              · have h14 : weight x = 1 ∨ weight x = 4 := hiff.mpr hzpq
                have hbne : (z p != z q) = true := by
                  cases hzp1 : z p <;> cases hzq1 : z q <;> simp [hzp1, hzq1] at hzpq ⊢
                simp only [hbne, ↓reduceIte]
                refine ⟨h14, ?_⟩
                have hle3 : (if x 2 then 1 else 0) + (if x 3 then 1 else 0) +
                    (if x 4 then 1 else 0) ≤ 3 := by
                  cases x 2 <;> cases x 3 <;> cases x 4 <;> decide
                rcases h14 with hw1 | hw4
                · right; refine ⟨by omega, ?_⟩
                  cases hx0 : x 0
                  · rfl
                  · exfalso; rw [← hx01', hx0] at hwx; simp only [↓reduceIte] at hwx; omega
                · left; refine ⟨by omega, ?_⟩
                  cases hx0 : x 0
                  · exfalso; rw [← hx01', hx0] at hwx
                    simp only [Bool.false_eq_true, ↓reduceIte] at hwx; omega
                  · rfl
              · have hnot14 : ¬ (weight x = 1 ∨ weight x = 4) := fun h => hzpq (hiff.mp h)
                have hbeq : (z p != z q) = false := by
                  cases hzp1 : z p <;> cases hzq1 : z q <;> simp [hzp1, hzq1] at hzpq ⊢
                simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                exact hnot14
      exact hsub
    · -- Case `x 0 ≠ x 1`: query `x 2 != x 3` and `x 3 != x 4` (2 queries)
      have h23 := readoutComputableInMod_xor_of_two_dvd (n := 5) (d := 2) dvd_rfl 2 3
      have h34 := readoutComputableInMod_xor_of_two_dvd (n := 5) (d := 2) dvd_rfl 3 4
      have hboth := h23.bind fun b23 =>
        h34.map fun b34 => if !b23 && !b34 then (some (2 : Fin 5)) else none
      exact hboth.weaken fun x b hb hx01 => by
        rw [hb]
        dsimp only [Function.comp_apply]
        have hwx := weight_fin5_sum x
        have hx01' : x 0 ≠ x 1 := by
          cases h0 : x 0 <;> cases h1 : x 1 <;> simp [h0, h1] at hx01 ⊢
        have h01_sum : (if x 0 then 1 else 0) + (if x 1 then 1 else 0) = 1 := by
          cases h0 : x 0 <;> cases h1 : x 1 <;> simp [h0, h1] at hx01' ⊢
        by_cases h234 : x 2 = x 3 ∧ x 3 = x 4
        · obtain ⟨h23', h34'⟩ := h234
          have hcond : (!(x 2 != x 3) && !(x 3 != x 4)) = true := by simp [h23', h34']
          simp only [hcond, ↓reduceIte]
          rw [← h34', ← h23'] at hwx
          cases hx2 : x 2
          · simp only [hx2, Bool.false_eq_true, ↓reduceIte] at hwx
            exact ⟨Or.inl (by omega), Or.inr ⟨by omega, hx2⟩⟩
          · simp only [hx2, ↓reduceIte] at hwx
            exact ⟨Or.inr (by omega), Or.inl ⟨by omega, hx2⟩⟩
        · have hcond : (!(x 2 != x 3) && !(x 3 != x 4)) = false := by
            cases h2 : x 2 <;> cases h3 : x 3 <;> cases h4 : x 4 <;> simp [h2, h3, h4] at h234 ⊢
          simp only [hcond, Bool.false_eq_true, ↓reduceIte]
          have h234_bounds : 1 ≤ (if x 2 then 1 else 0) + (if x 3 then 1 else 0) +
              (if x 4 then 1 else 0) ∧
              (if x 2 then 1 else 0) + (if x 3 then 1 else 0) + (if x 4 then 1 else 0) ≤ 2 := by
            cases h2 : x 2 <;> cases h3 : x 3 <;> cases h4 : x 4 <;> simp [h2, h3, h4] at h234 ⊢
          change ¬ (weight x = 1 ∨ weight x = 4)
          omega
  exact hstep

end AIN17

end CslibFrontier.Quantum
