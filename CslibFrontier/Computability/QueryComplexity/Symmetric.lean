/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.QueryComplexity.Measures
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Sensitivity of Symmetric Boolean Functions

A Boolean function `f : BooleanFunction n` is symmetric (`BooleanFunction.IsSymmetric`) when it
depends only on the Hamming weight of its input, equivalently when it is invariant under all
coordinate permutations (`isSymmetric_iff_perm_invariant`). Evaluating `f` at canonical vectors of
each weight `0, 1..., n` establishes a bijection (`symmetricEquivWeightTable`) between symmetric
`n`-variable Boolean functions and weight profiles `Fin (n + 1) → Bool`, showing there are
`2 ^ (n + 1)` symmetric Boolean functions on `n` bits (`card_isSymmetric`).

At an input `x : BitString n` of weight `w`, flipping any `true` bit moves the weight to `w - 1`
and flipping any `false` bit moves the weight to `w + 1`, yielding an exact closed form for
`sensitivityAt f x` (`sensitivityAt_of_isSymmetric`). From this formula we derive two classical
consequences:

1. **Turán's lower bound**: every nonconstant
   symmetric `n`-variable Boolean function satisfies `(n + 2) / 2 ≤ sensitivity f`
   (`⌈(n + 1) / 2⌉ ≤ s(f)`).
2. **Maximum-sensitivity characterization and count** (`sensitivity_eq_iff_hasIsolatedWeight`,
   `card_isSymmetric_and_sensitivity_eq`): a symmetric Boolean function has maximum sensitivity `n`
   if and only if its weight profile contains an isolated entry (a run of length `1`), and exactly
   `2 ^ (n + 1) - 2 * Nat.fib n` of the `2 ^ (n + 1)` symmetric `n`-variable Boolean functions have
   sensitivity `n`.

## Main definitions

* `CslibFrontier.QueryComplexity.canonicalOfWeight`: canonical `n`-bit string with first `k` bits
  `true`.
* `CslibFrontier.QueryComplexity.weightTable`: weight profile `Fin (n + 1) → Bool` of a Boolean
  function.
* `CslibFrontier.QueryComplexity.ofWeightTable`: symmetric Boolean function defined by a weight
  profile.
* `CslibFrontier.QueryComplexity.symmetricEquivWeightTable`: bijection between symmetric
  `n`-variable Boolean functions and `Fin (n + 1) → Bool`.
* `CslibFrontier.QueryComplexity.HasIsolatedWeight`: predicate asserting that a weight profile has
  an entry differing from all adjacent weights (a run of length `1`).

## Main results

* `CslibFrontier.QueryComplexity.isSymmetric_iff_perm_invariant`: `f.IsSymmetric` iff `f` is
  invariant under all coordinate permutations `Equiv.Perm (Fin n)`.
* `CslibFrontier.QueryComplexity.card_isSymmetric`:
  `Nat.card {f : BooleanFunction n | f.IsSymmetric} = 2 ^ (n + 1)`.
* `CslibFrontier.QueryComplexity.sensitivityAt_of_isSymmetric`: exact formula for
  `sensitivityAt f x` of a symmetric Boolean function.
* `CslibFrontier.QueryComplexity.turan_sensitivity_ge_of_isSymmetric`: Turán's bound
  `(n + 2) / 2 ≤ sensitivity f` for nonconstant symmetric Boolean functions.
* `CslibFrontier.QueryComplexity.sensitivity_eq_iff_hasIsolatedWeight`: `sensitivity f = n` iff
  `HasIsolatedWeight (weightTable f)`.
* `CslibFrontier.QueryComplexity.card_isSymmetric_and_sensitivity_eq`:
  `Nat.card {f : BooleanFunction n | f.IsSymmetric ∧ sensitivity f = n} =
    2 ^ (n + 1) - 2 * Nat.fib n`.
-/

public section

namespace CslibFrontier.QueryComplexity

open Cslib Cslib.BitString Finset

variable {n : ℕ}

/-! ### 1. Weight Profiles and Permutation Invariance -/

/-- A Boolean function `f : BooleanFunction n` depends only on Hamming weight if and only if it is
unchanged by every coordinate permutation `π : Equiv.Perm (Fin n)`. -/
theorem isSymmetric_iff_perm_invariant {f : BooleanFunction n} :
    f.IsSymmetric ↔ ∀ (π : Equiv.Perm (Fin n)) (x : BitString n), f (x ∘ π) = f x := by
  constructor
  · intro hf π x
    exact hf (x ∘ π) x (weight_comp_equiv x π)
  · intro hperm x y hxy
    let Tx : Finset (Fin n) := univ.filter fun i ↦ x i = true
    let Ty : Finset (Fin n) := univ.filter fun i ↦ y i = true
    have hcardT : #Tx = #Ty := hxy
    have hcardC : #(univ.filter fun i ↦ i ∉ Tx) = #(univ.filter fun i ↦ i ∉ Ty) := by
      have hx := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i ↦ i ∈ Tx)
      have hy := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i ↦ i ∈ Ty)
      have hx' : #(univ.filter fun i ↦ i ∈ Tx) = #Tx := by simp
      have hy' : #(univ.filter fun i ↦ i ∈ Ty) = #Ty := by simp
      omega
    obtain ⟨e₁⟩ : Nonempty ({i : Fin n // i ∈ Tx} ≃ {i : Fin n // i ∈ Ty}) :=
      Fintype.card_eq.mp (by simpa [Fintype.card_coe] using hcardT)
    obtain ⟨e₂⟩ : Nonempty ({i : Fin n // i ∉ Tx} ≃ {i : Fin n // i ∉ Ty}) :=
      Fintype.card_eq.mp (by
        rw [Fintype.card_subtype, Fintype.card_subtype]
        exact hcardC)
    let π : Equiv.Perm (Fin n) := e₁.subtypeCongr e₂
    have hyx : y ∘ π = x := by
      funext i
      by_cases hi : i ∈ Tx
      · have hπi : π i = (e₁ ⟨i, hi⟩).1 := by
          simp [π, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hi]
        rw [Function.comp_apply, hπi, (mem_filter.mp hi).2, (mem_filter.mp (e₁ ⟨i, hi⟩).2).2]
      · have hπi : π i = (e₂ ⟨i, hi⟩).1 := by
          simp [π, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg hi]
        rw [Function.comp_apply, hπi]
        have hx0 : x i = false := by
          cases hxi : x i
          · rfl
          · exact False.elim (hi (mem_filter.mpr ⟨mem_univ i, hxi⟩))
        have hy0 : y (e₂ ⟨i, hi⟩).1 = false := by
          cases hyi : y (e₂ ⟨i, hi⟩).1
          · rfl
          · exact False.elim ((e₂ ⟨i, hi⟩).2 (mem_filter.mpr ⟨mem_univ _, hyi⟩))
        rw [hx0, hy0]
    rw [← hyx, hperm π y]

/-- Canonical `n`-bit string of Hamming weight `k`, with its first `k` coordinates set to `true`. -/
def canonicalOfWeight (n : ℕ) (k : Fin (n + 1)) : BitString n :=
  fun i ↦ decide ((i : ℕ) < (k : ℕ))

/-- `canonicalOfWeight n k` has Hamming weight `k`. -/
@[simp]
theorem weight_canonicalOfWeight (n : ℕ) (k : Fin (n + 1)) :
    weight (canonicalOfWeight n k) = (k : ℕ) := by
  have hk : (k : ℕ) ≤ n := Nat.le_of_lt_succ k.2
  have hfilter : (univ.filter fun i : Fin n ↦ canonicalOfWeight n k i = true) =
      (Finset.range (k : ℕ)).attach.map
        ⟨fun j ↦ ⟨j.1, lt_of_lt_of_le (Finset.mem_range.mp j.2) hk⟩, by
          intro a b hab
          ext
          exact congrArg Fin.val hab⟩ := by
    ext i
    simp only [canonicalOfWeight, decide_eq_true_eq, mem_filter, mem_univ, true_and, mem_map,
      mem_attach, Subtype.exists, mem_range]
    exact ⟨fun hi ↦ ⟨i.1, hi, rfl⟩, fun ⟨_, ha, heq⟩ ↦ heq ▸ ha⟩
  rw [weight, hfilter, card_map, card_attach, card_range]

/-- The weight profile `Fin (n + 1) → Bool` of `f : BooleanFunction n`. -/
def weightTable (f : BooleanFunction n) : Fin (n + 1) → Bool :=
  fun k ↦ f (canonicalOfWeight n k)

/-- A symmetric Boolean function agrees at `x` with `weightTable f` at `weight x`. -/
theorem weightTable_apply_weight {f : BooleanFunction n} (hf : f.IsSymmetric) (x : BitString n) :
    weightTable f ⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩ = f x :=
  hf _ x (weight_canonicalOfWeight n _)

/-- The symmetric Boolean function induced by `w : Fin (n + 1) → Bool`. -/
def ofWeightTable (w : Fin (n + 1) → Bool) : BooleanFunction n :=
  fun x ↦ w ⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩

/-- `ofWeightTable w` is symmetric. -/
theorem isSymmetric_ofWeightTable (w : Fin (n + 1) → Bool) :
    (ofWeightTable w).IsSymmetric := by
  intro x y hxy
  simp only [ofWeightTable]
  congr 1
  exact Fin.ext hxy

/-- `weightTable (ofWeightTable w) = w`. -/
@[simp]
theorem weightTable_ofWeightTable (w : Fin (n + 1) → Bool) :
    weightTable (ofWeightTable w) = w := by
  funext k
  simp [weightTable, ofWeightTable]

/-- Bijection between symmetric `n`-variable Boolean functions and `Fin (n + 1) → Bool`. -/
def symmetricEquivWeightTable (n : ℕ) :
    {f : BooleanFunction n // f.IsSymmetric} ≃ (Fin (n + 1) → Bool) where
  toFun f := weightTable f.1
  invFun w := ⟨ofWeightTable w, isSymmetric_ofWeightTable w⟩
  left_inv f := by
    ext x
    exact weightTable_apply_weight f.2 x
  right_inv w := weightTable_ofWeightTable w

/-- There are `2 ^ (n + 1)` symmetric `n`-variable Boolean functions. -/
theorem card_isSymmetric (n : ℕ) :
    Nat.card {f : BooleanFunction n | f.IsSymmetric} = 2 ^ (n + 1) := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr (symmetricEquivWeightTable n)).trans (by simp)

/-! ### 2. Pointwise Sensitivity and Turán's Lower Bound -/

/-- Sensitive-coordinate characterization for a symmetric Boolean function via `weightTable f`. -/
theorem isSensitiveCoord_iff_of_isSymmetric {f : BooleanFunction n} (hf : f.IsSymmetric)
    (x : BitString n) (i : Fin n) :
    IsSensitiveCoord f x i ↔
      (x i = true ∧ ∃ h0 : 0 < weight x,
        weightTable f ⟨weight x - 1, by have := weight_le_length x; omega⟩ ≠
          weightTable f ⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩) ∨
      (x i = false ∧ ∃ hlt : weight x < n,
        weightTable f ⟨weight x + 1, Nat.succ_lt_succ hlt⟩ ≠
          weightTable f ⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩) := by
  unfold IsSensitiveCoord
  rw [← weightTable_apply_weight hf (Function.update x i (!x i)), ← weightTable_apply_weight hf x]
  cases hxi : x i
  · have hlt : weight x < n := by
      have hfalse : #(univ.filter fun j : Fin n ↦ x j = false) = n - weight x := by
        simpa using card_filter_eq_false_eq_card_sub_weight x
      have hpos : 0 < #(univ.filter fun j : Fin n ↦ x j = false) :=
        card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hxi⟩⟩
      omega
    have hw : weight (Function.update x i true) = weight x + 1 := weight_update_true hxi
    have hfin : (⟨weight (Function.update x i true),
        Nat.lt_succ_of_le (weight_le_length _)⟩ : Fin (n + 1)) =
        ⟨weight x + 1, Nat.succ_lt_succ hlt⟩ := Fin.ext hw
    simp [hfin, hlt]
  · have hpos : 0 < weight x :=
      card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hxi⟩⟩
    have hw := weight_update_false hxi
    have hfin : (⟨weight (Function.update x i false),
        Nat.lt_succ_of_le (weight_le_length _)⟩ : Fin (n + 1)) =
        ⟨weight x - 1, by have := weight_le_length x; omega⟩ := by
      ext; simp; omega
    simp [hfin, hpos]

/-- Exact formula for `sensitivityAt f x` when `f` is symmetric. -/
theorem sensitivityAt_of_isSymmetric {f : BooleanFunction n} (hf : f.IsSymmetric)
    (x : BitString n) :
    sensitivityAt f x =
      (if h0 : 0 < weight x then
        if weightTable f ⟨weight x - 1, by have := weight_le_length x; omega⟩ ≠
            weightTable f ⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩ then
          weight x
        else 0
      else 0) +
      (if hn : weight x < n then
        if weightTable f ⟨weight x + 1, Nat.succ_lt_succ hn⟩ ≠
            weightTable f ⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩ then
          n - weight x
        else 0
      else 0) := by
  let Ttrue : Finset (Fin n) := univ.filter fun i ↦ x i = true
  let Tfalse : Finset (Fin n) := univ.filter fun i ↦ x i = false
  have hdisj : Disjoint Ttrue Tfalse := by
    rw [Finset.disjoint_left]
    intro i ht hf'
    have h1 := (mem_filter.mp ht).2
    have h2 := (mem_filter.mp hf').2
    rw [h1] at h2
    exact Bool.noConfusion h2
  have hcard_true : #Ttrue = weight x := rfl
  have hcard_false : #Tfalse = n - weight x := by
    simpa [Tfalse] using card_filter_eq_false_eq_card_sub_weight x
  have hsplit : sensitiveCoords f x =
      (sensitiveCoords f x ∩ Ttrue) ∪ (sensitiveCoords f x ∩ Tfalse) := by
    ext i
    simp only [mem_union, mem_inter, Ttrue, Tfalse, mem_filter, mem_univ, true_and]
    cases x i <;> simp
  have hdisj' : Disjoint (sensitiveCoords f x ∩ Ttrue) (sensitiveCoords f x ∩ Tfalse) :=
    Disjoint.mono inter_subset_right inter_subset_right hdisj
  rw [sensitivityAt, hsplit, card_union_of_disjoint hdisj']
  congr 1
  · split_ifs with h0 hne
    · rw [← hcard_true]
      congr 1
      ext i
      simp only [mem_inter, mem_sensitiveCoords, Ttrue, mem_filter, mem_univ, true_and]
      exact ⟨fun h ↦ h.2, fun hxi ↦ ⟨(isSensitiveCoord_iff_of_isSymmetric hf x i).mpr
        (Or.inl ⟨hxi, h0, hne⟩), hxi⟩⟩
    · rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro i hi
      obtain ⟨hsens, hxi⟩ := mem_inter.mp hi
      have hxi' : x i = true := (mem_filter.mp hxi).2
      rcases (isSensitiveCoord_iff_of_isSymmetric hf x i).mp (mem_sensitiveCoords.mp hsens) with
        ⟨_, _, hne'⟩ | ⟨hf', _⟩
      · exact hne hne'
      · rw [hxi'] at hf'; exact Bool.noConfusion hf'
    · rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro i hi
      exact h0 (hcard_true ▸ card_pos.mpr ⟨i, (mem_inter.mp hi).2⟩)
  · split_ifs with hn hne
    · rw [← hcard_false]
      congr 1
      ext i
      simp only [mem_inter, mem_sensitiveCoords, Tfalse, mem_filter, mem_univ, true_and]
      exact ⟨fun h ↦ h.2, fun hxi ↦ ⟨(isSensitiveCoord_iff_of_isSymmetric hf x i).mpr
        (Or.inr ⟨hxi, hn, hne⟩), hxi⟩⟩
    · rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro i hi
      obtain ⟨hsens, hxi⟩ := mem_inter.mp hi
      have hxi' : x i = false := (mem_filter.mp hxi).2
      rcases (isSensitiveCoord_iff_of_isSymmetric hf x i).mp (mem_sensitiveCoords.mp hsens) with
        ⟨ht', _⟩ | ⟨_, _, hne'⟩
      · rw [hxi'] at ht'; exact Bool.noConfusion ht'
      · exact hne hne'
    · rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro i hi
      have hpos : 0 < n - weight x := hcard_false ▸ card_pos.mpr ⟨i, (mem_inter.mp hi).2⟩
      exact hn (by omega)

/-- **Turán's lower bound** [Turán ]: every nonconstant symmetric `n`-variable Boolean function
has sensitivity at least `(n + 2) / 2` (`= ⌈(n + 1) / 2⌉`).
-/
theorem turan_sensitivity_ge_of_isSymmetric {f : BooleanFunction n} (hf : f.IsSymmetric)
    (hnonconst : ∃ x y : BitString n, f x ≠ f y) :
    (n + 2) / 2 ≤ sensitivity f := by
  obtain ⟨x, y, hxy⟩ := hnonconst
  have hw_ne : weightTable f ⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩ ≠
      weightTable f ⟨weight y, Nat.lt_succ_of_le (weight_le_length y)⟩ := by
    rwa [weightTable_apply_weight hf, weightTable_apply_weight hf]
  have hex_adj : ∃ j : Fin n, weightTable f j.castSucc ≠ weightTable f j.succ := by
    by_contra hall
    push Not at hall
    have hconst : ∀ k : Fin (n + 1), weightTable f k = weightTable f 0 := by
      intro k
      induction k using Fin.induction with
      | zero => rfl
      | succ j ih => rw [← hall j, ih]
    exact hw_ne ((hconst _).trans (hconst _).symm)
  obtain ⟨j, hj⟩ := hex_adj
  let x₀ := canonicalOfWeight n j.castSucc
  let x₁ := canonicalOfWeight n j.succ
  have hx₀ : n - (j : ℕ) ≤ sensitivityAt f x₀ := by
    rw [sensitivityAt_of_isSymmetric hf x₀]
    have hw0 : weight x₀ = (j : ℕ) := weight_canonicalOfWeight n j.castSucc
    have hlt : weight x₀ < n := hw0 ▸ j.2
    have hne : weightTable f ⟨weight x₀ + 1, Nat.succ_lt_succ hlt⟩ ≠
        weightTable f ⟨weight x₀, Nat.lt_succ_of_le (weight_le_length x₀)⟩ := by
      have hf1 : (⟨weight x₀ + 1, Nat.succ_lt_succ hlt⟩ : Fin (n + 1)) = j.succ :=
        Fin.ext (by simp [hw0])
      have hf0 : (⟨weight x₀, Nat.lt_succ_of_le (weight_le_length x₀)⟩ : Fin (n + 1)) =
          j.castSucc := Fin.ext hw0
      rw [hf1, hf0]
      exact hj.symm
    refine le_trans ?_ (Nat.le_add_left _ _)
    split_ifs
    omega
  have hx₁ : (j : ℕ) + 1 ≤ sensitivityAt f x₁ := by
    rw [sensitivityAt_of_isSymmetric hf x₁]
    have hw1 : weight x₁ = (j : ℕ) + 1 := weight_canonicalOfWeight n j.succ
    have hpos : 0 < weight x₁ := by omega
    have hne : weightTable f ⟨weight x₁ - 1, by have := weight_le_length x₁; omega⟩ ≠
        weightTable f ⟨weight x₁, Nat.lt_succ_of_le (weight_le_length x₁)⟩ := by
      have hf0 : (⟨weight x₁ - 1, by have := weight_le_length x₁; omega⟩ : Fin (n + 1)) =
          j.castSucc := Fin.ext (by simp [hw1])
      have hf1 : (⟨weight x₁, Nat.lt_succ_of_le (weight_le_length x₁)⟩ : Fin (n + 1)) = j.succ :=
        Fin.ext hw1
      rw [hf0, hf1]
      exact hj
    refine le_trans ?_ (Nat.le_add_right _ _)
    split_ifs
    omega
  have hs0 : n - (j : ℕ) ≤ sensitivity f := hx₀.trans (sensitivityAt_le_sensitivity f x₀)
  have hs1 : (j : ℕ) + 1 ≤ sensitivity f := hx₁.trans (sensitivityAt_le_sensitivity f x₁)
  omega

/-! ### 3. Isolated Weights and Counting Maximum-Sensitivity Symmetric Functions -/

/-- A weight profile `w : Fin (n + 1) → Bool` has an **isolated weight** (a run of length `1`) if
some index `k` differs from every adjacent index in `Fin (n + 1)`. -/
def HasIsolatedWeight (w : Fin (n + 1) → Bool) : Prop :=
  ∃ k : Fin (n + 1),
    (∀ h : 0 < (k : ℕ), w ⟨(k : ℕ) - 1, by omega⟩ ≠ w k) ∧
    (∀ h : (k : ℕ) < n, w ⟨(k : ℕ) + 1, by omega⟩ ≠ w k)

instance instDecidablePredHasIsolatedWeight : DecidablePred (@HasIsolatedWeight n) :=
  fun w ↦ inferInstanceAs (Decidable (∃ k : Fin (n + 1),
    (∀ h : 0 < (k : ℕ), w ⟨(k : ℕ) - 1, by omega⟩ ≠ w k) ∧
    (∀ h : (k : ℕ) < n, w ⟨(k : ℕ) + 1, by omega⟩ ≠ w k)))

/-- A symmetric Boolean function `f` has `sensitivity f = n` iff `weightTable f` has an isolated
weight. -/
theorem sensitivity_eq_iff_hasIsolatedWeight {f : BooleanFunction n} (hf : f.IsSymmetric) :
    sensitivity f = n ↔ HasIsolatedWeight (weightTable f) := by
  have hpt : ∀ x : BitString n, sensitivityAt f x = n ↔
      (∀ h : 0 < weight x,
        weightTable f ⟨weight x - 1, by have := weight_le_length x; omega⟩ ≠
          weightTable f ⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩) ∧
      (∀ h : weight x < n,
        weightTable f ⟨weight x + 1, Nat.succ_lt_succ h⟩ ≠
          weightTable f ⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩) := by
    intro x
    rw [sensitivityAt_of_isSymmetric hf x]
    have hle : weight x ≤ n := weight_le_length x
    split_ifs with h0 h1 hn h2 hn' h2' hn'' h2''
    · exact ⟨fun _ ↦ ⟨fun _ ↦ h1, fun _ ↦ h2⟩, fun _ ↦ by omega⟩
    · refine ⟨fun h ↦ ?_, fun h ↦ absurd (h.2 hn) h2⟩
      omega
    · refine ⟨fun _ ↦ ⟨fun _ ↦ h1, fun h ↦ absurd h hn⟩, fun _ ↦ ?_⟩
      omega
    · refine ⟨fun h ↦ ?_, fun h ↦ absurd (h.1 h0) h1⟩
      omega
    · refine ⟨fun h ↦ ?_, fun h ↦ absurd (h.1 h0) h1⟩
      omega
    · refine ⟨fun h ↦ ?_, fun h ↦ absurd (h.1 h0) h1⟩
      omega
    · refine ⟨fun _ ↦ ⟨fun h ↦ absurd h h0, fun _ ↦ h2''⟩, fun _ ↦ ?_⟩
      omega
    · refine ⟨fun h ↦ ?_, fun h ↦ absurd (h.2 hn'') h2''⟩
      omega
    · refine ⟨fun _ ↦ ⟨fun h ↦ absurd h h0, fun h ↦ absurd h hn''⟩, fun _ ↦ ?_⟩
      omega
  constructor
  · intro hsens
    rcases eq_or_ne n 0 with rfl | hn0
    · exact ⟨0, fun h ↦ absurd h (Nat.not_lt_zero 0), fun h ↦ absurd h (Nat.not_lt_zero _)⟩
    · have hex : ∃ x : BitString n, sensitivityAt f x = n := by
        by_contra hall
        push Not at hall
        have hlt : sensitivity f < n := by
          rw [sensitivity, Finset.sup_lt_iff (Nat.pos_of_ne_zero hn0)]
          intro x _
          exact lt_of_le_of_ne (sensitivityAt_le_card f x) (hall x)
        omega
      obtain ⟨x, hx⟩ := hex
      obtain ⟨hl, hr⟩ := (hpt x).mp hx
      exact ⟨⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩, hl, hr⟩
  · rintro ⟨k, hl, hr⟩
    apply le_antisymm (sensitivity_le_card f)
    let x := canonicalOfWeight n k
    have hx : sensitivityAt f x = n := by
      rw [hpt x]
      have hwx : weight x = (k : ℕ) := weight_canonicalOfWeight n k
      refine ⟨fun hpos ↦ ?_, fun hlt ↦ ?_⟩
      · have hkpos : 0 < (k : ℕ) := hwx ▸ hpos
        have hf0 : (⟨weight x - 1, by have := weight_le_length x; omega⟩ : Fin (n + 1)) =
            ⟨(k : ℕ) - 1, by omega⟩ := Fin.ext (by simp [hwx])
        have hf1 : (⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩ : Fin (n + 1)) = k :=
          Fin.ext hwx
        rw [hf0, hf1]
        exact hl hkpos
      · have hklt : (k : ℕ) < n := hwx ▸ hlt
        have hf0 : (⟨weight x + 1, Nat.succ_lt_succ hlt⟩ : Fin (n + 1)) =
            ⟨(k : ℕ) + 1, by omega⟩ := Fin.ext (by simp [hwx])
        have hf1 : (⟨weight x, Nat.lt_succ_of_le (weight_le_length x)⟩ : Fin (n + 1)) = k :=
          Fin.ext hwx
        rw [hf0, hf1]
        exact hr hklt
    exact hx.symm.trans_le (sensitivityAt_le_sensitivity f x)

private def noIsolatedEquiv (m : ℕ) :
    {w : Fin (m + 3) → Bool // ¬ HasIsolatedWeight w} ≃
      {w : Fin (m + 2) → Bool // ¬ HasIsolatedWeight w} ⊕
        {w : Fin (m + 1) → Bool // ¬ HasIsolatedWeight w} where
  toFun w :=
    let i1 : Fin (m + 3) := (0 : Fin (m + 2)).succ
    let i2 : Fin (m + 3) := (0 : Fin (m + 1)).succ.succ
    have h01 : w.1 0 = w.1 i1 := by
      by_contra hne
      exact w.2 ⟨0, fun h ↦ absurd h (Nat.not_lt_zero 0), fun _ ↦ Ne.symm hne⟩
    if h12 : w.1 i1 = w.1 i2 then
      Sum.inl ⟨fun k : Fin (m + 2) ↦ w.1 k.succ, by
        rintro ⟨k, hl, hr⟩
        apply w.2
        refine ⟨k.succ, ?_, ?_⟩
        · intro _
          rcases eq_or_ne (k : ℕ) 0 with hk0 | hkne
          · have hk_eq : k = 0 := Fin.ext hk0
            subst hk_eq
            have h02 : w.1 i2 ≠ w.1 i1 := hr (Nat.succ_pos m)
            exact False.elim (h02 h12.symm)
          · have hpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hkne
            have hf0 : (⟨(k.succ : ℕ) - 1, by omega⟩ : Fin (m + 3)) =
                (⟨(k : ℕ) - 1, by omega⟩ : Fin (m + 2)).succ := Fin.ext (by simp; omega)
            rw [hf0]
            exact hl hpos
        · intro hlt
          have hklt : (k : ℕ) < m + 1 := by simp at hlt; omega
          have hf1 : (⟨(k.succ : ℕ) + 1, by omega⟩ : Fin (m + 3)) =
              (⟨(k : ℕ) + 1, by omega⟩ : Fin (m + 2)).succ := Fin.ext (by simp)
          rw [hf1]
          exact hr hklt⟩
    else
      Sum.inr ⟨fun k : Fin (m + 1) ↦ w.1 k.succ.succ, by
        rintro ⟨k, hl, hr⟩
        apply w.2
        refine ⟨k.succ.succ, ?_, ?_⟩
        · intro _
          rcases eq_or_ne (k : ℕ) 0 with hk0 | hkne
          · have hk_eq : k = 0 := Fin.ext hk0
            subst hk_eq
            exact h12
          · have hpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hkne
            have hf0 : (⟨(k.succ.succ : ℕ) - 1, by omega⟩ : Fin (m + 3)) =
                (⟨(k : ℕ) - 1, by omega⟩ : Fin (m + 1)).succ.succ := Fin.ext (by simp; omega)
            rw [hf0]
            exact hl hpos
        · intro hlt
          have hklt : (k : ℕ) < m := by simp at hlt; omega
          have hf1 : (⟨(k.succ.succ : ℕ) + 1, by omega⟩ : Fin (m + 3)) =
              (⟨(k : ℕ) + 1, by omega⟩ : Fin (m + 1)).succ.succ := Fin.ext (by simp)
          rw [hf1]
          exact hr hklt⟩
  invFun s :=
    match s with
    | Sum.inl u =>
      ⟨Fin.cons (u.1 0) u.1, by
        rintro ⟨k, hl, hr⟩
        induction k using Fin.cases with
        | zero =>
          have h := hr (Nat.succ_pos (m + 1))
          have hf1 : (⟨((0 : Fin (m + 3)) : ℕ) + 1, by simp⟩ : Fin (m + 3)) =
              (0 : Fin (m + 2)).succ := rfl
          rw [hf1, Fin.cons_succ, Fin.cons_zero] at h
          exact h rfl
        | succ j =>
          rcases eq_or_ne (j : ℕ) 0 with hj0 | hjne
          · have hj_eq : j = 0 := Fin.ext hj0
            subst hj_eq
            have h := hl (Nat.succ_pos 0)
            have hf0 : (⟨((0 : Fin (m + 2)).succ : ℕ) - 1, by simp⟩ : Fin (m + 3)) = 0 := rfl
            rw [hf0, Fin.cons_zero, Fin.cons_succ] at h
            exact h rfl
          · apply u.2
            refine ⟨j, fun hpos ↦ ?_, fun hlt ↦ ?_⟩
            · have h := hl (Nat.succ_pos _)
              have hf0 : (⟨(j.succ : ℕ) - 1, by simp; omega⟩ : Fin (m + 3)) =
                  (⟨(j : ℕ) - 1, by omega⟩ : Fin (m + 2)).succ := Fin.ext (by simp; omega)
              rw [hf0, Fin.cons_succ, Fin.cons_succ] at h
              exact h
            · have h := hr (by simp; omega)
              have hf1 : (⟨(j.succ : ℕ) + 1, by simp; omega⟩ : Fin (m + 3)) =
                  (⟨(j : ℕ) + 1, by omega⟩ : Fin (m + 2)).succ := Fin.ext (by simp)
              rw [hf1, Fin.cons_succ, Fin.cons_succ] at h
              exact h⟩
    | Sum.inr v =>
      ⟨Fin.cons (!v.1 0) (Fin.cons (!v.1 0) v.1), by
        rintro ⟨k, hl, hr⟩
        induction k using Fin.cases with
        | zero =>
          have h := hr (Nat.succ_pos (m + 1))
          have hf1 : (⟨((0 : Fin (m + 3)) : ℕ) + 1, by simp⟩ : Fin (m + 3)) =
              (0 : Fin (m + 2)).succ := rfl
          rw [hf1, Fin.cons_succ, Fin.cons_zero, Fin.cons_zero] at h
          exact h rfl
        | succ j =>
          induction j using Fin.cases with
          | zero =>
            have h := hl (Nat.succ_pos 0)
            have hf0 : (⟨((0 : Fin (m + 2)).succ : ℕ) - 1, by simp⟩ : Fin (m + 3)) = 0 := rfl
            rw [hf0, Fin.cons_zero, Fin.cons_succ, Fin.cons_zero] at h
            exact h rfl
          | succ i =>
            apply v.2
            refine ⟨i, fun hpos ↦ ?_, fun hlt ↦ ?_⟩
            · have h := hl (Nat.succ_pos _)
              have hf0 : (⟨(i.succ.succ : ℕ) - 1, by simp; omega⟩ : Fin (m + 3)) =
                  (⟨(i : ℕ) - 1, by omega⟩ : Fin (m + 1)).succ.succ := Fin.ext (by simp; omega)
              rw [hf0, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ] at h
              exact h
            · have h := hr (by simp; omega)
              have hf1 : (⟨(i.succ.succ : ℕ) + 1, by simp; omega⟩ : Fin (m + 3)) =
                  (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)).succ.succ := Fin.ext (by simp)
              rw [hf1, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ] at h
              exact h⟩
  left_inv w := by
    have h01 : w.1 0 = w.1 (0 : Fin (m + 2)).succ := by
      by_contra hne
      exact w.2 ⟨0, fun h ↦ absurd h (Nat.not_lt_zero 0), fun _ ↦ Ne.symm hne⟩
    dsimp only
    split_ifs with h12
    · ext k
      dsimp only
      induction k using Fin.cases with
      | zero =>
        rw [Fin.cons_zero]
        exact h01.symm
      | succ j =>
        rw [Fin.cons_succ]
    · have h2_not : (!w.1 (0 : Fin (m + 1)).succ.succ) = w.1 (0 : Fin (m + 2)).succ := by
        cases hw1 : w.1 (0 : Fin (m + 2)).succ <;>
          cases hw2 : w.1 (0 : Fin (m + 1)).succ.succ <;> simp_all
      ext k
      dsimp only
      induction k using Fin.cases with
      | zero =>
        rw [Fin.cons_zero]
        exact h2_not.trans h01.symm
      | succ j =>
        rw [Fin.cons_succ]
        induction j using Fin.cases with
        | zero =>
          rw [Fin.cons_zero]
          exact h2_not
        | succ i =>
          rw [Fin.cons_succ]
  right_inv s := by
    dsimp only
    rcases s with u | v
    · have h12 : (Fin.cons (u.1 0) u.1 : Fin (m + 3) → Bool) (0 : Fin (m + 2)).succ =
          (Fin.cons (u.1 0) u.1 : Fin (m + 3) → Bool) (0 : Fin (m + 1)).succ.succ := by
        simp only [Fin.cons_succ]
        by_contra hne
        exact u.2 ⟨0, fun h ↦ absurd h (Nat.not_lt_zero 0), fun _ ↦ Ne.symm hne⟩
      split_ifs with h
      · rfl
      · exact absurd h12 h
    · have h12 : (Fin.cons (!v.1 0) (Fin.cons (!v.1 0) v.1) : Fin (m + 3) → Bool)
            (0 : Fin (m + 2)).succ ≠
          (Fin.cons (!v.1 0) (Fin.cons (!v.1 0) v.1) : Fin (m + 3) → Bool)
            (0 : Fin (m + 1)).succ.succ := by
        simp only [Fin.cons_succ, Fin.cons_zero]
        cases v.1 0 <;> decide
      split_ifs with h
      · exact absurd h h12
      · rfl

private theorem card_not_hasIsolatedWeight (n : ℕ) :
    #(univ.filter fun w : Fin (n + 1) → Bool ↦ ¬ HasIsolatedWeight w) = 2 * Nat.fib n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | _ | m
    · rw [Nat.fib_zero, mul_zero, card_eq_zero, filter_eq_empty_iff]
      intro w _
      simp only [Classical.not_not]
      exact ⟨0, fun h ↦ absurd h (Nat.not_lt_zero 0), fun h ↦ absurd h (Nat.not_lt_zero _)⟩
    · rw [Nat.fib_one, mul_one, ← Fintype.card_subtype]
      have hiff : ∀ w : Fin 2 → Bool, ¬ HasIsolatedWeight w ↔ w 0 = w 1 := by
        intro w
        constructor
        · intro hno
          by_contra hne
          exact hno ⟨0, fun h ↦ absurd h (Nat.not_lt_zero 0), fun _ ↦ Ne.symm hne⟩
        · intro heq ⟨k, hl, hr⟩
          have hk2 := k.2
          rcases eq_or_ne (k : ℕ) 0 with hk0 | hk1
          · have hk_eq : k = 0 := Fin.ext hk0
            subst hk_eq
            exact hr Nat.one_pos heq.symm
          · have hk_eq : k = 1 := Fin.ext (by simp; omega)
            subst hk_eq
            exact hl Nat.one_pos heq
      refine (Fintype.card_congr ?_).trans Fintype.card_bool
      exact
        { toFun := fun w ↦ w.1 0
          invFun := fun b ↦ ⟨fun _ ↦ b, (hiff _).mpr rfl⟩
          left_inv := fun w ↦ by
            ext k
            dsimp only
            have hk2 := k.2
            rcases eq_or_ne (k : ℕ) 0 with hk0 | hk1
            · have hk_eq : k = 0 := Fin.ext hk0
              subst hk_eq
              rfl
            · have hk_eq : k = 1 := Fin.ext (by simp; omega)
              subst hk_eq
              exact (hiff w.1).mp w.2
          right_inv := fun _ ↦ rfl }
    · have hcard : #(univ.filter fun w : Fin (m + 3) → Bool ↦ ¬ HasIsolatedWeight w) =
          #(univ.filter fun w : Fin (m + 2) → Bool ↦ ¬ HasIsolatedWeight w) +
            #(univ.filter fun w : Fin (m + 1) → Bool ↦ ¬ HasIsolatedWeight w) := by
        simp only [← Fintype.card_subtype]
        rw [Fintype.card_congr (noIsolatedEquiv m), Fintype.card_sum]
      rw [hcard, ih (m + 1) (by omega), ih m (by omega), Nat.fib_add_two]
      omega

/-- **Exact count of symmetric Boolean functions with maximum sensitivity**: for every `n : ℕ`,
there are `2 ^ (n + 1) - 2 * Nat.fib n` symmetric `n`-variable Boolean functions with
`sensitivity f = n`. -/
theorem card_isSymmetric_and_sensitivity_eq (n : ℕ) :
    Nat.card {f : BooleanFunction n | f.IsSymmetric ∧ sensitivity f = n} =
      2 ^ (n + 1) - 2 * Nat.fib n := by
  classical
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin (n + 1) → Bool)))
    HasIsolatedWeight
  have huniv : #(univ : Finset (Fin (n + 1) → Bool)) = 2 ^ (n + 1) := by simp
  rw [card_not_hasIsolatedWeight n, huniv] at hsplit
  have hiso : #(univ.filter (HasIsolatedWeight (n := n))) = 2 ^ (n + 1) - 2 * Nat.fib n := by
    omega
  rw [Nat.card_eq_fintype_card, ← hiso, ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun f ↦ ⟨weightTable f.1,
        (sensitivity_eq_iff_hasIsolatedWeight f.2.1).mp f.2.2⟩
      invFun := fun w ↦ ⟨ofWeightTable w.1, isSymmetric_ofWeightTable w.1, by
        rw [sensitivity_eq_iff_hasIsolatedWeight (isSymmetric_ofWeightTable w.1),
          weightTable_ofWeightTable]
        exact w.2⟩
      left_inv := fun f ↦ by
        ext x
        exact weightTable_apply_weight f.2.1 x
      right_inv := fun w ↦ by
        ext k
        exact congrFun (weightTable_ofWeightTable w.1) k }

end CslibFrontier.QueryComplexity
