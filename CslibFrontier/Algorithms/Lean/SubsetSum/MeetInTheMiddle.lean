/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import Cslib.Algorithms.Lean.MergeSort.MergeSort
public import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Horowitz–Sahni Meet-in-the-Middle Algorithm for Subset Sum

This module formalizes the Horowitz–Sahni meet-in-the-middle algorithm for exact integer subset
sum in the `Cslib.Algorithms.Lean.TimeM` cost monad under standard Lean axioms:

1. **Ascending two-pointer list intersection (`twoPointerScan`)**: given two lists sorted in
   nondecreasing order, `twoPointerScan` decides whether they share a common element in at most
   `xs.length + ys.length` comparisons.
2. **Sorted subset-sum enumeration (`sortedSubsetSums`)**: constructs all `2 ^ as.length` subset
   sums of `as : List ℤ` directly in nondecreasing order by iteratively shifting (`addShiftList`)
   and merging (`Cslib.Algorithms.Lean.TimeM.merge`), avoiding `O(M log M)` sorting overhead and
   using at most `3 * 2 ^ as.length` operations.
3. **Meet-in-the-middle solver (`meetInTheMiddle`)**: splits `as` at `(as.length + 1) / 2`,
   reverses `b - S⁻` in linear time (`revSubList`) to preserve nondecreasing order, and runs
   `twoPointerScan` in `O(2 ^ (n / 2))` total operations.

## Main definitions

* `CslibFrontier.Algorithms.Lean.SubsetSum.twoPointerScan`
* `CslibFrontier.Algorithms.Lean.SubsetSum.sortedSubsetSums`
* `CslibFrontier.Algorithms.Lean.SubsetSum.meetInTheMiddle`

## Main results

* `CslibFrontier.Algorithms.Lean.SubsetSum.ret_twoPointerScan_eq_true_iff`
* `CslibFrontier.Algorithms.Lean.SubsetSum.time_twoPointerScan_le`
* `CslibFrontier.Algorithms.Lean.SubsetSum.sortedSubsetSums_sorted`
* `CslibFrontier.Algorithms.Lean.SubsetSum.mem_ret_sortedSubsetSums_iff`
* `CslibFrontier.Algorithms.Lean.SubsetSum.ret_meetInTheMiddle_eq_true_iff`
* `CslibFrontier.Algorithms.Lean.SubsetSum.time_meetInTheMiddle_le`
-/

public section

namespace CslibFrontier.Algorithms.Lean.SubsetSum

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TimeM
open scoped List

/-- Ascending two-pointer scan deciding whether two sorted lists share an element, charging one
tick per head comparison. -/
def twoPointerScan {α : Type} [LinearOrder α] : List α → List α → TimeM ℕ Bool
  | [], _ => pure false
  | _, [] => pure false
  | x :: xs, y :: ys => do
    ✓
    if x = y then
      return true
    else if x < y then
      twoPointerScan xs (y :: ys)
    else
      twoPointerScan (x :: xs) ys
termination_by xs ys => xs.length + ys.length

@[simp]
theorem ret_twoPointerScan_nil_left {α : Type} [LinearOrder α] (ys : List α) :
    ⟪twoPointerScan ([] : List α) ys⟫ = false := by
  unfold twoPointerScan
  rfl

@[simp]
theorem ret_twoPointerScan_nil_right {α : Type} [LinearOrder α] (xs : List α) :
    ⟪twoPointerScan xs ([] : List α)⟫ = false := by
  cases xs <;> unfold twoPointerScan <;> rfl

/-- On ascending sorted lists `xs` and `ys`, `twoPointerScan xs ys` returns `true` if and only if
`xs` and `ys` share a common element. -/
theorem ret_twoPointerScan_eq_true_iff {α : Type} [LinearOrder α] :
    ∀ {xs ys : List α}, IsSorted xs → IsSorted ys →
      (⟪twoPointerScan xs ys⟫ = true ↔ ∃ z, z ∈ xs ∧ z ∈ ys)
  | [], ys, _, _ => by simp
  | x :: xs, [], _, _ => by simp
  | x :: xs, y :: ys, hxs, hys => by
    rw [IsSorted, List.pairwise_cons] at hxs hys
    unfold twoPointerScan
    by_cases hxy : x = y
    · subst hxy
      simp only [↓reduceIte, ret_bind, ret_pure, true_iff]
      exact ⟨x, List.mem_cons_self, List.mem_cons_self⟩
    · by_cases hlt : x < y
      · simp only [hxy, ↓reduceIte, hlt, ret_bind]
        rw [ret_twoPointerScan_eq_true_iff hxs.2 (List.pairwise_cons.mpr hys)]
        constructor
        · rintro ⟨z, hz1, hz2⟩
          exact ⟨z, List.mem_cons_of_mem x hz1, hz2⟩
        · rintro ⟨z, hz1, hz2⟩
          rcases List.mem_cons.mp hz1 with rfl | hz1'
          · rcases List.mem_cons.mp hz2 with rfl | hz2'
            · exact (lt_irrefl z hlt).elim
            · exact (not_le_of_gt (hlt.trans_le (hys.1 z hz2')) le_rfl).elim
          · exact ⟨z, hz1', hz2⟩
      · simp only [hxy, ↓reduceIte, hlt, ret_bind]
        have hyx : y < x := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hxy)
        rw [ret_twoPointerScan_eq_true_iff (List.pairwise_cons.mpr hxs) hys.2]
        constructor
        · rintro ⟨z, hz1, hz2⟩
          exact ⟨z, hz1, List.mem_cons_of_mem y hz2⟩
        · rintro ⟨z, hz1, hz2⟩
          rcases List.mem_cons.mp hz2 with rfl | hz2'
          · rcases List.mem_cons.mp hz1 with rfl | hz1'
            · exact (lt_irrefl z hyx).elim
            · exact (not_le_of_gt (hyx.trans_le (hxs.1 z hz1')) le_rfl).elim
          · exact ⟨z, hz1, hz2'⟩
termination_by xs ys => xs.length + ys.length

/-- `twoPointerScan xs ys` performs at most `xs.length + ys.length` comparisons. -/
theorem time_twoPointerScan_le {α : Type} [LinearOrder α] :
    ∀ (xs ys : List α), (twoPointerScan xs ys).time ≤ xs.length + ys.length
  | [], _ => by
    unfold twoPointerScan
    simp
  | _ :: _, [] => by
    unfold twoPointerScan
    simp
  | x :: xs, y :: ys => by
    unfold twoPointerScan
    split_ifs with hxy hlt
    · simp only [time_bind, time_tick, time_pure, List.length_cons]
      omega
    · have ih := time_twoPointerScan_le xs (y :: ys)
      simp only [time_bind, time_tick, List.length_cons] at ih ⊢
      omega
    · have ih := time_twoPointerScan_le (x :: xs) ys
      simp only [time_bind, time_tick, List.length_cons] at ih ⊢
      omega
termination_by xs ys => xs.length + ys.length

private def addShiftList (a : ℤ) : List ℤ → TimeM ℕ (List ℤ)
  | [] => pure []
  | x :: xs => do
    ✓
    let rest ← addShiftList a xs
    return (x + a) :: rest

private theorem ret_addShiftList (a : ℤ) (xs : List ℤ) :
    ⟪addShiftList a xs⟫ = xs.map (· + a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [addShiftList, ih]

private theorem time_addShiftList (a : ℤ) (xs : List ℤ) :
    (addShiftList a xs).time = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [addShiftList, time_bind, time_tick, time_pure, ih, List.length_cons]
    omega

/-- Generates all `2 ^ as.length` subset sums of `as : List ℤ` in ascending order by iteratively
shifting and merging. -/
def sortedSubsetSums : List ℤ → TimeM ℕ (List ℤ)
  | [] => pure [0]
  | a :: as => do
    let s ← sortedSubsetSums as
    let shifted ← addShiftList a s
    merge s shifted

/-- `sortedSubsetSums as` produces a list sorted in nondecreasing order. -/
theorem sortedSubsetSums_sorted : ∀ (as : List ℤ), IsSorted ⟪sortedSubsetSums as⟫
  | [] => by simp [sortedSubsetSums, IsSorted]
  | a :: as => by
    have ih := sortedSubsetSums_sorted as
    have hshift : IsSorted (⟪sortedSubsetSums as⟫.map (· + a)) := by
      rw [IsSorted, List.pairwise_map]
      exact ih.imp fun hxy ↦ by linarith
    simpa [sortedSubsetSums, ret_addShiftList] using sorted_merge ih hshift

/-- Membership in `⟪sortedSubsetSums as⟫` characterizes sublist sums of `as`. -/
theorem mem_ret_sortedSubsetSums_iff :
    ∀ (as : List ℤ) (z : ℤ), z ∈ ⟪sortedSubsetSums as⟫ ↔ ∃ s, s <+ as ∧ s.sum = z
  | [], z => by
    simp only [sortedSubsetSums, ret_pure, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨[], List.Sublist.refl [], rfl⟩
    · rintro ⟨s, hs, rfl⟩
      cases List.sublist_nil.mp hs
      rfl
  | a :: as, z => by
    simp only [sortedSubsetSums, ret_bind, ret_addShiftList]
    have hperm :=
      (merge_perm ⟪sortedSubsetSums as⟫ (⟪sortedSubsetSums as⟫.map (· + a))).mem_iff (a := z)
    rw [hperm, List.mem_append, List.mem_map]
    constructor
    · rintro (hz | ⟨w, hw, rfl⟩)
      · obtain ⟨s, hs, rfl⟩ := (mem_ret_sortedSubsetSums_iff as z).mp hz
        exact ⟨s, List.Sublist.cons a hs, rfl⟩
      · obtain ⟨s, hs, rfl⟩ := (mem_ret_sortedSubsetSums_iff as w).mp hw
        exact ⟨a :: s, List.Sublist.cons_cons a hs, by simp [add_comm]⟩
    · rintro ⟨s, hs, rfl⟩
      rcases List.sublist_cons_iff.mp hs with hs' | ⟨t, rfl, ht⟩
      · exact Or.inl ((mem_ret_sortedSubsetSums_iff as s.sum).mpr ⟨s, hs', rfl⟩)
      · exact Or.inr ⟨t.sum, (mem_ret_sortedSubsetSums_iff as t.sum).mpr ⟨t, ht, rfl⟩,
          by simp [add_comm]⟩

/-- `⟪sortedSubsetSums as⟫` has length `2 ^ as.length`. -/
theorem length_ret_sortedSubsetSums :
    ∀ (as : List ℤ), ⟪sortedSubsetSums as⟫.length = 2 ^ as.length
  | [] => rfl
  | a :: as => by
    simp only [sortedSubsetSums, ret_bind, ret_addShiftList, merge_ret_length_eq_sum,
      List.length_map, length_ret_sortedSubsetSums as, List.length_cons, pow_succ]
    ring

/-- `sortedSubsetSums as` uses at most `3 * (2 ^ as.length - 1)` operations. -/
theorem time_sortedSubsetSums_le :
    ∀ (as : List ℤ), (sortedSubsetSums as).time ≤ 3 * (2 ^ as.length - 1)
  | [] => by simp [sortedSubsetSums]
  | a :: as => by
    have ih := time_sortedSubsetSums_le as
    have hm := merge_time ⟪sortedSubsetSums as⟫ (⟪sortedSubsetSums as⟫.map (· + a))
    simp only [sortedSubsetSums, time_bind, time_addShiftList, ret_addShiftList]
    rw [List.length_map, length_ret_sortedSubsetSums as] at hm
    rw [length_ret_sortedSubsetSums as, List.length_cons, pow_succ]
    have hpow : 1 ≤ 2 ^ as.length := Nat.one_le_two_pow
    omega

private def revSubListAux (b : ℤ) : List ℤ → List ℤ → TimeM ℕ (List ℤ)
  | [], acc => pure acc
  | x :: xs, acc => do
    ✓
    revSubListAux b xs ((b - x) :: acc)

private theorem ret_revSubListAux (b : ℤ) (xs acc : List ℤ) :
    ⟪revSubListAux b xs acc⟫ = (xs.map (b - ·)).reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp [revSubListAux]
  | cons x xs ih => simp [revSubListAux, ih]

private theorem time_revSubListAux (b : ℤ) (xs acc : List ℤ) :
    (revSubListAux b xs acc).time = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [revSubListAux, time_bind, time_tick, ih, List.length_cons]
    omega

private def revSubList (b : ℤ) (xs : List ℤ) : TimeM ℕ (List ℤ) :=
  revSubListAux b xs []

private theorem ret_revSubList (b : ℤ) (xs : List ℤ) :
    ⟪revSubList b xs⟫ = (xs.map (b - ·)).reverse := by
  simp [revSubList, ret_revSubListAux]

private theorem time_revSubList (b : ℤ) (xs : List ℤ) :
    (revSubList b xs).time = xs.length :=
  time_revSubListAux b xs []

private theorem sorted_revSubList (b : ℤ) {xs : List ℤ} (hxs : IsSorted xs) :
    IsSorted ⟪revSubList b xs⟫ := by
  rw [ret_revSubList, IsSorted, List.pairwise_reverse, List.pairwise_map]
  exact hxs.imp fun hxy ↦ sub_le_sub_left hxy b

/-- **Horowitz–Sahni meet-in-the-middle subset-sum solver**: splits `as` at `(as.length + 1) / 2`,
generates sorted subset sums of both halves, reverses `b - S⁻` into ascending order, and runs
`twoPointerScan`. -/
def meetInTheMiddle (as : List ℤ) (b : ℤ) : TimeM ℕ Bool := do
  let m := (as.length + 1) / 2
  let sPos ← sortedSubsetSums (as.take m)
  let sNeg ← sortedSubsetSums (as.drop m)
  let sTarget ← revSubList b sNeg
  twoPointerScan sTarget sPos

/-- **Correctness of Horowitz–Sahni meet-in-the-middle**: `meetInTheMiddle as b` returns `true` if
and only if `as` has a sublist summing to `b`. -/
theorem ret_meetInTheMiddle_eq_true_iff (as : List ℤ) (b : ℤ) :
    ⟪meetInTheMiddle as b⟫ = true ↔ ∃ s, s <+ as ∧ s.sum = b := by
  set m := (as.length + 1) / 2
  have hsPos : IsSorted ⟪sortedSubsetSums (as.take m)⟫ := sortedSubsetSums_sorted _
  have hsNeg : IsSorted ⟪sortedSubsetSums (as.drop m)⟫ := sortedSubsetSums_sorted _
  have hsTgt : IsSorted ⟪revSubList b ⟪sortedSubsetSums (as.drop m)⟫⟫ :=
    sorted_revSubList b hsNeg
  simp only [meetInTheMiddle, ret_bind]
  rw [ret_twoPointerScan_eq_true_iff hsTgt hsPos]
  constructor
  · rintro ⟨z, hzTgt, hzPos⟩
    rw [ret_revSubList, List.mem_reverse, List.mem_map] at hzTgt
    rcases hzTgt with ⟨w, hwNeg, rfl⟩
    obtain ⟨s₁, hs₁, hs₁_sum⟩ := (mem_ret_sortedSubsetSums_iff _ _).mp hzPos
    obtain ⟨s₂, hs₂, rfl⟩ := (mem_ret_sortedSubsetSums_iff _ _).mp hwNeg
    refine ⟨s₁ ++ s₂, ?_, ?_⟩
    · conv_rhs => rw [← List.take_append_drop m as]
      exact hs₁.append hs₂
    · rw [List.sum_append]
      linarith
  · rintro ⟨s, hs, rfl⟩
    rw [← List.take_append_drop m as] at hs
    obtain ⟨s₁, s₂, rfl, hs₁, hs₂⟩ := List.sublist_append_iff.mp hs
    refine ⟨s₁.sum, ?_, (mem_ret_sortedSubsetSums_iff _ _).mpr ⟨s₁, hs₁, rfl⟩⟩
    rw [ret_revSubList, List.mem_reverse, List.mem_map]
    refine ⟨s₂.sum, (mem_ret_sortedSubsetSums_iff _ _).mpr ⟨s₂, hs₂, rfl⟩, ?_⟩
    rw [List.sum_append]
    ring

/-- **`O(2 ^ (n / 2))` time bound for Horowitz–Sahni meet-in-the-middle**: total operations are at
most `5 * (2 ^ ((as.length + 1) / 2) + 2 ^ (as.length / 2))`. -/
theorem time_meetInTheMiddle_le (as : List ℤ) (b : ℤ) :
    (meetInTheMiddle as b).time ≤
      5 * (2 ^ ((as.length + 1) / 2) + 2 ^ (as.length / 2)) := by
  simp only [meetInTheMiddle, time_bind]
  set m := (as.length + 1) / 2
  have hpow_m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hpow_d : 1 ≤ 2 ^ (as.length / 2) := Nat.one_le_two_pow
  have hlen1 : (as.take m).length ≤ m := List.length_take_le m as
  have hlen2 : (as.drop m).length = as.length - m := List.length_drop
  have hm_sub : as.length - m = as.length / 2 := by omega
  have hpow1 : 2 ^ (as.take m).length ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hlen1
  have ht1 : (sortedSubsetSums (as.take m)).time ≤ 3 * (2 ^ m - 1) :=
    (time_sortedSubsetSums_le (as.take m)).trans (by omega)
  have ht2 : (sortedSubsetSums (as.drop m)).time ≤ 3 * (2 ^ (as.length / 2) - 1) := by
    have h := time_sortedSubsetSums_le (as.drop m)
    rwa [hlen2, hm_sub] at h
  have ht3 : (revSubList b ⟪sortedSubsetSums (as.drop m)⟫).time = 2 ^ (as.length / 2) := by
    rw [time_revSubList, length_ret_sortedSubsetSums, hlen2, hm_sub]
  have ht4 :
      (twoPointerScan ⟪revSubList b ⟪sortedSubsetSums (as.drop m)⟫⟫
        ⟪sortedSubsetSums (as.take m)⟫).time ≤ 2 ^ (as.length / 2) + 2 ^ m := by
    refine (time_twoPointerScan_le _ _).trans ?_
    rw [ret_revSubList, List.length_reverse, List.length_map,
      length_ret_sortedSubsetSums, length_ret_sortedSubsetSums, hlen2, hm_sub]
    omega
  omega

end CslibFrontier.Algorithms.Lean.SubsetSum
