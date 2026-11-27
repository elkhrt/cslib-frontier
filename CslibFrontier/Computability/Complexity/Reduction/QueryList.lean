/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Reduction.TruthTableVariants
public import CslibFrontier.Computability.Complexity.Reduction.Turing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

/-!
# Batch-list constructors and bounded-tuple enumeration for truth-table and Turing reductions

Many non-adaptive reductions in computational complexity compute an explicit list of oracle queries
`qs : α → List β` rather than an indexed query pair `(r : α → ℕ, q : α × ℕ → β)`
[Ladner, Lynch and Selman]. A central special case is fixed-arity exhaustive
support enumeration: given a unary bound `n = size a` and a fixed parameter `k : ℕ`, one
enumerates all index tuples of length at most `k` over `{0, …, n - 1}` in polynomial time `O(n^k)`
and forms a subproblem query `sub (a, cols)` for each tuple.

This module provides:

1. **List-query constructors** converting a polynomial-time batch generator `qs : α → List β`
   into disjunctive (`PolyTimeDTTReducible.of_queryList`), conjunctive
   (`PolyTimeCTTReducible.of_queryList`), and Turing
   (`PolyTimeTuringReducible.of_disjunctiveQueryList`,
   `PolyTimeTuringReducible.of_conjunctiveQueryList`) reductions.
2. **Turing-hardness transfer** across truth-table, disjunctive, and conjunctive reductions
   (`PolyTimeHard.polyTimeTuringHard_of_truthTable`, `NPHard.npTuringHard_of_truthTable`,
   `NPHard.npTuringHard_of_dtt`, `NPHard.npTuringHard_of_ctt`).
3. **Fixed-arity bounded-tuple enumeration** (`boundedNatLists n k`), its exact membership and
   bounded-cardinality `Finset` coverage characterizations, polynomial-time computability in unary
   `n` for every fixed `k`, and the resulting disjunctive truth-table and Turing reductions
   (`PolyTimeDTTReducible.of_boundedNatLists`, `PolyTimeTuringReducible.of_boundedNatLists`).

## Main definitions

* `Cslib.Complexity.boundedNatLists`: all lists of natural numbers of length at most `k` with
  entries strictly below `n`.

## Main results

* `Cslib.Complexity.PolyTimeDTTReducible.of_queryList`,
  `Cslib.Complexity.PolyTimeCTTReducible.of_queryList`: list-based disjunctive and conjunctive
  truth-table reductions.
* `Cslib.Complexity.PolyTimeTuringReducible.of_disjunctiveQueryList`,
  `Cslib.Complexity.PolyTimeTuringReducible.of_conjunctiveQueryList`: list-based non-adaptive
  polynomial-time Turing reductions without nonemptiness assumptions on the target carrier.
* `Cslib.Complexity.PolyTimeHard.polyTimeTuringHard_of_truthTable`,
  `Cslib.Complexity.NPHard.npTuringHard_of_truthTable`,
  `Cslib.Complexity.NPHard.npTuringHard_of_dtt`,
  `Cslib.Complexity.NPHard.npTuringHard_of_ctt`: hardness transfer to Turing hardness.
* `Cslib.Complexity.mem_boundedNatLists_iff`,
  `Cslib.Complexity.exists_mem_boundedNatLists_of_card_le`,
  `Cslib.Complexity.computableInPolyTime_boundedNatLists`: exact specification, finite-subset
  coverage, and polynomial-time generation of `boundedNatLists n k`.
* `Cslib.Complexity.PolyTimeDTTReducible.of_boundedNatLists`,
  `Cslib.Complexity.PolyTimeTuringReducible.of_boundedNatLists`: fixed-parameter bounded-tuple
  search reductions.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α β γ : Type}
variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : γ ↪ List Bool}
variable {A : Set α} {B : Set β} {L : Set γ}

/-! ### List-based disjunctive, conjunctive, and Turing reductions -/

section QueryList

attribute [local irreducible] encUnary encNat encPair encList encBool encBits

/-- A polynomial-time query-list generator `qs : α → List β` witnessing
`a ∈ A ↔ ∃ b ∈ qs a, b ∈ B` gives a polynomial-time disjunctive truth-table reduction
`A ≤ᵖ_{dtt} B`. -/
theorem PolyTimeDTTReducible.of_queryList [Nonempty β] {qs : α → List β}
    (hqs : ComputableInPolyTime qs encA (encList encB))
    (hiff : ∀ a, a ∈ A ↔ ∃ b ∈ qs a, b ∈ B) :
    PolyTimeDTTReducible encA encB A B := by
  obtain ⟨b₀⟩ := ‹Nonempty β›
  refine ⟨fun a => (qs a).length, fun p => (qs p.1).getD p.2 b₀, ⟨?_, ?_⟩, fun a => ?_⟩
  · fun_prop
  · have hget : ComputableInPolyTime (fun q : List β × ℕ => q.1.getD q.2 b₀)
        (encPair (encList encB) encUnary) encB :=
      ComputableInPolyTime.listGetD (encA := encB) b₀
    exact hget.comp ((hqs.comp (fst encA encUnary)).prod (snd encA encUnary))
  · dsimp only
    rw [hiff a]
    constructor
    · rintro ⟨b, hb_mem, hbB⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb_mem
      exact ⟨i, hi, by rwa [List.getD_eq_getElem _ _ hi]⟩
    · rintro ⟨i, hi, hgetB⟩
      rw [List.getD_eq_getElem _ _ hi] at hgetB
      exact ⟨(qs a)[i], List.getElem_mem hi, hgetB⟩

/-- A polynomial-time query-list generator `qs : α → List β` witnessing
`a ∈ A ↔ ∀ b ∈ qs a, b ∈ B` gives a polynomial-time conjunctive truth-table reduction
`A ≤ᵖ_{ctt} B`. -/
theorem PolyTimeCTTReducible.of_queryList [Nonempty β] {qs : α → List β}
    (hqs : ComputableInPolyTime qs encA (encList encB))
    (hiff : ∀ a, a ∈ A ↔ ∀ b ∈ qs a, b ∈ B) :
    PolyTimeCTTReducible encA encB A B := by
  obtain ⟨b₀⟩ := ‹Nonempty β›
  refine ⟨fun a => (qs a).length, fun p => (qs p.1).getD p.2 b₀, ⟨?_, ?_⟩, fun a => ?_⟩
  · fun_prop
  · have hget : ComputableInPolyTime (fun q : List β × ℕ => q.1.getD q.2 b₀)
        (encPair (encList encB) encUnary) encB :=
      ComputableInPolyTime.listGetD (encA := encB) b₀
    exact hget.comp ((hqs.comp (fst encA encUnary)).prod (snd encA encUnary))
  · dsimp only
    rw [hiff a]
    constructor
    · intro hall i hi
      rw [List.getD_eq_getElem _ _ hi]
      exact hall (qs a)[i] (List.getElem_mem hi)
    · intro hall b hb_mem
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb_mem
      have hi_val := hall i hi
      rwa [List.getD_eq_getElem _ _ hi] at hi_val

/-- A polynomial-time query-list generator `qs : α → List β` witnessing
`a ∈ A ↔ ∃ b ∈ qs a, b ∈ B` gives a polynomial-time Turing reduction `A ≤ᵖ_T B` without
requiring `Nonempty β`. -/
theorem PolyTimeTuringReducible.of_disjunctiveQueryList {qs : α → List β}
    (hqs : ComputableInPolyTime qs encA (encList encB))
    (hiff : ∀ a, a ∈ A ↔ ∃ b ∈ qs a, b ∈ B) :
    PolyTimeTuringReducible encA encB A B := by
  classical
  let O : Set (List Bool) := encB '' B
  have hsub : ComputableInPolyTime (fun p : α × β => encB p.2) (encPair encA encB) encBits :=
    (snd encA encB).encoding_comp
  have hbatch : ComputableInPolyTime (fun a => (qs a).map fun b => encB b)
      encA (encList encBits) :=
    ComputableInPolyTime.mapWithInput hqs hsub
  have hquery := (computableInPolyTimeWithOracle_map_mem O).preprocess hbatch
  have hany : ComputableInPolyTime (fun bs : List Bool => bs.any (fun b => b)) encBits encBool :=
    ComputableInPolyTime.bitsAnyWithInput id' (snd' id')
  refine ⟨fun a => ((qs a).map fun b => decide (encB b ∈ O)).any fun b => b,
    ?_, fun a => ?_⟩
  · convert hquery.map hany using 1
    funext a
    simp only [List.map_map, Function.comp_def]
  · rw [hiff a]
    simp only [List.any_eq_true, List.mem_map, O, encB.injective.mem_set_image]
    exact ⟨fun ⟨b, hb, hB⟩ => ⟨true, ⟨b, hb, decide_eq_true hB⟩, rfl⟩,
      fun ⟨_, ⟨b, hb, hdec⟩, rfl⟩ => ⟨b, hb, of_decide_eq_true hdec⟩⟩

/-- A polynomial-time query-list generator `qs : α → List β` witnessing
`a ∈ A ↔ ∀ b ∈ qs a, b ∈ B` gives a polynomial-time Turing reduction `A ≤ᵖ_T B` without
requiring `Nonempty β`. -/
theorem PolyTimeTuringReducible.of_conjunctiveQueryList {qs : α → List β}
    (hqs : ComputableInPolyTime qs encA (encList encB))
    (hiff : ∀ a, a ∈ A ↔ ∀ b ∈ qs a, b ∈ B) :
    PolyTimeTuringReducible encA encB A B := by
  classical
  let O : Set (List Bool) := encB '' B
  have hsub : ComputableInPolyTime (fun p : α × β => encB p.2) (encPair encA encB) encBits :=
    (snd encA encB).encoding_comp
  have hbatch : ComputableInPolyTime (fun a => (qs a).map fun b => encB b)
      encA (encList encBits) :=
    ComputableInPolyTime.mapWithInput hqs hsub
  have hquery := (computableInPolyTimeWithOracle_map_mem O).preprocess hbatch
  have hneg : ComputableInPolyTime (fun q : List Bool × Bool => !q.2)
      (encPair encBits encBool) encBool := by fun_prop
  have hall_fn : ComputableInPolyTime (fun bs : List Bool => !(bs.any fun b => !b))
      encBits encBool :=
    (by fun_prop : ComputableInPolyTime (!·) encBool encBool).comp
      (ComputableInPolyTime.bitsAnyWithInput id' hneg)
  refine ⟨fun a => !(((qs a).map fun b => decide (encB b ∈ O)).any fun b => !b),
    ?_, fun a => ?_⟩
  · convert hquery.map hall_fn using 1
    funext a
    simp only [List.map_map, Function.comp_def]
  · rw [hiff a, Bool.not_eq_true', List.any_eq_false]
    constructor
    · intro hall x hx
      rcases List.mem_map.mp hx with ⟨b, hb, rfl⟩
      have hbO : encB b ∈ O := ⟨b, hall b hb, rfl⟩
      simp [hbO]
    · intro hall b hb
      have hmem := List.mem_map_of_mem (f := fun b => decide (encB b ∈ O)) hb
      have hnot := hall (decide (encB b ∈ O)) hmem
      have hdec : decide (encB b ∈ O) = true := by
        cases h : decide (encB b ∈ O)
        · simp [h] at hnot
        · rfl
      exact encB.injective.mem_set_image.mp (of_decide_eq_true hdec)

end QueryList

/-! ### Hardness transfer along truth-table reductions -/

/-- Many-one hardness for `C` transfers across a polynomial-time truth-table reduction to
Turing hardness for `C`. -/
theorem PolyTimeHard.polyTimeTuringHard_of_truthTable
    {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (hL : PolyTimeHard C encL L) (hLB : PolyTimeTruthTableReducible encL encB L B) :
    PolyTimeTuringHard C encB B :=
  hL.polyTimeTuringHard_of_turing hLB.polyTimeTuringReducible

/-- `NP`-hardness transfers across a polynomial-time truth-table reduction to `NP`-Turing-hardness.
-/
theorem NPHard.npTuringHard_of_truthTable
    (hL : NPHard encL L) (hLB : PolyTimeTruthTableReducible encL encB L B) :
    NPTuringHard encB B :=
  hL.polyTimeTuringHard_of_truthTable hLB

/-- `NP`-hardness transfers across a polynomial-time disjunctive truth-table reduction to
`NP`-Turing-hardness. -/
theorem NPHard.npTuringHard_of_dtt
    (hL : NPHard encL L) (hLB : PolyTimeDTTReducible encL encB L B) :
    NPTuringHard encB B :=
  hL.npTuringHard_of_truthTable hLB.polyTimeTruthTableReducible

/-- `NP`-hardness transfers across a polynomial-time conjunctive truth-table reduction to
`NP`-Turing-hardness. -/
theorem NPHard.npTuringHard_of_ctt
    (hL : NPHard encL L) (hLB : PolyTimeCTTReducible encL encB L B) :
    NPTuringHard encB B :=
  hL.npTuringHard_of_truthTable hLB.polyTimeTruthTableReducible

/-! ### Fixed-arity bounded-tuple enumeration in polynomial time -/

/-- All lists of natural numbers of length at most `k` whose entries lie in `{0, …, n - 1}`. -/
@[expose]
def boundedNatLists (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => [] :: (List.range n).flatMap fun i => (boundedNatLists n k).map fun t => i :: t

private theorem mem_boundedNatLists_bounds {n : ℕ} :
    ∀ {k : ℕ} {cols : List ℕ}, cols ∈ boundedNatLists n k →
      cols.length ≤ k ∧ ∀ j ∈ cols, j < n
  | 0, cols, h => by
    simp only [boundedNatLists, List.mem_singleton] at h
    subst h
    simp
  | k + 1, cols, h => by
    simp only [boundedNatLists, List.mem_cons, List.mem_flatMap, List.mem_range,
      List.mem_map] at h
    rcases h with rfl | ⟨i, hi, t, ht, rfl⟩
    · simp
    · obtain ⟨hlen, hmem⟩ := mem_boundedNatLists_bounds ht
      refine ⟨Nat.succ_le_succ hlen, fun j hj => ?_⟩
      rcases List.mem_cons.mp hj with rfl | hjt
      · exact hi
      · exact hmem j hjt

private theorem mem_boundedNatLists_of_bounds {n : ℕ} :
    ∀ {k : ℕ} {cols : List ℕ}, cols.length ≤ k ∧ (∀ j ∈ cols, j < n) →
      cols ∈ boundedNatLists n k
  | 0, [], _ => by simp [boundedNatLists]
  | 0, _ :: _, ⟨hlen, _⟩ => by simp at hlen
  | k + 1, [], _ => by simp [boundedNatLists]
  | k + 1, i :: t, ⟨hlen, hlt⟩ => by
    simp only [boundedNatLists, List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map]
    exact Or.inr ⟨i, hlt i List.mem_cons_self, t,
      mem_boundedNatLists_of_bounds
        ⟨Nat.le_of_succ_le_succ hlen, fun j hj => hlt j (List.mem_cons_of_mem i hj)⟩,
      rfl⟩

/-- Exact specification of `boundedNatLists n k`: a list belongs to `boundedNatLists n k` if and
only if its length is at most `k` and every entry is strictly less than `n`. -/
theorem mem_boundedNatLists_iff {n k : ℕ} {cols : List ℕ} :
    cols ∈ boundedNatLists n k ↔ cols.length ≤ k ∧ ∀ j ∈ cols, j < n :=
  ⟨mem_boundedNatLists_bounds, mem_boundedNatLists_of_bounds⟩

/-- Every subset `T : Finset (Fin n)` of cardinality at most `k` is represented by some index list
`cols ∈ boundedNatLists n k` having the exact same underlying indices. -/
theorem exists_mem_boundedNatLists_of_card_le {n : ℕ} :
    ∀ {k : ℕ} (T : Finset (Fin n)), T.card ≤ k →
      ∃ cols ∈ boundedNatLists n k, ∀ j : Fin n, j ∈ T ↔ j.1 ∈ cols
  | 0, T, hT => by
    have h0 : T = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hT)
    subst h0
    exact ⟨[], by simp [boundedNatLists], fun _ => by simp⟩
  | k + 1, T, hT => by
    by_cases hne : T.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hne
      have hcard : (T.erase i₀).card ≤ k := by
        have := Finset.card_erase_of_mem hi₀
        omega
      obtain ⟨t, ht, hmem⟩ := exists_mem_boundedNatLists_of_card_le (T.erase i₀) hcard
      refine ⟨i₀.1 :: t, ?_, fun j => ?_⟩
      · simp only [boundedNatLists, List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map]
        exact Or.inr ⟨i₀.1, i₀.2, t, ht, rfl⟩
      · rw [List.mem_cons, ← hmem j, Finset.mem_erase]
        by_cases hji : j = i₀
        · subst hji; simp [hi₀]
        · have hne' : j.1 ≠ i₀.1 := fun h => hji (Fin.ext h)
          simp [hji, hne']
    · have h0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst h0
      exact ⟨[], by simp [boundedNatLists], fun _ => by simp⟩

/-- Concrete check on `boundedNatLists 2 1`. -/
theorem boundedNatLists_two_one : boundedNatLists 2 1 = [[], [0], [1]] := rfl

section BoundedPolyTime

attribute [local irreducible] encUnary encNat encPair encList encBool encBits

/-- For every fixed arity bound `k : ℕ`, enumerating `boundedNatLists n k` is computable in
polynomial time when `n` is given in unary. -/
@[fun_prop]
theorem computableInPolyTime_boundedNatLists (k : ℕ) :
    ComputableInPolyTime (fun n : ℕ => boundedNatLists n k) encUnary
      (encList (encList encUnary)) := by
  induction k with
  | zero =>
    unfold boundedNatLists
    fun_prop
  | succ k ih =>
    unfold boundedNatLists
    have hprev : ComputableInPolyTime (fun p : ℕ × ℕ => boundedNatLists p.1 k)
        (encPair encUnary encUnary) (encList (encList encUnary)) :=
      ih.comp (fst' (id' (encIn := encPair encUnary encUnary)))
    have h1 : ComputableInPolyTime
        (fun p : ℕ × ℕ => (boundedNatLists p.1 k).map fun t => p.2 :: t)
        (encPair encUnary encUnary) (encList (encList encUnary)) := by
      have hcons : ComputableInPolyTime (fun q : (ℕ × ℕ) × List ℕ => q.1.2 :: q.2)
          (encPair (encPair encUnary encUnary) (encList encUnary)) (encList encUnary) := by
        fun_prop
      exact ComputableInPolyTime.mapWithInput hprev hcons
    have h2 : ComputableInPolyTime
        (fun n : ℕ => (List.range n).flatMap fun i => (boundedNatLists n k).map fun t => i :: t)
        encUnary (encList (encList encUnary)) :=
      ComputableInPolyTime.flatMapWithInput ComputableInPolyTime.range h1
    exact (const ([] : List ℕ)).cons' h2

/-- **Parameterized bounded-tuple disjunctive truth-table reduction**: for fixed `k : ℕ`, if
membership in `A` is equivalent to the existence of a tuple `cols ∈ boundedNatLists (size a) k`
whose polynomial-time subproblem `sub (a, cols)` belongs to `B`, then `A ≤ᵖ_{dtt} B`. -/
theorem PolyTimeDTTReducible.of_boundedNatLists [Nonempty β] (k : ℕ)
    {size : α → ℕ} {sub : α × List ℕ → β}
    (hsize : ComputableInPolyTime size encA encUnary)
    (hsub : ComputableInPolyTime sub (encPair encA (encList encUnary)) encB)
    (hiff : ∀ a, a ∈ A ↔ ∃ cols ∈ boundedNatLists (size a) k, sub (a, cols) ∈ B) :
    PolyTimeDTTReducible encA encB A B := by
  have hqs : ComputableInPolyTime
      (fun a => (boundedNatLists (size a) k).map fun cols => sub (a, cols))
      encA (encList encB) :=
    ComputableInPolyTime.mapWithInput
      ((computableInPolyTime_boundedNatLists k).comp hsize) hsub
  refine PolyTimeDTTReducible.of_queryList hqs fun a => ?_
  rw [hiff a]
  simp only [List.mem_map]
  exact ⟨fun ⟨cols, hcols, hB⟩ => ⟨sub (a, cols), ⟨cols, hcols, rfl⟩, hB⟩,
    fun ⟨_, ⟨cols, hcols, rfl⟩, hB⟩ => ⟨cols, hcols, hB⟩⟩

/-- **Parameterized bounded-tuple polynomial-time Turing reduction**: for fixed `k : ℕ`, if
membership in `A` is equivalent to the existence of a tuple `cols ∈ boundedNatLists (size a) k`
whose polynomial-time subproblem `sub (a, cols)` belongs to `B`, then `A ≤ᵖ_T B` (without
requiring `Nonempty β`). -/
theorem PolyTimeTuringReducible.of_boundedNatLists (k : ℕ)
    {size : α → ℕ} {sub : α × List ℕ → β}
    (hsize : ComputableInPolyTime size encA encUnary)
    (hsub : ComputableInPolyTime sub (encPair encA (encList encUnary)) encB)
    (hiff : ∀ a, a ∈ A ↔ ∃ cols ∈ boundedNatLists (size a) k, sub (a, cols) ∈ B) :
    PolyTimeTuringReducible encA encB A B := by
  have hqs : ComputableInPolyTime
      (fun a => (boundedNatLists (size a) k).map fun cols => sub (a, cols))
      encA (encList encB) :=
    ComputableInPolyTime.mapWithInput
      ((computableInPolyTime_boundedNatLists k).comp hsize) hsub
  refine PolyTimeTuringReducible.of_disjunctiveQueryList hqs fun a => ?_
  rw [hiff a]
  simp only [List.mem_map]
  exact ⟨fun ⟨cols, hcols, hB⟩ => ⟨sub (a, cols), ⟨cols, hcols, rfl⟩, hB⟩,
    fun ⟨_, ⟨cols, hcols, rfl⟩, hB⟩ => ⟨cols, hcols, hB⟩⟩

end BoundedPolyTime

end Cslib.Complexity
