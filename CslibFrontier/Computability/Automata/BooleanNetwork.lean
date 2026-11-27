/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/
module

public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-!
# Asynchronous Boolean Networks over Bit Strings

An asynchronous Boolean network of dimension `n` consists of `n` coordinate update rules
`f_i : BitString n → Bool`. Applying coordinate `i` updates bit `i` of a state `x : BitString n`
to `f_i x` while leaving all other coordinates unchanged. Finite update words `w : List (Fin n)`
act on `BitString n` by right-to-left composition of single-coordinate updates, generating a
finite transformation monoid on `BitString n` and a finite family of observable coordinate
Boolean functions.

## Main definitions

* `CslibFrontier.Computability.Automata.BooleanNetwork`: an `n`-node Boolean network represented
  by `rule : Fin n → Cslib.BooleanFunction n`.
* `CslibFrontier.Computability.Automata.BooleanNetwork.step`: single-coordinate state update
  `Function.update x i (N.rule i x)`.
* `CslibFrontier.Computability.Automata.BooleanNetwork.evalWord`: iterated asynchronous state
  transition along a finite update word `w : List (Fin n)`.
* `CslibFrontier.Computability.Automata.BooleanNetwork.UpdateSchedule`: nonempty update schedule
  with designated final readout coordinate `head` and preceding updates `tail`.
* `CslibFrontier.Computability.Automata.BooleanNetwork.observe`: Boolean function read at
  `S.head` after executing `S : UpdateSchedule n`.
* `CslibFrontier.Computability.Automata.BooleanNetwork.observablesAt`,
  `CslibFrontier.Computability.Automata.BooleanNetwork.observables`: observable Boolean functions
  generated at a coordinate and across the network.
* `CslibFrontier.Computability.Automata.BooleanNetwork.substitute`: composition of a scheduled
  network observable with `n` feed-in Boolean functions on `m`-bit inputs.

## Main results

* `CslibFrontier.Computability.Automata.BooleanNetwork.evalWord_apply_of_notMem`: coordinates
  absent from an update word remain invariant.
* `CslibFrontier.Computability.Automata.BooleanNetwork.exists_schedule_head_eq_of_mem`:
  leftmost-write suffix reduction for any coordinate updated by a word.
* `CslibFrontier.Computability.Automata.BooleanNetwork.observables_eq_word_coords`: equivalence
  between coordinate projections plus nonempty scheduled observables and all coordinate components
  of word-induced state maps.
* `CslibFrontier.Computability.Automata.BooleanNetwork.ncard_observables_le`: the observable
  Boolean function set of an `n`-node network has cardinality at most `2 ^ (2 ^ n)`.
* `CslibFrontier.Computability.Automata.BooleanNetwork.exists_universal_feedIn`: any family of
  `m`-bit Boolean functions indexed by `k`-bit parameters is realized by a `2 ^ k`-node network
  under feed-in substitution.
-/

public section

namespace CslibFrontier.Computability.Automata

open Cslib

/-- An `n`-node Boolean network assigning a Boolean update function `BitString n → Bool` to each
coordinate `i : Fin n`. -/
@[ext]
structure BooleanNetwork (n : ℕ) where
  /-- Coordinate Boolean transition rules. -/
  rule : Fin n → BooleanFunction n

namespace BooleanNetwork

/-- Asynchronous single-coordinate state transition updating bit `i` to `N.rule i x`. -/
@[expose]
def step {n : ℕ} (N : BooleanNetwork n) (i : Fin n) (x : BitString n) : BitString n :=
  Function.update x i (N.rule i x)

/-- `N.step i` sets coordinate `i` to `N.rule i x`. -/
@[simp]
theorem step_self {n : ℕ} (N : BooleanNetwork n) (i : Fin n) (x : BitString n) :
    N.step i x i = N.rule i x := by
  simp [step]

/-- `N.step i` leaves every coordinate `j ≠ i` unchanged. -/
@[simp]
theorem step_of_ne {n : ℕ} (N : BooleanNetwork n) {i j : Fin n} (x : BitString n) (h : j ≠ i) :
    N.step i x j = x j := by
  simp [step, h]

/-- Iterated asynchronous transition along an update word `w : List (Fin n)`, applying the head
coordinate last and mapping the empty word to `id`. -/
@[expose]
def evalWord {n : ℕ} (N : BooleanNetwork n) (w : List (Fin n)) : BitString n → BitString n :=
  w.foldr (fun i acc ↦ N.step i ∘ acc) id

/-- Evaluating the empty update word acts as the identity on `BitString n`. -/
@[simp]
theorem evalWord_nil {n : ℕ} (N : BooleanNetwork n) : N.evalWord [] = id := rfl

/-- Evaluating `i :: w` applies `N.step i` after `N.evalWord w`. -/
@[simp]
theorem evalWord_cons {n : ℕ} (N : BooleanNetwork n) (i : Fin n) (w : List (Fin n))
    (x : BitString n) :
    N.evalWord (i :: w) x = N.step i (N.evalWord w x) := rfl

/-- Word evaluation composes contravariantly over list concatenation. -/
theorem evalWord_append {n : ℕ} (N : BooleanNetwork n) (u v : List (Fin n)) (x : BitString n) :
    N.evalWord (u ++ v) x = N.evalWord u (N.evalWord v x) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, evalWord_cons, ih]

/-- Coordinates not appearing in `w` are fixed by `N.evalWord w`. -/
theorem evalWord_apply_of_notMem {n : ℕ} (N : BooleanNetwork n) {w : List (Fin n)} {j : Fin n}
    (hj : j ∉ w) (x : BitString n) :
    N.evalWord w x j = x j := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hji : j ≠ i := fun h ↦ hj (by simp [h])
    have hjw : j ∉ w := fun h ↦ hj (List.mem_cons_of_mem i h)
    rw [evalWord_cons, step_of_ne N _ hji, ih hjw]

/-- A nonempty asynchronous update schedule with final updated readout coordinate `head` and
earlier update steps `tail`. -/
@[ext]
structure UpdateSchedule (n : ℕ) where
  /-- Final updated coordinate read as output. -/
  head : Fin n
  /-- Earlier coordinate updates executed right-to-left prior to `head`. -/
  tail : List (Fin n)
  deriving DecidableEq

/-- Underlying nonempty word `S.head :: S.tail` of an `UpdateSchedule`. -/
@[expose]
def UpdateSchedule.toList {n : ℕ} (S : UpdateSchedule n) : List (Fin n) :=
  S.head :: S.tail

/-- Single-step schedule updating and reading coordinate `i`. -/
@[expose]
def UpdateSchedule.singleton {n : ℕ} (i : Fin n) : UpdateSchedule n :=
  ⟨i, []⟩

/-- The `n`-bit observable Boolean function read at `S.head` after running `S`. -/
@[expose]
def observe {n : ℕ} (N : BooleanNetwork n) (S : UpdateSchedule n) : BooleanFunction n :=
  fun x ↦ N.evalWord S.toList x S.head

/-- Evaluating `N.observe S` applies `N.rule S.head` to `N.evalWord S.tail x`. -/
@[simp]
theorem observe_apply {n : ℕ} (N : BooleanNetwork n) (S : UpdateSchedule n) (x : BitString n) :
    N.observe S x = N.rule S.head (N.evalWord S.tail x) := by
  simp [observe, UpdateSchedule.toList]

/-- Leftmost-write suffix reduction: if coordinate `j` appears in `w`, then coordinate `j` of
`N.evalWord w` equals `N.observe S` for a suffix schedule `S` with `S.head = j`. -/
theorem exists_schedule_head_eq_of_mem {n : ℕ} (N : BooleanNetwork n) {w : List (Fin n)}
    {j : Fin n} (hj : j ∈ w) :
    ∃ S : UpdateSchedule n, S.head = j ∧ (fun x ↦ N.evalWord w x j) = N.observe S := by
  induction w with
  | nil => nomatch hj
  | cons i w ih =>
    by_cases hji : j = i
    · subst hji
      refine ⟨⟨j, w⟩, rfl, ?_⟩
      ext x
      simp [observe, UpdateSchedule.toList]
    · have hjw : j ∈ w := (List.mem_cons.mp hj).resolve_left hji
      obtain ⟨S, hhead, hfun⟩ := ih hjw
      refine ⟨S, hhead, ?_⟩
      ext x
      rw [evalWord_cons, step_of_ne N _ hji]
      exact congrFun hfun x

/-- Observable Boolean functions at coordinate `j`, comprising the coordinate projection together
with all scheduled observables terminating at `j`. -/
def observablesAt {n : ℕ} (N : BooleanNetwork n) (j : Fin n) : Set (BooleanFunction n) :=
  {fun x ↦ x j} ∪ {g | ∃ S : UpdateSchedule n, S.head = j ∧ N.observe S = g}

/-- All observable Boolean functions generated by `N` across all coordinates. -/
def observables {n : ℕ} (N : BooleanNetwork n) : Set (BooleanFunction n) :=
  {g | ∃ j : Fin n, g = fun x ↦ x j} ∪ Set.range N.observe

/-- Equivalence between `N.observables` and the set of coordinate components of `N.evalWord w`
over all finite words `w : List (Fin n)`. -/
theorem observables_eq_word_coords {n : ℕ} (N : BooleanNetwork n) :
    N.observables = {g | ∃ (w : List (Fin n)) (j : Fin n), g = fun x ↦ N.evalWord w x j} := by
  ext g
  simp only [observables, Set.mem_union, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro (⟨j, rfl⟩ | ⟨S, rfl⟩)
    · exact ⟨[], j, rfl⟩
    · exact ⟨S.toList, S.head, rfl⟩
  · rintro ⟨w, j, rfl⟩
    by_cases hj : j ∈ w
    · obtain ⟨S, _, hfun⟩ := N.exists_schedule_head_eq_of_mem hj
      exact Or.inr ⟨S, hfun.symm⟩
    · left
      refine ⟨j, ?_⟩
      ext x
      exact N.evalWord_apply_of_notMem hj x

/-- The observable Boolean function set of an `n`-node network is finite and has cardinality at
most `2 ^ (2 ^ n)`. -/
theorem ncard_observables_le {n : ℕ} (N : BooleanNetwork n) :
    N.observables.ncard ≤ 2 ^ (2 ^ n) := by
  calc
    N.observables.ncard ≤ (Set.univ : Set (BooleanFunction n)).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    _ = Fintype.card (BooleanFunction n) := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    _ = 2 ^ (2 ^ n) := by
      change Fintype.card (BitString n → Bool) = 2 ^ (2 ^ n)
      rw [Fintype.card_fun, Fintype.card_bool, BitString.card]

/-- Substitute `n` feed-in Boolean functions on `m`-bit inputs into the scheduled observable
`N.observe S`. -/
@[expose]
def substitute {n m : ℕ} (N : BooleanNetwork n) (S : UpdateSchedule n)
    (feed : Fin n → BooleanFunction m) : BooleanFunction m :=
  fun x ↦ N.observe S (fun i ↦ feed i x)

/-- Pointwise evaluation of `N.substitute S feed`. -/
@[simp]
theorem substitute_apply {n m : ℕ} (N : BooleanNetwork n) (S : UpdateSchedule n)
    (feed : Fin n → BooleanFunction m) (x : BitString m) :
    N.substitute S feed x = N.observe S (fun i ↦ feed i x) := rfl

/-- Universal feed-in realization: every parameterized Boolean function family
`φ : BitString m → BitString k → Bool` is realized on a `2 ^ k`-node projection Boolean network
by single-step schedules indexed via `Cslib.BitString.equivFin k`. -/
theorem exists_universal_feedIn {m k : ℕ} (φ : BitString m → BitString k → Bool) :
    ∃ (N : BooleanNetwork (2 ^ k)) (feed : Fin (2 ^ k) → BooleanFunction m),
      ∀ p : BitString k, ∃ S : UpdateSchedule (2 ^ k),
        N.substitute S feed = fun x ↦ φ x p := by
  refine ⟨⟨fun i x ↦ x i⟩, fun i x ↦ φ x ((BitString.equivFin k).symm i), fun p ↦ ?_⟩
  refine ⟨UpdateSchedule.singleton (BitString.equivFin k p), ?_⟩
  ext x
  simp [UpdateSchedule.singleton]

end BooleanNetwork

end CslibFrontier.Computability.Automata
