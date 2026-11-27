/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.ReadOnce
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Basic

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option

/-!
# Unanimity and Sliding-Window Branching Programs

An ordered read-once *unanimity branching program*
(`CslibFrontier.Computability.BranchingProgram.UnanimityProgram`) tests an acceptance predicate at
every positive prefix layer `1, …, n` rather than only at layer `n`. Adding a single absorbing
rejection sink `none` embeds every width-`w` unanimity program into a width-`(w + 1)`
`ReadOnceProgram`, while every positive-length width-`w` `ReadOnceProgram` embeds into a width-`w`
unanimity program.

A unanimity program has *window size `t`* (`UnanimityProgram.IsSlidingWindow`) when `1 ≤ t` and at
every layer `i ≤ n - t`, any length-`t` input segment synchronizes all reachable layer-`i` states
to the same layer-`(i + t)` state.

## Main definitions

* `CslibFrontier.Computability.BranchingProgram.UnanimityProgram`: ordered read-once unanimity
  branching programs.
* `CslibFrontier.Computability.BranchingProgram.UnanimityProgram.toReadOnceProgram`: width-`(w + 1)`
  simulation as a `ReadOnceProgram`.
* `CslibFrontier.Computability.BranchingProgram.UnanimityProgram.IsSlidingWindow`:
  self-synchronizing window property.
* `CslibFrontier.Computability.BranchingProgram.unanimityProgramClass`,
  `CslibFrontier.Computability.BranchingProgram.slidingWindowClass`: finite-width Boolean function
  classes.

## Main results

* `CslibFrontier.Computability.BranchingProgram.UnanimityProgram.eval_toReadOnceProgram`:
  `toReadOnceProgram` preserves Boolean outputs on every input.
* `CslibFrontier.Computability.BranchingProgram.UnanimityProgram.accepts_ofReadOnceProgram`:
  `ofReadOnceProgram` preserves Boolean outputs for `1 ≤ n`.
-/

public section

namespace CslibFrontier.Computability.BranchingProgram

open Cslib.BranchingPrograms

/-- An ordered read-once unanimity branching program of length `n` over state type `Q` and input
alphabet `X`. -/
@[ext]
structure UnanimityProgram (n : ℕ) (Q X : Type*) where
  /-- Initial state at layer `0`. -/
  init : Q
  /-- Layer-indexed transition map. -/
  step : Fin n → Q → X → Q
  /-- Layerwise acceptance predicate checked after step `i : Fin n`. -/
  layerAccept : Fin n → Q → Bool

namespace UnanimityProgram

variable {n : ℕ} {Q X : Type*}

/-- Segment evaluation starting at layer `i` in state `q` along `y : List X`. -/
def evalFromList (U : UnanimityProgram n Q X) (i : ℕ) (q : Q) (y : List X) : Q :=
  match y with
  | [] => q
  | a :: as =>
    if hi : i < n then U.evalFromList (i + 1) (U.step ⟨i, hi⟩ q a) as else q

/-- State reached after reading the first `min k n` symbols of `x : Fin n → X`. -/
def evalPrefix (U : UnanimityProgram n Q X) (x : Fin n → X) : ℕ → Q
  | 0 => U.init
  | k + 1 =>
    let q := U.evalPrefix x k
    if hk : k < n then U.step ⟨k, hk⟩ q (x ⟨k, hk⟩) else q

/-- Reachable state set at layer `i`. -/
def reachable (U : UnanimityProgram n Q X) : ℕ → Set Q
  | 0 => {U.init}
  | i + 1 =>
    if hi : i < n then {q' | ∃ q ∈ U.reachable i, ∃ a : X, U.step ⟨i, hi⟩ q a = q'}
    else U.reachable i

/-- Boolean output of `U` on `x : Fin n → X`. -/
def accepts (U : UnanimityProgram n Q X) (x : Fin n → X) : Bool :=
  decide (∀ i : Fin n, U.layerAccept i (U.evalPrefix x (i.1 + 1)) = true)

/-- Sink-augmented `ReadOnceProgram` simulating `U` with state type `Option Q`. -/
def toReadOnceProgram (U : UnanimityProgram n Q X) : ReadOnceProgram n (Option Q) X where
  start := some U.init
  step i s a :=
    match s with
    | none => none
    | some q =>
      let q' := U.step i q a
      if U.layerAccept i q' then some q' else none
  accept s := s.isSome

private lemma foldl_toReadOnceProgram_prefix (U : UnanimityProgram n Q X) (x : Fin n → X)
    (k : ℕ) (hk : k ≤ n) :
    Fin.foldl k
      (fun (s : Option Q) (j : Fin k) ↦
        U.toReadOnceProgram.step ⟨j.1, Nat.lt_of_lt_of_le j.2 hk⟩ s
          (x ⟨j.1, Nat.lt_of_lt_of_le j.2 hk⟩))
      (some U.init) =
      if ∀ j : Fin k, U.layerAccept ⟨j.1, Nat.lt_of_lt_of_le j.2 hk⟩
          (U.evalPrefix x (j.1 + 1)) = true then
        some (U.evalPrefix x k)
      else
        none := by
  induction k with
  | zero => simp [Fin.foldl_zero, evalPrefix]
  | succ k ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (Nat.le_of_lt hk)]
    by_cases hall : ∀ j : Fin k, U.layerAccept ⟨j.1, Nat.lt_of_lt_of_le j.2 (Nat.le_of_lt hk)⟩
        (U.evalPrefix x (j.1 + 1)) = true
    · rw [ite_eq_left hall]
      have hlt : k < n := hk
      have hstep : U.evalPrefix x (k + 1) = U.step ⟨k, hlt⟩ (U.evalPrefix x k) (x ⟨k, hlt⟩) := by
        simp [evalPrefix, hlt]
      simp only [toReadOnceProgram, ← hstep]
      by_cases hlast : U.layerAccept ⟨k, hk⟩ (U.evalPrefix x (k + 1)) = true
      · have hall' : ∀ j : Fin (k + 1), U.layerAccept ⟨j.1, Nat.lt_of_lt_of_le j.2 hk⟩
            (U.evalPrefix x (j.1 + 1)) = true := fun j ↦
          Fin.lastCases (by simpa using hlast) (fun j₀ ↦ hall j₀) j
        simp [hlast, hall']
      · have hnot : ¬ ∀ j : Fin (k + 1), U.layerAccept ⟨j.1, Nat.lt_of_lt_of_le j.2 hk⟩
            (U.evalPrefix x (j.1 + 1)) = true := fun h ↦ hlast (h (Fin.last k))
        simp [hlast, hnot]
    · rw [ite_eq_right hall]
      have hnot : ¬ ∀ j : Fin (k + 1), U.layerAccept ⟨j.1, Nat.lt_of_lt_of_le j.2 hk⟩
          (U.evalPrefix x (j.1 + 1)) = true := fun h ↦ hall fun j ↦ h j.castSucc
      simp [toReadOnceProgram, hnot]

/-- `toReadOnceProgram` evaluates to `U.accepts x` on every input `x`. -/
@[simp]
theorem eval_toReadOnceProgram (U : UnanimityProgram n Q X) (x : Fin n → X) :
    U.toReadOnceProgram.eval x = U.accepts x := by
  have hfold := foldl_toReadOnceProgram_prefix U x n le_rfl
  rw [ReadOnceProgram.eval, ReadOnceProgram.finalState]
  change (U.toReadOnceProgram.accept _) = _
  rw [show U.toReadOnceProgram.start = some U.init from rfl, hfold, accepts]
  by_cases h : ∀ j : Fin n, U.layerAccept j (U.evalPrefix x (j.1 + 1)) = true <;>
    simp [toReadOnceProgram, h]

/-- Embeds a `ReadOnceProgram` into a `UnanimityProgram` over the same state type. -/
def ofReadOnceProgram (P : ReadOnceProgram n Q X) : UnanimityProgram n Q X where
  init := P.start
  step := P.step
  layerAccept i q := if i.1 + 1 = n then P.accept q else true

/-- For `1 ≤ n`, `ofReadOnceProgram P` evaluates to `P.eval x` on every input `x`. -/
@[simp]
theorem accepts_ofReadOnceProgram (P : ReadOnceProgram n Q X) (hn : 1 ≤ n) (x : Fin n → X) :
    (ofReadOnceProgram P).accepts x = P.eval x := by
  suffices hfold : ∀ k (hk : k ≤ n),
      Fin.foldl k (fun s (j : Fin k) ↦ P.step ⟨j.1, Nat.lt_of_lt_of_le j.2 hk⟩ s
        (x ⟨j.1, Nat.lt_of_lt_of_le j.2 hk⟩)) P.start =
      (ofReadOnceProgram P).evalPrefix x k by
    rw [ReadOnceProgram.eval, ReadOnceProgram.finalState, hfold n le_rfl, accepts,
      Bool.eq_iff_iff, decide_eq_true_iff]
    refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
    · have hlast := h ⟨n - 1, by omega⟩
      have hn1 : (n - 1) + 1 = n := by omega
      change (if (n - 1) + 1 = n then P.accept ((ofReadOnceProgram P).evalPrefix x ((n - 1) + 1))
        else true) = true at hlast
      rw [ite_eq_left hn1, hn1] at hlast
      exact hlast
    · change (if i.1 + 1 = n then P.accept ((ofReadOnceProgram P).evalPrefix x (i.1 + 1))
        else true) = true
      by_cases hi : i.1 + 1 = n
      · rw [ite_eq_left hi, hi]
        exact h
      · rw [ite_eq_right hi]
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlt : k < n := hk
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (Nat.le_of_lt hlt)]
    simp [ofReadOnceProgram, evalPrefix, hlt]

/-- Sliding-window self-synchronization property with window size `t`. -/
def IsSlidingWindow (t : ℕ) (U : UnanimityProgram n Q X) : Prop :=
  1 ≤ t ∧ ∀ (i : ℕ), i + t ≤ n → ∀ (y : List X), y.length = t →
    ∀ q q' : Q, q ∈ U.reachable i → q' ∈ U.reachable i →
      U.evalFromList i q y = U.evalFromList i q' y

end UnanimityProgram

/-- Class of Boolean functions computed by width-`w` unanimity programs of length `n`. -/
def unanimityProgramClass (n w : ℕ) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ U : UnanimityProgram n (Fin w) Bool, U.accepts = f}

/-- Class of Boolean functions computed by width-`w` unanimity programs with window size `t`. -/
def slidingWindowClass (n w t : ℕ) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ U : UnanimityProgram n (Fin w) Bool, U.IsSlidingWindow t ∧ U.accepts = f}

end CslibFrontier.Computability.BranchingProgram
