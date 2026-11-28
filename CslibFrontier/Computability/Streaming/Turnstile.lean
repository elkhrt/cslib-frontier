/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Streaming.Basic
public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Turnstile (Dynamic) Streaming Algorithms and Linear Sketches

A **turnstile** (or **dynamic**) stream over an item universe `α` is a list of signed unit updates
`TurnstileUpdate.add a` (`+eₐ`) and `TurnstileUpdate.remove a` (`-eₐ`), accumulating an integer
frequency vector `freqVec s : α → ℤ`. Unlike insertion-only streams, turnstile streams have an
explicit inverse stream `negStream s` reversing and negating every update (`freqVec (negStream s) =
-freqVec s`).

This module connects turnstile streams to `Cslib.Streaming.Algorithm` from
`CslibFrontier.Computability.Streaming.Basic`:

* **Turnstile updates and frequency homomorphism**: `TurnstileUpdate`, `TurnstileStream`,
  `updateVec`, `freqVec`, `negStream`, `freqVec_append`, and `freqVec_negStream`.
* **Path-independent streaming algorithms**:
  `IsPathIndependent A` states that `A.state s` depends only on `freqVec s`. For any
  path-independent algorithm whose reachable states can be realized from `A.init`, frequency vectors
  returning `A` to `A.init` are closed under addition (`state_eq_init_of_freqVec_add`).
* **Linear-sketch streaming algorithms**: `linearSketchAlg M dec` maintains the integer sketch
  `M *ᵥ freqVec s : Fin k → ℤ` dynamically under insertions and deletions (`linearSketchAlg_state`),
  is path-independent (`linearSketchAlg_isPathIndependent`), and uses at most `b` bits of space on
  streams of length at most `m` whenever `|M r a| ≤ B` and `(2 * B * m + 1) ^ k ≤ 2 ^ b`
  (`linearSketchAlg_spaceLE`).
* **Scale-invariant partial specifications**: `IsScaleInvariant g` (`g (c • x) = g x` for `0 < c`),
  capturing support-based geometric and graph problems on turnstile streams.

## Main definitions

* `CslibFrontier.Computability.Streaming.Turnstile.TurnstileUpdate`,
  `CslibFrontier.Computability.Streaming.Turnstile.TurnstileStream`,
  `CslibFrontier.Computability.Streaming.Turnstile.freqVec`,
  `CslibFrontier.Computability.Streaming.Turnstile.negStream`
* `CslibFrontier.Computability.Streaming.Turnstile.IsPathIndependent`
* `CslibFrontier.Computability.Streaming.Turnstile.linearSketchAlg`
* `CslibFrontier.Computability.Streaming.Turnstile.IsScaleInvariant`

## Main results

* `CslibFrontier.Computability.Streaming.Turnstile.freqVec_append`,
  `CslibFrontier.Computability.Streaming.Turnstile.freqVec_negStream`
* `CslibFrontier.Computability.Streaming.Turnstile.IsPathIndependent.state_eq_init_of_freqVec_add`
* `CslibFrontier.Computability.Streaming.Turnstile.linearSketchAlg_state`,
  `CslibFrontier.Computability.Streaming.Turnstile.linearSketchAlg_isPathIndependent`,
  `CslibFrontier.Computability.Streaming.Turnstile.linearSketchAlg_spaceLE`
-/

public section

open scoped Matrix

namespace CslibFrontier.Computability.Streaming.Turnstile

/-! ### 1. Turnstile Updates and Frequency Vectors -/

/-- A single turnstile stream update over universe `α`: either inserting `a` (`+1`) or deleting `a`
(`-1`). -/
inductive TurnstileUpdate (α : Type*) : Type _
  | add (a : α)
  | remove (a : α)
  deriving DecidableEq, Repr

/-- Inverse turnstile update, swapping `add` and `remove`. -/
@[expose]
def TurnstileUpdate.inv {α : Type*} : TurnstileUpdate α → TurnstileUpdate α
  | .add a => .remove a
  | .remove a => .add a

@[simp]
theorem TurnstileUpdate.inv_inv {α : Type*} (u : TurnstileUpdate α) : u.inv.inv = u := by
  cases u <;> rfl

/-- A turnstile (dynamic) stream over `α` is a finite list of `add` and `remove` updates. -/
abbrev TurnstileStream (α : Type*) : Type _ :=
  List (TurnstileUpdate α)

/-- Signed unit frequency vector `± eₐ : α → ℤ` of a single turnstile update. -/
@[expose]
def updateVec {α : Type*} [DecidableEq α] : TurnstileUpdate α → (α → ℤ)
  | .add a => fun b => if b = a then 1 else 0
  | .remove a => fun b => if b = a then -1 else 0

@[simp]
theorem updateVec_inv {α : Type*} [DecidableEq α] (u : TurnstileUpdate α) :
    updateVec u.inv = -updateVec u := by
  cases u <;> ext b <;> simp only [TurnstileUpdate.inv, updateVec, Pi.neg_apply] <;>
    split_ifs <;> ring

/-- Accumulated integer frequency vector `x : α → ℤ` of a turnstile stream `s`. -/
@[expose]
def freqVec {α : Type*} [DecidableEq α] (s : TurnstileStream α) : α → ℤ :=
  s.foldl (fun x u => x + updateVec u) 0

@[simp]
theorem freqVec_nil {α : Type*} [DecidableEq α] :
    freqVec ([] : TurnstileStream α) = 0 :=
  rfl

private theorem foldl_updateVec_shift {α : Type*} [DecidableEq α] (s : TurnstileStream α)
    (x₀ : α → ℤ) :
    s.foldl (fun x u => x + updateVec u) x₀ = x₀ + freqVec s := by
  induction s generalizing x₀ with
  | nil => simp [freqVec]
  | cons u t ih =>
    simp only [List.foldl_cons, freqVec]
    rw [ih (x₀ + updateVec u), ih (0 + updateVec u), zero_add, add_assoc]

/-- `freqVec` is a monoid homomorphism from stream concatenation to pointwise vector addition. -/
@[simp]
theorem freqVec_append {α : Type*} [DecidableEq α] (s₁ s₂ : TurnstileStream α) :
    freqVec (s₁ ++ s₂) = freqVec s₁ + freqVec s₂ := by
  simp only [freqVec, List.foldl_append]
  exact foldl_updateVec_shift s₂ _

@[simp]
theorem freqVec_cons {α : Type*} [DecidableEq α] (u : TurnstileUpdate α) (s : TurnstileStream α) :
    freqVec (u :: s) = updateVec u + freqVec s := by
  simpa only [freqVec, List.foldl_cons, zero_add] using foldl_updateVec_shift s (updateVec u)

/-- Inverse stream reversing `s` and inverting every update. -/
@[expose]
def negStream {α : Type*} (s : TurnstileStream α) : TurnstileStream α :=
  s.reverse.map TurnstileUpdate.inv

/-- Processing `negStream s` negates the frequency vector of `s`. -/
@[simp]
theorem freqVec_negStream {α : Type*} [DecidableEq α] (s : TurnstileStream α) :
    freqVec (negStream s) = -freqVec s := by
  induction s with
  | nil => simp [negStream]
  | cons u t ih =>
    simp only [negStream, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      freqVec_append, freqVec_cons, freqVec_nil, add_zero, updateVec_inv] at ih ⊢
    rw [ih]
    ext a
    simp only [Pi.add_apply, Pi.neg_apply]
    ring

/-! ### 2. Path-Independent Streaming Algorithms -/

/-- A one-pass turnstile streaming algorithm `A` is **path-independent** if its memory state after
reading a stream `s` depends only on the final frequency vector `freqVec s`. -/
@[expose]
def IsPathIndependent {σ α β : Type*} [DecidableEq α]
    (A : Cslib.Streaming.Algorithm σ (TurnstileUpdate α) β) : Prop :=
  ∀ s₁ s₂ : TurnstileStream α, freqVec s₁ = freqVec s₂ → A.state s₁ = A.state s₂

namespace IsPathIndependent

variable {σ α β : Type*} [DecidableEq α]
  {A : Cslib.Streaming.Algorithm σ (TurnstileUpdate α) β}

/-- The output of a path-independent streaming algorithm depends only on `freqVec s`. -/
theorem run_eq_of_freqVec_eq (hA : IsPathIndependent A) {s₁ s₂ : TurnstileStream α}
    (hf : freqVec s₁ = freqVec s₂) : A.run s₁ = A.run s₂ :=
  congrArg A.output (hA s₁ s₂ hf)

/-- Additive closure of the zero-state kernel of a path-independent streaming algorithm: if `s₁`
and `s₂` both return `A` to `A.init`, then any stream `s` with `freqVec s = freqVec s₁ + freqVec s₂`
also returns `A` to `A.init`. -/
theorem state_eq_init_of_freqVec_add (hA : IsPathIndependent A) {s₁ s₂ s : TurnstileStream α}
    (h₁ : A.state s₁ = A.init) (h₂ : A.state s₂ = A.init)
    (hs : freqVec s = freqVec s₁ + freqVec s₂) : A.state s = A.init := by
  rw [hA s (s₁ ++ s₂) (hs.trans (freqVec_append s₁ s₂).symm), A.state_append, h₁]
  exact h₂

/-- Negation closure of the zero-state kernel of a path-independent streaming algorithm: if `s₁`
returns `A` to `A.init`, then any stream `s` with `freqVec s = -freqVec s₁` also returns `A` to
`A.init`. -/
theorem state_eq_init_of_freqVec_neg (hA : IsPathIndependent A) {s₁ s : TurnstileStream α}
    (h₁ : A.state s₁ = A.init) (hs : freqVec s = -freqVec s₁) : A.state s = A.init := by
  have hcancel : A.state (s₁ ++ negStream s₁) = A.init := by
    refine hA (s₁ ++ negStream s₁) [] ?_
    simp
  rw [A.state_append, h₁] at hcancel
  have hneg : A.state (negStream s₁) = A.init := hcancel
  rw [hA s (negStream s₁) (hs.trans (freqVec_negStream s₁).symm)]
  exact hneg

end IsPathIndependent

/-! ### 3. Linear-Sketch Turnstile Streaming Algorithms -/

/-- The deterministic turnstile streaming algorithm maintaining the linear sketch
`M *ᵥ freqVec s : Fin k → ℤ` in memory and applying `dec` at the end of the stream. -/
@[expose]
def linearSketchAlg {α β : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (M : Matrix (Fin k) α ℤ) (dec : (Fin k → ℤ) → β) :
    Cslib.Streaming.Algorithm (Fin k → ℤ) (TurnstileUpdate α) β where
  init := 0
  update q u :=
    match u with
    | .add a => fun r => q r + M r a
    | .remove a => fun r => q r - M r a
  output := dec

private theorem mulVec_updateVec {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (M : Matrix (Fin k) α ℤ) (u : TurnstileUpdate α) :
    M *ᵥ updateVec u =
      match u with
      | .add a => fun r => M r a
      | .remove a => fun r => -M r a := by
  cases u with
  | add a =>
    ext r
    simp [Matrix.mulVec, dotProduct, updateVec]
  | remove a =>
    ext r
    simp [Matrix.mulVec, dotProduct, updateVec]

private theorem linearSketchAlg_stateFrom {α β : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (M : Matrix (Fin k) α ℤ) (dec : (Fin k → ℤ) → β) (q : Fin k → ℤ) (s : TurnstileStream α) :
    (linearSketchAlg M dec).stateFrom q s = q + M *ᵥ freqVec s := by
  induction s generalizing q with
  | nil => simp [linearSketchAlg]
  | cons u t ih =>
    simp only [Cslib.Streaming.Algorithm.stateFrom_cons, freqVec_cons, Matrix.mulVec_add]
    rw [ih]
    have hstep : (linearSketchAlg M dec).update q u = q + M *ᵥ updateVec u := by
      rw [mulVec_updateVec]
      cases u <;> ext r <;> simp [linearSketchAlg, sub_eq_add_neg]
    rw [hstep, add_assoc]

/-- After reading any turnstile stream `s`, `linearSketchAlg M dec` holds `M *ᵥ freqVec s`. -/
@[simp]
theorem linearSketchAlg_state {α β : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (M : Matrix (Fin k) α ℤ) (dec : (Fin k → ℤ) → β) (s : TurnstileStream α) :
    (linearSketchAlg M dec).state s = M *ᵥ freqVec s := by
  rw [Cslib.Streaming.Algorithm.state, linearSketchAlg_stateFrom]
  simp [linearSketchAlg]

/-- Output characterization of `linearSketchAlg M dec`. -/
@[simp]
theorem linearSketchAlg_run {α β : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (M : Matrix (Fin k) α ℤ) (dec : (Fin k → ℤ) → β) (s : TurnstileStream α) :
    (linearSketchAlg M dec).run s = dec (M *ᵥ freqVec s) := by
  rw [Cslib.Streaming.Algorithm.run, linearSketchAlg_state]
  rfl

/-- Every linear-sketch streaming algorithm is path-independent. -/
theorem linearSketchAlg_isPathIndependent {α β : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (M : Matrix (Fin k) α ℤ) (dec : (Fin k → ℤ) → β) :
    IsPathIndependent (linearSketchAlg M dec) := by
  intro s₁ s₂ hf
  simp [hf]

private theorem linearSketchAlg_stateFrom_abs_le {α β : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (M : Matrix (Fin k) α ℤ) (dec : (Fin k → ℤ) → β) {B : ℕ}
    (hM : ∀ (r : Fin k) (a : α), |M r a| ≤ (B : ℤ))
    (s : TurnstileStream α) (q : Fin k → ℤ) (K : ℤ) (hq : ∀ r : Fin k, |q r| ≤ K) :
    ∀ r : Fin k, |(linearSketchAlg M dec).stateFrom q s r| ≤ K + (B : ℤ) * (s.length : ℤ) := by
  induction s generalizing q K with
  | nil =>
    intro r
    simpa using hq r
  | cons u t ih =>
    have hstep : ∀ r : Fin k, |(linearSketchAlg M dec).update q u r| ≤ K + (B : ℤ) := by
      intro r
      cases u with
      | add a =>
        dsimp only [linearSketchAlg]
        exact (abs_add_le (q r) (M r a)).trans (add_le_add (hq r) (hM r a))
      | remove a =>
        dsimp only [linearSketchAlg]
        have hsub : |q r - M r a| ≤ |q r| + |M r a| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (q r) (-M r a)
        exact hsub.trans (add_le_add (hq r) (hM r a))
    intro r
    have hrec := ih ((linearSketchAlg M dec).update q u) (K + (B : ℤ)) hstep r
    simp only [Cslib.Streaming.Algorithm.stateFrom_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one] at hrec ⊢
    linarith

/-- If every entry of `M : Matrix (Fin k) α ℤ` has absolute value at most `B` and
`(2 * B * m + 1) ^ k ≤ 2 ^ b`, then `linearSketchAlg M dec` uses at most `b` bits of space on
turnstile streams of length at most `m`. -/
theorem linearSketchAlg_spaceLE {α β : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (M : Matrix (Fin k) α ℤ) (dec : (Fin k → ℤ) → β) {B m b : ℕ}
    (hM : ∀ (r : Fin k) (a : α), |M r a| ≤ (B : ℤ))
    (hbits : (2 * B * m + 1) ^ k ≤ 2 ^ b) :
    (linearSketchAlg M dec).SpaceLE m b := by
  let L : ℤ := ((B * m : ℕ) : ℤ)
  let Box : Finset (Fin k → ℤ) := Fintype.piFinset fun _ : Fin k => Finset.Icc (-L) L
  have hsub : (linearSketchAlg M dec).reachable m ⊆ (Box : Set (Fin k → ℤ)) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Finset.mem_coe]
    refine Fintype.mem_piFinset.mpr fun r => Finset.mem_Icc.mpr ?_
    rw [← abs_le]
    have hlen := linearSketchAlg_stateFrom_abs_le M dec hM s 0 0 (fun _ => by simp) r
    have hmul : (B : ℤ) * (s.length : ℤ) ≤ L := by
      dsimp only [L]
      push_cast
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hs) (Nat.cast_nonneg B)
    have hst : (linearSketchAlg M dec).state s r = (linearSketchAlg M dec).stateFrom 0 s r := rfl
    rw [hst]
    linarith
  have hcard : Box.card = (2 * B * m + 1) ^ k := by
    simp only [Box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    have hmul2 : (L + 1 - -L).toNat = 2 * (B * m) + 1 := by dsimp only [L]; omega
    rw [hmul2]
    ring
  exact Cslib.Streaming.Algorithm.spaceLE_of_subset_finset hsub (hcard ▸ hbits)

/-! ### 4. Scale-Invariant Partial Specifications -/

/-- A partial specification `g : (α → ℤ) → Option γ` on frequency vectors is **scale-invariant** if
`g (c • x) = g x` for every positive integer `c > 0`. -/
@[expose]
def IsScaleInvariant {α γ : Type*} (g : (α → ℤ) → Option γ) : Prop :=
  ∀ (x : α → ℤ) (c : ℤ), 0 < c → g (c • x) = g x

/-- Positive natural-number scaling preserves any `IsScaleInvariant` specification. -/
theorem IsScaleInvariant.nat_smul {α γ : Type*} {g : (α → ℤ) → Option γ}
    (hg : IsScaleInvariant g) (x : α → ℤ) {c : ℕ} (hc : 0 < c) :
    g ((c : ℤ) • x) = g x :=
  hg x (c : ℤ) (Nat.cast_pos.mpr hc)

/-! ### 5. Non-Vacuity Check -/

private example :
    let M : Matrix (Fin 2) (Fin 3) ℤ := !![1, -1, 0; 0, 1, -1]
    let A := linearSketchAlg M (fun y => decide (y 0 ≠ 0 ∨ y 1 ≠ 0))
    IsPathIndependent A ∧ A.SpaceLE 3 6 := by
  intro M A
  refine ⟨linearSketchAlg_isPathIndependent M _, ?_⟩
  refine linearSketchAlg_spaceLE M _ (B := 1) ?_ (by norm_num)
  intro r a
  fin_cases r <;> fin_cases a <;> norm_num [M]

end CslibFrontier.Computability.Streaming.Turnstile
