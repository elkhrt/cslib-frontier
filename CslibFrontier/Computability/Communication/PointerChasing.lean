/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Protocol
public import Mathlib.Data.Finset.Card

import Mathlib.Data.Fintype.Card

/-!
# Pointer chasing and round complexity of binary communication protocols

Two-party pointer chasing on `Fin n → Fin n`, internal-vertex combinatorial rectangles, and
speaker-alternation round complexity with round-padding normalization for
`Cslib.Communication.Protocol`.
-/

public section

namespace CslibFrontier.Computability.Communication

open Cslib.Communication Finset

/-- Recursive `r`-step pointer position on `Fin n` (`n ≥ 1`): starts at `0`, applies `fA` at odd
steps `r > 0`, and applies `fB` at even steps `r > 0`. -/
def pointerAt {n : ℕ} [NeZero n] : ℕ → (Fin n → Fin n) → (Fin n → Fin n) → Fin n
  | 0, _, _ => 0
  | r + 1, fA, fB =>
    if r % 2 = 0 then fA (pointerAt r fA fB) else fB (pointerAt r fA fB)

/-- Boolean parity of `z : Fin n` corresponding to `(z.val + 1) mod 2 = 1`. -/
def pointerParity {n : ℕ} (z : Fin n) : Bool :=
  decide ((z.val + 1) % 2 = 1)

/-- The `k`-step Boolean pointer chasing function on `(Fin n → Fin n)`. -/
def pointerChase {n : ℕ} [NeZero n] (k : ℕ) (fA fB : Fin n → Fin n) : Bool :=
  pointerParity (pointerAt k fA fB)

/-- At most `(n + 1) / 2` elements of `Fin n` have `pointerParity z = b`. -/
theorem card_filter_pointerParity_le (n : ℕ) (b : Bool) :
    #(Finset.univ.filter fun z : Fin n ↦ pointerParity z = b) ≤ (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ m _ =>
    by_cases hm : m = 0
    · subst hm; cases b <;> decide
    · cases m with
      | zero => contradiction
      | succ k =>
        have hinj : ∃ f : {z : Fin (k + 2) // pointerParity z = b} → Fin ((k + 3) / 2),
            Function.Injective f := by
          refine ⟨fun z ↦ ⟨z.1.val / 2, by omega⟩, fun z₁ z₂ h ↦ ?_⟩
          apply Subtype.ext; apply Fin.ext
          have hdiv : z₁.1.val / 2 = z₂.1.val / 2 := Fin.mk.inj h
          have hp₁ := z₁.2; have hp₂ := z₂.2
          simp only [pointerParity] at hp₁ hp₂
          cases b
          · simp only [decide_eq_false_iff_not] at hp₁ hp₂; omega
          · simp only [decide_eq_true_eq] at hp₁ hp₂; omega
        obtain ⟨f, hf⟩ := hinj
        have hc := Fintype.card_le_of_injective f hf
        simpa [Fintype.card_subtype] using hc

/-- For even `n`, exactly `n / 2` elements of `Fin n` have `pointerParity z = b`. -/
theorem card_filter_pointerParity_eq_half_of_even {n : ℕ} (hn : Even n) (b : Bool) :
    #(Finset.univ.filter fun z : Fin n ↦ pointerParity z = b) = n / 2 := by
  have hsum : #(Finset.univ.filter fun z : Fin n ↦ pointerParity z = true) +
      #(Finset.univ.filter fun z : Fin n ↦ pointerParity z = false) = n := by
    have hcomp := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun z ↦ pointerParity z = true)
    simpa [Bool.not_eq_true] using hcomp
  obtain ⟨m, rfl⟩ := hn
  have hhalf : (m + m + 1) / 2 = m := by omega
  have ht := card_filter_pointerParity_le (m + m) true
  have hf := card_filter_pointerParity_le (m + m) false
  rw [hhalf] at ht hf
  have h2m : (m + m) / 2 = m := by omega
  rw [h2m]
  cases b <;> omega

/-- Number of speaker rounds of `p` when starting from speaker turn `turn`. -/
def roundsFrom {X Y Z : Type*} : Bool → Protocol X Y Z → ℕ
  | _, .output _ => 0
  | true, .alice _ p₀ p₁ => max (max (roundsFrom true p₀) (roundsFrom true p₁)) 1
  | true, .bob _ p₀ p₁ => max (max (roundsFrom false p₀) (roundsFrom false p₁)) 1 + 1
  | false, .bob _ p₀ p₁ => max (max (roundsFrom false p₀) (roundsFrom false p₁)) 1
  | false, .alice _ p₀ p₁ => max (max (roundsFrom true p₀) (roundsFrom true p₁)) 1 + 1

/-- Predicate asserting that `p` is not a root `.bob` node. -/
def StartsWithAlice {X Y Z : Type*} : Protocol X Y Z → Prop
  | .bob _ _ _ => False
  | _ => True

private theorem roundsFrom_active_le_depth {X Y Z : Type*} :
    ∀ (p : Protocol X Y Z) (turn : Bool),
      (match turn, p with
        | true, .bob _ _ _ => False
        | false, .alice _ _ _ => False
        | _, _ => True) →
      roundsFrom turn p ≤ p.depth
  | .output _, _, _ => le_rfl
  | .alice _ _ _, false, h => False.elim h
  | .bob _ _ _, true, h => False.elim h
  | .alice _ p₀ p₁, true, _ => by
    simp only [roundsFrom, Protocol.depth_alice]
    have h₀ : roundsFrom true p₀ ≤ p₀.depth + 1 := by
      cases p₀ with
      | output _ => simp [roundsFrom]
      | alice _ _ _ => exact (roundsFrom_active_le_depth _ true trivial).trans (Nat.le_succ _)
      | bob s' q₀ q₁ =>
        have hq := roundsFrom_active_le_depth (.bob s' q₀ q₁) false trivial
        simp only [roundsFrom] at hq ⊢; omega
    have h₁ : roundsFrom true p₁ ≤ p₁.depth + 1 := by
      cases p₁ with
      | output _ => simp [roundsFrom]
      | alice _ _ _ => exact (roundsFrom_active_le_depth _ true trivial).trans (Nat.le_succ _)
      | bob s' q₀ q₁ =>
        have hq := roundsFrom_active_le_depth (.bob s' q₀ q₁) false trivial
        simp only [roundsFrom] at hq ⊢; omega
    omega
  | .bob _ p₀ p₁, false, _ => by
    simp only [roundsFrom, Protocol.depth_bob]
    have h₀ : roundsFrom false p₀ ≤ p₀.depth + 1 := by
      cases p₀ with
      | output _ => simp [roundsFrom]
      | bob _ _ _ => exact (roundsFrom_active_le_depth _ false trivial).trans (Nat.le_succ _)
      | alice s' q₀ q₁ =>
        have hq := roundsFrom_active_le_depth (.alice s' q₀ q₁) true trivial
        simp only [roundsFrom] at hq ⊢; omega
    have h₁ : roundsFrom false p₁ ≤ p₁.depth + 1 := by
      cases p₁ with
      | output _ => simp [roundsFrom]
      | bob _ _ _ => exact (roundsFrom_active_le_depth _ false trivial).trans (Nat.le_succ _)
      | alice s' q₀ q₁ =>
        have hq := roundsFrom_active_le_depth (.alice s' q₀ q₁) true trivial
        simp only [roundsFrom] at hq ⊢; omega
    omega

/-- Round complexity from Alice's turn is bounded by tree depth when Alice speaks first. -/
theorem roundsFrom_le_depth {X Y Z : Type*} {p : Protocol X Y Z} (hA : StartsWithAlice p) :
    roundsFrom true p ≤ p.depth :=
  roundsFrom_active_le_depth p true (by cases p <;> simp [StartsWithAlice] at hA ⊢)

end CslibFrontier.Computability.Communication
