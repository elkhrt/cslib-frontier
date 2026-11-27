/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.EXPSPACE
import CslibFrontier.Computability.Complexity.Classes.Space.Time
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Iterated exponential time and space classes

This module defines the `k`-fold iterated base-2 exponential function `Cslib.Complexity.iterExp`
and the corresponding deterministic complexity classes `Cslib.Complexity.kEXP` (`^kEXP`) and
`Cslib.Complexity.kEXPSPACE` (`^kEXPSPACE`), recovering `P`, `PSPACE`, `EXP`, and `EXPSPACE` at
`k = 0, 1`, and proves the deterministic space-to-time inclusion
`Cslib.Complexity.kEXPSPACE_subset_kEXP_succ` (`^kEXPSPACE ⊆ ^(k+1)EXP`).

## Main definitions

* `Cslib.Complexity.iterExp`: `k`-fold iterated base-2 exponential.
* `Cslib.Complexity.kEXP`: deterministic `k`-fold exponential time.
* `Cslib.Complexity.kEXPSPACE`: deterministic `k`-fold exponential space.

## Main results

* `Cslib.Complexity.kEXP_zero`, `Cslib.Complexity.kEXPSPACE_zero`: `kEXP enc 0 = P enc` and
  `kEXPSPACE enc 0 = PSPACE enc`.
* `Cslib.Complexity.kEXP_one`, `Cslib.Complexity.kEXPSPACE_one`: `kEXP enc 1 = EXP enc` and
  `kEXPSPACE enc 1 = EXPSPACE enc`.
* `Cslib.Complexity.kEXP_subset_kEXPSPACE`: `^kEXP ⊆ ^kEXPSPACE`.
* `Cslib.Complexity.kEXPSPACE_subset_kEXP_succ`: `^kEXPSPACE ⊆ ^(k+1)EXP`.
-/

public section

namespace Cslib.Complexity

open Filter

/-- `k`-fold iterated base-2 exponential (`iterExp 0 n = n`, `iterExp (k + 1) n = 2 ^ iterExp k n`).
-/
@[expose] def iterExp : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => 2 ^ iterExp k n

@[simp] theorem iterExp_zero (n : ℕ) : iterExp 0 n = n := rfl

@[simp] theorem iterExp_succ (k n : ℕ) : iterExp (k + 1) n = 2 ^ iterExp k n := rfl

theorem iterExp_mono {a b : ℕ} (k : ℕ) (h : a ≤ b) : iterExp k a ≤ iterExp k b := by
  induction k with
  | zero => exact h
  | succ k ih => exact Nat.pow_le_pow_right (by decide) ih

theorem self_le_iterExp (k n : ℕ) : n ≤ iterExp k n := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (Nat.lt_two_pow_self (n := iterExp k n)).le

/-- `k`-fold exponential deterministic time class `^kEXP`. -/
@[expose] def kEXP {α : Type*} (enc : α ↪ List Bool) (k : ℕ) : Set (Set α) :=
  ⋃ d : ℕ, DTIME enc fun n => iterExp k (n ^ d)

/-- `k`-fold exponential deterministic space class `^kEXPSPACE`. -/
@[expose] def kEXPSPACE {α : Type*} (enc : α ↪ List Bool) (k : ℕ) : Set (Set α) :=
  ⋃ d : ℕ, DSPACE enc fun n => iterExp k (n ^ d)

theorem mem_kEXP_iff {α : Type*} {enc : α ↪ List Bool} {k : ℕ} {A : Set α} :
    A ∈ kEXP enc k ↔ ∃ d : ℕ, A ∈ DTIME enc fun n => iterExp k (n ^ d) :=
  Set.mem_iUnion

theorem mem_kEXPSPACE_iff {α : Type*} {enc : α ↪ List Bool} {k : ℕ} {A : Set α} :
    A ∈ kEXPSPACE enc k ↔ ∃ d : ℕ, A ∈ DSPACE enc fun n => iterExp k (n ^ d) :=
  Set.mem_iUnion

theorem kEXP_zero {α : Type} (enc : α ↪ List Bool) : kEXP enc 0 = P enc := by
  ext A
  rw [mem_kEXP_iff, mem_P_iff_exists_mem_DTIME]
  rfl

theorem kEXPSPACE_zero {α : Type} (enc : α ↪ List Bool) : kEXPSPACE enc 0 = PSPACE enc := by
  ext A
  rw [mem_kEXPSPACE_iff, mem_PSPACE_iff_exists_mem_DSPACE]
  rfl

theorem kEXP_one {α : Type*} (enc : α ↪ List Bool) : kEXP enc 1 = EXP enc := by
  ext A
  rw [mem_kEXP_iff, mem_EXP_iff]
  rfl

theorem kEXPSPACE_one {α : Type*} (enc : α ↪ List Bool) : kEXPSPACE enc 1 = EXPSPACE enc := by
  ext A
  rw [mem_kEXPSPACE_iff, mem_EXPSPACE_iff]
  rfl

theorem kEXP_subset_kEXPSPACE {α : Type*} (enc : α ↪ List Bool) (k : ℕ) :
    kEXP enc k ⊆ kEXPSPACE enc k := fun _ hA =>
  let ⟨d, hd⟩ := mem_kEXP_iff.mp hA
  mem_kEXPSPACE_iff.mpr ⟨d, DTIME_subset_DSPACE hd⟩

/-- Deterministic `k`-fold exponential space is contained in `(k + 1)`-fold exponential time
(`^kEXPSPACE ⊆ ^(k+1)EXP`). -/
theorem kEXPSPACE_subset_kEXP_succ {α : Type*} (enc : α ↪ List Bool) (k : ℕ) :
    kEXPSPACE enc k ⊆ kEXP enc (k + 1) := by
  intro A hA
  obtain ⟨d, hd⟩ := mem_kEXPSPACE_iff.mp hA
  obtain ⟨c, hc⟩ := exists_mem_DTIME_of_mem_DSPACE hd
  refine mem_kEXP_iff.mpr ⟨d + 2, DTIME_mono_of_eventually_le ?_ hc⟩
  have haux : ∀ (C : ℕ) (j : ℕ), ∀ᶠ n in atTop,
      (n + 2) + C * iterExp j (n ^ d) ≤ iterExp j (n ^ (d + 2)) := by
    intro C j
    induction j generalizing C with
    | zero =>
      filter_upwards [eventually_ge_atTop (max 2 (C + 3))] with n hn
      have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
      have hnC : C + 3 ≤ n := le_trans (le_max_right _ _) hn
      have hnd : 1 ≤ n ^ d := Nat.one_le_pow d n (by omega)
      have hnd1 : n ≤ n ^ (d + 1) := by
        calc n = n ^ 1 := (pow_one n).symm
          _ ≤ n ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : n * n ^ d = n ^ (d + 1) := by ring
      have h3 : 2 * n ^ (d + 1) ≤ n ^ (d + 2) := by
        calc 2 * n ^ (d + 1) ≤ n * n ^ (d + 1) := Nat.mul_le_mul_right _ hn2
          _ = n ^ (d + 2) := by ring
      have hstep : (C + 3) * n ^ d ≤ n * n ^ d := Nat.mul_le_mul_right _ hnC
      simp only [iterExp_zero]
      nlinarith
    | succ j ih =>
      filter_upwards [ih (C + 2), eventually_ge_atTop 2] with n hih hn2
      have h1 : n + 2 ≤ 2 ^ n := by
        clear hih
        induction n, hn2 using Nat.le_induction with
        | base => decide
        | succ m _ ihm =>
          have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
          omega
      have h2 : C ≤ 2 ^ C := (Nat.lt_two_pow_self (n := C)).le
      have hA_pos : 1 ≤ iterExp j (n ^ d) :=
        (Nat.one_le_pow d n (by omega)).trans (self_le_iterExp j _)
      have hpow : n + 2 + C * 2 ^ iterExp j (n ^ d) ≤
          2 ^ (n + 1 + C + iterExp j (n ^ d)) := by
        have hpos1 : 1 ≤ 2 ^ C * 2 ^ iterExp j (n ^ d) :=
          Nat.mul_pos Nat.one_le_two_pow Nat.one_le_two_pow
        have hpos2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        calc n + 2 + C * 2 ^ iterExp j (n ^ d)
            ≤ 2 ^ n + 2 ^ C * 2 ^ iterExp j (n ^ d) :=
              Nat.add_le_add h1 (Nat.mul_le_mul_right _ h2)
          _ ≤ 2 ^ n * (2 ^ C * 2 ^ iterExp j (n ^ d)) +
                2 ^ n * (2 ^ C * 2 ^ iterExp j (n ^ d)) :=
              Nat.add_le_add (Nat.le_mul_of_pos_right _ hpos1) (Nat.le_mul_of_pos_left _ hpos2)
          _ = 2 ^ (n + 1 + C + iterExp j (n ^ d)) := by
              rw [pow_add, pow_add, pow_add, pow_one]; ring
      have hexp : n + 1 + C + iterExp j (n ^ d) ≤
          n + 2 + (C + 2) * iterExp j (n ^ d) := by
        have : C ≤ C * iterExp j (n ^ d) := Nat.le_mul_of_pos_right C hA_pos
        nlinarith
      exact hpow.trans (Nat.pow_le_pow_right (by decide) (hexp.trans hih))
  filter_upwards [haux (c + 2) k] with n hle
  have h1 : n + 2 ≤ 2 ^ (n + 2) := (Nat.lt_two_pow_self (n := n + 2)).le
  calc (n + 2) * 2 ^ (c * iterExp k (n ^ d))
      ≤ 2 ^ (n + 2) * 2 ^ (c * iterExp k (n ^ d)) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (n + 2 + c * iterExp k (n ^ d)) := (pow_add 2 _ _).symm
    _ ≤ 2 ^ iterExp k (n ^ (d + 2)) := Nat.pow_le_pow_right (by decide) (by
        have : 0 ≤ 2 * iterExp k (n ^ d) := Nat.zero_le _
        nlinarith)

end Cslib.Complexity
