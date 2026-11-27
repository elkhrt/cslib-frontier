/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Classes.EXPSPACE
public import CslibFrontier.Computability.Complexity.Classes.Space.Closure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace
public import CslibFrontier.Foundations.Data.BitString.Enumeration

import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BoundedSearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec
import CslibFrontier.Foundations.Data.Nat.AffineBound
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import Mathlib.Computability.Halting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Iterated Exponential Space Complexity Classes (`k`-EXPSPACE)

This module defines the iterated base-2 exponential tower `iterExpTwo k n` and the deterministic
iterated-exponential space hierarchy `KEXPSPACE enc k` (with abbreviations `TwoEXPSPACE` and
`ThreeEXPSPACE`) directly over `Cslib.Complexity.DSPACE`, `Cslib.Complexity.PSPACE`, and
`Cslib.Complexity.EXPSPACE`.

## Main definitions

* `Cslib.Complexity.iterExpTwo`: the `k`-fold base-2 exponential tower
  `iterExpTwo 0 n = n`, `iterExpTwo (k + 1) n = 2 ^ iterExpTwo k n`.
* `Cslib.Complexity.KEXPSPACE`: deterministic `k`-fold exponential space,
  `⋃ d, DSPACE enc (fun n => iterExpTwo k (n ^ d))`.
* `Cslib.Complexity.TwoEXPSPACE`, `Cslib.Complexity.ThreeEXPSPACE`: `2`-EXPSPACE and
  `3`-EXPSPACE.

## Main results

* `Cslib.Complexity.KEXPSPACE_zero_eq_PSPACE`,
  `Cslib.Complexity.KEXPSPACE_one_eq_EXPSPACE`: identification of levels `0` and `1` with
  `Cslib.Complexity.PSPACE` and `Cslib.Complexity.EXPSPACE`.
* `Cslib.Complexity.DSPACE_iterExpTwo_subset_KEXPSPACE`,
  `Cslib.Complexity.KEXPSPACE_mono`: monotonicity and polynomial-exponent absorption.
* `Cslib.Complexity.compl_mem_KEXPSPACE`, `Cslib.Complexity.inter_mem_KEXPSPACE`,
  `Cslib.Complexity.union_mem_KEXPSPACE`,
  `Cslib.Complexity.PolyTimeReducible.mem_KEXPSPACE`: Boolean and reduction closures.
* `Cslib.Complexity.computableInSpace_two_pow_unary`,
  `Cslib.Complexity.computableInSpace_iterExpTwo_unary`: computing iterated base-2
  exponential lengths in unary within `iterExpTwo`-bounded work space.
* `Cslib.Complexity.setOf_exists_mem_KEXPSPACE`,
  `Cslib.Complexity.setOf_forall_mem_KEXPSPACE`,
  `Cslib.Complexity.setOf_exists_forall_mem_KEXPSPACE`,
  `Cslib.Complexity.setOf_exists_forall_mem_KEXPSPACE_iterExpTwo`: streaming quantifier
  elimination over `PSPACE` verifiers for `iterExpTwo k`-length bitstring witnesses.
-/

public section

namespace Cslib.Complexity

open Cslib Filter Turing Turing.MultiTapeTM

/-! ### Iterated base-2 exponential tower -/

/-- The `k`-fold base-2 exponential tower starting from `n`:
`iterExpTwo 0 n = n` and `iterExpTwo (k + 1) n = 2 ^ iterExpTwo k n`. -/
@[expose] def iterExpTwo : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => 2 ^ iterExpTwo k n

@[simp] theorem iterExpTwo_zero (n : ℕ) : iterExpTwo 0 n = n := rfl

@[simp] theorem iterExpTwo_succ (k n : ℕ) : iterExpTwo (k + 1) n = 2 ^ iterExpTwo k n := rfl

@[simp] theorem iterExpTwo_one (n : ℕ) : iterExpTwo 1 n = 2 ^ n := rfl

theorem iterExpTwo_two (n : ℕ) : iterExpTwo 2 n = 2 ^ 2 ^ n := rfl

theorem iterExpTwo_three (n : ℕ) : iterExpTwo 3 n = 2 ^ 2 ^ 2 ^ n := rfl

theorem iterExpTwo_pos {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : 0 < iterExpTwo k n := by
  cases k with
  | zero => omega
  | succ k => exact Nat.two_pow_pos _

theorem le_iterExpTwo (k n : ℕ) : n ≤ iterExpTwo k n := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans Nat.lt_two_pow_self.le

theorem iterExpTwo_mono_right (k : ℕ) : Monotone (iterExpTwo k) := by
  induction k with
  | zero => intro _ _ h; exact h
  | succ k ih => intro _ _ h; exact Nat.pow_le_pow_right two_pos (ih h)

theorem iterExpTwo_mono_left {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (n : ℕ) :
    iterExpTwo k₁ n ≤ iterExpTwo k₂ n := by
  induction hk with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Nat.lt_two_pow_self.le

theorem add_mul_iterExpTwo_le {k : ℕ} (hk : 1 ≤ k) (a b x : ℕ) :
    a + b * iterExpTwo k x ≤ iterExpTwo k (x + a + b + k) := by
  induction k generalizing a b with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      dsimp only [iterExpTwo]
      have h1 : a + b * 2 ^ x ≤ (a + b) * 2 ^ x := by
        rcases Nat.eq_zero_or_pos b with rfl | hb
        · simpa using Nat.le_mul_of_pos_right a (Nat.two_pow_pos x)
        · rw [Nat.add_mul]
          exact Nat.add_le_add_right (Nat.le_mul_of_pos_right a (Nat.two_pow_pos x)) _
      have h2 : a + b ≤ 2 ^ (a + b) := Nat.lt_two_pow_self.le
      calc a + b * 2 ^ x ≤ (a + b) * 2 ^ x := h1
        _ ≤ 2 ^ (a + b) * 2 ^ x := Nat.mul_le_mul_right _ h2
        _ = 2 ^ (x + a + b) := by rw [← pow_add]; congr 1; omega
        _ ≤ 2 ^ (x + a + b + 1) := Nat.pow_le_pow_right two_pos (by omega)
    | succ k' =>
      have hk' : 1 ≤ k' + 1 := Nat.succ_le_succ (Nat.zero_le _)
      have h1 : a + b * 2 ^ iterExpTwo (k' + 1) x ≤ 2 ^ (iterExpTwo (k' + 1) x + a + b) := by
        have hstep : a + b * 2 ^ iterExpTwo (k' + 1) x ≤ (a + b) * 2 ^ iterExpTwo (k' + 1) x := by
          rcases Nat.eq_zero_or_pos b with rfl | hb
          · simpa using Nat.le_mul_of_pos_right a (Nat.two_pow_pos _)
          · rw [Nat.add_mul]
            exact Nat.add_le_add_right (Nat.le_mul_of_pos_right a (Nat.two_pow_pos _)) _
        calc a + b * 2 ^ iterExpTwo (k' + 1) x
            ≤ (a + b) * 2 ^ iterExpTwo (k' + 1) x := hstep
          _ ≤ 2 ^ (a + b) * 2 ^ iterExpTwo (k' + 1) x :=
              Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
          _ = 2 ^ (iterExpTwo (k' + 1) x + a + b) := by rw [← pow_add]; congr 1; omega
      have h2 : iterExpTwo (k' + 1) x + a + b ≤ iterExpTwo (k' + 1) (x + a + b + (k' + 2)) := by
        have hih := ih hk' (a + b) 1
        have heq : x + (a + b) + 1 + (k' + 1) = x + a + b + (k' + 2) := by omega
        rw [one_mul, heq] at hih
        omega
      exact h1.trans (Nat.pow_le_pow_right two_pos h2)

/-- Polynomial functions of `iterExpTwo k (h n)` are absorbed into `iterExpTwo k (h' n)` for a
polynomially bounded `h'`. -/
theorem exists_polynomiallyBounded_poly_iterExpTwo (k c d : ℕ) {h : ℕ → ℕ}
    (hh : PolynomiallyBounded h) :
    ∃ h' : ℕ → ℕ, PolynomiallyBounded h' ∧
      ∀ n, c * (iterExpTwo k (h n) + 1) ^ d ≤ iterExpTwo k (h' n) := by
  cases k with
  | zero =>
    exact ⟨fun n => c * (h n + 1) ^ d, by fun_prop, fun _ => le_rfl⟩
  | succ k =>
    cases k with
    | zero =>
      refine ⟨fun n => d * (h n + 1) + c, by fun_prop, fun n => ?_⟩
      dsimp only [iterExpTwo]
      have hbase : 2 ^ h n + 1 ≤ 2 ^ (h n + 1) := by
        rw [pow_succ]; have := Nat.two_pow_pos (h n); omega
      calc c * (2 ^ h n + 1) ^ d ≤ c * (2 ^ (h n + 1)) ^ d :=
            Nat.mul_le_mul_left c (Nat.pow_le_pow_left hbase d)
        _ = c * 2 ^ (d * (h n + 1)) := by rw [← pow_mul, Nat.mul_comm (h n + 1) d]
        _ ≤ 2 ^ c * 2 ^ (d * (h n + 1)) := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
        _ = 2 ^ (d * (h n + 1) + c) := by rw [← pow_add, Nat.add_comm]
    | succ k' =>
      let C := c * 2 ^ d
      refine ⟨fun n => h n + d + C + 2 * (k' + 1) + 1, by fun_prop, fun n => ?_⟩
      have hk1 : 1 ≤ k' + 1 := Nat.succ_le_succ (Nat.zero_le _)
      have hpos : 1 ≤ iterExpTwo (k' + 2) (h n) := iterExpTwo_pos (by omega) (h n)
      have hbase : iterExpTwo (k' + 2) (h n) + 1 ≤ 2 * iterExpTwo (k' + 2) (h n) := by omega
      have hpow : (iterExpTwo (k' + 2) (h n)) ^ d ≤
          2 ^ iterExpTwo (k' + 1) (h n + d + (k' + 1)) := by
        rw [iterExpTwo_succ, ← pow_mul]
        refine Nat.pow_le_pow_right two_pos ?_
        have := add_mul_iterExpTwo_le hk1 0 d (h n)
        simpa [Nat.mul_comm] using this
      have hmul : C * 2 ^ iterExpTwo (k' + 1) (h n + d + (k' + 1)) ≤
          2 ^ (iterExpTwo (k' + 1) (h n + d + (k' + 1)) + C) := by
        calc C * 2 ^ iterExpTwo (k' + 1) (h n + d + (k' + 1))
            ≤ 2 ^ C * 2 ^ iterExpTwo (k' + 1) (h n + d + (k' + 1)) :=
              Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
          _ = 2 ^ (iterExpTwo (k' + 1) (h n + d + (k' + 1)) + C) := by
              rw [← pow_add, Nat.add_comm]
      have hexp : iterExpTwo (k' + 1) (h n + d + (k' + 1)) + C ≤
          iterExpTwo (k' + 1) (h n + d + C + 2 * (k' + 1) + 1) := by
        have hstep := add_mul_iterExpTwo_le hk1 C 1 (h n + d + (k' + 1))
        rw [one_mul] at hstep
        have heq : h n + d + (k' + 1) + C + 1 + (k' + 1) =
            h n + d + C + 2 * (k' + 1) + 1 := by omega
        rw [heq] at hstep
        omega
      calc c * (iterExpTwo (k' + 2) (h n) + 1) ^ d
          ≤ c * (2 * iterExpTwo (k' + 2) (h n)) ^ d :=
            Nat.mul_le_mul_left c (Nat.pow_le_pow_left hbase d)
        _ = C * (iterExpTwo (k' + 2) (h n)) ^ d := by rw [Nat.mul_pow, ← Nat.mul_assoc]
        _ ≤ C * 2 ^ iterExpTwo (k' + 1) (h n + d + (k' + 1)) :=
            Nat.mul_le_mul_left C hpow
        _ ≤ 2 ^ (iterExpTwo (k' + 1) (h n + d + (k' + 1)) + C) := hmul
        _ ≤ 2 ^ iterExpTwo (k' + 1) (h n + d + C + 2 * (k' + 1) + 1) :=
            Nat.pow_le_pow_right two_pos hexp

/-! ### The `KEXPSPACE` hierarchy over `Cslib.Complexity.DSPACE` -/

/-- Deterministic `k`-fold exponential space on encoded instances `enc : α ↪ List Bool`:
the union of `DSPACE enc (fun n => iterExpTwo k (n ^ d))` over all `d : ℕ`. -/
def KEXPSPACE {α : Type*} (enc : α ↪ List Bool) (k : ℕ) : Set (Set α) :=
  ⋃ d, DSPACE enc fun n => iterExpTwo k (n ^ d)

/-- Deterministic doubly-exponential space (`2-EXPSPACE`). -/
abbrev TwoEXPSPACE {α : Type*} (enc : α ↪ List Bool) : Set (Set α) :=
  KEXPSPACE enc 2

/-- Deterministic triply-exponential space (`3-EXPSPACE`). -/
abbrev ThreeEXPSPACE {α : Type*} (enc : α ↪ List Bool) : Set (Set α) :=
  KEXPSPACE enc 3

theorem mem_KEXPSPACE_iff {α : Type*} {enc : α ↪ List Bool} {k : ℕ} {A : Set α} :
    A ∈ KEXPSPACE enc k ↔ ∃ d, A ∈ DSPACE enc fun n => iterExpTwo k (n ^ d) :=
  Set.mem_iUnion

theorem KEXPSPACE_zero_eq_PSPACE {α : Type} (enc : α ↪ List Bool) :
    KEXPSPACE enc 0 = PSPACE enc :=
  Set.ext fun _ => mem_KEXPSPACE_iff.trans mem_PSPACE_iff_exists_mem_DSPACE.symm

theorem KEXPSPACE_one_eq_EXPSPACE {α : Type*} (enc : α ↪ List Bool) :
    KEXPSPACE enc 1 = EXPSPACE enc :=
  Set.ext fun _ => mem_KEXPSPACE_iff.trans mem_EXPSPACE_iff.symm

theorem DSPACE_iterExpTwo_subset_KEXPSPACE {α : Type*} {enc : α ↪ List Bool} {k : ℕ}
    {h : ℕ → ℕ} (hh : PolynomiallyBounded h) :
    DSPACE enc (fun n => iterExpTwo k (h n)) ⊆ KEXPSPACE enc k := fun _ hA =>
  let ⟨d, hd⟩ := hh
  mem_KEXPSPACE_iff.mpr
    ⟨d, DSPACE_mono_of_eventually_le (hd.mono fun _ hn => iterExpTwo_mono_right k hn) hA⟩

theorem KEXPSPACE_mono {α : Type*} {enc : α ↪ List Bool} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    KEXPSPACE enc k₁ ⊆ KEXPSPACE enc k₂ := fun _ hA =>
  let ⟨d, hd⟩ := mem_KEXPSPACE_iff.mp hA
  mem_KEXPSPACE_iff.mpr ⟨d, DSPACE_mono (fun n => iterExpTwo_mono_left hk (n ^ d)) hd⟩

theorem PSPACE_subset_KEXPSPACE {α : Type} {enc : α ↪ List Bool} (k : ℕ) :
    PSPACE enc ⊆ KEXPSPACE enc k := by
  rw [← KEXPSPACE_zero_eq_PSPACE]
  exact KEXPSPACE_mono (Nat.zero_le k)

theorem EXPSPACE_subset_TwoEXPSPACE {α : Type*} {enc : α ↪ List Bool} :
    EXPSPACE enc ⊆ TwoEXPSPACE enc :=
  KEXPSPACE_mono (by decide : 1 ≤ 2)

theorem TwoEXPSPACE_subset_ThreeEXPSPACE {α : Type*} {enc : α ↪ List Bool} :
    TwoEXPSPACE enc ⊆ ThreeEXPSPACE enc :=
  KEXPSPACE_mono (by decide : 2 ≤ 3)

/-- A Boolean decider computable in `ComputableInSpace` with space bounded by
`iterExpTwo k (h (enc a).length)` (for a polynomially bounded `h`) places its language in
`KEXPSPACE enc k`. -/
theorem mem_KEXPSPACE_of_computableInSpace {α : Type} {enc : α ↪ List Bool} {k : ℕ}
    {A : Set α} {f : α → Bool} {S : α → ℕ} {h : ℕ → ℕ}
    (hh : PolynomiallyBounded h)
    (hf : ComputableInSpace f enc encBool S)
    (hS : ∀ a, S a ≤ iterExpTwo k (h (enc a).length))
    (hA : ∀ a, a ∈ A ↔ f a = true) :
    A ∈ KEXPSPACE enc k := by
  obtain ⟨t, c, hc, -⟩ := hf
  have hdec : DecidableInTimeAndSpace A enc t
      (fun a => c * iterExpTwo k (h (enc a).length) + c) :=
    decidableInTimeAndSpace_iff.mpr
      ⟨f, hc.mono (fun _ => le_rfl) fun a => by
        have := hS a
        have hmul : c * (S a + 1) ≤ c * (iterExpTwo k (h (enc a).length) + 1) :=
          Nat.mul_le_mul_left c (Nat.add_le_add_right this 1)
        linarith, hA⟩
  exact DSPACE_iterExpTwo_subset_KEXPSPACE hh (mem_DSPACE_iff.mpr ⟨c, c, t, hdec⟩)

/-- `KEXPSPACE` is closed under complement. -/
theorem compl_mem_KEXPSPACE {α : Type} {enc : α ↪ List Bool} {k : ℕ} {A : Set α}
    (hA : A ∈ KEXPSPACE enc k) : Aᶜ ∈ KEXPSPACE enc k :=
  let ⟨d, hd⟩ := mem_KEXPSPACE_iff.mp hA
  mem_KEXPSPACE_iff.mpr ⟨d, compl_mem_DSPACE hd⟩

/-- `KEXPSPACE` is closed under intersection. -/
theorem inter_mem_KEXPSPACE {α : Type} {enc : α ↪ List Bool} {k : ℕ} {A B : Set α}
    (hA : A ∈ KEXPSPACE enc k) (hB : B ∈ KEXPSPACE enc k) :
    A ∩ B ∈ KEXPSPACE enc k := by
  obtain ⟨d₁, hd₁⟩ := mem_KEXPSPACE_iff.mp hA
  obtain ⟨d₂, hd₂⟩ := mem_KEXPSPACE_iff.mp hB
  obtain ⟨c₁, c₂, t₁, h₁⟩ := hd₁
  obtain ⟨c₃, c₄, t₂, h₂⟩ := hd₂
  obtain ⟨f₁, hf₁, hA₁⟩ := decidableInTimeAndSpace_iff.mp h₁
  obtain ⟨f₂, hf₂, hB₂⟩ := decidableInTimeAndSpace_iff.mp h₂
  let h : ℕ → ℕ := fun n => (n + 1) ^ max d₁ d₂
  have hh : PolynomiallyBounded h := by dsimp only [h]; fun_prop
  have hle₁ : ∀ n, n ^ d₁ ≤ h n := fun n =>
    (Nat.pow_le_pow_left (Nat.le_succ n) d₁).trans
      (Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_left d₁ d₂))
  have hle₂ : ∀ n, n ^ d₂ ≤ h n := fun n =>
    (Nat.pow_le_pow_left (Nat.le_succ n) d₂).trans
      (Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_right d₁ d₂))
  have hs₁ : ComputableInSpace f₁ enc encBool fun a =>
      c₁ * iterExpTwo k (h (enc a).length) + c₂ :=
    ⟨fun a => t₁ (enc a).length, 1,
      hf₁.mono (fun _ => le_rfl) fun a => by
        dsimp only
        have := iterExpTwo_mono_right k (hle₁ (enc a).length)
        nlinarith,
      fun a => by
        simp only [encBool_apply, List.length_singleton]
        omega⟩
  have hs₂ : ComputableInSpace f₂ enc encBool fun a =>
      c₃ * iterExpTwo k (h (enc a).length) + c₄ :=
    ⟨fun a => t₂ (enc a).length, 1,
      hf₂.mono (fun _ => le_rfl) fun a => by
        dsimp only
        have := iterExpTwo_mono_right k (hle₂ (enc a).length)
        nlinarith,
      fun a => by
        simp only [encBool_apply, List.length_singleton]
        omega⟩
  have hand : ComputableInSpace (fun a => f₁ a && f₂ a) enc encBool
      (fun a => (c₁ * iterExpTwo k (h (enc a).length) + c₂) +
        (c₃ * iterExpTwo k (h (enc a).length) + c₄) + 4) := by
    have hpair := hs₁.prod hs₂
    have hbool : ComputableInSpace (fun p : Bool × Bool => p.1 && p.2)
        (encPair encBool encBool) encBool fun p => (encPair encBool encBool p).length :=
      ComputableInSpace.of_finite _
    have hcomp := hbool.comp hpair
    refine hcomp.mono_le fun a => ?_
    simp only [length_encPair, encBool_apply, List.length_singleton]
    omega
  have hC : ∃ h' : ℕ → ℕ, PolynomiallyBounded h' ∧
      ∀ n, (c₁ + c₃) * iterExpTwo k (h n) + (c₂ + c₄ + 4) ≤ iterExpTwo k (h' n) := by
    obtain ⟨h', hh', hbound⟩ :=
      exists_polynomiallyBounded_poly_iterExpTwo k (c₁ + c₃ + c₂ + c₄ + 4) 1 hh
    refine ⟨h', hh', fun n => ?_⟩
    have := hbound n
    rw [pow_one] at this
    nlinarith
  obtain ⟨h', hh', hbound⟩ := hC
  exact mem_KEXPSPACE_of_computableInSpace hh' hand
    (fun a => by have := hbound (enc a).length; nlinarith)
    (fun a => by simp [hA₁ a, hB₂ a])

/-- `KEXPSPACE` is closed under union. -/
theorem union_mem_KEXPSPACE {α : Type} {enc : α ↪ List Bool} {k : ℕ} {A B : Set α}
    (hA : A ∈ KEXPSPACE enc k) (hB : B ∈ KEXPSPACE enc k) :
    A ∪ B ∈ KEXPSPACE enc k := by
  have h := compl_mem_KEXPSPACE (inter_mem_KEXPSPACE (compl_mem_KEXPSPACE hA)
    (compl_mem_KEXPSPACE hB))
  simpa only [← Set.compl_union, compl_compl] using h

/-- `KEXPSPACE` is closed under polynomial-time reductions. -/
theorem PolyTimeReducible.mem_KEXPSPACE {α β : Type} {enc : α ↪ List Bool}
    {encB : β ↪ List Bool} {k : ℕ} {A : Set α} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ KEXPSPACE encB k) :
    A ∈ KEXPSPACE enc k := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨Tg, Sg, -, hSg, hgO⟩ := hg.exists_computableInO
  have hgS := ComputableInSpace.of_inO hgO
  obtain ⟨cg, dg, hSg_le⟩ := hSg.exists_le
  obtain ⟨cl, dl, hlen_le⟩ := hg.polyBounded_length.exists_le
  obtain ⟨d, hd⟩ := mem_KEXPSPACE_iff.mp hB
  obtain ⟨c₁, c₂, t, hdec⟩ := hd
  obtain ⟨f, hf, hfB⟩ := decidableInTimeAndSpace_iff.mp hdec
  have hfS : ComputableInSpace f encB encBool fun b =>
      c₁ * iterExpTwo k ((encB b).length ^ d) + c₂ :=
    ⟨fun b => t (encB b).length, 1,
      hf.mono (fun _ => le_rfl) fun b => by dsimp only; omega,
      fun b => by simp only [encBool_apply, List.length_singleton]; omega⟩
  let hlen : ℕ → ℕ := fun n => (cl * (n + 1) ^ dl) ^ d + cg * (n + 1) ^ dg
  have hhlen : PolynomiallyBounded hlen := by dsimp only [hlen]; fun_prop
  obtain ⟨h', hh', hbound⟩ :=
    exists_polynomiallyBounded_poly_iterExpTwo k (c₁ + c₂ + 2) 1 hhlen
  refine mem_KEXPSPACE_of_computableInSpace hh' (hfS.comp hgS) (fun a => ?_) (fun a => ?_)
  · set n := (enc a).length
    have h1 : Sg a ≤ iterExpTwo k (hlen n) :=
      (hSg_le a).trans ((Nat.le_add_left _ _).trans (le_iterExpTwo k _))
    have h2 : (encB (g a)).length ^ d ≤ hlen n :=
      (Nat.pow_le_pow_left (hlen_le a) d).trans (Nat.le_add_right _ _)
    have h3 : iterExpTwo k ((encB (g a)).length ^ d) ≤ iterExpTwo k (hlen n) :=
      iterExpTwo_mono_right k h2
    have h4 := hbound n
    rw [pow_one] at h4
    nlinarith
  · exact (hAB a).trans (hfB (g a))

/-! ### Unary iterated base-2 exponential in `ComputableInSpace` -/

private theorem two_pow_step_inSpace :
    ComputableInSpace (fun m : ℕ => m + m) encUnary encUnary fun m => m + m := by
  have hid : ComputableInSpace (fun m : ℕ => m) encUnary encUnary fun m => m :=
    (ComputableInSpace.of_inO (ComputableInO.of_eq fun _ => rfl)).mono_le fun m => by
      simp [encUnary_apply]
  exact hid.append hid fun m => by
    simp only [encUnary_apply, List.replicate_add]

private theorem iterate_double_one (n : ℕ) : (fun m : ℕ => m + m)^[n] 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ]
    omega

/-- Computing `2 ^ n` in unary takes `O(2 ^ n)` work space. -/
theorem computableInSpace_two_pow_unary :
    ComputableInSpace (fun n : ℕ => 2 ^ n) encUnary encUnary fun n => 2 ^ n := by
  obtain ⟨_, Sbin, -, hSbin, hbinO⟩ := ComputableInPolyTime.unary_to_binary.exists_computableInO
  have hbin : ComputableInSpace (fun n : ℕ => n) encUnary encNat Sbin :=
    ComputableInSpace.of_inO hbinO
  obtain ⟨c, d, hSbin_le⟩ := hSbin.exists_le
  have hpoly : PolynomiallyBounded fun n => c * (n + 1) ^ d := by fun_prop
  obtain ⟨C, hC⟩ := hpoly.exists_le_mul_two_pow
  have hit := ComputableInSpace.iterate (β := ℕ) (n := fun n : ℕ => n) (init := fun _ => 1)
    (step := fun m => m + m) hbin (ComputableInSpace.constZero 1) two_pow_step_inSpace
    (Q := fun n => 2 * 2 ^ n) (B := fun n => 2 ^ n)
    (fun n j hj => by
      rw [iterate_double_one]
      have := Nat.pow_le_pow_right two_pos hj
      omega)
    (fun n j hj => by
      rw [iterate_double_one, encUnary_apply, List.length_replicate]
      exact Nat.pow_le_pow_right two_pos hj)
  have hbound : (fun n : ℕ => Sbin n + 0 + 2 * 2 ^ n + 2 ^ n + (encNat n).length) ≼
      fun n => 2 ^ n := by
    refine ⟨C + 5, fun n => ?_⟩
    have hs0 : Sbin n ≤ c * (n + 1) ^ d := by
      simpa [encUnary_apply] using hSbin_le n
    have hs : Sbin n ≤ C * 2 ^ n := hs0.trans (hC n)
    have hnlen : (encNat n).length ≤ n := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.size_le.mpr Nat.lt_two_pow_self
    have hn2 : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
    have hpos : 1 ≤ 2 ^ n := Nat.two_pow_pos n
    nlinarith
  exact (hit.weaken hbound).of_enc_eq fun n => by rw [iterate_double_one]

/-- Computing `iterExpTwo k n` in unary takes `O(iterExpTwo k n)` work space. -/
theorem computableInSpace_iterExpTwo_unary (k : ℕ) :
    ComputableInSpace (iterExpTwo k) encUnary encUnary fun n => iterExpTwo k n := by
  induction k with
  | zero =>
    exact (ComputableInSpace.of_inO (ComputableInO.of_eq fun _ => rfl)).mono_le fun n => by
      simp [encUnary_apply]
  | succ k ih =>
    have hcomp := computableInSpace_two_pow_unary.comp ih
    have hle : (fun n => iterExpTwo k n + 2 ^ iterExpTwo k n) ≼ fun n => iterExpTwo (k + 1) n := by
      refine ⟨2, fun n => ?_⟩
      simp only [iterExpTwo_succ]
      have := Nat.lt_two_pow_self (n := iterExpTwo k n)
      omega
    exact hcomp.weaken hle

/-! ### Bounded quantifier elimination in `KEXPSPACE` -/

/-- Space-bounded variant of `ComputableInO.exists_bits`. -/
theorem ComputableInSpace.exists_bits {C : Type} {encC : C ↪ List Bool}
    {test : C × List Bool → Bool} {Sf : C × List Bool → ℕ}
    (hf : ComputableInSpace test (encPair encC encBits) encBool Sf)
    {S : C × ℕ → ℕ}
    (hS : ∀ p w, w.length = p.2 → Sf (p.1, w) ≤ S p) :
    ∃ overhead : C × ℕ → ℕ,
      PolyBounded (fun p => (encPair encC encUnary p).length) overhead ∧
      ComputableInSpace (fun p => (Cslib.BitString.enumList p.2).any fun w => test (p.1, w))
        (encPair encC encUnary) encBool (fun p => overhead p + S p) := by
  obtain ⟨Tf, hfO⟩ := hf.exists_inO
  obtain ⟨overhead, ho, hsearch⟩ := hfO.exists_bits
    (T := fun p => listMax (fun w => Tf (p.1, w)) (Cslib.BitString.enumList p.2)) (S := S)
    (fun p w hw => le_listMax (f := fun w => Tf (p.1, w)) (Cslib.BitString.mem_enumList.mpr hw))
    hS
  exact ⟨overhead, ho, ComputableInSpace.of_inO hsearch⟩

/-- Existential quantification over bitstrings whose unary length is computable within
`iterExpTwo k (h (enc x).length)` work space, over a `PSPACE` verifier, stays in
`KEXPSPACE enc k`. -/
theorem setOf_exists_mem_KEXPSPACE {α : Type} {enc : α ↪ List Bool} {k : ℕ}
    {B : Set (α × List Bool)} {ℓ : α → ℕ} {h : ℕ → ℕ}
    (hh : PolynomiallyBounded h)
    (hB : B ∈ PSPACE (encPair enc encBits))
    (hℓ : ComputableInSpace ℓ enc encUnary fun x => iterExpTwo k (h (enc x).length)) :
    {x | ∃ w : List Bool, w.length = ℓ x ∧ (x, w) ∈ B} ∈ KEXPSPACE enc k := by
  obtain ⟨f, Tf, Sf, hfO, hSf, hBf⟩ := mem_PSPACE_iff_computableInO.mp hB
  obtain ⟨cf, df, hSf_le⟩ := hSf.exists_le
  let S : α × ℕ → ℕ := fun p => cf * ((encPair enc encUnary p).length + 1) ^ df
  obtain ⟨overhead, ho, hsearch⟩ :=
    ComputableInSpace.exists_bits (ComputableInSpace.of_inO hfO) (S := S)
      (fun p w hw => (hSf_le _).trans_eq <| by
        simp [S, encBits_apply, encUnary_apply, hw])
  obtain ⟨co, do_, ho_le⟩ := ho.exists_le
  have hid : ComputableInSpace (fun x : α => x) enc enc fun x => (enc x).length :=
    ComputableInSpace.of_inO (ComputableInO.of_eq fun _ => rfl)
  have hpair : ComputableInSpace (fun x => (x, ℓ x)) enc (encPair enc encUnary)
      fun x => (enc x).length + iterExpTwo k (h (enc x).length) :=
    hid.prod hℓ
  have hcomp := hsearch.comp hpair
  have hℓ_len : ∃ Cℓ, ∀ x, ℓ x ≤ Cℓ * (iterExpTwo k (h (enc x).length) + 1) := by
    obtain ⟨Cℓ, hCℓ⟩ := hℓ.length_le
    exact ⟨Cℓ, fun x => by simpa [encUnary_apply, List.length_replicate] using hCℓ x⟩
  obtain ⟨Cℓ, hCℓ⟩ := hℓ_len
  let hbase : ℕ → ℕ := fun n => h n + n
  have hhbase : PolynomiallyBounded hbase := by dsimp only [hbase]; fun_prop
  obtain ⟨h', hh', hbound⟩ := exists_polynomiallyBounded_poly_iterExpTwo k
    (co * (2 + Cℓ + 1) ^ do_ + cf * (2 + Cℓ + 1) ^ df + Cℓ + 2) (max do_ df + 1) hhbase
  refine mem_KEXPSPACE_of_computableInSpace hh' hcomp (fun x => ?_) (fun x => ?_)
  · set n := (enc x).length
    set E := iterExpTwo k (hbase n)
    have hE_ge_h : iterExpTwo k (h n) ≤ E := iterExpTwo_mono_right k (Nat.le_add_right _ _)
    have hE_ge_n : n ≤ E := (le_iterExpTwo k n).trans
      (iterExpTwo_mono_right k (Nat.le_add_left _ _))
    have hlen_pair : (encPair enc encUnary (x, ℓ x)).length + 1 ≤ (2 + Cℓ + 1) * (E + 1) := by
      rw [length_encPair, encUnary_apply, List.length_replicate]
      have := hCℓ x
      nlinarith
    have h1 : overhead (x, ℓ x) ≤ co * ((2 + Cℓ + 1) * (E + 1)) ^ do_ :=
      (ho_le (x, ℓ x)).trans (Nat.mul_le_mul_left co (Nat.pow_le_pow_left hlen_pair do_))
    have h2 : S (x, ℓ x) ≤ cf * ((2 + Cℓ + 1) * (E + 1)) ^ df :=
      Nat.mul_le_mul_left cf (Nat.pow_le_pow_left hlen_pair df)
    have hpow_o : (E + 1) ^ do_ ≤ (E + 1) ^ (max do_ df + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpow_f : (E + 1) ^ df ≤ (E + 1) ^ (max do_ df + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpow_1 : E + 1 ≤ (E + 1) ^ (max do_ df + 1) := by
      simpa using Nat.pow_le_pow_right (show 1 ≤ E + 1 by omega)
        (show 1 ≤ max do_ df + 1 by omega)
    rw [Nat.mul_pow] at h1 h2
    have hsum : n + iterExpTwo k (h n) + (overhead (x, ℓ x) + S (x, ℓ x)) ≤
        (co * (2 + Cℓ + 1) ^ do_ + cf * (2 + Cℓ + 1) ^ df + Cℓ + 2) *
          (E + 1) ^ (max do_ df + 1) := by
      have hno : co * (2 + Cℓ + 1) ^ do_ * (E + 1) ^ do_ ≤
          co * (2 + Cℓ + 1) ^ do_ * (E + 1) ^ (max do_ df + 1) :=
        Nat.mul_le_mul_left _ hpow_o
      have hnf : cf * (2 + Cℓ + 1) ^ df * (E + 1) ^ df ≤
          cf * (2 + Cℓ + 1) ^ df * (E + 1) ^ (max do_ df + 1) :=
        Nat.mul_le_mul_left _ hpow_f
      nlinarith
    exact hsum.trans (hbound n)
  · simp [BitString.mem_enumList, ← hBf]

/-- Universal quantification over bitstrings whose unary length is computable within
`iterExpTwo k (h (enc x).length)` work space, over a `PSPACE` verifier, stays in
`KEXPSPACE enc k`. -/
theorem setOf_forall_mem_KEXPSPACE {α : Type} {enc : α ↪ List Bool} {k : ℕ}
    {B : Set (α × List Bool)} {ℓ : α → ℕ} {h : ℕ → ℕ}
    (hh : PolynomiallyBounded h)
    (hB : B ∈ PSPACE (encPair enc encBits))
    (hℓ : ComputableInSpace ℓ enc encUnary fun x => iterExpTwo k (h (enc x).length)) :
    {x | ∀ w : List Bool, w.length = ℓ x → (x, w) ∈ B} ∈ KEXPSPACE enc k := by
  have hcompl := compl_mem_KEXPSPACE (setOf_exists_mem_KEXPSPACE hh (compl_mem_PSPACE hB) hℓ)
  convert hcompl using 1
  ext x
  simp

/-- Alternating `∃ s ∀ π` quantification over bitstrings of `KEXPSPACE k`-computable unary
lengths, over a `PSPACE` verifier, stays in `KEXPSPACE enc k`. -/
theorem setOf_exists_forall_mem_KEXPSPACE {α : Type} {enc : α ↪ List Bool} {k : ℕ}
    {B : Set ((α × List Bool) × List Bool)} {ℓ₁ ℓ₂ : α → ℕ} {h₁ h₂ : ℕ → ℕ}
    (hh₁ : PolynomiallyBounded h₁) (hh₂ : PolynomiallyBounded h₂)
    (hB : B ∈ PSPACE (encPair (encPair enc encBits) encBits))
    (hℓ₁ : ComputableInSpace ℓ₁ enc encUnary fun x => iterExpTwo k (h₁ (enc x).length))
    (hℓ₂ : ComputableInSpace ℓ₂ enc encUnary fun x => iterExpTwo k (h₂ (enc x).length)) :
    {x | ∃ s : List Bool, s.length = ℓ₁ x ∧
      ∀ π : List Bool, π.length = ℓ₂ x → ((x, s), π) ∈ B} ∈ KEXPSPACE enc k := by
  obtain ⟨f, Tf, Sf, hfO, hSf, hBf⟩ := mem_PSPACE_iff_computableInO.mp (compl_mem_PSPACE hB)
  obtain ⟨cf, df, hSf_le⟩ := hSf.exists_le
  let S_in : (α × List Bool) × ℕ → ℕ :=
    fun p => cf * ((encPair (encPair enc encBits) encUnary p).length + 1) ^ df
  obtain ⟨ov_in, hov_in, hsearch_in⟩ :=
    ComputableInSpace.exists_bits (ComputableInSpace.of_inO hfO) (S := S_in)
      (fun p w hw => (hSf_le _).trans_eq <| by
        simp [S_in, encBits_apply, encUnary_apply, hw])
  obtain ⟨co_in, do_in, hov_in_le⟩ := hov_in.exists_le
  -- Negate the inner existential to get `∀ π`
  have hnot_in : ComputableInSpace
      (fun p : (α × List Bool) × ℕ =>
        !((Cslib.BitString.enumList p.2).any fun π => f (p.1, π)))
      (encPair (encPair enc encBits) encUnary) encBool
      (fun p => ov_in p + S_in p + 1) := by
    have hneg : ComputableInSpace Bool.not encBool encBool fun b => (encBool b).length :=
      ComputableInSpace.of_finite _
    refine (hneg.comp hsearch_in).mono_le fun p => ?_
    simp only [encBool_apply, List.length_singleton]
    omega
  -- Compose with `(x, s) ↦ ((x, s), ℓ₂ x)`
  have hid_xs : ComputableInSpace (fun p : α × List Bool => p)
      (encPair enc encBits) (encPair enc encBits)
      fun p => (encPair enc encBits p).length :=
    ComputableInSpace.of_inO (ComputableInO.of_eq fun _ => rfl)
  have hℓ₂_xs : ComputableInSpace (fun p : α × List Bool => ℓ₂ p.1)
      (encPair enc encBits) encUnary
      fun p => (encPair enc encBits p).length + iterExpTwo k (h₂ (enc p.1).length) := by
    have hcomp := hℓ₂.comp (ComputableInSpace.fst enc encBits)
    exact hcomp.mono_le fun _ => le_rfl
  have hmid_pair := hid_xs.prod hℓ₂_xs
  have hmid := hnot_in.comp hmid_pair
  -- Now run outer `exists_bits` over `s` of length `ℓ₁ x`
  obtain ⟨Cℓ₁, hCℓ₁⟩ : ∃ Cℓ₁, ∀ x, ℓ₁ x ≤ Cℓ₁ * (iterExpTwo k (h₁ (enc x).length) + 1) := by
    obtain ⟨Cℓ₁, hCℓ₁⟩ := hℓ₁.length_le
    exact ⟨Cℓ₁, fun x => by simpa [encUnary_apply, List.length_replicate] using hCℓ₁ x⟩
  obtain ⟨Cℓ₂, hCℓ₂⟩ : ∃ Cℓ₂, ∀ x, ℓ₂ x ≤ Cℓ₂ * (iterExpTwo k (h₂ (enc x).length) + 1) := by
    obtain ⟨Cℓ₂, hCℓ₂⟩ := hℓ₂.length_le
    exact ⟨Cℓ₂, fun x => by simpa [encUnary_apply, List.length_replicate] using hCℓ₂ x⟩
  let hbase : ℕ → ℕ := fun n => h₁ n + h₂ n + n
  have hhbase : PolynomiallyBounded hbase := by dsimp only [hbase]; fun_prop
  let K : ℕ := 2 * (2 + Cℓ₁ + 1) + 1 + Cℓ₂ + 1
  let Smid_bound : α × ℕ → ℕ := fun p =>
    2 * (2 * (enc p.1).length + 1 + p.2) + iterExpTwo k (h₂ (enc p.1).length) +
      (co_in * (K * (iterExpTwo k (hbase (enc p.1).length) + p.2 + 1)) ^ do_in +
        cf * (K * (iterExpTwo k (hbase (enc p.1).length) + p.2 + 1)) ^ df + 1)
  obtain ⟨ov_out, hov_out, hsearch_out⟩ := ComputableInSpace.exists_bits hmid (S := Smid_bound)
      (fun p s hs => by
    set n := (enc p.1).length
    set E := iterExpTwo k (hbase n)
    have hE_ge_h₂ : iterExpTwo k (h₂ n) ≤ E :=
      iterExpTwo_mono_right k (by dsimp only [hbase]; omega)
    have hE_ge_n : n ≤ E := (le_iterExpTwo k n).trans
      (iterExpTwo_mono_right k (by dsimp only [hbase]; omega))
    have hlen_xs : (encPair enc encBits (p.1, s)).length = 2 * n + 1 + p.2 := by
      rw [length_encPair, encBits_apply, hs]
    have hlen_in : (encPair (encPair enc encBits) encUnary ((p.1, s), ℓ₂ p.1)).length + 1 ≤
        K * (E + p.2 + 1) := by
      rw [length_encPair, hlen_xs, encUnary_apply, List.length_replicate]
      have := hCℓ₂ p.1
      dsimp only [K]
      nlinarith
    have h1 : ov_in ((p.1, s), ℓ₂ p.1) ≤ co_in * (K * (E + p.2 + 1)) ^ do_in :=
      (hov_in_le _).trans (Nat.mul_le_mul_left co_in (Nat.pow_le_pow_left hlen_in do_in))
    have h2 : S_in ((p.1, s), ℓ₂ p.1) ≤ cf * (K * (E + p.2 + 1)) ^ df :=
      Nat.mul_le_mul_left cf (Nat.pow_le_pow_left hlen_in df)
    dsimp only [Smid_bound]
    rw [hlen_xs]
    dsimp only [E, n] at *
    omega)
  obtain ⟨co_out, do_out, hov_out_le⟩ := hov_out.exists_le
  have hid_x : ComputableInSpace (fun x : α => x) enc enc fun x => (enc x).length :=
    ComputableInSpace.of_inO (ComputableInO.of_eq fun _ => rfl)
  have houter := hsearch_out.comp (hid_x.prod hℓ₁)
  let M : ℕ := K * (1 + Cℓ₁ + 1)
  let D : ℕ := max do_out (max do_in df) + 1
  let Ctot : ℕ := co_out * (2 + Cℓ₁ + 1) ^ do_out + co_in * M ^ do_in + cf * M ^ df +
      6 * Cℓ₁ + 16
  obtain ⟨h', hh', hbound⟩ := exists_polynomiallyBounded_poly_iterExpTwo k Ctot D hhbase
  refine mem_KEXPSPACE_of_computableInSpace hh' houter (fun x => ?_) (fun x => ?_)
  · set n := (enc x).length
    set E := iterExpTwo k (hbase n)
    have hE_ge_h₁ : iterExpTwo k (h₁ n) ≤ E :=
      iterExpTwo_mono_right k (by dsimp only [hbase]; omega)
    have hE_ge_h₂ : iterExpTwo k (h₂ n) ≤ E :=
      iterExpTwo_mono_right k (by dsimp only [hbase]; omega)
    have hE_ge_n : n ≤ E := (le_iterExpTwo k n).trans
      (iterExpTwo_mono_right k (by dsimp only [hbase]; omega))
    have hℓ₁_le : ℓ₁ x ≤ Cℓ₁ * (E + 1) :=
      (hCℓ₁ x).trans (Nat.mul_le_mul_left Cℓ₁ (Nat.add_le_add_right hE_ge_h₁ 1))
    have hlen_p : (encPair enc encUnary (x, ℓ₁ x)).length + 1 ≤ (2 + Cℓ₁ + 1) * (E + 1) := by
      rw [length_encPair, encUnary_apply, List.length_replicate]
      nlinarith
    have hEℓ₁ : E + ℓ₁ x + 1 ≤ (1 + Cℓ₁ + 1) * (E + 1) := by nlinarith
    have hKE : K * (E + ℓ₁ x + 1) ≤ M * (E + 1) := by
      dsimp only [M]
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left K hEℓ₁
    have hov : ov_out (x, ℓ₁ x) ≤ co_out * (2 + Cℓ₁ + 1) ^ do_out * (E + 1) ^ D := by
      calc ov_out (x, ℓ₁ x) ≤ co_out * ((2 + Cℓ₁ + 1) * (E + 1)) ^ do_out :=
            (hov_out_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen_p _))
        _ = co_out * (2 + Cℓ₁ + 1) ^ do_out * (E + 1) ^ do_out := by rw [Nat.mul_pow, Nat.mul_assoc]
        _ ≤ co_out * (2 + Cℓ₁ + 1) ^ do_out * (E + 1) ^ D :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by dsimp only [D]; omega))
    have hin1 : co_in * (K * (E + ℓ₁ x + 1)) ^ do_in ≤ co_in * M ^ do_in * (E + 1) ^ D := by
      calc co_in * (K * (E + ℓ₁ x + 1)) ^ do_in ≤ co_in * (M * (E + 1)) ^ do_in :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hKE _)
        _ = co_in * M ^ do_in * (E + 1) ^ do_in := by rw [Nat.mul_pow, Nat.mul_assoc]
        _ ≤ co_in * M ^ do_in * (E + 1) ^ D :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by dsimp only [D]; omega))
    have hin2 : cf * (K * (E + ℓ₁ x + 1)) ^ df ≤ cf * M ^ df * (E + 1) ^ D := by
      calc cf * (K * (E + ℓ₁ x + 1)) ^ df ≤ cf * (M * (E + 1)) ^ df :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hKE _)
        _ = cf * M ^ df * (E + 1) ^ df := by rw [Nat.mul_pow, Nat.mul_assoc]
        _ ≤ cf * M ^ df * (E + 1) ^ D :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by dsimp only [D]; omega))
    have hpow_1 : E + 1 ≤ (E + 1) ^ D := by
      simpa using
        Nat.pow_le_pow_right (show 1 ≤ E + 1 by omega) (show 1 ≤ D by dsimp only [D]; omega)
    have hrest : n + iterExpTwo k (h₁ n) + (2 * (2 * n + 1 + ℓ₁ x) + iterExpTwo k (h₂ n) + 1) ≤
        (6 * Cℓ₁ + 16) * (E + 1) ^ D := by
      nlinarith
    have htot : n + iterExpTwo k (h₁ n) + (ov_out (x, ℓ₁ x) + Smid_bound (x, ℓ₁ x)) ≤
        Ctot * (E + 1) ^ D := by
      dsimp only [Smid_bound, Ctot]
      nlinarith
    exact htot.trans (hbound n)
  · simp only [Set.mem_ofPred_eq, List.any_eq_true, BitString.mem_enumList,
      Bool.not_eq_true', List.any_eq_false]
    constructor
    · rintro ⟨s, hs, hpi⟩
      refine ⟨s, hs, fun π hπ => ?_⟩
      have hmem := hpi π hπ
      have hnot : ((x, s), π) ∉ Bᶜ := fun h => h hmem
      rw [hBf] at hnot
      cases hf : f ((x, s), π) <;> simp_all
    · rintro ⟨s, hs, hpi⟩
      refine ⟨s, hs, fun π hπ => ?_⟩
      have hfalse := hpi π hπ
      have hnotmem : ((x, s), π) ∉ Bᶜ := by
        rw [hBf]; simp [hfalse]
      exact not_not.mp hnotmem

/-- Computing `x ↦ iterExpTwo k (m x)` in unary from a polynomial-time unary-valued `m` takes
`O(iterExpTwo k (h (enc x).length))` work space for a polynomially bounded `h`. -/
theorem computableInSpace_iterExpTwo_of_polyTime {α : Type} {enc : α ↪ List Bool} (k : ℕ)
    {m : α → ℕ} (hm : ComputableInPolyTime m enc encUnary) :
    ∃ h : ℕ → ℕ, PolynomiallyBounded h ∧
      ComputableInSpace (fun x => iterExpTwo k (m x)) enc encUnary
        fun x => iterExpTwo k (h (enc x).length) := by
  obtain ⟨_, Sm, -, hSm, hmO⟩ := hm.exists_computableInO
  have hmS := ComputableInSpace.of_inO hmO
  obtain ⟨cm, dm, hSm_le⟩ := hSm.exists_le
  obtain ⟨cl, dl, hlen_le⟩ := hm.polyBounded_length.exists_le
  let hm_bound : ℕ → ℕ := fun n => cl * (n + 1) ^ dl
  have hhm : PolynomiallyBounded hm_bound := by dsimp only [hm_bound]; fun_prop
  have hm_le : ∀ x, m x ≤ hm_bound (enc x).length := fun x => by
    simpa [encUnary_apply, List.length_replicate] using hlen_le x
  have hcomp := (computableInSpace_iterExpTwo_unary k).comp hmS
  let hbase : ℕ → ℕ := fun n => hm_bound n + cm * (n + 1) ^ dm
  have hhbase : PolynomiallyBounded hbase := by dsimp only [hbase, hm_bound]; fun_prop
  obtain ⟨h', hh', hbound⟩ := exists_polynomiallyBounded_poly_iterExpTwo k 2 1 hhbase
  refine ⟨h', hh', hcomp.mono_le fun x => ?_⟩
  set n := (enc x).length
  have h1 : Sm x ≤ iterExpTwo k (hbase n) :=
    (hSm_le x).trans ((Nat.le_add_left _ _).trans (le_iterExpTwo k _))
  have h2 : iterExpTwo k (m x) ≤ iterExpTwo k (hbase n) :=
    iterExpTwo_mono_right k ((hm_le x).trans (Nat.le_add_right _ _))
  have h3 := hbound n
  rw [pow_one] at h3
  omega

/-- Convenience corollary of `setOf_exists_forall_mem_KEXPSPACE` when the witness lengths are
`iterExpTwo k (m₁ x)` and `iterExpTwo k (m₂ x)` for polynomial-time unary-computable `m₁, m₂`. -/
theorem setOf_exists_forall_mem_KEXPSPACE_iterExpTwo {α : Type} {enc : α ↪ List Bool} {k : ℕ}
    {B : Set ((α × List Bool) × List Bool)} {m₁ m₂ : α → ℕ}
    (hm₁ : ComputableInPolyTime m₁ enc encUnary)
    (hm₂ : ComputableInPolyTime m₂ enc encUnary)
    (hB : B ∈ PSPACE (encPair (encPair enc encBits) encBits)) :
    {x | ∃ s : List Bool, s.length = iterExpTwo k (m₁ x) ∧
      ∀ π : List Bool, π.length = iterExpTwo k (m₂ x) → ((x, s), π) ∈ B} ∈ KEXPSPACE enc k := by
  obtain ⟨h₁, hh₁, hℓ₁⟩ := computableInSpace_iterExpTwo_of_polyTime k hm₁
  obtain ⟨h₂, hh₂, hℓ₂⟩ := computableInSpace_iterExpTwo_of_polyTime k hm₂
  exact setOf_exists_forall_mem_KEXPSPACE hh₁ hh₂ hB hℓ₁ hℓ₂

/-! ### Private non-vacuity and sharpness witnesses -/

section Examples

private example (k : ℕ) : (∅ : Set ℕ) ∈ KEXPSPACE encNat k :=
  PSPACE_subset_KEXPSPACE k (P_subset_PSPACE empty_mem_P)

private example (k : ℕ) : (Set.univ : Set ℕ) ∈ KEXPSPACE encNat k := by
  simpa using compl_mem_KEXPSPACE (PSPACE_subset_KEXPSPACE k (P_subset_PSPACE empty_mem_P))

private example (k : ℕ) :
    {e : ℕ | ((Denumerable.ofNat Nat.Partrec.Code e).eval 0).Dom} ∉ KEXPSPACE encNat k := by
  intro hmem
  obtain ⟨d, c₁, c₂, t, hdec⟩ := mem_KEXPSPACE_iff.mp hmem
  obtain ⟨f, hf, hiff⟩ := decidableInTimeAndSpace_iff.mp hdec
  have henc : Computable encNat :=
    ComputableInPolyTime.unary_to_binary.isComputable.computable_enc computable_encUnary
  have hf_comp : Computable f := hf.isComputable.computable_bool henc
  have hpred : ComputablePred fun c : Nat.Partrec.Code => (c.eval 0).Dom :=
    ComputablePred.computable_iff.mpr
      ⟨fun c => f (Encodable.encode c), hf_comp.comp Computable.encode, funext fun c =>
        propext (by
          simpa [Set.mem_ofPred_eq, Denumerable.ofNat_encode] using
            hiff (Encodable.encode c))⟩
  exact ComputablePred.halting_problem 0 hpred

end Examples

end Cslib.Complexity
