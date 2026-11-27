/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Log

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.PolyTime.Int.ExactDiv
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-Time Modular Linear Congruence Solvers over Binary Integers

Deterministic multi-tape Turing machine polynomial-time (`Turing.MultiTapeTM.ComputableInPolyTime`)
solvers and `Cslib.Complexity.P` decision certificates for linear congruences over binary-encoded
integers (`Turing.MultiTapeTM.encIntBin`) and moduli (`Turing.MultiTapeTM.encNat`), built on the
binary extended-Euclidean modular inverse `BinaryGcd.modInv` without introducing custom Turing
machines or axioms beyond standard Lean axioms:

* single-variable congruences `a * x ≡ b [MOD n]` (`solveModLinearNat`) and
  `a * x ≡ b [ZMOD (n : ℤ)]` (`solveModLinear`), total across all `n : ℕ` (including `n = 0`),
  returning a canonical representative `0 ≤ x < n` when `0 < n`;
* two-variable congruences `a₁ * x₁ + a₂ * x₂ ≡ b [ZMOD (n : ℤ)]` (`solveModLinear2`) for arbitrary
  composite moduli `n > 0`;
* `k`-variable linear congruences `∑ i, c_i * x_i ≡ b [ZMOD (p : ℤ)]` (`solveModLinearListPrime`)
  over a prime modulus `p`.

## Main definitions

* `CslibFrontier.solveModLinearNat`: extended-Euclidean solver for `a * x ≡ b [MOD n]`.
* `CslibFrontier.solveModLinear`: extended-Euclidean solver for `a * x ≡ b [ZMOD (n : ℤ)]`.
* `CslibFrontier.solveModLinear2`: solver for `a₁ * x₁ + a₂ * x₂ ≡ b [ZMOD (n : ℤ)]`.
* `CslibFrontier.solveModLinearListPrime`: solver for `listDot coeffs xs ≡ b [ZMOD (p : ℤ)]` modulo
  a prime `p`.

## Main results

* `CslibFrontier.modLinear_solvable_iff`: `(∃ x : ℤ, a * x ≡ b [ZMOD n]) ↔ (Int.gcd a n : ℤ) ∣ b`.
* `CslibFrontier.solveModLinear_stepCount_le`: the underlying Euclidean loop executes at most
  `2 * Nat.log 2 n + 3` steps for `0 < n`.
* `CslibFrontier.solveModLinear_sound`, `CslibFrontier.isSome_solveModLinear_iff`: soundness,
  canonical range `0 ≤ x < n`, and completeness of `solveModLinear`.
* `CslibFrontier.computableInPolyTime_solveModLinear`,
  `CslibFrontier.computableInPolyTime_solveModLinear2`,
  `CslibFrontier.computableInPolyTime_solveModLinearListPrime`: multi-tape polynomial-time
  certificates.
* `CslibFrontier.modLinearSolvableSet_mem_P`: membership of modular linear congruence solvability in
  `Cslib.Complexity.P`.
-/

public section

namespace CslibFrontier

open Turing.MultiTapeTM

/-- Binary encoding of a modular linear equation instance `(a, b, n) : ℤ × ℤ × ℕ`. -/
abbrev encModLinearInput : ℤ × ℤ × ℕ ↪ List Bool :=
  encPair encIntBin (encPair encIntBin encNat)

/-- Binary encoding of a natural-number triple `(a, b, n) : ℕ × ℕ × ℕ`. -/
abbrev encNatTriple : ℕ × ℕ × ℕ ↪ List Bool :=
  encPair encNat (encPair encNat encNat)

/-- Binary encoding of a two-variable modular linear equation `(a₁, a₂, b, n)`. -/
abbrev encModLinear2Input : ℤ × ℤ × ℤ × ℕ ↪ List Bool :=
  encPair encIntBin (encPair encIntBin (encPair encIntBin encNat))

/-- Binary encoding of a multi-variable modular linear equation `(coeffs, b, p)`. -/
abbrev encModLinearListInput : List ℤ × ℤ × ℕ ↪ List Bool :=
  encPair (encList encIntBin) (encPair encIntBin encNat)

/-- Algebraic solvability criterion for a single-variable modular linear congruence:
`a * x ≡ b [ZMOD n]` has a solution `x : ℤ` if and only if `(Int.gcd a n : ℤ) ∣ b`. -/
theorem modLinear_solvable_iff (a b n : ℤ) :
    (∃ x : ℤ, a * x ≡ b [ZMOD n]) ↔ (Int.gcd a n : ℤ) ∣ b := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun ⟨q, hq⟩ ↦ ?_⟩
  · rw [Int.modEq_iff_dvd] at hx
    rcases hx with ⟨y, hy⟩
    have ha : (Int.gcd a n : ℤ) ∣ a := Int.gcd_dvd_left a n
    have hn : (Int.gcd a n : ℤ) ∣ n := Int.gcd_dvd_right a n
    have hb : b = a * x + n * y := by linarith
    rw [hb]
    exact dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hn y)
  · refine ⟨Int.gcdA a n * q, ?_⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨Int.gcdB a n * q, ?_⟩
    have hbez := Int.gcd_eq_gcd_ab a n
    calc
      b - a * (Int.gcdA a n * q) = (Int.gcd a n : ℤ) * q - a * Int.gcdA a n * q := by
        rw [hq]; ring
      _ = (a * Int.gcdA a n + n * Int.gcdB a n) * q - a * Int.gcdA a n * q := by rw [hbez]
      _ = n * (Int.gcdB a n * q) := by ring

/-- Extended-Euclidean solver for `a * x ≡ b [MOD n]` on natural numbers, reducing `a` and `b`
modulo `n` first so the Euclidean loop runs in `O(log n)` steps. -/
def solveModLinearNat (a b n : ℕ) : Option ℕ :=
  if n = 0 then
    if a = 0 then (if b = 0 then some 0 else none)
    else if b % a = 0 then some (b / a) else none
  else
    let a₀ := a % n
    let b₀ := b % n
    let g := Nat.gcd n a₀
    if b₀ % g = 0 then
      some ((BinaryGcd.modInv a₀ n * (b₀ / g)) % n)
    else
      none

/-- When `0 < n` and `solveModLinearNat a b n = some x`, we have `x < n` and
`a * x ≡ b [MOD n]`. -/
theorem solveModLinearNat_sound {a b n x : ℕ} (hn : 0 < n)
    (h : solveModLinearNat a b n = some x) :
    x < n ∧ a * x ≡ b [MOD n] := by
  have hne : n ≠ 0 := Nat.ne_of_gt hn
  simp only [solveModLinearNat, hne, ↓reduceIte] at h
  set a₀ := a % n
  set b₀ := b % n
  set g := Nat.gcd n a₀
  split_ifs at h with hmod
  have hx : x = (BinaryGcd.modInv a₀ n * (b₀ / g)) % n := (Option.some.inj h).symm
  refine ⟨hx ▸ Nat.mod_lt _ hn, ?_⟩
  have hdvd : g ∣ b₀ := Nat.dvd_of_mod_eq_zero hmod
  have hinv : a₀ * BinaryGcd.modInv a₀ n ≡ g [MOD n] := BinaryGcd.mul_modInv_modEq_gcd a₀ hn
  have h1 : a * x ≡ a₀ * (BinaryGcd.modInv a₀ n * (b₀ / g)) [MOD n] := by
    rw [hx]
    exact (Nat.mod_modEq a n).symm.mul (Nat.mod_modEq _ n)
  have h2 : a₀ * (BinaryGcd.modInv a₀ n * (b₀ / g)) ≡ b₀ [MOD n] := by
    rw [← mul_assoc]
    have hm := hinv.mul_right (b₀ / g)
    rwa [Nat.mul_div_cancel' hdvd] at hm
  exact (h1.trans h2).trans (Nat.mod_modEq b n)

/-- For `0 < n`, `solveModLinearNat a b n` succeeds iff `Nat.gcd a n ∣ b`. -/
theorem isSome_solveModLinearNat_iff {a b n : ℕ} (hn : 0 < n) :
    (solveModLinearNat a b n).isSome ↔ Nat.gcd a n ∣ b := by
  have hne : n ≠ 0 := Nat.ne_of_gt hn
  simp only [solveModLinearNat, hne, ↓reduceIte]
  have hgcd : Nat.gcd n (a % n) = Nat.gcd a n := by
    rw [Nat.gcd_comm n (a % n), ← Nat.gcd_rec n a, Nat.gcd_comm]
  have hdvd_iff : Nat.gcd a n ∣ b % n ↔ Nat.gcd a n ∣ b :=
    Nat.dvd_mod_iff (Nat.gcd_dvd_right a n)
  split_ifs with hmod
  · simp only [Option.isSome_some, true_iff]
    rw [hgcd] at hmod
    exact hdvd_iff.mp (Nat.dvd_of_mod_eq_zero hmod)
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rw [hgcd] at hmod
    exact fun hdvd ↦ hmod (Nat.mod_eq_zero_of_dvd (hdvd_iff.mpr hdvd))

/-- Logarithmic step bound: for every `n ≥ 1`, the Euclidean loop solving `a * x ≡ b [MOD n]`
terminates in at most `2 * Nat.log 2 n + 3` steps. -/
theorem solveModLinear_stepCount_le (a : ℕ) {n : ℕ} (hn : 0 < n) :
    BinaryGcd.gcdCount (n, a % n) ≤ 2 * Nat.log 2 n + 3 := by
  have hsize_n : n.size ≤ Nat.log 2 n + 1 :=
    Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide) n)
  have hsize_a : (a % n).size ≤ n.size := Nat.size_le_size (Nat.mod_lt a hn).le
  have hb_n : n.bits.length = n.size := Nat.size_eq_bits_len n
  have hb_a : (a % n).bits.length = (a % n).size := Nat.size_eq_bits_len (a % n)
  change n.bits.length + (a % n).bits.length + 1 ≤ 2 * Nat.log 2 n + 3
  omega

/-- Convert a binary integer `z : ℤ` to its canonical natural residue `(z.emod n).natAbs`. -/
def intModToNat (z : ℤ) (n : ℕ) : ℕ :=
  (z.emod (n : ℤ)).natAbs

/-- When `0 < n`, `intModToNat z n < n` and `(intModToNat z n : ℤ) ≡ z [ZMOD (n : ℤ)]`. -/
theorem intModToNat_spec (z : ℤ) {n : ℕ} (hn : 0 < n) :
    intModToNat z n < n ∧ ((intModToNat z n : ℕ) : ℤ) ≡ z [ZMOD (n : ℤ)] := by
  have hnZ : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.mpr hn
  have hnn : 0 ≤ z.emod (n : ℤ) := Int.emod_nonneg z (ne_of_gt hnZ)
  have hlt : z.emod (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos z hnZ
  have hcast : ((intModToNat z n : ℕ) : ℤ) = z.emod (n : ℤ) := Int.natAbs_of_nonneg hnn
  exact ⟨Int.lt_of_ofNat_lt_ofNat (hcast.symm ▸ hlt), hcast ▸ Int.mod_modEq z (n : ℤ)⟩

/-- Extended-Euclidean solver for `a * x ≡ b [ZMOD (n : ℤ)]` returning a canonical representative
`0 ≤ x < n` whenever `0 < n` and a solution exists. -/
def solveModLinear (a b : ℤ) (n : ℕ) : Option ℤ :=
  if n = 0 then
    if a = 0 then (if b = 0 then some 0 else none)
    else if b.emod a = 0 then some (b.ediv a) else none
  else
    (solveModLinearNat (intModToNat a n) (intModToNat b n) n).map Nat.cast

/-- Soundness of `solveModLinear`: any returned `x` satisfies `a * x ≡ b [ZMOD (n : ℤ)]`, with
`0 ≤ x < n` whenever `0 < n`. -/
theorem solveModLinear_sound {a b : ℤ} {n : ℕ} {x : ℤ}
    (h : solveModLinear a b n = some x) :
    a * x ≡ b [ZMOD (n : ℤ)] ∧ (0 < n → 0 ≤ x ∧ x < (n : ℤ)) := by
  by_cases hn : n = 0
  · subst hn
    simp only [solveModLinear, ↓reduceIte, Nat.cast_zero, Int.modEq_zero_iff] at h ⊢
    refine ⟨?_, fun hlt ↦ (Nat.lt_irrefl 0 hlt).elim⟩
    by_cases ha : a = 0
    · simp only [ha, ↓reduceIte, zero_mul] at h ⊢
      split_ifs at h with hb
      exact hb.symm
    · simp only [ha, ↓reduceIte] at h
      split_ifs at h with hmod
      have hx : x = b.ediv a := (Option.some.inj h).symm
      rw [hx]
      have hdiv : b % a + a * (b / a) = b := Int.emod_add_mul_ediv b a
      have hmod' : b % a = 0 := hmod
      rw [hmod', zero_add] at hdiv
      exact hdiv
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    simp only [solveModLinear, hn, ↓reduceIte, Option.map_eq_some_iff] at h
    rcases h with ⟨k, hk, rfl⟩
    obtain ⟨hklt, hkmod⟩ := solveModLinearNat_sound hpos hk
    obtain ⟨_, ha_mod⟩ := intModToNat_spec a hpos
    obtain ⟨_, hb_mod⟩ := intModToNat_spec b hpos
    have hkZ : (intModToNat a n : ℤ) * (k : ℤ) ≡ (intModToNat b n : ℤ) [ZMOD (n : ℤ)] := by
      exact_mod_cast hkmod
    exact ⟨((ha_mod.symm.mul_right (k : ℤ)).trans hkZ).trans hb_mod,
      fun _ ↦ ⟨Int.natCast_nonneg k, Int.ofNat_lt.mpr hklt⟩⟩

/-- Completeness of `solveModLinear`: returns `some x` iff `(Int.gcd a (n : ℤ) : ℤ) ∣ b`. -/
theorem isSome_solveModLinear_iff (a b : ℤ) (n : ℕ) :
    (solveModLinear a b n).isSome ↔ (Int.gcd a (n : ℤ) : ℤ) ∣ b := by
  rw [← modLinear_solvable_iff]
  refine ⟨fun hs ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨x, (solveModLinear_sound hx).1⟩
  · by_cases hn : n = 0
    · subst hn
      simp only [Nat.cast_zero, Int.modEq_zero_iff] at hx
      simp only [solveModLinear, ↓reduceIte]
      by_cases ha : a = 0
      · subst ha
        simp [← hx]
      · have hmod : b.emod a = 0 := Int.emod_eq_zero_of_dvd ⟨x, hx.symm⟩
        simp [ha, hmod]
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      simp only [solveModLinear, hn, ↓reduceIte, Option.isSome_map,
        isSome_solveModLinearNat_iff hpos]
      obtain ⟨_, ha_mod⟩ := intModToNat_spec a hpos
      obtain ⟨_, hb_mod⟩ := intModToNat_spec b hpos
      have hsol : (intModToNat a n : ℤ) * x ≡ (intModToNat b n : ℤ) [ZMOD (n : ℤ)] :=
        ((ha_mod.mul_right x).trans hx).trans hb_mod.symm
      exact Int.ofNat_dvd.mp ((modLinear_solvable_iff _ _ _).mp ⟨x, hsol⟩)

/-- Solver for a two-variable modular linear congruence `a₁ * x₁ + a₂ * x₂ ≡ b [ZMOD (n : ℤ)]`
(`0 < n`) via two calls to `solveModLinear`. -/
def solveModLinear2 (a₁ a₂ b : ℤ) (n : ℕ) : Option (ℤ × ℤ) :=
  let g := Nat.gcd (intModToNat a₁ n) n
  match solveModLinear a₂ b g with
  | none => none
  | some x₂ =>
    match solveModLinear a₁ (b - a₂ * x₂) n with
    | none => none
    | some x₁ => some (x₁, x₂)

/-- Soundness of `solveModLinear2`. -/
theorem solveModLinear2_sound {a₁ a₂ b : ℤ} {n : ℕ} {p : ℤ × ℤ}
    (h : solveModLinear2 a₁ a₂ b n = some p) :
    a₁ * p.1 + a₂ * p.2 ≡ b [ZMOD (n : ℤ)] ∧
      (0 < n → 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2 ∧ p.2 < (n : ℤ)) := by
  dsimp only [solveModLinear2] at h
  set g := Nat.gcd (intModToNat a₁ n) n
  cases hx₂ : solveModLinear a₂ b g with
  | none => simp [hx₂] at h
  | some x₂ =>
    simp only [hx₂] at h
    cases hx₁ : solveModLinear a₁ (b - a₂ * x₂) n with
    | none => simp [hx₁] at h
    | some x₁ =>
      simp only [hx₁, Option.some.injEq] at h
      subst h
      obtain ⟨hm₁, hr₁⟩ := solveModLinear_sound hx₁
      obtain ⟨_, hr₂⟩ := solveModLinear_sound hx₂
      refine ⟨by simpa using hm₁.add_right (a₂ * x₂), fun hn ↦ ?_⟩
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right _ hn
      have hg_le : (g : ℤ) ≤ (n : ℤ) := Int.ofNat_le.mpr (Nat.le_of_dvd hn (Nat.gcd_dvd_right _ _))
      exact ⟨(hr₁ hn).1, (hr₁ hn).2, (hr₂ hg_pos).1, (hr₂ hg_pos).2.trans_le hg_le⟩

/-- Completeness of `solveModLinear2` for `0 < n`. -/
theorem isSome_solveModLinear2_iff (a₁ a₂ b : ℤ) {n : ℕ} (hn : 0 < n) :
    (solveModLinear2 a₁ a₂ b n).isSome ↔
      ∃ x₁ x₂ : ℤ, a₁ * x₁ + a₂ * x₂ ≡ b [ZMOD (n : ℤ)] := by
  refine ⟨fun hs ↦ ?_, fun ⟨x₁, x₂, hmod⟩ ↦ ?_⟩
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨p.1, p.2, (solveModLinear2_sound hp).1⟩
  · set g := Nat.gcd (intModToNat a₁ n) n
    have hg_eq : (g : ℤ) = (Int.gcd a₁ (n : ℤ) : ℤ) := by
      obtain ⟨_, ha⟩ := intModToNat_spec a₁ hn
      rw [Int.modEq_iff_dvd] at ha
      rcases ha with ⟨q, hq⟩
      have ha₁ : a₁ = (intModToNat a₁ n : ℤ) + (n : ℤ) * q := by linarith
      apply Int.dvd_antisymm (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      · refine Int.dvd_coe_gcd ?_ (Int.ofNat_dvd.mpr (Nat.gcd_dvd_right _ _))
        rw [ha₁]
        exact dvd_add (Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _))
          (dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr (Nat.gcd_dvd_right _ _)) q)
      · refine Int.ofNat_dvd.mpr (Nat.dvd_gcd ?_ (Int.ofNat_dvd.mp (Int.gcd_dvd_right a₁ n)))
        apply Int.ofNat_dvd.mp
        have hsub : (intModToNat a₁ n : ℤ) = a₁ - (n : ℤ) * q := by linarith
        rw [hsub]
        exact dvd_sub (Int.gcd_dvd_left a₁ n) (dvd_mul_of_dvd_left (Int.gcd_dvd_right a₁ n) q)
    have hmod_g : a₂ * x₂ ≡ b [ZMOD (g : ℤ)] := by
      rw [Int.modEq_iff_dvd] at hmod ⊢
      rcases hmod with ⟨q, hq⟩
      have ha₁g : (g : ℤ) ∣ a₁ := hg_eq ▸ Int.gcd_dvd_left a₁ (n : ℤ)
      have hng : (g : ℤ) ∣ (n : ℤ) := hg_eq ▸ Int.gcd_dvd_right a₁ (n : ℤ)
      have hdiff : b - a₂ * x₂ = a₁ * x₁ + (n : ℤ) * q := by linarith
      rw [hdiff]
      exact dvd_add (dvd_mul_of_dvd_left ha₁g x₁) (dvd_mul_of_dvd_left hng q)
    have hs₂ : (solveModLinear a₂ b g).isSome :=
      (isSome_solveModLinear_iff a₂ b g).mpr ((modLinear_solvable_iff a₂ b g).mp ⟨x₂, hmod_g⟩)
    obtain ⟨y₂, hy₂⟩ := Option.isSome_iff_exists.mp hs₂
    have hdvd_rem : (Int.gcd a₁ (n : ℤ) : ℤ) ∣ b - a₂ * y₂ := by
      rw [← hg_eq]
      exact Int.modEq_iff_dvd.mp (solveModLinear_sound hy₂).1
    have hs₁ : (solveModLinear a₁ (b - a₂ * y₂) n).isSome :=
      (isSome_solveModLinear_iff a₁ (b - a₂ * y₂) n).mpr hdvd_rem
    obtain ⟨y₁, hy₁⟩ := Option.isSome_iff_exists.mp hs₁
    simp [solveModLinear2, g, hy₂, hy₁]

/-- Inner product `∑ i, c_i * x_i` of two integer lists. -/
def listDot : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | _, [] => 0
  | c :: cs, x :: xs => c * x + listDot cs xs

/-- Left empty-list identity for `listDot`. -/
@[simp]
theorem listDot_nil_left (xs : List ℤ) : listDot [] xs = 0 := by rfl

/-- Right empty-list identity for `listDot`. -/
@[simp]
theorem listDot_nil_right (cs : List ℤ) : listDot cs [] = 0 := by
  cases cs <;> rfl

/-- Cons step identity for `listDot`. -/
@[simp]
theorem listDot_cons (c : ℤ) (cs : List ℤ) (x : ℤ) (xs : List ℤ) :
    listDot (c :: cs) (x :: xs) = c * x + listDot cs xs := by rfl

/-- Appending pairs distributes over `listDot` when lengths match. -/
theorem listDot_append : ∀ (cs₁ cs₂ xs₁ xs₂ : List ℤ), xs₁.length = cs₁.length →
    listDot (cs₁ ++ cs₂) (xs₁ ++ xs₂) = listDot cs₁ xs₁ + listDot cs₂ xs₂
  | [], cs₂, [], xs₂, _ => by simp
  | _ :: cs₁, cs₂, _ :: xs₁, xs₂, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [listDot_append cs₁ cs₂ xs₁ xs₂ h, add_assoc]

/-- Dotting any coefficient list with an equal-length zero list yields `0`. -/
theorem listDot_replicate_zero : ∀ cs : List ℤ, listDot cs (List.replicate cs.length 0) = 0
  | [] => rfl
  | _ :: cs => by simp [List.replicate_succ, listDot_replicate_zero cs]

private def modListStep (b : ℤ) (p : ℕ) (st : Bool × List ℤ) (c : ℤ) : Bool × List ℤ :=
  if st.1 then (true, st.2 ++ [0])
  else if intModToNat c p = 0 then (false, st.2 ++ [0])
  else
    match solveModLinear c b p with
    | none => (false, st.2 ++ [0])
    | some x => (true, st.2 ++ [x])

/-- Solver for a multi-variable linear congruence `∑ i, c_i * x_i ≡ b [ZMOD (p : ℤ)]` modulo a
prime `p`: sets all coordinates to `0` if `b ≡ 0 [ZMOD p]`, otherwise sets the first coordinate
with `c_i ≢ 0 [ZMOD p]` to `b * c_i⁻¹ mod p` and all other coordinates to `0`. -/
def solveModLinearListPrime (coeffs : List ℤ) (b : ℤ) (p : ℕ) : Option (List ℤ) :=
  if p = 0 then none
  else
    let init : Bool × List ℤ := (decide (intModToNat b p = 0), [])
    let res := coeffs.foldl (modListStep b p) init
    if res.1 then some res.2 else none

private lemma modListStep_len (b : ℤ) (p : ℕ) :
    ∀ (l : List ℤ) (s : Bool × List ℤ),
      (l.foldl (modListStep b p) s).2.length = s.2.length + l.length
  | [], _ => by simp
  | a :: l, s => by
    rw [List.foldl_cons, modListStep_len b p l]
    have hs : (modListStep b p s a).2.length = s.2.length + 1 := by
      dsimp only [modListStep]
      split_ifs
      · simp
      · simp
      · cases solveModLinear a b p <;> simp
    rw [hs, List.length_cons]
    omega

private lemma modListStep_invariant {b : ℤ} {p : ℕ} (hp : 0 < p) :
    ∀ (cs : List ℤ) (st : Bool × List ℤ),
      (∀ z ∈ st.2, 0 ≤ z ∧ z < (p : ℤ)) →
      (∀ z ∈ (cs.foldl (modListStep b p) st).2, 0 ≤ z ∧ z < (p : ℤ)) ∧
      (st.1 = true →
        (cs.foldl (modListStep b p) st).1 = true ∧
        (cs.foldl (modListStep b p) st).2 = st.2 ++ List.replicate cs.length 0) ∧
      (st.1 = false → (cs.foldl (modListStep b p) st).1 = true →
        ∃ ys, (cs.foldl (modListStep b p) st).2 = st.2 ++ ys ∧ ys.length = cs.length ∧
          listDot cs ys ≡ b [ZMOD (p : ℤ)])
  | [], st, hbd => ⟨hbd, fun h ↦ ⟨h, by simp⟩, fun h0 h1 ↦ by simp [h0] at h1⟩
  | c :: cs, st, hbd => by
    simp only [List.foldl_cons]
    have hbd_step : ∀ z ∈ (modListStep b p st c).2, 0 ≤ z ∧ z < (p : ℤ) := by
      dsimp only [modListStep]
      split_ifs
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hbd z hz
        · rw [List.mem_singleton.mp hz]; exact ⟨le_rfl, Int.natCast_pos.mpr hp⟩
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hbd z hz
        · rw [List.mem_singleton.mp hz]; exact ⟨le_rfl, Int.natCast_pos.mpr hp⟩
      · cases hx : solveModLinear c b p with
        | none =>
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hbd z hz
          · rw [List.mem_singleton.mp hz]; exact ⟨le_rfl, Int.natCast_pos.mpr hp⟩
        | some x =>
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hbd z hz
          · rw [List.mem_singleton.mp hz]; exact (solveModLinear_sound hx).2 hp
    obtain ⟨hbd_r, htrue, hfalse⟩ := modListStep_invariant hp cs (modListStep b p st c) hbd_step
    refine ⟨hbd_r, fun hst ↦ ?_, fun hst hr1 ↦ ?_⟩
    · have hms : modListStep b p st c = (true, st.2 ++ [0]) := by simp [modListStep, hst]
      rw [hms] at htrue ⊢
      obtain ⟨hr, heq⟩ := htrue rfl
      exact ⟨hr, by rw [heq, List.length_cons, List.replicate_succ, List.append_assoc]; rfl⟩
    · by_cases hc0 : intModToNat c p = 0
      · have hms : modListStep b p st c = (false, st.2 ++ [0]) := by simp [modListStep, hst, hc0]
        rw [hms] at hfalse hr1 ⊢
        obtain ⟨ys, hys, hylen, hydot⟩ := hfalse rfl hr1
        exact ⟨0 :: ys, by simpa [List.append_assoc] using hys, by simp [hylen],
          by simpa using hydot⟩
      · cases hx : solveModLinear c b p with
        | none =>
          have hms : modListStep b p st c = (false, st.2 ++ [0]) := by
            simp [modListStep, hst, hc0, hx]
          rw [hms] at hfalse hr1 ⊢
          obtain ⟨ys, hys, hylen, hydot⟩ := hfalse rfl hr1
          exact ⟨0 :: ys, by simpa [List.append_assoc] using hys, by simp [hylen],
            by simpa using hydot⟩
        | some x =>
          have hms : modListStep b p st c = (true, st.2 ++ [x]) := by
            simp [modListStep, hst, hc0, hx]
          rw [hms] at htrue ⊢
          obtain ⟨_, heq⟩ := htrue rfl
          refine ⟨x :: List.replicate cs.length 0,
            by simpa [List.append_assoc] using heq, by simp, ?_⟩
          rw [listDot_cons, listDot_replicate_zero, add_zero]
          exact (solveModLinear_sound hx).1

/-- Soundness of `solveModLinearListPrime`: returns `xs` of length `coeffs.length` with
`0 ≤ x < p` for every `x ∈ xs` and `listDot coeffs xs ≡ b [ZMOD (p : ℤ)]`. -/
theorem solveModLinearListPrime_sound {coeffs : List ℤ} {b : ℤ} {p : ℕ} {xs : List ℤ}
    (hp : 0 < p) (h : solveModLinearListPrime coeffs b p = some xs) :
    xs.length = coeffs.length ∧ (∀ x ∈ xs, 0 ≤ x ∧ x < (p : ℤ)) ∧
      listDot coeffs xs ≡ b [ZMOD (p : ℤ)] := by
  have hp0 : p ≠ 0 := Nat.ne_of_gt hp
  simp only [solveModLinearListPrime, hp0, ↓reduceIte] at h
  set init : Bool × List ℤ := (decide (intModToNat b p = 0), [])
  set res := coeffs.foldl (modListStep b p) init
  split_ifs at h with hr1
  have hxs : xs = res.2 := (Option.some.inj h).symm
  subst hxs
  have hlen : res.2.length = coeffs.length := by
    simpa [res, init] using modListStep_len b p coeffs init
  obtain ⟨hbd, htrue, hfalse⟩ :=
    modListStep_invariant (b := b) hp coeffs init (by simp [init])
  refine ⟨hlen, hbd, ?_⟩
  by_cases hb0 : intModToNat b p = 0
  · have hinit1 : init.1 = true := by simp [init, hb0]
    obtain ⟨_, heq⟩ := htrue hinit1
    simp only [init, List.nil_append] at heq
    rw [heq, listDot_replicate_zero]
    obtain ⟨_, hb⟩ := intModToNat_spec b hp
    simpa [hb0] using hb
  · have hinit0 : init.1 = false := by simp [init, hb0]
    obtain ⟨ys, heq, _, hydot⟩ := hfalse hinit0 hr1
    simp only [init, List.nil_append] at heq
    rwa [heq]

/-- Completeness of `solveModLinearListPrime` for every prime `p`. -/
theorem isSome_solveModLinearListPrime_iff (coeffs : List ℤ) (b : ℤ) {p : ℕ} (hp : p.Prime) :
    (solveModLinearListPrime coeffs b p).isSome ↔
      ∃ xs : List ℤ, xs.length = coeffs.length ∧ listDot coeffs xs ≡ b [ZMOD (p : ℤ)] := by
  refine ⟨fun hs ↦ ?_, fun ⟨xs, _, hdot⟩ ↦ ?_⟩
  · obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨hl, _, hd⟩ := solveModLinearListPrime_sound hp.pos hxs
    exact ⟨xs, hl, hd⟩
  · have hp0 : p ≠ 0 := hp.ne_zero
    have hsolv : ∀ (l : List ℤ) (acc : List ℤ),
        (∃ c ∈ l, intModToNat c p ≠ 0) →
        (l.foldl (modListStep b p) (false, acc)).1 = true := by
      intro l
      induction l with
      | nil => rintro _ ⟨_, h, _⟩; simp at h
      | cons c cs ih =>
        intro acc ⟨d, hd, hdnz⟩
        rw [List.foldl_cons]
        by_cases hc0 : intModToNat c p = 0
        · have hstep : modListStep b p (false, acc) c = (false, acc ++ [0]) := by
            simp [modListStep, hc0]
          rw [hstep]
          rcases List.mem_cons.mp hd with rfl | hdcs
          · exact (hdnz hc0).elim
          · exact ih _ ⟨d, hdcs, hdnz⟩
        · have hnotdvd : ¬ (p : ℤ) ∣ c := by
            intro hdvd
            obtain ⟨hclt, hc⟩ := intModToNat_spec c hp.pos
            rw [Int.modEq_iff_dvd] at hc
            rcases hc with ⟨q, hq⟩
            have hceq : (intModToNat c p : ℤ) = c - (p : ℤ) * q := by linarith
            have hd' : p ∣ intModToNat c p :=
              Int.ofNat_dvd.mp (hceq ▸ dvd_sub hdvd (dvd_mul_right _ _))
            exact hc0 (Nat.eq_zero_of_dvd_of_lt hd' hclt)
          have hgp : Int.gcd c (p : ℤ) ∣ p := Int.ofNat_dvd.mp (Int.gcd_dvd_right c (p : ℤ))
          have hg1 : Int.gcd c (p : ℤ) = 1 := by
            rcases (Nat.dvd_prime hp).mp hgp with h1 | hpeq
            · exact h1
            · exact (hnotdvd (hpeq ▸ Int.gcd_dvd_left c (p : ℤ))).elim
          have hs : (solveModLinear c b p).isSome := by
            rw [isSome_solveModLinear_iff, hg1]; simp
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
          have hstep : modListStep b p (false, acc) c = (true, acc ++ [x]) := by
            simp [modListStep, hc0, hx]
          rw [hstep]
          have hstay : ∀ (m : List ℤ) (a : List ℤ),
              (m.foldl (modListStep b p) (true, a)).1 = true := by
            intro m
            induction m with
            | nil => simp
            | cons _ m ihm => intro a; simp [modListStep, ihm]
          exact hstay cs (acc ++ [x])
    simp only [solveModLinearListPrime, hp0, ↓reduceIte]
    by_cases hb0 : intModToNat b p = 0
    · have hstay : ∀ (m : List ℤ) (a : List ℤ),
          (m.foldl (modListStep b p) (true, a)).1 = true := by
        intro m
        induction m with
        | nil => simp
        | cons _ m ihm => intro a; simp [modListStep, ihm]
      simp [hb0, hstay]
    · suffices hex : ∃ c ∈ coeffs, intModToNat c p ≠ 0 by
        simp [hb0, hsolv coeffs [] hex]
      by_contra hall
      push Not at hall
      have hzero : ∀ (cs ys : List ℤ), (∀ c ∈ cs, intModToNat c p = 0) →
          listDot cs ys ≡ 0 [ZMOD (p : ℤ)] := by
        intro cs
        induction cs with
        | nil => simp [Int.ModEq.refl]
        | cons c cs ih =>
          intro ys hc
          cases ys with
          | nil => simp [Int.ModEq.refl]
          | cons y ys =>
            obtain ⟨_, hcm⟩ := intModToNat_spec c hp.pos
            have hcZ : c ≡ 0 [ZMOD (p : ℤ)] := by
              simpa [hc c List.mem_cons_self] using hcm.symm
            have htail := ih ys fun d hd ↦ hc d (List.mem_cons_of_mem c hd)
            simpa using (hcZ.mul_right y).add htail
      have hbZ : (0 : ℤ) ≡ b [ZMOD (p : ℤ)] := (hzero coeffs xs hall).symm.trans hdot
      obtain ⟨hblt, hbm⟩ := intModToNat_spec b hp.pos
      have hd : p ∣ intModToNat b p := by
        have : (p : ℤ) ∣ (intModToNat b p : ℤ) := by
          simpa [Int.modEq_iff_dvd] using hbZ.trans hbm.symm
        exact Int.ofNat_dvd.mp this
      exact hb0 (Nat.eq_zero_of_dvd_of_lt hd hblt)

/-! ### Multi-tape Turing machine polynomial-time computability -/

/-- `intModToNat` is computable in polynomial time on binary encodings. -/
theorem computableInPolyTime_intModToNat {α : Type} {enc : α ↪ List Bool}
    {z : α → ℤ} {n : α → ℕ}
    (hz : ComputableInPolyTime z enc encIntBin)
    (hn : ComputableInPolyTime n enc encNat) :
    ComputableInPolyTime (fun x ↦ intModToNat (z x) (n x)) enc encNat :=
  ComputableInPolyTime.intBin_natAbs.comp
    (ComputableInPolyTime.intBin_emod' hz (ComputableInPolyTime.intBin_natCast.comp hn))

/-- `solveModLinearNat` is computable in multi-tape Turing machine polynomial time. -/
theorem computableInPolyTime_solveModLinearNat :
    ComputableInPolyTime (fun t : ℕ × ℕ × ℕ ↦ solveModLinearNat t.1 t.2.1 t.2.2)
      encNatTriple (encOption encNat) := by
  have ha : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ ↦ t.1) encNatTriple encNat :=
    ComputableInPolyTime.fst _ _
  have hb : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ ↦ t.2.1) encNatTriple encNat :=
    (ComputableInPolyTime.snd _ _).fst'
  have hn : ComputableInPolyTime (fun t : ℕ × ℕ × ℕ ↦ t.2.2) encNatTriple encNat :=
    (ComputableInPolyTime.snd _ _).snd'
  have ha₀ := ComputableInPolyTime.binary_mod' ha hn
  have hb₀ := ComputableInPolyTime.binary_mod' hb hn
  have hg := ComputableInPolyTime.binary_gcd' hn ha₀
  have hsol := ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.binary_mul'
      (ComputableInPolyTime.binary_modInv' ha₀ hn)
      (ComputableInPolyTime.binary_div' hb₀ hg)) hn
  have hsome := ComputableInPolyTime.optionSome encNat
  have hbranch0 :=
    (ComputableInPolyTime.decide_eq' ha (.const 0)).ite_decide
      ((ComputableInPolyTime.decide_eq' hb (.const 0)).ite_decide
        (hsome.comp (.const 0)) (.const none))
      ((ComputableInPolyTime.decide_eq'
        (ComputableInPolyTime.binary_mod' hb ha) (.const 0)).ite_decide
        (hsome.comp (ComputableInPolyTime.binary_div' hb ha)) (.const none))
  have hbranchPos :=
    (ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.binary_mod' hb₀ hg) (.const 0)).ite_decide
      (hsome.comp hsol) (.const none)
  exact (ComputableInPolyTime.decide_eq' hn (.const 0)).ite_decide hbranch0 hbranchPos

/-- `solveModLinear` is computable in polynomial time on a deterministic multi-tape Turing machine
with binary integer and modulus encodings. -/
theorem computableInPolyTime_solveModLinear :
    ComputableInPolyTime (fun t : ℤ × ℤ × ℕ ↦ solveModLinear t.1 t.2.1 t.2.2)
      encModLinearInput (encOption encIntBin) := by
  have ha : ComputableInPolyTime (fun t : ℤ × ℤ × ℕ ↦ t.1) encModLinearInput encIntBin :=
    ComputableInPolyTime.fst _ _
  have hb : ComputableInPolyTime (fun t : ℤ × ℤ × ℕ ↦ t.2.1) encModLinearInput encIntBin :=
    (ComputableInPolyTime.snd _ _).fst'
  have hn : ComputableInPolyTime (fun t : ℤ × ℤ × ℕ ↦ t.2.2) encModLinearInput encNat :=
    (ComputableInPolyTime.snd _ _).snd'
  have hsome := ComputableInPolyTime.optionSome encIntBin
  have hbranch0 :=
    (ComputableInPolyTime.decide_eq' ha (.const 0)).ite_decide
      ((ComputableInPolyTime.decide_eq' hb (.const 0)).ite_decide
        (hsome.comp (.const (0 : ℤ))) (.const none))
      ((ComputableInPolyTime.decide_eq'
        (ComputableInPolyTime.intBin_emod' hb ha) (.const 0)).ite_decide
        (hsome.comp (ComputableInPolyTime.intBin_ediv' hb ha)) (.const none))
  have hnatCall :
      ComputableInPolyTime
        (fun t : ℤ × ℤ × ℕ ↦
          solveModLinearNat (intModToNat t.1 t.2.2) (intModToNat t.2.1 t.2.2) t.2.2)
        encModLinearInput (encOption encNat) :=
    computableInPolyTime_solveModLinearNat.comp
      ((computableInPolyTime_intModToNat ha hn).prod
        ((computableInPolyTime_intModToNat hb hn).prod hn))
  have hcast_snd :
      ComputableInPolyTime (fun p : (ℤ × ℤ × ℕ) × ℕ ↦ (p.2 : ℤ))
        (encPair encModLinearInput encNat) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.snd encModLinearInput encNat)
  have hbranchPos :
      ComputableInPolyTime
        (fun t : ℤ × ℤ × ℕ ↦
          (solveModLinearNat (intModToNat t.1 t.2.2) (intModToNat t.2.1 t.2.2) t.2.2).map
            Nat.cast)
        encModLinearInput (encOption encIntBin) :=
    ComputableInPolyTime.optionMapWithInput (f := fun (_ : ℤ × ℤ × ℕ) (k : ℕ) ↦ (k : ℤ))
      hnatCall hcast_snd
  exact (ComputableInPolyTime.decide_eq' hn (.const 0)).ite_decide hbranch0 hbranchPos

/-- Compositional polynomial-time helper for `solveModLinear`. -/
theorem computableInPolyTime_solveModLinear' {α : Type} {enc : α ↪ List Bool}
    {a b : α → ℤ} {n : α → ℕ}
    (ha : ComputableInPolyTime a enc encIntBin)
    (hb : ComputableInPolyTime b enc encIntBin)
    (hn : ComputableInPolyTime n enc encNat) :
    ComputableInPolyTime (fun x ↦ solveModLinear (a x) (b x) (n x)) enc (encOption encIntBin) :=
  computableInPolyTime_solveModLinear.comp (ha.prod (hb.prod hn))

/-- `solveModLinear2` is computable in multi-tape Turing machine polynomial time. -/
theorem computableInPolyTime_solveModLinear2 :
    ComputableInPolyTime
      (fun t : ℤ × ℤ × ℤ × ℕ ↦ solveModLinear2 t.1 t.2.1 t.2.2.1 t.2.2.2)
      encModLinear2Input (encOption (encPair encIntBin encIntBin)) := by
  have ha₁ : ComputableInPolyTime (fun t : ℤ × ℤ × ℤ × ℕ ↦ t.1) encModLinear2Input encIntBin :=
    ComputableInPolyTime.fst _ _
  have ha₂ : ComputableInPolyTime (fun t : ℤ × ℤ × ℤ × ℕ ↦ t.2.1) encModLinear2Input encIntBin :=
    (ComputableInPolyTime.snd _ _).fst'
  have hb : ComputableInPolyTime (fun t : ℤ × ℤ × ℤ × ℕ ↦ t.2.2.1) encModLinear2Input encIntBin :=
    (ComputableInPolyTime.snd _ _).snd'.fst'
  have hn : ComputableInPolyTime (fun t : ℤ × ℤ × ℤ × ℕ ↦ t.2.2.2) encModLinear2Input encNat :=
    (ComputableInPolyTime.snd _ _).snd'.snd'
  have hg := ComputableInPolyTime.binary_gcd' (computableInPolyTime_intModToNat ha₁ hn) hn
  have hstep1 := computableInPolyTime_solveModLinear' ha₂ hb hg
  have hp_in := ComputableInPolyTime.fst encModLinear2Input encIntBin
  have hp_x₂ := ComputableInPolyTime.snd encModLinear2Input encIntBin
  have hrem := ComputableInPolyTime.intBin_sub' (hb.comp hp_in)
    (ComputableInPolyTime.intBin_mul' (ha₂.comp hp_in) hp_x₂)
  have hstep2 := computableInPolyTime_solveModLinear' (ha₁.comp hp_in) hrem (hn.comp hp_in)
  have hq_px₂ := ComputableInPolyTime.fst (encPair encModLinear2Input encIntBin) encIntBin
  have hq_x₁ := ComputableInPolyTime.snd (encPair encModLinear2Input encIntBin) encIntBin
  have hinner := hstep2.optionMapWithInput (f := fun px₂ x₁ ↦ (x₁, px₂.2))
    (encC := encPair encIntBin encIntBin)
    (hq_x₁.prod (hp_x₂.comp hq_px₂))
  have houter := hstep1.optionElimWithInput
    (body := fun t x₂ ↦ (solveModLinear t.1 (t.2.2.1 - t.2.1 * x₂) t.2.2.2).map fun x₁ ↦ (x₁, x₂))
    (.const none) hinner
  refine houter.of_enc_eq fun t ↦ ?_
  dsimp only [solveModLinear2]
  cases solveModLinear t.2.1 t.2.2.1 (Nat.gcd (intModToNat t.1 t.2.2.2) t.2.2.2) with
  | none => rfl
  | some x₂ =>
    dsimp only [Option.elim]
    cases solveModLinear t.1 (t.2.2.1 - t.2.1 * x₂) t.2.2.2 <;> rfl

/-- Compositional polynomial-time helper for `solveModLinear2`. -/
theorem computableInPolyTime_solveModLinear2' {α : Type} {enc : α ↪ List Bool}
    {a₁ a₂ b : α → ℤ} {n : α → ℕ}
    (ha₁ : ComputableInPolyTime a₁ enc encIntBin)
    (ha₂ : ComputableInPolyTime a₂ enc encIntBin)
    (hb : ComputableInPolyTime b enc encIntBin)
    (hn : ComputableInPolyTime n enc encNat) :
    ComputableInPolyTime (fun x ↦ solveModLinear2 (a₁ x) (a₂ x) (b x) (n x))
      enc (encOption (encPair encIntBin encIntBin)) :=
  computableInPolyTime_solveModLinear2.comp (ha₁.prod (ha₂.prod (hb.prod hn)))

/-- `solveModLinearListPrime` is computable in multi-tape Turing machine polynomial time. -/
theorem computableInPolyTime_solveModLinearListPrime :
    ComputableInPolyTime
      (fun t : List ℤ × ℤ × ℕ ↦ solveModLinearListPrime t.1 t.2.1 t.2.2)
      encModLinearListInput (encOption (encList encIntBin)) := by
  let encSt : Bool × List ℤ ↪ List Bool := encPair encBool (encList encIntBin)
  let encPar : ℤ × ℕ ↪ List Bool := encPair encIntBin encNat
  have hcoeffs := ComputableInPolyTime.fst (encList encIntBin) encPar
  have hpar := ComputableInPolyTime.snd (encList encIntBin) encPar
  have hb := hpar.fst'
  have hp := hpar.snd'
  have hinit : ComputableInPolyTime
      (fun t : List ℤ × ℤ × ℕ ↦ (decide (intModToNat t.2.1 t.2.2 = 0), ([] : List ℤ)))
      encModLinearListInput encSt :=
    (ComputableInPolyTime.decide_eq' (computableInPolyTime_intModToNat hb hp) (.const 0)).prod
      (.const [])
  have hstep : ComputableInPolyTime
      (fun q : ((ℤ × ℕ) × (Bool × List ℤ)) × ℤ ↦ modListStep q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair encPar encSt) encIntBin) encSt := by
    have hq1 := ComputableInPolyTime.fst (encPair encPar encSt) encIntBin
    have hc := ComputableInPolyTime.snd (encPair encPar encSt) encIntBin
    have hqb := hq1.fst'.fst'
    have hqp := hq1.fst'.snd'
    have hqst := hq1.snd'
    have hlist := hqst.snd'
    have happ0 := ComputableInPolyTime.listAppend' hlist (.const [0])
    have hsol := computableInPolyTime_solveModLinear' hc hqb hqp
    have hr_in := ComputableInPolyTime.fst (encPair (encPair encPar encSt) encIntBin) encIntBin
    have hr_x := ComputableInPolyTime.snd (encPair (encPair encPar encSt) encIntBin) encIntBin
    have hsingle_x := ComputableInPolyTime.cons' hr_x (.const [])
    have happ_x :
        ComputableInPolyTime
          (fun r : (((ℤ × ℕ) × (Bool × List ℤ)) × ℤ) × ℤ ↦ (true, r.1.1.2.2 ++ [r.2]))
          (encPair (encPair (encPair encPar encSt) encIntBin) encIntBin) encSt :=
      (ComputableInPolyTime.const true).prod
        (ComputableInPolyTime.listAppend' (hlist.comp hr_in) hsingle_x)
    have hmatch := hsol.optionElimWithInput
      (body := fun q x ↦ (true, q.1.2.2 ++ [x]))
      ((ComputableInPolyTime.const false).prod happ0) happ_x
    have raw := hqst.fst'.ite' ((ComputableInPolyTime.const true).prod happ0)
      ((ComputableInPolyTime.decide_eq'
        (computableInPolyTime_intModToNat hc hqp) (.const 0)).ite_decide
        ((ComputableInPolyTime.const false).prod happ0) hmatch)
    refine raw.of_enc_eq fun q ↦ ?_
    dsimp only [modListStep]
    split_ifs
    · rfl
    · rfl
    · cases solveModLinear q.2 q.1.1.1 q.1.1.2 <;> rfl
  have hlist_guard : ComputableInPolyTime
      (fun t : List ℤ × ℤ × ℕ ↦ if t.2.2 = 0 then ([] : List ℤ) else t.1)
      encModLinearListInput (encList encIntBin) :=
    (ComputableInPolyTime.decide_eq' hp (.const 0)).ite_decide (.const []) hcoeffs
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encIntBin) (encL := encList encIntBin) (encB := encSt) (encP := encPar)
    (par := fun t : List ℤ × ℤ × ℕ ↦ t.2)
    (list := fun t : List ℤ × ℤ × ℕ ↦ if t.2.2 = 0 then [] else t.1)
    (init := fun t : List ℤ × ℤ × ℕ ↦ (decide (intModToNat t.2.1 t.2.2 = 0), []))
    (step := fun bp st c ↦ modListStep bp.1 bp.2 st c)
    hpar hlist_guard hinit hstep
    (growth := fun t ↦ 4 * (encModLinearListInput t).length + 8)
    (((PolyBounded.const 4).mul .self).add (.const 8))
    (fun t st c hc ↦ by
      by_cases hp0 : t.2.2 = 0
      · simp [hp0] at hc
      · have hpos : 0 < t.2.2 := Nat.pos_of_ne_zero hp0
        have hp_len : t.2.2.size ≤ (encModLinearListInput t).length := by
          have h1 := length_le_encPair_right (encList encIntBin) encPar t
          have h2 := length_le_encPair_right encIntBin encNat t.2
          have h3 : (encNat t.2.2).length = t.2.2.size := by
            rw [encNat_apply, ← Nat.size_eq_bits_len]
          exact (h3 ▸ h2).trans h1
        have hbound_x : ∀ x : ℤ, 0 ≤ x → x < (t.2.2 : ℤ) → x.natAbs.size ≤ t.2.2.size := by
          intro x hx0 hxlt
          apply Nat.size_le_size
          have habs : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hx0
          exact Int.ofNat_le.mp (habs ▸ hxlt.le)
        have hpair_eq : ∀ (b' : Bool) (x : ℤ), x.natAbs.size ≤ t.2.2.size →
            (encSt (b', st.2 ++ [x])).length ≤
              (encSt st).length + (4 * (encModLinearListInput t).length + 8) := by
          intro b' x _
          have hx_bits : x.natAbs.bits.length = x.natAbs.size := Nat.size_eq_bits_len x.natAbs
          have hl : (encList encIntBin (st.2 ++ [x])).length =
              (encList encIntBin st.2).length + (2 * (x.natAbs.size + 1) + 1) := by
            simp only [length_encList, List.map_append, List.sum_append, List.map_cons,
              List.map_nil, List.sum_cons, List.sum_nil, length_encIntBin]
            omega
          have hb_len : ∀ u : Bool, (encBool u).length = 1 := fun u ↦ by cases u <;> rfl
          have hst1 : (encSt (b', st.2 ++ [x])).length =
              3 + (encList encIntBin (st.2 ++ [x])).length := by
            simp only [encSt, length_encPair, hb_len]
          have hst0 : (encSt st).length = 3 + (encList encIntBin st.2).length := by
            simp only [encSt, length_encPair, hb_len]
          omega
        dsimp only [modListStep]
        split_ifs
        · exact hpair_eq true 0 (by simp)
        · exact hpair_eq false 0 (by simp)
        · cases hx : solveModLinear c t.2.1 t.2.2 with
          | none => exact hpair_eq false 0 (by simp)
          | some x =>
            obtain ⟨hx0, hxlt⟩ := (solveModLinear_sound hx).2 hpos
            exact hpair_eq true x (hbound_x x hx0 hxlt))
  have hfinal := (ComputableInPolyTime.decide_eq' hp (.const 0)).ite_decide (.const none)
    (hfold.fst'.ite'
      ((ComputableInPolyTime.optionSome (encList encIntBin)).comp hfold.snd')
      (.const none))
  refine hfinal.of_enc_eq fun t ↦ ?_
  by_cases hp0 : t.2.2 = 0 <;> simp [solveModLinearListPrime, hp0]

/-- The decision problem of modular linear congruence solvability lies in `Cslib.Complexity.P`. -/
theorem modLinearSolvableSet_mem_P :
    { t : ℤ × ℤ × ℕ | ∃ x : ℤ, t.1 * x ≡ t.2.1 [ZMOD (t.2.2 : ℤ)] } ∈
      Cslib.Complexity.P encModLinearInput := by
  rw [Cslib.Complexity.mem_P]
  refine ⟨fun t ↦ (solveModLinear t.1 t.2.1 t.2.2).isSome,
    computableInPolyTime_solveModLinear.optionIsSome, fun t ↦ ?_⟩
  rw [Set.mem_ofPred_eq, modLinear_solvable_iff, isSome_solveModLinear_iff]

end CslibFrontier

end
