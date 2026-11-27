/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Padding.Tally
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Hartmanis--Immerman--Sewelson equivalence for tally languages in `NP`

`CslibFrontier.Computability.Complexity.Classes.Padding.Tally` proves one direction of the theorem
of Hartmanis, Immerman and Sewelson (`Cslib.Complexity.E_eq_NE_of_tally`): if every tally language
in `NP` lies in `P`, then `E = NE` (and `EXP = NEXP`). This module proves the converse inclusion
and records the complete equivalence between:

1. linear exponential time collapse `E encBits = NE encBits`;
2. polynomial-time decidability of every tally language in `NP`
   (`∀ L ∈ TALLY, L ∈ NP encBits → L ∈ P encBits`);
3. collapse of unary polynomial-time classes `P encUnary = NP encUnary`.

## Main results

* `Cslib.Complexity.mem_P_encUnary_preimage_iff_of_mem_TALLY`,
  `Cslib.Complexity.mem_NP_encUnary_preimage_iff_of_mem_TALLY`: a tally language lies in `P`
  (resp. `NP`) iff its `encUnary` preimage lies in `P encUnary` (resp. `NP encUnary`).
* `Cslib.Complexity.image_encUnary_mem_P_iff`, `Cslib.Complexity.image_encUnary_mem_NP_iff`:
  `encUnary '' A` is in `P encBits` (resp. `NP encBits`) iff `A` is in `P encUnary`
  (resp. `NP encUnary`).
* `Cslib.Complexity.P_encUnary_eq_NP_encUnary_iff_tally`: `P encUnary = NP encUnary` iff every
  tally problem in `NP encBits` lies in `P encBits`.
* `Cslib.Complexity.P_encUnary_eq_NP_encUnary_of_E_eq_NE`,
  `Cslib.Complexity.tally_NP_subset_P_of_E_eq_NE`: the converse direction of
  Hartmanis--Immerman--Sewelson.
* `Cslib.Complexity.E_eq_NE_iff_tally`,
  `Cslib.Complexity.P_encUnary_eq_NP_encUnary_iff_E_eq_NE`,
  `Cslib.Complexity.P_encUnary_ne_NP_encUnary_iff_E_ne_NE`,
  `Cslib.Complexity.P_ne_NP_of_P_encUnary_ne_NP_encUnary`: the full
  Hartmanis--Immerman--Sewelson characterization and `P ≠ NP` consequence.
-/

public section

namespace Cslib.Complexity

open Filter Turing.MultiTapeTM

private theorem allTrue_mem_P : {x : List Bool | ∀ b ∈ x, b = true} ∈ P encBits :=
  ⟨fun x => decide (x = List.replicate x.length true), by fun_prop, fun x => by
    simp [List.eq_replicate_iff]⟩

private theorem mem_tally_iff_length {L : Set (List Bool)} (hT : L ∈ TALLY) (x : List Bool) :
    x ∈ L ↔ (∀ b ∈ x, b = true) ∧ encUnary x.length ∈ L := by
  constructor
  · intro hx
    have hall : ∀ b ∈ x, b = true := hT x hx
    have hrep : x = List.replicate x.length true := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    exact ⟨hall, by simpa only [encUnary_apply, ← hrep] using hx⟩
  · rintro ⟨hall, hlen⟩
    have hrep : x = List.replicate x.length true := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    simpa only [encUnary_apply, ← hrep] using hlen

/-- A tally language `L ∈ TALLY` lies in `P encBits` iff its unary preimage `encUnary ⁻¹' L` lies
in `P encUnary`. -/
theorem mem_P_encUnary_preimage_iff_of_mem_TALLY {L : Set (List Bool)} (hT : L ∈ TALLY) :
    encUnary ⁻¹' L ∈ P encUnary ↔ L ∈ P encBits := by
  constructor
  · rintro ⟨dec, hdec, hiff⟩
    have hones : ComputableInPolyTime
        (fun x : List Bool => decide (x = List.replicate x.length true)) encBits encBool := by
      fun_prop
    have hlen : ComputableInPolyTime (fun x : List Bool => dec x.length) encBits encBool :=
      hdec.comp (ComputableInPolyTime.encoding_length encBits)
    refine ⟨fun x => decide (x = List.replicate x.length true) && dec x.length,
      ComputableInPolyTime.bool_and' hones hlen, fun x => ?_⟩
    rw [mem_tally_iff_length hT, ← Set.mem_preimage, hiff x.length, Bool.and_eq_true,
      decide_eq_true_eq, List.eq_replicate_iff]
    simp
  · intro hL
    exact PolyTimeReducible.mem_P ⟨encUnary, ComputableInPolyTime.of_eq fun _ => rfl,
      fun _ => Iff.rfl⟩ hL

/-- A tally language `L ∈ TALLY` lies in `NP encBits` iff its unary preimage `encUnary ⁻¹' L` lies
in `NP encUnary`. -/
theorem mem_NP_encUnary_preimage_iff_of_mem_TALLY {L : Set (List Bool)} (hT : L ∈ TALLY) :
    encUnary ⁻¹' L ∈ NP encUnary ↔ L ∈ NP encBits := by
  constructor
  · intro hpre
    have hlen : {x : List Bool | x.length ∈ encUnary ⁻¹' L} ∈ NP encBits :=
      PolyTimeReducible.mem_NP ⟨List.length, ComputableInPolyTime.encoding_length encBits,
        fun _ => Iff.rfl⟩ hpre
    have heq : L = {x : List Bool | ∀ b ∈ x, b = true} ∩
        {x : List Bool | x.length ∈ encUnary ⁻¹' L} :=
      Set.ext fun x => mem_tally_iff_length hT x
    rw [heq]
    exact inter_mem_NP (P_subset_NP allTrue_mem_P) hlen
  · intro hL
    exact PolyTimeReducible.mem_NP ⟨encUnary, ComputableInPolyTime.of_eq fun _ => rfl,
      fun _ => Iff.rfl⟩ hL

/-- For every set `A : Set ℕ`, the tally language `encUnary '' A` lies in `P encBits` iff
`A ∈ P encUnary`. -/
theorem image_encUnary_mem_P_iff {A : Set ℕ} :
    encUnary '' A ∈ P encBits ↔ A ∈ P encUnary := by
  have hpre : encUnary ⁻¹' (encUnary '' A) = A := Set.preimage_image_eq A encUnary.injective
  simpa only [hpre] using
    (mem_P_encUnary_preimage_iff_of_mem_TALLY (image_encUnary_mem_TALLY A)).symm

/-- For every set `A : Set ℕ`, the tally language `encUnary '' A` lies in `NP encBits` iff
`A ∈ NP encUnary`. -/
theorem image_encUnary_mem_NP_iff {A : Set ℕ} :
    encUnary '' A ∈ NP encBits ↔ A ∈ NP encUnary := by
  have hpre : encUnary ⁻¹' (encUnary '' A) = A := Set.preimage_image_eq A encUnary.injective
  simpa only [hpre] using
    (mem_NP_encUnary_preimage_iff_of_mem_TALLY (image_encUnary_mem_TALLY A)).symm

/-- `P encUnary = NP encUnary` iff every tally language in `NP encBits` lies in `P encBits`. -/
theorem P_encUnary_eq_NP_encUnary_iff_tally :
    P encUnary = NP encUnary ↔ ∀ L ∈ TALLY, L ∈ NP encBits → L ∈ P encBits := by
  constructor
  · intro hEq L hT hNP
    rw [← mem_P_encUnary_preimage_iff_of_mem_TALLY hT, hEq,
      mem_NP_encUnary_preimage_iff_of_mem_TALLY hT]
    exact hNP
  · intro hTally
    refine P_subset_NP.antisymm fun A hA => ?_
    rw [← image_encUnary_mem_P_iff]
    exact hTally (encUnary '' A) (image_encUnary_mem_TALLY A) (image_encUnary_mem_NP_iff.mpr hA)

private theorem two_pow_size_le_two_mul_add_one (n : ℕ) : 2 ^ n.size ≤ 2 * n + 1 := by
  by_cases hn : n = 0
  · subst hn; simp
  · have hpos : 1 ≤ n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    have hle : 2 ^ (n.size - 1) ≤ n :=
      not_lt.mp (Nat.size_le.not.mp (not_le.mpr (Nat.sub_lt hpos zero_lt_one)))
    have hpow : 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ']
    omega

/-- Converse of Hartmanis--Immerman--Sewelson: `E encBits = NE encBits` implies
`P encUnary = NP encUnary`. -/
theorem P_encUnary_eq_NP_encUnary_of_E_eq_NE (hE : E encBits = NE encBits) :
    P encUnary = NP encUnary := by
  refine P_subset_NP.antisymm fun A hA => ?_
  have hTallyNP : encUnary '' A ∈ NP encBits := image_encUnary_mem_NP_iff.mpr hA
  obtain ⟨td, sd, htd, hsd, hdecTS⟩ := ComputableInPolyTime.bitsToNat
  have hdecO : ComputableInO ofBits encBits encNat
      (fun w => td w.length) (fun w => sd w.length + w.length) :=
    ⟨1, hdecTS.mono (fun w => by simp [encBits_apply])
        (fun w => by simp [encBits_apply]; omega),
      fun w => by
        have hsz : (ofBits w).size ≤ w.length := Nat.size_le.mpr (ofBits_lt_two_pow w)
        simp only [encNat_apply, Nat.size_eq_bits_len, one_mul] at hsz ⊢; omega⟩
  obtain ⟨C₁, hC₁⟩ := htd.exists_le_mul_two_pow
  obtain ⟨C₂, hC₂⟩ := (hsd.add (by fun_prop : PolynomiallyBounded id)).exists_le_mul_two_pow
  let expand : List Bool → List Bool := fun w => List.replicate (ofBits w) true
  have hexp : ComputableInO expand encBits encBits
      (fun w => (C₁ + 2) * 2 ^ w.length) (fun w => (C₂ + 2) * 2 ^ w.length) := by
    have hcomp : ComputableInO (fun w => ofBits w) encBits encUnary
        (fun w => td w.length + ofBits w) (fun w => (sd w.length + w.length) + ofBits w) :=
      ComputableInO.natToUnary.comp hdecO
    have hbits := (ComputableInO.of_eq (f := encUnary) (encIn := encUnary) (encMid := encBits)
      fun _ => rfl).comp hcomp
    refine hbits.mono_le (fun w => ?_) (fun w => ?_)
    · have h1 := hC₁ w.length
      have h2 : ofBits w < 2 ^ w.length := ofBits_lt_two_pow w
      simp only [encUnary_apply, List.length_replicate]
      nlinarith
    · have h1 := hC₂ w.length
      have h2 : ofBits w < 2 ^ w.length := ofBits_lt_two_pow w
      dsimp only [id] at h1
      simp only [encUnary_apply, List.length_replicate]
      nlinarith
  obtain ⟨D, hD⟩ := preimage_mem_NTIME_of_mem_NP hTallyNP
    (T₀ := fun m => (C₁ + 2) * 2 ^ m) hexp
  have hBinNE : expand ⁻¹' (encUnary '' A) ∈ NE encBits := by
    refine mem_NE_iff.mpr ⟨2 * D, NTIME_mono_of_eventually_le ?_ hD⟩
    filter_upwards [eventually_ge_atTop (C₁ + 3)] with m hm
    have hbase : (C₁ + 2) * 2 ^ m + 1 ≤ 2 ^ (C₁ + 3) * 2 ^ m := by
      have hC : C₁ + 3 ≤ 2 ^ (C₁ + 3) := (Nat.lt_two_pow_self (n := C₁ + 3)).le
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      nlinarith
    calc ((C₁ + 2) * 2 ^ m + 1) ^ D
        ≤ (2 ^ (C₁ + 3) * 2 ^ m) ^ D := Nat.pow_le_pow_left hbase D
      _ = 2 ^ (D * (C₁ + 3 + m)) := by rw [← pow_add, ← pow_mul, mul_comm]
      _ ≤ 2 ^ (2 * D * m) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  rw [← hE] at hBinNE
  obtain ⟨k, hk⟩ := mem_E_iff.mp hBinNE
  have htoBitsO : ComputableInO (fun n : ℕ => n.bits) encUnary encBits
      (fun n => 2 * n) (fun n => 2 * n) := by
    refine ((ComputableInO.of_eq (f := encNat) (encIn := encNat) (encMid := encBits)
      fun _ => rfl).comp ComputableInO.unaryToNat).mono_le (fun n => ?_) (fun n => ?_) <;>
    · have hsz : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
      rw [← Nat.size_eq_bits_len] at hsz
      simp only [encNat_apply]; omega
  have hpreA : A = (fun n : ℕ => n.bits) ⁻¹' (expand ⁻¹' (encUnary '' A)) := by
    ext n
    have hof : ∀ m : ℕ, ofBits m.bits = m := fun m => by
      induction m using Nat.binaryRec with
      | zero => simp [ofBits]
      | bit b k ih =>
        rcases eq_or_ne k 0 with rfl | hk
        · cases b <;> simp [ofBits, Nat.bit]
        · rw [Nat.bits_append_bit k b (fun h => absurd h hk)]
          cases b <;> simp [ofBits, Nat.bit]
    simp [expand, hof n]
  let M : ℕ := max 1 k
  refine mem_P_iff_exists_mem_DTIME.mpr ⟨M + 1, ?_⟩
  rw [hpreA]
  refine DTIME_mono_of_eventually_le (t₁ := fun n => 2 * n + (2 * n + 1) ^ k) ?_
    (preimage_mem_DTIME (C := 1) hk htoBitsO fun n => ?_)
  · filter_upwards [eventually_ge_atTop (2 + 3 ^ k + 1)] with n hn
    have hn1 : 1 ≤ n := by have : 0 ≤ 3 ^ k := Nat.zero_le _; omega
    have h1 : n ≤ n ^ M := by
      simpa using Nat.pow_le_pow_right hn1 (le_max_left 1 k)
    have h2 : (2 * n + 1) ^ k ≤ 3 ^ k * n ^ M := by
      calc (2 * n + 1) ^ k ≤ (3 * n) ^ k := Nat.pow_le_pow_left (by omega) k
        _ = 3 ^ k * n ^ k := Nat.mul_pow 3 n k
        _ ≤ 3 ^ k * n ^ M :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn1 (le_max_right 1 k))
    calc 2 * n + (2 * n + 1) ^ k
        ≤ (2 + 3 ^ k) * n ^ M := by nlinarith
      _ ≤ n * n ^ M := Nat.mul_le_mul_right _ (by nlinarith)
      _ = n ^ (M + 1) := by rw [pow_succ']
  · simp only [encUnary_apply, List.length_replicate, encBits_apply]
    have hsz : 2 ^ (k * n.bits.length) ≤ (2 * n + 1) ^ k := by
      rw [Nat.size_eq_bits_len, mul_comm, pow_mul]
      exact Nat.pow_le_pow_left (two_pow_size_le_two_mul_add_one n) k
    omega

/-- If `E encBits = NE encBits`, then every tally language in `NP encBits` lies in `P encBits`. -/
theorem tally_NP_subset_P_of_E_eq_NE (hE : E encBits = NE encBits) :
    ∀ L ∈ TALLY, L ∈ NP encBits → L ∈ P encBits :=
  P_encUnary_eq_NP_encUnary_iff_tally.mp (P_encUnary_eq_NP_encUnary_of_E_eq_NE hE)

/-- **Hartmanis--Immerman--Sewelson theorem**: `E encBits = NE encBits` iff every tally language in
`NP encBits` belongs to `P encBits`. -/
theorem E_eq_NE_iff_tally :
    E encBits = NE encBits ↔ ∀ L ∈ TALLY, L ∈ NP encBits → L ∈ P encBits :=
  ⟨tally_NP_subset_P_of_E_eq_NE, E_eq_NE_of_tally⟩

/-- **Hartmanis--Immerman--Sewelson theorem (unary form)**: `P encUnary = NP encUnary` iff
`E encBits = NE encBits`. -/
theorem P_encUnary_eq_NP_encUnary_iff_E_eq_NE :
    P encUnary = NP encUnary ↔ E encBits = NE encBits :=
  P_encUnary_eq_NP_encUnary_iff_tally.trans E_eq_NE_iff_tally.symm

/-- Existence of a unary language in `NP encUnary \ P encUnary` is equivalent to
`E encBits ≠ NE encBits`. -/
theorem P_encUnary_ne_NP_encUnary_iff_E_ne_NE :
    P encUnary ≠ NP encUnary ↔ E encBits ≠ NE encBits :=
  P_encUnary_eq_NP_encUnary_iff_E_eq_NE.not

/-- Separation `P encUnary ≠ NP encUnary` implies standard binary separation
`P encBits ≠ NP encBits`. -/
theorem P_ne_NP_of_P_encUnary_ne_NP_encUnary (h : P encUnary ≠ NP encUnary) :
    P encBits ≠ NP encBits := fun hEq =>
  (P_encUnary_ne_NP_encUnary_iff_E_ne_NE.mp h) (E_eq_NE_of_P_eq_NP hEq)

end Cslib.Complexity
