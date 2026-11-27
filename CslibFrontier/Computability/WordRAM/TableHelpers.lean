/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Stamped
import CslibFrontier.Computability.WordRAM.CountingLoop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Word-RAM Primitives for Lookup Tables and Stamped Memory

This module provides reusable `Cslib.WordRAM.Code .standard` subroutines and binary-string coding
lemmas for Method-of-Four-Russians lookup-table constructions:

1. `bitStringCode`, `bitStringMask`, `bitsOfMaskBool`: bijective base-2 indexing of bitstrings of
   length `≤ ν` into `[1, 2 ^ (ν + 1))`.
2. `computeHCode`: computes the bank boundary `H = 2 ^ (W - 3)` from `width%` in `5` instructions.
3. `natLog2Code`: computes `Nat.log 2 v` in `≤ 4 * Nat.log 2 v + 6` instructions.
4. `copyInitToStampedCode`: copies an array slice into a generation-stamped bank as `Data.init`.
5. `unpackBitsToStampedCode`: unpacks `(len, mask)` into a generation-stamped bank as `Data.init`.
6. `bitStringCodeStamped`: validates a stamped `0`/`1` slice and computes its `bitStringCode`.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

public section

namespace CslibFrontier.WordRAM

open Cslib.WordRAM

/-! ### Bijective binary-string coding for lookup tables -/

/-- Bijective base-2 index of a bitstring `z`: `2^|z| + ∑_{i < |z|} z[i] · 2^i`, mapping
bitstrings of length `≤ ν` injectively into `[1, 2^(ν + 1))`. -/
def bitStringCode (z : List Bool) : ℕ :=
  2 ^ z.length + (z.zipIdx.map fun p => p.1.toNat * 2 ^ p.2).sum

private theorem bitStringCode_aux_le (z : List Bool) (k : ℕ) :
    (z.zipIdx k |>.map fun p => p.1.toNat * 2 ^ p.2).sum + 2 ^ k ≤ 2 ^ (k + z.length) := by
  induction z generalizing k with
  | nil => simp
  | cons b z ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, List.length_cons]
    have h1 := ih (k + 1)
    have h2 : b.toNat * 2 ^ k ≤ 2 ^ k := by cases b <;> simp
    have h3 : k + 1 + z.length = k + z.length + 1 := by omega
    have h4 : k + (z.length + 1) = k + z.length + 1 := by omega
    rw [h3] at h1
    rw [h4]
    rw [pow_succ] at h1 ⊢
    omega

private theorem bitStringCode_aux_lt (z : List Bool) (k : ℕ) :
    (z.zipIdx k |>.map fun p => p.1.toNat * 2 ^ p.2).sum < 2 ^ (k + z.length) := by
  have h1 := bitStringCode_aux_le z k
  have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- `bitStringCode z` is strictly less than `2 ^ (z.length + 1)`. -/
theorem bitStringCode_lt (z : List Bool) : bitStringCode z < 2 ^ (z.length + 1) := by
  unfold bitStringCode
  have h := bitStringCode_aux_lt z 0
  rw [Nat.zero_add] at h
  rw [pow_succ]
  omega

/-- `bitStringCode z` is at least `2 ^ z.length`. -/
theorem le_bitStringCode (z : List Bool) : 2 ^ z.length ≤ bitStringCode z :=
  Nat.le_add_right _ _

/-- `bitStringCode z` is strictly positive. -/
theorem bitStringCode_pos (z : List Bool) : 0 < bitStringCode z :=
  lt_of_lt_of_le (Nat.pos_of_ne_zero (by positivity)) (le_bitStringCode z)

private theorem bitStringCode_aux_shift (z : List Bool) (k : ℕ) :
    (z.zipIdx k |>.map fun p => p.1.toNat * 2 ^ p.2).sum =
      2 ^ k * (z.zipIdx 0 |>.map fun p => p.1.toNat * 2 ^ p.2).sum := by
  induction z generalizing k with
  | nil => simp
  | cons b z ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons]
    rw [ih (k + 1), ih 1, pow_succ, pow_one, mul_add]
    ring

/-- The bitstring length equals `Nat.log 2 (bitStringCode z)`. -/
theorem natLog_bitStringCode (z : List Bool) : Nat.log 2 (bitStringCode z) = z.length := by
  apply le_antisymm
  · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (Nat.ne_of_gt (bitStringCode_pos z))
      (bitStringCode_lt z))
  · exact Nat.le_log_of_pow_le Nat.one_lt_two (le_bitStringCode z)

/-- `bitStringCode` is injective on `List Bool`. -/
theorem bitStringCode_injective : Function.Injective bitStringCode := by
  intro z₁ z₂ h
  have hlen : z₁.length = z₂.length := by
    rw [← natLog_bitStringCode z₁, ← natLog_bitStringCode z₂, h]
  have hsum : (z₁.zipIdx.map fun p => p.1.toNat * 2 ^ p.2).sum =
      (z₂.zipIdx.map fun p => p.1.toNat * 2 ^ p.2).sum := by
    unfold bitStringCode at h
    rw [hlen] at h
    omega
  clear h
  induction z₁ generalizing z₂ with
  | nil =>
    cases z₂ with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons b₁ z₁ ih =>
    cases z₂ with
    | nil => simp at hlen
    | cons b₂ z₂ =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, pow_zero, mul_one] at hsum
      rw [bitStringCode_aux_shift z₁ 1, bitStringCode_aux_shift z₂ 1, pow_one] at hsum
      have hb : b₁ = b₂ := by
        cases b₁ <;> cases b₂ <;> simp at hsum ⊢ <;> omega
      subst hb
      have hrest : (z₁.zipIdx.map fun p => p.1.toNat * 2 ^ p.2).sum =
          (z₂.zipIdx.map fun p => p.1.toNat * 2 ^ p.2).sum := by omega
      exact congrArg (List.cons b₁) (ih hlen hrest)

/-- Bitwise representation of the lower `z.length` bits of `bitStringCode z`. -/
def bitStringMask (z : List Bool) : ℕ :=
  (z.zipIdx.map fun p => p.1.toNat * 2 ^ p.2).sum

theorem bitStringCode_eq_two_pow_add_mask (z : List Bool) :
    bitStringCode z = 2 ^ z.length + bitStringMask z := by
  unfold bitStringCode bitStringMask; rfl

theorem bitStringMask_lt (z : List Bool) : bitStringMask z < 2 ^ z.length := by
  simpa [bitStringMask] using bitStringCode_aux_lt z 0

theorem bitStringMask_cons (b : Bool) (z : List Bool) :
    bitStringMask (b :: z) = b.toNat + 2 * bitStringMask z := by
  unfold bitStringMask
  simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, pow_zero, mul_one]
  rw [bitStringCode_aux_shift z 1, pow_one]

theorem bitStringMask_testBit (z : List Bool) (i : ℕ) (hi : i < z.length) :
    (bitStringMask z >>> i) % 2 = (z[i]).toNat := by
  induction z generalizing i with
  | nil => simp at hi
  | cons b z ih =>
    rw [bitStringMask_cons]
    cases i with
    | zero =>
      simp only [Nat.shiftRight_zero, List.getElem_cons_zero]
      cases b <;> simp
    | succ i =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
      have hsr : (b.toNat + 2 * bitStringMask z) >>> (i + 1) = bitStringMask z >>> i := by
        rw [Nat.add_comm i 1, Nat.shiftRight_add, Nat.shiftRight_one]
        congr 1; cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      rw [hsr]
      simpa using ih i hi

/-- `bitStringCode` when the input is encoded as `0`/`1` words via `Bool.toNat`. -/
theorem bitStringCode_eq_of_mem {z : List Bool} {mem : ℕ → ℕ} {base : ℕ}
    (hm : ∀ i (hi : i < z.length), mem (base + i) = (z[i]).toNat) :
    bitStringCode z =
      2 ^ z.length + ((List.range z.length).map fun i => mem (base + i) * 2 ^ i).sum := by
  unfold bitStringCode
  congr 1
  have hlen : (z.zipIdx.map fun p => p.1.toNat * 2 ^ p.2).length =
      ((List.range z.length).map fun i => mem (base + i) * 2 ^ i).length := by simp
  refine congrArg List.sum (List.ext_getElem hlen fun i hi₁ hi₂ => ?_)
  have hi : i < z.length := by simpa using hi₂
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add, List.getElem_range]
  rw [hm i hi]

/-- Boolean bitstring decoded from `(len, mask)` (little-endian bits `0 .. len - 1`). -/
def bitsOfMaskBool (len mask : ℕ) : List Bool :=
  (List.range len).map fun i => decide ((mask >>> i) % 2 = 1)

theorem length_bitsOfMaskBool (len mask : ℕ) : (bitsOfMaskBool len mask).length = len := by
  simp [bitsOfMaskBool]

theorem getElem_bitsOfMaskBool {len mask i : ℕ} (hi : i < (bitsOfMaskBool len mask).length) :
    (bitsOfMaskBool len mask)[i] = decide ((mask >>> i) % 2 = 1) := by
  simp [bitsOfMaskBool]

theorem bitStringMask_bitsOfMaskBool (len mask : ℕ) (h : mask < 2 ^ len) :
    bitStringMask (bitsOfMaskBool len mask) = mask := by
  induction len generalizing mask with
  | zero =>
    simp only [pow_zero] at h
    have : mask = 0 := by omega
    subst this; simp [bitsOfMaskBool, bitStringMask]
  | succ len ih =>
    have hcons : bitsOfMaskBool (len + 1) mask =
        decide (mask % 2 = 1) :: bitsOfMaskBool len (mask / 2) := by
      simp only [bitsOfMaskBool, List.range_succ_eq_map, List.map_cons, Nat.shiftRight_zero,
        List.map_map, Function.comp_def]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      rw [show i.succ = 1 + i by omega, Nat.shiftRight_add, Nat.shiftRight_one]
    rw [hcons, bitStringMask_cons, ih (mask / 2) (by rw [pow_succ] at h; omega)]
    have : (decide (mask % 2 = 1)).toNat = mask % 2 := by
      rcases Nat.mod_two_eq_zero_or_one mask with hm | hm <;> simp [hm]
    rw [this]; omega

theorem bitStringCode_bitsOfMaskBool (len mask : ℕ) (h : mask < 2 ^ len) :
    bitStringCode (bitsOfMaskBool len mask) = 2 ^ len + mask := by
  rw [bitStringCode_eq_two_pow_add_mask, length_bitsOfMaskBool,
    bitStringMask_bitsOfMaskBool len mask h]

/-! ### Reusable Word-RAM Building Blocks -/

/-- Compute `H = 2 ^ (W - 3)` into register `0` in `5` instructions (reading `width%`). -/
def computeHCode : Code .standard 2 :=
  let r0 : Fin 2 := 0
  let r1 : Fin 2 := 1
  ram[ r0 ← width%; r1 ← #3; r0 ← r0 - r1; r1 ← #1; r0 ← r1 <<< r0 ]

/-- `computeHCode` is `rand`-free. -/
theorem isRandFree_computeHCode : computeHCode.IsRandFree := by
  simp [computeHCode, Code.IsRandFree]

/-- `computeHCode` computes `2 ^ (W - 3)` in `5` instructions without touching memory. -/
theorem computeHCode_exec {W : ℕ} (hW : 3 ≤ W) (x : Data 2) :
    ∃ y : Data 2, ExecWithin W computeHCode x y 5 ∧
      y.regs 0 = 2 ^ (W - 3) ∧ y.mem = x.mem := by
  have h3 : Fits W 3 := by
    have : 8 ≤ 2 ^ W := calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right Nat.two_pos hW
    exact show 3 < 2 ^ W by omega
  have h1 : Fits W 1 := Fits.of_le h3 (by omega)
  have hW3 : Fits W (W - 3) := Fits.of_le (fits_self W) (Nat.sub_le W 3)
  have hpow : Fits W (1 <<< (W - 3)) := by
    rw [Nat.shiftLeft_eq, one_mul]
    exact Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
  refine ⟨_, (ExecWithin.width.seq ((ExecWithin.const h3).seq
    ((ExecWithin.bin (by simpa using hW3)).seq ((ExecWithin.const h1).seq
      (ExecWithin.bin (by simpa using hpow)))))).mono (by omega), ?_, rfl⟩
  simp [Nat.shiftLeft_eq]

private def natLog2Body : Code .standard 5 :=
  let r1 : Fin 5 := 1
  let r2 : Fin 5 := 2
  let r3 : Fin 5 := 3
  ram[ r1 ← r1 + r3; r2 ← r2 >>> r3 ]

private def natLog2Pre : Code .standard 5 :=
  let r0 : Fin 5 := 0
  let r1 : Fin 5 := 1
  let r2 : Fin 5 := 2
  let r3 : Fin 5 := 3
  let r4 : Fin 5 := 4
  ram[ r4 ← #0; r3 ← #1; r1 ← #0; r2 ← r0 >>> r3 ]

/-- Compute `Nat.log 2 (x.regs 0)` into register `1` in `≤ 4 * Nat.log 2 v + 6` instructions,
preserving register `0` and all of memory. -/
def natLog2Code : Code .standard 5 :=
  .seq natLog2Pre (.loop (.lt 4 2) natLog2Body)

/-- `natLog2Code` does not read word width. -/
theorem not_readsWidth_natLog2Code : ¬natLog2Code.ReadsWidth := by
  simp [natLog2Code, natLog2Pre, natLog2Body, Code.ReadsWidth, Op.ReadsWidth, Op.bin]

/-- `natLog2Code` is `rand`-free. -/
theorem isRandFree_natLog2Code : natLog2Code.IsRandFree := by
  simp [natLog2Code, natLog2Pre, natLog2Body, Code.IsRandFree]

private theorem natLog2_step {v : ℕ} (hv : 1 ≤ v) :
    (if v / 2 = 0 then 0 else Nat.log 2 (v / 2) + 1) + 1 = Nat.log 2 v + 1 := by
  by_cases h2 : v < 2
  · have : v = 1 := by omega
    subst this; simp
  · have hge : 2 ≤ v := by omega
    have hpos : v / 2 ≠ 0 := by omega
    simp only [hpos, ↓reduceIte]
    rw [Nat.log_of_one_lt_of_le Nat.one_lt_two hge]

/-- Specification of `natLog2Code`. -/
theorem natLog2Code_exec {W : ℕ} (hW : 1 ≤ W) {x : Data 5} (hv : Fits W (x.regs 0)) :
    ∃ y : Data 5, ExecWithin W natLog2Code x y (4 * Nat.log 2 (x.regs 0) + 6) ∧
      y.regs 1 = Nat.log 2 (x.regs 0) ∧ y.regs 0 = x.regs 0 ∧ y.mem = x.mem := by
  set v := x.regs 0
  have h1 : Fits W 1 := fits_one (by omega)
  have hdiv : Fits W (v >>> 1) :=
    Fits.of_le hv (by rw [Nat.shiftRight_eq_div_pow, pow_one]; exact Nat.div_le_self v 2)
  let x1 := x.set 4 0
  let x2 := x1.set 3 1
  let x3 := x2.set 1 0
  let x4 := x3.set 2 (v >>> 1)
  have hpre : ExecWithin W natLog2Pre x x4 4 :=
    (ExecWithin.const (fits_zero W)).seq ((ExecWithin.const h1).seq
      ((ExecWithin.const (fits_zero W)).seq (ExecWithin.bin (by simpa [x3, x2, x1] using hdiv))))
  let I (y : Data 5) : Prop :=
    y.regs 0 = v ∧ y.regs 3 = 1 ∧ y.regs 4 = 0 ∧ y.mem = x.mem ∧ Fits W (y.regs 2) ∧
      y.regs 1 + (if y.regs 2 = 0 then 0 else Nat.log 2 (y.regs 2) + 1) = Nat.log 2 v
  let μ (y : Data 5) : ℕ := if y.regs 2 = 0 then 0 else Nat.log 2 (y.regs 2) + 1
  have hI4 : I x4 := by
    refine ⟨by simp [x4, x3, x2, x1, v], by simp [x4, x3, x2], by simp [x4, x3, x2, x1], rfl,
      by simpa [x4] using hdiv, ?_⟩
    simp only [x4, x3, Data.set_regs, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 5) ≠ 2),
      Nat.zero_add, Nat.shiftRight_eq_div_pow, pow_one]
    by_cases hv2 : v < 2
    · have : v / 2 = 0 := by omega
      simp only [this, ↓reduceIte]
      have : v = 0 ∨ v = 1 := by omega
      rcases this with hv' | hv' <;> simp [hv']
    · have hge : 2 ≤ v := by omega
      have hne : v / 2 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      exact (Nat.log_of_one_lt_of_le Nat.one_lt_two hge).symm
  have hμ4 : μ x4 = Nat.log 2 v := by
    have := hI4.2.2.2.2.2
    simp only [x4, x3, Data.set_regs, Function.update_of_ne (by decide : (1 : Fin 5) ≠ 2),
      Function.update_self, Nat.zero_add] at this
    simpa [μ, x4] using this
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant (w := W)
    (cond := .lt 4 2) (body := natLog2Body) I μ (fun s hs hc => by
      obtain ⟨hs0, hs3, hs4, hsm, hs2, hseq⟩ := hs
      have hpos : 1 ≤ s.regs 2 := by simp [Cond.Holds, hs4] at hc; omega
      have hs1_le : s.regs 1 + 1 ≤ Nat.log 2 v := by
        have : s.regs 2 ≠ 0 := by omega
        simp only [this, ↓reduceIte] at hseq
        omega
      have hs1_fits : Fits W (s.regs 1 + s.regs 3) := by
        rw [hs3]
        exact Fits.of_le hv (hs1_le.trans (Nat.log_le_self 2 v))
      let s1 := s.set 1 (s.regs 1 + s.regs 3)
      have hs2_fits : Fits W (s1.regs 2 >>> s1.regs 3) := by
        have h2e : s1.regs 2 = s.regs 2 := by simp [s1]
        have h3e : s1.regs 3 = 1 := by simp [s1, hs3]
        rw [h2e, h3e, Nat.shiftRight_eq_div_pow, pow_one]
        exact Fits.of_le hs2 (Nat.div_le_self _ 2)
      let s2 := s1.set 2 (s1.regs 2 >>> s1.regs 3)
      refine ⟨s2, (ExecWithin.bin hs1_fits).seq (ExecWithin.bin hs2_fits), ?_, ?_⟩
      · refine ⟨by simp [s2, s1, hs0], by simp [s2, s1, hs3], by simp [s2, s1, hs4], hsm,
          by simpa [s2] using hs2_fits, ?_⟩
        have hstep := natLog2_step hpos
        simp only [s2, s1, Data.set_regs, Function.update_self,
          Function.update_of_ne (by decide : (1 : Fin 5) ≠ 2),
          Function.update_of_ne (by decide : (2 : Fin 5) ≠ 1),
          Function.update_of_ne (by decide : (3 : Fin 5) ≠ 1), hs3,
          Nat.shiftRight_eq_div_pow, pow_one]
        have hne : s.regs 2 ≠ 0 := by omega
        simp only [hne, ↓reduceIte] at hseq
        omega
      · simp only [μ, s2, s1, Data.set_regs, Function.update_self,
          Function.update_of_ne (by decide : (2 : Fin 5) ≠ 1),
          Function.update_of_ne (by decide : (3 : Fin 5) ≠ 1), hs3,
          Nat.shiftRight_eq_div_pow, pow_one]
        have hne : s.regs 2 ≠ 0 := by omega
        simp only [hne, ↓reduceIte]
        have hstep := natLog2_step hpos
        omega) hI4
  have hy2 : y.regs 2 = 0 := by
    simp only [Cond.Holds, hIy.2.2.1] at hstop; omega
  have hy1 : y.regs 1 = Nat.log 2 v := by
    simpa only [hy2, ↓reduceIte, Nat.add_zero] using hIy.2.2.2.2.2
  refine ⟨y, (hpre.seq hy).mono (by rw [hμ4]; omega), hy1, hIy.1, hIy.2.2.2.1⟩

private def copyInitPre : Code .standard 9 :=
  let r1 : Fin 9 := 1
  let r2 : Fin 9 := 2
  let r3 : Fin 9 := 3
  let r4 : Fin 9 := 4
  let r5 : Fin 9 := 5
  let r6 : Fin 9 := 6
  ram[ r5 ← #1; *r2 ← r3; r6 ← r2 + r5; *r6 ← r1; r4 ← #0 ]

private def copyInitBody : Code .standard 9 :=
  let r0 : Fin 9 := 0
  let r2 : Fin 9 := 2
  let r3 : Fin 9 := 3
  let r4 : Fin 9 := 4
  let r5 : Fin 9 := 5
  let r6 : Fin 9 := 6
  let r7 : Fin 9 := 7
  let r8 : Fin 9 := 8
  ram[
    r6 ← r0 + r4;
    r7 ← *r6;
    r8 ← r4 + r5;
    r6 ← r8 + r8;
    r6 ← r2 + r6;
    *r6 ← r3;
    r6 ← r6 + r5;
    *r6 ← r7;
    r4 ← r4 + r5
  ]

/-- Copy `mem[qBase .. qBase + qLen)` into generation-stamped bank `[base, base + 2 * H)` as
`Data.init q` at generation `gen`. Regs: `0=qBase, 1=qLen, 2=base, 3=gen`. -/
def copyInitToStampedCode : Code .standard 9 :=
  .seq copyInitPre (.loop (.lt 4 1) copyInitBody)

/-- `copyInitToStampedCode` does not read word width. -/
theorem not_readsWidth_copyInitToStampedCode : ¬copyInitToStampedCode.ReadsWidth := by
  simp [copyInitToStampedCode, copyInitPre, copyInitBody, Code.ReadsWidth, Op.ReadsWidth, Op.bin]

/-- `copyInitToStampedCode` is `rand`-free. -/
theorem isRandFree_copyInitToStampedCode : copyInitToStampedCode.IsRandFree := by
  simp [copyInitToStampedCode, copyInitPre, copyInitBody, Code.IsRandFree]

/-- Specification of `copyInitToStampedCode`. -/
theorem copyInitToStampedCode_exec {W base H gen₀ gen : ℕ} {x : Data 9}
    (hgen : gen₀ < gen) (hlen : x.regs 1 < H) (hsrc : x.regs 0 + x.regs 1 ≤ base)
    (hbase : base + 2 * H ≤ 2 ^ W) (hB : x.regs 2 = base) (hG : x.regs 3 = gen)
    (hst : StampLe base H gen₀ x.mem) :
    let q := (List.range (x.regs 1)).map fun i => x.mem (x.regs 0 + i)
    ∃ y : Data 9,
      ExecWithin W copyInitToStampedCode x y (11 * x.regs 1 + 7) ∧
      MemRepresents base H gen y.mem (Data.init q (r := 1)).mem ∧
      StampLe base H gen y.mem ∧
      ∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → y.mem p = x.mem p := by
  set qBase := x.regs 0
  set qLen := x.regs 1
  set q := (List.range qLen).map fun i => x.mem (qBase + i)
  have h1_fits : Fits W 1 := show 1 < 2 ^ W by omega
  have hb1_fits : Fits W (base + 1) := show base + 1 < 2 ^ W by omega
  obtain ⟨hrep0, hst0⟩ := stampLe_reset hst hgen
  let x1 := x.set 5 1
  let x2 := x1.write base gen
  let x3 := x2.set 6 (base + 1)
  let x4 := x3.write (base + 1) qLen
  let x5 := x4.set 4 0
  have hx5_pre : ExecWithin W copyInitPre x x5 5 := by
    have s1 : ExecWithin W (.op (Op.const (B := .standard) 5 1)) x x1 1 :=
      ExecWithin.const h1_fits
    have s2 : ExecWithin W (.op (Op.store (B := .standard) 2 3)) x1 x2 1 := by
      simpa [x2, x1, hB, hG] using ExecWithin.store (w := W) (x := x1) (a := 2) (s := 3)
    have s3 : ExecWithin W (.op (.bin .add 6 2 5)) x2 x3 1 := by
      simpa [x3, x2, x1, hB] using ExecWithin.bin (w := W) (x := x2) (f := .add) (d := 6) (i := 2)
        (j := 5) (by simpa [x2, x1, hB] using hb1_fits)
    have s4 : ExecWithin W (.op (Op.store (B := .standard) 6 1)) x3 x4 1 := by
      simpa [x4, x3, x2, x1, qLen] using ExecWithin.store (w := W) (x := x3) (a := 6) (s := 1)
    have s5 : ExecWithin W (.op (Op.const (B := .standard) 4 0)) x4 x5 1 :=
      ExecWithin.const (fits_zero W)
    exact s1.seq (s2.seq (s3.seq (s4.seq s5)))
  let P (k : ℕ) (s : Data 9) : Prop :=
    s.regs 0 = qBase ∧ s.regs 1 = qLen ∧ s.regs 2 = base ∧ s.regs 3 = gen ∧ s.regs 5 = 1 ∧
      MemRepresents base H gen s.mem (fun a =>
        if a = 0 then qLen else if a - 1 < k then x.mem (qBase + (a - 1)) else 0) ∧
      StampLe base H gen s.mem ∧
      ∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → s.mem p = x.mem p
  have hP0 : P 0 x5 := by
    have ⟨hr, hs, hf⟩ := stampedWrite_memRepresents (a := 0) (v := qLen) (by omega) hrep0 hst0
    refine ⟨by simp [x5, x4, x3, x2, x1, qBase], by simp [x5, x4, x3, x2, x1, qLen],
      by simp [x5, x4, x3, x2, x1, hB], by simp [x5, x4, x3, x2, x1, hG],
      by simp [x5, x4, x3, x2, x1], fun a ha => ?_,
      by simpa [x5, x4, x3, x2, x1, Nat.mul_zero, Nat.add_zero] using hs,
      fun p hp => by simpa [x5, x4, x3, x2, x1, Nat.mul_zero, Nat.add_zero] using hf p hp⟩
    have := hr a ha
    simp only [x5, x4, x3, x2, x1, Data.set_mem, Data.write_mem, Nat.mul_zero,
      Nat.add_zero] at this ⊢
    rw [this]
    by_cases ha0 : a = 0 <;> simp [ha0]
  obtain ⟨y, hy, hPy, _⟩ := ExecWithin.loop_count (w := W) (N := qLen) (T := 9)
    (index := 4) (limit := 1) P (fun s hs => hs.2.1) (fun s hs hlt => by
      obtain ⟨hs0, hs1, hs2, hs3, hs5, hsrep, hsst, hsfr⟩ := hs
      set i := s.regs 4
      have hf1 : Fits W (s.regs 0 + s.regs 4) := by rw [hs0]; exact show qBase + i < 2 ^ W by omega
      let s1 := s.set 6 (qBase + i)
      let s2 := s1.set 7 (s1.mem (qBase + i))
      have hval : s1.mem (qBase + i) = x.mem (qBase + i) := hsfr (qBase + i) (by omega)
      have hf3 : Fits W (s2.regs 4 + s2.regs 5) := by
        simp only [s2, s1, Data.set_regs, Function.update_of_ne (by decide : (4 : Fin 9) ≠ 7),
          Function.update_of_ne (by decide : (4 : Fin 9) ≠ 6),
          Function.update_of_ne (by decide : (5 : Fin 9) ≠ 7),
          Function.update_of_ne (by decide : (5 : Fin 9) ≠ 6), hs5]
        exact show i + 1 < 2 ^ W by omega
      let s3 := s2.set 8 (i + 1)
      have hf4 : Fits W (s3.regs 8 + s3.regs 8) := by
        simp only [s3, Data.set_regs, Function.update_self]
        exact show (i + 1) + (i + 1) < 2 ^ W by omega
      let s4 := s3.set 6 (2 * (i + 1))
      have hf5 : Fits W (s4.regs 2 + s4.regs 6) := by
        simp only [s4, s3, s2, s1, Data.set_regs, Function.update_self,
          Function.update_of_ne (by decide : (2 : Fin 9) ≠ 6),
          Function.update_of_ne (by decide : (2 : Fin 9) ≠ 8),
          Function.update_of_ne (by decide : (2 : Fin 9) ≠ 7), hs2]
        exact show base + 2 * (i + 1) < 2 ^ W by omega
      let s5 := s4.set 6 (base + 2 * (i + 1))
      let s6 := s5.write (base + 2 * (i + 1)) gen
      have hf7 : Fits W (s6.regs 6 + s6.regs 5) := by
        simp only [s6, s5, s4, s3, s2, s1, Data.write_regs, Data.set_regs, Function.update_self,
          Function.update_of_ne (by decide : (5 : Fin 9) ≠ 6),
          Function.update_of_ne (by decide : (5 : Fin 9) ≠ 8),
          Function.update_of_ne (by decide : (5 : Fin 9) ≠ 7), hs5]
        exact show base + 2 * (i + 1) + 1 < 2 ^ W by omega
      let s7 := s6.set 6 (base + 2 * (i + 1) + 1)
      let s8 := s7.write (base + 2 * (i + 1) + 1) (x.mem (qBase + i))
      let s9 := s8.set 4 (i + 1)
      have hbody : ExecWithin W copyInitBody s s9 9 := by
        have e1 : ExecWithin W (.op (.bin .add 6 0 4)) s s1 1 := by
          simpa [s1, hs0] using ExecWithin.bin (w := W) (x := s) (f := .add) (d := 6) (i := 0)
            (j := 4) hf1
        have e2 : ExecWithin W (.op (Op.load (B := .standard) 7 6)) s1 s2 1 := by
          simpa [s2, s1] using ExecWithin.load (w := W) (x := s1) (d := 7) (a := 6)
        have e3 : ExecWithin W (.op (.bin .add 8 4 5)) s2 s3 1 := by
          simpa [s3, s2, s1, hs5] using ExecWithin.bin (w := W) (x := s2) (f := .add) (d := 8)
            (i := 4) (j := 5) hf3
        have e4 : ExecWithin W (.op (.bin .add 6 8 8)) s3 s4 1 := by
          have : (i + 1) + (i + 1) = 2 * (i + 1) := by omega
          simpa [s4, s3, this] using ExecWithin.bin (w := W) (x := s3) (f := .add) (d := 6)
            (i := 8) (j := 8) hf4
        have e5 : ExecWithin W (.op (.bin .add 6 2 6)) s4 s5 1 := by
          simpa [s5, s4, s3, s2, s1, hs2] using ExecWithin.bin (w := W) (x := s4) (f := .add)
            (d := 6) (i := 2) (j := 6) hf5
        have e6 : ExecWithin W (.op (Op.store (B := .standard) 6 3)) s5 s6 1 := by
          simpa [s6, s5, s4, s3, s2, s1, hs3] using ExecWithin.store (w := W) (x := s5) (a := 6)
            (s := 3)
        have e7 : ExecWithin W (.op (.bin .add 6 6 5)) s6 s7 1 := by
          simpa [s7, s6, s5, s4, s3, s2, s1, hs5] using ExecWithin.bin (w := W) (x := s6) (f :=
            .add)
            (d := 6) (i := 6) (j := 5) hf7
        have e8 : ExecWithin W (.op (Op.store (B := .standard) 6 7)) s7 s8 1 := by
          simpa [s8, s7, s6, s5, s4, s3, s2, hval] using ExecWithin.store (w := W) (x := s7)
            (a := 6) (s := 7)
        have e9 : ExecWithin W (.op (.bin .add 4 4 5)) s8 s9 1 := by
          have hf9 : Fits W (s8.regs 4 + s8.regs 5) := by simpa [s8, s7, s6, s5, s4, s3] using hf3
          simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs5] using ExecWithin.bin (w := W) (x := s8)
            (f := .add) (d := 4) (i := 4) (j := 5) hf9
        exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))
      obtain ⟨hrep', hst', hfr'⟩ :=
        stampedWrite_memRepresents (a := i + 1) (v := x.mem (qBase + i)) (by omega) hsrep hsst
      refine ⟨s9, hbody, ⟨by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs0],
        by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs1],
        by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs2],
        by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs3],
        by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs5],
        fun a ha => ?_, ?_, fun p hp => ?_⟩, by simp [s9]⟩
      · have hm : s9.mem = Function.update (Function.update s.mem (base + 2 * (i + 1)) gen)
            (base + 2 * (i + 1) + 1) (x.mem (qBase + i)) := by
          simp [s9, s8, s7, s6, s5, s4, s3, s2, s1]
        rw [hm, hrep' a ha]
        by_cases ha0 : a = 0
        · subst ha0; simp
        · by_cases hai : a = i + 1
          · subst hai; simp
          · simp only [Function.update_of_ne hai, ha0, ↓reduceIte]
            by_cases hlt' : a - 1 < i
            · have : a - 1 < i + 1 := by omega
              simp [hlt', this]
            · have : ¬(a - 1 < i + 1) := by omega
              simp [hlt', this]
      · simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1] using hst'
      · have hm : s9.mem = Function.update (Function.update s.mem (base + 2 * (i + 1)) gen)
            (base + 2 * (i + 1) + 1) (x.mem (qBase + i)) := by
          simp [s9, s8, s7, s6, s5, s4, s3, s2, s1]
        rw [hm]; exact (hfr' p hp).trans (hsfr p hp)) (by simp [x5]) hP0
  refine ⟨y, (hx5_pre.seq hy).mono (by simp [x5]; omega), ?_, hPy.2.2.2.2.2.2.1, hPy.2.2.2.2.2.2.2⟩
  intro a ha
  rw [hPy.2.2.2.2.2.1 a ha]
  rcases a with _ | a
  · simp [q]
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
      Data.init_mem_succ, q, List.getD_eq_getElem?_getD]
    by_cases hlt : a < qLen <;> simp [hlt]

private def unpackBitsPre : Code .standard 9 :=
  let r0 : Fin 9 := 0
  let r2 : Fin 9 := 2
  let r3 : Fin 9 := 3
  let r4 : Fin 9 := 4
  let r5 : Fin 9 := 5
  let r6 : Fin 9 := 6
  ram[ r5 ← #1; *r2 ← r3; r6 ← r2 + r5; *r6 ← r0; r4 ← #0 ]

private def unpackBitsBody : Code .standard 9 :=
  let r1 : Fin 9 := 1
  let r2 : Fin 9 := 2
  let r3 : Fin 9 := 3
  let r4 : Fin 9 := 4
  let r5 : Fin 9 := 5
  let r6 : Fin 9 := 6
  let r7 : Fin 9 := 7
  let r8 : Fin 9 := 8
  ram[
    r7 ← r1 >>> r4;
    r7 ← r7 &&& r5;
    r8 ← r4 + r5;
    r6 ← r8 + r8;
    r6 ← r2 + r6;
    *r6 ← r3;
    r6 ← r6 + r5;
    *r6 ← r7;
    r4 ← r4 + r5
  ]

/-- Unpack `(len, mask)` into generation-stamped bank `[base, base + 2 * H)` as
`Data.init ((bitsOfMaskBool len mask).map Bool.toNat)` at generation `gen`.
Regs: `0=len, 1=mask, 2=base, 3=gen`. -/
def unpackBitsToStampedCode : Code .standard 9 :=
  .seq unpackBitsPre (.loop (.lt 4 0) unpackBitsBody)

/-- `unpackBitsToStampedCode` does not read word width. -/
theorem not_readsWidth_unpackBitsToStampedCode : ¬unpackBitsToStampedCode.ReadsWidth := by
  simp [unpackBitsToStampedCode, unpackBitsPre, unpackBitsBody, Code.ReadsWidth,
    Op.ReadsWidth, Op.bin]

/-- `unpackBitsToStampedCode` is `rand`-free. -/
theorem isRandFree_unpackBitsToStampedCode : unpackBitsToStampedCode.IsRandFree := by
  simp [unpackBitsToStampedCode, unpackBitsPre, unpackBitsBody, Code.IsRandFree]

/-- Specification of `unpackBitsToStampedCode`. -/
theorem unpackBitsToStampedCode_exec {W base H gen₀ gen : ℕ} {x : Data 9}
    (hgen : gen₀ < gen) (hlen : x.regs 0 < H) (hmask : Fits W (x.regs 1))
    (hbase : base + 2 * H ≤ 2 ^ W) (hB : x.regs 2 = base) (hG : x.regs 3 = gen)
    (hst : StampLe base H gen₀ x.mem) :
    let q := (bitsOfMaskBool (x.regs 0) (x.regs 1)).map Bool.toNat
    ∃ y : Data 9,
      ExecWithin W unpackBitsToStampedCode x y (11 * x.regs 0 + 7) ∧
      MemRepresents base H gen y.mem (Data.init q (r := 1)).mem ∧
      StampLe base H gen y.mem ∧
      ∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → y.mem p = x.mem p := by
  set len := x.regs 0
  set mask := x.regs 1
  set q := (bitsOfMaskBool len mask).map Bool.toNat
  have h1_fits : Fits W 1 := show 1 < 2 ^ W by omega
  have hb1_fits : Fits W (base + 1) := show base + 1 < 2 ^ W by omega
  obtain ⟨hrep0, hst0⟩ := stampLe_reset hst hgen
  let x1 := x.set 5 1
  let x2 := x1.write base gen
  let x3 := x2.set 6 (base + 1)
  let x4 := x3.write (base + 1) len
  let x5 := x4.set 4 0
  have hx5_pre : ExecWithin W unpackBitsPre x x5 5 := by
    have s1 : ExecWithin W (.op (Op.const (B := .standard) 5 1)) x x1 1 :=
      ExecWithin.const h1_fits
    have s2 : ExecWithin W (.op (Op.store (B := .standard) 2 3)) x1 x2 1 := by
      simpa [x2, x1, hB, hG] using ExecWithin.store (w := W) (x := x1) (a := 2) (s := 3)
    have s3 : ExecWithin W (.op (.bin .add 6 2 5)) x2 x3 1 := by
      simpa [x3, x2, x1, hB] using ExecWithin.bin (w := W) (x := x2) (f := .add) (d := 6) (i := 2)
        (j := 5) (by simpa [x2, x1, hB] using hb1_fits)
    have s4 : ExecWithin W (.op (Op.store (B := .standard) 6 0)) x3 x4 1 := by
      simpa [x4, x3, x2, x1, len] using ExecWithin.store (w := W) (x := x3) (a := 6) (s := 0)
    have s5 : ExecWithin W (.op (Op.const (B := .standard) 4 0)) x4 x5 1 :=
      ExecWithin.const (fits_zero W)
    exact s1.seq (s2.seq (s3.seq (s4.seq s5)))
  let bitOf (i : ℕ) : ℕ := (mask >>> i) &&& 1
  let P (k : ℕ) (s : Data 9) : Prop :=
    s.regs 0 = len ∧ s.regs 1 = mask ∧ s.regs 2 = base ∧ s.regs 3 = gen ∧ s.regs 5 = 1 ∧
      MemRepresents base H gen s.mem (fun a =>
        if a = 0 then len else if a - 1 < k then bitOf (a - 1) else 0) ∧
      StampLe base H gen s.mem ∧
      ∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → s.mem p = x.mem p
  have hP0 : P 0 x5 := by
    have ⟨hr, hs, hf⟩ := stampedWrite_memRepresents (a := 0) (v := len) (by omega) hrep0 hst0
    refine ⟨by simp [x5, x4, x3, x2, x1, len], by simp [x5, x4, x3, x2, x1, mask],
      by simp [x5, x4, x3, x2, x1, hB], by simp [x5, x4, x3, x2, x1, hG],
      by simp [x5, x4, x3, x2, x1], fun a ha => ?_,
      by simpa [x5, x4, x3, x2, x1, Nat.mul_zero, Nat.add_zero] using hs,
      fun p hp => by simpa [x5, x4, x3, x2, x1, Nat.mul_zero, Nat.add_zero] using hf p hp⟩
    have := hr a ha
    simp only [x5, x4, x3, x2, x1, Data.set_mem, Data.write_mem, Nat.mul_zero,
      Nat.add_zero] at this ⊢
    rw [this]
    by_cases ha0 : a = 0 <;> simp [ha0]
  obtain ⟨y, hy, hPy, _⟩ := ExecWithin.loop_count (w := W) (N := len) (T := 9)
    (index := 4) (limit := 0) P (fun s hs => hs.1) (fun s hs hlt => by
      obtain ⟨hs0, hs1, hs2, hs3, hs5, hsrep, hsst, hsfr⟩ := hs
      set i := s.regs 4
      have hf1 : Fits W (s.regs 1 >>> s.regs 4) := by
        rw [hs1, Nat.shiftRight_eq_div_pow]
        exact Fits.of_le hmask (Nat.div_le_self _ _)
      let s1 := s.set 7 (mask >>> i)
      have hf2 : Fits W (s1.regs 7 &&& s1.regs 5) := by
        have h5 : s1.regs 5 = 1 := by simp [s1, hs5]
        have h7 : s1.regs 7 = mask >>> i := by simp [s1]
        rw [h5, h7, Nat.and_one_is_mod]
        exact Fits.of_le h1_fits (by omega)
      let s2 := s1.set 7 (bitOf i)
      have hf3 : Fits W (s2.regs 4 + s2.regs 5) := by
        simp only [s2, s1, Data.set_regs, Function.update_of_ne (by decide : (4 : Fin 9) ≠ 7),
          Function.update_of_ne (by decide : (5 : Fin 9) ≠ 7), hs5]
        exact show i + 1 < 2 ^ W by omega
      let s3 := s2.set 8 (i + 1)
      have hf4 : Fits W (s3.regs 8 + s3.regs 8) := by
        simp only [s3, Data.set_regs, Function.update_self]
        exact show (i + 1) + (i + 1) < 2 ^ W by omega
      let s4 := s3.set 6 (2 * (i + 1))
      have hf5 : Fits W (s4.regs 2 + s4.regs 6) := by
        simp only [s4, s3, s2, s1, Data.set_regs, Function.update_self,
          Function.update_of_ne (by decide : (2 : Fin 9) ≠ 6),
          Function.update_of_ne (by decide : (2 : Fin 9) ≠ 8),
          Function.update_of_ne (by decide : (2 : Fin 9) ≠ 7), hs2]
        exact show base + 2 * (i + 1) < 2 ^ W by omega
      let s5 := s4.set 6 (base + 2 * (i + 1))
      let s6 := s5.write (base + 2 * (i + 1)) gen
      have hf7 : Fits W (s6.regs 6 + s6.regs 5) := by
        simp only [s6, s5, s4, s3, s2, s1, Data.write_regs, Data.set_regs, Function.update_self,
          Function.update_of_ne (by decide : (5 : Fin 9) ≠ 6),
          Function.update_of_ne (by decide : (5 : Fin 9) ≠ 8),
          Function.update_of_ne (by decide : (5 : Fin 9) ≠ 7), hs5]
        exact show base + 2 * (i + 1) + 1 < 2 ^ W by omega
      let s7 := s6.set 6 (base + 2 * (i + 1) + 1)
      let s8 := s7.write (base + 2 * (i + 1) + 1) (bitOf i)
      let s9 := s8.set 4 (i + 1)
      have hbody : ExecWithin W unpackBitsBody s s9 9 := by
        have e1 : ExecWithin W (.op (.bin .shiftRight 7 1 4)) s s1 1 := by
          simpa [s1, hs1] using ExecWithin.bin (w := W) (x := s) (f := .shiftRight) (d := 7)
            (i := 1) (j := 4) hf1
        have e2 : ExecWithin W (.op (.bin .and 7 7 5)) s1 s2 1 := by
          simpa [s2, s1, hs5, bitOf] using ExecWithin.bin (w := W) (x := s1) (f := .and) (d := 7)
            (i := 7) (j := 5) hf2
        have e3 : ExecWithin W (.op (.bin .add 8 4 5)) s2 s3 1 := by
          simpa [s3, s2, s1, hs5] using ExecWithin.bin (w := W) (x := s2) (f := .add) (d := 8)
            (i := 4) (j := 5) hf3
        have e4 : ExecWithin W (.op (.bin .add 6 8 8)) s3 s4 1 := by
          have : (i + 1) + (i + 1) = 2 * (i + 1) := by omega
          simpa [s4, s3, this] using ExecWithin.bin (w := W) (x := s3) (f := .add) (d := 6)
            (i := 8) (j := 8) hf4
        have e5 : ExecWithin W (.op (.bin .add 6 2 6)) s4 s5 1 := by
          simpa [s5, s4, s3, s2, s1, hs2] using ExecWithin.bin (w := W) (x := s4) (f := .add)
            (d := 6) (i := 2) (j := 6) hf5
        have e6 : ExecWithin W (.op (Op.store (B := .standard) 6 3)) s5 s6 1 := by
          simpa [s6, s5, s4, s3, s2, s1, hs3] using ExecWithin.store (w := W) (x := s5) (a := 6)
            (s := 3)
        have e7 : ExecWithin W (.op (.bin .add 6 6 5)) s6 s7 1 := by
          simpa [s7, s6, s5, s4, s3, s2, s1, hs5] using ExecWithin.bin (w := W) (x := s6) (f :=
            .add)
            (d := 6) (i := 6) (j := 5) hf7
        have e8 : ExecWithin W (.op (Op.store (B := .standard) 6 7)) s7 s8 1 := by
          simpa [s8, s7, s6, s5, s4, s3, s2] using ExecWithin.store (w := W) (x := s7) (a := 6)
            (s := 7)
        have e9 : ExecWithin W (.op (.bin .add 4 4 5)) s8 s9 1 := by
          have hf9 : Fits W (s8.regs 4 + s8.regs 5) := by simpa [s8, s7, s6, s5, s4, s3] using hf3
          simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs5] using ExecWithin.bin (w := W) (x := s8)
            (f := .add) (d := 4) (i := 4) (j := 5) hf9
        exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))
      obtain ⟨hrep', hst', hfr'⟩ :=
        stampedWrite_memRepresents (a := i + 1) (v := bitOf i) (by omega) hsrep hsst
      refine ⟨s9, hbody, ⟨by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs0],
        by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs1],
        by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs2],
        by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs3],
        by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hs5],
        fun a ha => ?_, ?_, fun p hp => ?_⟩, by simp [s9]⟩
      · have hm : s9.mem = Function.update (Function.update s.mem (base + 2 * (i + 1)) gen)
            (base + 2 * (i + 1) + 1) (bitOf i) := by
          simp [s9, s8, s7, s6, s5, s4, s3, s2, s1]
        rw [hm, hrep' a ha]
        by_cases ha0 : a = 0
        · subst ha0; simp
        · by_cases hai : a = i + 1
          · subst hai; simp
          · simp only [Function.update_of_ne hai, ha0, ↓reduceIte]
            by_cases hlt' : a - 1 < i
            · have : a - 1 < i + 1 := by omega
              simp [hlt', this]
            · have : ¬(a - 1 < i + 1) := by omega
              simp [hlt', this]
      · simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1] using hst'
      · have hm : s9.mem = Function.update (Function.update s.mem (base + 2 * (i + 1)) gen)
            (base + 2 * (i + 1) + 1) (bitOf i) := by
          simp [s9, s8, s7, s6, s5, s4, s3, s2, s1]
        rw [hm]; exact (hfr' p hp).trans (hsfr p hp)) (by simp [x5]) hP0
  refine ⟨y, (hx5_pre.seq hy).mono (by simp [x5]; omega), ?_, hPy.2.2.2.2.2.2.1, hPy.2.2.2.2.2.2.2⟩
  intro a ha
  rw [hPy.2.2.2.2.2.1 a ha]
  rcases a with _ | a
  · simp [q, bitsOfMaskBool]
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
      Data.init_mem_succ, q, bitsOfMaskBool, List.getD_eq_getElem?_getD]
    by_cases hlt : a < len
    · simp only [List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some,
        hlt, ↓reduceIte, bitOf, Nat.and_one_is_mod]
      rcases Nat.mod_two_eq_zero_or_one (mask >>> a) with hm | hm <;> simp [hm]
    · simp [hlt]

private def bscPre : Code .standard 12 :=
  let r4 : Fin 12 := 4
  let r5 : Fin 12 := 5
  let r6 : Fin 12 := 6
  let r7 : Fin 12 := 7
  let r8 : Fin 12 := 8
  ram[ r5 ← #1; r8 ← #1; r6 ← #1; r7 ← #0; r4 ← #0 ]

private def bscReadAddr : Code .standard 12 :=
  let r0 : Fin 12 := 0
  let r2 : Fin 12 := 2
  let r4 : Fin 12 := 4
  let r9 : Fin 12 := 9
  let r10 : Fin 12 := 10
  let r11 : Fin 12 := 11
  ram[ r11 ← r0 + r4; r9 ← r11 + r11; r9 ← r2 + r9; r10 ← *r9 ]

private def bscReadBranch : Code .standard 12 :=
  let r3 : Fin 12 := 3
  let r5 : Fin 12 := 5
  let r9 : Fin 12 := 9
  let r10 : Fin 12 := 10
  ram[ if r10 = r3 then [ r9 ← r9 + r5; r10 ← *r9 ] else [ r10 ← #0 ] ]

private def bscAccBranch : Code .standard 12 :=
  let r5 : Fin 12 := 5
  let r6 : Fin 12 := 6
  let r7 : Fin 12 := 7
  let r8 : Fin 12 := 8
  let r10 : Fin 12 := 10
  ram[
    if r5 < r10 then [
      r8 ← #0
    ] else [
      if r10 = r5 then [
        r7 ← r7 + r6
      ] else [
        r7 ← r7
      ]
    ]
  ]

private def bscStep : Code .standard 12 :=
  let r4 : Fin 12 := 4
  let r5 : Fin 12 := 5
  let r6 : Fin 12 := 6
  ram[ r6 ← r6 + r6; r4 ← r4 + r5 ]

private def bscBody : Code .standard 12 :=
  .seq bscReadAddr (.seq bscReadBranch (.seq bscAccBranch bscStep))

/-- Compute `bitStringCode` (reg `7`) and validity `0`/`1` (reg `8`) of the stamped slice
`[qBase .. qBase + qLen)` inside bank `[base, base + 2 * H)` at generation `gen`, leaving all of
memory unchanged. Regs: `0=qBase, 1=qLen, 2=base, 3=gen`. -/
def bitStringCodeStamped : Code .standard 12 :=
  let r6 : Fin 12 := 6
  let r7 : Fin 12 := 7
  .seq bscPre (.seq (.loop (.lt 4 1) bscBody) (ram[ r7 ← r7 + r6 ]))

/-- `bitStringCodeStamped` does not read word width. -/
theorem not_readsWidth_bitStringCodeStamped : ¬bitStringCodeStamped.ReadsWidth := by
  simp [bitStringCodeStamped, bscPre, bscBody, bscReadAddr, bscReadBranch, bscAccBranch, bscStep,
    Code.ReadsWidth, Op.ReadsWidth, Op.bin]

/-- `bitStringCodeStamped` is `rand`-free. -/
theorem isRandFree_bitStringCodeStamped : bitStringCodeStamped.IsRandFree := by
  simp [bitStringCodeStamped, bscPre, bscBody, bscReadAddr, bscReadBranch, bscAccBranch, bscStep,
    Code.IsRandFree]

/-- Specification of `bitStringCodeStamped`: runs in `≤ 18 * qLen + 8` instructions without
modifying memory, sets `reg 8 = 1` iff all `qLen` words are `0`/`1`, and sets `reg 7` to
`bitStringCode` of the corresponding bitstring. -/
theorem bitStringCodeStamped_exec {W base H gen : ℕ} {x : Data 12}
    (hq : x.regs 0 + x.regs 1 ≤ H) (hpow : 2 ^ (x.regs 1 + 1) ≤ 2 ^ W)
    (hbase : base + 2 * H ≤ 2 ^ W) (hB : x.regs 2 = base) (hG : x.regs 3 = gen) :
    let qBase := x.regs 0
    let qLen := x.regs 1
    let z : List Bool := (List.range qLen).map fun i =>
      decide (stampedRead base gen x.mem (qBase + i) = 1)
    ∃ y : Data 12,
      ExecWithin W bitStringCodeStamped x y (18 * qLen + 8) ∧
      y.mem = x.mem ∧
      (y.regs 8 = 1 ↔ ∀ i < qLen, stampedRead base gen x.mem (qBase + i) ≤ 1) ∧
      y.regs 8 ≤ 1 ∧
      (y.regs 8 = 1 → y.regs 7 = bitStringCode z) := by
  set qBase := x.regs 0
  set qLen := x.regs 1
  have h1_fits : Fits W 1 := by
    have : 2 ≤ 2 ^ (qLen + 1) := by
      rw [pow_succ]; have := Nat.one_le_two_pow (n := qLen); omega
    exact show 1 < 2 ^ W by omega
  let x1 := x.set 5 1
  let x2 := x1.set 8 1
  let x3 := x2.set 6 1
  let x4 := x3.set 7 0
  let x5 := x4.set 4 0
  have hpre : ExecWithin W bscPre x x5 5 :=
    (ExecWithin.const h1_fits).seq ((ExecWithin.const h1_fits).seq
      ((ExecWithin.const h1_fits).seq ((ExecWithin.const (fits_zero W)).seq
        (ExecWithin.const (fits_zero W)))))
  let accOf (k : ℕ) : ℕ :=
    ((List.range k).map fun i =>
      (decide (stampedRead base gen x.mem (qBase + i) = 1)).toNat * 2 ^ i).sum
  let P (k : ℕ) (s : Data 12) : Prop :=
    s.regs 0 = qBase ∧ s.regs 1 = qLen ∧ s.regs 2 = base ∧ s.regs 3 = gen ∧ s.regs 5 = 1 ∧
      s.mem = x.mem ∧ s.regs 6 = 2 ^ k ∧ s.regs 7 < 2 ^ k ∧ s.regs 8 ≤ 1 ∧
      (s.regs 8 = 1 ↔ ∀ i < k, stampedRead base gen x.mem (qBase + i) ≤ 1) ∧
      (s.regs 8 = 1 → s.regs 7 = accOf k)
  have hP0 : P 0 x5 := ⟨by simp [x5, x4, x3, x2, x1, qBase], by simp [x5, x4, x3, x2, x1, qLen],
    by simp [x5, x4, x3, x2, x1, hB], by simp [x5, x4, x3, x2, x1, hG],
    by simp [x5, x4, x3, x2, x1], rfl, by simp [x5, x4, x3], by simp [x5, x4],
    by simp [x5, x4, x3, x2], by simp [x5, x4, x3, x2], fun _ => by simp [x5, x4, accOf]⟩
  obtain ⟨y0, hy0, hPy0, _⟩ := ExecWithin.loop_count (w := W) (N := qLen) (T := 16)
    (index := 4) (limit := 1) P (fun s hs => hs.2.1) (fun s hs hlt => by
      obtain ⟨hs0, hs1, hs2, hs3, hs5, hsm, hs6, hs7, hs8le, hs8iff, hs7eq⟩ := hs
      set i := s.regs 4
      have hpow_i : 2 ^ (i + 1) ≤ 2 ^ qLen := Nat.pow_le_pow_right Nat.two_pos (by omega)
      have hpow_W : 2 ^ (i + 1) < 2 ^ W := by
        have : 2 ^ (qLen + 1) = 2 ^ qLen * 2 := pow_succ 2 qLen
        have := Nat.one_le_two_pow (n := qLen)
        omega
      have hf1 : Fits W (s.regs 0 + s.regs 4) := by rw [hs0]; exact show qBase + i < 2 ^ W by omega
      let s1 := s.set 11 (qBase + i)
      have hf2 : Fits W (s1.regs 11 + s1.regs 11) := by
        simp only [s1, Data.set_regs, Function.update_self]
        exact show (qBase + i) + (qBase + i) < 2 ^ W by omega
      let s2 := s1.set 9 (2 * (qBase + i))
      have hf3 : Fits W (s2.regs 2 + s2.regs 9) := by
        simp only [s2, s1, Data.set_regs, Function.update_self,
          Function.update_of_ne (by decide : (2 : Fin 12) ≠ 9),
          Function.update_of_ne (by decide : (2 : Fin 12) ≠ 11), hs2]
        exact show base + 2 * (qBase + i) < 2 ^ W by omega
      let s3 := s2.set 9 (base + 2 * (qBase + i))
      let s4 := s3.set 10 (x.mem (base + 2 * (qBase + i)))
      have e1234 : ExecWithin W bscReadAddr s s4 4 := by
        have e1 : ExecWithin W (.op (.bin .add 11 0 4)) s s1 1 := by
          simpa [s1, hs0] using ExecWithin.bin (w := W) (x := s) (f := .add) (d := 11) (i := 0)
            (j := 4) hf1
        have e2 : ExecWithin W (.op (.bin .add 9 11 11)) s1 s2 1 := by
          have : (qBase + i) + (qBase + i) = 2 * (qBase + i) := by omega
          simpa [s2, s1, this] using ExecWithin.bin (w := W) (x := s1) (f := .add) (d := 9)
            (i := 11) (j := 11) hf2
        have e3 : ExecWithin W (.op (.bin .add 9 2 9)) s2 s3 1 := by
          simpa [s3, s2, s1, hs2] using ExecWithin.bin (w := W) (x := s2) (f := .add) (d := 9)
            (i := 2) (j := 9) hf3
        have e4 : ExecWithin W (.op (Op.load (B := .standard) 10 9)) s3 s4 1 := by
          simpa [s4, s3, s2, s1, hsm] using ExecWithin.load (w := W) (x := s3) (d := 10) (a := 9)
        exact e1.seq (e2.seq (e3.seq e4))
      let v := stampedRead base gen x.mem (qBase + i)
      have e5 : ∃ s5', ExecWithin W bscReadBranch s4 s5' 4 ∧
          s5'.regs 10 = v ∧
          (∀ j : Fin 12, j ≠ 9 → j ≠ 10 → s5'.regs j = s4.regs j) ∧ s5'.mem = x.mem := by
        by_cases hst_eq : x.mem (base + 2 * (qBase + i)) = gen
        · have hc : (Cond.eq 10 3).Holds s4 := by
            simp [Cond.Holds, s4, s3, s2, s1, hs3, hst_eq]
          have hf95 : Fits W (s4.regs 9 + s4.regs 5) := by
            simp only [s4, s3, s2, s1, Data.set_regs, Function.update_self,
              Function.update_of_ne (by decide : (9 : Fin 12) ≠ 10),
              Function.update_of_ne (by decide : (5 : Fin 12) ≠ 10),
              Function.update_of_ne (by decide : (5 : Fin 12) ≠ 9),
              Function.update_of_ne (by decide : (5 : Fin 12) ≠ 11), hs5]
            exact show base + 2 * (qBase + i) + 1 < 2 ^ W by omega
          let t1 := s4.set 9 (base + 2 * (qBase + i) + 1)
          let t2 := t1.set 10 (x.mem (base + 2 * (qBase + i) + 1))
          have eb : ExecWithin W (.seq (.op (.bin .add 9 9 5)) (.op (.load 10 9))) s4 t2 2 := by
            have ea : ExecWithin W (.op (.bin .add 9 9 5)) s4 t1 1 := by
              simpa [t1, s4, s3, s2, s1, hs5] using ExecWithin.bin (w := W) (x := s4) (f := .add)
                (d := 9) (i := 9) (j := 5) hf95
            have eb' : ExecWithin W (.op (Op.load (B := .standard) 10 9)) t1 t2 1 := by
              simpa [t2, t1, s4, s3, s2, s1, hsm] using ExecWithin.load (w := W) (x := t1)
                (d := 10) (a := 9)
            exact ea.seq eb'
          refine ⟨t2, (ExecWithin.branch_pos hc eb).mono (by omega), ?_,
            fun j hj9 hj10 => by simp [t2, t1, hj9, hj10], by simp [t2, t1, s4, s3, s2, s1, hsm]⟩
          simp only [t2, v, Data.set_regs, Function.update_self]
          exact (stampedRead_eq_of_eq hst_eq).symm
        · have hc : ¬(Cond.eq 10 3).Holds s4 := by
            simp [Cond.Holds, s4, s3, s2, s1, hs3, hst_eq]
          let t1 := s4.set 10 0
          refine ⟨t1, (ExecWithin.branch_neg hc (ExecWithin.const (fits_zero W))).mono (by omega),
            ?_, fun j _ hj10 => by simp [t1, hj10], by simp [t1, s4, s3, s2, s1, hsm]⟩
          simp only [t1, v, Data.set_regs, Function.update_self]
          exact (stampedRead_eq_zero_of_ne hst_eq).symm
      obtain ⟨s5', he5, hs5'_10, hs5'_fr, hs5'_mem⟩ := e5
      have hs5'_r : ∀ j : Fin 12, j ≠ 9 → j ≠ 10 → j ≠ 11 → s5'.regs j = s.regs j :=
        fun j h9 h10 h11 => by rw [hs5'_fr j h9 h10]; simp [s4, s3, s2, s1, h9, h10, h11]
      have e6 : ∃ s6', ExecWithin W bscAccBranch s5' s6' 5 ∧
          s6'.mem = x.mem ∧ s6'.regs 8 ≤ 1 ∧
          (s6'.regs 8 = 1 ↔ (s.regs 8 = 1 ∧ v ≤ 1)) ∧
          (s6'.regs 8 = 1 → s6'.regs 7 = s.regs 7 + (decide (v = 1)).toNat * 2 ^ i) ∧
          s6'.regs 7 < 2 ^ (i + 1) ∧
          (∀ j : Fin 12, j ≠ 7 → j ≠ 8 → s6'.regs j = s5'.regs j) := by
        by_cases hv1 : 1 < v
        · have hc : (Cond.lt 5 10).Holds s5' := by
            simpa [Cond.Holds, hs5'_10, hs5'_r 5 (by decide) (by decide) (by decide), hs5] using hv1
          let t1 := s5'.set 8 0
          refine ⟨t1, (ExecWithin.branch_pos hc (ExecWithin.const (fits_zero W))).mono (by omega),
            hs5'_mem, by simp [t1], ?_, ?_, ?_, fun j _ hj8 => by simp [t1, hj8]⟩
          · simp [t1]; omega
          · simp [t1]
          · rw [show t1.regs 7 = s.regs 7 by
              rw [show t1.regs 7 = s5'.regs 7 by simp [t1],
                hs5'_r 7 (by decide) (by decide) (by decide)]]
            rw [pow_succ]; omega
        · have hc : ¬(Cond.lt 5 10).Holds s5' := by
            simpa [Cond.Holds, hs5'_10, hs5'_r 5 (by decide) (by decide) (by decide), hs5] using hv1
          have hvle : v ≤ 1 := by omega
          by_cases hv_eq : v = 1
          · have hc2 : (Cond.eq 10 5).Holds s5' := by
              simp [Cond.Holds, hs5'_10, hs5'_r 5 (by decide) (by decide) (by decide), hs5, hv_eq]
            have hf76 : Fits W (s5'.regs 7 + s5'.regs 6) := by
              rw [hs5'_r 7 (by decide) (by decide) (by decide),
                hs5'_r 6 (by decide) (by decide) (by decide), hs6]
              rw [pow_succ] at hpow_W
              exact show s.regs 7 + 2 ^ i < 2 ^ W by omega
            let t1 := s5'.set 7 (s5'.regs 7 + s5'.regs 6)
            refine ⟨t1,
              (ExecWithin.branch_neg hc
                (ExecWithin.branch_pos hc2 (ExecWithin.bin hf76))).mono (by omega),
              hs5'_mem, ?_, ?_, ?_, ?_, fun j hj7 _ => by simp [t1, hj7]⟩
            · rw [show t1.regs 8 = s.regs 8 by
                simp [t1, hs5'_r 8 (by decide) (by decide) (by decide)]]
              exact hs8le
            · simp [t1, hs5'_r 8 (by decide) (by decide) (by decide), hvle]
            · intro _; simp [t1, hs5'_r 7 (by decide) (by decide) (by decide),
                hs5'_r 6 (by decide) (by decide) (by decide), hs6, hv_eq]
            · simp only [t1, Data.set_regs, Function.update_self,
                hs5'_r 7 (by decide) (by decide) (by decide),
                hs5'_r 6 (by decide) (by decide) (by decide), hs6, pow_succ]
              omega
          · have hc2 : ¬(Cond.eq 10 5).Holds s5' := by
              simp [Cond.Holds, hs5'_10, hs5'_r 5 (by decide) (by decide) (by decide), hs5, hv_eq]
            let t1 := s5'.set 7 (s5'.regs 7)
            refine ⟨t1,
              (ExecWithin.branch_neg hc
                (ExecWithin.branch_neg hc2 ExecWithin.copy)).mono (by omega),
              hs5'_mem, ?_, ?_, ?_, ?_, fun j hj7 _ => by simp [t1, hj7]⟩
            · rw [show t1.regs 8 = s.regs 8 by
                simp [t1, hs5'_r 8 (by decide) (by decide) (by decide)]]
              exact hs8le
            · simp [t1, hs5'_r 8 (by decide) (by decide) (by decide), hvle]
            · intro _; simp [t1, hs5'_r 7 (by decide) (by decide) (by decide), hv_eq]
            · simp only [t1, Data.set_regs, Function.update_self,
                hs5'_r 7 (by decide) (by decide) (by decide), pow_succ]
              omega
      obtain ⟨s6', he6, hs6'_mem, hs6'_8le, hs6'_8iff, hs6'_7eq, hs6'_7lt, hs6'_fr⟩ := e6
      have hs6'_r : ∀ j : Fin 12, j ≠ 7 → j ≠ 8 → j ≠ 9 → j ≠ 10 → j ≠ 11 → s6'.regs j = s.regs j :=
        fun j h7 h8 h9 h10 h11 => (hs6'_fr j h7 h8).trans (hs5'_r j h9 h10 h11)
      have hf66 : Fits W (s6'.regs 6 + s6'.regs 6) := by
        rw [hs6'_r 6 (by decide) (by decide) (by decide) (by decide) (by decide), hs6]
        have : 2 ^ i + 2 ^ i = 2 ^ (i + 1) := by rw [pow_succ]; omega
        rw [this]; exact hpow_W
      let s7' := s6'.set 6 (s6'.regs 6 + s6'.regs 6)
      have hf45 : Fits W (s7'.regs 4 + s7'.regs 5) := by
        simp only [s7', Data.set_regs, Function.update_of_ne (by decide : (4 : Fin 12) ≠ 6),
          Function.update_of_ne (by decide : (5 : Fin 12) ≠ 6),
          hs6'_r 4 (by decide) (by decide) (by decide) (by decide) (by decide),
          hs6'_r 5 (by decide) (by decide) (by decide) (by decide) (by decide), hs5]
        exact show i + 1 < 2 ^ W by omega
      let s8' := s7'.set 4 (i + 1)
      have e78 : ExecWithin W bscStep s6' s8' 2 := by
        have e7 : ExecWithin W (.op (.bin .add 6 6 6)) s6' s7' 1 := ExecWithin.bin hf66
        have e8 : ExecWithin W (.op (.bin .add 4 4 5)) s7' s8' 1 := by
          simpa [s8', s7', hs6'_r 4 (by decide) (by decide) (by decide) (by decide) (by decide),
            hs6'_r 5 (by decide) (by decide) (by decide) (by decide) (by decide), hs5] using
            ExecWithin.bin (w := W) (x := s7') (f := .add) (d := 4) (i := 4) (j := 5) hf45
        exact e7.seq e8
      refine ⟨s8', (e1234.seq (he5.seq (he6.seq e78))).mono (by omega),
        ⟨by simp [s8', s7', hs6'_r 0 (by decide) (by decide) (by decide) (by decide) (by decide),
          hs0],
         by simp [s8', s7', hs6'_r 1 (by decide) (by decide) (by decide) (by decide) (by decide),
           hs1],
         by simp [s8', s7', hs6'_r 2 (by decide) (by decide) (by decide) (by decide) (by decide),
           hs2],
         by simp [s8', s7', hs6'_r 3 (by decide) (by decide) (by decide) (by decide) (by decide),
           hs3],
         by simp [s8', s7', hs6'_r 5 (by decide) (by decide) (by decide) (by decide) (by decide),
           hs5],
         by simp [s8', s7', hs6'_mem],
         by simp [s8', s7', hs6'_r 6 (by decide) (by decide) (by decide) (by decide) (by decide),
           hs6, pow_succ]; omega,
         by simpa [s8', s7'] using hs6'_7lt,
         by simpa [s8', s7'] using hs6'_8le,
         ?_, ?_⟩, by simp [s8']⟩
      · simp only [s8', s7', Data.set_regs, Function.update_of_ne (by decide : (8 : Fin 12) ≠ 4),
          Function.update_of_ne (by decide : (8 : Fin 12) ≠ 6), hs6'_8iff, hs8iff]
        constructor
        · rintro ⟨hprev, hcur⟩ j hj
          by_cases hji : j = i
          · subst hji; exact hcur
          · exact hprev j (by omega)
        · intro hall
          exact ⟨fun j hj => hall j (by omega), hall i (by omega)⟩
      · intro h8
        have h8' : s6'.regs 8 = 1 := by simpa [s8', s7'] using h8
        have hs8 : s.regs 8 = 1 := (hs6'_8iff.mp h8').1
        have h7eq := hs6'_7eq h8'
        simp only [s8', s7', Data.set_regs, Function.update_of_ne (by decide : (7 : Fin 12) ≠ 4),
          Function.update_of_ne (by decide : (7 : Fin 12) ≠ 6), h7eq, hs7eq hs8, accOf,
          List.range_succ, List.map_append, List.map_singleton, List.sum_append,
          List.sum_singleton, v]) (by simp [x5]) hP0
  obtain ⟨_, _, _, _, _, hy0_mem, hy0_6, hy0_7, hy0_8le, hy0_8iff, hy0_7eq⟩ := hPy0
  have hfinal_fits : Fits W (y0.regs 7 + y0.regs 6) := by
    rw [hy0_6]
    rw [pow_succ] at hpow
    exact show y0.regs 7 + 2 ^ qLen < 2 ^ W by omega
  let y := y0.set 7 (y0.regs 7 + y0.regs 6)
  have hfinal : ExecWithin W (.op (.bin .add 7 7 6)) y0 y 1 := ExecWithin.bin hfinal_fits
  refine ⟨y, (hpre.seq (hy0.seq hfinal)).mono (by simp [x5]; omega),
    by simp [y, hy0_mem], by simpa [y] using hy0_8iff, by simpa [y] using hy0_8le, fun h8 => ?_⟩
  have h8' : y0.regs 8 = 1 := by simpa [y] using h8
  simp only [y, Data.set_regs, Function.update_self, hy0_7eq h8', hy0_6, accOf,
    bitStringCode, List.length_map, List.length_range]
  rw [Nat.add_comm]
  congr 1
  refine congrArg List.sum (List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_)
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range, Nat.zero_add]

end CslibFrontier.WordRAM
