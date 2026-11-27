/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.WordRAMOracle
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.CountingLoop
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lookup-Table Compilation and Stamped Oracle Wrapping

This module provides reusable Method-of-Four-Russians compilation primitives for Word-RAM oracle
reductions:

1. **Stamped bitstring table lookup (`bitTableLookupCode`)**: answers any stamped query of length
   `≤ ν` from bank `[H, 2*H)` in `O(qLen + 1)` steps without modifying memory.
2. **Bitstring table builder (`buildBitTableCode`)**: enumerates all binary strings of length `≤ ν`
   and solves `Q` on each in generation-stamped bank `[4*H, 6*H)`, populating `[H, 2*H)`.
3. **Stamped oracle wrapper (`wrapStampedOracle`)**: wraps an inner oracle reduction `c_A` plus a
   stamped lookup subroutine `sub` into a pure subroutine for `compileOracle` operating in bank
   `[2*H, 4*H)`.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

public section

namespace CslibFrontier.Complexity.FineGrained

open Cslib.WordRAM CslibFrontier.WordRAM

/-! ### Stamped Bitstring Table Lookup (`bitTableLookupCode`) -/

private def btlBscReg (j : Fin 12) : Fin (16 + 5) := ⟨5 + j.val, by omega⟩

private theorem btlBscReg_injective : Function.Injective btlBscReg := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [btlBscReg] at hv
  exact Fin.ext (by omega)

/-- Stamped oracle subroutine answering binary-string queries of length `≤ ν = mem[3 * base]`
from the precomputed lookup table at `[H, 2 * H)` (`H = base / 2`), leaving memory unchanged.
Args: `0 = qBase, 1 = qLen, 2 = base, 3 = gen`; output: `4 = ans`. -/
def bitTableLookupCode : Code .standard (16 + 5) :=
  let r0 : Fin 21 := 0; let r1 : Fin 21 := 1; let r2 : Fin 21 := 2
  let r3 : Fin 21 := 3; let r4 : Fin 21 := 4
  let rH : Fin 21 := 17; let rNuAddr : Fin 21 := 18; let rNu : Fin 21 := 19
  let rOne : Fin 21 := 20
  .seq
    (ram[
      rOne ← #1;
      rH ← r2 >>> rOne;
      rNuAddr ← r2 + r2;
      rNuAddr ← rNuAddr + r2;
      rNu ← *rNuAddr
    ])
    (.branch (.lt rNu r1)
      (.op (.const r4 0))
      (.seq (.op (.copy (btlBscReg 0) r0))
        (.seq (.op (.copy (btlBscReg 1) r1))
          (.seq (.op (.copy (btlBscReg 2) r2))
            (.seq (.op (.copy (btlBscReg 3) r3))
              (.seq (bitStringCodeStamped.rename btlBscReg)
                (.branch (.eq (btlBscReg 8) rOne)
                  (.seq (.op (.bin .add rNuAddr rH (btlBscReg 7)))
                    (.op (.load r4 rNuAddr)))
                  (.op (.const r4 0)))))))))

theorem isRandFree_bitTableLookupCode : bitTableLookupCode.IsRandFree := by
  refine ⟨⟨trivial, trivial, trivial, trivial, trivial⟩, trivial,
    trivial, trivial, trivial, trivial, isRandFree_rename isRandFree_bitStringCodeStamped,
    ⟨trivial, trivial⟩, trivial⟩

/-- Specification of `bitTableLookupCode`: executes in `≤ 18 * qLen + 25` instructions without
changing memory, returning `mem[H + bitStringCode z]` whenever `q =
  encBits z` with `z.length ≤ ν`. -/
theorem bitTableLookupCode_exec {W H nu base gen : ℕ} {x : Data 21}
    (hbase : base = 2 * H) (h6H : 6 * H < 2 ^ W) (hH_pos : 1 ≤ H)
    (hpow_nu : 2 ^ (nu + 1) ≤ H)
    (hmem_nu : x.mem (6 * H) = nu)
    (h0 : x.regs 0 + x.regs 1 ≤ H) (h2 : x.regs 2 = base) (h3 : x.regs 3 = gen) :
    let qBase := x.regs 0
    let qLen := x.regs 1
    let z : List Bool := (List.range qLen).map fun i =>
      decide (stampedRead base gen x.mem (qBase + i) = 1)
    ∃ y : Data 21,
      ExecWithin W bitTableLookupCode x y (18 * qLen + 25) ∧
      y.mem = x.mem ∧
      (qLen ≤ nu →
        ((∀ i < qLen, stampedRead base gen x.mem (qBase + i) ≤ 1) →
          y.regs 4 = x.mem (H + bitStringCode z)) ∧
        (¬(∀ i < qLen, stampedRead base gen x.mem (qBase + i) ≤ 1) → y.regs 4 = 0)) ∧
      (nu < qLen → y.regs 4 = 0) := by
  set qBase := x.regs 0
  set qLen := x.regs 1
  have h1_fits : Fits W 1 := show 1 < 2 ^ W by omega
  have hH_fits : Fits W H := show H < 2 ^ W by omega
  have h4H_fits : Fits W (4 * H) := show 4 * H < 2 ^ W by omega
  have h6H_fits : Fits W (6 * H) := h6H
  let x1 := x.set 20 1
  let x2 := x1.set 17 H
  let x3 := x2.set 18 (4 * H)
  let x4 := x3.set 18 (6 * H)
  let x5 := x4.set 19 nu
  have hpre : ExecWithin (B := .standard) W
      (.seq (.op (.const 20 1))
        (.seq (.op (.bin .shiftRight 17 2 20))
          (.seq (.op (.bin .add 18 2 2))
            (.seq (.op (.bin .add 18 18 2))
              (.op (.load 19 18)))))) x x5 5 := by
    have e1 : ExecWithin W (.op (Op.const (B := .standard) 20 1)) x x1 1 :=
      ExecWithin.const h1_fits
    have e2 : ExecWithin W (.op (.bin .shiftRight 17 2 20)) x1 x2 1 := by
      have hs : (2 * H) >>> 1 = H := by rw [Nat.shiftRight_eq_div_pow, pow_one]; omega
      simpa [x2, x1, h2, hbase, hs] using ExecWithin.bin (w := W) (x := x1) (f := .shiftRight)
        (d := 17) (i := 2) (j := 20) (by simpa [x1, h2, hbase, hs] using hH_fits)
    have e3 : ExecWithin W (.op (.bin .add 18 2 2)) x2 x3 1 := by
      have ha : 2 * H + 2 * H = 4 * H := by omega
      simpa [x3, x2, x1, h2, hbase, ha] using ExecWithin.bin (w := W) (x := x2) (f := .add)
        (d := 18) (i := 2) (j := 2) (by simpa [x2, x1, h2, hbase, ha] using h4H_fits)
    have e4 : ExecWithin W (.op (.bin .add 18 18 2)) x3 x4 1 := by
      have ha : 4 * H + 2 * H = 6 * H := by omega
      simpa [x4, x3, x2, x1, h2, hbase, ha] using ExecWithin.bin (w := W) (x := x3) (f := .add)
        (d := 18) (i := 18) (j := 2) (by simpa [x3, x2, x1, h2, hbase, ha] using h6H_fits)
    have e5 : ExecWithin W (.op (Op.load (B := .standard) 19 18)) x4 x5 1 := by
      simpa [x5, x4, x3, x2, x1, hmem_nu] using ExecWithin.load (B := .standard) (w := W) (x := x4)
        (d := 19) (a := 18)
    exact e1.seq (e2.seq (e3.seq (e4.seq e5)))
  by_cases hgt : nu < qLen
  · have hc : (Cond.lt 19 1).Holds x5 := by
      simp [Cond.Holds, x5, x4, x3, x2, x1, qLen, hgt]
    let y := x5.set 4 0
    refine ⟨y,
      (hpre.seq (ExecWithin.branch_pos hc (ExecWithin.const (fits_zero W)))).mono (by omega),
      rfl, fun hle => (by omega), fun _ => by simp [y]⟩
  · have hle : qLen ≤ nu := by omega
    have hc : ¬(Cond.lt 19 1).Holds x5 := by
      simp [Cond.Holds, x5, x4, x3, x2, x1, qLen, hgt]
    let x6 := x5.set (btlBscReg 0) (x5.regs 0)
    let x7 := x6.set (btlBscReg 1) (x6.regs 1)
    let x8 := x7.set (btlBscReg 2) (x7.regs 2)
    let x9 := x8.set (btlBscReg 3) (x8.regs 3)
    have hx9_0 : (x9.comap btlBscReg).regs 0 = qBase := by
      simp [x9, x8, x7, x6, x5, x4, x3, x2, x1, btlBscReg, Fin.ext_iff, qBase]
    have hx9_1 : (x9.comap btlBscReg).regs 1 = qLen := by
      simp [x9, x8, x7, x6, x5, x4, x3, x2, x1, btlBscReg, Fin.ext_iff, qLen]
    have hx9_2 : (x9.comap btlBscReg).regs 2 = base := by
      simp [x9, x8, x7, x6, x5, x4, x3, x2, x1, btlBscReg, Fin.ext_iff, h2]
    have hx9_3 : (x9.comap btlBscReg).regs 3 = gen := by
      simp [x9, x8, x7, x6, x5, x4, x3, x2, x1, btlBscReg, Fin.ext_iff, h3]
    have hpow_q : 2 ^ (qLen + 1) ≤ 2 ^ W := by
      have : 2 ^ (qLen + 1) ≤ 2 ^ (nu + 1) := Nat.pow_le_pow_right Nat.two_pos (by omega)
      omega
    obtain ⟨b_out, hb_out, hb_mem, hb_iff, _, hb_code⟩ :=
      bitStringCodeStamped_exec (W := W) (base := base) (H := H) (gen := gen)
        (x := x9.comap btlBscReg) (by rw [hx9_0, hx9_1]; exact h0)
        (by rw [hx9_1]; exact hpow_q) (by omega) hx9_2 hx9_3
    obtain ⟨x10, hx10, hx10_eq, hx10_fr⟩ :=
      ExecWithin.rename_post btlBscReg_injective ⟨b_out, hb_out, rfl⟩
    have hx10_mem : x10.mem = x.mem := (congrArg Data.mem hx10_eq.symm).trans hb_mem
    have hx10_H : x10.regs 17 = H := by
      have hne : ∀ j : Fin 12, btlBscReg j ≠ (17 : Fin 21) := fun j h => by
        have := congrArg Fin.val h; simp [btlBscReg] at this; omega
      rw [hx10_fr 17 hne]; simp [x9, x8, x7, x6, x5, x4, x3, x2, btlBscReg, Fin.ext_iff]
    have hx10_one : x10.regs 20 = 1 := by
      have hne : ∀ j : Fin 12, btlBscReg j ≠ (20 : Fin 21) := fun j h => by
        have := congrArg Fin.val h; simp [btlBscReg] at this; omega
      rw [hx10_fr 20 hne]; simp [x9, x8, x7, x6, x5, x4, x3, x2, x1, btlBscReg, Fin.ext_iff]
    have hx10_8 : x10.regs (btlBscReg 8) = b_out.regs 8 :=
      congrFun (congrArg Data.regs hx10_eq.symm) 8
    have hx10_7 : x10.regs (btlBscReg 7) = b_out.regs 7 :=
      congrFun (congrArg Data.regs hx10_eq.symm) 7
    have hx9_mem : x9.mem = x.mem := rfl
    by_cases hvalid : ∀ i < qLen, stampedRead base gen x.mem (qBase + i) ≤ 1
    · have hb8 : b_out.regs 8 = 1 := by
        rw [hb_iff]; simpa only [Data.comap_mem, hx9_mem, hx9_0, hx9_1] using hvalid
      have hc2 : (Cond.eq (btlBscReg 8) 20).Holds x10 := by
        simp [Cond.Holds, hx10_8, hx10_one, hb8]
      have hb7 : b_out.regs 7 = bitStringCode
          ((List.range qLen).map fun i => decide (stampedRead base gen x.mem (qBase + i) = 1)) := by
        simpa only [Data.comap_mem, hx9_mem, hx9_0, hx9_1] using hb_code hb8
      have haddr_fits : Fits W (x10.regs 17 + x10.regs (btlBscReg 7)) := by
        rw [hx10_H, hx10_7, hb7]
        have hlt := bitStringCode_lt
          ((List.range qLen).map fun i => decide (stampedRead base gen x.mem (qBase + i) = 1))
        simp only [List.length_map, List.length_range] at hlt
        have hlt2 : 2 ^ (qLen + 1) ≤ 2 ^ (nu + 1) := Nat.pow_le_pow_right Nat.two_pos (by omega)
        exact show H + bitStringCode _ < 2 ^ W by omega
      let x11 := x10.set 18 (x10.regs 17 + x10.regs (btlBscReg 7))
      let y := x11.set 4 (x11.mem (x11.regs 18))
      have hbr2 : ExecWithin W
          (.branch (.eq (btlBscReg 8) 20)
            (.seq (.op (.bin .add 18 17 (btlBscReg 7))) (.op (.load 4 18)))
            (.op (.const 4 0))) x10 y 3 :=
        (ExecWithin.branch_pos hc2
          ((ExecWithin.bin haddr_fits).seq ExecWithin.load)).mono (by omega)
      have htail_ex : ExecWithin W
          (.seq (.op (.copy (btlBscReg 0) 0))
            (.seq (.op (.copy (btlBscReg 1) 1))
              (.seq (.op (.copy (btlBscReg 2) 2))
                (.seq (.op (.copy (btlBscReg 3) 3))
                  (.seq (bitStringCodeStamped.rename btlBscReg)
                    (.branch (.eq (btlBscReg 8) 20)
                      (.seq (.op (.bin .add 18 17 (btlBscReg 7))) (.op (.load 4 18)))
                      (.op (.const 4 0)))))))) x5 y (18 * qLen + 15) :=
        (ExecWithin.copy.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
          (ExecWithin.copy.seq (hx10.seq hbr2))))).mono (by rw [hx9_1]; omega)
      refine ⟨y, (hpre.seq (ExecWithin.branch_neg hc htail_ex)).mono (by omega),
        by simp [y, x11, hx10_mem], fun _ => ⟨fun _ => by
          simp [y, x11, hx10_mem, hx10_H, hx10_7, hb7], fun hnv => (hnv hvalid).elim⟩,
        fun h => (by omega)⟩
    · have hb8 : b_out.regs 8 ≠ 1 := fun h =>
        hvalid (by simpa only [Data.comap_mem, hx9_mem, hx9_0, hx9_1] using hb_iff.mp h)
      have hc2 : ¬(Cond.eq (btlBscReg 8) 20).Holds x10 := by
        simp [Cond.Holds, hx10_8, hx10_one, hb8]
      let y := x10.set 4 0
      have hbr2 : ExecWithin W
          (.branch (.eq (btlBscReg 8) 20)
            (.seq (.op (.bin .add 18 17 (btlBscReg 7))) (.op (.load 4 18)))
            (.op (.const 4 0))) x10 y 3 :=
        ExecWithin.branch_neg hc2 (ExecWithin.const (fits_zero W))
      have htail_ex : ExecWithin W
          (.seq (.op (.copy (btlBscReg 0) 0))
            (.seq (.op (.copy (btlBscReg 1) 1))
              (.seq (.op (.copy (btlBscReg 2) 2))
                (.seq (.op (.copy (btlBscReg 3) 3))
                  (.seq (bitStringCodeStamped.rename btlBscReg)
                    (.branch (.eq (btlBscReg 8) 20)
                      (.seq (.op (.bin .add 18 17 (btlBscReg 7))) (.op (.load 4 18)))
                      (.op (.const 4 0)))))))) x5 y (18 * qLen + 15) :=
        (ExecWithin.copy.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
          (ExecWithin.copy.seq (hx10.seq hbr2))))).mono (by rw [hx9_1]; omega)
      refine ⟨y, (hpre.seq (ExecWithin.branch_neg hc htail_ex)).mono (by omega),
        by simp [y, hx10_mem], fun _ => ⟨fun hv => (hvalid hv).elim, fun _ => by simp [y]⟩,
        fun h => (by omega)⟩

/-! ### Lookup-Table Construction (`buildBitTableCode`) -/

private def bbtUnpackReg {r_Q : ℕ} (j : Fin 9) : Fin (r_Q + 26) := ⟨11 + j.val, by omega⟩
private def bbtStampReg {r_Q : ℕ} (j : Fin (r_Q + 6)) : Fin (r_Q + 26) := ⟨20 + j.val, by omega⟩

private theorem bbtUnpackReg_injective {r_Q : ℕ} :
    Function.Injective (bbtUnpackReg (r_Q := r_Q)) := by
  intro a b h; have hv :=
    congrArg Fin.val h; simp only [bbtUnpackReg] at hv; exact Fin.ext (by omega)

private theorem bbtStampReg_injective {r_Q : ℕ} :
    Function.Injective (bbtStampReg (r_Q := r_Q)) := by
  intro a b h; have hv :=
    congrArg Fin.val h; simp only [bbtStampReg] at hv; exact Fin.ext (by omega)

private def bbtInnerBody {r_Q : ℕ} (c_Q : Code .standard r_Q) (out_Q : Fin r_Q) :
    Code .standard (r_Q + 26) :=
  let rH : Fin (r_Q + 26) := ⟨0, by omega⟩
  let rW : Fin (r_Q + 26) := ⟨1, by omega⟩
  let rLen : Fin (r_Q + 26) := ⟨3, by omega⟩
  let rMask : Fin (r_Q + 26) := ⟨4, by omega⟩
  let rPow : Fin (r_Q + 26) := ⟨5, by omega⟩
  let rBaseQ : Fin (r_Q + 26) := ⟨6, by omega⟩
  let rGenQ : Fin (r_Q + 26) := ⟨7, by omega⟩
  let rOne : Fin (r_Q + 26) := ⟨8, by omega⟩
  let rAddr : Fin (r_Q + 26) := ⟨9, by omega⟩
  .seq (.op (.bin .add rGenQ rGenQ rOne))
    (.seq (.op (.copy (bbtUnpackReg 0) rLen))
      (.seq (.op (.copy (bbtUnpackReg 1) rMask))
        (.seq (.op (.copy (bbtUnpackReg 2) rBaseQ))
          (.seq (.op (.copy (bbtUnpackReg 3) rGenQ))
            (.seq (unpackBitsToStampedCode.rename bbtUnpackReg)
              (.seq (.op (.copy (bbtStampReg stampBaseReg) rBaseQ))
                (.seq (.op (.copy (bbtStampReg stampGenReg) rGenQ))
                  (.seq (.op (.copy (bbtStampReg stampWidthReg) rW))
                    (.seq ((zeroPrefixRegs (stampCode c_Q)).rename bbtStampReg)
                      (.seq (.op (.bin .add rAddr rPow rMask))
                        (.seq (.op (.bin .add rAddr rH rAddr))
                          (.seq (.op (.store rAddr (bbtStampReg (stampVirtReg out_Q))))
                            (.op (.bin .add rMask rMask rOne))))))))))))))

private def bbtOuterBody {r_Q : ℕ} (c_Q : Code .standard r_Q) (out_Q : Fin r_Q) :
    Code .standard (r_Q + 26) :=
  let rLen : Fin (r_Q + 26) := ⟨3, by omega⟩
  let rMask : Fin (r_Q + 26) := ⟨4, by omega⟩
  let rPow : Fin (r_Q + 26) := ⟨5, by omega⟩
  let rOne : Fin (r_Q + 26) := ⟨8, by omega⟩
  .seq (.op (.bin .shiftLeft rPow rOne rLen))
    (.seq (.op (.const rMask 0))
      (.seq (.loop (.lt rMask rPow) (bbtInnerBody c_Q out_Q))
        (.op (.bin .add rLen rLen rOne))))

/-- Build the lookup table `mem[H + bitStringCode z] = (O_Q (encBits z)).toNat` for all bitstrings
`z` of length `≤ ν` using stamped bank `[4 * H, 6 * H)`.
Inputs: `0 = H, 1 = w_log, 2 = ν`. Preserves `[0, H)`, `[2 * H, 4 * H)`, and `mem[6 * H]`. -/
def buildBitTableCode {r_Q : ℕ} (c_Q : Code .standard r_Q) (out_Q : Fin r_Q) :
    Code .standard (r_Q + 26) :=
  let rH : Fin (r_Q + 26) := ⟨0, by omega⟩
  let rNu : Fin (r_Q + 26) := ⟨2, by omega⟩
  let rLen : Fin (r_Q + 26) := ⟨3, by omega⟩
  let rBaseQ : Fin (r_Q + 26) := ⟨6, by omega⟩
  let rGenQ : Fin (r_Q + 26) := ⟨7, by omega⟩
  let rOne : Fin (r_Q + 26) := ⟨8, by omega⟩
  let rNu1 : Fin (r_Q + 26) := ⟨10, by omega⟩
  .seq
    (ram[
      rOne ← #1;
      rBaseQ ← rH + rH;
      rBaseQ ← rBaseQ + rBaseQ;
      rGenQ ← #0;
      rNu1 ← rNu + rOne;
      rLen ← #0
    ])
    (.loop (.lt rLen rNu1) (bbtOuterBody c_Q out_Q))

theorem isRandFree_buildBitTableCode {r_Q : ℕ} {c_Q : Code .standard r_Q} (out_Q : Fin r_Q)
    (hc : c_Q.IsRandFree) : (buildBitTableCode c_Q out_Q).IsRandFree := by
  refine ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial⟩,
    ⟨trivial, trivial, ⟨trivial, trivial, trivial, trivial, trivial,
      isRandFree_rename isRandFree_unpackBitsToStampedCode, trivial, trivial, trivial,
      isRandFree_rename (isRandFree_zeroPrefixRegs (isRandFree_stampCode hc)),
      trivial, trivial, trivial, trivial⟩, trivial⟩⟩

private theorem bitsOfMaskBool_bitStringMask (z : List Bool) :
    bitsOfMaskBool z.length (bitStringMask z) = z := by
  apply bitStringCode_injective
  rw [bitStringCode_bitsOfMaskBool _ _ (bitStringMask_lt z), bitStringCode_eq_two_pow_add_mask]

private theorem bbtInnerBody_exec {r_Q W w_log H nu T_max len mask : ℕ}
    {Q : Set (List Bool)} {c_Q : Code .standard r_Q} {out_Q : Fin r_Q}
    {x u : Data (r_Q + 26)}
    (hrf : c_Q.IsRandFree) (hH : H = 2 ^ w_log) (h6H : 6 * H ≤ 2 ^ W)
    (hpow_nu : 2 ^ (nu + 1) ≤ H) (hlen_le : len ≤ nu) (hm_lt : mask < 2 ^ len)
    (hQ : ∀ z : List Bool, z.length ≤ nu → c_Q.Answers out_Q w_log (encBits z) (z ∈ Q) T_max)
    (hu0 : u.regs ⟨0, by omega⟩ = H) (hu1 : u.regs ⟨1, by omega⟩ = w_log)
    (hu2 : u.regs ⟨2, by omega⟩ = nu) (hu3 : u.regs ⟨3, by omega⟩ = len)
    (hu4 : u.regs ⟨4, by omega⟩ = mask) (hu5 : u.regs ⟨5, by omega⟩ = 2 ^ len)
    (hu6 : u.regs ⟨6, by omega⟩ = 4 * H) (hu8 : u.regs ⟨8, by omega⟩ = 1)
    (hu10 : u.regs ⟨10, by omega⟩ = nu + 1) (hu7 : u.regs ⟨7, by omega⟩ = 2 ^ len - 1 + mask)
    (hust : StampLe (4 * H) H (u.regs ⟨7, by omega⟩) u.mem)
    (hutab : ∀ z : List Bool, z.length < len →
      u.mem (H + bitStringCode z) = (oracleOf Q encBits (encBits z)).toNat)
    (humask : ∀ k < mask, u.mem (H + (2 ^ len + k)) =
      (oracleOf Q encBits (encBits (bitsOfMaskBool len k))).toNat)
    (hulo : ∀ a < H, u.mem a = x.mem a)
    (humid : ∀ a, 2 * H ≤ a → a < 4 * H → u.mem a = x.mem a)
    (hu6H : u.mem (6 * H) = x.mem (6 * H)) :
    ∃ u14 : Data (r_Q + 26),
      ExecWithin W (bbtInnerBody c_Q out_Q) u u14 (11 * nu + 7 * T_max + r_Q + 26) ∧
      u14.regs ⟨0, by omega⟩ = H ∧ u14.regs ⟨1, by omega⟩ = w_log ∧ u14.regs ⟨2, by omega⟩ = nu ∧
      u14.regs ⟨3, by omega⟩ = len ∧ u14.regs ⟨5, by omega⟩ = 2 ^ len ∧
      u14.regs ⟨6, by omega⟩ = 4 * H ∧ u14.regs ⟨8, by omega⟩ = 1 ∧
      u14.regs ⟨10, by omega⟩ = nu + 1 ∧ u14.regs ⟨7, by omega⟩ = 2 ^ len - 1 + (mask + 1) ∧
      StampLe (4 * H) H (u14.regs ⟨7, by omega⟩) u14.mem ∧
      (∀ z : List Bool, z.length < len →
        u14.mem (H + bitStringCode z) = (oracleOf Q encBits (encBits z)).toNat) ∧
      (∀ k < mask + 1, u14.mem (H + (2 ^ len + k)) =
        (oracleOf Q encBits (encBits (bitsOfMaskBool len k))).toNat) ∧
      (∀ a < H, u14.mem a = x.mem a) ∧
      (∀ a, 2 * H ≤ a → a < 4 * H → u14.mem a = x.mem a) ∧
      u14.mem (6 * H) = x.mem (6 * H) ∧
      u14.regs ⟨4, by omega⟩ = mask + 1 := by
  have hH_le : 2 ^ w_log ≤ H := le_of_eq hH.symm
  have h2pow_le : 2 ^ (len + 1) ≤ 2 ^ (nu + 1) := Nat.pow_le_pow_right Nat.two_pos (by omega)
  have hnu_lt : nu + 1 < H := lt_of_lt_of_le Nat.lt_two_pow_self hpow_nu
  have hu0' : u.regs 0 = H := hu0
  have hu1' : u.regs 1 = w_log := hu1
  have hgen_new : u.regs ⟨7, by omega⟩ + 1 = 2 ^ len + mask := by
    have := Nat.one_le_two_pow (n := len); omega
  have hgen_fits : Fits W (u.regs ⟨7, by omega⟩ + 1) := by
    rw [hgen_new]
    have : 2 ^ len + mask < 2 ^ (len + 1) := by rw [pow_succ]; omega
    exact show 2 ^ len + mask < 2 ^ W by omega
  let u1 := u.set ⟨7, by omega⟩ (u.regs ⟨7, by omega⟩ + 1)
  have he1 : ExecWithin W
      (.op (.bin .add ⟨7, by omega⟩ ⟨7, by omega⟩ ⟨8, by omega⟩)) u u1 1 := by
    simpa [u1, hu8] using ExecWithin.bin (w := W) (x := u) (f := .add)
      (d := ⟨7, by omega⟩) (i := ⟨7, by omega⟩) (j := ⟨8, by omega⟩)
      (by simpa [hu8] using hgen_fits)
  let u2 := u1.set (bbtUnpackReg 0) (u1.regs ⟨3, by omega⟩)
  let u3 := u2.set (bbtUnpackReg 1) (u2.regs ⟨4, by omega⟩)
  let u4 := u3.set (bbtUnpackReg 2) (u3.regs ⟨6, by omega⟩)
  let u5 := u4.set (bbtUnpackReg 3) (u4.regs ⟨7, by omega⟩)
  have hu5_low : ∀ j : Fin (r_Q + 26), j.val < 11 → u5.regs j = u1.regs j := fun j hj => by
    have hne : ∀ k : Fin 9, j ≠ bbtUnpackReg k := fun k h => by
      have := congrArg Fin.val h; simp [bbtUnpackReg] at this; omega
    simp [u5, u4, u3, u2, hne]
  have hu5_u0 : (u5.comap bbtUnpackReg).regs 0 = len := by
    simp [u5, u4, u3, u2, u1, bbtUnpackReg, Fin.ext_iff, hu3]
  have hu5_u1 : (u5.comap bbtUnpackReg).regs 1 = mask := by
    simp [u5, u4, u3, u2, u1, bbtUnpackReg, Fin.ext_iff, hu4]
  have hu5_u2 : (u5.comap bbtUnpackReg).regs 2 = 4 * H := by
    simp [u5, u4, u3, u2, u1, bbtUnpackReg, Fin.ext_iff, hu6]
  have hu5_u3 : (u5.comap bbtUnpackReg).regs 3 = 2 ^ len + mask := by
    simp [u5, u4, u3, u2, u1, bbtUnpackReg, Fin.ext_iff, hgen_new]
  have hmask_fits : Fits W mask := show mask < 2 ^ W by omega
  obtain ⟨up_out, hup_out, hup_rep, hup_st, hup_fr⟩ :=
    unpackBitsToStampedCode_exec (W := W) (base := 4 * H) (H := H)
      (gen₀ := u.regs ⟨7, by omega⟩) (gen := 2 ^ len + mask)
      (x := u5.comap bbtUnpackReg) (by omega) (by rw [hu5_u0]; omega)
      (by rw [hu5_u1]; exact hmask_fits) (by omega) hu5_u2 hu5_u3 hust
  obtain ⟨u6, hu6_ex, hu6_eq, hu6_fr⟩ :=
    ExecWithin.rename_post (bbtUnpackReg_injective (r_Q := r_Q)) ⟨up_out, hup_out, rfl⟩
  have hu6_mem : u6.mem = up_out.mem := congrArg Data.mem hu6_eq.symm
  have hu6_low : ∀ j : Fin (r_Q + 26), j.val < 11 → u6.regs j = u1.regs j := fun j hj => by
    have hne : ∀ k : Fin 9, bbtUnpackReg (r_Q := r_Q) k ≠ j := fun k h => by
      have := congrArg Fin.val h; simp [bbtUnpackReg] at this; omega
    exact (hu6_fr j hne).trans (hu5_low j hj)
  let u7 := u6.set (bbtStampReg stampBaseReg) (u6.regs ⟨6, by omega⟩)
  let u8 := u7.set (bbtStampReg stampGenReg) (u7.regs ⟨7, by omega⟩)
  let u9 := u8.set (bbtStampReg stampWidthReg) (u8.regs ⟨1, by omega⟩)
  let u9_s : Data (r_Q + 6) :=
    ⟨fun k => if k.val < r_Q then 0 else (u9.comap bbtStampReg).regs k, u9.mem⟩
  set z_cur := bitsOfMaskBool len mask
  have hz_len : z_cur.length = len := length_bitsOfMaskBool len mask
  obtain ⟨y_Q, ⟨t_Q, ht_Q, hex_Q⟩, hyQ_le, hyQ_iff⟩ :=
    hQ z_cur (by rw [hz_len]; exact hlen_le)
  have hq_fits : InputFits w_log (encBits z_cur) := by
    refine inputFits_encBits ?_
    rw [hz_len, logWidth, one_mul]
    have h1 : 2 ^ (Nat.log 2 len + 1) ≤ 2 ^ (len + 1) :=
      Nat.pow_le_pow_right Nat.two_pos (Nat.add_le_add_right (Nat.log_le_self 2 len) 1)
    have h2 : 2 ^ (len + 1) ≤ 2 ^ w_log := by omega
    exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp (h1.trans h2)
  have hu9_s_B : u9_s.regs stampBaseReg = 4 * H := by
    have hlt : ¬(stampBaseReg (r := r_Q)).val < r_Q := by simp
    simp only [u9_s, hlt, ↓reduceIte, Data.comap_regs]
    have h1' : bbtStampReg (r_Q := r_Q) stampBaseReg ≠ bbtStampReg stampGenReg :=
      bbtStampReg_injective.ne stampBaseReg_ne_stampGenReg
    have h2' : bbtStampReg (r_Q := r_Q) stampBaseReg ≠ bbtStampReg stampWidthReg :=
      bbtStampReg_injective.ne stampBaseReg_ne_stampWidthReg
    have h67 : (⟨6, by omega⟩ : Fin (r_Q + 26)) ≠ ⟨7, by omega⟩ := by simp [Fin.ext_iff]
    simp only [u9, u8, u7, Data.set_regs, Function.update_of_ne h1',
      Function.update_of_ne h2', Function.update_self, hu6_low ⟨6, by omega⟩ (by simp),
      u1, Function.update_of_ne h67, hu6]
  have hu9_s_G : u9_s.regs stampGenReg = 2 ^ len + mask := by
    have hlt : ¬(stampGenReg (r := r_Q)).val < r_Q := by simp
    simp only [u9_s, hlt, ↓reduceIte, Data.comap_regs]
    have h2' : bbtStampReg (r_Q := r_Q) stampGenReg ≠ bbtStampReg stampWidthReg :=
      bbtStampReg_injective.ne stampGenReg_ne_stampWidthReg
    have hne7 : (⟨7, by omega⟩ : Fin (r_Q + 26)) ≠ bbtStampReg stampBaseReg :=
      Fin.ne_of_val_ne (by simp [bbtStampReg]; omega)
    simp only [u9, u8, u7, Data.set_regs, Function.update_of_ne h2',
      Function.update_of_ne hne7, Function.update_self, hu6_low ⟨7, by omega⟩ (by simp),
      u1, hgen_new]
  have hu9_s_W : u9_s.regs stampWidthReg = w_log := by
    have hlt : ¬(stampWidthReg (r := r_Q)).val < r_Q := by simp
    simp only [u9_s, hlt, ↓reduceIte, Data.comap_regs]
    have hne1b : (⟨1, by omega⟩ : Fin (r_Q + 26)) ≠ bbtStampReg stampBaseReg :=
      Fin.ne_of_val_ne (by simp [bbtStampReg]; omega)
    have hne1g : (⟨1, by omega⟩ : Fin (r_Q + 26)) ≠ bbtStampReg stampGenReg :=
      Fin.ne_of_val_ne (by simp [bbtStampReg]; omega)
    have h17 : (⟨1, by omega⟩ : Fin (r_Q + 26)) ≠ ⟨7, by omega⟩ := by simp [Fin.ext_iff]
    simp only [u9, u8, u7, Data.set_regs, Function.update_of_ne hne1b,
      Function.update_of_ne hne1g, Function.update_self, hu6_low ⟨1, by omega⟩ (by simp),
      u1, Function.update_of_ne h17, hu1]
  have hu9_s_virt : u9_s.regs ∘ stampVirtReg = (Data.init (encBits z_cur) (r := r_Q)).regs := by
    funext i; simp [u9_s, Data.init_regs]
  have hu9_s_rep : MemRepresents (4 * H) H (2 ^ len + mask) u9_s.mem
      (Data.init (encBits z_cur) (r := r_Q)).mem := by
    intro a ha
    have hm : u9_s.mem = up_out.mem := by simp [u9_s, u9, u8, u7, hu6_mem]
    rw [hm]
    have hrep' := hup_rep a ha
    rw [hu5_u0, hu5_u1] at hrep'
    refine hrep'.trans ?_
    cases a <;> simp [Data.init_mem_zero, Data.init_mem_succ, z_cur, encBits_apply]
  have hu9_s_st : StampLe (4 * H) H (2 ^ len + mask) u9_s.mem := by
    have hm : u9_s.mem = up_out.mem := by simp [u9_s, u9, u8, u7, hu6_mem]
    rw [hm]; exact hup_st
  obtain ⟨y_s, hy_s, _, _, _, hy_s_virt, _, hy_s_st, hy_s_fr⟩ :=
    stampCode_exec (W := W) (base := 4 * H) (H := H) (gen := 2 ^ len + mask)
      hrf (Data.Bounded.init hq_fits) hH_le (by omega) hex_Q
      hu9_s_B hu9_s_G hu9_s_W hu9_s_virt hu9_s_rep hu9_s_st
  obtain ⟨u10, hu10_ex, hu10_eq, hu10_fr⟩ :=
    ExecWithin.rename_post (bbtStampReg_injective (r_Q := r_Q))
      ⟨y_s, zeroPrefixRegs_exec (r := r_Q) (m := 6) hy_s, rfl⟩
  have hu10_low : ∀ j : Fin (r_Q + 26), j.val < 11 → u10.regs j = u1.regs j := fun j hj => by
    have hneS : ∀ k : Fin (r_Q + 6), bbtStampReg (r_Q := r_Q) k ≠ j := fun k h => by
      have := congrArg Fin.val h; simp [bbtStampReg] at this; omega
    have hu9j : u9.regs j = u6.regs j := by
      simp only [u9, u8, u7, Data.set_regs,
        Function.update_of_ne (hneS stampBaseReg).symm,
        Function.update_of_ne (hneS stampGenReg).symm,
        Function.update_of_ne (hneS stampWidthReg).symm]
    exact (hu10_fr j hneS).trans (hu9j.trans (hu6_low j hj))
  have hu10_mem_eq : ∀ p, ¬(4 * H ≤ p ∧ p < 6 * H) → u10.mem p = u.mem p := by
    intro p hp
    have hm : u10.mem = y_s.mem := congrArg Data.mem hu10_eq.symm
    rw [hm, hy_s_fr p (by omega), show u9_s.mem p =
      up_out.mem p by simp [u9_s, u9, u8, u7, hu6_mem]]
    exact hup_fr p (by omega)
  have hu10_out : u10.regs (bbtStampReg (stampVirtReg out_Q)) =
      (oracleOf Q encBits (encBits z_cur)).toNat := by
    have h1' : u10.regs (bbtStampReg (stampVirtReg out_Q)) = y_Q.regs out_Q :=
      (congrFun (congrArg Data.regs hu10_eq.symm) (stampVirtReg out_Q)).trans
        (congrFun hy_s_virt out_Q)
    rw [h1']
    by_cases hzQ : z_cur ∈ Q
    · rw [hyQ_iff.mpr hzQ, (oracleOf_enc Q encBits z_cur).mpr hzQ]; rfl
    · have hne' : y_Q.regs out_Q ≠ 1 := fun h => hzQ (hyQ_iff.mp h)
      have h0' : y_Q.regs out_Q = 0 := by omega
      have hf' : oracleOf Q encBits (encBits z_cur) = false := by
        cases h : oracleOf Q encBits (encBits z_cur)
        · rfl
        · exact absurd ((oracleOf_enc Q encBits z_cur).mp h) hzQ
      rw [h0', hf']; rfl
  have hidx_fits : Fits W (2 ^ len + mask) := by
    have : 2 ^ len + mask < 2 ^ (len + 1) := by rw [pow_succ]; omega
    exact show 2 ^ len + mask < 2 ^ W by omega
  have haddr_fits : Fits W (H + (2 ^ len + mask)) := by
    have : 2 ^ len + mask < 2 ^ (len + 1) := by rw [pow_succ]; omega
    exact show H + (2 ^ len + mask) < 2 ^ W by omega
  let u11 := u10.set ⟨9, by omega⟩ (2 ^ len + mask)
  let u12 := u11.set ⟨9, by omega⟩ (H + (2 ^ len + mask))
  let u13 := u12.write (H + (2 ^ len + mask)) (oracleOf Q encBits (encBits z_cur)).toNat
  let u14 := u13.set ⟨4, by omega⟩ (mask + 1)
  have he_tail : ExecWithin W
      (.seq (.op (.bin .add ⟨9, by omega⟩ ⟨5, by omega⟩ ⟨4, by omega⟩))
        (.seq (.op (.bin .add ⟨9, by omega⟩ ⟨0, by omega⟩ ⟨9, by omega⟩))
          (.seq (.op (.store ⟨9, by omega⟩ (bbtStampReg (stampVirtReg out_Q))))
            (.op (.bin .add ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨8, by omega⟩))))) u10 u14 4 := by
    have eA : ExecWithin W (.op (.bin .add ⟨9, by omega⟩ ⟨5, by omega⟩ ⟨4, by omega⟩))
        u10 u11 1 := by
      simpa [u11, hu10_low ⟨5, by omega⟩ (by simp), hu10_low ⟨4, by omega⟩ (by simp),
        u1, hu5, hu4] using ExecWithin.bin (w := W) (x := u10) (f := .add)
        (d := ⟨9, by omega⟩) (i := ⟨5, by omega⟩) (j := ⟨4, by omega⟩)
        (by simpa [hu10_low ⟨5, by omega⟩ (by simp), hu10_low ⟨4, by omega⟩ (by simp),
          u1, hu5, hu4] using hidx_fits)
    have eB : ExecWithin W (.op (.bin .add ⟨9, by omega⟩ ⟨0, by omega⟩ ⟨9, by omega⟩))
        u11 u12 1 := by
      have hu10_0 : u10.regs 0 = H := by
        have h := hu10_low ⟨0, by omega⟩ (by simp)
        simpa [u1, hu0', Fin.ext_iff] using h
      simpa [u12, u11, hu10_0, Fin.ext_iff] using
        ExecWithin.bin (w := W) (x := u11) (f := .add)
          (d := ⟨9, by omega⟩) (i := ⟨0, by omega⟩) (j := ⟨9, by omega⟩)
          (by simpa [u11, hu10_0, Fin.ext_iff] using haddr_fits)
    have eC : ExecWithin (B := .standard) W
        (.op (.store ⟨9, by omega⟩ (bbtStampReg (stampVirtReg out_Q)))) u12 u13 1 := by
      have hne9 : bbtStampReg (r_Q := r_Q) (stampVirtReg out_Q) ≠ ⟨9, by omega⟩ :=
        Fin.ne_of_val_ne (by simp [bbtStampReg]; omega)
      simpa [u13, u12, u11, hne9, hu10_out] using
        ExecWithin.store (w := W) (x := u12) (a := ⟨9, by omega⟩)
          (s := bbtStampReg (stampVirtReg out_Q))
    have eD : ExecWithin W (.op (.bin .add ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨8, by omega⟩))
        u13 u14 1 := by
      have hfm : Fits W (mask + 1) := show mask + 1 < 2 ^ W by omega
      simpa [u14, u13, u12, u11, hu10_low ⟨4, by omega⟩ (by simp),
        hu10_low ⟨8, by omega⟩ (by simp), u1, hu8, hu4] using
        ExecWithin.bin (w := W) (x := u13) (f := .add) (d := ⟨4, by omega⟩)
          (i := ⟨4, by omega⟩) (j := ⟨8, by omega⟩)
          (by simpa [u13, u12, u11, hu10_low ⟨4, by omega⟩ (by simp),
            hu10_low ⟨8, by omega⟩ (by simp), u1, hu8, hu4] using hfm)
    exact eA.seq (eB.seq (eC.seq eD))
  have hbody_ex : ExecWithin W (bbtInnerBody c_Q out_Q) u u14 (11 * nu + 7 * T_max + r_Q + 26) :=
    (he1.seq (ExecWithin.copy.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
      (ExecWithin.copy.seq (hu6_ex.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
        (ExecWithin.copy.seq (hu10_ex.seq he_tail)))))))))).mono (by rw [hu5_u0]; omega)
  refine ⟨u14, hbody_ex, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [u14]⟩
  · have h := hu10_low ⟨0, by omega⟩ (by simp)
    simp [u14, u13, u12, u11, Fin.ext_iff]; simpa [u1, hu0', Fin.ext_iff] using h
  · have h := hu10_low ⟨1, by omega⟩ (by simp)
    simp [u14, u13, u12, u11, Fin.ext_iff]; simpa [u1, hu1', Fin.ext_iff] using h
  · simp [u14, u13, u12, u11, hu10_low ⟨2, by omega⟩ (by simp), u1, hu2, Fin.ext_iff]
  · simp [u14, u13, u12, u11, hu10_low ⟨3, by omega⟩ (by simp), u1, hu3, Fin.ext_iff]
  · simp [u14, u13, u12, u11, hu10_low ⟨5, by omega⟩ (by simp), u1, hu5, Fin.ext_iff]
  · simp [u14, u13, u12, u11, hu10_low ⟨6, by omega⟩ (by simp), u1, hu6, Fin.ext_iff]
  · simp [u14, u13, u12, u11, hu10_low ⟨8, by omega⟩ (by simp), u1, hu8, Fin.ext_iff]
  · simp [u14, u13, u12, u11, hu10_low ⟨10, by omega⟩ (by simp), u1, hu10, Fin.ext_iff]
  · simp [u14, u13, u12, u11, hu10_low ⟨7, by omega⟩ (by simp), u1, hu7, Fin.ext_iff]; omega
  · intro a ha
    have hne : 4 * H + 2 * a ≠ H + (2 ^ len + mask) := by
      have : 2 ^ len + mask < 2 ^ (len + 1) := by rw [pow_succ]; omega
      omega
    have hm : u14.mem (4 * H + 2 * a) = y_s.mem (4 * H + 2 * a) := by
      simp only [u14, u13, u12, u11, Data.set_mem, Data.write_mem, Function.update_of_ne hne]
      exact congrFun (congrArg Data.mem hu10_eq.symm) _
    rw [hm, show u14.regs ⟨7, by omega⟩ = 2 ^ len + mask by
      simp [u14, u13, u12, u11, hu10_low ⟨7, by omega⟩ (by simp), u1, hgen_new, Fin.ext_iff]]
    exact hy_s_st a ha
  · intro z hz
    have hlt_code : bitStringCode z < 2 ^ len :=
      (bitStringCode_lt z).trans_le (Nat.pow_le_pow_right Nat.two_pos (by omega))
    have hne : H + bitStringCode z ≠ H + (2 ^ len + mask) := by omega
    simp only [u14, u13, u12, u11, Data.set_mem, Data.write_mem, Function.update_of_ne hne]
    rw [hu10_mem_eq _ (by omega)]; exact hutab z hz
  · intro k hk
    by_cases hkm : k = mask
    · subst hkm; simp [u14, u13, z_cur]
    · have hne : H + (2 ^ len + k) ≠ H + (2 ^ len + mask) := by omega
      simp only [u14, u13, u12, u11, Data.set_mem, Data.write_mem, Function.update_of_ne hne]
      have hlt_k : 2 ^ len + k < 2 ^ (len + 1) := by rw [pow_succ]; omega
      rw [hu10_mem_eq _ (by omega)]; exact humask k (by omega)
  · intro a ha
    have hne : a ≠ H + (2 ^ len + mask) := by omega
    simp only [u14, u13, u12, u11, Data.set_mem, Data.write_mem, Function.update_of_ne hne]
    rw [hu10_mem_eq _ (by omega)]; exact hulo a ha
  · intro a ha1 ha2
    have hne : a ≠ H + (2 ^ len + mask) := by
      have : 2 ^ len + mask < 2 ^ (len + 1) := by rw [pow_succ]; omega
      omega
    simp only [u14, u13, u12, u11, Data.set_mem, Data.write_mem, Function.update_of_ne hne]
    rw [hu10_mem_eq _ (by omega)]; exact humid a ha1 ha2
  · have hne : 6 * H ≠ H + (2 ^ len + mask) := by
      have : 2 ^ len + mask < 2 ^ (len + 1) := by rw [pow_succ]; omega
      omega
    simp only [u14, u13, u12, u11, Data.set_mem, Data.write_mem, Function.update_of_ne hne]
    rw [hu10_mem_eq _ (by omega)]; exact hu6H

/-- Specification of `buildBitTableCode`: populates
`mem[H + bitStringCode z] = (O_Q (encBits z)).toNat`
for all `z` of length `≤ ν` in time `≤ 2^(ν + 1) * (11 * ν + 7 * T_max + r_Q + 40) + 20`. -/
theorem buildBitTableCode_exec {r_Q W w_log H nu T_max : ℕ}
    {Q : Set (List Bool)} {c_Q : Code .standard r_Q} {out_Q : Fin r_Q}
    {x : Data (r_Q + 26)}
    (hrf : c_Q.IsRandFree) (hH : H = 2 ^ w_log) (h6H : 6 * H ≤ 2 ^ W)
    (hpow_nu : 2 ^ (nu + 1) ≤ H)
    (h0 : x.regs ⟨0, by omega⟩ = H) (h1 : x.regs ⟨1, by omega⟩ = w_log)
    (h2 : x.regs ⟨2, by omega⟩ = nu)
    (hQ : ∀ z : List Bool, z.length ≤ nu →
      c_Q.Answers out_Q w_log (encBits z) (z ∈ Q) T_max)
    (hst0 : StampLe (4 * H) H 0 x.mem) :
    ∃ y : Data (r_Q + 26),
      ExecWithin W (buildBitTableCode c_Q out_Q) x y
        (2 ^ (nu + 1) * (11 * nu + 7 * T_max + r_Q + 40) + 20) ∧
      (∀ z : List Bool, z.length ≤ nu →
        y.mem (H + bitStringCode z) = (oracleOf Q encBits (encBits z)).toNat) ∧
      (∀ a < H, y.mem a = x.mem a) ∧
      (∀ a, 2 * H ≤ a → a < 4 * H → y.mem a = x.mem a) ∧
      y.mem (6 * H) = x.mem (6 * H) := by
  have hH_le : 2 ^ w_log ≤ H := by omega
  have hnu_lt : nu + 1 < H := lt_of_lt_of_le Nat.lt_two_pow_self hpow_nu
  have h1_fits : Fits W 1 := by
    have := Nat.one_le_two_pow (n := w_log); exact show 1 < 2 ^ W by omega
  have h2H_fits : Fits W (2 * H) := by
    have := Nat.one_le_two_pow (n := w_log); exact show 2 * H < 2 ^ W by omega
  have h4H_fits : Fits W (4 * H) := by
    have := Nat.one_le_two_pow (n := w_log); exact show 4 * H < 2 ^ W by omega
  have hnu1_fits : Fits W (nu + 1) := show nu + 1 < 2 ^ W by omega
  have h0' : x.regs 0 = H := h0
  have h1' : x.regs 1 = w_log := h1
  let s1 := x.set ⟨8, by omega⟩ 1
  let s2 := s1.set ⟨6, by omega⟩ (2 * H)
  let s3 := s2.set ⟨6, by omega⟩ (4 * H)
  let s4 := s3.set ⟨7, by omega⟩ 0
  let s5 := s4.set ⟨10, by omega⟩ (nu + 1)
  let s6 := s5.set ⟨3, by omega⟩ 0
  have hsetup : ExecWithin (B := .standard) W
      (.seq (.op (.const ⟨8, by omega⟩ 1))
        (.seq (.op (.bin .add ⟨6, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩))
          (.seq (.op (.bin .add ⟨6, by omega⟩ ⟨6, by omega⟩ ⟨6, by omega⟩))
            (.seq (.op (.const ⟨7, by omega⟩ 0))
              (.seq (.op (.bin .add ⟨10, by omega⟩ ⟨2, by omega⟩ ⟨8, by omega⟩))
                (.op (.const ⟨3, by omega⟩ 0))))))) x s6 6 := by
    have e1 : ExecWithin W (.op (Op.const (B := .standard) ⟨8, by omega⟩ 1)) x s1 1 :=
      ExecWithin.const h1_fits
    have e2 : ExecWithin W (.op (.bin .add ⟨6, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)) s1 s2 1 := by
      have ha : H + H = 2 * H := by omega
      simpa [s2, s1, h0', ha] using ExecWithin.bin (w := W) (x := s1) (f := .add)
        (d := ⟨6, by omega⟩) (i := ⟨0, by omega⟩) (j := ⟨0, by omega⟩)
        (by simpa [s1, h0', ha] using h2H_fits)
    have e3 : ExecWithin W (.op (.bin .add ⟨6, by omega⟩ ⟨6, by omega⟩ ⟨6, by omega⟩)) s2 s3 1 := by
      have ha : 2 * H + 2 * H = 4 * H := by omega
      simpa [s3, s2, ha] using ExecWithin.bin (w := W) (x := s2) (f := .add)
        (d := ⟨6, by omega⟩) (i := ⟨6, by omega⟩) (j := ⟨6, by omega⟩)
        (by simpa [s2, ha] using h4H_fits)
    have e4 : ExecWithin W (.op (Op.const (B := .standard) ⟨7, by omega⟩ 0)) s3 s4 1 :=
      ExecWithin.const (fits_zero W)
    have e5 : ExecWithin W (.op (.bin .add ⟨10, by omega⟩ ⟨2, by omega⟩ ⟨8,
      by omega⟩)) s4 s5 1 := by
      simpa [s5, s4, s3, s2, s1, h2] using ExecWithin.bin (w := W) (x := s4) (f := .add)
        (d := ⟨10, by omega⟩) (i := ⟨2, by omega⟩) (j := ⟨8, by omega⟩)
        (by simpa [s4, s3, s2, s1, h2] using hnu1_fits)
    have e6 : ExecWithin W (.op (Op.const (B := .standard) ⟨3, by omega⟩ 0)) s5 s6 1 :=
      ExecWithin.const (fits_zero W)
    exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
  let B_step := 11 * nu + 7 * T_max + r_Q + 26
  let OuterI (d : Data (r_Q + 26)) : Prop :=
    d.regs ⟨0, by omega⟩ = H ∧ d.regs ⟨1, by omega⟩ = w_log ∧ d.regs ⟨2, by omega⟩ = nu ∧
      d.regs ⟨6, by omega⟩ = 4 * H ∧ d.regs ⟨8, by omega⟩ = 1 ∧ d.regs ⟨10, by omega⟩ = nu + 1 ∧
      d.regs ⟨3, by omega⟩ ≤ nu + 1 ∧
      d.regs ⟨7, by omega⟩ = 2 ^ (d.regs ⟨3, by omega⟩) - 1 ∧
      StampLe (4 * H) H (d.regs ⟨7, by omega⟩) d.mem ∧
      (∀ z : List Bool, z.length < d.regs ⟨3, by omega⟩ →
        d.mem (H + bitStringCode z) = (oracleOf Q encBits (encBits z)).toNat) ∧
      (∀ a < H, d.mem a = x.mem a) ∧
      (∀ a, 2 * H ≤ a → a < 4 * H → d.mem a = x.mem a) ∧
      d.mem (6 * H) = x.mem (6 * H)
  let OuterΦ (d : Data (r_Q + 26)) : ℕ :=
    (2 ^ (nu + 1) - 2 ^ (d.regs ⟨3, by omega⟩)) * (B_step + 4) +
      (nu + 1 - d.regs ⟨3, by omega⟩) * 8
  have hI_s6 : OuterI s6 :=
    ⟨by simp [s6, s5, s4, s3, s2, s1, h0', Fin.ext_iff],
      by simp [s6, s5, s4, s3, s2, s1, h1', Fin.ext_iff],
      by simp [s6, s5, s4, s3, s2, s1, h2, Fin.ext_iff],
      by simp [s6, s5, s4, s3, Fin.ext_iff],
      by simp [s6, s5, s4, s3, s2, s1, Fin.ext_iff], by simp [s6, s5, Fin.ext_iff],
      by simp [s6], by simp [s6, s5, s4, Fin.ext_iff],
      by simpa [s6, s5, s4, s3, s2, s1, Fin.ext_iff] using hst0, fun z hz => by simp [s6] at hz,
      fun _ _ => rfl, fun _ _ _ => rfl, rfl⟩
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_potential (w := W)
    (cond := .lt ⟨3, by omega⟩ ⟨10, by omega⟩) (body := bbtOuterBody c_Q out_Q) OuterI OuterΦ
    (fun d hd hcond => by
      obtain ⟨hd0, hd1, hd2, hd6, hd8, hd10, _, hd7, hdst, hdtab, hdlo, hdmid, hd6H⟩ := hd
      have hd0' : d.regs 0 = H := hd0
      have hd1' : d.regs 1 = w_log := hd1
      set len := d.regs ⟨3, by omega⟩
      have hlen_le : len ≤ nu := by simp [Cond.Holds, hd10] at hcond; omega
      have hpow_le : 2 ^ len ≤ 2 ^ nu := Nat.pow_le_pow_right Nat.two_pos hlen_le
      have h2pow_le : 2 ^ (len + 1) ≤ 2 ^ (nu + 1) :=
        Nat.pow_le_pow_right Nat.two_pos (by omega)
      have hpow_fits : Fits W (1 <<< len) := by
        rw [Nat.shiftLeft_eq, one_mul]; exact show 2 ^ len < 2 ^ W by omega
      let d1 := d.set ⟨5, by omega⟩ (2 ^ len)
      let d2 := d1.set ⟨4, by omega⟩ 0
      have e_shift : ExecWithin W
          (.op (.bin .shiftLeft ⟨5, by omega⟩ ⟨8, by omega⟩ ⟨3, by omega⟩)) d d1 1 := by
        have hs : 1 <<< len = 2 ^ len := by simp [Nat.shiftLeft_eq]
        simpa [d1, hd8, hs, len] using ExecWithin.bin (w := W) (x := d) (f := .shiftLeft)
          (d := ⟨5, by omega⟩) (i := ⟨8, by omega⟩) (j := ⟨3, by omega⟩)
          (by simpa [hd8, len] using hpow_fits)
      have e_zero : ExecWithin W (.op (Op.const (B := .standard) ⟨4, by omega⟩ 0)) d1 d2 1 :=
        ExecWithin.const (fits_zero W)
      let InnerP (m : ℕ) (u : Data (r_Q + 26)) : Prop :=
        u.regs ⟨0, by omega⟩ = H ∧ u.regs ⟨1, by omega⟩ = w_log ∧ u.regs ⟨2, by omega⟩ = nu ∧
          u.regs ⟨3, by omega⟩ = len ∧ u.regs ⟨5, by omega⟩ = 2 ^ len ∧
          u.regs ⟨6, by omega⟩ = 4 * H ∧ u.regs ⟨8, by omega⟩ = 1 ∧ u.regs ⟨10, by omega⟩ = nu + 1 ∧
          u.regs ⟨7, by omega⟩ = 2 ^ len - 1 + m ∧
          StampLe (4 * H) H (u.regs ⟨7, by omega⟩) u.mem ∧
          (∀ z : List Bool, z.length < len →
            u.mem (H + bitStringCode z) = (oracleOf Q encBits (encBits z)).toNat) ∧
          (∀ k < m, u.mem (H + (2 ^ len + k)) =
            (oracleOf Q encBits (encBits (bitsOfMaskBool len k))).toNat) ∧
          (∀ a < H, u.mem a = x.mem a) ∧
          (∀ a, 2 * H ≤ a → a < 4 * H → u.mem a = x.mem a) ∧
          u.mem (6 * H) = x.mem (6 * H)
      have hIP0 : InnerP 0 d2 :=
        ⟨by simp [d2, d1, hd0', Fin.ext_iff], by simp [d2, d1, hd1', Fin.ext_iff],
          by simp [d2, d1, hd2, Fin.ext_iff], by simp [d2, d1, len, Fin.ext_iff],
          by simp [d2, d1, Fin.ext_iff], by simp [d2, d1, hd6, Fin.ext_iff],
          by simp [d2, d1, hd8, Fin.ext_iff], by simp [d2, d1, hd10, Fin.ext_iff],
          by simp [d2, d1, hd7, Fin.ext_iff],
          by simpa [d2, d1, Fin.ext_iff] using hdst, hdtab, fun _ hk => (Nat.not_lt_zero _ hk).elim,
          hdlo, hdmid, hd6H⟩
      obtain ⟨d3, hd3, hIP_end, _⟩ := ExecWithin.loop_count (w := W) (N := 2 ^ len) (T := B_step)
        (index := ⟨4, by omega⟩) (limit := ⟨5, by omega⟩) InnerP (fun u hu => hu.2.2.2.2.1)
        (fun u hu hmlt => by
          obtain ⟨hu0, hu1, hu2, hu3, hu5, hu6, hu8, hu10, hu7, hust, hutab, humask, hulo, humid,
            hu6H⟩ := hu
          obtain ⟨u14, hbody_ex, r0, r1, r2, r3, r5, r6, r8, r10, r7, rst, rtab, rmask, rlo, rmid,
            r6H, r4⟩ := bbtInnerBody_exec (x := x) hrf hH h6H hpow_nu hlen_le hmlt hQ
            hu0 hu1 hu2 hu3 rfl hu5 hu6 hu8 hu10 hu7 hust hutab humask hulo humid hu6H
          exact ⟨u14, hbody_ex, ⟨r0, r1, r2, r3, r5, r6, r8, r10, r7, rst, rtab, rmask, rlo, rmid,
            r6H⟩, r4⟩)
        (x := d2) (by simp [d2]) (by simpa [d2] using hIP0)
      obtain ⟨h30, h31, h32, h33, _, h36, h38, h310, h37, h3st, h3tab, h3mask, h3lo, h3mid, h36H⟩ :=
        hIP_end
      have h30' : d3.regs 0 = H := h30
      have h31' : d3.regs 1 = w_log := h31
      have hlen1_fits : Fits W (len + 1) := show len + 1 < 2 ^ W by omega
      let d4 := d3.set ⟨3, by omega⟩ (len + 1)
      have he_inc : ExecWithin W (.op (.bin .add ⟨3, by omega⟩ ⟨3, by omega⟩ ⟨8,
        by omega⟩)) d3 d4 1 := by
        simpa [d4, h33, h38] using ExecWithin.bin (w := W) (x := d3) (f := .add)
          (d := ⟨3, by omega⟩) (i := ⟨3, by omega⟩) (j := ⟨8, by omega⟩)
          (by simpa [h33, h38] using hlen1_fits)
      have hd2_4 : d2.regs ⟨4, by omega⟩ = 0 := by simp [d2]
      have hpow_sub : 2 ^ (nu + 1) - 2 ^ len = (2 ^ (nu + 1) - 2 ^ (len + 1)) + 2 ^ len := by
        have h2l : 2 ^ (len + 1) = 2 ^ len + 2 ^ len := by rw [pow_succ]; omega
        omega
      refine ⟨d4, 2 ^ len * (B_step + 2) + 5,
        (e_shift.seq (e_zero.seq (hd3.seq he_inc))).mono (by rw [hd2_4, Nat.sub_zero]; omega),
        ⟨by simp [d4, h30'], by simp [d4, h31'], by simp [d4, h32], by simp [d4, h36],
          by simp [d4, h38], by simp [d4, h310], by simp [d4]; omega,
          by simp [d4, h37, pow_succ]; have := Nat.one_le_two_pow (n := len); omega,
          by simpa [d4] using h3st, fun z hz => ?_, by simpa [d4] using h3lo,
          by simpa [d4] using h3mid, by simpa [d4] using h36H⟩, ?_⟩
      · simp only [d4, Data.set_regs, Function.update_self] at hz
        by_cases hlt' : z.length < len
        · exact h3tab z hlt'
        · have hzeq : z.length = len := by omega
          have hm_lt : bitStringMask z < 2 ^ len := hzeq ▸ bitStringMask_lt z
          have hcode_eq : bitStringCode z = 2 ^ len + bitStringMask z := by
            rw [bitStringCode_eq_two_pow_add_mask, hzeq]
          have hbm : bitsOfMaskBool len (bitStringMask z) = z := by
            rw [← hzeq]; exact bitsOfMaskBool_bitStringMask z
          simpa [d4, hcode_eq, hbm] using h3mask (bitStringMask z) hm_lt
      · have hd4_3 : d4.regs ⟨3, by omega⟩ = len + 1 := by simp [d4]
        change 2 ^ len * (B_step + 2) + 5 + 2 +
          ((2 ^ (nu + 1) - 2 ^ (d4.regs ⟨3, by omega⟩)) * (B_step + 4) +
            (nu + 1 - d4.regs ⟨3, by omega⟩) * 8) ≤
          (2 ^ (nu + 1) - 2 ^ len) * (B_step + 4) + (nu + 1 - len) * 8
        rw [hd4_3, hpow_sub, Nat.add_mul]
        have hlen_sub : nu + 1 - len = (nu + 1 - (len + 1)) + 1 := by omega
        rw [hlen_sub, Nat.add_mul, Nat.one_mul]
        have hmul_le : 2 ^ len * (B_step + 2) + 2 ^ len * 2 ≤ 2 ^ len * (B_step + 4) := by
          rw [← Nat.mul_add]
        have h1 : 1 ≤ 2 ^ len := Nat.one_le_two_pow
        have h2l : 2 ≤ 2 ^ len * 2 := by omega
        omega) hI_s6
  obtain ⟨_, _, _, _, _, hy10, hy3le, _, _, hytab, hylo, hymid, hy6H⟩ := hIy
  have hy3 : y.regs ⟨3, by omega⟩ = nu + 1 := by
    simp only [Cond.Holds, hy10] at hstop; omega
  have htime_le : 6 + (OuterΦ s6 + 2) ≤ 2 ^ (nu + 1) * (11 * nu + 7 * T_max + r_Q + 40) + 20 := by
    dsimp only [OuterΦ, s6, B_step]
    simp only [Data.set_regs, Function.update_self, pow_zero]
    have hB : 11 * nu + 7 * T_max + r_Q + 26 + 4 = 11 * nu + 7 * T_max + r_Q + 30 := by omega
    rw [hB]
    have hnu_pow : nu + 1 ≤ 2 ^ (nu + 1) := le_of_lt Nat.lt_two_pow_self
    have hsub1 : 2 ^ (nu + 1) - 1 ≤ 2 ^ (nu + 1) := Nat.sub_le _ _
    have h1 : (2 ^ (nu + 1) - 1) * (11 * nu + 7 * T_max + r_Q + 30) ≤
        2 ^ (nu + 1) * (11 * nu + 7 * T_max + r_Q + 30) := Nat.mul_le_mul_right _ hsub1
    have h2 : (nu + 1 - 0) * 8 ≤ 2 ^ (nu + 1) * 8 := Nat.mul_le_mul_right 8 (by omega)
    have h3 : 2 ^ (nu + 1) * (11 * nu + 7 * T_max + r_Q + 30) + 2 ^ (nu + 1) * 8 =
        2 ^ (nu + 1) * (11 * nu + 7 * T_max + r_Q + 38) := by ring
    have h4 : 2 ^ (nu + 1) * (11 * nu + 7 * T_max + r_Q + 38) ≤
        2 ^ (nu + 1) * (11 * nu + 7 * T_max + r_Q + 40) := Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨y, (hsetup.seq hy).mono htime_le, fun z hz => hytab z (by omega), hylo, hymid, hy6H⟩

/-! ### Stamped Oracle Wrapper (`wrapStampedOracle`) -/

/-- Zero caller virtual registers `0 .. r_A - 1` of a `compileOracleStamped` program in `r_A`
instructions before running `base`. -/
def zeroStampedCaller {r_A r_s : ℕ} (base : Code .standard ((r_A + 6) + (r_s + 5))) :
    Code .standard ((r_A + 6) + (r_s + 5)) :=
  (List.finRange r_A).foldr
    (fun i acc => .seq (.op (.const (stampedCallerReg (stampVirtReg i)) 0)) acc) base

theorem isRandFree_zeroStampedCaller {r_A r_s : ℕ}
    {base : Code .standard ((r_A + 6) + (r_s + 5))} (hbase : base.IsRandFree) :
    (zeroStampedCaller base).IsRandFree := by
  unfold zeroStampedCaller
  induction List.finRange r_A with
  | nil => exact hbase
  | cons _ _ ih => exact ⟨trivial, ih⟩

theorem zeroStampedCaller_exec {r_A r_s W T : ℕ}
    {base : Code .standard ((r_A + 6) + (r_s + 5))} {x y : Data ((r_A + 6) + (r_s + 5))}
    (h : ExecWithin W base ⟨fun k => if k.val < r_A then 0 else x.regs k, x.mem⟩ y T) :
    ExecWithin W (zeroStampedCaller base) x y (r_A + T) := by
  have haux : ∀ (l : List (Fin r_A)) (s : Data ((r_A + 6) + (r_s + 5))),
      ExecWithin W base
        ⟨fun k => if hlt : k.val < r_A then
            if (⟨k.val, hlt⟩ : Fin r_A) ∈ l then 0 else s.regs k
          else s.regs k, s.mem⟩ y T →
      ExecWithin W (l.foldr
        (fun i acc => .seq (.op (.const (stampedCallerReg (stampVirtReg i)) 0)) acc) base)
        s y (l.length + T) := by
    intro l
    induction l with
    | nil =>
      intro s hs
      simpa only [List.foldr_nil, List.length_nil, Nat.zero_add, List.not_mem_nil,
        ↓reduceIte, dite_eq_ite, ite_self] using hs
    | cons i l ih =>
      intro s hs
      let idx : Fin ((r_A + 6) + (r_s + 5)) := stampedCallerReg (stampVirtReg i)
      have h1 : ExecWithin W (.op (Op.const (B := .standard) idx 0)) s (s.set idx 0) 1 :=
        ExecWithin.const (fits_zero W)
      have h2 := ih (s.set idx 0) (by
        convert hs using 2
        · ext k
          by_cases hlt : k.val < r_A
          · simp only [hlt, ↓reduceDIte, List.mem_cons, Data.set_regs]
            by_cases hk : (⟨k.val, hlt⟩ : Fin r_A) = i
            · have hkeq : k = idx := Fin.ext (by
                have := congrArg Fin.val hk
                simpa [idx] using this)
              subst hkeq; simp [hk]
            · have hkne : k ≠ idx := fun heq =>
                hk (Fin.ext (by
                  have := congrArg Fin.val heq
                  simpa [idx] using this))
              simp [hk, Function.update_of_ne hkne]
          · have hkne : k ≠ idx := fun heq => by
              have := congrArg Fin.val heq
              simp [idx] at this; omega
            simp [hlt, Data.set_regs, Function.update_of_ne hkne]
        · rfl)
      exact (h1.seq h2).mono (by simp; omega)
  have hmain := haux (List.finRange r_A) x (by
    convert h using 2
    ext k
    by_cases hlt : k.val < r_A
    · simp [hlt, List.mem_finRange]
    · simp [hlt])
  simpa only [zeroStampedCaller, List.length_finRange] using hmain

private def wsoCopyReg {r_A r_s : ℕ} (j : Fin 9) : Fin (((r_A + 6) + (r_s + 5) + 18) + 3) :=
  ⟨9 + j.val, by omega⟩

private def wsoOracleReg {r_A r_s : ℕ} (j : Fin ((r_A + 6) + (r_s + 5))) :
    Fin (((r_A + 6) + (r_s + 5) + 18) + 3) :=
  ⟨18 + j.val, by omega⟩

private theorem wsoCopyReg_injective {r_A r_s : ℕ} :
    Function.Injective (wsoCopyReg (r_A := r_A) (r_s := r_s)) := by
  intro a b h; have hv := congrArg Fin.val h; simp only [wsoCopyReg] at hv; exact Fin.ext (by omega)

private theorem wsoOracleReg_injective {r_A r_s : ℕ} :
    Function.Injective (wsoOracleReg (r_A := r_A) (r_s := r_s)) := by
  intro a b h; have hv :=
    congrArg Fin.val h; simp only [wsoOracleReg] at hv; exact Fin.ext (by omega)

/-- Wrap an oracle program `c_A` + stamped lookup `sub` into an oracle-compilation subroutine for
`compileOracle` operating in stamped bank `[2*H, 4*H)`.
Args: `0=qBase, 1=qLen`; persistent: `3=H, 4=w_log, 5=genA`; output: `2=ans`. -/
def wrapStampedOracle {r_A r_s : ℕ} (c_A : OracleCode .standard r_A) (out_A : Fin r_A)
    (sub : Code .standard (r_s + 5)) : Code .standard (((r_A + 6) + (r_s + 5) + 18) + 3) :=
  let rTot := ((r_A + 6) + (r_s + 5) + 18) + 3
  let r0 : Fin rTot := ⟨0, by omega⟩
  let r1 : Fin rTot := ⟨1, by omega⟩
  let r2 : Fin rTot := ⟨2, by omega⟩
  let r3 : Fin rTot := ⟨3, by omega⟩
  let r4 : Fin rTot := ⟨4, by omega⟩
  let r5 : Fin rTot := ⟨5, by omega⟩
  let r6 : Fin rTot := ⟨6, by omega⟩
  let r7 : Fin rTot := ⟨7, by omega⟩
  .seq
    (ram[ r7 ← #1; r5 ← r5 + r7; r6 ← r3 + r3 ])
    (.seq (.op (.copy (wsoCopyReg 0) r0))
      (.seq (.op (.copy (wsoCopyReg 1) r1))
        (.seq (.op (.copy (wsoCopyReg 2) r6))
          (.seq (.op (.copy (wsoCopyReg 3) r5))
            (.seq (copyInitToStampedCode.rename wsoCopyReg)
              (.seq (.op (.copy (wsoOracleReg (stampedCallerReg stampBaseReg)) r6))
                (.seq (.op (.copy (wsoOracleReg (stampedCallerReg stampGenReg)) r5))
                  (.seq (.op (.copy (wsoOracleReg (stampedCallerReg stampWidthReg)) r4))
                    (.seq ((zeroStampedCaller (compileOracleStamped c_A sub)).rename wsoOracleReg)
                      (.op (.copy r2
                        (wsoOracleReg (stampedCallerReg (stampVirtReg out_A))))))))))))))

theorem isRandFree_wrapStampedOracle {r_A r_s : ℕ} (c_A : OracleCode .standard r_A)
    (out_A : Fin r_A) {sub : Code .standard (r_s + 5)} (hsub : sub.IsRandFree) :
    (wrapStampedOracle c_A out_A sub).IsRandFree :=
  ⟨⟨trivial, trivial, trivial⟩, trivial, trivial, trivial, trivial,
    isRandFree_rename isRandFree_copyInitToStampedCode, trivial, trivial, trivial,
    isRandFree_rename (isRandFree_zeroStampedCaller (isRandFree_compileOracleStamped c_A hsub)),
    trivial⟩

/-- Execution specification of `wrapStampedOracle`. -/
theorem wrapStampedOracle_exec {r_A r_s W w_log H gen₀ t_A : ℕ}
    {O : List ℕ → Bool} {c_A : OracleCode .standard r_A} {out_A : Fin r_A}
    {sub : Code .standard (r_s + 5)} {q : List ℕ} {y_A : Data r_A} {qs_A : List (List ℕ)}
    {T_sub : List ℕ → ℕ}
    {x : Data (((r_A + 6) + (r_s + 5) + 18) + 3)}
    (hH : 2 ^ w_log ≤ H) (h4H : 4 * H ≤ 2 ^ W)
    (hgenW : Fits W (gen₀ + 1)) (hq_fits : InputFits w_log q)
    (hrun : OracleExec w_log O c_A (.init q) y_A t_A qs_A)
    (hsub : ∀ (qi : List ℕ) (xs : Data (r_s + 5)),
      qi ∈ qs_A →
      xs.regs ⟨0, by omega⟩ + qi.length < 2 ^ w_log →
      xs.regs ⟨1, by omega⟩ = qi.length →
      xs.regs ⟨2, by omega⟩ = 2 * H →
      xs.regs ⟨3, by omega⟩ = gen₀ + 1 →
      qi = (List.range qi.length).map
        (fun i => stampedRead (2 * H) (gen₀ + 1) xs.mem (xs.regs ⟨0, by omega⟩ + i)) →
      (∀ p, ¬(2 * H ≤ p ∧ p < 4 * H) → xs.mem p = x.mem p) →
      ∃ z : Data (r_s + 5),
        ExecWithin W sub xs z (T_sub qi) ∧
        z.regs ⟨4, by omega⟩ = (O qi).toNat ∧
        z.mem = xs.mem)
    (h0 : x.regs ⟨0, by omega⟩ + q.length < H)
    (h1 : x.regs ⟨1, by omega⟩ = q.length)
    (hq_eq : q = (List.range q.length).map fun i => x.mem (x.regs ⟨0, by omega⟩ + i))
    (h3 : x.regs ⟨3, by omega⟩ = H) (h4 : x.regs ⟨4, by omega⟩ = w_log)
    (h5 : x.regs ⟨5, by omega⟩ = gen₀)
    (hst : StampLe (2 * H) H gen₀ x.mem) :
    ∃ z : Data (((r_A + 6) + (r_s + 5) + 18) + 3),
      ExecWithin W (wrapStampedOracle c_A out_A sub) x z
        (11 * q.length + 7 * t_A + (qs_A.map fun qi => T_sub qi + 5).sum + r_A + 20) ∧
      z.regs ⟨2, by omega⟩ = y_A.regs out_A ∧
      z.regs ⟨3, by omega⟩ = H ∧
      z.regs ⟨4, by omega⟩ = w_log ∧
      z.regs ⟨5, by omega⟩ = gen₀ + 1 ∧
      StampLe (2 * H) H (gen₀ + 1) z.mem ∧
      ∀ p, ¬(2 * H ≤ p ∧ p < 4 * H) → z.mem p = x.mem p := by
  have h1_fits : Fits W 1 := by
    have := Nat.one_le_two_pow (n := w_log); exact show 1 < 2 ^ W by omega
  have h2H_fits : Fits W (2 * H) := by
    have := Nat.one_le_two_pow (n := w_log); exact show 2 * H < 2 ^ W by omega
  let rTot := ((r_A + 6) + (r_s + 5) + 18) + 3
  let x1 := x.set ⟨7, by omega⟩ 1
  let x2 := x1.set ⟨5, by omega⟩ (gen₀ + 1)
  let x3 := x2.set ⟨6, by omega⟩ (2 * H)
  have he123 : ExecWithin (B := .standard) W
      (.seq (.op (.const ⟨7, by omega⟩ 1))
        (.seq (.op (.bin .add ⟨5, by omega⟩ ⟨5, by omega⟩ ⟨7, by omega⟩))
          (.op (.bin .add ⟨6, by omega⟩ ⟨3, by omega⟩ ⟨3, by omega⟩)))) x x3 3 := by
    have s1 : ExecWithin W (.op (Op.const (B := .standard) ⟨7, by omega⟩ 1)) x x1 1 :=
      ExecWithin.const h1_fits
    have s2 : ExecWithin W (.op (.bin .add ⟨5, by omega⟩ ⟨5, by omega⟩ ⟨7, by omega⟩)) x1 x2 1 := by
      simpa [x2, x1, h5] using ExecWithin.bin (w := W) (x := x1) (f := .add)
        (d := ⟨5, by omega⟩) (i := ⟨5, by omega⟩) (j :=
          ⟨7, by omega⟩) (by simpa [x1, h5] using hgenW)
    have s3 : ExecWithin W (.op (.bin .add ⟨6, by omega⟩ ⟨3, by omega⟩ ⟨3, by omega⟩)) x2 x3 1 := by
      have ha : H + H = 2 * H := by omega
      simpa [x3, x2, x1, h3, ha] using ExecWithin.bin (w := W) (x := x2) (f := .add)
        (d := ⟨6, by omega⟩) (i := ⟨3, by omega⟩) (j :=
          ⟨3, by omega⟩) (by simpa [x2, x1, h3, ha] using h2H_fits)
    exact s1.seq (s2.seq s3)
  let x4 := x3.set (wsoCopyReg 0) (x3.regs ⟨0, by omega⟩)
  let x5 := x4.set (wsoCopyReg 1) (x4.regs ⟨1, by omega⟩)
  let x6 := x5.set (wsoCopyReg 2) (x5.regs ⟨6, by omega⟩)
  let x7 := x6.set (wsoCopyReg 3) (x6.regs ⟨5, by omega⟩)
  have hx7_r : ∀ j : Fin rTot, j.val < 9 → x7.regs j = x3.regs j := fun j hj => by
    have hne : ∀ k : Fin 9, j ≠ wsoCopyReg k := fun k h => by
      have := congrArg Fin.val h; simp [wsoCopyReg] at this; omega
    simp [x7, x6, x5, x4, hne]
  have hx7_c0 : (x7.comap wsoCopyReg).regs 0 = x.regs ⟨0, by omega⟩ := by
    simp [x7, x6, x5, x4, x3, x2, x1, wsoCopyReg, Fin.ext_iff]
  have hx7_c1 : (x7.comap wsoCopyReg).regs 1 = q.length := by
    have h1_reg : x.regs 1 = q.length := h1
    simp [x7, x6, x5, x4, x3, x2, x1, wsoCopyReg, Fin.ext_iff, h1_reg]
  have hx7_c2 : (x7.comap wsoCopyReg).regs 2 = 2 * H := by
    simp [x7, x6, x5, x4, x3, wsoCopyReg, Fin.ext_iff]
  have hx7_c3 : (x7.comap wsoCopyReg).regs 3 = gen₀ + 1 := by
    simp [x7, x6, x5, x4, x3, x2, wsoCopyReg, Fin.ext_iff]
  obtain ⟨c_out, hc_out, hc_rep, hc_st, hc_fr⟩ :=
    copyInitToStampedCode_exec (W := W) (base := 2 * H) (H := H) (gen₀ := gen₀) (gen := gen₀ + 1)
      (x := x7.comap wsoCopyReg) (by omega)
      (by rw [hx7_c1]; exact lt_of_le_of_lt (Nat.le_add_left _ _) h0)
      (by rw [hx7_c0, hx7_c1]; omega) (by omega) hx7_c2 hx7_c3 hst
  have hq_eq' : (List.range ((x7.comap wsoCopyReg).regs 1)).map
      (fun i => (x7.comap wsoCopyReg).mem ((x7.comap wsoCopyReg).regs 0 + i)) = q := by
    simpa only [Data.comap_mem, hx7_c0, hx7_c1, x7, x6, x5, x4, x3, x2, x1, Data.set_mem] using
      hq_eq.symm
  rw [hq_eq'] at hc_rep
  obtain ⟨x8, hx8, hx8_eq, hx8_fr⟩ :=
    ExecWithin.rename_post (wsoCopyReg_injective (r_A := r_A) (r_s := r_s)) ⟨c_out, hc_out, rfl⟩
  have hx8_mem : x8.mem = c_out.mem := congrArg Data.mem hx8_eq.symm
  have hx8_r : ∀ j : Fin rTot, j.val < 9 → x8.regs j = x3.regs j := fun j hj => by
    have hne : ∀ k : Fin 9, wsoCopyReg (r_A := r_A) (r_s := r_s) k ≠ j := fun k h => by
      have := congrArg Fin.val h; simp [wsoCopyReg] at this; omega
    exact (hx8_fr j hne).trans (hx7_r j hj)
  let x9 := x8.set (wsoOracleReg (stampedCallerReg stampBaseReg)) (x8.regs ⟨6, by omega⟩)
  let x10 := x9.set (wsoOracleReg (stampedCallerReg stampGenReg)) (x9.regs ⟨5, by omega⟩)
  let x11 := x10.set (wsoOracleReg (stampedCallerReg stampWidthReg)) (x10.regs ⟨4, by omega⟩)
  let x11_o : Data ((r_A + 6) + (r_s + 5)) :=
    ⟨fun k => if k.val < r_A then 0 else (x11.comap wsoOracleReg).regs k, x11.mem⟩
  have hx11_B : x11_o.regs (stampedCallerReg stampBaseReg) = 2 * H := by
    have hlt : ¬(stampedCallerReg (r_s := r_s) (stampBaseReg (r := r_A))).val < r_A := by simp
    simp only [x11_o, hlt, ↓reduceIte, Data.comap_regs]
    have h1' : wsoOracleReg (r_A := r_A) (r_s := r_s) (stampedCallerReg stampBaseReg) ≠
        wsoOracleReg (stampedCallerReg stampGenReg) :=
      wsoOracleReg_injective.ne (stampedCallerReg_injective.ne stampBaseReg_ne_stampGenReg)
    have h2' : wsoOracleReg (r_A := r_A) (r_s := r_s) (stampedCallerReg stampBaseReg) ≠
        wsoOracleReg (stampedCallerReg stampWidthReg) :=
      wsoOracleReg_injective.ne (stampedCallerReg_injective.ne stampBaseReg_ne_stampWidthReg)
    simp only [x11, x10, x9, Data.set_regs, Function.update_of_ne h1', Function.update_of_ne h2',
      Function.update_self, hx8_r ⟨6, by omega⟩ (by simp), x3]
  have hx11_G : x11_o.regs (stampedCallerReg stampGenReg) = gen₀ + 1 := by
    have hlt : ¬(stampedCallerReg (r_s := r_s) (stampGenReg (r := r_A))).val < r_A := by simp
    simp only [x11_o, hlt, ↓reduceIte, Data.comap_regs]
    have h2' : wsoOracleReg (r_A := r_A) (r_s := r_s) (stampedCallerReg stampGenReg) ≠
        wsoOracleReg (stampedCallerReg stampWidthReg) :=
      wsoOracleReg_injective.ne (stampedCallerReg_injective.ne stampGenReg_ne_stampWidthReg)
    have hne5 : (⟨5, by omega⟩ : Fin rTot) ≠ wsoOracleReg (stampedCallerReg stampBaseReg) :=
      Fin.ne_of_val_ne (by simp [wsoOracleReg]; omega)
    have h56 : (⟨5, by omega⟩ : Fin rTot) ≠ ⟨6, by omega⟩ := by simp [Fin.ext_iff]
    simp only [x11, x10, x9, Data.set_regs, Function.update_of_ne h2', Function.update_of_ne hne5,
      Function.update_self, hx8_r ⟨5, by omega⟩ (by simp), x3, Function.update_of_ne h56, x2]
  have hx11_W : x11_o.regs (stampedCallerReg stampWidthReg) = w_log := by
    have hlt : ¬(stampedCallerReg (r_s := r_s) (stampWidthReg (r := r_A))).val < r_A := by simp
    simp only [x11_o, hlt, ↓reduceIte, Data.comap_regs]
    have hne4b : (⟨4, by omega⟩ : Fin rTot) ≠ wsoOracleReg (stampedCallerReg stampBaseReg) :=
      Fin.ne_of_val_ne (by simp [wsoOracleReg]; omega)
    have hne4g : (⟨4, by omega⟩ : Fin rTot) ≠ wsoOracleReg (stampedCallerReg stampGenReg) :=
      Fin.ne_of_val_ne (by simp [wsoOracleReg]; omega)
    have h46 : (⟨4, by omega⟩ : Fin rTot) ≠ ⟨6, by omega⟩ := by simp [Fin.ext_iff]
    have h45 : (⟨4, by omega⟩ : Fin rTot) ≠ ⟨5, by omega⟩ := by simp [Fin.ext_iff]
    have h47 : (⟨4, by omega⟩ : Fin rTot) ≠ ⟨7, by omega⟩ := by simp [Fin.ext_iff]
    simp only [x11, x10, x9, Data.set_regs, Function.update_of_ne hne4b,
      Function.update_of_ne hne4g, Function.update_self, hx8_r ⟨4, by omega⟩ (by simp), x3,
      Function.update_of_ne h46, x2, Function.update_of_ne h45, x1, Function.update_of_ne h47, h4]
  have hx11_virt :
      x11_o.regs ∘ (stampedCallerReg ∘ stampVirtReg) = (Data.init q (r := r_A)).regs := by
    funext i; simp [x11_o, Data.init_regs]
  have hx11_rep : MemRepresents (2 * H) H (gen₀ + 1) x11_o.mem (Data.init q (r := r_A)).mem := by
    intro a ha; rw [show x11_o.mem = c_out.mem by simp [x11_o, x11, x10, x9, hx8_mem]]
    exact hc_rep a ha
  have hx11_st : StampLe (2 * H) H (gen₀ + 1) x11_o.mem := by
    rw [show x11_o.mem = c_out.mem by simp [x11_o, x11, x10, x9, hx8_mem]]; exact hc_st
  have hx11_fr : ∀ p, ¬(2 * H ≤ p ∧ p < 4 * H) → x11_o.mem p = x.mem p := fun p hp => by
    rw [show x11_o.mem p = c_out.mem p by simp [x11_o, x11, x10, x9, hx8_mem]]
    exact hc_fr p (by omega)
  obtain ⟨y_o, hy_o, _, _, _, hy_o_virt, _, hy_o_st, hy_o_fr⟩ :=
    compileOracleStamped_exec (W := W) (base := 2 * H) (H := H) (gen := gen₀ + 1)
      (x := x11_o) (Data.Bounded.init hq_fits) hH (by omega) hrun
      (fun qi xs hqi hbl hql hqb hqg hqrep hxs_fr =>
        hsub qi xs hqi hbl hql hqb hqg hqrep
          (fun p hp => (hxs_fr p (by omega)).trans (hx11_fr p hp)))
      hx11_B hx11_G hx11_W hx11_virt hx11_rep hx11_st
  obtain ⟨x12, hx12, hx12_eq, hx12_fr⟩ :=
    ExecWithin.rename_post (wsoOracleReg_injective (r_A := r_A) (r_s := r_s))
      ⟨y_o, zeroStampedCaller_exec hy_o, rfl⟩
  have hx12_r : ∀ j : Fin rTot, j.val < 9 → x12.regs j = x3.regs j := fun j hj => by
    have hneO : ∀ k : Fin ((r_A + 6) + (r_s + 5)), wsoOracleReg (r_A := r_A) (r_s := r_s) k ≠ j :=
      fun k h => by have := congrArg Fin.val h; simp [wsoOracleReg] at this; omega
    have h11j : x11.regs j = x8.regs j := by
      simp only [x11, x10, x9, Data.set_regs,
        Function.update_of_ne (hneO (stampedCallerReg stampBaseReg)).symm,
        Function.update_of_ne (hneO (stampedCallerReg stampGenReg)).symm,
        Function.update_of_ne (hneO (stampedCallerReg stampWidthReg)).symm]
    exact (hx12_fr j hneO).trans (h11j.trans (hx8_r j hj))
  let z := x12.set ⟨2, by omega⟩ (x12.regs (wsoOracleReg (stampedCallerReg (stampVirtReg out_A))))
  have hexec : ExecWithin W (wrapStampedOracle c_A out_A sub) x z
      (11 * q.length + 7 * t_A + (qs_A.map fun qi => T_sub qi + 5).sum + r_A + 20) :=
    (he123.seq (ExecWithin.copy.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
      (ExecWithin.copy.seq (hx8.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
        (ExecWithin.copy.seq (hx12.seq ExecWithin.copy)))))))))).mono (by
      simp only [hx7_c1]; omega)
  refine ⟨z, hexec, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1' := congrFun (congrArg Data.regs hx12_eq.symm) (stampedCallerReg (stampVirtReg out_A))
    have h2' := congrFun hy_o_virt out_A
    simp only [z, Data.set_regs, Function.update_self]
    exact (show x12.regs (wsoOracleReg (stampedCallerReg (stampVirtReg out_A))) =
      y_o.regs (stampedCallerReg (stampVirtReg out_A)) from h1').trans h2'
  · simp [z, hx12_r ⟨3, by omega⟩ (by simp), x3, x2, x1, h3, Fin.ext_iff]
  · simp [z, hx12_r ⟨4, by omega⟩ (by simp), x3, x2, x1, h4, Fin.ext_iff]
  · simp [z, hx12_r ⟨5, by omega⟩ (by simp), x3, x2, Fin.ext_iff]
  · have hm : z.mem = y_o.mem := congrArg Data.mem hx12_eq.symm
    rw [hm]; exact hy_o_st
  · intro p hp
    have hm : z.mem = y_o.mem := congrArg Data.mem hx12_eq.symm
    rw [hm, hy_o_fr p (by omega), hx11_fr p hp]

/-! ### Combined Method-of-Four-Russians Word-RAM Program -/

/-- Register embedding for `nuCode` inside `fourRussiansProg`. -/
@[expose] def frNuReg {r_nu r_Q r_B r_A : ℕ} (j : Fin (r_nu + 2)) :
    Fin (8 + (r_nu + 2) + (r_Q + 26) + ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))) :=
  ⟨8 + j.val, by omega⟩

/-- Register embedding for `buildBitTableCode` inside `fourRussiansProg`. -/
@[expose] def frBuildReg {r_nu r_Q r_B r_A : ℕ} (j : Fin (r_Q + 26)) :
    Fin (8 + (r_nu + 2) + (r_Q + 26) + ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))) :=
  ⟨8 + (r_nu + 2) + j.val, by omega⟩

/-- Register embedding for `compileOracle c_B (wrapStampedOracle ...)` inside `fourRussiansProg`. -/
@[expose] def frCompReg {r_nu r_Q r_B r_A : ℕ}
    (j : Fin ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))) :
    Fin (8 + (r_nu + 2) + (r_Q + 26) + ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))) :=
  ⟨8 + (r_nu + 2) + (r_Q + 26) + j.val, by omega⟩

theorem frNuReg_injective {r_nu r_Q r_B r_A : ℕ} :
    Function.Injective (frNuReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)) := by
  intro a b h
  have hv := congrArg Fin.val h; simp only [frNuReg] at hv; exact Fin.ext (by omega)

theorem frBuildReg_injective {r_nu r_Q r_B r_A : ℕ} :
    Function.Injective (frBuildReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)) := by
  intro a b h
  have hv := congrArg Fin.val h; simp only [frBuildReg] at hv; exact Fin.ext (by omega)

theorem frCompReg_injective {r_nu r_Q r_B r_A : ℕ} :
    Function.Injective (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)) := by
  intro a b h
  have hv := congrArg Fin.val h; simp only [frCompReg] at hv; exact Fin.ext (by omega)

theorem frNuReg_val {r_nu r_Q r_B r_A : ℕ} (j : Fin (r_nu + 2)) :
    (frNuReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A) j).val = 8 + j.val := rfl

theorem frBuildReg_val {r_nu r_Q r_B r_A : ℕ} (j : Fin (r_Q + 26)) :
    (frBuildReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A) j).val =
      8 + (r_nu + 2) + j.val := rfl

theorem frCompReg_val {r_nu r_Q r_B r_A : ℕ}
    (j : Fin ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))) :
    (frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A) j).val =
      8 + (r_nu + 2) + (r_Q + 26) + j.val := rfl

/-- Combined Method-of-Four-Russians Word-RAM program: computes `H = 2^(W-3)` and `w_log = W-3`,
runs `nuCode` on `s = mem[0]` to obtain `ν`, stores `mem[6*H] := ν`, builds the lookup table for
`Q` via `buildBitTableCode`, and runs `c_B` with oracle calls routed through
`wrapStampedOracle c_A out_A bitTableLookupCode`. Output is written to register `6`. -/
@[expose] def fourRussiansProg {r_nu r_Q r_B r_A : ℕ}
    (nuCode : Code .standard (r_nu + 2))
    (c_Q : Code .standard r_Q) (out_Q : Fin r_Q)
    (c_B : OracleCode .standard r_B) (out_B : Fin r_B)
    (c_A : OracleCode .standard r_A) (out_A : Fin r_A) :
    Code .standard
      (8 + (r_nu + 2) + (r_Q + 26) + ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))) :=
  let rTot := 8 + (r_nu + 2) + (r_Q + 26) + ((r_B + 1) + (((r_A + 6) + (16 + 5) + 18) + 3))
  let rH : Fin rTot := ⟨0, by omega⟩
  let rW : Fin rTot := ⟨1, by omega⟩
  let rS : Fin rTot := ⟨2, by omega⟩
  let rNu : Fin rTot := ⟨3, by omega⟩
  let r4 : Fin rTot := ⟨4, by omega⟩
  let r5 : Fin rTot := ⟨5, by omega⟩
  let rOut : Fin rTot := ⟨6, by omega⟩
  let nuReg := frNuReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
  let buildReg := frBuildReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
  let compReg := frCompReg (r_nu := r_nu) (r_Q := r_Q) (r_B := r_B) (r_A := r_A)
  let stage01 := ram[
    rW ← width%;
    r5 ← #3;
    rW ← rW - r5;
    r5 ← #1;
    rH ← r5 <<< rW;
    r4 ← #0;
    rS ← *r4
  ]
  let stageStoreNu := ram[
    r4 ← rH + rH;
    r5 ← r4 + r4;
    r4 ← r4 + r5;
    *r4 ← rNu
  ]
  let subA := wrapStampedOracle c_A out_A bitTableLookupCode
  .seq stage01
    (.seq (.op (.copy (nuReg 0) rS))
      (.seq (nuCode.rename nuReg)
        (.seq (.op (.copy rNu (nuReg 1)))
          (.seq stageStoreNu
            (.seq (.op (.copy (buildReg ⟨0, by omega⟩) rH))
              (.seq (.op (.copy (buildReg ⟨1, by omega⟩) rW))
                (.seq (.op (.copy (buildReg ⟨2, by omega⟩) rNu))
                  (.seq ((buildBitTableCode c_Q out_Q).rename buildReg)
                    (.seq (.op (.copy (compReg callerWidthReg) rW))
                      (.seq (.op (.copy (compReg (subReg ⟨3, by omega⟩)) rH))
                        (.seq (.op (.copy (compReg (subReg ⟨4, by omega⟩)) rW))
                          (.seq ((compileOracle c_B subA).rename compReg)
                            (.op (.copy rOut (compReg (callerReg out_B))))))))))))))))

theorem isRandFree_fourRussiansProg {r_nu r_Q r_B r_A : ℕ}
    {nuCode : Code .standard (r_nu + 2)} {c_Q : Code .standard r_Q} (out_Q : Fin r_Q)
    (c_B : OracleCode .standard r_B) (out_B : Fin r_B)
    (c_A : OracleCode .standard r_A) (out_A : Fin r_A)
    (hnu : nuCode.IsRandFree) (hQ : c_Q.IsRandFree) :
    (fourRussiansProg nuCode c_Q out_Q c_B out_B c_A out_A).IsRandFree :=
  ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial,
    isRandFree_rename hnu, trivial, ⟨trivial, trivial, trivial, trivial⟩,
    trivial, trivial, trivial, isRandFree_rename (isRandFree_buildBitTableCode out_Q hQ),
    trivial, trivial, trivial,
    isRandFree_rename (isRandFree_compileOracle c_B
      (isRandFree_wrapStampedOracle c_A out_A isRandFree_bitTableLookupCode)),
    trivial⟩

end CslibFrontier.Complexity.FineGrained
