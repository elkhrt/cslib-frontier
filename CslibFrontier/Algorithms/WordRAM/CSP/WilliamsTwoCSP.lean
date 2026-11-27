/-
Copyright (c) 2026 Formal Papers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime
public import CslibFrontier.Computability.WordRAM.Time
public import CslibFrontier.Algorithms.WordRAM.CSP.BinaryCSP

import CslibFrontier.Computability.WordRAM.Admission
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Tactic.UpdateSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Williams Subexponential 2-CSP Solver on the Standard WordRAM

Implements the single fixed `160`-register standard WordRAM program (`williamsProgram`) backed by
`Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime`, proving exact charged execution
(`exec_williamsProgram`) and uniform WordRAM decidability (`uniformDecidableInTime_binaryCSPSAT`).

## Main definitions

* `williamsTime`, `williamsEnvelope`, `williamsWidth`, `williamsProgram`.

## Main results

* `inputFits_williamsWidth`: raw input fits in `williamsWidth I` bits.
* `exec_williamsProgram`: charged execution of `williamsProgram` on `I.encode`.
* `uniformDecidableInTime_binaryCSPSAT`: uniform decidability of `BinaryCSPSAT` on the standard
  WordRAM.
-/

public section

namespace Cslib.Algorithms.WordRAM.CSP

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle

/-! ### Native WordRAM Subroutines: Power Table and Matrix Builder -/

namespace PowTable

private abbrev rD : Fin 8 := 0
private abbrev rB : Fin 8 := 1
private abbrev rBase : Fin 8 := 2
private abbrev rJ : Fin 8 := 3
private abbrev rVal : Fin 8 := 4
private abbrev rAddr : Fin 8 := 5
private abbrev rLim : Fin 8 := 6
private abbrev rOne : Fin 8 := 7

private def body : Code .standard 8 := ram[
  rAddr ← rBase + rJ; *rAddr ← rVal; rVal ← rVal * rD; rJ ← rJ + rOne ]

private def program : Code .standard 8 := ram[
  rJ ← #0; rVal ← #1; rOne ← #1; rLim ← rB + rOne;
  while rJ < rLim do [ ⟪body⟫ ] ]

private theorem exec {w d b base : ℕ} (x : Data 8)
    (hd_reg : x.regs rD = d) (hb_reg : x.regs rB = b) (hbase_reg : x.regs rBase = base)
    (hfit : Fits w (base + b + 2 + d ^ (b + 1) + d)) :
    ∃ y, ExecWithin w program x y (6 * b + 12) ∧
      (∀ j ≤ b, y.mem (base + j) = d ^ j) ∧
      (∀ a, ¬(base ≤ a ∧ a < base + (b + 1)) → y.mem a = x.mem a) := by
  let P (k : ℕ) (s : Data 8) : Prop :=
    s.regs rD = d ∧ s.regs rBase = base ∧ s.regs rOne = 1 ∧ s.regs rLim = b + 1 ∧
    s.regs rVal = d ^ k ∧
    (∀ j < k, s.mem (base + j) = d ^ j) ∧
    (∀ a, ¬(base ≤ a ∧ a < base + k) → s.mem a = x.mem a)
  have hbody : ∀ s, P (s.regs rJ) s → s.regs rJ < b + 1 →
      ∃ z, ExecWithin w body s z 4 ∧ P (s.regs rJ + 1) z ∧ z.regs rJ = s.regs rJ + 1 := by
    intro s ⟨hsD, hsBase, hsOne, hsLim, hsVal, hsMem, hsOut⟩ hlt
    have hpow_le : d ^ (s.regs rJ + 1) ≤ d ^ (b + 1) := by
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp
      · exact Nat.pow_le_pow_right hd0 hlt
    have hpow_cur : d ^ s.regs rJ ≤ d ^ (b + 1) + 1 := by
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · cases s.regs rJ <;> simp
      · exact (Nat.pow_le_pow_right hd0 (by omega)).trans (Nat.le_succ _)
    have hpow_mul : d ^ s.regs rJ * d ≤ d ^ (b + 1) := by
      rw [← pow_succ]; exact hpow_le
    refine WP.exists_execWithin ?_
    unfold body
    wram_exec [hsD, hsBase, hsOne, hsVal]
    have hstep := prefix_write_step hsMem hsOut (z := Function.update s.mem (base + s.regs rJ)
      (d ^ s.regs rJ)) rfl
    refine ⟨⟨by wram_simp [hsD], by wram_simp [hsBase], by wram_simp [hsOne],
      by wram_simp [hsLim], by wram_simp [pow_succ], hstep.1, hstep.2⟩, by wram_simp⟩
  refine WP.exists_execWithin ?_
  unfold program
  wram_exec [hd_reg, hb_reg, hbase_reg]
  have h0 : P 0 ((((x.set rJ 0).set rVal 1).set rOne 1).set rLim (b + 1)) :=
    ⟨by wram_simp [hd_reg], by wram_simp [hbase_reg], by wram_simp, by wram_simp,
      by wram_simp [pow_zero], fun _ h => by omega, fun _ _ => rfl⟩
  wram_call (ExecWithin.loop_count P (fun s hs => hs.2.2.2.1) hbody
    (by wram_simp) (by wram_simp [h0]))
    with y ⟨⟨_, _, _, _, _, hmem, hout⟩, hend⟩
  refine ⟨by wram_simp; omega, fun j hj => hmem j (by omega), hout⟩

end PowTable

namespace FillMatrix

private abbrev rN1 : Fin 32 := 0
private abbrev rN12 : Fin 32 := 1
private abbrev rD : Fin 32 := 2
private abbrev rM : Fin 32 := 3
private abbrev rStride : Fin 32 := 4
private abbrev rPowBase : Fin 32 := 5
private abbrev rSide : Fin 32 := 6
private abbrev rRowBlock : Fin 32 := 7
private abbrev rColBlock : Fin 32 := 8
private abbrev rRowOff : Fin 32 := 9
private abbrev rColOff : Fin 32 := 10
private abbrev rRowLim : Fin 32 := 11
private abbrev rColLim : Fin 32 := 12
private abbrev rDst : Fin 32 := 13
private abbrev rZero : Fin 32 := 14
private abbrev rOne : Fin 32 := 15
private abbrev rTwo : Fin 32 := 16
private abbrev rArea : Fin 32 := 17
private abbrev rIdx : Fin 32 := 18
private abbrev rRow : Fin 32 := 19
private abbrev rCol : Fin 32 := 20
private abbrev rCi : Fin 32 := 21
private abbrev rCPtr : Fin 32 := 22
private abbrev rViol : Fin 32 := 23
private abbrev rX : Fin 32 := 24
private abbrev rY : Fin 32 := 25
private abbrev rBx : Fin 32 := 26
private abbrev rBy : Fin 32 := 27
private abbrev rOkX : Fin 32 := 28
private abbrev rOkY : Fin 32 := 29
private abbrev rAddr : Fin 32 := 30
private abbrev rTmp : Fin 32 := 31

private structure Args where
  n : ℕ
  d : ℕ
  m : ℕ
  powBase : ℕ
  rowBlock : ℕ
  colBlock : ℕ
  dst : ℕ

private structure Entry (A : Args) (x : Data 32) : Prop where
  n1 : x.regs rN1 = blockN1 A.n
  n12 : x.regs rN12 = blockN1 A.n + blockN2 A.n
  d : x.regs rD = A.d
  m : x.regs rM = A.m
  stride : x.regs rStride = 2 + A.d * A.d
  powBase : x.regs rPowBase = A.powBase
  side : x.regs rSide = blockM A.n A.d
  rowBlock : x.regs rRowBlock = A.rowBlock
  colBlock : x.regs rColBlock = A.colBlock
  rowOff : x.regs rRowOff = blockOff A.n A.rowBlock
  colOff : x.regs rColOff = blockOff A.n A.colBlock
  rowLim : x.regs rRowLim = blockLim A.n A.d A.rowBlock
  colLim : x.regs rColLim = blockLim A.n A.d A.colBlock
  dst : x.regs rDst = A.dst

private def computeBlock (rVar rBlk : Fin 32) : Code .standard 32 := ram[
  if rVar < rN1 then [ rBlk ← #0 ]
  else [ if rVar < rN12 then [ rBlk ← #1 ] else [ rBlk ← #2 ] ] ]

private def decodeVar (rVar rBlk rOk : Fin 32) : Code .standard 32 := ram[
  if rBlk = rRowBlock then [
    rTmp ← rVar - rRowOff; rAddr ← rPowBase + rTmp; rTmp ← *rAddr;
    rVar ← rRow / rTmp; rVar ← rVar % rD; rOk ← #1 ]
  else [
    if rBlk = rColBlock then [
      rTmp ← rVar - rColOff; rAddr ← rPowBase + rTmp; rTmp ← *rAddr;
      rVar ← rCol / rTmp; rVar ← rVar % rD; rOk ← #1 ]
    else [ rOk ← #0 ] ] ]

private def checkStep : Code .standard 32 :=
  .seq (ram[ rX ← *rCPtr; rAddr ← rCPtr + rOne; rY ← *rAddr ])
  (.seq (computeBlock rX rBx)
  (.seq (computeBlock rY rBy)
  (.seq (decodeVar rX rBx rOkX)
  (.seq (decodeVar rY rBy rOkY)
  (.seq (ram[
    if rOkX = rOne then [
      if rOkY = rOne then [
        rTmp ← rX * rD; rTmp ← rTmp + rY; rTmp ← rTmp + rTwo;
        rAddr ← rCPtr + rTmp; rTmp ← *rAddr;
        if rTmp = rZero then [ rViol ← #2 ] else [ rTmp ← #0 ] ]
      else [ rTmp ← #0 ] ]
    else [ rTmp ← #0 ] ])
  (ram[ rCPtr ← rCPtr + rStride; rCi ← rCi + rOne ]))))))

private def cellBody : Code .standard 32 :=
  .seq (ram[ rRow ← rIdx / rSide; rCol ← rIdx % rSide ])
  (.seq (ram[
    if rRow < rRowLim then [
      if rCol < rColLim then [
        rViol ← #0; rCi ← #0; rCPtr ← #4;
        while rCi < rM do [ ⟪checkStep⟫ ] ]
      else [ rViol ← #2 ] ]
    else [ rViol ← #2 ] ])
  (ram[ rAddr ← rDst + rIdx; *rAddr ← rViol; rIdx ← rIdx + rOne ]))

private def program : Code .standard 32 := ram[
  rZero ← #0; rOne ← #1; rTwo ← #2; rArea ← rSide * rSide; rIdx ← #0;
  while rIdx < rArea do [ ⟪cellBody⟫ ] ]

private theorem checkStep_preserves :
    ∀ i : Fin 32, i.val < 21 → checkStep.Preserves i := by decide

private theorem cellBody_preserves :
    ∀ i : Fin 32, i.val < 18 → cellBody.Preserves i := by decide

private theorem entry_of_regs {A : Args} {x y : Data 32} (hx : Entry A x)
    (h : ∀ i : Fin 32, i.val < 14 → y.regs i = x.regs i) : Entry A y := by regs_frame

private theorem exec_computeBlock {w : ℕ} (rVar rBlk : Fin 32)
    (hVar : rVar = rX ∨ rVar = rY) (hBlk : rBlk = rBx ∨ rBlk = rBy)
    (A : Args) (x : Data 32) (hx : Entry A x) (v : ℕ) (hv : x.regs rVar = v)
    (hfit : Fits w 2) :
    ∃ y, ExecWithin w (computeBlock rVar rBlk) x y 5 ∧
      y.regs rBlk = blockOf A.n v ∧
      (∀ i, i ≠ rBlk → y.regs i = x.regs i) ∧ y.mem = x.mem := by
  refine WP.exists_execWithin ?_
  unfold computeBlock; simp only [blockOf_eq]
  rcases hVar with rfl | rfl <;> rcases hBlk with rfl | rfl <;>
  · by_cases h1 : v < blockN1 A.n
    · wram_exec [hv, hx.n1, h1]
      exact ⟨by wram_simp [h1], fun i hi => by wram_simp [hi], rfl⟩
    · by_cases h2 : v < blockN1 A.n + blockN2 A.n
      · wram_exec [hv, hx.n1, hx.n12, h1, h2]
        exact ⟨by wram_simp [h1, h2], fun i hi => by wram_simp [hi], rfl⟩
      · wram_exec [hv, hx.n1, hx.n12, h1, h2]
        exact ⟨by wram_simp [h1, h2], fun i hi => by wram_simp [hi], rfl⟩

private theorem exec_decodeVar {w : ℕ} (rVar rBlk rOk : Fin 32)
    (hVar : rVar = rX ∨ rVar = rY) (hBlk : rBlk = rBx ∨ rBlk = rBy)
    (hOk : rOk = rOkX ∨ rOk = rOkY)
    (A : Args) (x : Data 32) (hx : Entry A x) (hd : 0 < A.d)
    (v : ℕ) (hv_lt : v < A.n) (hrow : x.regs rRow < blockM A.n A.d)
    (hcol : x.regs rCol < blockM A.n A.d)
    (hv : x.regs rVar = v) (hb : x.regs rBlk = blockOf A.n v)
    (hpow : ∀ j ≤ blockB A.n, x.mem (A.powBase + j) = A.d ^ j)
    (hfit : Fits w (A.powBase + blockB A.n + blockM A.n A.d + A.d + 4)) :
    ∃ y, ExecWithin w (decodeVar rVar rBlk rOk) x y 10 ∧
      y.regs rOk = (if blockOf A.n v = A.rowBlock ∨ blockOf A.n v = A.colBlock then 1 else 0) ∧
      ((blockOf A.n v = A.rowBlock ∨ blockOf A.n v = A.colBlock) →
        y.regs rVar = ((if blockOf A.n v = A.rowBlock then x.regs rRow else x.regs rCol) /
          A.d ^ (v - if blockOf A.n v = A.rowBlock then blockOff A.n A.rowBlock
            else blockOff A.n A.colBlock)) % A.d) ∧
      (∀ i, i ≠ rVar → i ≠ rOk → i ≠ rAddr → i ≠ rTmp → y.regs i = x.regs i) ∧
      y.mem = x.mem := by
  have hsub_le (blk : ℕ) (hblk : blockOf A.n v = blk) :
      v - blockOff A.n blk ≤ blockB A.n := by
    have := blockN1_le A.n; have := blockN2_le A.n; have := blockN3_le A.n
    have := block_sum A.n
    simp only [blockOf_eq, blockOff_eq] at *
    split_ifs at * <;> omega
  have hpow_pos (j : ℕ) : 0 < A.d ^ j := Nat.pos_of_ne_zero (pow_ne_zero j hd.ne')
  refine WP.exists_execWithin ?_
  unfold decodeVar
  by_cases hr : blockOf A.n v = A.rowBlock
  · have hle := hsub_le A.rowBlock hr
    have hpm := hpow (v - blockOff A.n A.rowBlock) hle
    have hpd : 0 < A.d ^ (v - blockOff A.n A.rowBlock) := hpow_pos _
    rcases hVar with rfl | rfl <;> rcases hBlk with rfl | rfl <;> rcases hOk with rfl | rfl
    all_goals
      wram_exec [hv, hb, hx.rowBlock, hx.rowOff, hx.powBase, hx.d, hr, hpm, hpd.ne']
      exact ⟨by wram_simp [hr]; simp, fun _ => by wram_simp [hr],
        fun i h1 h2 h3 h4 => by wram_simp [h1, h2, h3, h4], rfl⟩
  · by_cases hc : blockOf A.n v = A.colBlock
    · have hle := hsub_le A.colBlock hc
      have hpm := hpow (v - blockOff A.n A.colBlock) hle
      have hpd : 0 < A.d ^ (v - blockOff A.n A.colBlock) := hpow_pos _
      have hne : A.colBlock ≠ A.rowBlock := hc ▸ hr
      rcases hVar with rfl | rfl <;> rcases hBlk with rfl | rfl <;> rcases hOk with rfl | rfl
      all_goals
        wram_exec [hv, hb, hx.rowBlock, hx.colBlock, hx.colOff, hx.powBase, hx.d, hr, hc, hpm,
          hpd.ne']
        exact ⟨by wram_simp [hc]; simp, fun _ => by wram_simp [hc, hne],
          fun i h1 h2 h3 h4 => by wram_simp [h1, h2, h3, h4], rfl⟩
    · rcases hVar with rfl | rfl <;> rcases hBlk with rfl | rfl <;> rcases hOk with rfl | rfl
      all_goals
        wram_exec [hv, hb, hx.rowBlock, hx.colBlock, hr, hc]
        exact ⟨by simp [hr, hc], fun h => by exfalso; rcases h with h | h <;> contradiction,
          fun i h1 h2 h3 h4 => by wram_simp [h1, h2, h3, h4], rfl⟩

private theorem exec_checkStep {w : ℕ} (I : BinaryCSP) (A : Args) (x : Data 32)
    (hAn : A.n = I.n) (hAd : A.d = I.d) (hAm : A.m = I.m) (hd : 0 < I.d)
    (hx : Entry A x) (hzero : x.regs rZero = 0) (hone : x.regs rOne = 1)
    (htwo : x.regs rTwo = 2)
    (hrow : x.regs rRow < blockM I.n I.d) (hcol : x.regs rCol < blockM I.n I.d)
    (hi : x.regs rCi < I.m) (hptr : x.regs rCPtr = 4 + x.regs rCi * (2 + I.d * I.d))
    (hviol : x.regs rViol = 0 ∨ x.regs rViol = 2)
    (hin : ∀ a < 4 + I.m * (2 + I.d * I.d), x.mem a = (Data.init I.encode : Data 32).mem a)
    (hpow : ∀ j ≤ blockB I.n, x.mem (A.powBase + j) = I.d ^ j)
    (hfit : Fits w (A.powBase + blockB I.n + blockM I.n I.d + 4 + I.m * (2 + I.d * I.d) + 8)) :
    ∃ y, ExecWithin w checkStep x y 58 ∧
      y.regs rCi = x.regs rCi + 1 ∧
      y.regs rCPtr = 4 + (x.regs rCi + 1) * (2 + I.d * I.d) ∧
      y.regs rViol = (if x.regs rViol = 0 ∧
        constraintOk I.n I.d A.rowBlock A.colBlock (x.regs rRow) (x.regs rCol)
          (I.constraints ⟨x.regs rCi, hi⟩) then 0 else 2) ∧
      y.mem = x.mem := by
  cases A with | mk An Ad Am Apow ArB AcB Adst =>
  dsimp only at hAn hAd hAm hpow hfit ⊢
  subst hAn; subst hAd; subst hAm
  let A : Args := ⟨I.n, I.d, I.m, Apow, ArB, AcB, Adst⟩
  let ci : Fin I.m := ⟨x.regs rCi, hi⟩
  have hfst_lt : 4 + x.regs rCi * (2 + I.d * I.d) < 4 + I.m * (2 + I.d * I.d) := by
    have : x.regs rCi * (2 + I.d * I.d) + (2 + I.d * I.d) ≤ I.m * (2 + I.d * I.d) := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right (2 + I.d * I.d) (Nat.succ_le_of_lt hi)
    omega
  have hsnd_lt : 4 + x.regs rCi * (2 + I.d * I.d) + 1 < 4 + I.m * (2 + I.d * I.d) := by
    have : x.regs rCi * (2 + I.d * I.d) + (2 + I.d * I.d) ≤ I.m * (2 + I.d * I.d) := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right (2 + I.d * I.d) (Nat.succ_le_of_lt hi)
    omega
  have hmem_fst : x.mem (4 + x.regs rCi * (2 + I.d * I.d)) = (I.constraints ci).fst.val :=
    (hin _ hfst_lt).trans (BinaryCSP.encode_mem_fst I ci)
  have hmem_snd : x.mem (4 + x.regs rCi * (2 + I.d * I.d) + 1) = (I.constraints ci).snd.val :=
    (hin _ hsnd_lt).trans (BinaryCSP.encode_mem_snd I ci)
  refine WP.exists_execWithin ?_
  unfold checkStep
  wram_exec [hptr, hone, hmem_fst, hmem_snd]
  wram_call (exec_computeBlock rX rBx (Or.inl rfl) (Or.inl rfl) A _ (by regs_frame)
    (I.constraints ci).fst.val (by wram_simp) (hfit.of_le (by omega)))
    with s1 ⟨hs1_bx, hs1_r, hs1_m⟩
  wram_call (exec_computeBlock rY rBy (Or.inr rfl) (Or.inr rfl) A s1 (by regs_frame)
    (I.constraints ci).snd.val (by regs_frame) (hfit.of_le (by omega)))
    with s2 ⟨hs2_by, hs2_r, hs2_m⟩
  have hs2_pow : ∀ j ≤ blockB I.n, s2.mem (A.powBase + j) = I.d ^ j := by
    simpa only [hs2_m, hs1_m, Data.set_mem] using hpow
  have hd_le : I.d ≤ I.m * (2 + I.d * I.d) :=
    le_trans (by nlinarith) (Nat.le_mul_of_pos_left _ (by omega : 0 < I.m))
  have hs2_row : s2.regs rRow = x.regs rRow := by regs_frame
  have hs2_col : s2.regs rCol = x.regs rCol := by regs_frame
  have hdec1 := exec_decodeVar rX rBx rOkX (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    A s2 (by regs_frame) hd (I.constraints ci).fst.val (I.constraints ci).fst.isLt
    (by rw [hs2_row]; exact hrow) (by rw [hs2_col]; exact hcol)
    (by regs_frame) (by regs_frame) hs2_pow (hfit.of_le (by dsimp only [A]; omega))
  wram_call hdec1 with s3 ⟨hs3_okx, hs3_vx, hs3_r, hs3_m⟩
  have hs3_pow : ∀ j ≤ blockB I.n, s3.mem (A.powBase + j) = I.d ^ j := by
    simpa only [hs3_m] using hs2_pow
  have hs3_row : s3.regs rRow = x.regs rRow := by regs_frame
  have hs3_col : s3.regs rCol = x.regs rCol := by regs_frame
  have hdec2 := exec_decodeVar rY rBy rOkY (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
    A s3 (by regs_frame) hd (I.constraints ci).snd.val (I.constraints ci).snd.isLt
    (by rw [hs3_row]; exact hrow) (by rw [hs3_col]; exact hcol)
    (by regs_frame) (by regs_frame) hs3_pow (hfit.of_le (by dsimp only [A]; omega))
  wram_call hdec2 with s4 ⟨hs4_oky, hs4_vy, hs4_r, hs4_m⟩
  have hs4_m0 : s4.mem = x.mem := by
    simp only [hs4_m, hs3_m, hs2_m, hs1_m, Data.set_mem]
  have hs4_zero : s4.regs rZero = 0 := by regs_frame
  have hs4_one : s4.regs rOne = 1 := by regs_frame
  have hs4_two : s4.regs rTwo = 2 := by regs_frame
  have hs4_d : s4.regs rD = I.d := by regs_frame
  have hs4_stride : s4.regs rStride = 2 + I.d * I.d := by regs_frame
  have hs4_ci : s4.regs rCi = x.regs rCi := by regs_frame
  have hs4_cptr : s4.regs rCPtr = 4 + x.regs rCi * (2 + I.d * I.d) := by regs_frame
  have hs4_viol : s4.regs rViol = x.regs rViol := by regs_frame
  have hs4_okx : s4.regs rOkX =
      (if blockOf I.n (I.constraints ci).fst.val = A.rowBlock ∨
          blockOf I.n (I.constraints ci).fst.val = A.colBlock then 1 else 0) := by regs_frame
  have hs4_oky' : s4.regs rOkY =
      (if blockOf I.n (I.constraints ci).snd.val = A.rowBlock ∨
          blockOf I.n (I.constraints ci).snd.val = A.colBlock then 1 else 0) := hs4_oky
  have hs4_row : s4.regs rRow = x.regs rRow := by regs_frame
  have hs4_col : s4.regs rCol = x.regs rCol := by regs_frame
  have hci_fit : Fits w (x.regs rCi + 1) := hfit.of_le (by
    have : I.m ≤ I.m * (2 + I.d * I.d) := Nat.le_mul_of_pos_right _ (by omega)
    omega)
  have hcptr_fit : Fits w (4 + x.regs rCi * (2 + I.d * I.d) + (2 + I.d * I.d)) := hfit.of_le (by
    have : x.regs rCi * (2 + I.d * I.d) + (2 + I.d * I.d) ≤ I.m * (2 + I.d * I.d) := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right (2 + I.d * I.d) (Nat.succ_le_of_lt hi)
    omega)
  by_cases hbx : blockOf I.n (I.constraints ci).fst.val = A.rowBlock ∨
      blockOf I.n (I.constraints ci).fst.val = A.colBlock
  · by_cases hby : blockOf I.n (I.constraints ci).snd.val = A.rowBlock ∨
        blockOf I.n (I.constraints ci).snd.val = A.colBlock
    · have hvx_eq : s4.regs rX =
          ((if blockOf I.n (I.constraints ci).fst.val = A.rowBlock then x.regs rRow
            else x.regs rCol) /
            I.d ^ ((I.constraints ci).fst.val -
              if blockOf I.n (I.constraints ci).fst.val = A.rowBlock then
                blockOff I.n A.rowBlock else blockOff I.n A.colBlock)) % I.d := by
        rw [hs4_r rX (by decide) (by decide) (by decide) (by decide), hs3_vx hbx]
        simp only [show s2.regs rRow = x.regs rRow by regs_frame,
          show s2.regs rCol = x.regs rCol by regs_frame]
        rfl
      have hvy_eq : s4.regs rY =
          ((if blockOf I.n (I.constraints ci).snd.val = A.rowBlock then x.regs rRow
            else x.regs rCol) /
            I.d ^ ((I.constraints ci).snd.val -
              if blockOf I.n (I.constraints ci).snd.val = A.rowBlock then
                blockOff I.n A.rowBlock else blockOff I.n A.colBlock)) % I.d := by
        rw [hs4_vy hby]
        simp only [show s3.regs rRow = x.regs rRow by regs_frame,
          show s3.regs rCol = x.regs rCol by regs_frame]
        rfl
      let u : Fin I.d := ⟨s4.regs rX, by rw [hvx_eq]; exact Nat.mod_lt _ hd⟩
      let v : Fin I.d := ⟨s4.regs rY, by rw [hvy_eq]; exact Nat.mod_lt _ hd⟩
      have hperm_lt : 4 + x.regs rCi * (2 + I.d * I.d) + (u.val * I.d + v.val + 2) <
          4 + I.m * (2 + I.d * I.d) := by
        have h1 : u.val * I.d + v.val + 2 < 2 + I.d * I.d := by
          have : u.val * I.d + v.val < I.d * I.d := by
            calc u.val * I.d + v.val < u.val * I.d + I.d := Nat.add_lt_add_left v.isLt _
              _ = (u.val + 1) * I.d := by ring
              _ ≤ I.d * I.d := Nat.mul_le_mul_right I.d u.isLt
          omega
        have h2 : x.regs rCi * (2 + I.d * I.d) + (2 + I.d * I.d) ≤ I.m * (2 + I.d * I.d) := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right (2 + I.d * I.d) (Nat.succ_le_of_lt hi)
        omega
      have hmem_perm :
          s4.mem (4 + x.regs rCi * (2 + I.d * I.d) + (s4.regs rX * I.d + s4.regs rY + 2)) =
          if (u, v) ∈ (I.constraints ci).permitted then 1 else 0 := by
        rw [hs4_m0, hin _ hperm_lt, BinaryCSP.encode_mem_perm I ci u v]
      have hok_iff : constraintOk I.n I.d ArB AcB (x.regs rRow) (x.regs rCol)
          (I.constraints ⟨x.regs rCi, hi⟩) ↔ (u, v) ∈ (I.constraints ci).permitted := by
        simp only [constraintOk_iff, hasPermitted_iff]
        constructor
        · intro h
          obtain ⟨hx', hy', hm⟩ := h hbx hby
          convert hm using 2 <;> apply Fin.ext
          · exact hvx_eq
          · exact hvy_eq
        · intro hm _ _
          refine ⟨by rw [← hvx_eq]; exact u.isLt, by rw [← hvy_eq]; exact v.isLt, ?_⟩
          convert hm using 2 <;> apply Fin.ext
          · exact hvx_eq.symm
          · exact hvy_eq.symm
      by_cases hperm : (u, v) ∈ (I.constraints ci).permitted
      · wram_exec [hs4_okx, hs4_oky', hs4_one, hs4_two, hs4_zero, hs4_d, hs4_stride, hs4_ci,
          hs4_cptr, hs4_viol, hbx, hby, hmem_perm, hperm, hci_fit, hcptr_fit]
        refine ⟨by wram_simp, by wram_simp [Nat.succ_mul, Nat.add_assoc], ?_, hs4_m0⟩
        wram_simp [hs4_viol, hok_iff.mpr hperm]
        rcases hviol with hv0 | hv2
        · simp [hv0]
        · simp [hv2]
      · wram_exec [hs4_okx, hs4_oky', hs4_one, hs4_two, hs4_zero, hs4_d, hs4_stride, hs4_ci,
          hs4_cptr, hs4_viol, hbx, hby, hmem_perm, hperm, hci_fit, hcptr_fit]
        refine ⟨by wram_simp, by wram_simp [Nat.succ_mul, Nat.add_assoc], ?_, hs4_m0⟩
        wram_simp [hok_iff.not.mpr hperm]; simp
    · have hok_true : constraintOk I.n I.d ArB AcB (x.regs rRow) (x.regs rCol)
          (I.constraints ⟨x.regs rCi, hi⟩) := fun _ hy => absurd hy hby
      wram_exec [hs4_okx, hs4_oky', hs4_one, hs4_stride, hs4_ci, hs4_cptr, hs4_viol, hbx, hby,
        hci_fit, hcptr_fit]
      refine ⟨by wram_simp, by wram_simp [Nat.succ_mul, Nat.add_assoc], ?_, hs4_m0⟩
      wram_simp [hs4_viol, hok_true]
      rcases hviol with hv0 | hv2
      · simp [hv0]
      · simp [hv2]
  · have hok_true : constraintOk I.n I.d ArB AcB (x.regs rRow) (x.regs rCol)
        (I.constraints ⟨x.regs rCi, hi⟩) := fun hx _ => absurd hx hbx
    wram_exec [hs4_okx, hs4_oky', hs4_one, hs4_stride, hs4_ci, hs4_cptr, hs4_viol, hbx,
      hci_fit, hcptr_fit]
    refine ⟨by wram_simp, by wram_simp [Nat.succ_mul, Nat.add_assoc], ?_, hs4_m0⟩
    wram_simp [hs4_viol, hok_true]
    rcases hviol with hv0 | hv2
    · simp [hv0]
    · simp [hv2]

private theorem exec_cellBody {w q : ℕ} (I : BinaryCSP) (A : Args) (x : Data 32)
    (hAn : A.n = I.n) (hAd : A.d = I.d) (hAm : A.m = I.m) (hd : 0 < I.d)
    (hx : Entry A x) (hq : x.regs rIdx = q) (hlt : q < blockM I.n I.d * blockM I.n I.d)
    (hzero : x.regs rZero = 0) (hone : x.regs rOne = 1) (htwo : x.regs rTwo = 2)
    (hin : ∀ a < 4 + I.m * (2 + I.d * I.d), x.mem a = (Data.init I.encode : Data 32).mem a)
    (hpow : ∀ j ≤ blockB I.n, x.mem (A.powBase + j) = I.d ^ j)
    (hfit : Fits w (A.dst + blockM I.n I.d * blockM I.n I.d + A.powBase + blockB I.n +
      blockM I.n I.d + 4 + I.m * (2 + I.d * I.d) + 8)) :
    ∃ y, ExecWithin w cellBody x y (60 * I.m + 20) ∧ y.regs rIdx = q + 1 ∧
      y.mem = Function.update x.mem (A.dst + q)
        (encode (williamsWeight I A.rowBlock A.colBlock
          (q / blockM I.n I.d) (q % blockM I.n I.d))) := by
  cases A with | mk An Ad Am Apow ArB AcB Adst =>
  dsimp only at hAn hAd hAm hpow hfit ⊢
  subst hAn; subst hAd; subst hAm
  let A : Args := ⟨I.n, I.d, I.m, Apow, ArB, AcB, Adst⟩
  have hM_pos : 0 < blockM I.n I.d := by
    rw [blockM_eq]; exact Nat.pos_of_ne_zero (pow_ne_zero _ hd.ne')
  have hrow_lt : q / blockM I.n I.d < blockM I.n I.d := Nat.div_lt_of_lt_mul hlt
  have hcol_lt : q % blockM I.n I.d < blockM I.n I.d := Nat.mod_lt _ hM_pos
  refine WP.exists_execWithin ?_
  unfold cellBody
  wram_exec [hq, hx.side, hx.rowLim, hx.colLim, hx.dst, hone, hM_pos.ne']
  · rename_i hr
    let P (k : ℕ) (s : Data 32) : Prop :=
      Entry A s ∧ s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs rTwo = 2 ∧
      s.regs rIdx = q ∧ s.regs rRow = q / blockM I.n I.d ∧ s.regs rCol = q % blockM I.n I.d ∧
      s.regs rCPtr = 4 + k * (2 + I.d * I.d) ∧
      s.regs rViol = (if ∀ (j : ℕ) (hj : j < k) (hm : j < I.m),
        constraintOk I.n I.d A.rowBlock A.colBlock (q / blockM I.n I.d) (q % blockM I.n I.d)
          (I.constraints ⟨j, hm⟩) then 0 else 2) ∧
      s.mem = x.mem
    have hstep : ∀ s, P (s.regs rCi) s → s.regs rCi < I.m →
        ∃ z, ExecWithin w checkStep s z 58 ∧ P (s.regs rCi + 1) z ∧
          z.regs rCi = s.regs rCi + 1 := by
      intro s ⟨hsE, hs0, hs1, hs2, hsI, hsR, hsC, hsP, hsV, hsM⟩ hlti
      have hviol_or : s.regs rViol = 0 ∨ s.regs rViol = 2 := by
        rw [hsV]; split_ifs <;> simp
      obtain ⟨z, he, hzCi, hzPtr, hzViol, hzMem⟩ := exec_checkStep I A s rfl rfl rfl hd hsE
        hs0 hs1 hs2 (by rw [hsR]; exact hrow_lt) (by rw [hsC]; exact hcol_lt) hlti hsP
        hviol_or (by simpa only [hsM] using hin) (by simpa only [hsM] using hpow)
        (hfit.of_le (by dsimp only [A]; omega))
      have hpres (i : Fin 32) (hi' : i.val < 21) : z.regs i = s.regs i :=
        he.regs_eq (checkStep_preserves i hi')
      refine ⟨z, he, ⟨entry_of_regs hsE (fun i hi' => hpres i (by omega)),
        (hpres rZero (by decide)).trans hs0, (hpres rOne (by decide)).trans hs1,
        (hpres rTwo (by decide)).trans hs2, (hpres rIdx (by decide)).trans hsI,
        (hpres rRow (by decide)).trans hsR, (hpres rCol (by decide)).trans hsC,
        hzPtr, ?_, hzMem.trans hsM⟩, hzCi⟩
      rw [hzViol, hsR, hsC, hsV]
      by_cases hprev : ∀ (j : ℕ) (hj : j < s.regs rCi) (hm : j < I.m),
          constraintOk I.n I.d A.rowBlock A.colBlock (q / blockM I.n I.d) (q % blockM I.n I.d)
            (I.constraints ⟨j, hm⟩)
      · by_cases hcur : constraintOk I.n I.d A.rowBlock A.colBlock (q / blockM I.n I.d)
            (q % blockM I.n I.d) (I.constraints ⟨s.regs rCi, hlti⟩)
        · have hall : ∀ (j : ℕ) (hj : j < s.regs rCi + 1) (hm : j < I.m),
              constraintOk I.n I.d A.rowBlock A.colBlock (q / blockM I.n I.d)
                (q % blockM I.n I.d) (I.constraints ⟨j, hm⟩) := by
            intro j hj hm
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
            · exact hprev j hj' hm
            · exact hcur
          rw [ite_eq_left hprev, ite_eq_left hall]; simp [hcur]
        · have hnot : ¬∀ (j : ℕ) (hj : j < s.regs rCi + 1) (hm : j < I.m),
              constraintOk I.n I.d A.rowBlock A.colBlock (q / blockM I.n I.d)
                (q % blockM I.n I.d) (I.constraints ⟨j, hm⟩) :=
            fun hall => hcur (hall (s.regs rCi) (Nat.lt_succ_self _) hlti)
          rw [ite_eq_left hprev, ite_eq_right hnot]; simp [hcur]
      · have hnot : ¬∀ (j : ℕ) (hj : j < s.regs rCi + 1) (hm : j < I.m),
            constraintOk I.n I.d A.rowBlock A.colBlock (q / blockM I.n I.d)
              (q % blockM I.n I.d) (I.constraints ⟨j, hm⟩) :=
          fun hall => hprev fun j hj hm => hall j (by omega) hm
        rw [ite_eq_right hprev, ite_eq_right hnot]; simp
    have h0 : P 0 (((((((x.set rRow (q / blockM I.n I.d)).set rCol (q % blockM I.n I.d)).set
        rViol 0).set rCi 0).set rCPtr 4))) := by
      refine ⟨by regs_frame, by wram_simp [hzero], by wram_simp [hone], by wram_simp [htwo],
        by wram_simp [hq], by wram_simp, by wram_simp, by wram_simp; ring, ?_, rfl⟩
      wram_simp
      exact (ite_eq_left (fun j hj => absurd hj (Nat.not_lt_zero j))).symm
    wram_call (ExecWithin.loop_count P (fun s hs => hs.1.m) hstep
      (by wram_simp; exact Nat.zero_le _) (by wram_simp; exact h0))
      with s ⟨⟨hsE, _, hs1, _, hsI, _, _, _, hsV, hsM⟩, hend⟩
    wram_exec [hsE.dst, hsI, hs1, hsV]
    refine ⟨by wram_simp; dsimp only [A]; omega, by wram_simp, ?_⟩
    have hiff : (∀ i : Fin I.m, constraintOk I.n I.d ArB AcB
        (q / blockM I.n I.d) (q % blockM I.n I.d) (I.constraints i)) ↔
        (∀ (j : ℕ) (_ : j < I.m) (hm : j < I.m),
          constraintOk I.n I.d ArB AcB (q / blockM I.n I.d)
            (q % blockM I.n I.d) (I.constraints ⟨j, hm⟩)) :=
      ⟨fun h j _ hm => h ⟨j, hm⟩, fun h i => h i.val i.isLt i.isLt⟩
    dsimp only [A] at hsV hend ⊢
    simp only [Data.set_mem, Data.write_mem, hsM, ← hiff, williamsWeight_eq]
    by_cases hall : ∀ i : Fin I.m, constraintOk I.n I.d ArB AcB
        (q / blockM I.n I.d) (q % blockM I.n I.d) (I.constraints i)
    · rw [ite_eq_left hall, ite_eq_left ⟨hr, hc, hall⟩]; rfl
    · rw [ite_eq_right hall, ite_eq_right (fun h => hall h.2.2)]; rfl
  · rename_i hr
    refine ⟨by wram_simp, ?_⟩
    rw [Data.set_mem, Data.write_mem, williamsWeight_eq, ite_eq_right (fun h => hc h.2.1)]; rfl
  · refine ⟨by wram_simp, ?_⟩
    rw [Data.set_mem, Data.write_mem, williamsWeight_eq, ite_eq_right (fun h => hc h.1)]; rfl

private theorem exec {w : ℕ} (I : BinaryCSP) (A : Args) (x : Data 32)
    (hAn : A.n = I.n) (hAd : A.d = I.d) (hAm : A.m = I.m) (hd : 0 < I.d)
    (hx : Entry A x)
    (hdisj_in : 4 + I.m * (2 + I.d * I.d) ≤ A.dst)
    (hdisj_pow : A.powBase + blockB I.n + 1 ≤ A.dst)
    (hin : ∀ a < 4 + I.m * (2 + I.d * I.d), x.mem a = (Data.init I.encode : Data 32).mem a)
    (hpow : ∀ j ≤ blockB I.n, x.mem (A.powBase + j) = I.d ^ j)
    (hfit : Fits w (A.dst + blockM I.n I.d * blockM I.n I.d + A.powBase + blockB I.n +
      blockM I.n I.d + 4 + I.m * (2 + I.d * I.d) + 8)) :
    ∃ y, ExecWithin w program x y ((60 * I.m + 22) * (blockM I.n I.d * blockM I.n I.d) + 12) ∧
      (∀ q < blockM I.n I.d * blockM I.n I.d,
        y.mem (A.dst + q) = encode (williamsWeight I A.rowBlock A.colBlock
          (q / blockM I.n I.d) (q % blockM I.n I.d))) ∧
      (∀ a, ¬(A.dst ≤ a ∧ a < A.dst + blockM I.n I.d * blockM I.n I.d) → y.mem a = x.mem a) := by
  cases A with | mk An Ad Am Apow ArB AcB Adst =>
  dsimp only at hAn hAd hAm hdisj_in hdisj_pow hpow hfit ⊢
  subst hAn; subst hAd; subst hAm
  let A : Args := ⟨I.n, I.d, I.m, Apow, ArB, AcB, Adst⟩
  let area := blockM I.n I.d * blockM I.n I.d
  let P (k : ℕ) (s : Data 32) : Prop :=
    Entry A s ∧ s.regs rZero = 0 ∧ s.regs rOne = 1 ∧ s.regs rTwo = 2 ∧ s.regs rArea = area ∧
    (∀ q < k, s.mem (A.dst + q) = encode (williamsWeight I A.rowBlock A.colBlock
      (q / blockM I.n I.d) (q % blockM I.n I.d))) ∧
    (∀ a, ¬(A.dst ≤ a ∧ a < A.dst + k) → s.mem a = x.mem a)
  have hbody : ∀ s, P (s.regs rIdx) s → s.regs rIdx < area →
      ∃ z, ExecWithin w cellBody s z (60 * I.m + 20) ∧ P (s.regs rIdx + 1) z ∧
        z.regs rIdx = s.regs rIdx + 1 := by
    intro s ⟨hsE, hs0, hs1, hs2, hsA, hsMem, hsOut⟩ hlt
    have hsin : ∀ a < 4 + I.m * (2 + I.d * I.d),
        s.mem a = (Data.init I.encode : Data 32).mem a := fun a ha =>
      (hsOut a (by dsimp only [A]; omega)).trans (hin a ha)
    have hspow : ∀ j ≤ blockB I.n, s.mem (A.powBase + j) = I.d ^ j := fun j hj =>
      (hsOut (A.powBase + j) (by dsimp only [A]; omega)).trans (hpow j hj)
    obtain ⟨z, he, hzI, hzM⟩ := exec_cellBody I A s rfl rfl rfl hd hsE rfl hlt hs0 hs1 hs2
      hsin hspow hfit
    have hpres (i : Fin 32) (hi' : i.val < 18) : z.regs i = s.regs i :=
      he.regs_eq (cellBody_preserves i hi')
    have hstep := prefix_write_step hsMem hsOut hzM
    refine ⟨z, he, ⟨entry_of_regs hsE (fun i hi' => hpres i (by omega)),
      (hpres rZero (by decide)).trans hs0, (hpres rOne (by decide)).trans hs1,
      (hpres rTwo (by decide)).trans hs2, (hpres rArea (by decide)).trans hsA,
      hstep.1, hstep.2⟩, hzI⟩
  refine WP.exists_execWithin ?_
  unfold program
  wram_exec [hx.side]
  have h0 : P 0 (((((x.set rZero 0).set rOne 1).set rTwo 2).set rArea area).set rIdx 0) :=
    ⟨by regs_frame, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      fun _ h => by omega, fun _ _ => rfl⟩
  wram_call (ExecWithin.loop_count P (fun s hs => hs.2.2.2.2.1) hbody
    (by wram_simp; exact Nat.zero_le _) (by wram_simp; exact h0))
    with y ⟨⟨_, _, _, _, _, hmem, hout⟩, _⟩
  refine ⟨by wram_simp; dsimp only [area]; rw [Nat.mul_comm, Nat.add_assoc]; omega, hmem, hout⟩

end FillMatrix

/-! ### Complete Fixed `160`-Register Williams WordRAM Program -/

namespace WilliamsRAM

private abbrev cN : Fin 160 := 128
private abbrev cD : Fin 160 := 129
private abbrev cM : Fin 160 := 130
private abbrev cB : Fin 160 := 131
private abbrev cN1 : Fin 160 := 132
private abbrev cN2 : Fin 160 := 133
private abbrev cN12 : Fin 160 := 134
private abbrev cN3 : Fin 160 := 135
private abbrev cSide : Fin 160 := 136
private abbrev cM1 : Fin 160 := 137
private abbrev cM2 : Fin 160 := 138
private abbrev cM3 : Fin 160 := 139
private abbrev cStride : Fin 160 := 140
private abbrev cPowBase : Fin 160 := 141
private abbrev cAB : Fin 160 := 142
private abbrev cBC : Fin 160 := 143
private abbrev cAC : Fin 160 := 144
private abbrev cScratch : Fin 160 := 145
private abbrev cOut : Fin 160 := 146
private abbrev cZero : Fin 160 := 147
private abbrev cOne : Fin 160 := 148
private abbrev cTwo : Fin 160 := 149
private abbrev cThree : Fin 160 := 150
private abbrev cFour : Fin 160 := 151
private abbrev cCells : Fin 160 := 152
private abbrev cAddr : Fin 160 := 153
private abbrev cTmp : Fin 160 := 154

private abbrev pt (i : Fin 8) : Fin 160 := Fin.castLE (by decide) i
private abbrev low (i : Fin 32) : Fin 160 := Fin.castLE (by decide) i
private abbrev cp (i : Fin 128) : Fin 160 := Fin.castLE (by decide) i

private abbrev ptD : Fin 160 := pt PowTable.rD
private abbrev ptB : Fin 160 := pt PowTable.rB
private abbrev ptBase : Fin 160 := pt PowTable.rBase
private abbrev fmN1 : Fin 160 := low FillMatrix.rN1
private abbrev fmN12 : Fin 160 := low FillMatrix.rN12
private abbrev fmD : Fin 160 := low FillMatrix.rD
private abbrev fmM : Fin 160 := low FillMatrix.rM
private abbrev fmStride : Fin 160 := low FillMatrix.rStride
private abbrev fmPowBase : Fin 160 := low FillMatrix.rPowBase
private abbrev fmSide : Fin 160 := low FillMatrix.rSide
private abbrev fmRowBlock : Fin 160 := low FillMatrix.rRowBlock
private abbrev fmColBlock : Fin 160 := low FillMatrix.rColBlock
private abbrev fmRowOff : Fin 160 := low FillMatrix.rRowOff
private abbrev fmColOff : Fin 160 := low FillMatrix.rColOff
private abbrev fmRowLim : Fin 160 := low FillMatrix.rRowLim
private abbrev fmColLim : Fin 160 := low FillMatrix.rColLim
private abbrev fmDst : Fin 160 := low FillMatrix.rDst
private abbrev cpSide : Fin 160 := cp CountPrime.Reg.side
private abbrev cpMod : Fin 160 := cp CountPrime.Reg.modulus
private abbrev cpAB : Fin 160 := cp CountPrime.Reg.inputAB
private abbrev cpBC : Fin 160 := cp CountPrime.Reg.inputBC
private abbrev cpAC : Fin 160 := cp CountPrime.Reg.inputAC
private abbrev cpScratch : Fin 160 := cp CountPrime.Reg.scratch
private abbrev cpRes : Fin 160 := cp CountPrime.Reg.result

private def setupBlocks : Code .standard 160 := ram[
  cB ← cN + cTwo; cB ← cB / cThree;
  if cN < cB then [ cN1 ← cN ] else [ cN1 ← cB ];
  cTmp ← cN - cN1;
  if cTmp < cB then [ cN2 ← cTmp ] else [ cN2 ← cB ];
  cN12 ← cN1 + cN2; cN3 ← cN - cN12;
  cStride ← cD * cD; cStride ← cStride + cTwo;
  cPowBase ← cM * cStride; cPowBase ← cPowBase + cFour;
  ptD ← cD; ptB ← cB; ptBase ← cPowBase ]

private abbrev loadArgs (rRowBlk rColBlk rRowOff rColOff rRowLim rColLim rDst : Fin 160) :
    Code .standard 160 := ram[
  fmN1 ← cN1; fmN12 ← cN12; fmD ← cD; fmM ← cM; fmStride ← cStride; fmPowBase ← cPowBase;
  fmSide ← cSide; fmRowBlock ← rRowBlk; fmColBlock ← rColBlk; fmRowOff ← rRowOff;
  fmColOff ← rColOff; fmRowLim ← rRowLim; fmColLim ← rColLim; fmDst ← rDst ]

private def mainBody : Code .standard 160 :=
  .seq setupBlocks
  (.seq (PowTable.program.rename (Fin.castLE (by decide)))
  (.seq (ram[
    cAddr ← cPowBase + cB; cSide ← *cAddr;
    cAddr ← cPowBase + cN1; cM1 ← *cAddr;
    cAddr ← cPowBase + cN2; cM2 ← *cAddr;
    cAddr ← cPowBase + cN3; cM3 ← *cAddr;
    cCells ← cSide * cSide;
    cAB ← cPowBase + cB; cAB ← cAB + cOne;
    cBC ← cAB + cCells; cAC ← cBC + cCells; cScratch ← cAC + cCells ])
  (.seq (loadArgs cZero cOne cZero cN1 cM1 cM2 cAB)
  (.seq (FillMatrix.program.rename (Fin.castLE (by decide)))
  (.seq (loadArgs cOne cTwo cN1 cN12 cM2 cM3 cBC)
  (.seq (FillMatrix.program.rename (Fin.castLE (by decide)))
  (.seq (loadArgs cZero cTwo cZero cN12 cM1 cM3 cAC)
  (.seq (FillMatrix.program.rename (Fin.castLE (by decide)))
  (.seq (ram[
    cpSide ← cSide; cpMod ← cFour; cpAB ← cAB; cpBC ← cBC; cpAC ← cAC; cpScratch ← cScratch ])
  (.seq (CountPrime.program.rename (Fin.castLE (by decide)))
  (ram[
    if cZero < cpRes then [ cOut ← #1 ] else [ cOut ← #0 ] ])))))))))))

private def williamsCode : Code .standard 160 := ram[
  cZero ← #0; cOne ← #1; cTwo ← #2; cThree ← #3; cFour ← #4;
  cN ← *cOne; cD ← *cTwo; cM ← *cThree;
  if cN = cZero then [ cOut ← #1 ]
  else [
    if cD = cZero then [ cOut ← #0 ]
    else [ ⟪mainBody⟫ ] ] ]

private theorem exec_setupBlocks {w : ℕ} (I : BinaryCSP) (x : Data 160)
    (h0 : x.regs cZero = 0) (h1 : x.regs cOne = 1) (h2 : x.regs cTwo = 2)
    (h3 : x.regs cThree = 3) (h4 : x.regs cFour = 4)
    (hn : x.regs cN = I.n) (hd : x.regs cD = I.d) (hm : x.regs cM = I.m)
    (hfit : Fits w (4 + I.m * (2 + I.d * I.d) + I.d * I.d + I.n + 8)) :
    ∃ y, ExecWithin w setupBlocks x y 20 ∧
      y.regs cZero = 0 ∧ y.regs cOne = 1 ∧ y.regs cTwo = 2 ∧ y.regs cFour = 4 ∧
      y.regs cN = I.n ∧ y.regs cD = I.d ∧ y.regs cM = I.m ∧
      y.regs cB = blockB I.n ∧ y.regs cN1 = blockN1 I.n ∧ y.regs cN2 = blockN2 I.n ∧
      y.regs cN12 = blockN1 I.n + blockN2 I.n ∧ y.regs cN3 = blockN3 I.n ∧
      y.regs cStride = 2 + I.d * I.d ∧ y.regs cPowBase = 4 + I.m * (2 + I.d * I.d) ∧
      y.regs (pt PowTable.rD) = I.d ∧ y.regs (pt PowTable.rB) = blockB I.n ∧
      y.regs (pt PowTable.rBase) = 4 + I.m * (2 + I.d * I.d) ∧
      y.mem = x.mem := by
  have h3ne : (3 : ℕ) ≠ 0 := by decide
  have hb_le : blockB I.n ≤ I.n + 1 := by rw [blockB_eq]; omega
  have hcomm : I.m * (I.d * I.d + 2) = I.m * (2 + I.d * I.d) := by ring
  refine WP.exists_execWithin ?_
  unfold setupBlocks
  by_cases hlt1 : I.n < blockB I.n
  · have hn1 : blockN1 I.n = I.n := by rw [blockN1_eq]; omega
    have hlt2 : I.n - blockN1 I.n < blockB I.n := by omega
    have hn2 : blockN2 I.n = I.n - blockN1 I.n := by rw [blockN2_eq]; omega
    wram_exec [h0, h1, h2, h3, h4, hn, hd, hm, h3ne, (blockB_eq I.n).symm,
      hlt1, hn1, hlt2, hn2]
    exact ⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2], by wram_simp [h4],
      by wram_simp [hn], by wram_simp [hd], by wram_simp [hm], by wram_simp,
      by wram_simp [hn1], by wram_simp [hn1, hn2, Nat.sub_self], by wram_simp [hn1, hn2],
      by wram_simp [blockN3_eq, hn1, hn2], by wram_simp; ring,
      by wram_simp; ring, by wram_simp, by wram_simp, by wram_simp; ring, rfl⟩
  · have hn1 : blockN1 I.n = blockB I.n := by rw [blockN1_eq]; omega
    by_cases hlt2 : I.n - blockN1 I.n < blockB I.n
    · have hn2 : blockN2 I.n = I.n - blockN1 I.n := by rw [blockN2_eq]; omega
      wram_exec [h0, h1, h2, h3, h4, hn, hd, hm, h3ne, (blockB_eq I.n).symm,
        hlt1, hn1, hlt2, hn2]
      exact ⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2], by wram_simp [h4],
        by wram_simp [hn], by wram_simp [hd], by wram_simp [hm], by wram_simp,
        by wram_simp [hn1], by wram_simp [hn1, hn2], by wram_simp [hn1, hn2],
        by wram_simp [blockN3_eq, hn1, hn2], by wram_simp; ring,
        by wram_simp; ring, by wram_simp, by wram_simp, by wram_simp; ring, rfl⟩
    · have hn2 : blockN2 I.n = blockB I.n := by rw [blockN2_eq]; omega
      wram_exec [h0, h1, h2, h3, h4, hn, hd, hm, h3ne, (blockB_eq I.n).symm,
        hlt1, hn1, hlt2, hn2]
      exact ⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2], by wram_simp [h4],
        by wram_simp [hn], by wram_simp [hd], by wram_simp [hm], by wram_simp,
        by wram_simp [hn1], by wram_simp [hn2], by wram_simp [hn1, hn2],
        by wram_simp [blockN3_eq, hn1, hn2], by wram_simp; ring,
        by wram_simp; ring, by wram_simp, by wram_simp, by wram_simp; ring, rfl⟩

end WilliamsRAM

/-- Exact WordRAM instruction-count bound for `williamsProgram` on `I`. -/
def williamsTime (I : BinaryCSP) : ℕ :=
  let M := blockM I.n I.d
  15 * (I.n + 1) + 3 * ((60 * I.m + 22) * (M * M) + 30) + CountPrime.cost M 4 + 200

/-- Word-value envelope dominating every address, power, and `CountPrime` budget during
`williamsProgram` execution on `I`. -/
def williamsEnvelope (I : BinaryCSP) : ℕ :=
  let b := blockB I.n
  let M := blockM I.n I.d
  let stride := 2 + I.d * I.d
  let powBase := 4 + I.m * stride
  let abBase := powBase + b + 1
  let bcBase := abBase + M * M
  let acBase := bcBase + M * M
  let scratch := acBase + M * M
  CountPrime.addressBudget M 4 (Nat.clog 2 M) scratch abBase bcBase acBase +
    CountPrime.magnitudeBudget 4 (Nat.clog 2 M) 1 +
    M * I.d + I.d ^ (b + 1) + I.n + I.d + I.m + 64

/-- Sufficient physical word width for `williamsProgram` on `I` (logarithmic in
`williamsEnvelope I`, i.e., `O(n log d + log m)`). -/
def williamsWidth (I : BinaryCSP) : ℕ :=
  Nat.clog 2 (williamsEnvelope I) + 3

/-- The single fixed `160`-register standard WordRAM program implementing Williams' `#2-CSP` /
`2-CSP-SAT` algorithm. -/
def williamsProgram : Program .standard 160 :=
  WilliamsRAM.williamsCode.program WilliamsRAM.cOut

private theorem williamsCode_not_readsWidth : ¬WilliamsRAM.williamsCode.ReadsWidth := by
  decide +kernel

/-- The raw encoding of any binary CSP fits in `williamsWidth I` bits. -/
theorem inputFits_williamsWidth (I : BinaryCSP) :
    InputFits (williamsWidth I) I.encode := by
  let E := williamsEnvelope I
  have hlt : ∀ v < E, Fits (williamsWidth I) v := fun v hv =>
    fits_of_lt_clog_le hv (by dsimp only [E]; unfold williamsWidth; omega)
  have hlen_lt : I.encode.length < E := by
    have h2 : 0 < 2 ^ Nat.clog 2 (blockM I.n I.d) := Nat.two_pow_pos _
    rw [BinaryCSP.encode_length]
    dsimp only [E, williamsEnvelope, CountPrime.addressBudget]
    omega
  refine ⟨hlt _ hlen_lt, fun v hv => hlt v ?_⟩
  have hlt_v := I.mem_encode_lt hv
  dsimp only [E, williamsEnvelope]; omega

/-- Complete charged execution of `williamsProgram` on `I.encode` at every word width
`W ≥ williamsWidth I`: halts in at most `williamsTime I` instructions with output `1` iff
`I.IsSatisfiable` (and `0` otherwise). -/
theorem exec_williamsProgram (I : BinaryCSP) {W : ℕ} (hW : williamsWidth I ≤ W) :
    williamsProgram.Answers W I.encode I.IsSatisfiable (williamsTime I) := by
  let b := blockB I.n
  let M := blockM I.n I.d
  let stride := 2 + I.d * I.d
  let powBase := 4 + I.m * stride
  let abBase := powBase + b + 1
  let bcBase := abBase + M * M
  let acBase := bcBase + M * M
  let scratch := acBase + M * M
  let E := williamsEnvelope I
  let wBase := Nat.clog 2 E + 1
  have hW_ge : wBase + 2 ≤ W := by
    simpa only [wBase, williamsWidth, Nat.add_assoc] using hW
  have hfit_E : Fits (wBase + 2) E := by
    have h := fits_of_clog_lt (B := E) (W := wBase + 2) (by dsimp only [wBase]; omega)
    exact h
  have hmag : Cslib.GenericRAM.Signed.Fits wBase
      (CountPrime.magnitudeBudget 4 (Nat.clog 2 M) 1 : ℤ) := by
    have hm : CountPrime.magnitudeBudget 4 (Nat.clog 2 M) 1 < 2 ^ Nat.clog 2 E :=
      fits_of_lt_clog_le (B := E)
        (by dsimp only [E, williamsEnvelope, b, M, stride, powBase, abBase, bcBase, acBase,
          scratch]; omega) le_rfl
    refine ⟨by omega, ?_, ?_⟩
    · simp only [wBase, Nat.add_sub_cancel]
      exact (neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _)
    · simp only [wBase, Nat.add_sub_cancel]
      exact_mod_cast hm
  have haddr : Fits (wBase + 2)
      (CountPrime.addressBudget M 4 (Nat.clog 2 M) scratch abBase bcBase acBase) :=
    hfit_E.of_le (by
      dsimp only [E, williamsEnvelope, b, M, stride, powBase, abBase, bcBase, acBase, scratch]
      omega)
  have hcore : ∃ y, ExecWithin (wBase + 2) WilliamsRAM.williamsCode
      (.init I.encode) y (williamsTime I - 1) ∧
      y.regs WilliamsRAM.cOut ≤ 1 ∧ (y.regs WilliamsRAM.cOut = 1 ↔ I.IsSatisfiable) := by
    have h2 : 0 < 2 ^ Nat.clog 2 M := Nat.two_pow_pos _
    refine WP.exists_execWithin ?_
    unfold WilliamsRAM.williamsCode
    wram_exec [BinaryCSP.encode_mem_n I, BinaryCSP.encode_mem_d I, BinaryCSP.encode_mem_m I]
    · refine ⟨by dsimp only [williamsTime]; omega, by wram_simp, ?_⟩
      wram_simp
      exact ⟨fun _ => ⟨fun i => Fin.elim0 (hc ▸ i),
        fun i => Fin.elim0 (hc ▸ (I.constraints i).fst)⟩, fun _ => trivial⟩
    · rename_i hn0
      refine ⟨by dsimp only [williamsTime]; omega, by wram_simp, ?_⟩
      wram_simp
      exact ⟨False.elim, fun ⟨σ, _⟩ =>
        absurd (σ ⟨0, Nat.pos_of_ne_zero hn0⟩).isLt (by omega)⟩
    · rename_i hn0
      have hd : 0 < I.d := Nat.pos_of_ne_zero hc
      have hb_pos : 1 ≤ b := by dsimp only [b]; rw [blockB_eq]; omega
      have hb_le : b ≤ I.n := by dsimp only [b]; rw [blockB_eq]; omega
      have hdd_le : I.d * I.d ≤ I.d ^ (blockB I.n + 1) := by
        calc I.d * I.d = I.d ^ 2 := (sq I.d).symm
          _ ≤ I.d ^ (blockB I.n + 1) := Nat.pow_le_pow_right hd (by dsimp only [b] at hb_pos; omega)
      unfold WilliamsRAM.mainBody
      wram_call (WilliamsRAM.exec_setupBlocks (w := wBase + 2) I _
        (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
        (by wram_simp) (by wram_simp) (by wram_simp)
        (hfit_E.of_le (by
          dsimp only [E, williamsEnvelope, CountPrime.addressBudget, scratch, acBase, bcBase,
            abBase, powBase, stride, b, M] at h2 ⊢
          omega))) with sS ⟨hsS0, hsS1, hsS2, hsS4, hsSN, hsSD, hsSM, hsSB, hsSN1, hsSN2,
        hsSN12, hsSN3, hsSStr, hsSPB, hsSptD, hsSptB, hsSptBase, hsSMem⟩
      have hpow_fit : Fits (wBase + 2) (powBase + b + 2 + I.d ^ (b + 1) + I.d) :=
        hfit_E.of_le (by
          dsimp only [E, williamsEnvelope, CountPrime.addressBudget, scratch, acBase, bcBase,
            abBase, powBase, stride, b, M] at h2 ⊢
          omega)
      wram_call (PowTable.exec (w := wBase + 2) (d := I.d) (b := b) (base := powBase) _
        hsSptD hsSptB hsSptBase hpow_fit)
        canonical (Fin.castLE_injective _) with sP ⟨hsP_pow, hsP_out⟩
      have hsP_m0 : ∀ a < powBase, sP.mem a = (Data.init I.encode : Data 160).mem a := by
        intro a ha; exact (hsP_out a (by omega)).trans (congrFun hsSMem a)
      have hsP_pB : sP.mem (powBase + b) = M := by
        dsimp only [M]; rw [blockM_eq]; exact hsP_pow b le_rfl
      have hsP_p1 : sP.mem (powBase + blockN1 I.n) = I.d ^ blockN1 I.n :=
        hsP_pow _ (blockN1_le I.n)
      have hsP_p2 : sP.mem (powBase + blockN2 I.n) = I.d ^ blockN2 I.n :=
        hsP_pow _ (blockN2_le I.n)
      have hsP_p3 : sP.mem (powBase + blockN3 I.n) = I.d ^ blockN3 I.n :=
        hsP_pow _ (blockN3_le I.n)
      dsimp only [powBase, stride, b] at hsP_pB hsP_p1 hsP_p2 hsP_p3
      wram_exec [hsP_pB, hsP_p1, hsP_p2, hsP_p3, hsS0, hsS1, hsS2, hsS4, hsSD, hsSM, hsSB,
        hsSN1, hsSN2, hsSN12, hsSN3, hsSStr, hsSPB]
      · let A_AB : FillMatrix.Args := ⟨I.n, I.d, I.m, powBase, 0, 1, abBase⟩
        let A_BC : FillMatrix.Args := ⟨I.n, I.d, I.m, powBase, 1, 2, bcBase⟩
        let A_AC : FillMatrix.Args := ⟨I.n, I.d, I.m, powBase, 0, 2, acBase⟩
        have hfm_fit (dst : ℕ) (hdst : dst ≤ acBase) :
            Fits (wBase + 2) (dst + M * M + powBase + b + M + 4 + I.m * stride + 8) :=
          hfit_E.of_le (by
            dsimp only [E, williamsEnvelope, CountPrime.addressBudget, scratch, acBase, bcBase,
              abBase, powBase, stride, b, M] at h2 hdst ⊢
            omega)
        -- Call 1: Fill AB
        wram_call (FillMatrix.exec (w := wBase + 2) I A_AB _ rfl rfl rfl hd
          (by
            refine ⟨by wram_simp [A_AB], by wram_simp [A_AB], by wram_simp [A_AB],
              by wram_simp [A_AB], by wram_simp [A_AB],
              by wram_simp [A_AB, powBase, stride], by wram_simp [A_AB, M],
              by wram_simp [A_AB], by wram_simp [A_AB], by wram_simp [A_AB, blockOff_eq],
              by wram_simp [A_AB, blockOff_eq], by wram_simp [A_AB, blockLim_eq],
              by wram_simp [A_AB, blockLim_eq], by wram_simp [A_AB, abBase, powBase, stride, b]⟩)
          (by dsimp only [A_AB, abBase, powBase, stride]; omega)
          (by dsimp only [A_AB, abBase]; omega)
          (fun a ha => by wram_simp; exact hsP_m0 a ha)
          (fun j hj => by wram_simp; exact hsP_pow j hj)
          (hfm_fit abBase (by dsimp only [acBase, bcBase]; omega)))
          canonical (Fin.castLE_injective _) with sAB ⟨hsAB_mem, hsAB_out⟩
        -- Call 2: Fill BC
        wram_exec [hsS0, hsS1, hsS2, hsSD, hsSM, hsSN1, hsSN12, hsSStr, hsSPB]
        wram_call (FillMatrix.exec (w := wBase + 2) I A_BC _ rfl rfl rfl hd
          (by
            refine ⟨by wram_simp [A_BC], by wram_simp [A_BC], by wram_simp [A_BC],
              by wram_simp [A_BC], by wram_simp [A_BC],
              by wram_simp [A_BC, powBase, stride], by wram_simp [A_BC, M],
              by wram_simp [A_BC], by wram_simp [A_BC], by wram_simp [A_BC, blockOff_eq],
              by wram_simp [A_BC, blockOff_eq], by wram_simp [A_BC, blockLim_eq],
              by wram_simp [A_BC, blockLim_eq],
              by wram_simp [A_BC, bcBase, abBase, powBase, stride, b, M]⟩)
          (by dsimp only [A_BC, bcBase, abBase, powBase, stride]; omega)
          (by dsimp only [A_BC, bcBase, abBase]; omega)
          (fun a ha => by
            wram_simp
            rw [hsAB_out a (by dsimp only [A_AB, abBase, powBase, stride]; omega)]
            wram_simp; exact hsP_m0 a ha)
          (fun j hj => by
            wram_simp
            rw [hsAB_out _ (by dsimp only [A_AB, A_BC, abBase, powBase, stride, b]; omega)]
            wram_simp; exact hsP_pow j hj)
          (hfm_fit bcBase (by dsimp only [acBase]; omega)))
          canonical (Fin.castLE_injective _) with sBC ⟨hsBC_mem, hsBC_out⟩
        -- Call 3: Fill AC
        wram_exec [hsS0, hsS2, hsSD, hsSM, hsSN1, hsSN12, hsSStr, hsSPB]
        wram_call (FillMatrix.exec (w := wBase + 2) I A_AC _ rfl rfl rfl hd
          (by
            refine ⟨by wram_simp [A_AC], by wram_simp [A_AC], by wram_simp [A_AC],
              by wram_simp [A_AC], by wram_simp [A_AC],
              by wram_simp [A_AC, powBase, stride], by wram_simp [A_AC, M],
              by wram_simp [A_AC], by wram_simp [A_AC], by wram_simp [A_AC, blockOff_eq],
              by wram_simp [A_AC, blockOff_eq], by wram_simp [A_AC, blockLim_eq],
              by wram_simp [A_AC, blockLim_eq],
              by wram_simp [A_AC, acBase, bcBase, abBase, powBase, stride, b, M]⟩)
          (by dsimp only [A_AC, acBase, bcBase, abBase, powBase, stride]; omega)
          (by dsimp only [A_AC, acBase, bcBase, abBase]; omega)
          (fun a ha => by
            wram_simp
            rw [hsBC_out a (by dsimp only [A_BC, bcBase, abBase, powBase, stride]; omega)]
            wram_simp
            rw [hsAB_out a (by dsimp only [A_AB, abBase, powBase, stride]; omega)]
            wram_simp; exact hsP_m0 a ha)
          (fun j hj => by
            wram_simp
            rw [hsBC_out _ (by dsimp only [A_BC, A_AC, bcBase, abBase, powBase, stride, b]; omega)]
            wram_simp
            rw [hsAB_out _ (by dsimp only [A_AB, A_AC, abBase, powBase, stride, b]; omega)]
            wram_simp; exact hsP_pow j hj)
          (hfm_fit acBase le_rfl))
          canonical (Fin.castLE_injective _) with sAC ⟨hsAC_mem, hsAC_out⟩
        -- Call 4: CountPrime with p = 4
        wram_exec [hsS4]
        wram_call (CountPrime.exec (w := wBase) (n := M) (p := 4) (scratch := scratch)
          (a := abBase) (b := bcBase) (c := acBase) (A := 1) _
          (fun q => williamsWeight I 0 1 (q / M) (q % M))
          (fun q => williamsWeight I 1 2 (q / M) (q % M))
          (fun q => williamsWeight I 0 2 (q / M) (q % M))
          (by decide) (by wram_simp) (by wram_simp)
          (by wram_simp [abBase, powBase, stride, b])
          (by wram_simp [bcBase, abBase, powBase, stride, b, M])
          (by wram_simp [acBase, bcBase, abBase, powBase, stride, b, M])
          (by wram_simp [scratch, acBase, bcBase, abBase, powBase, stride, b, M])
          (by dsimp only [scratch, acBase, bcBase]; omega)
          (by dsimp only [scratch, acBase]; omega)
          (by dsimp only [scratch]; omega)
          (fun i _ => williamsWeight_abs_le_one I 0 1 _ _)
          (fun i _ => williamsWeight_abs_le_one I 1 2 _ _)
          (fun i _ => williamsWeight_abs_le_one I 0 2 _ _)
          (fun q hq => by
            wram_simp
            rw [hsAC_out _ (by
              dsimp only [A_AC, acBase, bcBase, abBase, powBase, stride, b]; omega)]
            wram_simp
            rw [hsBC_out _ (by dsimp only [A_BC, bcBase, abBase, powBase, stride, b]; omega)]
            wram_simp
            exact hsAB_mem q hq)
          (fun q hq => by
            wram_simp
            rw [hsAC_out _ (by
              dsimp only [A_AC, acBase, bcBase, abBase, powBase, stride, b]; omega)]
            wram_simp
            exact hsBC_mem q hq)
          (fun q hq => by wram_simp; exact hsAC_mem q hq)
          hmag haddr)
          canonical (Fin.castLE_injective _) with sCP ⟨_, hsCP_res, _⟩
        have hres_eq : sCP.regs CountPrime.Reg.result = I.solCount := by
          have h1 : sCP.regs CountPrime.Reg.result =
              countZeroMod
                (fun α β : Fin M => williamsWeight I 0 1 ((α.val * M + β.val) / M)
                  ((α.val * M + β.val) % M))
                (fun α β : Fin M => williamsWeight I 1 2 ((α.val * M + β.val) / M)
                  ((α.val * M + β.val) % M))
                (fun α β : Fin M => williamsWeight I 0 2 ((α.val * M + β.val) / M)
                  ((α.val * M + β.val) % M)) 4 := hsCP_res
          rw [h1, ← countZeroMod_eq_solCount I hd]
          have hM_pos : 0 < M := by
            dsimp only [M]; rw [blockM_eq]; exact Nat.pos_of_ne_zero (pow_ne_zero _ hd.ne')
          congr 1 <;> funext α β
          all_goals
            rw [Nat.mul_comm α.val M]
            simp only [Nat.mul_add_div hM_pos, Nat.div_eq_of_lt β.isLt, Nat.add_zero,
              Nat.mul_add_mod, Nat.mod_eq_of_lt β.isLt]
        by_cases hpos : 0 < I.solCount
        · wram_exec [hsS0, hres_eq, hpos]
          refine ⟨by dsimp only [williamsTime, b, M]; omega, by wram_simp, ?_⟩
          wram_simp [I.isSatisfiable_iff_solCount_pos, hpos]
        · wram_exec [hsS0, hres_eq, hpos]
          refine ⟨by dsimp only [williamsTime, b, M]; omega, by wram_simp, ?_⟩
          wram_simp [I.isSatisfiable_iff_solCount_pos, hpos]
      all_goals exact hfit_E.of_le (by
        have hN1 := blockN1_le I.n; have hN2 := blockN2_le I.n; have hN3 := blockN3_le I.n
        dsimp only [E, williamsEnvelope, CountPrime.addressBudget, scratch, acBase, bcBase,
          abBase, powBase, stride, b, M] at h2 ⊢
        omega)
  obtain ⟨y, he, hle1, hiff⟩ := hcore
  have heW := he.mono_width williamsCode_not_readsWidth hW_ge
  obtain ⟨t, ht, hrun⟩ := heW
  exact ⟨y.regs WilliamsRAM.cOut, t + 1, hrun.executes WilliamsRAM.cOut,
    by dsimp only [williamsTime] at ht ⊢; omega, hle1, hiff⟩

/-- **Williams' `#2-CSP` / `2-CSP-SAT` Theorem on the Standard WordRAM**:
`BinaryCSPSAT` is uniformly decidable on the standard WordRAM by one fixed `160`-register
program in `williamsTime I = O((m + 1) · M² + M^{2.81})` instructions at every word width
`w ≥ williamsWidth I`. -/
theorem uniformDecidableInTime_binaryCSPSAT :
    UniformDecidableInTime .standard BinaryCSPSAT
      (fun _ => BinaryCSP.encode) (fun I _ => williamsTime I) (fun I w => williamsWidth I ≤ w) :=
  ⟨160, williamsProgram, fun I _ hw _ => exec_williamsProgram I hw,
    InputAdmissible.of_width williamsWidth (fun _ => le_rfl) inputFits_williamsWidth⟩


/-- Explicit formula for `williamsTime`. -/
theorem williamsTime_eq (I : BinaryCSP) :
    williamsTime I =
      15 * (I.n + 1) + 3 * ((60 * I.m + 22) * (blockM I.n I.d * blockM I.n I.d) + 30) +
        CountPrime.cost (blockM I.n I.d) 4 + 200 := by
  rfl

/-- Explicit formula for `williamsEnvelope`. -/
theorem williamsEnvelope_eq (I : BinaryCSP) :
    williamsEnvelope I =
      let b := blockB I.n
      let M := blockM I.n I.d
      let stride := 2 + I.d * I.d
      let powBase := 4 + I.m * stride
      let abBase := powBase + b + 1
      let bcBase := abBase + M * M
      let acBase := bcBase + M * M
      let scratch := acBase + M * M
      CountPrime.addressBudget M 4 (Nat.clog 2 M) scratch abBase bcBase acBase +
        CountPrime.magnitudeBudget 4 (Nat.clog 2 M) 1 +
        M * I.d + I.d ^ (b + 1) + I.n + I.d + I.m + 64 := by
  rfl

/-- Explicit formula for `williamsWidth`. -/
theorem williamsWidth_eq (I : BinaryCSP) :
    williamsWidth I = Nat.clog 2 (williamsEnvelope I) + 3 := by
  rfl

end Cslib.Algorithms.WordRAM.CSP
