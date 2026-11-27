/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Oracle
import CslibFrontier.Computability.WordRAM.Call
import Mathlib.Tactic.Linarith

/-!
# Generation-Stamped Memory Compilation for Word RAM

This module compiles arbitrary `rand`-free `Cslib.WordRAM.Code .standard` and `OracleCode`
programs (including programs that read `width%`) into a generation-stamped memory bank
`[base, base + 2 * H)` inside a larger physical width `W`:

- Virtual cell `a < H` is stored as `(stamp, value)` at physical addresses `base + 2 * a` and
  `base + 2 * a + 1`.
- Resetting all `H` virtual cells to `0` between calls costs a single increment `gen ← gen + 1`.
- Logical `width%` instructions are routed to a dedicated `stampWidthReg` register so that
  programs running at logical width `w` (`2 ^ w ≤ H`) execute identically inside physical width `W`
  with `≤ 7 * t` instruction overhead and zero memory writes outside `[base, base + 2 * H)`.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

public section

namespace CslibFrontier.WordRAM

open Cslib.WordRAM

/-! ### Generation-Stamped Memory (`stampCode`, `compileOracleStamped`) -/

/-- Virtual memory value at address `a` in generation-stamped bank `[base, base + 2 * H)`. -/
@[expose]
def stampedRead (base gen : ℕ) (phys : ℕ → ℕ) (a : ℕ) : ℕ :=
  if phys (base + 2 * a) = gen then phys (base + 2 * a + 1) else 0

theorem stampedRead_eq_of_eq {base gen : ℕ} {phys : ℕ → ℕ} {a : ℕ}
    (h : phys (base + 2 * a) = gen) :
    stampedRead base gen phys a = phys (base + 2 * a + 1) := by
  simp only [stampedRead, h, ↓reduceIte]

theorem stampedRead_eq_zero_of_ne {base gen : ℕ} {phys : ℕ → ℕ} {a : ℕ}
    (h : phys (base + 2 * a) ≠ gen) :
    stampedRead base gen phys a = 0 := by
  simp only [stampedRead, h, ↓reduceIte]

/-- Physical memory `phys` represents virtual memory `virt` on `[0, H)` at generation `gen` inside
bank `[base, base + 2 * H)`. -/
@[expose]
def MemRepresents (base H gen : ℕ) (phys virt : ℕ → ℕ) : Prop :=
  ∀ a < H, stampedRead base gen phys a = virt a

/-- Every stamp cell in `[base, base + 2 * H)` is at most `gen`, so incrementing `gen` resets all
`H` virtual cells to `0` in `O(1)` time. -/
@[expose]
def StampLe (base H gen : ℕ) (phys : ℕ → ℕ) : Prop :=
  ∀ a < H, phys (base + 2 * a) ≤ gen

/-- Incrementing `gen` above all existing stamps resets virtual memory to all zeros. -/
theorem stampLe_reset {base H gen gen' : ℕ} {phys : ℕ → ℕ} (h : StampLe base H gen phys)
    (hlt : gen < gen') :
    MemRepresents base H gen' phys (fun _ => 0) ∧ StampLe base H gen' phys := by
  refine ⟨fun a ha => ?_, fun a ha => (h a ha).trans (le_of_lt hlt)⟩
  have hne : phys (base + 2 * a) ≠ gen' := by have := h a ha; omega
  simp [stampedRead, hne]

/-- Writing virtual value `v` at address `a < H` in stamped bank `[base, base + 2 * H)`. -/
theorem stampedWrite_memRepresents {base H gen a v : ℕ} {phys virt : ℕ → ℕ}
    (ha : a < H) (hrep : MemRepresents base H gen phys virt) (hst : StampLe base H gen phys) :
    let phys' := Function.update (Function.update phys (base + 2 * a) gen) (base + 2 * a + 1) v
    MemRepresents base H gen phys' (Function.update virt a v) ∧
      StampLe base H gen phys' ∧
      ∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → phys' p = phys p := by
  intro phys'
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun p hp => ?_⟩
  · by_cases hba : b = a
    · subst hba
      simp only [stampedRead, phys',
        Function.update_of_ne (by omega : base + 2 * b ≠ base + 2 * b + 1),
        Function.update_self, ↓reduceIte]
    · have h1 : base + 2 * b ≠ base + 2 * a + 1 := by omega
      have h2 : base + 2 * b ≠ base + 2 * a := by omega
      have h3 : base + 2 * b + 1 ≠ base + 2 * a + 1 := by omega
      have h4 : base + 2 * b + 1 ≠ base + 2 * a := by omega
      simp only [stampedRead, phys', Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne hba]
      exact hrep b hb
  · by_cases hba : b = a
    · subst hba
      simp [phys']
    · simp only [phys', Function.update_of_ne (by omega : base + 2 * b ≠ base + 2 * a + 1),
        Function.update_of_ne (by omega : base + 2 * b ≠ base + 2 * a)]
      exact hst b hb
  · simp only [phys', Function.update_of_ne (by omega : p ≠ base + 2 * a + 1),
      Function.update_of_ne (by omega : p ≠ base + 2 * a)]

/-- Virtual register `i` inside a stamped register file `Fin (r + 6)`. -/
abbrev stampVirtReg {r : ℕ} (i : Fin r) : Fin (r + 6) := Fin.castAdd 6 i

/-- Register holding the physical bank base address. -/
abbrev stampBaseReg {r : ℕ} : Fin (r + 6) := ⟨r, by omega⟩

/-- Register holding the current generation stamp. -/
abbrev stampGenReg {r : ℕ} : Fin (r + 6) := ⟨r + 1, by omega⟩

/-- Scratch register 0 for stamped memory access. -/
abbrev stampS0Reg {r : ℕ} : Fin (r + 6) := ⟨r + 2, by omega⟩

/-- Scratch register 1 for stamped memory access. -/
abbrev stampS1Reg {r : ℕ} : Fin (r + 6) := ⟨r + 3, by omega⟩

/-- Scratch register 2 for stamped memory access. -/
abbrev stampS2Reg {r : ℕ} : Fin (r + 6) := ⟨r + 4, by omega⟩

/-- Register holding the simulated logical word width `w`. -/
abbrev stampWidthReg {r : ℕ} : Fin (r + 6) := ⟨r + 5, by omega⟩

theorem stampVirtReg_val {r : ℕ} (i : Fin r) : (stampVirtReg i).val = i.val := rfl

theorem stampBaseReg_val {r : ℕ} : (stampBaseReg (r := r)).val = r := rfl

theorem stampGenReg_val {r : ℕ} : (stampGenReg (r := r)).val = r + 1 := rfl

theorem stampWidthReg_val {r : ℕ} : (stampWidthReg (r := r)).val = r + 5 := rfl

theorem stampBaseReg_ne_stampGenReg {r : ℕ} : (stampBaseReg (r := r)) ≠ stampGenReg :=
  Fin.ne_of_val_ne (by dsimp [stampBaseReg, stampGenReg]; omega)

theorem stampBaseReg_ne_stampWidthReg {r : ℕ} : (stampBaseReg (r := r)) ≠ stampWidthReg :=
  Fin.ne_of_val_ne (by dsimp [stampBaseReg, stampWidthReg]; omega)

theorem stampGenReg_ne_stampWidthReg {r : ℕ} : (stampGenReg (r := r)) ≠ stampWidthReg :=
  Fin.ne_of_val_ne (by dsimp [stampGenReg, stampWidthReg]; omega)

/-- Translate a single `Op .standard r` into generation-stamped code over `Fin (r + 6)`, routing
logical `width%` instructions to `stampWidthReg`. -/
def stampOp {r : ℕ} : Op .standard r → Code .standard (r + 6)
  | .const d v => .op (.const (stampVirtReg d) v)
  | .copy d s => .op (.copy (stampVirtReg d) (stampVirtReg s))
  | .alu .width d _ => .op (.copy (stampVirtReg d) stampWidthReg)
  | .alu (.bin f) d args => .op (.alu (.bin f) (stampVirtReg d) (stampVirtReg ∘ args))
  | .load d a =>
      let va := stampVirtReg a
      let vd := stampVirtReg d
      let s0 := stampS0Reg (r := r)
      let s1 := stampS1Reg (r := r)
      let s2 := stampS2Reg (r := r)
      let rb := stampBaseReg (r := r)
      let rg := stampGenReg (r := r)
      ram[
        s0 ← va + va;
        s0 ← rb + s0;
        s1 ← *s0;
        if s1 = rg then [
          s2 ← #1;
          s0 ← s0 + s2;
          vd ← *s0
        ] else [
          vd ← #0
        ]
      ]
  | .store a s =>
      let va := stampVirtReg a
      let vs := stampVirtReg s
      let s0 := stampS0Reg (r := r)
      let s1 := stampS1Reg (r := r)
      let rb := stampBaseReg (r := r)
      let rg := stampGenReg (r := r)
      ram[
        s0 ← va + va;
        s0 ← rb + s0;
        *s0 ← rg;
        s1 ← #1;
        s0 ← s0 + s1;
        *s0 ← vs
      ]

/-- Compile a structured program to operate in generation-stamped bank `[base, base + 2 * H)`. -/
def stampCode {r : ℕ} : Code .standard r → Code .standard (r + 6)
  | .op o => stampOp o
  | .seq c₁ c₂ => .seq (stampCode c₁) (stampCode c₂)
  | .branch cond pos neg => .branch (cond.rename stampVirtReg) (stampCode pos) (stampCode neg)
  | .loop cond body => .loop (cond.rename stampVirtReg) (stampCode body)
  | .rand dst src => .rand (stampVirtReg dst) (stampVirtReg src)

/-- `stampCode` produces `rand`-free code whenever `c` is `rand`-free. -/
theorem isRandFree_stampCode {r : ℕ} {c : Code .standard r} (hc : c.IsRandFree) :
    (stampCode c).IsRandFree := by
  induction c with
  | op o =>
    cases o with
    | alu f _ _ => cases f <;> trivial
    | _ => trivial
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hc.1, ih₂ hc.2⟩
  | branch _ _ _ ihp ihn => exact ⟨ihp hc.1, ihn hc.2⟩
  | loop _ _ ih => exact ih hc
  | rand _ _ => exact hc

private theorem cond_holds_of_regs_eq' {r : ℕ} {cond : Cond r} {x₁ x₂ : Data r}
    (hr : x₂.regs = x₁.regs) : cond.Holds x₂ ↔ cond.Holds x₁ := by
  cases cond <;> simp [Cond.Holds, hr]

private theorem stampOp_exec {r w W base H gen : ℕ} {o : Op .standard r} {x₀ y₀ : Data r}
    {x : Data (r + 6)}
    (hx₀ : x₀.Bounded w) (hH : 2 ^ w ≤ H)
    (hbase : base + 2 * H ≤ 2 ^ W) (ho : o.eval w x₀ = some y₀)
    (hB : x.regs stampBaseReg = base) (hG : x.regs stampGenReg = gen)
    (hW : x.regs stampWidthReg = w)
    (hregs : x.regs ∘ stampVirtReg = x₀.regs)
    (hrep : MemRepresents base H gen x.mem x₀.mem) (hst : StampLe base H gen x.mem) :
    ∃ y : Data (r + 6),
      ExecWithin W (stampOp o) x y 7 ∧
      y.regs stampBaseReg = base ∧
      y.regs stampGenReg = gen ∧
      y.regs stampWidthReg = w ∧
      y.regs ∘ stampVirtReg = y₀.regs ∧
      MemRepresents base H gen y.mem y₀.mem ∧
      StampLe base H gen y.mem ∧
      ∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → y.mem p = x.mem p := by
  have h1_fits : Fits W 1 := by
    have hp : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    exact show 1 < 2 ^ W by omega
  have hw : w ≤ W := by
    have : 2 ^ w < 2 ^ W := by have := Nat.one_le_two_pow (n := w); omega
    exact le_of_lt ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp this)
  have hne_bgw : ∀ i : Fin r,
      stampVirtReg i ≠ stampBaseReg ∧ stampVirtReg i ≠ stampGenReg ∧
        stampVirtReg i ≠ stampWidthReg := fun i =>
    ⟨Fin.ne_of_val_ne (by simp; omega), Fin.ne_of_val_ne (by simp; omega),
      Fin.ne_of_val_ne (by simp; omega)⟩
  cases o with
  | const d v =>
    have hoW := Op.eval_mono_width (by simp [Op.ReadsWidth]) ho hw
    obtain ⟨hv, rfl⟩ := Data.put_eq_some.mp hoW
    refine ⟨x.set (stampVirtReg d) v, (ExecWithin.const hv).mono (by omega),
      ?_, ?_, ?_, ?_, hrep, hst, fun _ _ => rfl⟩
    · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).1.symm, hB]
    · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).2.1.symm, hG]
    · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).2.2.symm, hW]
    · funext i
      simp only [Function.comp_apply, Data.set_regs]
      by_cases hi : i = d
      · subst hi; simp
      · rw [Function.update_of_ne (fun h => hi (Fin.castAdd_injective r 6 h)),
          Function.update_of_ne hi]
        exact congrFun hregs i
  | copy d s =>
    cases ho
    refine ⟨x.set (stampVirtReg d) (x.regs (stampVirtReg s)), ExecWithin.copy.mono (by omega),
      ?_, ?_, ?_, ?_, hrep, hst, fun _ _ => rfl⟩
    · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).1.symm, hB]
    · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).2.1.symm, hG]
    · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).2.2.symm, hW]
    · funext i
      simp only [Function.comp_apply, Data.set_regs]
      by_cases hi : i = d
      · subst hi; simp only [Function.update_self]; exact congrFun hregs s
      · rw [Function.update_of_ne (fun h => hi (Fin.castAdd_injective r 6 h)),
          Function.update_of_ne hi]
        exact congrFun hregs i
  | alu f d args =>
    cases f with
    | width =>
      simp only [Op.eval, StandardOp.eval] at ho
      obtain ⟨-, rfl⟩ := Data.put_eq_some.mp ho
      refine ⟨x.set (stampVirtReg d) (x.regs stampWidthReg), ExecWithin.copy.mono (by omega),
        ?_, ?_, ?_, ?_, hrep, hst, fun _ _ => rfl⟩
      · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).1.symm, hB]
      · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).2.1.symm, hG]
      · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).2.2.symm, hW]
      · funext i
        simp only [Function.comp_apply, Data.set_regs]
        by_cases hi : i = d
        · subst hi; simp [hW]
        · rw [Function.update_of_ne (fun h => hi (Fin.castAdd_injective r 6 h)),
            Function.update_of_ne hi]
          exact congrFun hregs i
    | bin f =>
      have hoW := Op.eval_mono_width (by simp [Op.ReadsWidth]) ho hw
      obtain ⟨v, hval, hv, rfl⟩ := Op.eval_alu_eq_some.mp hoW
      have hval' : Basis.standard.interp W (.bin f) (x.regs ∘ (stampVirtReg ∘ args)) = some v := by
        simpa only [show x.regs ∘ (stampVirtReg ∘ args) = x₀.regs ∘ args by
          funext k; exact congrFun hregs (args k)] using hval
      refine ⟨x.set (stampVirtReg d) v, (ExecWithin.alu hval' hv).mono (by omega),
        ?_, ?_, ?_, ?_, hrep, hst, fun _ _ => rfl⟩
      · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).1.symm, hB]
      · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).2.1.symm, hG]
      · simp [Data.set_regs, Function.update_of_ne (hne_bgw d).2.2.symm, hW]
      · funext i
        simp only [Function.comp_apply, Data.set_regs]
        by_cases hi : i = d
        · subst hi; simp
        · rw [Function.update_of_ne (fun h => hi (Fin.castAdd_injective r 6 h)),
            Function.update_of_ne hi]
          exact congrFun hregs i
  | load d a =>
    cases ho
    have hBS0 : (stampBaseReg (r := r)) ≠ stampS0Reg := Fin.ne_of_val_ne (by simp)
    have hBS1 : (stampBaseReg (r := r)) ≠ stampS1Reg := Fin.ne_of_val_ne (by simp)
    have hBS2 : (stampBaseReg (r := r)) ≠ stampS2Reg := Fin.ne_of_val_ne (by simp)
    have hGS0 : (stampGenReg (r := r)) ≠ stampS0Reg := Fin.ne_of_val_ne (by simp)
    have hGS1 : (stampGenReg (r := r)) ≠ stampS1Reg := Fin.ne_of_val_ne (by simp)
    have hGS2 : (stampGenReg (r := r)) ≠ stampS2Reg := Fin.ne_of_val_ne (by simp)
    have hWS0 : (stampWidthReg (r := r)) ≠ stampS0Reg := Fin.ne_of_val_ne (by simp)
    have hWS1 : (stampWidthReg (r := r)) ≠ stampS1Reg := Fin.ne_of_val_ne (by simp)
    have hWS2 : (stampWidthReg (r := r)) ≠ stampS2Reg := Fin.ne_of_val_ne (by simp)
    have hS01 : (stampS0Reg (r := r)) ≠ stampS1Reg := Fin.ne_of_val_ne (by simp)
    have hS02 : (stampS0Reg (r := r)) ≠ stampS2Reg := Fin.ne_of_val_ne (by simp)
    have ha_lt : x₀.regs a < H := lt_of_lt_of_le (hx₀.1 a) hH
    have hva : x.regs (stampVirtReg a) = x₀.regs a := congrFun hregs a
    have h2a_fits : Fits W (x.regs (stampVirtReg a) + x.regs (stampVirtReg a)) := by
      rw [hva]; exact show x₀.regs a + x₀.regs a < 2 ^ W by omega
    let x1 := x.set stampS0Reg (x.regs (stampVirtReg a) + x.regs (stampVirtReg a))
    have hx1_s0 : x1.regs stampS0Reg = 2 * x₀.regs a := by simp [x1, hva]; omega
    have hx1_rb : x1.regs stampBaseReg = base := by simp [x1, hB, hBS0]
    have hx1_rg : x1.regs stampGenReg = gen := by simp [x1, hG, hGS0]
    have hx1_rw : x1.regs stampWidthReg = w := by simp [x1, hW, hWS0]
    have haddr_fits : Fits W (x1.regs stampBaseReg + x1.regs stampS0Reg) := by
      rw [hx1_rb, hx1_s0]; exact show base + 2 * x₀.regs a < 2 ^ W by omega
    let x2 := x1.set stampS0Reg (x1.regs stampBaseReg + x1.regs stampS0Reg)
    have hx2_s0 : x2.regs stampS0Reg = base + 2 * x₀.regs a := by simp [x2, hx1_rb, hx1_s0]
    have hx2_rg : x2.regs stampGenReg = gen := by simp [x2, hx1_rg, hGS0]
    have hx2_rw : x2.regs stampWidthReg = w := by simp [x2, hx1_rw, hWS0]
    let x3 := x2.set stampS1Reg (x2.mem (x2.regs stampS0Reg))
    have hx3_s0 : x3.regs stampS0Reg = base + 2 * x₀.regs a := by simp [x3, hx2_s0, hS01]
    have hx3_s1 : x3.regs stampS1Reg = x.mem (base + 2 * x₀.regs a) := by
      simp only [x3, Data.set_regs, Function.update_self, hx2_s0]; rfl
    have hx3_rg : x3.regs stampGenReg = gen := by simp [x3, hx2_rg, hGS1]
    have hx3_rb : x3.regs stampBaseReg = base := by simp [x3, x2, hx1_rb, hBS1, hBS0]
    have hx3_rw : x3.regs stampWidthReg = w := by simp [x3, hx2_rw, hWS1]
    have hx3_virt : ∀ i : Fin r, x3.regs (stampVirtReg i) = x₀.regs i := fun i => by
      have h0 : stampVirtReg i ≠ stampS0Reg := Fin.ne_of_val_ne (by simp; omega)
      have h1 : stampVirtReg i ≠ stampS1Reg := Fin.ne_of_val_ne (by simp; omega)
      simp only [x3, x2, x1, Data.set_regs, Function.update_of_ne h1, Function.update_of_ne h0]
      exact congrFun hregs i
    have hs1 : ExecWithin W (.op (.bin .add stampS0Reg (stampVirtReg a) (stampVirtReg a))) x x1 1 :=
      ExecWithin.bin h2a_fits
    have hs2 : ExecWithin W (.op (.bin .add stampS0Reg stampBaseReg stampS0Reg)) x1 x2 1 :=
      ExecWithin.bin haddr_fits
    have hs3 : ExecWithin W (.op (Op.load (B := .standard) stampS1Reg stampS0Reg)) x2 x3 1 :=
      ExecWithin.load
    by_cases hst_eq : x.mem (base + 2 * x₀.regs a) = gen
    · have hcond : (Cond.eq stampS1Reg stampGenReg).Holds x3 := by
        simp [Cond.Holds, hx3_s1, hx3_rg, hst_eq]
      let x4 := x3.set stampS2Reg 1
      have hx4_s0 : x4.regs stampS0Reg = base + 2 * x₀.regs a := by simp [x4, hx3_s0, hS02]
      have hx4_s2 : x4.regs stampS2Reg = 1 := by simp [x4]
      have haddr1_fits : Fits W (x4.regs stampS0Reg + x4.regs stampS2Reg) := by
        rw [hx4_s0, hx4_s2]; exact show base + 2 * x₀.regs a + 1 < 2 ^ W by omega
      let x5 := x4.set stampS0Reg (x4.regs stampS0Reg + x4.regs stampS2Reg)
      have hx5_s0 : x5.regs stampS0Reg = base + 2 * x₀.regs a + 1 := by simp [x5, hx4_s0, hx4_s2]
      let x6 := x5.set (stampVirtReg d) (x5.mem (x5.regs stampS0Reg))
      have hval_eq : x5.mem (x5.regs stampS0Reg) = x₀.mem (x₀.regs a) := by
        have hr := hrep (x₀.regs a) ha_lt
        simp only [stampedRead, hst_eq, ↓reduceIte] at hr
        rw [hx5_s0]; exact hr
      have hb_exec : ExecWithin W
          (.seq (.op (.const stampS2Reg 1))
            (.seq (.op (.bin .add stampS0Reg stampS0Reg stampS2Reg))
              (.op (.load (stampVirtReg d) stampS0Reg))))
          x3 x6 3 :=
        (ExecWithin.const h1_fits).seq ((ExecWithin.bin haddr1_fits).seq ExecWithin.load)
      refine ⟨x6,
        (hs1.seq (hs2.seq (hs3.seq (ExecWithin.branch_pos hcond hb_exec)))).mono (by omega),
        ?_, ?_, ?_, ?_, hrep, hst, fun _ _ => rfl⟩
      · simp [x6, x5, x4, hx3_rb, (hne_bgw d).1.symm, hBS0, hBS2]
      · simp [x6, x5, x4, hx3_rg, (hne_bgw d).2.1.symm, hGS0, hGS2]
      · simp [x6, x5, x4, hx3_rw, (hne_bgw d).2.2.symm, hWS0, hWS2]
      · funext i
        simp only [Function.comp_apply, x6, Data.set_regs]
        by_cases hi : i = d
        · subst hi; simp [hval_eq]
        · have h0 : stampVirtReg i ≠ stampS0Reg := Fin.ne_of_val_ne (by simp; omega)
          have h2 : stampVirtReg i ≠ stampS2Reg := Fin.ne_of_val_ne (by simp; omega)
          rw [Function.update_of_ne (fun h => hi (Fin.castAdd_injective r 6 h)),
            Function.update_of_ne hi]
          simp [x5, x4, h0, h2, hx3_virt i]
    · have hcond : ¬(Cond.eq stampS1Reg stampGenReg).Holds x3 := by
        simp [Cond.Holds, hx3_s1, hx3_rg, hst_eq]
      let x4 := x3.set (stampVirtReg d) 0
      have hval_eq : (0 : ℕ) = x₀.mem (x₀.regs a) := by
        have hr := hrep (x₀.regs a) ha_lt
        simp only [stampedRead, hst_eq, ↓reduceIte] at hr
        exact hr
      refine ⟨x4, (hs1.seq (hs2.seq (hs3.seq
          (ExecWithin.branch_neg hcond (ExecWithin.const (fits_zero W)))))).mono (by omega),
        ?_, ?_, ?_, ?_, hrep, hst, fun _ _ => rfl⟩
      · simp [x4, hx3_rb, (hne_bgw d).1.symm]
      · simp [x4, hx3_rg, (hne_bgw d).2.1.symm]
      · simp [x4, hx3_rw, (hne_bgw d).2.2.symm]
      · funext i
        simp only [Function.comp_apply, x4, Data.set_regs]
        by_cases hi : i = d
        · subst hi; simp [hval_eq]
        · rw [Function.update_of_ne (fun h => hi (Fin.castAdd_injective r 6 h)),
            Function.update_of_ne hi]
          exact hx3_virt i
  | store a s =>
    cases ho
    have hBS0 : (stampBaseReg (r := r)) ≠ stampS0Reg := Fin.ne_of_val_ne (by simp)
    have hBS1 : (stampBaseReg (r := r)) ≠ stampS1Reg := Fin.ne_of_val_ne (by simp)
    have hGS0 : (stampGenReg (r := r)) ≠ stampS0Reg := Fin.ne_of_val_ne (by simp)
    have hGS1 : (stampGenReg (r := r)) ≠ stampS1Reg := Fin.ne_of_val_ne (by simp)
    have hWS0 : (stampWidthReg (r := r)) ≠ stampS0Reg := Fin.ne_of_val_ne (by simp)
    have hWS1 : (stampWidthReg (r := r)) ≠ stampS1Reg := Fin.ne_of_val_ne (by simp)
    have hS01 : (stampS0Reg (r := r)) ≠ stampS1Reg := Fin.ne_of_val_ne (by simp)
    have ha_lt : x₀.regs a < H := lt_of_lt_of_le (hx₀.1 a) hH
    have hva : x.regs (stampVirtReg a) = x₀.regs a := congrFun hregs a
    have hvs : x.regs (stampVirtReg s) = x₀.regs s := congrFun hregs s
    have h2a_fits : Fits W (x.regs (stampVirtReg a) + x.regs (stampVirtReg a)) := by
      rw [hva]; exact show x₀.regs a + x₀.regs a < 2 ^ W by omega
    let x1 := x.set stampS0Reg (x.regs (stampVirtReg a) + x.regs (stampVirtReg a))
    have hx1_s0 : x1.regs stampS0Reg = 2 * x₀.regs a := by simp [x1, hva]; omega
    have hx1_rb : x1.regs stampBaseReg = base := by simp [x1, hB, hBS0]
    have hx1_rw : x1.regs stampWidthReg = w := by simp [x1, hW, hWS0]
    have haddr_fits : Fits W (x1.regs stampBaseReg + x1.regs stampS0Reg) := by
      rw [hx1_rb, hx1_s0]; exact show base + 2 * x₀.regs a < 2 ^ W by omega
    let x2 := x1.set stampS0Reg (x1.regs stampBaseReg + x1.regs stampS0Reg)
    have hx2_s0 : x2.regs stampS0Reg = base + 2 * x₀.regs a := by simp [x2, hx1_rb, hx1_s0]
    have hx2_rg : x2.regs stampGenReg = gen := by simp [x2, x1, hG, hGS0]
    have hx2_rw : x2.regs stampWidthReg = w := by simp [x2, hx1_rw, hWS0]
    let x3 := x2.write (x2.regs stampS0Reg) (x2.regs stampGenReg)
    let x4 := x3.set stampS1Reg 1
    have hx4_s0 : x4.regs stampS0Reg = base + 2 * x₀.regs a := by simp [x4, x3, hx2_s0, hS01]
    have hx4_s1 : x4.regs stampS1Reg = 1 := by simp [x4]
    have haddr1_fits : Fits W (x4.regs stampS0Reg + x4.regs stampS1Reg) := by
      rw [hx4_s0, hx4_s1]; exact show base + 2 * x₀.regs a + 1 < 2 ^ W by omega
    let x5 := x4.set stampS0Reg (x4.regs stampS0Reg + x4.regs stampS1Reg)
    have hx5_s0 : x5.regs stampS0Reg = base + 2 * x₀.regs a + 1 := by simp [x5, hx4_s0, hx4_s1]
    have hx5_vs : x5.regs (stampVirtReg s) = x₀.regs s := by
      have h0 : stampVirtReg s ≠ stampS0Reg := Fin.ne_of_val_ne (by simp; omega)
      have h1 : stampVirtReg s ≠ stampS1Reg := Fin.ne_of_val_ne (by simp; omega)
      simp [x5, x4, x3, x2, x1, h0, h1, hvs]
    let x6 := x5.write (x5.regs stampS0Reg) (x5.regs (stampVirtReg s))
    have hx6_mem : x6.mem = Function.update (Function.update x.mem (base + 2 * x₀.regs a) gen)
        (base + 2 * x₀.regs a + 1) (x₀.regs s) := by
      simp only [x6, Data.write_mem, hx5_s0, hx5_vs]
      simp only [x5, x4, x3, Data.set_mem, Data.write_mem, hx2_s0, hx2_rg]
      rfl
    obtain ⟨hrep', hst', hframe'⟩ := stampedWrite_memRepresents ha_lt hrep hst
    refine ⟨x6,
      ((ExecWithin.bin h2a_fits).seq ((ExecWithin.bin haddr_fits).seq
        (ExecWithin.store.seq ((ExecWithin.const h1_fits).seq
          ((ExecWithin.bin haddr1_fits).seq ExecWithin.store))))).mono (by omega),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [x6, x5, x4, x3, x2, hx1_rb, hBS0, hBS1]
    · simp [x6, x5, x4, x3, hx2_rg, hGS0, hGS1]
    · simp [x6, x5, x4, x3, hx2_rw, hWS0, hWS1]
    · funext i
      have h0 : stampVirtReg i ≠ stampS0Reg := Fin.ne_of_val_ne (by simp; omega)
      have h1 : stampVirtReg i ≠ stampS1Reg := Fin.ne_of_val_ne (by simp; omega)
      simp only [Function.comp_apply, x6, x5, x4, x3, x2, x1, Data.write_regs, Data.set_regs,
        Function.update_of_ne h0, Function.update_of_ne h1]
      exact congrFun hregs i
    · rw [hx6_mem]; exact hrep'
    · rw [hx6_mem]; exact hst'
    · intro p hp; rw [hx6_mem]; exact hframe' p hp

/-- **Stamped execution theorem**: any `rand`-free `WordRAM.Code` (including programs that read
`width%`) executes inside generation-stamped bank `[base, base + 2 * H)` with `≤ 7 * t`
instructions while leaving memory outside `[base, base + 2 * H)` completely untouched. -/
theorem stampCode_exec {r w W t base H gen : ℕ} {c : Code .standard r} {x₀ y₀ : Data r}
    {x : Data (r + 6)}
    (hrf : c.IsRandFree) (hx₀ : x₀.Bounded w) (hH : 2 ^ w ≤ H)
    (hbase : base + 2 * H ≤ 2 ^ W) (h : Exec w c x₀ y₀ t)
    (hB : x.regs stampBaseReg = base) (hG : x.regs stampGenReg = gen)
    (hW : x.regs stampWidthReg = w)
    (hregs : x.regs ∘ stampVirtReg = x₀.regs)
    (hrep : MemRepresents base H gen x.mem x₀.mem) (hst : StampLe base H gen x.mem) :
    ∃ y : Data (r + 6),
      ExecWithin W (stampCode c) x y (7 * t) ∧
      y.regs stampBaseReg = base ∧
      y.regs stampGenReg = gen ∧
      y.regs stampWidthReg = w ∧
      y.regs ∘ stampVirtReg = y₀.regs ∧
      MemRepresents base H gen y.mem y₀.mem ∧
      StampLe base H gen y.mem ∧
      ∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → y.mem p = x.mem p := by
  induction h generalizing x with
  | op ho =>
    obtain ⟨y, hy, hB', hG', hW', hr', hrep', hst', hfr⟩ :=
      stampOp_exec hx₀ hH hbase ho hB hG hW hregs hrep hst
    exact ⟨y, hy.mono (by omega), hB', hG', hW', hr', hrep', hst', hfr⟩
  | seq h₁ _ ih₁ ih₂ =>
    obtain ⟨y, hy, hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩ :=
      ih₁ hrf.1 hx₀ hB hG hW hregs hrep hst
    obtain ⟨z, hz, hBz, hGz, hWz, hrz, hrepz, hstz, hfrz⟩ :=
      ih₂ hrf.2 (h₁.bounded hx₀) hBy hGy hWy hry hrepy hsty
    exact ⟨z, (hy.seq hz).mono (by omega), hBz, hGz, hWz, hrz, hrepz, hstz,
      fun p hp => (hfrz p hp).trans (hfry p hp)⟩
  | branch_pos hcond _ ih =>
    obtain ⟨y, hy, hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩ :=
      ih hrf.1 hx₀ hB hG hW hregs hrep hst
    have hc' : (Cond.rename stampVirtReg _).Holds x :=
      (Cond.holds_rename _ x).mpr ((cond_holds_of_regs_eq' hregs).mpr hcond)
    exact ⟨y, (ExecWithin.branch_pos hc' hy).mono (by omega), hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩
  | branch_neg hcond _ ih =>
    obtain ⟨y, hy, hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩ :=
      ih hrf.2 hx₀ hB hG hW hregs hrep hst
    have hc' : ¬(Cond.rename stampVirtReg _).Holds x := fun h =>
      hcond ((cond_holds_of_regs_eq' hregs).mp ((Cond.holds_rename _ x).mp h))
    exact ⟨y, (ExecWithin.branch_neg hc' hy).mono (by omega), hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩
  | loop_exit hcond =>
    have hc' : ¬(Cond.rename stampVirtReg _).Holds x := fun h =>
      hcond ((cond_holds_of_regs_eq' hregs).mp ((Cond.holds_rename _ x).mp h))
    exact ⟨x, (ExecWithin.loop_exit hc').mono (by omega), hB, hG, hW, hregs, hrep, hst,
      fun _ _ => rfl⟩
  | loop_iter hcond hb _ ihb ihl =>
    obtain ⟨y, hy, hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩ := ihb hrf hx₀ hB hG hW hregs hrep hst
    obtain ⟨z, hz, hBz, hGz, hWz, hrz, hrepz, hstz, hfrz⟩ :=
      ihl hrf (hb.bounded hx₀) hBy hGy hWy hry hrepy hsty
    have hc' : (Cond.rename stampVirtReg _).Holds x :=
      (Cond.holds_rename _ x).mpr ((cond_holds_of_regs_eq' hregs).mpr hcond)
    exact ⟨z, (ExecWithin.loop_iter hc' hy hz).mono (by omega), hBz, hGz, hWz, hrz, hrepz, hstz,
      fun p hp => (hfrz p hp).trans (hfry p hp)⟩

/-- Left-bank register inside `compileOracleStamped`. -/
abbrev stampedCallerReg {r_c r_s : ℕ} (i : Fin (r_c + 6)) : Fin ((r_c + 6) + (r_s + 5)) :=
  Fin.castAdd (r_s + 5) i

/-- Right-bank register inside `compileOracleStamped`. -/
abbrev stampedSubReg {r_c r_s : ℕ} (j : Fin (r_s + 5)) : Fin ((r_c + 6) + (r_s + 5)) :=
  Fin.natAdd (r_c + 6) j

private theorem stampedSubReg_injective {r_c r_s : ℕ} :
    Function.Injective (stampedSubReg (r_c := r_c) (r_s := r_s)) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [stampedSubReg, Fin.val_natAdd] at hv
  exact Fin.ext (by omega)

private theorem stampedCallerReg_ne_subReg {r_c r_s : ℕ} (i : Fin (r_c + 6)) (j : Fin (r_s + 5)) :
    stampedCallerReg (r_s := r_s) i ≠ stampedSubReg (r_c := r_c) j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [stampedCallerReg, stampedSubReg, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem stampedCallerReg_val {r_c r_s : ℕ} (i : Fin (r_c + 6)) :
    (stampedCallerReg (r_s := r_s) i).val = i.val := rfl

theorem stampedCallerReg_injective {r_c r_s : ℕ} :
    Function.Injective (stampedCallerReg (r_c := r_c) (r_s := r_s)) := by
  intro a b h; exact Fin.ext (by simpa [stampedCallerReg_val] using congrArg Fin.val h)

/-- Compile an `OracleCode` into generation-stamped bank `[base, base + 2 * H)` calling a stamped
subroutine `sub` (args: `0 = qBase`, `1 = qLen`, `2 = base`, `3 = gen`, output in `4`). -/
def compileOracleStamped {r_c r_s : ℕ} (c : OracleCode .standard r_c)
    (sub : Code .standard (r_s + 5)) : Code .standard ((r_c + 6) + (r_s + 5)) :=
  match c with
  | .op o => (stampOp o).rename stampedCallerReg
  | .seq c₁ c₂ => .seq (compileOracleStamped c₁ sub) (compileOracleStamped c₂ sub)
  | .branch cond pos neg =>
      .branch (cond.rename (stampedCallerReg ∘ stampVirtReg))
        (compileOracleStamped pos sub) (compileOracleStamped neg sub)
  | .loop cond body =>
      .loop (cond.rename (stampedCallerReg ∘ stampVirtReg)) (compileOracleStamped body sub)
  | .query dst base len =>
      .seq (.op (.copy (stampedSubReg ⟨0, by omega⟩) (stampedCallerReg (stampVirtReg base))))
        (.seq (.op (.copy (stampedSubReg ⟨1, by omega⟩) (stampedCallerReg (stampVirtReg len))))
          (.seq (.op (.copy (stampedSubReg ⟨2, by omega⟩) (stampedCallerReg stampBaseReg)))
            (.seq (.op (.copy (stampedSubReg ⟨3, by omega⟩) (stampedCallerReg stampGenReg)))
              (.seq (sub.rename stampedSubReg)
                (.op (.copy (stampedCallerReg (stampVirtReg dst))
                  (stampedSubReg ⟨4, by omega⟩)))))))

/-- `compileOracleStamped` produces `rand`-free code whenever `sub` is `rand`-free. -/
theorem isRandFree_compileOracleStamped {r_c r_s : ℕ} (c : OracleCode .standard r_c)
    {sub : Code .standard (r_s + 5)} (hsub : sub.IsRandFree) :
    (compileOracleStamped c sub).IsRandFree := by
  induction c with
  | op o =>
    exact isRandFree_rename (by
      cases o with
      | alu f _ _ => cases f <;> trivial
      | _ => trivial)
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | branch _ _ _ ihp ihn => exact ⟨ihp, ihn⟩
  | loop _ _ ih => exact ih
  | query _ _ _ =>
    exact ⟨trivial, trivial, trivial, trivial, isRandFree_rename hsub, trivial⟩

/-- **Stamped inline oracle compilation theorem**: executes `compileOracleStamped c sub` inside
bank `[base, base + 2 * H)` in time `≤ 7 * t + ∑_{q ∈ qs} (T_sub q + 5)`, preserving all memory
outside `[base, base + 2 * H)` whenever `sub` leaves memory unchanged. -/
theorem compileOracleStamped_exec {r_c r_s w W t base H gen : ℕ} {O : List ℕ → Bool}
    {c : OracleCode .standard r_c} {sub : Code .standard (r_s + 5)}
    {x₀ y₀ : Data r_c} {qs : List (List ℕ)} {T_sub : List ℕ → ℕ}
    {x : Data ((r_c + 6) + (r_s + 5))}
    (hx₀ : x₀.Bounded w) (hH : 2 ^ w ≤ H)
    (hbase : base + 2 * H ≤ 2 ^ W)
    (hrun : OracleExec w O c x₀ y₀ t qs)
    (hsub : ∀ (q : List ℕ) (xs : Data (r_s + 5)),
      q ∈ qs →
      xs.regs ⟨0, by omega⟩ + q.length < 2 ^ w →
      xs.regs ⟨1, by omega⟩ = q.length →
      xs.regs ⟨2, by omega⟩ = base →
      xs.regs ⟨3, by omega⟩ = gen →
      q = (List.range q.length).map
        (fun i => stampedRead base gen xs.mem (xs.regs ⟨0, by omega⟩ + i)) →
      (∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → xs.mem p = x.mem p) →
      ∃ z : Data (r_s + 5),
        ExecWithin W sub xs z (T_sub q) ∧
        z.regs ⟨4, by omega⟩ = (O q).toNat ∧
        z.mem = xs.mem)
    (hB : x.regs (stampedCallerReg stampBaseReg) = base)
    (hG : x.regs (stampedCallerReg stampGenReg) = gen)
    (hW : x.regs (stampedCallerReg stampWidthReg) = w)
    (hregs : x.regs ∘ (stampedCallerReg ∘ stampVirtReg) = x₀.regs)
    (hrep : MemRepresents base H gen x.mem x₀.mem) (hst : StampLe base H gen x.mem) :
    ∃ y : Data ((r_c + 6) + (r_s + 5)),
      ExecWithin W (compileOracleStamped c sub) x y (7 * t + (qs.map fun q => T_sub q + 5).sum) ∧
      y.regs (stampedCallerReg stampBaseReg) = base ∧
      y.regs (stampedCallerReg stampGenReg) = gen ∧
      y.regs (stampedCallerReg stampWidthReg) = w ∧
      y.regs ∘ (stampedCallerReg ∘ stampVirtReg) = y₀.regs ∧
      MemRepresents base H gen y.mem y₀.mem ∧
      StampLe base H gen y.mem ∧
      ∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → y.mem p = x.mem p := by
  have hmain : ∀ (m₀ : ℕ → ℕ),
      (∀ (q : List ℕ) (xs : Data (r_s + 5)),
        q ∈ qs →
        xs.regs ⟨0, by omega⟩ + q.length < 2 ^ w →
        xs.regs ⟨1, by omega⟩ = q.length →
        xs.regs ⟨2, by omega⟩ = base →
        xs.regs ⟨3, by omega⟩ = gen →
        q = (List.range q.length).map
          (fun i => stampedRead base gen xs.mem (xs.regs ⟨0, by omega⟩ + i)) →
        (∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → xs.mem p = m₀ p) →
        ∃ z : Data (r_s + 5),
          ExecWithin W sub xs z (T_sub q) ∧
          z.regs ⟨4, by omega⟩ = (O q).toNat ∧
          z.mem = xs.mem) →
      (∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → x.mem p = m₀ p) →
      ∃ y : Data ((r_c + 6) + (r_s + 5)),
        ExecWithin W (compileOracleStamped c sub) x y (7 * t + (qs.map fun q => T_sub q + 5).sum) ∧
        y.regs (stampedCallerReg stampBaseReg) = base ∧
        y.regs (stampedCallerReg stampGenReg) = gen ∧
        y.regs (stampedCallerReg stampWidthReg) = w ∧
        y.regs ∘ (stampedCallerReg ∘ stampVirtReg) = y₀.regs ∧
        MemRepresents base H gen y.mem y₀.mem ∧
        StampLe base H gen y.mem ∧
        ∀ p, ¬(base ≤ p ∧ p < base + 2 * H) → y.mem p = x.mem p := by
    intro m₀ hsub' hx_m₀
    clear hsub
    induction hrun generalizing x with
    | op ho =>
      obtain ⟨y₂, hy₂, hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩ :=
        stampOp_exec (x := x.comap stampedCallerReg) hx₀ hH hbase ho hB hG hW hregs hrep hst
      obtain ⟨y, hy, hy_eq, _⟩ :=
        ExecWithin.rename_post (Fin.castAdd_injective (r_c + 6) (r_s + 5)) ⟨y₂, hy₂, rfl⟩
      have hm : y.mem = y₂.mem := congrArg Data.mem hy_eq.symm
      have hr : y.regs ∘ stampedCallerReg = y₂.regs := congrArg Data.regs hy_eq.symm
      refine ⟨y, hy.mono (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (congrFun hr stampBaseReg).trans hBy
      · exact (congrFun hr stampGenReg).trans hGy
      · exact (congrFun hr stampWidthReg).trans hWy
      · funext i; exact (congrFun hr (stampVirtReg i)).trans (congrFun hry i)
      · rw [hm]; exact hrepy
      · rw [hm]; exact hsty
      · intro p hp; rw [hm]; exact hfry p hp
    | @seq c₁ c₂ _ _ _ _ _ qs₁ qs₂ h₁ _ ih₁ ih₂ =>
      obtain ⟨y, hy, hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩ := ih₁ hx₀ hB hG hW hregs hrep hst
        (fun q xs hq => hsub' q xs (List.mem_append.mpr (Or.inl hq))) hx_m₀
      obtain ⟨z, hz, hBz, hGz, hWz, hrz, hrepz, hstz, hfrz⟩ :=
        ih₂ (h₁.bounded hx₀) hBy hGy hWy hry hrepy hsty
          (fun q xs hq => hsub' q xs (List.mem_append.mpr (Or.inr hq)))
          (fun p hp => (hfry p hp).trans (hx_m₀ p hp))
      refine ⟨z, (hy.seq hz).mono ?_, hBz, hGz, hWz, hrz, hrepz, hstz,
        fun p hp => (hfrz p hp).trans (hfry p hp)⟩
      simp only [List.map_append, List.sum_append]; omega
    | branch_pos hcond _ ih =>
      obtain ⟨y, hy, hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩ :=
        ih hx₀ hB hG hW hregs hrep hst hsub' hx_m₀
      have hc' : (Cond.rename (stampedCallerReg ∘ stampVirtReg) _).Holds x :=
        (Cond.holds_rename _ x).mpr ((cond_holds_of_regs_eq' hregs).mpr hcond)
      exact ⟨y, (ExecWithin.branch_pos hc' hy).mono (by omega),
        hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩
    | branch_neg hcond _ ih =>
      obtain ⟨y, hy, hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩ :=
        ih hx₀ hB hG hW hregs hrep hst hsub' hx_m₀
      have hc' : ¬(Cond.rename (stampedCallerReg ∘ stampVirtReg) _).Holds x := fun h =>
        hcond ((cond_holds_of_regs_eq' hregs).mp ((Cond.holds_rename _ x).mp h))
      exact ⟨y, (ExecWithin.branch_neg hc' hy).mono (by omega),
        hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩
    | loop_exit hcond =>
      have hc' : ¬(Cond.rename (stampedCallerReg ∘ stampVirtReg) _).Holds x := fun h =>
        hcond ((cond_holds_of_regs_eq' hregs).mp ((Cond.holds_rename _ x).mp h))
      exact ⟨x, (ExecWithin.loop_exit hc').mono (by simp), hB, hG, hW, hregs, hrep, hst,
        fun _ _ => rfl⟩
    | @loop_iter cond body _ _ _ _ _ qs₁ qs₂ hcond hb _ ihb ihl =>
      obtain ⟨y, hy, hBy, hGy, hWy, hry, hrepy, hsty, hfry⟩ := ihb hx₀ hB hG hW hregs hrep hst
        (fun q xs hq => hsub' q xs (List.mem_append.mpr (Or.inl hq))) hx_m₀
      obtain ⟨z, hz, hBz, hGz, hWz, hrz, hrepz, hstz, hfrz⟩ :=
        ihl (hb.bounded hx₀) hBy hGy hWy hry hrepy hsty
          (fun q xs hq => hsub' q xs (List.mem_append.mpr (Or.inr hq)))
          (fun p hp => (hfry p hp).trans (hx_m₀ p hp))
      have hc' : (cond.rename (stampedCallerReg ∘ stampVirtReg)).Holds x :=
        (Cond.holds_rename _ x).mpr ((cond_holds_of_regs_eq' hregs).mpr hcond)
      refine ⟨z, (ExecWithin.loop_iter hc' hy hz).mono ?_, hBz, hGz, hWz, hrz, hrepz, hstz,
        fun p hp => (hfrz p hp).trans (hfry p hp)⟩
      simp only [List.map_append, List.sum_append]; omega
    | @query dst qbase qlen x₁ h1 hbl =>
      set q := (List.range (x₁.regs qlen)).map fun i => x₁.mem (x₁.regs qbase + i) with hq_def
      let x1 := x.set (stampedSubReg ⟨0, by omega⟩) (x.regs (stampedCallerReg (stampVirtReg qbase)))
      let x2 := x1.set (stampedSubReg ⟨1,
        by omega⟩) (x1.regs (stampedCallerReg (stampVirtReg qlen)))
      let x3 := x2.set (stampedSubReg ⟨2, by omega⟩) (x2.regs (stampedCallerReg stampBaseReg))
      let x4 := x3.set (stampedSubReg ⟨3, by omega⟩) (x3.regs (stampedCallerReg stampGenReg))
      have hcaller_eq : ∀ k : Fin (r_c + 6),
          x4.regs (stampedCallerReg k) = x.regs (stampedCallerReg k) := by
        intro k
        have h0 := stampedCallerReg_ne_subReg (r_s := r_s) k ⟨0, by omega⟩
        have h1' := stampedCallerReg_ne_subReg (r_s := r_s) k ⟨1, by omega⟩
        have h2' := stampedCallerReg_ne_subReg (r_s := r_s) k ⟨2, by omega⟩
        have h3' := stampedCallerReg_ne_subReg (r_s := r_s) k ⟨3, by omega⟩
        simp only [x4, x3, x2, x1, Data.set_regs, Function.update_of_ne h3',
          Function.update_of_ne h2', Function.update_of_ne h1', Function.update_of_ne h0]
      have hsub_ne : ∀ a b : Fin (r_s + 5), a ≠ b →
          stampedSubReg (r_c := r_c) a ≠ stampedSubReg (r_c := r_c) b := fun a b hab h =>
        hab (stampedSubReg_injective h)
      have hx4_0 : x4.regs (stampedSubReg ⟨0, by omega⟩) = x₁.regs qbase := by
        have h01 := hsub_ne ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.ne_of_val_ne (by simp))
        have h02 := hsub_ne ⟨0, by omega⟩ ⟨2, by omega⟩ (Fin.ne_of_val_ne (by simp))
        have h03 := hsub_ne ⟨0, by omega⟩ ⟨3, by omega⟩ (Fin.ne_of_val_ne (by simp))
        simp only [x4, x3, x2, x1, Data.set_regs, Function.update_of_ne h03,
          Function.update_of_ne h02, Function.update_of_ne h01, Function.update_self]
        exact congrFun hregs qbase
      have hx4_1 : x4.regs (stampedSubReg ⟨1, by omega⟩) = x₁.regs qlen := by
        have h12 := hsub_ne ⟨1, by omega⟩ ⟨2, by omega⟩ (Fin.ne_of_val_ne (by simp))
        have h13 := hsub_ne ⟨1, by omega⟩ ⟨3, by omega⟩ (Fin.ne_of_val_ne (by simp))
        have h0 := stampedCallerReg_ne_subReg (r_s := r_s) (stampVirtReg qlen) ⟨0, by omega⟩
        simp only [x4, x3, x2, x1, Data.set_regs, Function.update_of_ne h13,
          Function.update_of_ne h12, Function.update_self, Function.update_of_ne h0]
        exact congrFun hregs qlen
      have hx4_2 : x4.regs (stampedSubReg ⟨2, by omega⟩) = base := by
        have h23 := hsub_ne ⟨2, by omega⟩ ⟨3, by omega⟩ (Fin.ne_of_val_ne (by simp))
        have h0 := stampedCallerReg_ne_subReg (r_c := r_c) (r_s := r_s) stampBaseReg ⟨0, by omega⟩
        have h1' := stampedCallerReg_ne_subReg (r_c := r_c) (r_s := r_s) stampBaseReg ⟨1, by omega⟩
        simp only [x4, x3, x2, x1, Data.set_regs, Function.update_of_ne h23,
          Function.update_self, Function.update_of_ne h1', Function.update_of_ne h0, hB]
      have hx4_3 : x4.regs (stampedSubReg ⟨3, by omega⟩) = gen := by
        have h0 := stampedCallerReg_ne_subReg (r_c := r_c) (r_s := r_s) stampGenReg ⟨0, by omega⟩
        have h1' := stampedCallerReg_ne_subReg (r_c := r_c) (r_s := r_s) stampGenReg ⟨1, by omega⟩
        have h2' := stampedCallerReg_ne_subReg (r_c := r_c) (r_s := r_s) stampGenReg ⟨2, by omega⟩
        simp only [x4, x3, x2, x1, Data.set_regs, Function.update_self, Function.update_of_ne h2',
          Function.update_of_ne h1', Function.update_of_ne h0, hG]
      have hq_len : q.length = x₁.regs qlen := by simp [hq_def]
      have hq_rep : q = (List.range q.length).map (fun i =>
          stampedRead base gen (x4.comap stampedSubReg).mem
            ((x4.comap stampedSubReg).regs ⟨0, by omega⟩ + i)) := by
        rw [hq_len]
        simp only [Data.comap_mem, Data.comap_regs, hx4_0, x4, x3, x2, x1, Data.set_mem, hq_def]
        refine List.map_congr_left fun i hi => ?_
        rw [List.mem_range] at hi
        change x₁.regs qbase + x₁.regs qlen < 2 ^ w at hbl
        exact (hrep _ (lt_of_lt_of_le (by omega) hH)).symm
      obtain ⟨z, hz, hz4, hzmem⟩ := hsub' q (x4.comap stampedSubReg) (List.mem_singleton_self _)
        (by simp only [Data.comap_regs, hx4_0, hq_len]; exact hbl)
        (by simp only [Data.comap_regs, hx4_1, hq_len])
        (by simp only [Data.comap_regs, hx4_2])
        (by simp only [Data.comap_regs, hx4_3]) hq_rep hx_m₀
      obtain ⟨y₁, hy₁, hy₁_sub, hy₁_frame⟩ :=
        ExecWithin.rename_post (stampedSubReg_injective (r_c := r_c) (r_s := r_s)) ⟨z, hz, rfl⟩
      have hy₁_eq : y₁.comap stampedSubReg = z := hy₁_sub.symm
      have hy₁_mem : y₁.mem = x.mem := by
        have hm : y₁.mem = z.mem := congrArg Data.mem hy₁_eq
        rw [hm, hzmem]; rfl
      have hy₁_4 : y₁.regs (stampedSubReg ⟨4, by omega⟩) = (O q).toNat := by
        have := congrArg (fun d => d.regs ⟨4, by omega⟩) hy₁_eq
        simpa only [Data.comap_regs] using this.trans hz4
      have hy₁_caller : ∀ k : Fin (r_c + 6),
          y₁.regs (stampedCallerReg k) = x.regs (stampedCallerReg k) := fun k =>
        (hy₁_frame (stampedCallerReg k)
          (fun j => (stampedCallerReg_ne_subReg k j).symm)).trans (hcaller_eq k)
      let y := y₁.set (stampedCallerReg (stampVirtReg dst)) (y₁.regs (stampedSubReg ⟨4, by omega⟩))
      have hvd_ne_b : stampVirtReg dst ≠ stampBaseReg := Fin.ne_of_val_ne (by simp; omega)
      have hvd_ne_g : stampVirtReg dst ≠ stampGenReg := Fin.ne_of_val_ne (by simp; omega)
      have hvd_ne_w : stampVirtReg dst ≠ stampWidthReg := Fin.ne_of_val_ne (by simp; omega)
      refine ⟨y, (ExecWithin.copy.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
          (ExecWithin.copy.seq (hy₁.seq ExecWithin.copy))))).mono (by simp; omega),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show y.regs _ = _ from rfl]
        simp only [y, Data.set_regs,
          Function.update_of_ne (fun h => hvd_ne_b (Fin.castAdd_injective _ _ h).symm),
          hy₁_caller, hB]
      · simp only [y, Data.set_regs,
          Function.update_of_ne (fun h => hvd_ne_g (Fin.castAdd_injective _ _ h).symm),
          hy₁_caller, hG]
      · simp only [y, Data.set_regs,
          Function.update_of_ne (fun h => hvd_ne_w (Fin.castAdd_injective _ _ h).symm),
          hy₁_caller, hW]
      · funext i
        simp only [Function.comp_apply, y, Data.set_regs]
        by_cases hi : i = dst
        · subst hi; simp only [Function.update_self, hy₁_4, hq_def]
        · have hne : stampedCallerReg (r_s := r_s) (stampVirtReg i) ≠
              stampedCallerReg (stampVirtReg dst) := fun h =>
            hi (Fin.castAdd_injective r_c 6 (Fin.castAdd_injective (r_c + 6) (r_s + 5) h))
          rw [Function.update_of_ne hne, hy₁_caller, Function.update_of_ne hi]
          exact congrFun hregs i
      · simpa only [y, Data.set_mem, hy₁_mem] using hrep
      · simpa only [y, Data.set_mem, hy₁_mem] using hst
      · intro p _; simp [y, hy₁_mem]
  exact hmain x.mem hsub (fun _ _ => rfl)

end CslibFrontier.WordRAM
