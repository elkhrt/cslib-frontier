/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.WordRAMSATSelfReducibility
import CslibFrontier.Computability.WordRAM.CountingLoop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Brute-Force Word-RAM SAT Solver

Implements `bruteForceSATCode`, a deterministic `rand`-free Word-RAM solver deciding `FinSAT` in
`O(2^n · L)` steps without modifying memory.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

public section

namespace CslibFrontier.Complexity.FineGrained

open Cslib.WordRAM CslibFrontier.WordRAM Cslib.Logic.PL

/-! ### Brute-Force Word-RAM SAT Solver (`bruteForceSATCode`) -/

/-- Brute-force Word-RAM SAT solver checking all `2^n` assignments `0 .. 2^n - 1` against the
encoded CNF formula at `mem[2 .. L]` in `O(2^n · L)` steps without modifying memory.
Output in reg `4`. -/
def bruteForceSATCode : Code .standard 16 :=
  let r0 : Fin 16 := 0; let r1 : Fin 16 := 1; let r2 : Fin 16 := 2; let r3 : Fin 16 := 3
  let r4 : Fin 16 := 4; let r5 : Fin 16 := 5; let r6 : Fin 16 := 6; let r7 : Fin 16 := 7
  let r8 : Fin 16 := 8; let r9 : Fin 16 := 9; let r10 : Fin 16 := 10; let r11 : Fin 16 := 11
  let r12 : Fin 16 := 12; let r13 : Fin 16 := 13; let r14 : Fin 16 := 14; let r15 : Fin 16 := 15
  let litBody : Code .standard 16 :=
    .seq (ram[ r12 ← *r9; r13 ← r12 >>> r1; r14 ← r12 &&& r1;
      r15 ← r5 >>> r13; r15 ← r15 &&& r1 ])
      (.seq (.branch (.eq r15 r14) (.op (.const r11 1)) (.op (.const r15 0)))
        (.op (.bin .add r9 r9 r1)))
  let clauseBody : Code .standard 16 :=
    .seq (ram[ r8 ← *r7; r9 ← r7 + r1; r10 ← r9 + r8; r11 ← #0 ])
      (.seq (.loop (.lt r9 r10) litBody)
        (.seq (.branch (.eq r11 r0) (.op (.const r6 0)) (.op (.const r15 0)))
          (.op (.copy r7 r10))))
  let maskBody : Code .standard 16 :=
    .seq (ram[ r6 ← #1; r7 ← #2 ])
      (.seq (.loop (.lt r7 r2) clauseBody)
        (.seq (.branch (.eq r6 r1) (.op (.const r4 1)) (.op (.const r15 0)))
          (.op (.bin .add r5 r5 r1))))
  let setup : Code .standard 16 := ram[
    r0 ← #0; r1 ← #1; r2 ← *r0; r2 ← r2 + r1;
    r15 ← *r1; r3 ← r1 <<< r15; r4 ← #0; r5 ← #0 ]
  .seq setup (.loop (.lt r5 r3) maskBody)

theorem isRandFree_bruteForceSATCode : bruteForceSATCode.IsRandFree := by
  simp [bruteForceSATCode, Code.IsRandFree]

/-- Execution specification of `bruteForceSATCode`: decides `x ∈ FinSAT` in
`≤ 2^n * (14 * L + 16) + 15`
instructions without changing memory whenever `2^n`, `L + 2`, and `2*n + 2` fit in `w`. -/
theorem bruteForceSATCode_exec {w : ℕ} {x : FinCNF}
    (hw_pow : Fits w (2 ^ x.1)) (hw_mem : Fits w ((encFinCNF x).length + 2))
    (hw_n : Fits w (2 * x.1 + 2)) :
    ∃ y : Data 16,
      ExecWithin w bruteForceSATCode (.init (encFinCNF x)) y
        (2 ^ x.1 * (14 * (encFinCNF x).length + 16) + 15) ∧
      y.regs 4 ≤ 1 ∧ (y.regs 4 = 1 ↔ x ∈ FinSAT) ∧
      y.mem = (Data.init (encFinCNF x) (r := 16)).mem := by
  rcases x with ⟨n, φ⟩
  dsimp only at hw_pow hw_mem hw_n ⊢
  set L := (encFinCNF ⟨n, φ⟩).length
  have h1_f : Fits w 1 := Fits.of_le hw_mem (by omega)
  have h2_f : Fits w 2 := Fits.of_le hw_mem (by omega)
  let x0 : Data 16 := .init (encFinCNF ⟨n, φ⟩)
  have hmem0 : x0.mem 0 = L := by simp [x0, Data.init_mem_zero, L]
  have hmem1 : x0.mem 1 = n := by
    change x0.mem (0 + 1) = n; simp [x0, Data.init_mem_succ, encFinCNF_eq_cons]
  let r0 : Fin 16 := 0; let r1 : Fin 16 := 1; let r2 : Fin 16 := 2; let r3 : Fin 16 := 3
  let r4 : Fin 16 := 4; let r5 : Fin 16 := 5; let r6 : Fin 16 := 6; let r7 : Fin 16 := 7
  let r8 : Fin 16 := 8; let r9 : Fin 16 := 9; let r10 : Fin 16 := 10; let r11 : Fin 16 := 11
  let r12 : Fin 16 := 12; let r13 : Fin 16 := 13; let r14 : Fin 16 := 14; let r15 : Fin 16 := 15
  let s1 := x0.set 0 0; let s2 := s1.set 1 1; let s3 := s2.set 2 L; let s4 := s3.set 2 (L + 1)
  let s5 := s4.set 15 n; let s6 := s5.set 3 (2 ^ n); let s7 := s6.set 4 0; let s8 := s7.set 5 0
  have hsetup : ExecWithin (B := .standard) w (ram[ r0 ← #0; r1 ← #1; r2 ← *r0; r2 ← r2 + r1;
      r15 ← *r1; r3 ← r1 <<< r15; r4 ← #0; r5 ← #0 ]) x0 s8 8 := by
    have e1 : ExecWithin (B := .standard) w (.op (.const 0 0)) x0 s1 1 :=
      ExecWithin.const (fits_zero w)
    have e2 : ExecWithin (B := .standard) w (.op (.const 1 1)) s1 s2 1 :=
      ExecWithin.const h1_f
    have e3 : ExecWithin (B := .standard) w (.op (.load 2 0)) s2 s3 1 := by
      simpa [s3, s2, s1, hmem0] using ExecWithin.load (w := w) (x := s2) (d := 2) (a := 0)
    have e4 : ExecWithin (B := .standard) w (.op (.bin .add 2 2 1)) s3 s4 1 := by
      simpa [s4, s3, s2] using ExecWithin.bin (w := w) (x := s3) (f := .add) (d := 2) (i := 2) (j :=
        1)
        (by simpa [s3, s2] using Fits.of_le hw_mem (by omega))
    have e5 : ExecWithin (B := .standard) w (.op (.load 15 1)) s4 s5 1 := by
      simpa [s5, s4, s3, s2, s1, hmem1] using ExecWithin.load (w := w) (x := s4) (d := 15) (a := 1)
    have e6 : ExecWithin (B := .standard) w (.op (.bin .shiftLeft 3 1 15)) s5 s6 1 := by
      simpa [s6, s5, s4, s3, s2, Nat.shiftLeft_eq] using ExecWithin.bin (w := w) (x := s5) (f :=
        .shiftLeft)
        (d := 3) (i := 1) (j := 15) (by simpa [s5, s4, s3, s2, Nat.shiftLeft_eq] using hw_pow)
    exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq
      ((ExecWithin.const (fits_zero w)).seq (ExecWithin.const (fits_zero w))))))))
  let assignOf (mask : ℕ) : Fin n → Bool := fun v => decide ((mask >>> v.val) % 2 = 1)
  let InvM (mask : ℕ) (d : Data 16) : Prop :=
    d.regs 0 = 0 ∧ d.regs 1 = 1 ∧ d.regs 2 = L + 1 ∧ d.regs 3 = 2 ^ n ∧ d.mem = x0.mem ∧
      d.regs 4 ≤ 1 ∧ (d.regs 4 = 1 ↔ ∃ m < mask, φ.eval (assignOf m) = true)
  have hInvM0 : InvM 0 s8 :=
    ⟨by simp [s8, s7, s6, s5, s4, s3, s2, s1], by simp [s8, s7, s6, s5, s4, s3, s2],
    by simp [s8, s7, s6, s5, s4], by simp [s8, s7, s6], rfl, by simp [s8, s7], by simp [s8, s7]⟩
  obtain ⟨y, hy, hIy, _⟩ := ExecWithin.loop_count (w := w) (N := 2 ^ n) (T := 14 * L + 14)
    (index := 5) (limit := 3) InvM (fun d hd => hd.2.2.2.1)
    (fun d hd hmlt => by
      obtain ⟨hd0, hd1, hd2, hd3, hdmem, hd4le, hd4iff⟩ := hd
      set mask := d.regs 5
      have hm_lt : mask < 2 ^ n := hmlt
      let d1 := d.set 6 1; let d2 := d1.set 7 2
      -- Clause loop by induction on remaining clauses ψ_rem
      have hcl_eval : ∀ (ψ_pre ψ_rem : CNF (Fin n)) (ptr : ℕ) (u : Data 16),
          φ = ψ_pre ++ ψ_rem → ptr = 2 + (encodeClauses ψ_pre).length →
          u.regs 0 = 0 → u.regs 1 = 1 → u.regs 2 = L + 1 → u.regs 3 = 2 ^ n → u.regs 4 = d.regs 4 →
          u.regs 5 = mask → u.regs 7 = ptr → u.mem = x0.mem → u.regs 6 ≤ 1 →
          (u.regs 6 = 1 ↔ ψ_pre.eval (assignOf mask) = true) →
          ∃ v : Data 16,
            ExecWithin w (.loop (.lt 7 2) (.seq (ram[ r8 ← *r7; r9 ← r7 + r1; r10 ← r9 +
              r8; r11 ← #0 ])
              (.seq (.loop (.lt 9 10) (.seq (ram[ r12 ← *r9; r13 ← r12 >>> r1; r14 ← r12 &&& r1;
                  r15 ← r5 >>> r13; r15 ← r15 &&& r1 ])
                (.seq (.branch (.eq r15 r14) (.op (.const r11 1)) (.op (.const r15 0)))
                  (.op (.bin .add r9 r9 r1)))))
                (.seq (.branch (.eq r11 r0) (.op (.const r6 0)) (.op (.const r15 0)))
                  (.op (.copy r7 r10)))))) u v (14 * (encodeClauses ψ_rem).length + 2) ∧
            v.regs 0 = 0 ∧ v.regs 1 = 1 ∧ v.regs 2 = L + 1 ∧ v.regs 3 = 2 ^ n ∧
              v.regs 4 = d.regs 4 ∧
            v.regs 5 = mask ∧ v.mem = x0.mem ∧ v.regs 6 ≤ 1 ∧ (v.regs 6 = 1 ↔
              φ.eval (assignOf mask) = true) := by
        intro ψ_pre ψ_rem
        induction ψ_rem generalizing ψ_pre with
        | nil =>
          intro ptr u hφ hptr hu0 hu1 hu2 hu3 hu4 hu5 hu7 humem hu6le hu6iff
          have hφ' : ψ_pre = φ := by simpa using hφ.symm
          have hL_eq : L = (encodeClauses φ).length + 1 := by
            dsimp only [L]; exact encFinCNF_length ⟨n, φ⟩
          have hstop : ¬(Cond.lt 7 2).Holds u := by simp [Cond.Holds, hu7, hu2, hptr, hφ']; omega
          exact ⟨u, (ExecWithin.loop_exit hstop).mono (by omega), hu0, hu1, hu2, hu3, hu4, hu5,
            humem, hu6le, hφ' ▸ hu6iff⟩
        | cons c ψ_rem ih_cl =>
          intro ptr u hφ hptr hu0 hu1 hu2 hu3 hu4 hu5 hu7 humem hu6le hu6iff
          have hlen_le : c.length + 1 + (encodeClauses ψ_rem).length +
            (encodeClauses ψ_pre).length = L - 1 := by
            have hL_eq : L = (encodeClauses φ).length + 1 := by
              dsimp only [L]; exact encFinCNF_length ⟨n, φ⟩
            have hlen_φ : (encodeClauses φ).length =
                (encodeClauses ψ_pre).length + (c.length + 1 + (encodeClauses ψ_rem).length) := by
              rw [hφ, encodeClauses_append, encodeClauses_cons, List.length_append,
                List.length_append, length_encodeClause]
            omega
          have hcond_c : (Cond.lt 7 2).Holds u := by simp [Cond.Holds, hu7, hu2, hptr]; omega
          have hmem_cLen : u.mem ptr = c.length := by
            rw [humem]
            have hget : (encodeClauses φ)[(encodeClauses ψ_pre).length]? = some c.length := by
              rw [hφ, encodeClauses_append, encodeClauses_cons]
              simp [encodeClause_eq]
            rw [show ptr = ((encodeClauses ψ_pre).length + 1) + 1 by omega]
            simp [x0, Data.init_mem_succ, encFinCNF_eq_cons, hget]
          have hmem_lit : ∀ j (hj : j < c.length), u.mem (ptr + 1 + j) = litCode (c[j]) := by
            intro j hj
            rw [humem]
            have hget : (encodeClauses φ)[(encodeClauses ψ_pre).length + 1 + j]? =
              some (litCode c[j]) := by
              rw [hφ]
              have h1 : encodeClauses (ψ_pre ++ c :: ψ_rem) =
                encodeClauses ψ_pre ++ (c.length :: c.map litCode ++ encodeClauses ψ_rem) := by
                rw [encodeClauses_append, encodeClauses_cons, encodeClause_eq]
              rw [h1, List.getElem?_append_right (by omega), show (encodeClauses ψ_pre).length + 1 +
                j - (encodeClauses ψ_pre).length = j + 1 by omega, List.cons_append,
                List.getElem?_cons_succ, List.getElem?_append_left (by simp [hj]),
                List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some]
            rw [show ptr + 1 + j = ((encodeClauses ψ_pre).length + 1 + j + 1) + 1 by omega]
            simp [x0, Data.init_mem_succ, encFinCNF_eq_cons, hget]
          let u1 := u.set 8 c.length; let u2 := u1.set 9 (ptr + 1); let u3 :=
            u2.set 10 (ptr + 1 + c.length); let u4 := u3.set 11 0
          have hu14 : ExecWithin (B := .standard) w (ram[ r8 ← *r7; r9 ← r7 + r1; r10 ← r9 +
            r8; r11 ← #0 ]) u u4 4 := by
            have e1 : ExecWithin (B := .standard) w (.op (.load 8 7)) u u1 1 := by
              simpa [u1, hu7, hmem_cLen] using ExecWithin.load (w := w) (x := u) (d := 8) (a := 7)
            have e2 : ExecWithin (B := .standard) w (.op (.bin .add 9 7 1)) u1 u2 1 := by
              simpa [u2, u1, hu7, hu1] using ExecWithin.bin (w := w) (x := u1) (f := .add) (d :=
                9) (i := 7) (j := 1)
                (by simpa [u1, hu7, hu1] using Fits.of_le hw_mem (by omega))
            have e3 : ExecWithin (B := .standard) w (.op (.bin .add 10 9 8)) u2 u3 1 := by
              simpa [u3, u2, u1] using ExecWithin.bin (w := w) (x := u2) (f := .add) (d := 10) (i :=
                9) (j := 8)
                (by simpa [u2, u1] using Fits.of_le hw_mem (by omega))
            exact e1.seq (e2.seq (e3.seq (ExecWithin.const (fits_zero w))))
          let LitI (v : Data 16) : Prop :=
            v.regs 0 = 0 ∧ v.regs 1 = 1 ∧ v.regs 2 = L + 1 ∧ v.regs 3 = 2 ^ n ∧
              v.regs 4 = d.regs 4 ∧
              v.regs 5 = mask ∧ v.regs 6 = u.regs 6 ∧ v.regs 10 = ptr + 1 + c.length ∧
                v.mem = x0.mem ∧
              ptr + 1 ≤ v.regs 9 ∧ v.regs 9 ≤ ptr + 1 + c.length ∧
              v.regs 11 ≤ 1 ∧ (v.regs 11 = 1 ↔
                Clause.eval (assignOf mask) (c.take (v.regs 9 - (ptr + 1))) = true)
          have hLI0 : LitI u4 := ⟨by simp [u4, u3, u2, u1, hu0], by simp [u4, u3, u2, u1, hu1],
            by simp [u4, u3, u2, u1, hu2], by simp [u4, u3, u2, u1, hu3], by simp [u4, u3, u2, u1,
              hu4],
            by simp [u4, u3, u2, u1, hu5], by simp [u4, u3, u2, u1], by simp [u4, u3],
            by simp [u4, u3, u2, u1, humem], by simp [u4, u3, u2], by simp [u4, u3, u2],
            by simp [u4], by simp [u4, u3, u2, Clause.eval]⟩
          obtain ⟨u5, hu5_ex, hLI_end, hLI_stop⟩ := ExecWithin.loop_invariant (w := w) (cond :=
            .lt 9 10)
            (body := .seq (ram[ r12 ← *r9; r13 ← r12 >>> r1; r14 ← r12 &&& r1;
                r15 ← r5 >>> r13; r15 ← r15 &&& r1 ])
              (.seq (.branch (.eq r15 r14) (.op (.const r11 1)) (.op (.const r15 0)))
                (.op (.bin .add r9 r9 r1)))) LitI (fun v => ptr + 1 + c.length - v.regs 9)
            (fun v hv hc_l => by
              obtain ⟨hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv10, hvmem, hv9ge, hv9le, hv11le,
                hv11iff⟩ := hv
              have hv9_lt : v.regs 9 < ptr + 1 + c.length := by
                simp only [Cond.Holds, hv10] at hc_l; exact hc_l
              set j := v.regs 9 - (ptr + 1)
              have hj_lt : j < c.length := by omega
              have hv9_eq : v.regs 9 = ptr + 1 + j := by omega
              set l := c[j]
              have hvm : v.mem (v.regs 9) = litCode l := by
                rw [hvmem, ← humem, hv9_eq]; exact hmem_lit j hj_lt
              have hr_sh_f : Fits w (mask >>> l.1.val) :=
                Fits.of_le (Fits.of_le hw_pow (le_of_lt hm_lt))
                  (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _)
              let v1 := v.set 12 (litCode l); let v2 := v1.set 13 l.1.val; let v3 :=
                v2.set 14 l.2.toNat
              let v4 := v3.set 15 (mask >>> l.1.val); let v5 := v4.set 15 ((mask >>> l.1.val) % 2)
              have he15 : ExecWithin (B := .standard) w
                  (ram[ r12 ← *r9; r13 ← r12 >>> r1; r14 ← r12 &&& r1;
                    r15 ← r5 >>> r13; r15 ← r15 &&& r1 ]) v v5 5 := by
                have e1 : ExecWithin (B := .standard) w (.op (.load 12 9)) v v1 1 := by
                  simpa [v1, hvm] using ExecWithin.load (w := w) (x := v) (d := 12) (a := 9)
                have e2 : ExecWithin (B := .standard) w
                    (.op (.bin .shiftRight 13 12 1)) v1 v2 1 := by
                  simpa [v2, v1, hv1, litCode_shiftRight] using ExecWithin.bin (w := w) (x :=
                    v1) (f := .shiftRight) (d := 13) (i := 12) (j := 1)
                    (by simpa [v1, hv1, litCode_shiftRight] using
                      Fits.of_le hw_n (by have := l.1.isLt; omega))
                have e3 : ExecWithin (B := .standard) w (.op (.bin .and 14 12 1)) v2 v3 1 := by
                  have hand : litCode l &&& 1 = l.2.toNat := litCode_and_one l
                  have h12 : v2.regs 12 = litCode l := by simp [v2, v1]
                  have h1' : v2.regs 1 = 1 := by simp [v2, v1, hv1]
                  have hf : Fits w l.2.toNat := by cases l.2 <;> exact Fits.of_le h1_f (by simp)
                  have hb := ExecWithin.bin (w := w) (x := v2) (f := .and) (d := 14) (i := 12)
                    (j := 1) (by rw [h12, h1']; dsimp only [BinOp.eval]; rw [hand]; exact hf)
                  simpa only [v3, BinOp.eval, h12, h1', hand] using hb
                have e4 : ExecWithin (B := .standard) w
                    (.op (.bin .shiftRight 15 5 13)) v3 v4 1 := by
                  simpa [v4, v3, v2, v1, hv5] using ExecWithin.bin (w := w) (x := v3) (f :=
                    .shiftRight) (d := 15) (i := 5) (j := 13)
                    (by simpa [v3, v2, v1, hv5] using hr_sh_f)
                have e5 : ExecWithin (B := .standard) w (.op (.bin .and 15 15 1)) v4 v5 1 := by
                  simpa [v5, v4, v3, v2, v1, hv1, Nat.and_one_is_mod] using ExecWithin.bin (w :=
                    w) (x := v4) (f := .and) (d := 15) (i := 15) (j := 1)
                    (by simpa [v4, v3, v2, v1, hv1,
                      Nat.and_one_is_mod] using Fits.of_le h1_f (by omega))
                exact e1.seq (e2.seq (e3.seq (e4.seq e5)))
              have hmatch : ((mask >>> l.1.val) % 2 = l.2.toNat) ↔
                (Literal.eval (assignOf mask) l = true) := by
                simp only [Literal.eval_eq_true_iff, assignOf]
                rcases Nat.mod_two_eq_zero_or_one (mask >>> l.1.val) with hm | hm <;>
                  cases l.2 <;> simp [hm]
              let v6 := if (mask >>> l.1.val) % 2 = l.2.toNat then v5.set 11 1 else v5.set 15 0
              have he6 : ExecWithin (B := .standard) w
                  (.branch (.eq 15 14) (.op (.const 11 1)) (.op (.const 15 0))) v5 v6 3 := by
                by_cases hm' : (mask >>> l.1.val) % 2 = l.2.toNat
                · simpa [v6, hm'] using
                    (ExecWithin.branch_pos (by simp [Cond.Holds, v5, v4, v3, hm'])
                      (ExecWithin.const h1_f)).mono (by omega)
                · simpa [v6, hm'] using
                    (ExecWithin.branch_neg (by simp [Cond.Holds, v5, v4, v3, hm'])
                      (ExecWithin.const (fits_zero w))).mono (by omega)
              let v7 := v6.set 9 (v.regs 9 + 1)
              have he7 : ExecWithin w (.op (.bin .add 9 9 1)) v6 v7 1 := by
                have h9' : v6.regs 9 = v.regs 9 := by
                  dsimp [v6]; split_ifs <;> simp [v5, v4, v3, v2, v1]
                have h1' : v6.regs 1 = 1 := by
                  dsimp [v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hv1]
                simpa [v7, h9', h1'] using ExecWithin.bin (w := w) (x := v6) (f := .add) (d :=
                  9) (i := 9) (j := 1)
                  (by simpa [h9', h1'] using Fits.of_le hw_mem (by omega))
              refine ⟨v7, (he15.seq (he6.seq he7)).mono (by omega : 5 + (3 + 1) ≤ 9),
                ⟨by dsimp [v7, v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hv0],
                  by dsimp [v7, v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hv1],
                  by dsimp [v7, v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hv2],
                  by dsimp [v7, v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hv3],
                  by dsimp [v7, v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hv4],
                  by dsimp [v7, v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hv5],
                  by dsimp [v7, v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hv6],
                  by dsimp [v7, v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hv10],
                  by dsimp [v7, v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hvmem],
                  by simp [v7]; omega, by simp [v7]; omega,
                  by dsimp [v7, v6]; split_ifs <;> simp [v5, v4, v3, v2, v1, hv11le],
                  ?_⟩, by simp [v7]; omega⟩
              have htake_eq : v7.regs 9 - (ptr + 1) = j + 1 := by simp [v7]; omega
              rw [htake_eq, List.take_succ_eq_append_getElem hj_lt]
              simp only [Clause.eval, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
                Bool.or_eq_true]
              dsimp [v7, v6]; split_ifs with hm'
              · simp only [Data.set_regs, Function.update_of_ne (by decide : (11 : Fin 16) ≠ 9),
                  Function.update_self, true_iff]
                exact Or.inr (hmatch.mp hm')
              · have hnf : Literal.eval (assignOf mask) l ≠ true := fun h => hm' (hmatch.mpr h)
                have hnf' : ¬(Literal.eval (assignOf mask) c[j] = true) := hnf
                simp only [v5, v4, v3, v2, v1, Data.set_regs,
                  Function.update_of_ne (by decide : (11 : Fin 16) ≠ 9),
                  Function.update_of_ne (by decide : (11 : Fin 16) ≠ 15),
                  Function.update_of_ne (by decide : (11 : Fin 16) ≠ 14),
                  Function.update_of_ne (by decide : (11 : Fin 16) ≠ 13),
                  Function.update_of_ne (by decide : (11 : Fin 16) ≠ 12), hv11iff]
                simp [Clause.eval, hnf']) hLI0
          obtain ⟨h50, h51, h52, h53, h54, h55, h56, h510, h5mem, h59ge, h59le, h511le, h511iff⟩ :=
            hLI_end
          have h59 : u5.regs 9 = ptr + 1 + c.length := by
            simp only [Cond.Holds, h510] at hLI_stop; omega
          have h511_c : u5.regs 11 = 1 ↔ c.eval (assignOf mask) = true := by
            rw [h511iff, h59, show ptr + 1 + c.length - (ptr + 1) =
              c.length by omega, List.take_length]
          let u6 := if u5.regs 11 = 0 then u5.set 6 0 else u5.set 15 0
          have he6 : ExecWithin (B := .standard) w
              (.branch (.eq 11 0) (.op (.const 6 0)) (.op (.const 15 0))) u5 u6 3 := by
            by_cases h11z : u5.regs 11 = 0
            · simpa [u6, h11z] using
                (ExecWithin.branch_pos (by simp [Cond.Holds, h50, h11z])
                  (ExecWithin.const (fits_zero w))).mono (by omega)
            · simpa [u6, h11z] using
                (ExecWithin.branch_neg (by simp [Cond.Holds, h50, h11z])
                  (ExecWithin.const (fits_zero w))).mono (by omega)
          let u7 := u6.set 7 (ptr + 1 + c.length)
          have he7 : ExecWithin (B := .standard) w (.op (.copy 7 10)) u6 u7 1 := by
            have h10' : u6.regs 10 = ptr + 1 + c.length := by dsimp [u6]; split_ifs <;> simp [h510]
            simpa [u7, h10'] using ExecWithin.copy (w := w) (x := u6) (d := 7) (s := 10)
          have hnext_ptr : ptr + 1 + c.length = 2 + (encodeClauses (ψ_pre ++ [c])).length := by
            rw [hptr, encodeClauses_append, encodeClauses_cons, encodeClauses_nil,
              List.append_nil, List.length_append, length_encodeClause]
            omega
          have hu7_6_le : u7.regs 6 ≤ 1 := by dsimp [u7, u6]; split_ifs <;> simp [h56, hu6le]
          have hu7_6_iff : u7.regs 6 = 1 ↔ (ψ_pre ++ [c]).eval (assignOf mask) = true := by
            simp only [CNF.eval_append, CNF.eval_cons, CNF.eval_nil, Bool.and_true,
              Bool.and_eq_true]
            dsimp [u7, u6]; split_ifs with h11z
            · have hcf : c.eval (assignOf mask) ≠ true := fun h => by have := h511_c.mpr h; omega
              simp [hcf]
            · have hct : c.eval (assignOf mask) = true := h511_c.mp (by omega)
              simp [h56, hu6iff, hct]
          obtain ⟨v_end, hv_end, hve0, hve1, hve2, hve3, hve4, hve5, hvemem, hve6le, hve6iff⟩ :=
            ih_cl (ψ_pre ++ [c]) (ptr + 1 + c.length) u7 (by simp [hφ]) hnext_ptr
              (by dsimp [u7, u6]; split_ifs <;> simp [h50])
              (by dsimp [u7, u6]; split_ifs <;> simp [h51])
              (by dsimp [u7, u6]; split_ifs <;> simp [h52])
              (by dsimp [u7, u6]; split_ifs <;> simp [h53])
              (by dsimp [u7, u6]; split_ifs <;> simp [h54])
              (by dsimp [u7, u6]; split_ifs <;> simp [h55])
              (by simp [u7]) (by dsimp [u7, u6]; split_ifs <;> simp [h5mem]) hu7_6_le hu7_6_iff
          have hcl_t : (4 + ((ptr + 1 + c.length - u4.regs 9) * (9 + 2) + 2 + (3 + 1))) +
              (14 * (encodeClauses ψ_rem).length + 2) + 2 ≤
                14 * (encodeClauses (c :: ψ_rem)).length + 2 := by
            simp only [u4, u3, u2, Data.set_regs,
              Function.update_of_ne (by decide : (9 : Fin 16) ≠ 11),
              Function.update_of_ne (by decide : (9 : Fin 16) ≠ 10), Function.update_self,
              encodeClauses_cons, List.length_append, length_encodeClause]
            omega
          refine ⟨v_end,
            (ExecWithin.loop_iter hcond_c
              (hu14.seq (hu5_ex.seq (he6.seq he7))) hv_end).mono hcl_t,
            hve0, hve1, hve2, hve3, hve4, hve5, hvemem, hve6le, hve6iff⟩
      obtain ⟨d3, hd3_ex, hd3_0, hd3_1, hd3_2, hd3_3, hd3_4, hd3_5, hd3_mem, hd3_6le, hd3_6iff⟩ :=
        hcl_eval [] φ 2 d2 (by simp) (by simp) (by simp [d2, d1, hd0]) (by simp [d2, d1, hd1])
          (by simp [d2, d1, hd2]) (by simp [d2, d1, hd3]) (by simp [d2, d1]) (by simp [d2, d1,
            mask])
          (by simp [d2]) (by simp [d2, d1, hdmem]) (by simp [d2, d1]) (by simp [d2, d1])
      let d4 := if d3.regs 6 = 1 then d3.set 4 1 else d3.set 15 0
      have hd34 : ExecWithin (B := .standard) w
          (.branch (.eq 6 1) (.op (.const 4 1)) (.op (.const 15 0))) d3 d4 3 := by
        by_cases h61 : d3.regs 6 = 1
        · simpa [d4, h61] using
            (ExecWithin.branch_pos (by simp [Cond.Holds, hd3_1, h61])
              (ExecWithin.const h1_f)).mono (by omega)
        · simpa [d4, h61] using
            (ExecWithin.branch_neg (by simp [Cond.Holds, hd3_1, h61])
              (ExecWithin.const (fits_zero w))).mono (by omega)
      let d5 := d4.set 5 (mask + 1)
      have hd45 : ExecWithin w (.op (.bin .add 5 5 1)) d4 d5 1 := by
        have h5' : d4.regs 5 = mask := by dsimp [d4]; split_ifs <;> simp [hd3_5]
        have h1' : d4.regs 1 = 1 := by dsimp [d4]; split_ifs <;> simp [hd3_1]
        simpa [d5, h5', h1'] using ExecWithin.bin (w := w) (x := d4) (f := .add) (d := 5) (i := 5)
          (j := 1) (by simpa [h5', h1'] using Fits.of_le hw_pow (by omega))
      have hbody_t : (1 + 1) + ((14 * (encodeClauses φ).length + 2) + (3 + 1)) ≤
          14 * L + 14 := by
        have : (encodeClauses φ).length ≤ L := by
          have := encFinCNF_length ⟨n, φ⟩; dsimp only [L] at this ⊢; omega
        omega
      refine ⟨d5, (((ExecWithin.const h1_f).seq (ExecWithin.const h2_f)).seq
          (hd3_ex.seq (hd34.seq hd45))).mono hbody_t,
        ⟨by dsimp [d5, d4]; split_ifs <;> simp [hd3_0],
          by dsimp [d5, d4]; split_ifs <;> simp [hd3_1],
          by dsimp [d5, d4]; split_ifs <;> simp [hd3_2],
          by dsimp [d5, d4]; split_ifs <;> simp [hd3_3],
          by dsimp [d5, d4]; split_ifs <;> simp [hd3_mem],
          by dsimp [d5, d4]; split_ifs <;> simp [hd3_4, hd4le], ?_⟩, by simp [d5]⟩
      dsimp [d5, d4]; split_ifs with h61
      · simp only [Data.set_regs, Function.update_of_ne (by decide : (4 : Fin 16) ≠ 5),
          Function.update_self, true_iff]
        exact ⟨mask, by omega, hd3_6iff.mp h61⟩
      · simp only [Data.set_regs, Function.update_of_ne (by decide : (4 : Fin 16) ≠ 5),
          Function.update_of_ne (by decide : (4 : Fin 16) ≠ 15), hd3_4, hd4iff]
        constructor
        · rintro ⟨m', hm', hs⟩; exact ⟨m', by omega, hs⟩
        · rintro ⟨m', hm', hs⟩
          by_cases hmeq : m' = mask
          · subst hmeq; exact absurd (hd3_6iff.mpr hs) h61
          · exact ⟨m', by omega, hs⟩)
    (x := s8) (by simp [s8]) (by simpa [s8] using hInvM0)
  obtain ⟨_, _, _, _, hymem, hy4le, hy4iff⟩ := hIy
  refine ⟨y, (hsetup.seq hy).mono (by
    simp only [s8, Data.set_regs, Function.update_self, Nat.sub_zero]
    have h16 : 14 * L + 14 + 2 = 14 * L + 16 := by omega
    rw [h16]; omega), hy4le, ?_, hymem⟩
  rw [hy4iff, mem_finSAT_iff]
  constructor
  · rintro ⟨m, _, hm⟩; exact ⟨assignOf m, hm⟩
  · rintro ⟨σ, hσ⟩
    let bits : List Bool := (List.range n).attach.map fun ⟨i, hi⟩ => σ ⟨i, List.mem_range.mp hi⟩
    refine ⟨bitStringMask bits, by simpa [bits] using bitStringMask_lt bits, ?_⟩
    have heq : assignOf (bitStringMask bits) = σ := by
      funext v
      have htb := bitStringMask_testBit bits v.val (by simp [bits, v.isLt])
      simp only [bits, List.getElem_map, List.getElem_attach, List.getElem_range, Fin.eta] at htb
      dsimp only [assignOf]; rw [htb]; cases σ v <;> rfl
    rwa [heq]


end CslibFrontier.Complexity.FineGrained
