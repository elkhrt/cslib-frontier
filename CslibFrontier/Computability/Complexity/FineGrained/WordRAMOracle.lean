/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.TableHelpers
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.CountingLoop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fine-Grained Reductions and Efficient Self-Reducibility on the Word RAM

This module defines fine-grained decision classes, adaptive oracle fine-grained reductions, and
efficient fine-grained self-reducibility on the standard deterministic Word RAM:

1. **Word-RAM decision classes (`WordRAMDecidableInTime`, `WordRAMDecidableInO`)**: uniform
   `rand`-free `Cslib.WordRAM` deciders over `Basis.standard` with `O(log(T + |enc|))` word width,
   directly embedding into `Cslib.WordRAM.UniformDecidableInTime`.
2. **Fine-grained reductions (`FineGrainedDeltaReducible`, `FineGrainedReducible`,
   `FineGrainedStarReducible`)**: adaptive oracle fine-grained reductions `(P, p) ≤_δ (Q, q)` and
   `(P, p) ≤ (Q, q)`.
3. **Fine-grained transfer lemma (`FineGrainedReducible.decidableInO_of_faster`)**: if
   `(P, p) ≤ (Q, q)` and `Q` is solvable in `O(q(n)^{1 - ε})`, then `P` is solvable in
   `O(p(n)^{1 - δ})` for some `δ > 0`, compiled via `compileOracle` and generation-stamped memory.
4. **Efficient self-reducibility (`EfficientlySelfReducible`, `EfficientlyComputable`)**:
   fine-grained self-reducibility with query bound `p(n') ≤ p(n)^α` and efficiently computable
   time bounds `p : ℕ → ℕ`.
5. **Synthetic upwards reduction (`syntheticUpwardsReduction`)**: padding `x ↦ x 0 1^{|x|^2}` gives
   `(P', s^{3/2}) ≤ (P, s^3)` for every binary language `P`.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

public section

namespace CslibFrontier.Complexity.FineGrained

open Cslib.WordRAM CslibFrontier.WordRAM

/-! ### Encodings, Oracles, and Word-RAM Decision Classes -/

/-- Characteristic oracle `O : List ℕ → Bool` of a problem `P` under an injective encoding `enc`. -/
noncomputable def oracleOf {α : Type*} (P : Set α) (enc : α ↪ List ℕ) : List ℕ → Bool :=
  fun q => @decide (∃ a ∈ P, enc a = q) (Classical.propDecidable _)

theorem oracleOf_enc {α : Type*} (P : Set α) (enc : α ↪ List ℕ) (a : α) :
    oracleOf P enc (enc a) = true ↔ a ∈ P := by
  simp only [oracleOf, decide_eq_true_eq]
  exact ⟨fun ⟨a', ha', heq⟩ => enc.injective heq ▸ ha', fun ha => ⟨a, ha, rfl⟩⟩

theorem oracleOf_eq_false_of_not_mem_range {α : Type*} (P : Set α) (enc : α ↪ List ℕ)
    {q : List ℕ} (hq : q ∉ Set.range enc) : oracleOf P enc q = false := by
  simp only [oracleOf, decide_eq_false_iff_not]
  rintro ⟨a, -, rfl⟩
  exact hq ⟨a, rfl⟩

/-- Size of an encoded query `q = enc b` (and `0` outside the range of `enc`). -/
noncomputable def querySize {β : Type*} (enc : β ↪ List ℕ) (size : β → ℕ) (q : List ℕ) : ℕ :=
  @dite ℕ (∃ b, enc b = q) (Classical.propDecidable _)
    (fun h => size (Classical.choose h)) (fun _ => 0)

theorem querySize_enc {β : Type*} (enc : β ↪ List ℕ) (size : β → ℕ) (b : β) :
    querySize enc size (enc b) = size b := by
  have h : ∃ b', enc b' = enc b := ⟨b, rfl⟩
  rw [querySize, dite_eq_left h]
  exact congrArg size (enc.injective (Classical.choose_spec h))

theorem querySize_of_not_mem_range {β : Type*} (enc : β ↪ List ℕ) (size : β → ℕ)
    {q : List ℕ} (hq : q ∉ Set.range enc) : querySize enc size q = 0 := by
  have h : ¬∃ b, enc b = q := fun ⟨b, hb⟩ => hq ⟨b, hb⟩
  rw [querySize, dite_eq_right h]

/-- Canonical bit-per-word encoding of binary strings `List Bool` into `List ℕ`. -/
def encBits : List Bool ↪ List ℕ where
  toFun z := z.map Bool.toNat
  inj' := by
    intro z₁ z₂ h
    have hlen : z₁.length = z₂.length := by
      simpa using congrArg List.length h
    refine List.ext_getElem hlen fun i hi₁ hi₂ => ?_
    have hi := congrArg (fun l => l[i]?) h
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂,
      Option.map_some, Option.some.injEq] at hi
    cases hb₁ : z₁[i] <;> cases hb₂ : z₂[i] <;> simp_all

theorem encBits_apply (z : List Bool) : encBits z = z.map Bool.toNat := by
  rfl

@[simp]
theorem encBits_length (z : List Bool) : (encBits z).length = z.length :=
  List.length_map _

/-- Every binary string `z` fits in any word width `w ≥ logWidth 1 z.length`. -/
theorem inputFits_encBits {w : ℕ} {z : List Bool} (hw : logWidth 1 z.length ≤ w) :
    InputFits w (encBits z) := by
  have h1 : 1 ≤ w := le_trans (by simp [logWidth]) hw
  refine ⟨?_, ?_⟩
  · rw [encBits_length]
    have hlt : z.length < 2 ^ (Nat.log 2 z.length + 1) :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two z.length
    have hlw : logWidth 1 z.length = Nat.log 2 z.length + 1 := by simp [logWidth]
    exact Fits.mono (by rw [← hlw] at hlt; exact hlt) hw
  · intro v hv
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hv
    have hlt : b.toNat ≤ 1 := by cases b <;> decide
    exact Fits.of_le (fits_one (by omega)) hlt

/-- A problem `P : Set α` encoded by `enc` is decidable on the standard Word RAM within time `T`
using `O(log(T + |enc|))` word width and a fixed `rand`-free structured program. -/
@[expose]
def WordRAMDecidableInTime {α : Type*} (P : Set α) (enc : α ↪ List ℕ) (T : α → ℕ) : Prop :=
  ∃ (r : ℕ) (c : Code .standard r) (out : Fin r) (k : ℕ),
    c.IsRandFree ∧ 0 < k ∧
    ∀ a w, logWidth k (T a + (enc a).length) ≤ w → InputFits w (enc a) →
      c.Answers out w (enc a) (a ∈ P) (T a)

/-- Direct bridge to `Cslib.WordRAM.UniformDecidableInTime`. -/
theorem WordRAMDecidableInTime.uniformDecidableInTime {α : Type*} {P : Set α}
    {enc : α ↪ List ℕ} {T : α → ℕ} (h : WordRAMDecidableInTime P enc T) :
    ∃ k : ℕ, 0 < k ∧
      UniformDecidableInTime .standard P (fun _ => enc) (fun a _ => T a + 1)
        (fun a w => logWidth k (T a + (enc a).length) ≤ w) := by
  obtain ⟨_, c, out, k, _, hk, hdec⟩ := h
  exact ⟨k, hk, UniformDecidableInTime.of_code c out
    (inputAdmissible_of_widthIndependent enc _) hdec⟩

/-- `P` is decidable on the Word RAM in time `O(f)` (up to a positive constant factor and additive
constant to accommodate zero-valued bounds such as `p(0) = 0`). -/
@[expose] def WordRAMDecidableInO {α : Type*} (P : Set α) (enc : α ↪ List ℕ) (f : α → ℝ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ WordRAMDecidableInTime P enc (fun a => C * ⌈max 0 (f a)⌉₊ + C)

theorem WordRAMDecidableInTime.mono {α : Type*} {P : Set α} {enc : α ↪ List ℕ}
    {T₁ T₂ : α → ℕ} (h : WordRAMDecidableInTime P enc T₁) (hle : ∀ a, T₁ a ≤ T₂ a) :
    WordRAMDecidableInTime P enc T₂ := by
  obtain ⟨r, c, out, k, hrf, hk, hdec⟩ := h
  refine ⟨r, c, out, k, hrf, hk, fun a w hw hi => ?_⟩
  have hw' : logWidth k (T₁ a + (enc a).length) ≤ w :=
    (logWidth_mono le_rfl (Nat.add_le_add_right (hle a) _)).trans hw
  obtain ⟨y, hy, hy1, hyiff⟩ := hdec a w hw' hi
  exact ⟨y, hy.mono (hle a), hy1, hyiff⟩

theorem WordRAMDecidableInO.mono {α : Type*} {P : Set α} {enc : α ↪ List ℕ} {f g : α → ℝ}
    (h : WordRAMDecidableInO P enc f)
    (hfg : ∃ K : ℕ, 0 < K ∧ ∀ a, max 0 (f a) ≤ (K : ℝ) * max 0 (g a) + (K : ℝ)) :
    WordRAMDecidableInO P enc g := by
  obtain ⟨C, hC, hdec⟩ := h
  obtain ⟨K, hK, hle⟩ := hfg
  refine ⟨C * (K + 1) + C, by positivity, hdec.mono fun a => ?_⟩
  have hceil : ⌈max 0 (f a)⌉₊ ≤ K * ⌈max 0 (g a)⌉₊ + K := by
    refine Nat.ceil_le.mpr ?_
    push_cast
    exact (hle a).trans (by
      have hg := Nat.le_ceil (max 0 (g a))
      nlinarith)
  have : C * ⌈max 0 (f a)⌉₊ + C ≤ C * (K * ⌈max 0 (g a)⌉₊ + K) + C :=
    Nat.add_le_add_right (Nat.mul_le_mul_left C hceil) C
  nlinarith

/-! ### Fine-Grained Reductions -/

/-- Adaptive `δ`-fine-grained oracle reduction: `(P, p)` `δ`-fine-grained reduces to
`(Q, q)`, written `(P, p(n)) ≤_δ (Q, q(n))`. Every oracle query produced by the reduction is a
valid encoded instance of `Q`. -/
@[expose] def FineGrainedDeltaReducible {α β : Type*}
    (P : Set α) (encP : α ↪ List ℕ) (sizeP : α → ℕ) (p : ℕ → ℝ)
    (Q : Set β) (encQ : β ↪ List ℕ) (sizeQ : β → ℕ) (q : ℕ → ℝ)
    (δ : ℝ → ℝ) : Prop :=
  Monotone p ∧ Monotone q ∧ (∀ n, 0 ≤ p n) ∧ (∀ n, 0 ≤ q n) ∧
  (∀ ε, 0 < ε → 0 < δ ε) ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ (r : ℕ) (c : OracleCode .standard r) (out : Fin r) (C k : ℕ),
      0 < C ∧ 0 < k ∧
      ∀ a w, logWidth k (⌈p (sizeP a)⌉₊ + (encP a).length) ≤ w → InputFits w (encP a) →
        ∃ y t qs,
          OracleExec w (oracleOf Q encQ) c (.init (encP a)) y t qs ∧
          y.regs out ≤ 1 ∧ (y.regs out = 1 ↔ a ∈ P) ∧
          (∀ qi ∈ qs, qi ∈ Set.range encQ) ∧
          (t : ℝ) ≤ (C : ℝ) * (p (sizeP a)) ^ (1 - δ ε) + (C : ℝ) ∧
          ((qs.map fun qi => (q (querySize encQ sizeQ qi)) ^ (1 - ε)).sum : ℝ) ≤
            (C : ℝ) * (p (sizeP a)) ^ (1 - δ ε) + (C : ℝ)

/-- Adaptive fine-grained oracle reduction: `(P, p)` fine-grained reduces to `(Q, q)`, written
`(P, p(n)) ≤ (Q, q(n))`, if `(P, p) ≤_δ (Q, q)` for some `δ : ℝ → ℝ`. -/
@[expose] def FineGrainedReducible {α β : Type*}
    (P : Set α) (encP : α ↪ List ℕ) (sizeP : α → ℕ) (p : ℕ → ℝ)
    (Q : Set β) (encQ : β ↪ List ℕ) (sizeQ : β → ℕ) (q : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ → ℝ, FineGrainedDeltaReducible P encP sizeP p Q encQ sizeQ q δ

/-- `O^*`-variant of fine-grained reduction (suppressing polynomial factors
`((encP a).length + 1)^e`), used for parameterized problems such as SAT. -/
@[expose] def FineGrainedStarReducible {α β : Type*}
    (P : Set α) (encP : α ↪ List ℕ) (sizeP : α → ℕ) (p : ℕ → ℝ)
    (Q : Set β) (encQ : β ↪ List ℕ) (sizeQ : β → ℕ) (q : ℕ → ℝ) : Prop :=
  ∃ δ : ℝ → ℝ,
    Monotone p ∧ Monotone q ∧ (∀ n, 0 ≤ p n) ∧ (∀ n, 0 ≤ q n) ∧
    (∀ ε, 0 < ε → 0 < δ ε) ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ (r : ℕ) (c : OracleCode .standard r) (out : Fin r) (C e k : ℕ),
        0 < C ∧ 0 < k ∧
        ∀ a w, logWidth k (⌈p (sizeP a)⌉₊ + (encP a).length) ≤ w → InputFits w (encP a) →
          ∃ y t qs,
            OracleExec w (oracleOf Q encQ) c (.init (encP a)) y t qs ∧
            y.regs out ≤ 1 ∧ (y.regs out = 1 ↔ a ∈ P) ∧
            (∀ qi ∈ qs, qi ∈ Set.range encQ) ∧
            (t : ℝ) ≤
              (C : ℝ) * (((encP a).length + 1 : ℕ) : ℝ) ^ e * (p (sizeP a)) ^ (1 - δ ε) +
                (C : ℝ) * (((encP a).length + 1 : ℕ) : ℝ) ^ e ∧
            ((qs.map fun qi => (q (querySize encQ sizeQ qi)) ^ (1 - ε)).sum : ℝ) ≤
              (C : ℝ) * (((encP a).length + 1 : ℕ) : ℝ) ^ e * (p (sizeP a)) ^ (1 - δ ε) +
                (C : ℝ) * (((encP a).length + 1 : ℕ) : ℝ) ^ e

/-- Every fine-grained reduction is in particular an `O^*` fine-grained reduction (`e = 0`). -/
theorem FineGrainedReducible.star {α β : Type*}
    {P : Set α} {encP : α ↪ List ℕ} {sizeP : α → ℕ} {p : ℕ → ℝ}
    {Q : Set β} {encQ : β ↪ List ℕ} {sizeQ : β → ℕ} {q : ℕ → ℝ}
    (h : FineGrainedReducible P encP sizeP p Q encQ sizeQ q) :
    FineGrainedStarReducible P encP sizeP p Q encQ sizeQ q := by
  obtain ⟨δ, hp, hq, hp0, hq0, hδ, hred⟩ := h
  refine ⟨δ, hp, hq, hp0, hq0, hδ, fun ε hε => ?_⟩
  obtain ⟨r, c, out, C, k, hC, hk, hrun⟩ := hred ε hε
  refine ⟨r, c, out, C, 0, k, hC, hk, fun a w hw hi => ?_⟩
  obtain ⟨y, t, qs, hex, hy1, hyiff, hvalid, ht, hsum⟩ := hrun a w hw hi
  refine ⟨y, t, qs, hex, hy1, hyiff, hvalid, ?_, ?_⟩ <;> simpa using ‹_›

/-! ### Efficient Self-Reducibility -/

/-- Efficient fine-grained self-reducibility: `P` is *efficiently
self-reducible for `p`* if for every `0 < α < 1` there is a fine-grained self-reduction
`(P, p) ≤ (P, p)` whose oracle queries all satisfy `p(n') ≤ p(n)^α`. -/
@[expose] def EfficientlySelfReducible {α : Type*} (P : Set α) (enc : α ↪ List ℕ)
    (size : α → ℕ) (p : ℕ → ℝ) : Prop :=
  Monotone p ∧ (∀ n, 0 ≤ p n) ∧
  ∀ a_exp : ℝ, 0 < a_exp → a_exp < 1 →
    ∃ δ : ℝ → ℝ, (∀ ε, 0 < ε → 0 < δ ε) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (r : ℕ) (c : OracleCode .standard r) (out : Fin r) (C k : ℕ),
          0 < C ∧ 0 < k ∧
          ∀ a w, logWidth k (⌈p (size a)⌉₊ + (enc a).length) ≤ w → InputFits w (enc a) →
            ∃ y t qs,
              OracleExec w (oracleOf P enc) c (.init (enc a)) y t qs ∧
              y.regs out ≤ 1 ∧ (y.regs out = 1 ↔ a ∈ P) ∧
              (∀ qi ∈ qs, qi ∈ Set.range enc) ∧
              (t : ℝ) ≤ (C : ℝ) * (p (size a)) ^ (1 - δ ε) + (C : ℝ) ∧
              ((qs.map fun qi => (p (querySize enc size qi)) ^ (1 - ε)).sum : ℝ) ≤
                (C : ℝ) * (p (size a)) ^ (1 - δ ε) + (C : ℝ) ∧
              (∀ qi ∈ qs, ∀ a', enc a' = qi → p (size a') ≤ (p (size a)) ^ a_exp)

/-- `p : ℕ → ℕ` is *efficiently computable* on the Word RAM if a fixed `rand`-free program maps `s`
(in reg `0`) to `p s` (in reg `1`) within `O(p(s)^{1 - η} + 1)` steps for some `0 < η < 1`,
leaving memory unchanged. -/
@[expose] def EfficientlyComputable (p : ℕ → ℕ) : Prop :=
  ∃ (r : ℕ) (c : Code .standard (r + 2)) (C : ℕ) (η : ℝ),
    c.IsRandFree ∧ 0 < C ∧ 0 < η ∧ η < 1 ∧
    ∀ s W (x : Data (r + 2)),
      Fits W (s + p s + 1) → x.regs 0 = s →
      ∃ y : Data (r + 2),
        ExecWithin W c x y (C * ⌈((p s : ℝ)) ^ (1 - η)⌉₊ + C) ∧
        y.regs 1 = p s ∧ y.mem = x.mem

/-- `p(s) = s^2` is efficiently computable (`1` multiplication instruction). -/
theorem efficientlyComputable_sq : EfficientlyComputable (fun s => s ^ 2) := by
  let r0 : Fin 2 := 0
  let r1 : Fin 2 := 1
  refine ⟨0, ram[r1 ← r0 * r0], 1, 1 / 2, by simp [Code.IsRandFree],
    Nat.one_pos, by norm_num, by norm_num, fun s W x hfits hx0 => ?_⟩
  have hmul : Fits W (x.regs 0 * x.regs 0) := by
    rw [hx0]; exact Fits.of_le hfits (by nlinarith)
  refine ⟨x.set 1 (x.regs 0 * x.regs 0), (ExecWithin.bin hmul).mono (by omega), ?_, rfl⟩
  simp [hx0, sq]

/-! ### Stamped Pure-Solver Wrapper and Basic Fine-Grained Transfer Lemma -/

private def wrapCopyReg {r_Q : ℕ} (j : Fin 9) : Fin ((r_Q + 21) + 3) :=
  ⟨9 + j.val, by omega⟩

private def wrapStampReg {r_Q : ℕ} (j : Fin (r_Q + 6)) : Fin ((r_Q + 21) + 3) :=
  ⟨18 + j.val, by omega⟩

/-- Wrap a pure `WordRAM.Code .standard r_Q` solver `c_Q` into an oracle-compilation subroutine
(`sub : Code .standard ((r_Q + 21) + 3)`) operating in stamped bank `[2*H, 4*H)`.
Arguments: `0=qBase`, `1=qLen`; persistent: `3=H`, `4=w_log`, `5=gen`; output: `2=ans`. -/
def wrapPureSolverCode {r_Q : ℕ} (c_Q : Code .standard r_Q) (out_Q : Fin r_Q) :
    Code .standard ((r_Q + 21) + 3) :=
  let r0 : Fin ((r_Q + 21) + 3) := ⟨0, by omega⟩
  let r1 : Fin ((r_Q + 21) + 3) := ⟨1, by omega⟩
  let r2 : Fin ((r_Q + 21) + 3) := ⟨2, by omega⟩
  let r3 : Fin ((r_Q + 21) + 3) := ⟨3, by omega⟩
  let r4 : Fin ((r_Q + 21) + 3) := ⟨4, by omega⟩
  let r5 : Fin ((r_Q + 21) + 3) := ⟨5, by omega⟩
  let r6 : Fin ((r_Q + 21) + 3) := ⟨6, by omega⟩
  let r7 : Fin ((r_Q + 21) + 3) := ⟨7, by omega⟩
  .seq
    (ram[
      r7 ← #1;
      r5 ← r5 + r7;
      r6 ← r3 + r3
    ])
    (.seq (.op (.copy (wrapCopyReg 0) r0))
      (.seq (.op (.copy (wrapCopyReg 1) r1))
        (.seq (.op (.copy (wrapCopyReg 2) r6))
          (.seq (.op (.copy (wrapCopyReg 3) r5))
            (.seq (copyInitToStampedCode.rename wrapCopyReg)
              (.seq (.op (.copy (wrapStampReg stampBaseReg) r6))
                (.seq (.op (.copy (wrapStampReg stampGenReg) r5))
                  (.seq (.op (.copy (wrapStampReg stampWidthReg) r4))
                    (.seq ((zeroPrefixRegs (stampCode c_Q)).rename wrapStampReg)
                      (.op (.copy r2 (wrapStampReg (stampVirtReg out_Q)))))))))))))

theorem isRandFree_wrapPureSolverCode {r_Q : ℕ} {c_Q : Code .standard r_Q} (out_Q : Fin r_Q)
    (hc : c_Q.IsRandFree) : (wrapPureSolverCode c_Q out_Q).IsRandFree := by
  refine ⟨⟨trivial, trivial, trivial⟩, trivial, trivial, trivial, trivial,
    isRandFree_rename isRandFree_copyInitToStampedCode, trivial, trivial, trivial,
    isRandFree_rename (isRandFree_zeroPrefixRegs (isRandFree_stampCode hc)), trivial⟩

private theorem wrapCopyReg_injective {r_Q : ℕ} :
    Function.Injective (wrapCopyReg (r_Q := r_Q)) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [wrapCopyReg] at hv
  exact Fin.ext (by omega)

private theorem wrapStampReg_injective {r_Q : ℕ} :
    Function.Injective (wrapStampReg (r_Q := r_Q)) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [wrapStampReg] at hv
  exact Fin.ext (by omega)

/-- Execution specification of `wrapPureSolverCode`. -/
theorem wrapPureSolverCode_exec {r_Q W w_log H gen₀ t_Q : ℕ}
    {c_Q : Code .standard r_Q} {out_Q : Fin r_Q} {q : List ℕ} {y_Q : Data r_Q}
    {x : Data ((r_Q + 21) + 3)}
    (hrf : c_Q.IsRandFree) (hH : 2 ^ w_log ≤ H) (h4H : 4 * H ≤ 2 ^ W)
    (hgenW : Fits W (gen₀ + 1)) (hq_fits : InputFits w_log q)
    (hrun : Exec w_log c_Q (.init q) y_Q t_Q)
    (h0 : x.regs ⟨0, by omega⟩ + q.length < H)
    (h1 : x.regs ⟨1, by omega⟩ = q.length)
    (hq_eq : q = (List.range q.length).map fun i => x.mem (x.regs ⟨0, by omega⟩ + i))
    (h3 : x.regs ⟨3, by omega⟩ = H) (h4 : x.regs ⟨4, by omega⟩ = w_log)
    (h5 : x.regs ⟨5, by omega⟩ = gen₀)
    (hst : StampLe (2 * H) H gen₀ x.mem) :
    ∃ z : Data ((r_Q + 21) + 3),
      ExecWithin W (wrapPureSolverCode c_Q out_Q) x z (11 * q.length + 7 * t_Q + r_Q + 20) ∧
      z.regs ⟨2, by omega⟩ = y_Q.regs out_Q ∧
      z.regs ⟨3, by omega⟩ = H ∧
      z.regs ⟨4, by omega⟩ = w_log ∧
      z.regs ⟨5, by omega⟩ = gen₀ + 1 ∧
      StampLe (2 * H) H (gen₀ + 1) z.mem ∧
      ∀ a < 2 * H, z.mem a = x.mem a := by
  have h1_fits : Fits W 1 := by
    have : 1 ≤ 2 ^ w_log := Nat.one_le_two_pow
    exact show 1 < 2 ^ W by omega
  have h2H_fits : Fits W (2 * H) := by
    have : 1 ≤ 2 ^ w_log := Nat.one_le_two_pow
    exact show 2 * H < 2 ^ W by omega
  -- Step 1: r7 ← 1; r5 ← gen₀ + 1; r6 ← 2 * H
  let x1 := x.set ⟨7, by omega⟩ 1
  let x2 := x1.set ⟨5, by omega⟩ (gen₀ + 1)
  let x3 := x2.set ⟨6, by omega⟩ (2 * H)
  have he123 : ExecWithin W
      (.seq (.op (.const ⟨7, by omega⟩ 1))
        (.seq (.op (.bin .add ⟨5, by omega⟩ ⟨5, by omega⟩ ⟨7, by omega⟩))
          (.op (.bin .add ⟨6, by omega⟩ ⟨3, by omega⟩ ⟨3, by omega⟩)))) x x3 3 := by
    have s1 : ExecWithin W (.op (Op.const (B := .standard) ⟨7, by omega⟩ 1)) x x1 1 :=
      ExecWithin.const h1_fits
    have s2 : ExecWithin W (.op (.bin .add ⟨5, by omega⟩ ⟨5, by omega⟩ ⟨7, by omega⟩)) x1 x2 1 := by
      have hf : Fits W (x1.regs ⟨5, by omega⟩ + x1.regs ⟨7, by omega⟩) := by
        simpa [x1, h5] using hgenW
      simpa [x2, x1, h5] using ExecWithin.bin (w := W) (x := x1) (f := .add)
        (d := ⟨5, by omega⟩) (i := ⟨5, by omega⟩) (j := ⟨7, by omega⟩) hf
    have s3 : ExecWithin W (.op (.bin .add ⟨6, by omega⟩ ⟨3, by omega⟩ ⟨3, by omega⟩)) x2 x3 1 := by
      have hf : Fits W (x2.regs ⟨3, by omega⟩ + x2.regs ⟨3, by omega⟩) := by
        have : H + H = 2 * H := by omega
        simpa [x2, x1, h3, this] using h2H_fits
      have : H + H = 2 * H := by omega
      simpa [x3, x2, x1, h3, this] using ExecWithin.bin (w := W) (x := x2) (f := .add)
        (d := ⟨6, by omega⟩) (i := ⟨3, by omega⟩) (j := ⟨3, by omega⟩) hf
    exact s1.seq (s2.seq s3)
  -- Step 2: copy args to wrapCopyReg and run copyInitToStampedCode
  let x4 := x3.set (wrapCopyReg 0) (x3.regs ⟨0, by omega⟩)
  let x5 := x4.set (wrapCopyReg 1) (x4.regs ⟨1, by omega⟩)
  let x6 := x5.set (wrapCopyReg 2) (x5.regs ⟨6, by omega⟩)
  let x7 := x6.set (wrapCopyReg 3) (x6.regs ⟨5, by omega⟩)
  have hx7_r : ∀ j : Fin ((r_Q + 21) + 3), j.val < 9 → x7.regs j = x3.regs j := by
    intro j hj
    have hne : ∀ k : Fin 9, j ≠ wrapCopyReg k := fun k h => by
      have := congrArg Fin.val h; simp [wrapCopyReg] at this; omega
    simp [x7, x6, x5, x4, hne 0, hne 1, hne 2, hne 3]
  have hx7_c0 : (x7.comap wrapCopyReg).regs 0 = x.regs ⟨0, by omega⟩ := by
    simp [x7, x6, x5, x4, x3, x2, x1, wrapCopyReg, Fin.ext_iff]
  have hx7_c1 : (x7.comap wrapCopyReg).regs 1 = q.length := by
    rw [← h1]
    simp [x7, x6, x5, x4, x3, x2, x1, wrapCopyReg, Fin.ext_iff]
  have hx7_c2 : (x7.comap wrapCopyReg).regs 2 = 2 * H := by
    simp [x7, x6, x5, x4, x3, wrapCopyReg, Fin.ext_iff]
  have hx7_c3 : (x7.comap wrapCopyReg).regs 3 = gen₀ + 1 := by
    simp [x7, x6, x5, x4, x3, x2, wrapCopyReg, Fin.ext_iff]
  have hq_len_H : (x7.comap wrapCopyReg).regs 1 < H := by
    rw [hx7_c1]; exact lt_of_le_of_lt (Nat.le_add_left _ _) h0
  have hq_src : (x7.comap wrapCopyReg).regs 0 + (x7.comap wrapCopyReg).regs 1 ≤ 2 * H := by
    rw [hx7_c0, hx7_c1]; omega
  obtain ⟨c_out, hc_out, hc_rep, hc_st, hc_fr⟩ :=
    copyInitToStampedCode_exec (W := W) (base := 2 * H) (H := H) (gen₀ := gen₀) (gen := gen₀ + 1)
      (x := x7.comap wrapCopyReg) (by omega) hq_len_H hq_src (by omega) hx7_c2 hx7_c3 hst
  have hq_eq' : (List.range ((x7.comap wrapCopyReg).regs 1)).map
      (fun i => (x7.comap wrapCopyReg).mem ((x7.comap wrapCopyReg).regs 0 + i)) = q := by
    simpa only [Data.comap_mem, hx7_c0, hx7_c1, x7, x6, x5, x4, x3, x2, x1, Data.set_mem] using
      hq_eq.symm
  rw [hq_eq'] at hc_rep
  obtain ⟨x8, hx8, hx8_eq, hx8_fr⟩ :=
    ExecWithin.rename_post (wrapCopyReg_injective (r_Q := r_Q)) ⟨c_out, hc_out, rfl⟩
  have hx8_mem : x8.mem = c_out.mem := congrArg Data.mem hx8_eq.symm
  have hx8_r : ∀ j : Fin ((r_Q + 21) + 3), j.val < 9 → x8.regs j = x3.regs j := by
    intro j hj
    have hne : ∀ k : Fin 9, wrapCopyReg (r_Q := r_Q) k ≠ j := fun k h => by
      have := congrArg Fin.val h; simp [wrapCopyReg] at this; omega
    exact (hx8_fr j hne).trans (hx7_r j hj)
  -- Step 3: set stampBaseReg, stampGenReg, stampWidthReg and run zeroPrefixRegs (stampCode c_Q)
  let x9 := x8.set (wrapStampReg stampBaseReg) (x8.regs ⟨6, by omega⟩)
  let x10 := x9.set (wrapStampReg stampGenReg) (x9.regs ⟨5, by omega⟩)
  let x11 := x10.set (wrapStampReg stampWidthReg) (x10.regs ⟨4, by omega⟩)
  let x11_s : Data (r_Q + 6) :=
    ⟨fun k => if k.val < r_Q then 0 else (x11.comap wrapStampReg).regs k, x11.mem⟩
  have hx11_s_B : x11_s.regs stampBaseReg = 2 * H := by
    have hlt : ¬(stampBaseReg (r := r_Q)).val < r_Q := by simp
    simp only [x11_s, hlt, ↓reduceIte, Data.comap_regs]
    have h1' : (wrapStampReg (r_Q := r_Q) stampBaseReg) ≠ wrapStampReg stampGenReg :=
      wrapStampReg_injective.ne stampBaseReg_ne_stampGenReg
    have h2' : (wrapStampReg (r_Q := r_Q) stampBaseReg) ≠ wrapStampReg stampWidthReg :=
      wrapStampReg_injective.ne stampBaseReg_ne_stampWidthReg
    simp [x11, x10, x9, h1', h2', hx8_r ⟨6, by omega⟩ (by simp), x3]
  have hx11_s_G : x11_s.regs stampGenReg = gen₀ + 1 := by
    have hlt : ¬(stampGenReg (r := r_Q)).val < r_Q := by simp
    simp only [x11_s, hlt, ↓reduceIte, Data.comap_regs]
    have h2' : (wrapStampReg (r_Q := r_Q) stampGenReg) ≠ wrapStampReg stampWidthReg :=
      wrapStampReg_injective.ne stampGenReg_ne_stampWidthReg
    have hne6 : (⟨5, by omega⟩ : Fin ((r_Q + 21) + 3)) ≠ wrapStampReg stampBaseReg :=
      Fin.ne_of_val_ne (by simp [wrapStampReg]; omega)
    simp [x11, x10, x9, h2', hne6, hx8_r ⟨5, by omega⟩ (by simp), x3, x2]
  have hx11_s_W : x11_s.regs stampWidthReg = w_log := by
    have hlt : ¬(stampWidthReg (r := r_Q)).val < r_Q := by simp
    simp only [x11_s, hlt, ↓reduceIte, Data.comap_regs]
    have hne4b : (⟨4, by omega⟩ : Fin ((r_Q + 21) + 3)) ≠ wrapStampReg stampBaseReg :=
      Fin.ne_of_val_ne (by simp [wrapStampReg]; omega)
    have hne4g : (⟨4, by omega⟩ : Fin ((r_Q + 21) + 3)) ≠ wrapStampReg stampGenReg :=
      Fin.ne_of_val_ne (by simp [wrapStampReg]; omega)
    simp [x11, x10, x9, hne4b, hne4g, hx8_r ⟨4, by omega⟩ (by simp), x3, x2, x1, h4]
  have hx11_s_virt : x11_s.regs ∘ stampVirtReg = (Data.init q (r := r_Q)).regs := by
    funext i
    simp [x11_s, Data.init_regs]
  have hx11_s_rep : MemRepresents (2 * H) H (gen₀ + 1) x11_s.mem (Data.init q (r := r_Q)).mem := by
    intro a ha
    have : x11_s.mem = c_out.mem := by simp [x11_s, x11, x10, x9, hx8_mem]
    rw [this]; exact hc_rep a ha
  have hx11_s_st : StampLe (2 * H) H (gen₀ + 1) x11_s.mem := by
    have : x11_s.mem = c_out.mem := by simp [x11_s, x11, x10, x9, hx8_mem]
    rw [this]; exact hc_st
  obtain ⟨y_s, hy_s, _, _, _, hy_s_virt, _, hy_s_st, hy_s_fr⟩ :=
    stampCode_exec (W := W) (base := 2 * H) (H := H) (gen := gen₀ + 1)
      hrf (Data.Bounded.init hq_fits) hH (by omega) hrun
      hx11_s_B hx11_s_G hx11_s_W hx11_s_virt hx11_s_rep hx11_s_st
  have hz_zero := zeroPrefixRegs_exec (r := r_Q) (m := 6) hy_s
  obtain ⟨x12, hx12, hx12_eq, hx12_fr⟩ :=
    ExecWithin.rename_post (wrapStampReg_injective (r_Q := r_Q)) ⟨y_s, hz_zero, rfl⟩
  have hx12_r : ∀ j : Fin ((r_Q + 21) + 3), j.val < 9 → x12.regs j = x3.regs j := by
    intro j hj
    have hneS : ∀ k : Fin (r_Q + 6), wrapStampReg (r_Q := r_Q) k ≠ j := fun k h => by
      have := congrArg Fin.val h; simp [wrapStampReg] at this; omega
    have h11 : x11.regs j = x8.regs j := by
      simp [x11, x10, x9, (hneS stampBaseReg).symm, (hneS stampGenReg).symm,
        (hneS stampWidthReg).symm]
    exact (hx12_fr j hneS).trans (h11.trans (hx8_r j hj))
  let z := x12.set ⟨2, by omega⟩ (x12.regs (wrapStampReg (stampVirtReg out_Q)))
  have hexec : ExecWithin W (wrapPureSolverCode c_Q out_Q) x z
      (11 * q.length + 7 * t_Q + r_Q + 20) :=
    (he123.seq (ExecWithin.copy.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
      (ExecWithin.copy.seq (hx8.seq (ExecWithin.copy.seq (ExecWithin.copy.seq
        (ExecWithin.copy.seq (hx12.seq ExecWithin.copy)))))))))).mono
      (by simp only [hx7_c1]; omega)
  refine ⟨z, hexec, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hvo := congrFun (congrArg Data.regs hx12_eq.symm) (stampVirtReg out_Q)
    have hyo := congrFun hy_s_virt out_Q
    simp only [z, Data.set_regs, Function.update_self]
    exact (show x12.regs (wrapStampReg (stampVirtReg out_Q)) = y_s.regs (stampVirtReg out_Q) from
      hvo).trans hyo
  · simp [z, hx12_r ⟨3, by omega⟩ (by simp), x3, x2, x1, h3]
  · simp [z, hx12_r ⟨4, by omega⟩ (by simp), x3, x2, x1, h4]
  · simp [z, hx12_r ⟨5, by omega⟩ (by simp), x3, x2]
  · have hm : z.mem = y_s.mem := congrArg Data.mem hx12_eq.symm
    rw [hm]; exact hy_s_st
  · intro a ha
    have hm : z.mem = y_s.mem := congrArg Data.mem hx12_eq.symm
    rw [hm, hy_s_fr a (by omega), show x11_s.mem a =
      c_out.mem a by simp [x11_s, x11, x10, x9, hx8_mem]]
    exact hc_fr a (by omega)

/-- **Basic Fine-Grained Transfer Lemma**:
if `(P, p) ≤ (Q, q)` and `Q` is solvable in time `O(q(n)^{1 - ε})` for some `ε > 0`, then `P` is
solvable in time `O(p(n)^{1 - δ})` for some `δ > 0`.
(Requires the standard Word-RAM encoding condition that input words of `P` fit in
`O(log(p(sizeP a) +
  |encP a|))` bits, which holds automatically for binary, graph, and CNF inputs.) -/
theorem FineGrainedReducible.decidableInO_of_faster {α β : Type*}
    {P : Set α} {encP : α ↪ List ℕ} {sizeP : α → ℕ} {p : ℕ → ℝ}
    {Q : Set β} {encQ : β ↪ List ℕ} {sizeQ : β → ℕ} {q : ℕ → ℝ} {ε : ℝ}
    (hred : FineGrainedReducible P encP sizeP p Q encQ sizeQ q)
    (hp_int : ∀ n, p n = 0 ∨ 1 ≤ p n) (hq_int : ∀ n, q n = 0 ∨ 1 ≤ q n)
    (henc : ∃ k_e : ℕ, 0 < k_e ∧
      ∀ a, InputFits (logWidth k_e (⌈p (sizeP a)⌉₊ + (encP a).length)) (encP a))
    (hε : 0 < ε)
    (hQ : WordRAMDecidableInO Q encQ (fun b => (q (sizeQ b)) ^ (1 - ε))) :
    ∃ δ : ℝ, 0 < δ ∧ WordRAMDecidableInO P encP (fun a => (p (sizeP a)) ^ (1 - δ)) := by
  -- Clamp ε to ε' = min ε (1/2) ∈ (0, 1/2] so 1 - ε' ≥ 1/2
  set ε' := min ε (1 / 2 : ℝ)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have hε'_half : ε' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨δ_fn, hp_mono, hq_mono, hp0, hq0, hδ_pos, hfg⟩ := hred
  obtain ⟨r_A, c_A, out_A, C_A, k_A, hC_A, hk_A, hA⟩ := hfg ε' hε'
  set d := min (δ_fn ε') (1 / 2 : ℝ)
  have hd_pos : 0 < d := lt_min (hδ_pos ε' hε') (by norm_num)
  have hd_le : d ≤ δ_fn ε' := min_le_left _ _
  have hd_half : d ≤ 1 / 2 := min_le_right _ _
  obtain ⟨C_Q, hC_Q, r_Q, c_Q, out_Q, k_Q, hrf_Q, hk_Q, hQ_dec⟩ := hQ
  obtain ⟨k_e, hk_e, henc_fits⟩ := henc
  -- Build combined Word-RAM program: compute H = 2^(W-3), set w_log = W-3, run compileOracle
  let r_sub := r_Q + 21
  let r_tot := (r_A + 1) + (r_sub + 3)
  let sub := wrapPureSolverCode c_Q out_Q
  let rH : Fin r_tot := subReg ⟨3, by omega⟩
  let rWlog : Fin r_tot := subReg ⟨4, by omega⟩
  let rGen : Fin r_tot := subReg ⟨5, by omega⟩
  let rTmp : Fin r_tot := subReg ⟨6, by omega⟩
  let rCW : Fin r_tot := callerWidthReg
  let mainCode : Code .standard r_tot :=
    .seq
      (ram[
        rWlog ← width%;
        rTmp ← #3;
        rWlog ← rWlog - rTmp;
        rCW ← rWlog;
        rTmp ← #1;
        rH ← rTmp <<< rWlog;
        rGen ← #0
      ])
      (compileOracle c_A sub)
  have hmain_rf : mainCode.IsRandFree :=
    ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩,
      isRandFree_compileOracle c_A (isRandFree_wrapPureSolverCode out_Q hrf_Q)⟩
  -- Time constant
  let C_tot : ℕ := (30 * C_Q + r_Q + 50) * (2 * C_A + 2) + 20
  have hC_tot_pos : 0 < C_tot := by positivity
  -- Width multiplier
  let K_tot : ℕ := 2 * (k_A + k_Q + k_e + C_A + C_Q + r_Q + 10)
  have hK_tot_pos : 0 < K_tot := by positivity
  refine ⟨d, hd_pos, C_tot, hC_tot_pos, r_tot, mainCode, callerReg out_A, K_tot, hmain_rf,
    hK_tot_pos, fun a W hW _ => ?_⟩
  set P_val : ℝ := (p (sizeP a)) ^ (1 - d)
  set T_tot : ℕ := C_tot * ⌈max 0 P_val⌉₊ + C_tot
  have hP_nonneg : 0 ≤ P_val := Real.rpow_nonneg (hp0 _) _
  have hmaxP : max 0 P_val = P_val := max_eq_right hP_nonneg
  have hP_le : (p (sizeP a)) ^ (1 - δ_fn ε') ≤ P_val + 1 := by
    rcases hp_int (sizeP a) with hpz | hp1
    · rw [hpz]
      by_cases h0 : (1 : ℝ) - δ_fn ε' = 0
      · rw [h0, Real.rpow_zero]; linarith
      · rw [Real.zero_rpow h0]; linarith
    · have hle : (1 : ℝ) - δ_fn ε' ≤ 1 - d := by linarith
      exact (Real.rpow_le_rpow_of_exponent_le hp1 hle).trans (by linarith)
  -- Relate Nat.log 2 (⌈p(s)⌉₊ + L) to Nat.log 2 (T_tot + L)
  have hp_sq_le : ⌈p (sizeP a)⌉₊ ≤ (T_tot + (encP a).length) ^ 2 := by
    rcases hp_int (sizeP a) with hpz | hp1
    · simp [hpz]
    · have h1 : p (sizeP a) ≤ P_val ^ 2 := by
        calc p (sizeP a) = (p (sizeP a)) ^ ((1 : ℝ)) := (Real.rpow_one _).symm
          _ ≤ (p (sizeP a)) ^ (2 * (1 - d)) :=
              Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
          _ = P_val ^ 2 := by
              rw [show (2 : ℝ) * (1 - d) = (1 - d) * 2 by ring, Real.rpow_mul (hp0 _),
                Real.rpow_two]
      have h2 : P_val ≤ (T_tot : ℝ) := by
        have hc := Nat.le_ceil P_val
        have hC1 : (1 : ℝ) ≤ (C_tot : ℝ) := by exact_mod_cast hC_tot_pos
        rw [← hmaxP] at hc
        have : (T_tot : ℝ) = (C_tot : ℝ) * (⌈max 0 P_val⌉₊ : ℝ) + (C_tot : ℝ) := by
          push_cast [T_tot]; ring
        nlinarith
      have h3 : p (sizeP a) ≤ ((T_tot + (encP a).length : ℕ) : ℝ) ^ 2 := by
        have hTle : (T_tot : ℝ) ≤ ((T_tot + (encP a).length : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_add_right _ _
        nlinarith
      exact Nat.ceil_le.mpr (by exact_mod_cast h3)
  have hlog_p : Nat.log 2 (⌈p (sizeP a)⌉₊ + (encP a).length) + 1 ≤
      2 * (Nat.log 2 (T_tot + (encP a).length) + 1) := by
    have hlt : T_tot + (encP a).length < 2 ^ (Nat.log 2 (T_tot + (encP a).length) + 1) :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two _
    have hsum_lt : ⌈p (sizeP a)⌉₊ + (encP a).length <
        2 ^ (2 * (Nat.log 2 (T_tot + (encP a).length) + 1)) := by
      have hlt' : (T_tot + (encP a).length) ^ 2 + (T_tot + (encP a).length) <
          (2 ^ (Nat.log 2 (T_tot + (encP a).length) + 1)) ^ 2 := by
        have hpos : 1 ≤ 2 ^ (Nat.log 2 (T_tot + (encP a).length) + 1) := Nat.one_le_two_pow
        nlinarith
      rw [← pow_mul, mul_comm] at hlt'
      omega
    rcases Nat.eq_zero_or_pos (⌈p (sizeP a)⌉₊ + (encP a).length) with hz | hpos
    · rw [hz]; simp; omega
    · exact Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow hpos.ne' hsum_lt)
  set w_log := W - 3
  have hW_ge_log : K_tot * (Nat.log 2 (T_tot + (encP a).length) + 1) ≤ W := hW
  have hW_ge10 : 10 ≤ W := by
    have : 1 ≤ Nat.log 2 (T_tot + (encP a).length) + 1 := by omega
    have : K_tot ≤ W := le_trans (Nat.le_mul_of_pos_right _ this) hW_ge_log
    omega
  have hw_log_A : logWidth k_A (⌈p (sizeP a)⌉₊ + (encP a).length) ≤ w_log := by
    have hmul : k_A * (Nat.log 2 (⌈p (sizeP a)⌉₊ + (encP a).length) + 1) ≤
        2 * k_A * (Nat.log 2 (T_tot + (encP a).length) + 1) := by
      calc k_A * (Nat.log 2 (⌈p (sizeP a)⌉₊ + (encP a).length) + 1)
          ≤ k_A * (2 * (Nat.log 2 (T_tot + (encP a).length) + 1)) := Nat.mul_le_mul_left _ hlog_p
        _ = 2 * k_A * (Nat.log 2 (T_tot + (encP a).length) + 1) := by ring
    have hK : 2 * k_A + 3 ≤ K_tot := by omega
    have h1 : 1 ≤ Nat.log 2 (T_tot + (encP a).length) + 1 := by omega
    have hW' : (2 * k_A + 3) * (Nat.log 2 (T_tot + (encP a).length) + 1) ≤ W :=
      (Nat.mul_le_mul_right _ hK).trans hW_ge_log
    have hW'' : 2 * k_A * (Nat.log 2 (T_tot + (encP a).length) + 1) + 3 ≤ W := by
      have : 3 ≤ 3 * (Nat.log 2 (T_tot + (encP a).length) + 1) := by omega
      rw [Nat.add_mul] at hW'; omega
    simp only [logWidth, w_log]; omega
  have hw_log_e : logWidth k_e (⌈p (sizeP a)⌉₊ + (encP a).length) ≤ w_log := by
    have hK : 2 * k_e + 3 ≤ K_tot := by omega
    have h1 : 1 ≤ Nat.log 2 (T_tot + (encP a).length) + 1 := by omega
    have hW' : (2 * k_e + 3) * (Nat.log 2 (T_tot + (encP a).length) + 1) ≤ W :=
      (Nat.mul_le_mul_right _ hK).trans hW_ge_log
    have hle2 : k_e * (Nat.log 2 (⌈p (sizeP a)⌉₊ + (encP a).length) + 1) ≤
        2 * k_e * (Nat.log 2 (T_tot + (encP a).length) + 1) := by
      calc k_e * (Nat.log 2 (⌈p (sizeP a)⌉₊ + (encP a).length) + 1)
          ≤ k_e * (2 * (Nat.log 2 (T_tot + (encP a).length) + 1)) := Nat.mul_le_mul_left _ hlog_p
        _ = 2 * k_e * (Nat.log 2 (T_tot + (encP a).length) + 1) := by ring
    have hW'' : 2 * k_e * (Nat.log 2 (T_tot + (encP a).length) + 1) + 3 ≤ W := by
      have : 3 ≤ 3 * (Nat.log 2 (T_tot + (encP a).length) + 1) := by omega
      rw [Nat.add_mul] at hW'; omega
    simp only [logWidth, w_log]; omega
  have hfits_A : InputFits w_log (encP a) := (henc_fits a).mono hw_log_e
  obtain ⟨y_A, t_A, qs_A, hex_A, hyA_le, hyA_iff, hvalid_A, ht_A, hsum_A⟩ :=
    hA a w_log hw_log_A hfits_A
  -- Bound t_A and each query's time
  have ht_A_nat : t_A ≤ C_A * ⌈max 0 P_val⌉₊ + 2 * C_A := by
    have h1 : (t_A : ℝ) ≤ (C_A : ℝ) * (P_val + 1) + (C_A : ℝ) := ht_A.trans (by nlinarith)
    have h2 : P_val ≤ (⌈max 0 P_val⌉₊ : ℝ) := by rw [hmaxP]; exact Nat.le_ceil P_val
    have h3 : (t_A : ℝ) ≤ ((C_A * ⌈max 0 P_val⌉₊ + 2 * C_A : ℕ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast h3
  have ht_A_lt_H : t_A < 2 ^ w_log := by
    have hlt : T_tot + (encP a).length < 2 ^ (Nat.log 2 (T_tot + (encP a).length) + 1) :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two _
    have hw1 : Nat.log 2 (T_tot + (encP a).length) + 1 ≤ w_log := by
      have : 1 ≤ Nat.log 2 (T_tot + (encP a).length) + 1 := by omega
      have hK : 4 ≤ K_tot := by omega
      have : 4 * (Nat.log 2 (T_tot + (encP a).length) + 1) ≤ W :=
        (Nat.mul_le_mul_right _ hK).trans hW_ge_log
      omega
    have hpow := Nat.pow_le_pow_right Nat.two_pos hw1
    have hTA : t_A ≤ T_tot := by
      have h2CA : 2 * C_A ≤ C_tot := by
        have h1 : 1 ≤ 30 * C_Q + r_Q + 50 := by omega
        have h2 : 2 * C_A + 2 ≤ (30 * C_Q + r_Q + 50) * (2 * C_A + 2) :=
          Nat.le_mul_of_pos_left _ h1
        omega
      have hmul : C_A * ⌈max 0 P_val⌉₊ ≤ C_tot * ⌈max 0 P_val⌉₊ :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  -- Run setup of mainCode
  have h3_fits : Fits W 3 := by
    have : 2 ^ 3 ≤ 2 ^ W := Nat.pow_le_pow_right Nat.two_pos (by omega)
    exact show 3 < 2 ^ W by norm_num at this; omega
  have h1_fits : Fits W 1 := Fits.of_le h3_fits (by omega)
  have hwlog_fits : Fits W w_log := Fits.of_le (fits_self W) (Nat.sub_le W 3)
  have hH_fits : Fits W (2 ^ w_log) := Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
  let x0 : Data r_tot := .init (encP a)
  let s1 := x0.set rWlog W
  let s2 := s1.set rTmp 3
  let s3 := s2.set rWlog w_log
  let s4 := s3.set rCW w_log
  let s5 := s4.set rTmp 1
  let s6 := s5.set rH (2 ^ w_log)
  let s7 := s6.set rGen 0
  have hsetup : ExecWithin (B := .standard) W
      (ram[rWlog ← width%; rTmp ← #3; rWlog ← rWlog - rTmp; rCW ← rWlog;
        rTmp ← #1; rH ← rTmp <<< rWlog; rGen ← #0]) x0 s7 7 := by
    have e1 : ExecWithin W (.op (.width rWlog)) x0 s1 1 := ExecWithin.width
    have e2 : ExecWithin W (.op (Op.const (B := .standard) rTmp 3)) s1 s2 1 :=
      ExecWithin.const h3_fits
    have e3 : ExecWithin W (.op (.bin .sub rWlog rWlog rTmp)) s2 s3 1 := by
      have hne : rWlog ≠ rTmp := Fin.ne_of_val_ne (by simp [rWlog, rTmp])
      simpa [s3, s2, s1, hne, w_log] using ExecWithin.bin (w := W) (x := s2) (f := .sub)
        (d := rWlog) (i := rWlog) (j := rTmp) (by simpa [s2, s1, hne, w_log] using hwlog_fits)
    have e4 : ExecWithin W (.op (Op.copy (B := .standard) rCW rWlog)) s3 s4 1 := by
      simpa [s4, s3] using ExecWithin.copy (B := .standard) (w := W) (x := s3) (d := rCW)
        (s := rWlog)
    have e5 : ExecWithin W (.op (Op.const (B := .standard) rTmp 1)) s4 s5 1 :=
      ExecWithin.const h1_fits
    have e6 : ExecWithin W (.op (.bin .shiftLeft rH rTmp rWlog)) s5 s6 1 := by
      have hne1 : rWlog ≠ rTmp := Fin.ne_of_val_ne (by simp [rWlog, rTmp])
      have hne2 : rWlog ≠ rCW := (callerWidthReg_ne_subReg _).symm
      have hne3 : rTmp ≠ rCW := (callerWidthReg_ne_subReg _).symm
      have hshift : 1 <<< w_log = 2 ^ w_log := by simp [Nat.shiftLeft_eq]
      simpa [s6, s5, s4, s3, hne1, hne2, hne3, hshift] using
        ExecWithin.bin (w := W) (x := s5) (f := .shiftLeft) (d := rH) (i := rTmp) (j := rWlog)
          (by simpa [s5, s4, s3, hne1, hne2, hne3, hshift] using hH_fits)
    have e7 : ExecWithin W (.op (Op.const (B := .standard) rGen 0)) s6 s7 1 :=
      ExecWithin.const (fits_zero W)
    exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
  -- Define invariant for compileOracle
  let H := 2 ^ w_log
  let Inv (m : ℕ → ℕ) (rs : Fin (r_sub + 3) → ℕ) (k : ℕ) : Prop :=
    rs ⟨3, by omega⟩ = H ∧ rs ⟨4, by omega⟩ = w_log ∧
      rs ⟨5, by omega⟩ + k ≤ t_A ∧ StampLe (2 * H) H (rs ⟨5, by omega⟩) m
  have hinv_lo : ∀ m₁ m₂ rs k, (∀ addr, 2 ^ w_log ≤ addr → m₁ addr = m₂ addr) →
      Inv m₁ rs k → Inv m₂ rs k := by
    intro m₁ m₂ rs k hagree ⟨h3', h4', h5', hst'⟩
    refine ⟨h3', h4', h5', fun addr ha => ?_⟩
    rw [← hagree (2 * H + 2 * addr) (by change 2 ^ w_log ≤ 2 * 2 ^ w_log + 2 * addr; omega)]
    exact hst' addr ha
  have hinv_args : ∀ m rs k u v, Inv m rs k →
      Inv m (Function.update (Function.update rs ⟨0, by omega⟩ u) ⟨1, by omega⟩ v) k := by
    intro m rs k u v ⟨h3', h4', h5', hst'⟩
    refine ⟨?_, ?_, ?_, hst'⟩ <;> simp [Fin.ext_iff, h3', h4', h5']
  -- Check initial conditions on s7
  have hs7_W : s7.regs callerWidthReg = w_log := by
    have h1' := callerWidthReg_ne_subReg (r_c := r_A) (r_s := r_sub + 3) ⟨3, by omega⟩
    have h2' := callerWidthReg_ne_subReg (r_c := r_A) (r_s := r_sub + 3) ⟨5, by omega⟩
    have h3' := callerWidthReg_ne_subReg (r_c := r_A) (r_s := r_sub + 3) ⟨6, by omega⟩
    simp only [s7, s6, s5, s4, Data.set_regs, rCW, rH, rGen, rTmp,
      Function.update_of_ne h1', Function.update_of_ne h2', Function.update_of_ne h3',
      Function.update_self]
  have hs7_caller : s7.regs ∘ callerReg = (Data.init (encP a) (r := r_A)).regs := by
    funext i
    have hne : ∀ j : Fin (r_sub + 3), callerReg (r_c := r_A) i ≠ subReg j := callerReg_ne_subReg i
    have hneW := callerReg_ne_callerWidthReg (r_s := r_sub + 3) i
    simp only [Function.comp_apply, s7, s6, s5, s4, s3, s2, s1, x0, Data.set_regs, Data.init_regs,
      rH, rWlog, rGen, rTmp, rCW, Function.update_of_ne (hne _), Function.update_of_ne hneW]
  have hs7_mem : ∀ addr < 2 ^ w_log, s7.mem addr = (Data.init (encP a) (r := r_A)).mem addr :=
    fun _ _ => rfl
  have hs7_inv : Inv s7.mem (s7.regs ∘ subReg) qs_A.length := by
    have h35 : subReg (r_c := r_A) (⟨3, by omega⟩ : Fin (r_sub + 3)) ≠ subReg ⟨5, by omega⟩ :=
      fun h => by have := subReg_injective h; simp [Fin.ext_iff] at this
    have h45 : subReg (r_c := r_A) (⟨4, by omega⟩ : Fin (r_sub + 3)) ≠ subReg ⟨5, by omega⟩ :=
      fun h => by have := subReg_injective h; simp [Fin.ext_iff] at this
    have h43 : subReg (r_c := r_A) (⟨4, by omega⟩ : Fin (r_sub + 3)) ≠ subReg ⟨3, by omega⟩ :=
      fun h => by have := subReg_injective h; simp [Fin.ext_iff] at this
    have h46 : subReg (r_c := r_A) (⟨4, by omega⟩ : Fin (r_sub + 3)) ≠ subReg ⟨6, by omega⟩ :=
      fun h => by have := subReg_injective h; simp [Fin.ext_iff] at this
    have h4W := (callerWidthReg_ne_subReg (r_c := r_A) (r_s := r_sub + 3) ⟨4, by omega⟩).symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Function.comp_apply, s7, s6, Data.set_regs, rH, rGen,
        Function.update_of_ne h35, Function.update_self, H]
    · simp only [Function.comp_apply, s7, s6, s5, s4, s3, Data.set_regs, rWlog, rH, rGen, rTmp, rCW,
        Function.update_of_ne h45, Function.update_of_ne h43, Function.update_of_ne h46,
        Function.update_of_ne h4W, Function.update_self]
    · simp only [Function.comp_apply, s7, rGen, Data.set_regs, Function.update_self, Nat.zero_add]
      exact hex_A.length_queries_le
    · intro addr _
      have hmem_eq : s7.mem (2 * H + 2 * addr) = x0.mem (2 * H + 2 * addr) := rfl
      have hne0 : 2 * H + 2 * addr ≠ 0 := by have : 1 ≤ H := Nat.one_le_two_pow; omega
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne0
      rw [hmem_eq, hm]
      simp only [Function.comp_apply, s7, rGen, Data.set_regs, Function.update_self,
        x0, Data.init_mem_succ]
      have hge : (encP a).length ≤ m := by
        have hlen : (encP a).length < 2 ^ w_log := hfits_A.1
        change (encP a).length < H at hlen
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; simp
  -- Bound each query time using hQ_dec
  let T_sub (qi : List ℕ) : ℕ :=
    11 * qi.length + 7 * (C_Q * ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊ + 2 * C_Q) +
      r_Q + 20
  obtain ⟨y_fin, hy_fin, _, hy_caller, _, _⟩ :=
    compileOracle_exec (W := W) (w := w_log) (c := c_A) (sub := sub) (T_sub := T_sub) (Inv := Inv)
      (by omega) (Data.Bounded.init hfits_A) hex_A hinv_lo hinv_args
      (fun qi k xsub hqi hk1 hbl hq_m hq_l hinv_sub => by
        obtain ⟨h3', h4', h5', hst'⟩ := hinv_sub
        obtain ⟨b, rfl⟩ := hvalid_A qi hqi
        have hq_fits_b : InputFits w_log (encQ b) :=
          hex_A.inputFits_queries (Data.Bounded.init hfits_A) _ hqi
        have hT_b_le : C_Q * ⌈max 0 ((q (sizeQ b)) ^ (1 - ε))⌉₊ + C_Q ≤
            C_Q * ⌈max 0 ((q (sizeQ b)) ^ (1 - ε'))⌉₊ + 2 * C_Q := by
          rcases hq_int (sizeQ b) with hqz | hq1
          · rw [hqz]
            by_cases h1ε : (1 : ℝ) - ε = 0
            · have : ⌈max 0 ((0 : ℝ) ^ (1 - ε))⌉₊ = 1 := by rw [h1ε, Real.rpow_zero]; norm_num
              rw [this]; omega
            · have : ⌈max 0 ((0 : ℝ) ^ (1 - ε))⌉₊ = 0 := by rw [Real.zero_rpow h1ε]; norm_num
              rw [this]; omega
          · have hpow : (q (sizeQ b)) ^ (1 - ε) ≤ (q (sizeQ b)) ^ (1 - ε') :=
              Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
            have hceil : ⌈max 0 ((q (sizeQ b)) ^ (1 - ε))⌉₊ ≤
                ⌈max 0 ((q (sizeQ b)) ^ (1 - ε'))⌉₊ :=
              Nat.ceil_mono (max_le_max_left 0 hpow)
            have hmul := Nat.mul_le_mul_left C_Q hceil
            omega
        have hq_sum_le : (q (sizeQ b)) ^ (1 - ε') ≤ (C_A : ℝ) * (P_val + 1) + (C_A : ℝ) := by
          have hmem_le : (q (sizeQ b)) ^ (1 - ε') ≤
              (qs_A.map fun qi => (q (querySize encQ sizeQ qi)) ^ (1 - ε')).sum := by
            have hmem' : (q (sizeQ b)) ^ (1 - ε') ∈
                qs_A.map (fun qi => (q (querySize encQ sizeQ qi)) ^ (1 - ε')) := by
              refine List.mem_map.mpr ⟨encQ b, hqi, ?_⟩
              rw [querySize_enc]
            exact List.single_le_sum (fun x hx => by
              obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
              exact Real.rpow_nonneg (hq0 _) _) _ hmem'
          have hCA_mul := mul_le_mul_of_nonneg_left hP_le (Nat.cast_nonneg C_A)
          linarith
        have hT_b_lt_Ttot : C_Q * ⌈max 0 ((q (sizeQ b)) ^ (1 - ε))⌉₊ + C_Q + (encQ b).length ≤
            T_tot := by
          have hlen_b : (encQ b).length ≤ t_A := by
            have h1 := hex_A.sum_query_length_le
            have h2 : (encQ b).length + 1 ≤ (qs_A.map fun q => q.length + 1).sum :=
              List.single_le_sum (fun _ _ => Nat.zero_le _) _
                (List.mem_map.mpr ⟨encQ b, hqi, rfl⟩)
            omega
          have hceil_b : ⌈max 0 ((q (sizeQ b)) ^ (1 - ε'))⌉₊ ≤
              C_A * ⌈max 0 P_val⌉₊ + 2 * C_A := by
            refine Nat.ceil_le.mpr ?_
            rw [max_eq_right (Real.rpow_nonneg (hq0 _) _)]
            have hP_c : P_val ≤ (⌈max 0 P_val⌉₊ : ℝ) := by rw [hmaxP]; exact Nat.le_ceil P_val
            have hCA_c := mul_le_mul_of_nonneg_left (show P_val + 1 ≤ (⌈max 0 P_val⌉₊ : ℝ) + 1 by
              linarith) (Nat.cast_nonneg C_A)
            push_cast
            linarith
          have h1 : C_Q * ⌈max 0 ((q (sizeQ b)) ^ (1 - ε))⌉₊ + C_Q ≤
              C_Q * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A) + 2 * C_Q := by
            have hmul := Nat.mul_le_mul_left C_Q hceil_b
            omega
          have h2 : C_Q * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A) + 2 * C_Q + t_A ≤ T_tot := by
            have hmul1 : C_Q * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A) =
                (C_Q * C_A) * ⌈max 0 P_val⌉₊ + 2 * (C_Q * C_A) := by ring
            have hC_ge : (C_Q * C_A + C_A) ≤ C_tot := by
              have hexp : (30 * C_Q + r_Q + 50) * (2 * C_A + 2) =
                  60 * (C_Q * C_A) + 60 * C_Q + 2 * (r_Q + 50) * C_A + 2 * (r_Q + 50) := by ring
              have h2' : 2 * C_A ≤ 2 * (r_Q + 50) * C_A :=
                Nat.mul_le_mul_right _ (by omega)
              change C_Q * C_A + C_A ≤ (30 * C_Q + r_Q + 50) * (2 * C_A + 2) + 20
              omega
            have hCA_P := Nat.mul_le_mul_right ⌈max 0 P_val⌉₊ hC_ge
            have hC_const : 2 * (C_Q * C_A) + 2 * C_Q + 2 * C_A ≤ C_tot := by
              have hexp : (30 * C_Q + r_Q + 50) * (2 * C_A + 2) =
                  60 * (C_Q * C_A) + 60 * C_Q + 2 * (r_Q + 50) * C_A + 2 * (r_Q + 50) := by ring
              have h2' : 2 * C_A ≤ 2 * (r_Q + 50) * C_A :=
                Nat.mul_le_mul_right _ (by omega)
              change 2 * (C_Q * C_A) + 2 * C_Q + 2 * C_A ≤
                (30 * C_Q + r_Q + 50) * (2 * C_A + 2) + 20
              omega
            have hadd : (C_Q * C_A + C_A) * ⌈max 0 P_val⌉₊ =
                C_Q * C_A * ⌈max 0 P_val⌉₊ + C_A * ⌈max 0 P_val⌉₊ := by ring
            change _ ≤ C_tot * ⌈max 0 P_val⌉₊ + C_tot
            omega
          omega
        have hw_log_Q : logWidth k_Q
            (C_Q * ⌈max 0 ((q (sizeQ b)) ^ (1 - ε))⌉₊ + C_Q + (encQ b).length) ≤ w_log := by
          have h1 : logWidth k_Q
              (C_Q * ⌈max 0 ((q (sizeQ b)) ^ (1 - ε))⌉₊ + C_Q + (encQ b).length) ≤
              logWidth k_Q (T_tot + (encP a).length) :=
            logWidth_mono le_rfl (hT_b_lt_Ttot.trans (Nat.le_add_right _ _))
          have hK : k_Q + 3 ≤ K_tot := by omega
          have h2 : 1 ≤ Nat.log 2 (T_tot + (encP a).length) + 1 := by omega
          have h3 : (k_Q + 3) * (Nat.log 2 (T_tot + (encP a).length) + 1) ≤ W :=
            (Nat.mul_le_mul_right _ hK).trans hW_ge_log
          have hexp : (k_Q + 3) * (Nat.log 2 (T_tot + (encP a).length) + 1) =
              k_Q * (Nat.log 2 (T_tot + (encP a).length) + 1) +
              3 * (Nat.log 2 (T_tot + (encP a).length) + 1) := by ring
          simp only [logWidth, w_log] at h1 h3 ⊢
          omega
        obtain ⟨y_Q, ⟨t_Q, ht_Q, hex_Q⟩, hyQ_le, hyQ_iff⟩ := hQ_dec b w_log hw_log_Q hq_fits_b
        have hgenW : Fits W (xsub.regs ⟨5, by omega⟩ + 1) := by
          have hlt : xsub.regs ⟨5, by omega⟩ + 1 ≤ t_A := by omega
          exact Fits.mono (lt_of_le_of_lt hlt ht_A_lt_H) (by omega)
        have h4H : 4 * H ≤ 2 ^ W := by
          have : 4 * 2 ^ w_log = 2 ^ (w_log + 2) := by rw [pow_add]; ring
          change 4 * 2 ^ w_log ≤ 2 ^ W
          rw [this]
          exact Nat.pow_le_pow_right Nat.two_pos (by omega)
        obtain ⟨z, hz, hz2, hz3, hz4, hz5, hzst, hzfr⟩ :=
          wrapPureSolverCode_exec hrf_Q le_rfl h4H hgenW hq_fits_b hex_Q hbl hq_l hq_m
            h3' h4' rfl hst'
        have hz2_eq : z.regs ⟨2, by omega⟩ = (oracleOf Q encQ (encQ b)).toNat := by
          rw [hz2]
          by_cases hb : b ∈ Q
          · have : y_Q.regs out_Q = 1 := hyQ_iff.mpr hb
            rw [this, (oracleOf_enc Q encQ b).mpr hb]; rfl
          · have hne : y_Q.regs out_Q ≠ 1 := fun h => hb (hyQ_iff.mp h)
            have h0 : y_Q.regs out_Q = 0 := by omega
            have hf : oracleOf Q encQ (encQ b) = false := by
              cases h : oracleOf Q encQ (encQ b)
              · rfl
              · exact absurd ((oracleOf_enc Q encQ b).mp h) hb
            rw [h0, hf]; rfl
        have ht_sub : 11 * (encQ b).length + 7 * t_Q + r_Q + 20 ≤ T_sub (encQ b) := by
          dsimp only at ht_Q
          simp only [T_sub, querySize_enc]
          omega
        refine ⟨z, hz.mono ht_sub, hz2_eq, fun addr ha => hzfr addr (by omega),
          ⟨hz3, hz4, by omega, hz5 ▸ hzst⟩⟩)
      le_rfl hs7_W hs7_caller hs7_mem hs7_inv
  -- Sum total execution time and check output
  have hsum_Tsub : (qs_A.map fun qi => T_sub qi + 3).sum ≤
      (14 * C_Q + r_Q + 40) * t_A + 7 * C_Q * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A) +
        7 * C_Q * t_A := by
    have hsplit : ∀ l : List (List ℕ),
        (l.map fun qi => T_sub qi + 3).sum ≤
          (14 * C_Q + r_Q + 40) * (l.map fun qi => qi.length + 1).sum +
            7 * C_Q * (l.map fun qi => ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 -
              ε'))⌉₊).sum := by
      intro l
      induction l with
      | nil => simp
      | cons qi l ih =>
        simp only [List.map_cons, List.sum_cons]
        have hstep : T_sub qi + 3 ≤
            (14 * C_Q + r_Q + 40) * (qi.length + 1) +
              7 * C_Q * ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊ := by
          dsimp only [T_sub]
          have hmul1 : (14 * C_Q + r_Q + 40) * (qi.length + 1) =
              (14 * C_Q + r_Q + 40) * qi.length + (14 * C_Q + r_Q + 40) := by ring
          have hmul2 : 11 * qi.length ≤ (14 * C_Q + r_Q + 40) * qi.length :=
            Nat.mul_le_mul_right _ (by omega)
          have hmul3 : 7 * (C_Q * ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊ + 2 * C_Q) =
              7 * C_Q * ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊ + 14 * C_Q := by ring
          omega
        have hdist1 :
            (14 * C_Q + r_Q + 40) * (qi.length + 1 + (l.map fun qi => qi.length + 1).sum) =
            (14 * C_Q + r_Q + 40) * (qi.length + 1) +
            (14 * C_Q + r_Q + 40) * (l.map fun qi => qi.length + 1).sum := by ring
        have hdist2 : 7 * C_Q * (⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊ +
            (l.map fun qi => ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊).sum) =
            7 * C_Q * ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊ +
            7 * C_Q * (l.map fun qi => ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊).sum :=
          by ring
        omega
    have hlen_sum := hex_A.sum_query_length_le
    have hceil_sum :
        (qs_A.map fun qi => ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊).sum ≤
          C_A * ⌈max 0 P_val⌉₊ + 2 * C_A + qs_A.length := by
      have hceil_le_add : ∀ l : List (List ℕ),
          ((l.map fun qi => ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊).sum : ℝ) ≤
            (l.map fun qi => (q (querySize encQ sizeQ qi)) ^ (1 - ε')).sum + l.length := by
        intro l
        induction l with
        | nil => simp
        | cons qi l ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
          have h1 : (⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊ : ℝ) ≤
              (q (querySize encQ sizeQ qi)) ^ (1 - ε') + 1 := by
            rw [max_eq_right (Real.rpow_nonneg (hq0 _) _)]
            exact le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg (hq0 _) _))
          linarith
      have hreal :
          ((qs_A.map fun qi => ⌈max 0 ((q (querySize encQ sizeQ qi)) ^ (1 - ε'))⌉₊).sum : ℝ) ≤
            ((C_A * ⌈max 0 P_val⌉₊ + 2 * C_A + qs_A.length : ℕ) : ℝ) := by
        have hP_c : P_val ≤ (⌈max 0 P_val⌉₊ : ℝ) := by rw [hmaxP]; exact Nat.le_ceil P_val
        have h1 := hceil_le_add qs_A
        have hCA1 := mul_le_mul_of_nonneg_left hP_le (Nat.cast_nonneg C_A)
        have hCA2 := mul_le_mul_of_nonneg_left hP_c (Nat.cast_nonneg C_A)
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
        linarith
      exact_mod_cast hreal
    have hqlen_le := hex_A.length_queries_le
    have hsp := hsplit qs_A
    have hm1 := Nat.mul_le_mul_left (14 * C_Q + r_Q + 40) hlen_sum
    have hm2 := Nat.mul_le_mul_left (7 * C_Q) hceil_sum
    have hm3 := Nat.mul_le_mul_left (7 * C_Q) hqlen_le
    have hd : 7 * C_Q * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A + qs_A.length) =
        7 * C_Q * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A) + 7 * C_Q * qs_A.length := by ring
    omega
  have hfinal_time : 7 + (t_A + (qs_A.map fun qi => T_sub qi + 3).sum) ≤ T_tot := by
    have h1 : 7 + (t_A + (qs_A.map fun qi => T_sub qi + 3).sum) ≤
        (21 * C_Q + r_Q + 41) * t_A + 7 * C_Q * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A) + 7 := by
      have hexp : (21 * C_Q + r_Q + 41) * t_A =
          (14 * C_Q + r_Q + 40) * t_A + 7 * C_Q * t_A + t_A := by ring
      omega
    have h2 : (21 * C_Q + r_Q + 41) * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A) +
        7 * C_Q * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A) + 7 ≤ T_tot := by
      have hcomb : (21 * C_Q + r_Q + 41) * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A) +
          7 * C_Q * (C_A * ⌈max 0 P_val⌉₊ + 2 * C_A) =
          (28 * C_Q + r_Q + 41) * C_A * ⌈max 0 P_val⌉₊ +
          (28 * C_Q + r_Q + 41) * (2 * C_A) := by ring
      have hcoef : (28 * C_Q + r_Q + 41) * C_A ≤ C_tot := by
        have h1' : (28 * C_Q + r_Q + 41) * C_A ≤ (30 * C_Q + r_Q + 50) * (2 * C_A + 2) :=
          Nat.mul_le_mul (by omega) (by omega)
        change (28 * C_Q + r_Q + 41) * C_A ≤ (30 * C_Q + r_Q + 50) * (2 * C_A + 2) + 20
        omega
      have hconst : (28 * C_Q + r_Q + 41) * (2 * C_A) + 7 ≤ C_tot := by
        have hexp : (30 * C_Q + r_Q + 50) * (2 * C_A + 2) =
            (30 * C_Q + r_Q + 50) * (2 * C_A) + 2 * (30 * C_Q + r_Q + 50) := by ring
        have h1' : (28 * C_Q + r_Q + 41) * (2 * C_A) ≤ (30 * C_Q + r_Q + 50) * (2 * C_A) :=
          Nat.mul_le_mul_right _ (by omega)
        change (28 * C_Q + r_Q + 41) * (2 * C_A) + 7 ≤ (30 * C_Q + r_Q + 50) * (2 * C_A + 2) + 20
        omega
      have hmulP := Nat.mul_le_mul_right ⌈max 0 P_val⌉₊ hcoef
      change _ ≤ C_tot * ⌈max 0 P_val⌉₊ + C_tot
      omega
    have hmulT := Nat.mul_le_mul_left (21 * C_Q + r_Q + 41) ht_A_nat
    omega
  refine ⟨y_fin, (hsetup.seq hy_fin).mono hfinal_time, ?_, ?_⟩
  · have := congrFun hy_caller out_A
    change y_fin.regs (callerReg out_A) = y_A.regs out_A at this
    rw [this]; exact hyA_le
  · have := congrFun hy_caller out_A
    change y_fin.regs (callerReg out_A) = y_A.regs out_A at this
    rw [this]; exact hyA_iff

/-! ### Synthetic Upwards Reduction -/

/-- Quadratic synthetic padding `x ↦ x 0 1^{|x|^2}`. -/
def syntheticPad (x : List Bool) : List Bool :=
  x ++ false :: List.replicate (x.length ^ 2) true

/-- Quadratically padded language `P' = { x 0 1^{|x|^2} | x ∈ P }`. -/
def syntheticP' (P : Set (List Bool)) : Set (List Bool) :=
  { y | ∃ x ∈ P, y = syntheticPad x }

theorem length_syntheticPad (x : List Bool) :
    (syntheticPad x).length = x.length + 1 + x.length ^ 2 := by
  simp [syntheticPad]; omega

theorem syntheticPad_injective : Function.Injective syntheticPad := by
  intro x₁ x₂ h
  have hlen : x₁.length = x₂.length := by
    have hl := congrArg List.length h
    simp only [length_syntheticPad] at hl
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith
  have hpre := congrArg (List.take x₁.length) h
  simpa [syntheticPad, hlen] using hpre

private def syntheticScanPre : Code .standard 10 :=
  let r0 : Fin 10 := 0; let r1 : Fin 10 := 1; let r2 : Fin 10 := 2
  let r3 : Fin 10 := 3; let r4 : Fin 10 := 4; let r7 : Fin 10 := 7
  let r9 : Fin 10 := 9
  ram[ r7 ← #0; r2 ← #1; r0 ← *r7; r3 ← #0; r4 ← #0; r9 ← #0; r1 ← #0 ]

private def syntheticScanBody : Code .standard 10 :=
  let r1 : Fin 10 := 1; let r2 : Fin 10 := 2; let r3 : Fin 10 := 3
  let r4 : Fin 10 := 4; let r5 : Fin 10 := 5; let r6 : Fin 10 := 6
  let r7 : Fin 10 := 7
  ram[
    r5 ← r2 + r1;
    r6 ← *r5;
    if r6 = r7 then [ r3 ← #1; r4 ← r1 ] else [ r3 ← r3 ];
    r1 ← r1 + r2
  ]

private def syntheticCheckLen : Code .standard 10 :=
  let r2 : Fin 10 := 2; let r4 : Fin 10 := 4; let r8 : Fin 10 := 8
  ram[ r8 ← r4 * r4; r8 ← r8 + r4; r8 ← r8 + r2 ]

private def syntheticUpwardsCode : OracleCode .standard 10 :=
  .seq (.ofCode (.seq syntheticScanPre (.loop (.lt 1 0) syntheticScanBody)))
    (.branch (.eq 3 2)
      (.seq (.ofCode syntheticCheckLen)
        (.branch (.eq 8 0) (.query 9 2 4) (.op (.const 9 0))))
      (.op (.const 9 0)))

private theorem mem_syntheticP'_iff_take {P : Set (List Bool)} {y : List Bool} {m : ℕ}
    (hm : m < y.length) (hy_m : y[m] = false)
    (hy_hi : ∀ j (hj : j < y.length), m < j → y[j] = true) :
    (y.length = m + 1 + m ^ 2 ∧ y.take m ∈ P) ↔ y ∈ syntheticP' P := by
  have heq : y.length = m + 1 + m ^ 2 → y = syntheticPad (y.take m) := by
    intro hlen
    have htake : (y.take m).length = m := by simp [List.length_take]; omega
    refine List.ext_getElem (by rw [length_syntheticPad, htake, hlen]) fun j hj₁ hj₂ => ?_
    simp only [syntheticPad]
    by_cases hjm : j < m
    · rw [List.getElem_append_left (by omega), List.getElem_take]
    · by_cases hje : j = m
      · subst hje
        rw [List.getElem_append_right (by omega : (y.take j).length ≤ j)]
        simp only [htake, Nat.sub_self, List.getElem_cons_zero]
        exact hy_m
      · simp only [List.getElem_append_right (by omega : (y.take m).length ≤ j), htake]
        have hpos : 0 < j - m := by omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j - m ≠ 0)
        simp only [hk, List.getElem_cons_succ, List.getElem_replicate]
        exact hy_hi j hj₁ (by omega)
  constructor
  · rintro ⟨hlen, hmem⟩
    exact ⟨y.take m, hmem, heq hlen⟩
  · rintro ⟨x, hx, rfl⟩
    have hxm : x.length = m := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have htrue : (syntheticPad x)[m] = true := by
          simp only [syntheticPad, List.getElem_append_right (by omega : x.length ≤ m)]
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m - x.length ≠ 0)
          simp only [hk, List.getElem_cons_succ, List.getElem_replicate]
        rw [hy_m] at htrue; cases htrue
      · have hfalse : (syntheticPad x)[x.length]'(by rw [length_syntheticPad]; omega) = false := by
          simp only [syntheticPad, List.getElem_append_right le_rfl, Nat.sub_self,
            List.getElem_cons_zero]
        have htrue := hy_hi x.length (by rw [length_syntheticPad]; omega) hgt
        rw [hfalse] at htrue; cases htrue
    subst hxm
    refine ⟨length_syntheticPad x, ?_⟩
    simpa [syntheticPad] using hx

/-- **Synthetic upwards reduction**: for any language `P : Set (List Bool)`,
the padded language `P' = { x 0 1^{|x|^2} | x ∈ P }` satisfies `(P', s^{3/2}) ≤ (P, s^3)`. -/
theorem syntheticUpwardsReduction (P : Set (List Bool)) :
    FineGrainedReducible (syntheticP' P) encBits List.length (fun s => (s : ℝ) ^ (3 / 2 : ℝ))
      P encBits List.length (fun s => (s : ℝ) ^ (3 : ℝ)) := by
  refine ⟨fun ε => min (1 / 3) ε, ?_, ?_, fun _ => by positivity, fun _ => by positivity,
    fun ε hε => lt_min (by norm_num) hε, fun ε hε => ?_⟩
  · intro a b hab
    exact Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) (by norm_num)
  · intro a b hab
    exact Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) (by norm_num)
  · refine ⟨10, syntheticUpwardsCode, 9, 35, 3, by omega, by omega, fun y w hw hi => ?_⟩
    set s := y.length
    have hlen_y : (encBits y).length = s := by simp [s]
    have h1_fits : Fits w 1 := by
      have h3w : 3 ≤ w := le_trans (by simp [logWidth]) hw
      exact fits_one (by omega)
    -- Execute syntheticScanPre
    let x0 : Data 10 := .init (encBits y)
    let x1 := x0.set 7 0
    let x2 := x1.set 2 1
    let x3 := x2.set 0 s
    let x4 := x3.set 3 0
    let x5 := x4.set 4 0
    let x6 := x5.set 9 0
    let x7 := x6.set 1 0
    have hpre : ExecWithin (B := .standard) w syntheticScanPre x0 x7 7 := by
      have e1 : ExecWithin w (.op (Op.const (B := .standard) 7 0)) x0 x1 1 :=
        ExecWithin.const (fits_zero w)
      have e2 : ExecWithin w (.op (Op.const (B := .standard) 2 1)) x1 x2 1 :=
        ExecWithin.const h1_fits
      have e3 : ExecWithin w (.op (Op.load (B := .standard) 0 7)) x2 x3 1 := by
        simpa [x3, x2, x1, x0, s] using ExecWithin.load (w := w) (x := x2) (d := 0) (a := 7)
      have e4 : ExecWithin w (.op (Op.const (B := .standard) 3 0)) x3 x4 1 :=
        ExecWithin.const (fits_zero w)
      have e5 : ExecWithin w (.op (Op.const (B := .standard) 4 0)) x4 x5 1 :=
        ExecWithin.const (fits_zero w)
      have e6 : ExecWithin w (.op (Op.const (B := .standard) 9 0)) x5 x6 1 :=
        ExecWithin.const (fits_zero w)
      have e7 : ExecWithin w (.op (Op.const (B := .standard) 1 0)) x6 x7 1 :=
        ExecWithin.const (fits_zero w)
      exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
    -- Execute scan loop
    let Inv (k : ℕ) (d : Data 10) : Prop :=
      k ≤ s ∧ d.regs 0 = s ∧ d.regs 2 = 1 ∧ d.regs 7 = 0 ∧ d.regs 9 = 0 ∧ d.mem = x0.mem ∧
        d.regs 3 ≤ 1 ∧
        (d.regs 3 = 0 → ∀ j (hj : j < y.length), j < k → y[j]'hj = true) ∧
        (d.regs 3 = 1 → ∃ (hm : d.regs 4 < y.length), d.regs 4 < k ∧ y[d.regs 4]'hm = false ∧
          ∀ j (hj : j < y.length), j < k → d.regs 4 < j → y[j]'hj = true)
    have hI0 : Inv 0 x7 := ⟨Nat.zero_le s, by simp [x7, x6, x5, x4, x3],
      by simp [x7, x6, x5, x4, x3, x2], by simp [x7, x6, x5, x4, x3, x2, x1],
      by simp [x7, x6], rfl, by simp [x7, x6, x5, x4],
      fun _ _ _ hj => (Nat.not_lt_zero _ hj).elim, fun h => by simp [x7, x6, x5, x4] at h⟩
    obtain ⟨d_scan, hd_scan, hI_scan, _⟩ := ExecWithin.loop_count (w := w) (N := s) (T := 7)
      (index := 1) (limit := 0) (body := syntheticScanBody) Inv (fun d hd => hd.2.1)
      (fun d hd hlt => by
        obtain ⟨_, hd0, hd2, hd7, hd9, hdm, hd3le, hd_none, hd_some⟩ := hd
        set i := d.regs 1
        have hi_lt : i < s := hlt
        have hf5 : Fits w (d.regs 2 + d.regs 1) := by
          rw [hd2]; exact Fits.of_le hi.1 (by omega)
        let d1 := d.set 5 (1 + i)
        let d2 := d1.set 6 ((y[i]'hi_lt).toNat)
        have hmem_i : d1.mem (1 + i) = (y[i]'hi_lt).toNat := by
          simp only [d1, Data.set_mem, hdm, x0, show 1 + i = i + 1 by omega, Data.init_mem_succ,
            encBits_apply, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem hi_lt, Option.map_some, Option.getD_some]
        have e1 : ExecWithin w (.op (.bin .add 5 2 1)) d d1 1 := by
          simpa [d1, hd2] using ExecWithin.bin (w := w) (x := d) (f := .add) (d := 5) (i := 2)
            (j := 1) hf5
        have e2 : ExecWithin w (.op (Op.load (B := .standard) 6 5)) d1 d2 1 := by
          simpa [d2, d1, hmem_i] using ExecWithin.load (B := .standard) (w := w) (x := d1)
            (d := 6) (a := 5)
        have hbr : ∃ d3, ExecWithin (B := .standard) w
            (.branch (.eq 6 7)
              (.seq (.op (.const 3 1)) (.op (.copy 4 1)))
              (.op (.copy 3 3))) d2 d3 4 ∧
            d3.regs 0 = s ∧ d3.regs 1 = i ∧ d3.regs 2 = 1 ∧ d3.regs 7 = 0 ∧ d3.regs 9 = 0 ∧
            d3.mem = x0.mem ∧ d3.regs 3 ≤ 1 ∧
            (d3.regs 3 = 0 → ∀ j (hj : j < y.length), j < i + 1 → y[j]'hj = true) ∧
            (d3.regs 3 = 1 → ∃ (hm : d3.regs 4 < y.length), d3.regs 4 < i + 1 ∧
              y[d3.regs 4]'hm = false ∧
              ∀ j (hj : j < y.length), j < i + 1 → d3.regs 4 < j → y[j]'hj = true) := by
          cases hbi : y[i]'hi_lt with
          | false =>
            have hc : (Cond.eq 6 7).Holds d2 := by simp [Cond.Holds, d2, d1, hd7, hbi]
            let t1 := d2.set 3 1
            let t2 := t1.set 4 i
            refine ⟨t2, (ExecWithin.branch_pos hc ((ExecWithin.const h1_fits).seq
                (by simpa [t2, t1, d2, d1] using ExecWithin.copy (w := w) (x := t1) (d := 4) (s :=
                  1)))).mono
                (by omega),
              by simp [t2, t1, d2, d1, hd0], by simp [t2, t1, d2, d1, i],
              by simp [t2, t1, d2, d1, hd2], by simp [t2, t1, d2, d1, hd7],
              by simp [t2, t1, d2, d1, hd9], by simp [t2, t1, d2, d1, hdm],
              by simp [t2, t1], fun h => by simp [t2, t1] at h, fun _ => ?_⟩
            refine ⟨by simpa [t2] using hi_lt, by simp [t2], by simpa [t2] using hbi,
              fun j hj _ hgt => by simp [t2] at hgt; omega⟩
          | true =>
            have hc : ¬(Cond.eq 6 7).Holds d2 := by simp [Cond.Holds, d2, d1, hd7, hbi]
            let t1 := d2.set 3 (d.regs 3)
            refine ⟨t1, (ExecWithin.branch_neg hc
                (by simpa [t1, d2, d1] using ExecWithin.copy (w := w) (x := d2) (d := 3) (s :=
                  3))).mono
                (by omega),
              by simp [t1, d2, d1, hd0], by simp [t1, d2, d1, i],
              by simp [t1, d2, d1, hd2], by simp [t1, d2, d1, hd7],
              by simp [t1, d2, d1, hd9], by simp [t1, d2, d1, hdm],
              by simpa [t1] using hd3le, fun h0 => ?_, fun h1 => ?_⟩
            · intro j hj hltj
              by_cases hji : j = i
              · subst hji; exact hbi
              · exact hd_none (by simpa [t1] using h0) j hj (by omega)
            · obtain ⟨hm, hk, hf, hhi⟩ := hd_some (by simpa [t1] using h1)
              have hr4 : t1.regs 4 = d.regs 4 := by simp [t1, d2, d1]
              refine ⟨by omega, by omega, by simpa [hr4] using hf, fun j hj hltj hgt => ?_⟩
              by_cases hji : j = i
              · subst hji; exact hbi
              · exact hhi j hj (by omega) (by omega)
        obtain ⟨d3, hd3, h30, h31, h32, h37, h39, h3m, h33le, h3_0, h3_1⟩ := hbr
        have hf_inc : Fits w (d3.regs 1 + d3.regs 2) := by
          rw [h31, h32]; exact Fits.of_le hi.1 (by omega)
        let d4 := d3.set 1 (i + 1)
        have he_inc : ExecWithin w (.op (.bin .add 1 1 2)) d3 d4 1 := by
          simpa [d4, h31, h32] using ExecWithin.bin (w := w) (x := d3) (f := .add) (d := 1)
            (i := 1) (j := 2) hf_inc
        refine ⟨d4, (e1.seq (e2.seq (hd3.seq he_inc))).mono (by omega),
          ⟨by omega, by simp [d4, h30], by simp [d4, h32], by simp [d4, h37], by simp [d4, h39],
            by simp [d4, h3m], by simp [d4, h33le],
            fun h j hj hltj => h3_0 (by simpa [d4] using h) j hj hltj,
            fun h => by
              obtain ⟨hm, hk, hf, hhi⟩ := h3_1 (by simpa [d4] using h)
              exact ⟨by simpa [d4] using hm, by simpa [d4] using hk, by simpa [d4] using hf,
                fun j hj hltj hgt => hhi j hj hltj (by simpa [d4] using hgt)⟩⟩, by simp [d4]⟩)
      (x := x7) (by simp [x7]) (by simpa [x7] using hI0)
    have hscan_or : ∃ t_sc ≤ 9 * s + 9,
        OracleExec w (oracleOf P encBits)
          (.ofCode (.seq syntheticScanPre (.loop (.lt 1 0) syntheticScanBody))) x0 d_scan t_sc []
            := by
      have hsc : ExecWithin w (.seq syntheticScanPre (.loop (.lt 1 0) syntheticScanBody))
          x0 d_scan (9 * s + 9) := (hpre.seq hd_scan).mono (by omega)
      obtain ⟨t_sc, ht_sc, hex_sc⟩ := hsc
      have hrf_sc : (Code.seq syntheticScanPre (.loop (.lt 1 0) syntheticScanBody)).IsRandFree := by
        simp [syntheticScanPre, syntheticScanBody, Code.IsRandFree]
      exact ⟨t_sc, ht_sc, oracleExec_of_exec hex_sc hrf_sc⟩
    obtain ⟨t_sc, ht_sc, hex_sc⟩ := hscan_or
    obtain ⟨_, hs0, hs2, hs7, hs9, hsm, hs3le, hs_none, hs_some⟩ := hI_scan
    -- Branch on found (reg 3 = reg 2)
    by_cases hfound : d_scan.regs 3 = 1
    · have hc1 : (Cond.eq 3 2).Holds d_scan := by simp [Cond.Holds, hfound, hs2]
      obtain ⟨hm_lt, _, hy_m, hy_hi_raw⟩ := hs_some hfound
      have hy_hi : ∀ j (hj : j < y.length), d_scan.regs 4 < j → y[j]'hj = true :=
        fun j hj hgt => hy_hi_raw j hj hj hgt
      set m := d_scan.regs 4
      have hm_sq : m * m + m + 1 < 2 ^ w := by
        have hcube : m * m + m + 1 < (s + 1) ^ 3 := by
          have h1 : (s + 1) ^ 3 = s * s * s + 3 * s * s + 3 * s + 1 := by ring
          nlinarith
        exact (fits_of_lt_pow (k := 3) (n := s) hcube).mono
          ((logWidth_mono le_rfl (by rw [← hlen_y]; exact Nat.le_add_left _ _)).trans hw)
      let e1 := d_scan.set 8 (m * m)
      let e2 := e1.set 8 (m * m + m)
      let e3 := e2.set 8 (m * m + m + 1)
      have hchk : ExecWithin w syntheticCheckLen d_scan e3 3 := by
        have c1 : ExecWithin w (.op (.bin .mul 8 4 4)) d_scan e1 1 :=
          ExecWithin.bin (show m * m < 2 ^ w by omega)
        have c2 : ExecWithin w (.op (.bin .add 8 8 4)) e1 e2 1 := by
          have hf2 : Fits w (e1.regs 8 + e1.regs 4) := by
            change e1.regs 8 + e1.regs 4 < 2 ^ w
            simp only [e1, Data.set_regs, Function.update_self,
              Function.update_of_ne (by decide : (4 : Fin 10) ≠ 8)]
            change m * m + m < 2 ^ w
            omega
          simpa [e2, e1, m] using ExecWithin.bin (w := w) (x := e1) (f := .add) (d := 8) (i := 8)
            (j := 4) hf2
        have c3 : ExecWithin w (.op (.bin .add 8 8 2)) e2 e3 1 := by
          have hf3 : Fits w (e2.regs 8 + e2.regs 2) := by
            change e2.regs 8 + e2.regs 2 < 2 ^ w
            simp only [e2, e1, Data.set_regs, Function.update_self,
              Function.update_of_ne (by decide : (2 : Fin 10) ≠ 8), hs2]
            omega
          simpa [e3, e2, e1, hs2, m] using ExecWithin.bin (w := w) (x := e2) (f := .add) (d := 8)
            (i := 8) (j := 2) hf3
        exact c1.seq (c2.seq c3)
      obtain ⟨t_chk, ht_chk, hex_chk⟩ := hchk
      have hchk_o : OracleExec w (oracleOf P encBits) (.ofCode syntheticCheckLen) d_scan e3 t_chk []
        :=
        oracleExec_of_exec hex_chk (by simp [syntheticCheckLen, Code.IsRandFree])
      by_cases hlen_eq : m * m + m + 1 = s
      · have hc2 : (Cond.eq 8 0).Holds e3 := by simp [Cond.Holds, e3, e2, e1, hs0, hlen_eq]
        have hbl : Fits w (e3.regs 2 + e3.regs 4) := by
          simp only [e3, e2, e1, Data.set_regs, Function.update_of_ne (by decide : (2 : Fin 10) ≠
            8),
            Function.update_of_ne (by decide : (4 : Fin 10) ≠ 8), hs2, m]
          exact Fits.of_le hi.1 (by omega)
        have hq_ex := OracleExec.query (B := .standard) (w := w) (O := oracleOf P encBits)
          (dst := 9) (base := 2) (len := 4) (x := e3) h1_fits hbl
        have hq_val : ((List.range (e3.regs 4)).map fun i => e3.mem (e3.regs 2 + i)) =
            encBits (y.take m) := by
          have he3_2 : e3.regs 2 = 1 := by simp [e3, e2, e1, hs2]
          have he3_4 : e3.regs 4 = m := by simp [e3, e2, e1, m]
          rw [he3_2, he3_4]
          refine List.ext_getElem (by simp [List.length_take]; omega) fun i hi₁ hi₂ => ?_
          have hil : i < m := by simpa using hi₁
          simp only [List.getElem_map, List.getElem_range, e3, e2, e1, Data.set_mem, hsm, x0,
            show 1 + i = i + 1 by omega, Data.init_mem_succ, encBits_apply,
            List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem (lt_trans hil hm_lt), Option.map_some, Option.getD_some,
            List.getElem_take]
        refine ⟨_, _, _, OracleExec.seq hex_sc (OracleExec.branch_pos hc1
          (OracleExec.seq hchk_o (OracleExec.branch_pos hc2 hq_ex))), ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Data.set_regs, Function.update_self]; cases oracleOf P encBits _ <;> decide
        · simp only [Data.set_regs, Function.update_self, hq_val]
          have hmem_iff := mem_syntheticP'_iff_take (P := P) hm_lt hy_m hy_hi
          have : (oracleOf P encBits (encBits (y.take m))).toNat = 1 ↔
              oracleOf P encBits (encBits (y.take m)) = true := by
            cases oracleOf P encBits (encBits (y.take m)) <;> simp
          rw [this, oracleOf_enc, ← hmem_iff]
          exact ⟨fun h => ⟨by change s = m + 1 + m ^ 2; rw [← hlen_eq]; ring, h⟩, fun h => h.2⟩
        · intro qi hqi
          simp only [List.nil_append] at hqi
          rw [List.mem_singleton] at hqi
          subst hqi; rw [hq_val]; exact ⟨y.take m, rfl⟩
        · have he3_4 : e3.regs 4 = m := by simp [e3, e2, e1, m]
          have htime_nat : t_sc + (t_chk + (e3.regs 4 + 1 + 1) + 1) ≤ 10 * s + 25 := by
            rw [he3_4]; omega
          have hs_real : (s : ℝ) ≤ (s : ℝ) ^ (3 / 2 * (1 - min (1 / 3 : ℝ) ε)) + 1 := by
            rcases Nat.eq_zero_or_pos s with hs0' | hpos
            · rw [hs0', Nat.cast_zero]; positivity
            · have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hpos
              have hexp : (1 : ℝ) ≤ (3 / 2 : ℝ) * (1 - min (1 / 3 : ℝ) ε) := by
                have := min_le_left (1 / 3 : ℝ) ε; linarith
              calc (s : ℝ) = (s : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ (s : ℝ) ^ ((3 / 2 : ℝ) * (1 - min (1 / 3 : ℝ) ε)) :=
                    Real.rpow_le_rpow_of_exponent_le hs1 hexp
                _ ≤ _ := by linarith
          calc ((t_sc + (t_chk + (e3.regs 4 + 1 + 1) + 1) : ℕ) : ℝ)
              ≤ (10 * s + 25 : ℕ) := by exact_mod_cast htime_nat
            _ = 10 * (s : ℝ) + 25 := by push_cast; ring
            _ ≤ 35 * ((s : ℝ) ^ (3 / 2 : ℝ)) ^ (1 - min (1 / 3 : ℝ) ε) + 35 := by
                rw [← Real.rpow_mul (Nat.cast_nonneg s)]
                have hnn : 0 ≤ (s : ℝ) ^ (3 / 2 * (1 - min (1 / 3 : ℝ) ε)) := by positivity
                linarith
        · simp only [List.nil_append, List.map_singleton, List.sum_singleton, hq_val,
            querySize_enc, List.length_take, Nat.min_eq_left (le_of_lt hm_lt)]
          have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (show 1 ≤ s by omega)
          have hms : (m : ℝ) ^ (3 : ℝ) ≤ (s : ℝ) ^ (3 / 2 : ℝ) := by
            have hm2 : (m : ℝ) ^ (2 : ℕ) ≤ (s : ℝ) := by
              exact_mod_cast (show m ^ 2 ≤ s by nlinarith)
            calc (m : ℝ) ^ (3 : ℝ) = ((m : ℝ) ^ (2 : ℝ)) ^ (3 / 2 : ℝ) := by
                  rw [← Real.rpow_mul (Nat.cast_nonneg m)]; norm_num
              _ ≤ (s : ℝ) ^ (3 / 2 : ℝ) := by
                  refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
                  simpa [Real.rpow_two] using hm2
          have h2 : ((s : ℝ) ^ (3 / 2 : ℝ)) ^ (1 - ε) ≤
              35 * ((s : ℝ) ^ (3 / 2 : ℝ)) ^ (1 - min (1 / 3 : ℝ) ε) + 35 := by
            have hge1 : (1 : ℝ) ≤ (s : ℝ) ^ (3 / 2 : ℝ) := Real.one_le_rpow hs1 (by norm_num)
            have hexp : 1 - ε ≤ 1 - min (1 / 3 : ℝ) ε := by
              have := min_le_right (1 / 3 : ℝ) ε; linarith
            have := Real.rpow_le_rpow_of_exponent_le hge1 hexp
            have hnn := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ) ^ (3 / 2 : ℝ))
              (1 - min (1 / 3 : ℝ) ε)
            linarith
          by_cases h1ε : 0 ≤ 1 - ε
          · exact (Real.rpow_le_rpow (by positivity) hms h1ε).trans h2
          · rcases Nat.eq_zero_or_pos m with hm0 | hm1
            · rw [hm0, Nat.cast_zero, Real.zero_rpow (by norm_num),
                Real.zero_rpow (by linarith)]
              positivity
            · have hm1r : (1 : ℝ) ≤ (m : ℝ) ^ (3 : ℝ) := by
                have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
                calc (1 : ℝ) = (1 : ℝ) ^ (3 : ℝ) := by norm_num
                  _ ≤ (m : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow (by norm_num) this (by norm_num)
              have hle1 : ((m : ℝ) ^ (3 : ℝ)) ^ (1 - ε) ≤ 1 :=
                Real.rpow_le_one_of_one_le_of_nonpos hm1r (by linarith)
              have hnn : 0 ≤ ((s : ℝ) ^ (3 / 2 : ℝ)) ^ (1 - min (1 / 3 : ℝ) ε) :=
                Real.rpow_nonneg (by positivity) _
              linarith
      · have hc2 : ¬(Cond.eq 8 0).Holds e3 := by simp [Cond.Holds, e3, e2, e1, hs0, hlen_eq]
        refine ⟨_, _, _, OracleExec.seq hex_sc (OracleExec.branch_pos hc1
          (OracleExec.seq hchk_o
            (OracleExec.branch_neg hc2 (OracleExec.op (o := .const 9 0)
              (Data.put_of_fits (fits_zero w)))))),
          by simp [Data.set_regs], ?_, by simp, ?_,
          by simp only [List.append_nil, List.map_nil, List.sum_nil]; positivity⟩
        · simp only [Data.set_regs, Function.update_self, zero_ne_one, false_iff]
          intro hmem
          have hmem' := (mem_syntheticP'_iff_take (P := P) hm_lt hy_m hy_hi).mpr hmem
          have hsq : m ^ 2 = m * m := by ring
          exact hlen_eq (by change m * m + m + 1 = y.length; omega)
        · have htime_nat : t_sc + (t_chk + (1 + 2) + 1) ≤ 10 * s + 25 := by omega
          have hs_real : (s : ℝ) ≤ (s : ℝ) ^ (3 / 2 * (1 - min (1 / 3 : ℝ) ε)) + 1 := by
            rcases Nat.eq_zero_or_pos s with hs0' | hpos
            · rw [hs0', Nat.cast_zero]; positivity
            · have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hpos
              have hexp : (1 : ℝ) ≤ (3 / 2 : ℝ) * (1 - min (1 / 3 : ℝ) ε) := by
                have := min_le_left (1 / 3 : ℝ) ε; linarith
              calc (s : ℝ) = (s : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ (s : ℝ) ^ ((3 / 2 : ℝ) * (1 - min (1 / 3 : ℝ) ε)) :=
                    Real.rpow_le_rpow_of_exponent_le hs1 hexp
                _ ≤ _ := by linarith
          calc ((t_sc + (t_chk + (1 + 2) + 1) : ℕ) : ℝ)
              ≤ (10 * s + 25 : ℕ) := by exact_mod_cast htime_nat
            _ = 10 * (s : ℝ) + 25 := by push_cast; ring
            _ ≤ 35 * ((s : ℝ) ^ (3 / 2 : ℝ)) ^ (1 - min (1 / 3 : ℝ) ε) + 35 := by
                rw [← Real.rpow_mul (Nat.cast_nonneg s)]
                have hnn : 0 ≤ (s : ℝ) ^ (3 / 2 * (1 - min (1 / 3 : ℝ) ε)) := by positivity
                linarith
    · have h0 : d_scan.regs 3 = 0 := by omega
      have hc1 : ¬(Cond.eq 3 2).Holds d_scan := by simp [Cond.Holds, h0, hs2]
      refine ⟨_, _, _, OracleExec.seq hex_sc
        (OracleExec.branch_neg hc1 (OracleExec.op (o := .const 9 0)
          (Data.put_of_fits (fits_zero w)))),
        by simp [Data.set_regs], ?_, by simp, ?_,
        by simp only [List.append_nil, List.map_nil, List.sum_nil]; positivity⟩
      · simp only [Data.set_regs, Function.update_self, zero_ne_one, false_iff]
        rintro ⟨x, -, rfl⟩
        have hfalse : (syntheticPad x)[x.length]'(by rw [length_syntheticPad]; omega) = false := by
          simp only [syntheticPad, List.getElem_append_right le_rfl, Nat.sub_self,
            List.getElem_cons_zero]
        have htrue := hs_none h0 x.length (by rw [length_syntheticPad]; omega)
          (by change x.length < (syntheticPad x).length; rw [length_syntheticPad]; omega)
        rw [hfalse] at htrue; cases htrue
      · have htime_nat : t_sc + (1 + 2) ≤ 10 * s + 25 := by omega
        have hs_real : (s : ℝ) ≤ (s : ℝ) ^ (3 / 2 * (1 - min (1 / 3 : ℝ) ε)) + 1 := by
          rcases Nat.eq_zero_or_pos s with hs0' | hpos
          · rw [hs0', Nat.cast_zero]; positivity
          · have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hpos
            have hexp : (1 : ℝ) ≤ (3 / 2 : ℝ) * (1 - min (1 / 3 : ℝ) ε) := by
              have := min_le_left (1 / 3 : ℝ) ε; linarith
            calc (s : ℝ) = (s : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
              _ ≤ (s : ℝ) ^ ((3 / 2 : ℝ) * (1 - min (1 / 3 : ℝ) ε)) :=
                  Real.rpow_le_rpow_of_exponent_le hs1 hexp
              _ ≤ _ := by linarith
        calc ((t_sc + (1 + 2) : ℕ) : ℝ)
            ≤ (10 * s + 25 : ℕ) := by exact_mod_cast htime_nat
          _ = 10 * (s : ℝ) + 25 := by push_cast; ring
          _ ≤ 35 * ((s : ℝ) ^ (3 / 2 : ℝ)) ^ (1 - min (1 / 3 : ℝ) ε) + 35 := by
              rw [← Real.rpow_mul (Nat.cast_nonneg s)]
              have hnn : 0 ≤ (s : ℝ) ^ (3 / 2 * (1 - min (1 / 3 : ℝ) ε)) := by positivity
              linarith

end CslibFrontier.Complexity.FineGrained
