/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.Call
import Mathlib.Tactic.Linarith

/-!
# Oracle Word RAM and Memory-Isolated Compilation

This module extends `Cslib.WordRAM` with deterministic adaptive oracle queries (`OracleCode`,
`OracleExec`) and constructs exact-cost, memory-isolated compilation primitives into pure
`Cslib.WordRAM.Code .standard`:

1. **Oracle Word RAM (`OracleCode`, `OracleExec`)**: structured word-RAM programs augmented with
   `query dst base len`, which submits the word array `mem[base .. base + len)` to an oracle
   `O : List ℕ → Bool`, writes `(O q).toNat` to `dst`, charges `len + 1` instructions, and records
   `q` in the adaptive query trace.
2. **Memory locality (`OracleExec.agree_lt`, `exec_agree_lt`)**: executions at width `w` with
   `w`-bounded inputs depend only on, and modify only, memory addresses below `2 ^ w`.
3. **Inline oracle compilation (`compileOracle`)**: replaces every `query` instruction with a call
   to a pure `WordRAM.Code` subroutine operating in disjoint registers and memory `[H, 2^W)`, while
   the outer oracle program runs unmodified in `[0, H)`.

All results are proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

public section

namespace CslibFrontier.WordRAM

open Cslib.WordRAM

/-! ### Structured Oracle Word RAM -/

/-- Structured word-RAM programs with deterministic adaptive oracle queries. -/
inductive OracleCode (B : Basis) (r : ℕ) where
  /-- A standard data instruction. -/
  | op (o : Op B r)
  /-- Sequential composition `c₁; c₂`. -/
  | seq (c₁ c₂ : OracleCode B r)
  /-- Conditional branch on `c`. -/
  | branch (c : Cond r) (pos neg : OracleCode B r)
  /-- While loop on `c`. -/
  | loop (c : Cond r) (body : OracleCode B r)
  /-- Submit the word array `mem[base .. base + len)` to the oracle and store the 0/1 reply in
  register `dst`. -/
  | query (dst base len : Fin r)
  deriving DecidableEq

namespace OracleCode

variable {B : Basis} {r r' : ℕ}

/-- Whether an oracle program reads the word size `w`. -/
@[expose]
def ReadsWidth : OracleCode B r → Prop
  | .op o => o.ReadsWidth
  | .seq c₁ c₂ => c₁.ReadsWidth ∨ c₂.ReadsWidth
  | .branch _ pos neg => pos.ReadsWidth ∨ neg.ReadsWidth
  | .loop _ body => body.ReadsWidth
  | .query _ _ _ => False

instance decidableReadsWidth : (c : OracleCode B r) → Decidable c.ReadsWidth
  | .op o => inferInstanceAs (Decidable o.ReadsWidth)
  | .seq c₁ c₂ =>
    have := c₁.decidableReadsWidth
    have := c₂.decidableReadsWidth
    inferInstanceAs (Decidable (c₁.ReadsWidth ∨ c₂.ReadsWidth))
  | .branch _ pos neg =>
    have := pos.decidableReadsWidth
    have := neg.decidableReadsWidth
    inferInstanceAs (Decidable (pos.ReadsWidth ∨ neg.ReadsWidth))
  | .loop _ body => body.decidableReadsWidth
  | .query _ _ _ => isFalse id

/-- Compiled size of an oracle program. -/
@[simp]
def size : OracleCode B r → ℕ
  | .op _ => 1
  | .seq c₁ c₂ => c₁.size + c₂.size
  | .branch _ pos neg => neg.size + pos.size + 2
  | .loop _ body => body.size + 3
  | .query _ _ _ => 1

/-- Embed a `rand`-free structured `WordRAM.Code` into `OracleCode`. -/
def ofCode : Code B r → OracleCode B r
  | .op o => .op o
  | .seq c₁ c₂ => .seq (ofCode c₁) (ofCode c₂)
  | .branch c pos neg => .branch c (ofCode pos) (ofCode neg)
  | .loop c body => .loop c (ofCode body)
  | .rand dst _ => .op (.copy dst dst)

/-- `ofCode` preserves `¬ReadsWidth`. -/
theorem readsWidth_ofCode (c : Code B r) : (ofCode c).ReadsWidth ↔ c.ReadsWidth := by
  induction c with
  | op o => simp [ofCode, ReadsWidth, Code.ReadsWidth]
  | seq c₁ c₂ ih₁ ih₂ => simp [ofCode, ReadsWidth, Code.ReadsWidth, ih₁, ih₂]
  | branch _ pos neg ihp ihn => simp [ofCode, ReadsWidth, Code.ReadsWidth, ihp, ihn]
  | loop _ body ih => simp [ofCode, ReadsWidth, Code.ReadsWidth, ih]
  | rand _ _ => simp [ofCode, ReadsWidth, Code.ReadsWidth, Op.ReadsWidth]

end OracleCode

/-- Big-step operational semantics of `OracleCode` against a deterministic oracle
`O : List ℕ → Bool`, tracking exact instruction count (charging `len + 1` per query) and the
chronological list of adaptive queries submitted to `O`. -/
inductive OracleExec {B : Basis} {r : ℕ} (w : ℕ) (O : List ℕ → Bool) :
    OracleCode B r → Data r → Data r → ℕ → List (List ℕ) → Prop where
  | op {o : Op B r} {x y : Data r} :
      o.eval w x = some y → OracleExec w O (.op o) x y 1 []
  | seq {c₁ c₂ : OracleCode B r} {x y z : Data r} {m n : ℕ} {qs₁ qs₂ : List (List ℕ)} :
      OracleExec w O c₁ x y m qs₁ → OracleExec w O c₂ y z n qs₂ →
      OracleExec w O (.seq c₁ c₂) x z (m + n) (qs₁ ++ qs₂)
  | branch_pos {c : Cond r} {pos neg : OracleCode B r} {x y : Data r} {n : ℕ}
      {qs : List (List ℕ)} :
      c.Holds x → OracleExec w O pos x y n qs →
      OracleExec w O (.branch c pos neg) x y (n + 1) qs
  | branch_neg {c : Cond r} {pos neg : OracleCode B r} {x y : Data r} {n : ℕ}
      {qs : List (List ℕ)} :
      ¬c.Holds x → OracleExec w O neg x y n qs →
      OracleExec w O (.branch c pos neg) x y (n + 2) qs
  | loop_exit {c : Cond r} {body : OracleCode B r} {x : Data r} :
      ¬c.Holds x → OracleExec w O (.loop c body) x x 2 []
  | loop_iter {c : Cond r} {body : OracleCode B r} {x y z : Data r} {m n : ℕ}
      {qs₁ qs₂ : List (List ℕ)} :
      c.Holds x → OracleExec w O body x y m qs₁ →
      OracleExec w O (.loop c body) y z n qs₂ →
      OracleExec w O (.loop c body) x z (m + n + 2) (qs₁ ++ qs₂)
  | query {dst base len : Fin r} {x : Data r} :
      Fits w 1 → Fits w (x.regs base + x.regs len) →
      OracleExec w O (.query dst base len) x
        (x.set dst (O ((List.range (x.regs len)).map fun i => x.mem (x.regs base + i))).toNat)
        (x.regs len + 1)
        [(List.range (x.regs len)).map fun i => x.mem (x.regs base + i)]

/-- Bounded-time oracle execution. -/
def OracleExecWithin {B : Basis} {r : ℕ} (w : ℕ) (O : List ℕ → Bool) (c : OracleCode B r)
    (x y : Data r) (T : ℕ) (qs : List (List ℕ)) : Prop :=
  ∃ t ≤ T, OracleExec w O c x y t qs

/-- Every `rand`-free `WordRAM.Exec` embeds into `OracleExec` with no queries. -/
theorem oracleExec_of_exec {B : Basis} {r w t : ℕ} {O : List ℕ → Bool} {c : Code B r}
    {x y : Data r} (h : Exec w c x y t) (hrf : c.IsRandFree) :
    OracleExec w O (.ofCode c) x y t [] := by
  induction h with
  | op ho => exact .op ho
  | seq _ _ ih₁ ih₂ =>
    simpa only [OracleCode.ofCode, List.append_nil] using OracleExec.seq (ih₁ hrf.1) (ih₂ hrf.2)
  | branch_pos hc _ ih => exact .branch_pos hc (ih hrf.1)
  | branch_neg hc _ ih => exact .branch_neg hc (ih hrf.2)
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc _ _ ihb ihl =>
    simpa only [OracleCode.ofCode, List.append_nil] using
      OracleExec.loop_iter hc (ihb hrf) (ihl hrf)

/-- A single data instruction preserves `Data.Bounded w`. -/
theorem op_eval_bounded {B : Basis} {r w : ℕ} {o : Op B r} {x y : Data r}
    (hx : x.Bounded w) (h : o.eval w x = some y) : y.Bounded w := by
  cases o with
  | const d v =>
    obtain ⟨hv, rfl⟩ := Data.put_eq_some.mp h
    refine ⟨fun i => ?_, hx.2⟩
    by_cases hi : i = d
    · subst hi; simpa [Data.set_regs] using hv
    · simpa [Data.set_regs, Function.update_of_ne hi] using hx.1 i
  | copy d s =>
    cases h
    refine ⟨fun i => ?_, hx.2⟩
    by_cases hi : i = d
    · subst hi; simpa [Data.set_regs] using hx.1 s
    · simpa [Data.set_regs, Function.update_of_ne hi] using hx.1 i
  | alu f d args =>
    obtain ⟨v, _, hv, rfl⟩ := Op.eval_alu_eq_some.mp h
    refine ⟨fun i => ?_, hx.2⟩
    by_cases hi : i = d
    · subst hi; simpa [Data.set_regs] using hv
    · simpa [Data.set_regs, Function.update_of_ne hi] using hx.1 i
  | load d a =>
    cases h
    refine ⟨fun i => ?_, hx.2⟩
    by_cases hi : i = d
    · subst hi; simpa [Data.set_regs] using hx.2 (x.regs a)
    · simpa [Data.set_regs, Function.update_of_ne hi] using hx.1 i
  | store a s =>
    cases h
    refine ⟨hx.1, fun addr => ?_⟩
    by_cases ha : addr = x.regs a
    · subst ha; simpa [Data.write_mem] using hx.1 s
    · simpa [Data.write_mem, Function.update_of_ne ha] using hx.2 addr

/-- `OracleExec` preserves `Data.Bounded w`. -/
theorem OracleExec.bounded {B : Basis} {r w t : ℕ} {O : List ℕ → Bool}
    {c : OracleCode B r} {x y : Data r} {qs : List (List ℕ)}
    (hx : x.Bounded w) (h : OracleExec w O c x y t qs) : y.Bounded w := by
  induction h with
  | op ho => exact op_eval_bounded hx ho
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hx)
  | branch_pos _ _ ih => exact ih hx
  | branch_neg _ _ ih => exact ih hx
  | loop_exit _ => exact hx
  | loop_iter _ _ _ ihb ihl => exact ihl (ihb hx)
  | @query dst _ _ _ h1 _ =>
    refine ⟨fun i => ?_, hx.2⟩
    by_cases hi : i = dst
    · subst hi
      rw [Data.set_regs, Function.update_self]
      cases O _
      · exact Fits.of_le h1 (by decide)
      · exact h1
    · rw [Data.set_regs, Function.update_of_ne hi]
      exact hx.1 i

/-- Determinism of `OracleExec`. -/
theorem OracleExec.unique {B : Basis} {r w t₁ t₂ : ℕ} {O : List ℕ → Bool}
    {c : OracleCode B r} {x y₁ y₂ : Data r} {qs₁ qs₂ : List (List ℕ)}
    (h₁ : OracleExec w O c x y₁ t₁ qs₁) (h₂ : OracleExec w O c x y₂ t₂ qs₂) :
    y₁ = y₂ ∧ t₁ = t₂ ∧ qs₁ = qs₂ := by
  induction h₁ generalizing y₂ t₂ qs₂ with
  | op ho =>
    cases h₂ with | op ho' =>
      rw [ho] at ho'
      exact ⟨Option.some.inj ho', rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with | seq h₂a h₂b =>
      obtain ⟨rfl, rfl, rfl⟩ := ih₁ h₂a
      obtain ⟨rfl, rfl, rfl⟩ := ih₂ h₂b
      exact ⟨rfl, rfl, rfl⟩
  | branch_pos hc _ ih =>
    cases h₂ with
    | branch_pos _ h₂' =>
      obtain ⟨rfl, rfl, rfl⟩ := ih h₂'
      exact ⟨rfl, rfl, rfl⟩
    | branch_neg hnc _ => exact (hnc hc).elim
  | branch_neg hnc _ ih =>
    cases h₂ with
    | branch_pos hc _ => exact (hnc hc).elim
    | branch_neg _ h₂' =>
      obtain ⟨rfl, rfl, rfl⟩ := ih h₂'
      exact ⟨rfl, rfl, rfl⟩
  | loop_exit hnc =>
    cases h₂ with
    | loop_exit _ => exact ⟨rfl, rfl, rfl⟩
    | loop_iter hc _ _ => exact (hnc hc).elim
  | loop_iter hc _ _ ihb ihl =>
    cases h₂ with
    | loop_exit hnc => exact (hnc hc).elim
    | loop_iter _ h₂b h₂l =>
      obtain ⟨rfl, rfl, rfl⟩ := ihb h₂b
      obtain ⟨rfl, rfl, rfl⟩ := ihl h₂l
      exact ⟨rfl, rfl, rfl⟩
  | query _ _ =>
    cases h₂ with | query _ _ => exact ⟨rfl, rfl, rfl⟩

/-- Every `OracleExec` run satisfies `(qs.map (fun q => q.length + 1)).sum ≤ t`. -/
theorem OracleExec.sum_query_length_le {B : Basis} {r w t : ℕ} {O : List ℕ → Bool}
    {c : OracleCode B r} {x y : Data r} {qs : List (List ℕ)}
    (h : OracleExec w O c x y t qs) :
    (qs.map fun q => q.length + 1).sum ≤ t := by
  induction h with
  | op _ => simp
  | seq _ _ ih₁ ih₂ => simp only [List.map_append, List.sum_append]; omega
  | branch_pos _ _ ih => omega
  | branch_neg _ _ ih => omega
  | loop_exit _ => simp
  | loop_iter _ _ _ ihb ihl => simp only [List.map_append, List.sum_append]; omega
  | query _ _ => simp

/-- Every `OracleExec` run makes at most `t` oracle queries. -/
theorem OracleExec.length_queries_le {B : Basis} {r w t : ℕ} {O : List ℕ → Bool}
    {c : OracleCode B r} {x y : Data r} {qs : List (List ℕ)}
    (h : OracleExec w O c x y t qs) : qs.length ≤ t := by
  have h2 : ∀ l : List (List ℕ), l.length ≤ (l.map fun q => q.length + 1).sum := by
    intro l
    induction l with
    | nil => simp
    | cons q l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  exact (h2 qs).trans h.sum_query_length_le

/-- Every query emitted during a `w`-bounded `OracleExec` run satisfies `InputFits w q`. -/
theorem OracleExec.inputFits_queries {B : Basis} {r w t : ℕ} {O : List ℕ → Bool}
    {c : OracleCode B r} {x y : Data r} {qs : List (List ℕ)}
    (hx : x.Bounded w) (h : OracleExec w O c x y t qs) :
    ∀ q ∈ qs, InputFits w q := by
  induction h with
  | op _ => simp
  | seq h₁ _ ih₁ ih₂ =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ih₁ hx q hq
    · exact ih₂ (h₁.bounded hx) q hq
  | branch_pos _ _ ih => exact ih hx
  | branch_neg _ _ ih => exact ih hx
  | loop_exit _ => simp
  | loop_iter _ hb _ ihb ihl =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ihb hx q hq
    · exact ihl (hb.bounded hx) q hq
  | query _ hbl =>
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    refine ⟨?_, ?_⟩
    · simp only [List.length_map, List.length_range]
      exact Fits.of_le hbl (Nat.le_add_left _ _)
    · intro u hu
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hu
      exact hx.2 _

/-- Width monotonicity for `OracleExec` on programs that do not read the word size. -/
theorem OracleExec.mono_width {B : Basis} {r w w' t : ℕ} {O : List ℕ → Bool}
    {c : OracleCode B r} {x y : Data r} {qs : List (List ℕ)}
    (hc : ¬c.ReadsWidth) (hw : w ≤ w') (h : OracleExec w O c x y t qs) :
    OracleExec w' O c x y t qs := by
  induction h with
  | op ho =>
    exact .op (Op.eval_mono_width hc ho hw)
  | seq _ _ ih₁ ih₂ =>
    exact .seq (ih₁ (fun h => hc (Or.inl h))) (ih₂ (fun h => hc (Or.inr h)))
  | branch_pos hcond _ ih =>
    exact .branch_pos hcond (ih (fun h => hc (Or.inl h)))
  | branch_neg hcond _ ih =>
    exact .branch_neg hcond (ih (fun h => hc (Or.inr h)))
  | loop_exit hcond => exact .loop_exit hcond
  | loop_iter hcond _ _ ihb ihl =>
    exact .loop_iter hcond (ihb hc) (ihl hc)
  | query h1 hbl =>
    exact .query (h1.mono hw) (hbl.mono hw)

/-- Oracle agreement on all queries made during a run preserves the run. -/
theorem OracleExec.congr_oracle {B : Basis} {r w t : ℕ} {O₁ O₂ : List ℕ → Bool}
    {c : OracleCode B r} {x y : Data r} {qs : List (List ℕ)}
    (h : OracleExec w O₁ c x y t qs) (hO : ∀ q ∈ qs, O₁ q = O₂ q) :
    OracleExec w O₂ c x y t qs := by
  induction h with
  | op ho => exact .op ho
  | seq _ _ ih₁ ih₂ =>
    exact .seq (ih₁ fun q hq => hO q (List.mem_append_left _ hq))
      (ih₂ fun q hq => hO q (List.mem_append_right _ hq))
  | branch_pos hc _ ih => exact .branch_pos hc (ih hO)
  | branch_neg hc _ ih => exact .branch_neg hc (ih hO)
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc _ _ ihb ihl =>
    exact .loop_iter hc (ihb fun q hq => hO q (List.mem_append_left _ hq))
      (ihl fun q hq => hO q (List.mem_append_right _ hq))
  | query h1 hbl =>
    have hq := hO _ (List.mem_singleton_self _)
    rw [hq]
    exact .query h1 hbl

/-! ### Memory locality below `2 ^ w` -/

/-- A single data instruction at width `w` on `w`-bounded data touches only addresses `< 2^w`. -/
theorem op_eval_agree_lt {B : Basis} {r w : ℕ} {o : Op B r} {x₁ x₂ y₁ : Data r}
    (hx : x₁.Bounded w) (hregs : x₂.regs = x₁.regs)
    (hmem : ∀ a < 2 ^ w, x₂.mem a = x₁.mem a) (h : o.eval w x₁ = some y₁) :
    ∃ y₂ : Data r, o.eval w x₂ = some y₂ ∧ y₂.regs = y₁.regs ∧
      (∀ a < 2 ^ w, y₂.mem a = y₁.mem a) ∧ (∀ a, 2 ^ w ≤ a → y₂.mem a = x₂.mem a) := by
  cases o with
  | const d v =>
    obtain ⟨hv, rfl⟩ := Data.put_eq_some.mp h
    refine ⟨x₂.set d v, ?_, ?_, hmem, fun _ _ => rfl⟩
    · simp [Op.eval, Data.put, hv]
    · simp [Data.set_regs, hregs]
  | copy d s =>
    cases h
    refine ⟨x₂.set d (x₂.regs s), rfl, ?_, hmem, fun _ _ => rfl⟩
    simp [Data.set_regs, hregs]
  | alu f d args =>
    obtain ⟨v, hval, hv, rfl⟩ := Op.eval_alu_eq_some.mp h
    refine ⟨x₂.set d v, ?_, ?_, hmem, fun _ _ => rfl⟩
    · rw [Op.eval_alu_eq_some]
      refine ⟨v, ?_, hv, rfl⟩
      simpa only [Function.comp_def, hregs] using hval
    · simp [Data.set_regs, hregs]
  | load d a =>
    cases h
    have ha : x₁.regs a < 2 ^ w := hx.1 a
    refine ⟨x₂.set d (x₂.mem (x₂.regs a)), rfl, ?_, hmem, fun _ _ => rfl⟩
    simp [Data.set_regs, hregs, hmem _ ha]
  | store a s =>
    cases h
    have ha : x₁.regs a < 2 ^ w := hx.1 a
    refine ⟨x₂.write (x₂.regs a) (x₂.regs s), rfl, hregs, fun b hb => ?_, fun b hb => ?_⟩
    · simp only [Data.write_mem, hregs]
      by_cases hba : b = x₁.regs a
      · subst hba; simp
      · simp [Function.update_of_ne hba, hmem b hb]
    · simp only [Data.write_mem, hregs]
      have hba : b ≠ x₁.regs a := by omega
      simp [Function.update_of_ne hba]

private theorem cond_holds_of_regs_eq {r : ℕ} {cond : Cond r} {x₁ x₂ : Data r}
    (hr : x₂.regs = x₁.regs) : cond.Holds x₂ ↔ cond.Holds x₁ := by
  cases cond <;> simp [Cond.Holds, hr]

/-- **Memory locality for `OracleExec`**: an execution at width `w` from `w`-bounded data reads and
writes only addresses `< 2 ^ w`, leaving all addresses `≥ 2 ^ w` completely untouched. -/
theorem OracleExec.agree_lt {B : Basis} {r w t : ℕ} {O : List ℕ → Bool}
    {c : OracleCode B r} {x₁ x₂ y₁ : Data r} {qs : List (List ℕ)}
    (hx : x₁.Bounded w) (hregs : x₂.regs = x₁.regs)
    (hmem : ∀ a < 2 ^ w, x₂.mem a = x₁.mem a) (h : OracleExec w O c x₁ y₁ t qs) :
    ∃ y₂ : Data r, OracleExec w O c x₂ y₂ t qs ∧ y₂.regs = y₁.regs ∧
      (∀ a < 2 ^ w, y₂.mem a = y₁.mem a) ∧ (∀ a, 2 ^ w ≤ a → y₂.mem a = x₂.mem a) := by
  induction h generalizing x₂ with
  | op ho =>
    obtain ⟨y₂, ho₂, hr, hm, hhi⟩ := op_eval_agree_lt hx hregs hmem ho
    exact ⟨y₂, .op ho₂, hr, hm, hhi⟩
  | seq h₁ _ ih₁ ih₂ =>
    obtain ⟨y₂, hy₂, hr₁, hm₁, hhi₁⟩ := ih₁ hx hregs hmem
    obtain ⟨z₂, hz₂, hr₂, hm₂, hhi₂⟩ := ih₂ (h₁.bounded hx) hr₁ hm₁
    exact ⟨z₂, .seq hy₂ hz₂, hr₂, hm₂, fun a ha => (hhi₂ a ha).trans (hhi₁ a ha)⟩
  | branch_pos hc _ ih =>
    obtain ⟨y₂, hy₂, hr, hm, hhi⟩ := ih hx hregs hmem
    exact ⟨y₂, .branch_pos ((cond_holds_of_regs_eq hregs).mpr hc) hy₂, hr, hm, hhi⟩
  | branch_neg hnc _ ih =>
    obtain ⟨y₂, hy₂, hr, hm, hhi⟩ := ih hx hregs hmem
    exact ⟨y₂, .branch_neg (fun hc => hnc ((cond_holds_of_regs_eq hregs).mp hc)) hy₂, hr, hm, hhi⟩
  | loop_exit hnc =>
    exact ⟨x₂, .loop_exit (fun hc => hnc ((cond_holds_of_regs_eq hregs).mp hc)),
      hregs, hmem, fun _ _ => rfl⟩
  | loop_iter hc hb _ ihb ihl =>
    obtain ⟨y₂, hy₂, hr₁, hm₁, hhi₁⟩ := ihb hx hregs hmem
    obtain ⟨z₂, hz₂, hr₂, hm₂, hhi₂⟩ := ihl (hb.bounded hx) hr₁ hm₁
    exact ⟨z₂, .loop_iter ((cond_holds_of_regs_eq hregs).mpr hc) hy₂ hz₂,
      hr₂, hm₂, fun a ha => (hhi₂ a ha).trans (hhi₁ a ha)⟩
  | @query dst base len x₁' h1 hbl =>
    have hq_eq : ((List.range (x₂.regs len)).map fun i => x₂.mem (x₂.regs base + i)) =
        ((List.range (x₁'.regs len)).map fun i => x₁'.mem (x₁'.regs base + i)) := by
      rw [hregs]
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      change x₁'.regs base + x₁'.regs len < 2 ^ w at hbl
      exact hmem _ (by omega)
    have hbl₂ : Fits w (x₂.regs base + x₂.regs len) := by rw [hregs]; exact hbl
    refine ⟨x₂.set dst (O ((List.range (x₂.regs len)).map fun i =>
        x₂.mem (x₂.regs base + i))).toNat, ?_, ?_, hmem, fun _ _ => rfl⟩
    · rw [← hq_eq, ← hregs]
      exact .query h1 hbl₂
    · rw [Data.set_regs, Data.set_regs, hq_eq, hregs]

/-- **Memory locality for pure `WordRAM.Code`**: a `rand`-free execution at width `w` from
`w`-bounded data reads and writes only addresses `< 2 ^ w`. -/
theorem exec_agree_lt {B : Basis} {r w t : ℕ} {c : Code B r} {x₁ x₂ y₁ : Data r}
    (hx : x₁.Bounded w) (hrf : c.IsRandFree) (hregs : x₂.regs = x₁.regs)
    (hmem : ∀ a < 2 ^ w, x₂.mem a = x₁.mem a) (h : Exec w c x₁ y₁ t) :
    ∃ y₂ : Data r, Exec w c x₂ y₂ t ∧ y₂.regs = y₁.regs ∧
      (∀ a < 2 ^ w, y₂.mem a = y₁.mem a) ∧ (∀ a, 2 ^ w ≤ a → y₂.mem a = x₂.mem a) := by
  induction h generalizing x₂ with
  | op ho =>
    obtain ⟨y₂, ho₂, hr, hm, hhi⟩ := op_eval_agree_lt hx hregs hmem ho
    exact ⟨y₂, .op ho₂, hr, hm, hhi⟩
  | seq h₁ _ ih₁ ih₂ =>
    obtain ⟨y₂, hy₂, hr₁, hm₁, hhi₁⟩ := ih₁ hx hrf.1 hregs hmem
    obtain ⟨z₂, hz₂, hr₂, hm₂, hhi₂⟩ := ih₂ (h₁.bounded hx) hrf.2 hr₁ hm₁
    exact ⟨z₂, .seq hy₂ hz₂, hr₂, hm₂, fun a ha => (hhi₂ a ha).trans (hhi₁ a ha)⟩
  | branch_pos hc _ ih =>
    obtain ⟨y₂, hy₂, hr, hm, hhi⟩ := ih hx hrf.1 hregs hmem
    exact ⟨y₂, .branch_pos ((cond_holds_of_regs_eq hregs).mpr hc) hy₂, hr, hm, hhi⟩
  | branch_neg hnc _ ih =>
    obtain ⟨y₂, hy₂, hr, hm, hhi⟩ := ih hx hrf.2 hregs hmem
    exact ⟨y₂, .branch_neg (fun hc => hnc ((cond_holds_of_regs_eq hregs).mp hc)) hy₂, hr, hm, hhi⟩
  | loop_exit hnc =>
    exact ⟨x₂, .loop_exit (fun hc => hnc ((cond_holds_of_regs_eq hregs).mp hc)),
      hregs, hmem, fun _ _ => rfl⟩
  | loop_iter hc hb _ ihb ihl =>
    obtain ⟨y₂, hy₂, hr₁, hm₁, hhi₁⟩ := ihb hx hrf hregs hmem
    obtain ⟨z₂, hz₂, hr₂, hm₂, hhi₂⟩ := ihl (hb.bounded hx) hrf hr₁ hm₁
    exact ⟨z₂, .loop_iter ((cond_holds_of_regs_eq hregs).mpr hc) hy₂ hz₂,
      hr₂, hm₂, fun a ha => (hhi₂ a ha).trans (hhi₁ a ha)⟩

/-! ### Inline Oracle Compilation (`compileOracle`) -/

/-- Caller register embedded into `Fin ((r_c + 1) + r_s)`. -/
abbrev callerReg {r_c r_s : ℕ} (i : Fin r_c) : Fin ((r_c + 1) + r_s) :=
  Fin.castAdd r_s (Fin.castAdd 1 i)

/-- Dedicated register holding the logical word width `w` of the caller inside `compileOracle`. -/
abbrev callerWidthReg {r_c r_s : ℕ} : Fin ((r_c + 1) + r_s) :=
  Fin.castAdd r_s ⟨r_c, by omega⟩

/-- Subroutine register embedded into `Fin ((r_c + 1) + r_s)`. -/
abbrev subReg {r_c r_s : ℕ} (j : Fin r_s) : Fin ((r_c + 1) + r_s) :=
  Fin.natAdd (r_c + 1) j

theorem callerReg_injective {r_c r_s : ℕ} :
    Function.Injective (callerReg (r_c := r_c) (r_s := r_s)) :=
  (Fin.castAdd_injective (r_c + 1) r_s).comp (Fin.castAdd_injective r_c 1)

theorem subReg_injective {r_c r_s : ℕ} :
    Function.Injective (subReg (r_c := r_c) (r_s := r_s)) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [subReg, Fin.val_natAdd] at hv
  exact Fin.ext (by omega)

theorem callerReg_ne_callerWidthReg {r_c r_s : ℕ} (i : Fin r_c) :
    callerReg (r_s := r_s) i ≠ callerWidthReg (r_c := r_c) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [callerReg, callerWidthReg, Fin.val_castAdd] at hv
  omega

theorem callerReg_ne_subReg {r_c r_s : ℕ} (i : Fin r_c) (j : Fin r_s) :
    callerReg (r_s := r_s) i ≠ subReg (r_c := r_c) j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [callerReg, subReg, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem callerWidthReg_ne_subReg {r_c r_s : ℕ} (j : Fin r_s) :
    callerWidthReg (r_c := r_c) (r_s := r_s) ≠ subReg (r_c := r_c) j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [callerWidthReg, subReg, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

/-- Translate a single `Op .standard r_c` for `compileOracle`, routing `.width` to
`callerWidthReg` so the compiled program simulates width `w` inside any larger physical `W`. -/
def compileOp {r_c r_s : ℕ} : Op .standard r_c → Op .standard ((r_c + 1) + r_s)
  | .const d v => .const (callerReg d) v
  | .copy d s => .copy (callerReg d) (callerReg s)
  | .alu .width d _ => .copy (callerReg d) callerWidthReg
  | .alu (.bin f) d args => .alu (.bin f) (callerReg d) (callerReg ∘ args)
  | .load d a => .load (callerReg d) (callerReg a)
  | .store a s => .store (callerReg a) (callerReg s)

/-- Zero out registers `0 .. r - 1` before executing `base`, leaving registers `r .. r + m - 1`
and all of memory untouched. -/
def zeroPrefixRegs {r m : ℕ} (base : Code .standard (r + m)) : Code .standard (r + m) :=
  (List.finRange r).foldr (fun i acc => .seq (.op (.const (Fin.castAdd m i) 0)) acc) base

/-- `zeroPrefixRegs` preserves `IsRandFree`. -/
theorem isRandFree_zeroPrefixRegs {r m : ℕ} {base : Code .standard (r + m)}
    (hbase : base.IsRandFree) : (zeroPrefixRegs base).IsRandFree := by
  unfold zeroPrefixRegs
  induction List.finRange r with
  | nil => exact hbase
  | cons _ _ ih => exact ⟨trivial, ih⟩

/-- Executing `zeroPrefixRegs base` zeroes registers `0 .. r - 1` in `r` instructions and then runs
`base` (leaving registers `r .. r + m - 1` and memory unchanged prior to `base`). -/
theorem zeroPrefixRegs_exec {r m W T : ℕ} {base : Code .standard (r + m)} {x y : Data (r + m)}
    (h : ExecWithin W base ⟨fun k => if k.val < r then 0 else x.regs k, x.mem⟩ y T) :
    ExecWithin W (zeroPrefixRegs base) x y (r + T) := by
  have haux : ∀ (l : List (Fin r)) (s : Data (r + m)),
      ExecWithin W base
        ⟨fun k => if hlt : k.val < r then
            if (⟨k.val, hlt⟩ : Fin r) ∈ l then 0 else s.regs k
          else s.regs k, s.mem⟩ y T →
      ExecWithin W (l.foldr (fun i acc => .seq (.op (.const (Fin.castAdd m i) 0)) acc) base)
        s y (l.length + T) := by
    intro l
    induction l with
    | nil =>
      intro s hs
      simpa only [List.foldr_nil, List.length_nil, Nat.zero_add, List.not_mem_nil,
        ↓reduceIte, dite_eq_ite, ite_self] using hs
    | cons i l ih =>
      intro s hs
      have h1 : ExecWithin W (.op (Op.const (B := .standard) (Fin.castAdd m i) 0))
          s (s.set (Fin.castAdd m i) 0) 1 :=
        ExecWithin.const (fits_zero W)
      have h2 := ih (s.set (Fin.castAdd m i) 0) (by
        convert hs using 2
        · ext k
          by_cases hlt : k.val < r
          · simp only [hlt, ↓reduceDIte, List.mem_cons, Data.set_regs]
            by_cases hk : (⟨k.val, hlt⟩ : Fin r) = i
            · have hkeq : k = Fin.castAdd m i := Fin.ext (by simpa using congrArg Fin.val hk)
              subst hkeq; simp
            · have hkne : k ≠ Fin.castAdd m i := fun heq =>
                hk (Fin.ext (by simpa using congrArg Fin.val heq))
              simp [hk, Function.update_of_ne hkne]
          · have hkne : k ≠ Fin.castAdd m i := fun heq => by
              have := congrArg Fin.val heq; simp at this; omega
            simp [hlt, Data.set_regs, Function.update_of_ne hkne]
        · rfl)
      exact (h1.seq h2).mono (by simp; omega)
  have hmain := haux (List.finRange r) x (by
    convert h using 2
    ext k
    by_cases hlt : k.val < r
    · simp [hlt, List.mem_finRange]
    · simp [hlt])
  simpa only [zeroPrefixRegs, List.length_finRange] using hmain

/-- Compile an oracle program `c` into pure `WordRAM.Code` by replacing every `query dst base len`
with a call to `sub` (which takes `base` in reg `0`, `len` in reg `1`, and writes its 0/1 reply
to reg `2`). Logical `width%` instructions read `callerWidthReg`. -/
def compileOracle {r_c r_s : ℕ} (c : OracleCode .standard r_c)
    (sub : Code .standard (r_s + 3)) : Code .standard ((r_c + 1) + (r_s + 3)) :=
  match c with
  | .op o => .op (compileOp o)
  | .seq c₁ c₂ => .seq (compileOracle c₁ sub) (compileOracle c₂ sub)
  | .branch cond pos neg =>
      .branch (cond.rename callerReg) (compileOracle pos sub) (compileOracle neg sub)
  | .loop cond body => .loop (cond.rename callerReg) (compileOracle body sub)
  | .query dst base len =>
      .seq (.op (.copy (subReg ⟨0, by omega⟩) (callerReg base)))
        (.seq (.op (.copy (subReg ⟨1, by omega⟩) (callerReg len)))
          (.seq (sub.rename subReg)
            (.op (.copy (callerReg dst) (subReg ⟨2, by omega⟩)))))

/-- Renaming preserves `Code.IsRandFree`. -/
theorem isRandFree_rename {B : Basis} {r r' : ℕ} {f : Fin r → Fin r'} {c : Code B r}
    (hc : c.IsRandFree) : (c.rename f).IsRandFree := by
  induction c with
  | op _ => trivial
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hc.1, ih₂ hc.2⟩
  | branch _ _ _ ihp ihn => exact ⟨ihp hc.1, ihn hc.2⟩
  | loop _ _ ih => exact ih hc
  | rand _ _ => exact hc

/-- `compileOracle` produces `rand`-free code whenever `sub` is `rand`-free. -/
theorem isRandFree_compileOracle {r_c r_s : ℕ} (c : OracleCode .standard r_c)
    {sub : Code .standard (r_s + 3)} (hsub : sub.IsRandFree) :
    (compileOracle c sub).IsRandFree := by
  induction c with
  | op _ => trivial
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | branch _ _ _ ihp ihn => exact ⟨ihp, ihn⟩
  | loop _ _ ih => exact ih
  | query _ _ _ => exact ⟨trivial, trivial, isRandFree_rename hsub, trivial⟩

private theorem compileOp_eval {r_c r_s w W : ℕ} {o : Op .standard r_c} {x₁ y₁ : Data r_c}
    {x : Data ((r_c + 1) + r_s)} (hw : w ≤ W) (hx₁ : x₁.Bounded w)
    (hWreg : x.regs callerWidthReg = w)
    (hregs : x.regs ∘ callerReg = x₁.regs)
    (hmem : ∀ a < 2 ^ w, x.mem a = x₁.mem a) (ho : o.eval w x₁ = some y₁) :
    ∃ y : Data ((r_c + 1) + r_s),
      (compileOp o).eval W x = some y ∧
      y.regs callerWidthReg = w ∧
      y.regs ∘ subReg = x.regs ∘ subReg ∧
      y.regs ∘ callerReg = y₁.regs ∧
      (∀ a < 2 ^ w, y.mem a = y₁.mem a) ∧
      (∀ a, 2 ^ w ≤ a → y.mem a = x.mem a) := by
  cases o with
  | alu f d args =>
    cases f with
    | width =>
      simp only [Op.eval, StandardOp.eval] at ho
      obtain ⟨-, rfl⟩ := Data.put_eq_some.mp ho
      refine ⟨x.set (callerReg d) w, ?_, ?_, ?_, ?_, hmem, fun _ _ => rfl⟩
      · simp only [compileOp, Op.eval]; rw [hWreg]
      · rw [Data.set_regs, Function.update_of_ne (callerReg_ne_callerWidthReg d).symm, hWreg]
      · funext j
        simp [Data.set_regs, Function.update_of_ne (callerReg_ne_subReg d j).symm]
      · funext i
        simp only [Function.comp_apply, Data.set_regs]
        by_cases hi : i = d
        · subst hi; simp
        · rw [Function.update_of_ne (fun h => hi (callerReg_injective h)),
            Function.update_of_ne hi]
          exact congrFun hregs i
    | bin f =>
      obtain ⟨y₂, ho₂, hr₂, hm₂, hhi₂⟩ :=
        op_eval_agree_lt (x₂ := x.comap callerReg) hx₁ hregs hmem ho
      have hno : ¬(Op.alu (B := .standard) (.bin f) d args).ReadsWidth := by simp [Op.ReadsWidth]
      have hoW : (Op.alu (B := .standard) (.bin f) d args).eval W (x.comap callerReg) = some y₂ :=
        Op.eval_mono_width hno ho₂ hw
      have hren := Op.eval_rename callerReg_injective (.alu (B := .standard) (.bin f) d args) W x
      rw [hoW, Option.map_some] at hren
      refine ⟨y₂.extend callerReg x, hren, ?_, ?_, ?_, hm₂, hhi₂⟩
      · exact Function.extend_apply' _ _ _
          (by rintro ⟨i, hi⟩; exact callerReg_ne_callerWidthReg i hi) |>.trans hWreg
      · funext j
        exact Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact callerReg_ne_subReg i j hi)
      · change ((y₂.extend callerReg x).comap callerReg).regs = _
        rw [Data.comap_extend callerReg_injective, hr₂]
  | const d v =>
    obtain ⟨y₂, ho₂, hr₂, hm₂, hhi₂⟩ :=
      op_eval_agree_lt (x₂ := x.comap callerReg) hx₁ hregs hmem ho
    have hno : ¬(Op.const (B := .standard) d v).ReadsWidth := id
    have hoW := Op.eval_mono_width hno ho₂ hw
    have hren := Op.eval_rename callerReg_injective (.const (B := .standard) d v) W x
    rw [hoW, Option.map_some] at hren
    refine ⟨y₂.extend callerReg x, hren, ?_, ?_, ?_, hm₂, hhi₂⟩
    · exact Function.extend_apply' _ _ _
        (by rintro ⟨i, hi⟩; exact callerReg_ne_callerWidthReg i hi) |>.trans hWreg
    · funext j
      exact Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact callerReg_ne_subReg i j hi)
    · change ((y₂.extend callerReg x).comap callerReg).regs = _
      rw [Data.comap_extend callerReg_injective, hr₂]
  | copy d s =>
    obtain ⟨y₂, ho₂, hr₂, hm₂, hhi₂⟩ :=
      op_eval_agree_lt (x₂ := x.comap callerReg) hx₁ hregs hmem ho
    have hno : ¬(Op.copy (B := .standard) d s).ReadsWidth := id
    have hoW := Op.eval_mono_width hno ho₂ hw
    have hren := Op.eval_rename callerReg_injective (.copy (B := .standard) d s) W x
    rw [hoW, Option.map_some] at hren
    refine ⟨y₂.extend callerReg x, hren, ?_, ?_, ?_, hm₂, hhi₂⟩
    · exact Function.extend_apply' _ _ _
        (by rintro ⟨i, hi⟩; exact callerReg_ne_callerWidthReg i hi) |>.trans hWreg
    · funext j
      exact Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact callerReg_ne_subReg i j hi)
    · change ((y₂.extend callerReg x).comap callerReg).regs = _
      rw [Data.comap_extend callerReg_injective, hr₂]
  | load d a =>
    obtain ⟨y₂, ho₂, hr₂, hm₂, hhi₂⟩ :=
      op_eval_agree_lt (x₂ := x.comap callerReg) hx₁ hregs hmem ho
    have hno : ¬(Op.load (B := .standard) d a).ReadsWidth := id
    have hoW := Op.eval_mono_width hno ho₂ hw
    have hren := Op.eval_rename callerReg_injective (.load (B := .standard) d a) W x
    rw [hoW, Option.map_some] at hren
    refine ⟨y₂.extend callerReg x, hren, ?_, ?_, ?_, hm₂, hhi₂⟩
    · exact Function.extend_apply' _ _ _
        (by rintro ⟨i, hi⟩; exact callerReg_ne_callerWidthReg i hi) |>.trans hWreg
    · funext j
      exact Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact callerReg_ne_subReg i j hi)
    · change ((y₂.extend callerReg x).comap callerReg).regs = _
      rw [Data.comap_extend callerReg_injective, hr₂]
  | store a s =>
    obtain ⟨y₂, ho₂, hr₂, hm₂, hhi₂⟩ :=
      op_eval_agree_lt (x₂ := x.comap callerReg) hx₁ hregs hmem ho
    have hno : ¬(Op.store (B := .standard) a s).ReadsWidth := id
    have hoW := Op.eval_mono_width hno ho₂ hw
    have hren := Op.eval_rename callerReg_injective (.store (B := .standard) a s) W x
    rw [hoW, Option.map_some] at hren
    refine ⟨y₂.extend callerReg x, hren, ?_, ?_, ?_, hm₂, hhi₂⟩
    · exact Function.extend_apply' _ _ _
        (by rintro ⟨i, hi⟩; exact callerReg_ne_callerWidthReg i hi) |>.trans hWreg
    · funext j
      exact Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact callerReg_ne_subReg i j hi)
    · change ((y₂.extend callerReg x).comap callerReg).regs = _
      rw [Data.comap_extend callerReg_injective, hr₂]

/-- **Inline oracle compilation theorem**: if `c` executes at logical width `w ≤ W` with oracle
`O` from `w`-bounded data `x₀`, and `sub` answers every query `q` of `c` in time `≤ T_sub q`
while preserving `[0, 2^w)` and advancing an invariant `Inv` indexed by remaining-query budget,
then `compileOracle c sub` executes at width `W` in time `≤ t + ∑_{q ∈ qs} (T_sub q + 3)`
(even if `c` reads `width%`, since `callerWidthReg` holds `w`). -/
theorem compileOracle_exec {r_c r_s w W t : ℕ} {O : List ℕ → Bool}
    {c : OracleCode .standard r_c} {sub : Code .standard (r_s + 3)}
    {x₀ y₀ : Data r_c} {qs : List (List ℕ)} {T_sub : List ℕ → ℕ}
    {Inv : (ℕ → ℕ) → (Fin (r_s + 3) → ℕ) → ℕ → Prop}
    (hw : w ≤ W) (hx₀ : x₀.Bounded w)
    (hrun : OracleExec w O c x₀ y₀ t qs)
    (hinv_lo : ∀ m₁ m₂ rs k, (∀ a, 2 ^ w ≤ a → m₁ a = m₂ a) → Inv m₁ rs k → Inv m₂ rs k)
    (hinv_args : ∀ m rs k u v, Inv m rs k →
      Inv m (Function.update (Function.update rs ⟨0, by omega⟩ u) ⟨1, by omega⟩ v) k)
    (hsub : ∀ (q : List ℕ) (k : ℕ) (x : Data (r_s + 3)),
      q ∈ qs → 1 ≤ k →
      x.regs ⟨0, by omega⟩ + q.length < 2 ^ w →
      q = (List.range q.length).map (fun i => x.mem (x.regs ⟨0, by omega⟩ + i)) →
      x.regs ⟨1, by omega⟩ = q.length →
      Inv x.mem x.regs k →
      ∃ z : Data (r_s + 3),
        ExecWithin W sub x z (T_sub q) ∧
        z.regs ⟨2, by omega⟩ = (O q).toNat ∧
        (∀ a < 2 ^ w, z.mem a = x.mem a) ∧
        Inv z.mem z.regs (k - 1))
    {x : Data ((r_c + 1) + (r_s + 3))} {k₀ : ℕ} (hk₀ : qs.length ≤ k₀)
    (hWreg : x.regs callerWidthReg = w)
    (hregs : x.regs ∘ callerReg = x₀.regs)
    (hmem : ∀ a < 2 ^ w, x.mem a = x₀.mem a)
    (hinv : Inv x.mem (x.regs ∘ subReg) k₀) :
    ∃ y : Data ((r_c + 1) + (r_s + 3)),
      ExecWithin W (compileOracle c sub) x y (t + (qs.map fun q => T_sub q + 3).sum) ∧
      y.regs callerWidthReg = w ∧
      y.regs ∘ callerReg = y₀.regs ∧
      (∀ a < 2 ^ w, y.mem a = y₀.mem a) ∧
      Inv y.mem (y.regs ∘ subReg) (k₀ - qs.length) := by
  induction hrun generalizing x k₀ with
  | op ho =>
    obtain ⟨y, hy, hWy, hsuby, hry, hmy, hhiy⟩ := compileOp_eval hw hx₀ hWreg hregs hmem ho
    refine ⟨y, (ExecWithin.op hy).mono (by simp), hWy, hry, hmy, ?_⟩
    rw [hsuby]
    simpa using hinv_lo x.mem y.mem (x.regs ∘ subReg) k₀ (fun a ha => (hhiy a ha).symm) hinv
  | @seq c₁ c₂ _ _ _ _ _ qs₁ qs₂ h₁ _ ih₁ ih₂ =>
    have hq₁ : qs₁.length ≤ k₀ := by simp only [List.length_append] at hk₀; omega
    obtain ⟨y, hy, hWy, hry, hmy, hinvy⟩ := ih₁ hx₀
      (fun q k xs hq => hsub q k xs (List.mem_append.mpr (Or.inl hq))) hq₁ hWreg hregs hmem hinv
    have hq₂ : qs₂.length ≤ k₀ - qs₁.length := by simp only [List.length_append] at hk₀; omega
    obtain ⟨z, hz, hWz, hrz, hmz, hinvz⟩ := ih₂ (h₁.bounded hx₀)
      (fun q k xs hq => hsub q k xs (List.mem_append.mpr (Or.inr hq))) hq₂ hWy hry hmy hinvy
    refine ⟨z, (hy.seq hz).mono ?_, hWz, hrz, hmz, ?_⟩
    · simp only [List.map_append, List.sum_append]; omega
    · simpa only [List.length_append, Nat.sub_sub] using hinvz
  | branch_pos hcond _ ih =>
    obtain ⟨y, hy, hWy, hry, hmy, hinvy⟩ := ih hx₀ hsub hk₀ hWreg hregs hmem hinv
    have hc' : (Cond.rename callerReg _).Holds x :=
      (Cond.holds_rename _ x).mpr ((cond_holds_of_regs_eq hregs).mpr hcond)
    exact ⟨y, (ExecWithin.branch_pos hc' hy).mono (by omega), hWy, hry, hmy, hinvy⟩
  | branch_neg hcond _ ih =>
    obtain ⟨y, hy, hWy, hry, hmy, hinvy⟩ := ih hx₀ hsub hk₀ hWreg hregs hmem hinv
    have hc' : ¬(Cond.rename callerReg _).Holds x := fun h =>
      hcond ((cond_holds_of_regs_eq hregs).mp ((Cond.holds_rename _ x).mp h))
    exact ⟨y, (ExecWithin.branch_neg hc' hy).mono (by omega), hWy, hry, hmy, hinvy⟩
  | loop_exit hcond =>
    have hc' : ¬(Cond.rename callerReg _).Holds x := fun h =>
      hcond ((cond_holds_of_regs_eq hregs).mp ((Cond.holds_rename _ x).mp h))
    exact ⟨x, (ExecWithin.loop_exit hc').mono (by simp), hWreg, hregs, hmem, by simpa using hinv⟩
  | @loop_iter cond body _ _ _ _ _ qs₁ qs₂ hcond hb _ ihb ihl =>
    have hq₁ : qs₁.length ≤ k₀ := by simp only [List.length_append] at hk₀; omega
    obtain ⟨y, hy, hWy, hry, hmy, hinvy⟩ := ihb hx₀
      (fun q k xs hq => hsub q k xs (List.mem_append.mpr (Or.inl hq))) hq₁ hWreg hregs hmem hinv
    have hq₂ : qs₂.length ≤ k₀ - qs₁.length := by simp only [List.length_append] at hk₀; omega
    obtain ⟨z, hz, hWz, hrz, hmz, hinvz⟩ := ihl (hb.bounded hx₀)
      (fun q k xs hq => hsub q k xs (List.mem_append.mpr (Or.inr hq))) hq₂ hWy hry hmy hinvy
    have hc' : (cond.rename callerReg).Holds x :=
      (Cond.holds_rename _ x).mpr ((cond_holds_of_regs_eq hregs).mpr hcond)
    refine ⟨z, (ExecWithin.loop_iter hc' hy hz).mono ?_, hWz, hrz, hmz, ?_⟩
    · simp only [List.map_append, List.sum_append]; omega
    · simpa only [List.length_append, Nat.sub_sub] using hinvz
  | query h1 hbl =>
    rename_i dst base len x₁
    set q := (List.range (x₁.regs len)).map fun i => x₁.mem (x₁.regs base + i) with hq_def
    have hk1 : 1 ≤ k₀ := by simpa using hk₀
    let x₁' := x.set (subReg ⟨0, by omega⟩) (x.regs (callerReg base))
    let x₂' := x₁'.set (subReg ⟨1, by omega⟩) (x₁'.regs (callerReg len))
    have hx₂_0 : x₂'.regs (subReg ⟨0, by omega⟩) = x₁.regs base := by
      have hne : subReg (r_c := r_c) (r_s := r_s + 3) ⟨0, by omega⟩ ≠ subReg ⟨1, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp [subReg] at this
      simp only [x₂', x₁', Data.set_regs, Function.update_of_ne hne, Function.update_self]
      exact congrFun hregs base
    have hx₂_1 : x₂'.regs (subReg ⟨1, by omega⟩) = x₁.regs len := by
      have hne : callerReg (r_s := r_s + 3) len ≠ subReg (r_c := r_c) ⟨0, by omega⟩ :=
        callerReg_ne_subReg len _
      simp only [x₂', x₁', Data.set_regs, Function.update_self, Function.update_of_ne hne]
      exact congrFun hregs len
    have hx₂_caller : ∀ i : Fin r_c, x₂'.regs (callerReg i) = x₁.regs i := by
      intro i
      have h0 := callerReg_ne_subReg (r_s := r_s + 3) i ⟨0, by omega⟩
      have h1' := callerReg_ne_subReg (r_s := r_s + 3) i ⟨1, by omega⟩
      simp only [x₂', x₁', Data.set_regs, Function.update_of_ne h1', Function.update_of_ne h0]
      exact congrFun hregs i
    have hx₂_W : x₂'.regs callerWidthReg = w := by
      have h0 := callerWidthReg_ne_subReg (r_c := r_c) (r_s := r_s + 3) ⟨0, by omega⟩
      have h1' := callerWidthReg_ne_subReg (r_c := r_c) (r_s := r_s + 3) ⟨1, by omega⟩
      simp only [x₂', x₁', Data.set_regs, Function.update_of_ne h1', Function.update_of_ne h0,
        hWreg]
    have hq_len : q.length = x₁.regs len := by simp [hq_def]
    have hq_mem : q = (List.range q.length).map
        (fun i => (x₂'.comap subReg).mem ((x₂'.comap subReg).regs ⟨0, by omega⟩ + i)) := by
      rw [hq_len]
      simp only [Data.comap_mem, Data.comap_regs, hx₂_0, x₂', x₁', Data.set_mem, hq_def]
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      change x₁.regs base + x₁.regs len < 2 ^ w at hbl
      exact (hmem _ (by omega)).symm
    have hinv₂ : Inv (x₂'.comap subReg).mem (x₂'.comap subReg).regs k₀ := by
      have hsub_eq : (x₂'.comap subReg).regs =
          Function.update (Function.update (x.regs ∘ subReg) ⟨0, by omega⟩ (x₁.regs base))
            ⟨1, by omega⟩ (x₁.regs len) := by
        have h0 := Data.comap_set (subReg_injective (r_c := r_c) (r_s := r_s + 3)) x ⟨0, by omega⟩
          (x.regs (callerReg base))
        have h1' := Data.comap_set (subReg_injective (r_c := r_c) (r_s := r_s + 3)) x₁'
          ⟨1, by omega⟩ (x₁'.regs (callerReg len))
        have heq1 : x₁'.regs (callerReg len) = x₁.regs len := by
          have hne := callerReg_ne_subReg (r_s := r_s + 3) len ⟨0, by omega⟩
          simp only [x₁', Data.set_regs, Function.update_of_ne hne]
          exact congrFun hregs len
        have heq0 : x.regs (callerReg base) = x₁.regs base := congrFun hregs base
        have hce : x₂'.comap subReg =
            ((x.comap subReg).set ⟨0, by omega⟩ (x₁.regs base)).set ⟨1,
              by omega⟩ (x₁.regs len) := by
          change (x₁'.set (subReg ⟨1, by omega⟩) (x₁'.regs (callerReg len))).comap subReg = _
          rw [h1', heq1]
          change ((x.set (subReg ⟨0, by omega⟩) (x.regs (callerReg base))).comap subReg).set
            ⟨1, by omega⟩ (x₁.regs len) = _
          rw [h0, heq0]
        rw [hce]; rfl
      rw [hsub_eq]
      exact hinv_args x.mem (x.regs ∘ subReg) k₀ _ _ hinv
    obtain ⟨z, hz, hz2, hzmem, hzinv⟩ := hsub q k₀ (x₂'.comap subReg) (List.mem_singleton_self _)
      hk1 (by simp only [Data.comap_regs, hx₂_0, hq_len]; exact hbl) hq_mem
      (by simp only [Data.comap_regs, hx₂_1, hq_len]) hinv₂
    obtain ⟨y₁, hy₁, hy₁_sub, hy₁_frame⟩ :=
      ExecWithin.rename_post (subReg_injective (r_c := r_c) (r_s := r_s + 3)) ⟨z, hz, rfl⟩
    have hy₁_eq : y₁.comap subReg = z := hy₁_sub.symm
    have hy₁_2 : y₁.regs (subReg ⟨2, by omega⟩) = (O q).toNat := by
      have := congrArg (fun d => d.regs ⟨2, by omega⟩) hy₁_eq
      simpa only [Data.comap_regs] using this.trans hz2
    have hy₁_mem : ∀ a < 2 ^ w, y₁.mem a = x₁.mem a := fun a ha => by
      have hm : y₁.mem = z.mem := congrArg Data.mem hy₁_eq
      rw [congrFun hm a, hzmem a ha]; exact hmem a ha
    have hy₁_inv : Inv y₁.mem (y₁.regs ∘ subReg) (k₀ - 1) := by
      have hm : y₁.mem = z.mem := congrArg Data.mem hy₁_eq
      have hr : y₁.regs ∘ subReg = z.regs := congrArg Data.regs hy₁_eq
      rw [hm, hr]; exact hzinv
    let y := y₁.set (callerReg dst) (y₁.regs (subReg ⟨2, by omega⟩))
    have hstep1 :
        ExecWithin W (.op (Op.copy (B := .standard) (subReg ⟨0, by omega⟩) (callerReg base)))
          x x₁' 1 :=
      ExecWithin.copy
    have hstep2 :
        ExecWithin W (.op (Op.copy (B := .standard) (subReg ⟨1, by omega⟩) (callerReg len)))
          x₁' x₂' 1 :=
      ExecWithin.copy
    have hstep4 :
        ExecWithin W (.op (Op.copy (B := .standard) (callerReg dst) (subReg ⟨2, by omega⟩)))
          y₁ y 1 :=
      ExecWithin.copy
    refine ⟨y, (hstep1.seq (hstep2.seq (hy₁.seq hstep4))).mono (by simp; omega), ?_, ?_, hy₁_mem,
      ?_⟩
    · simp only [y, Data.set_regs,
        Function.update_of_ne (callerReg_ne_callerWidthReg dst).symm,
        hy₁_frame callerWidthReg (fun j => (callerWidthReg_ne_subReg j).symm), hx₂_W]
    · funext i
      simp only [Function.comp_apply, y, Data.set_regs]
      by_cases hi : i = dst
      · subst hi
        simp only [Function.update_self, hy₁_2, hq_def]
      · have hne : callerReg (r_s := r_s + 3) i ≠ callerReg dst := fun h =>
          hi (callerReg_injective h)
        rw [Function.update_of_ne hne,
          hy₁_frame (callerReg i) (fun j => (callerReg_ne_subReg i j).symm), hx₂_caller i,
          Function.update_of_ne hi]
    · have hy_sub : y.regs ∘ subReg = y₁.regs ∘ subReg := by
        funext j
        have hne := (callerReg_ne_subReg (r_s := r_s + 3) dst j).symm
        simp [y, Data.set_regs, Function.update_of_ne hne]
      rw [show y.mem = y₁.mem from rfl, hy_sub]
      simpa using hy₁_inv

end CslibFrontier.WordRAM
