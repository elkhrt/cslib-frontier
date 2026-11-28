/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Injective
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Determinant

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

/-!
# Deterministic Oracle Logarithmic Space and $\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}}$

This module formalizes deterministic partial-walk evaluation for `walkVec`, deterministic
logarithmic-space oracle Turing machines with a write-only append-only query tape
(`Cslib.Complexity.OracleMultiTapeTM`, `Cslib.Complexity.LOracle`),
and the modular-counting oracle logspace class $\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}}$
(`Cslib.Complexity.LModL`) of Buntrock, Damm, Hertrampf, and Meinel, under
standard Lean axioms.

## Main definitions

* `Cslib.Complexity.iterOpt`: deterministic partial-function walk iterator over `T`
  steps.
* `Cslib.Complexity.OracleInstruction`,
  `Cslib.Complexity.OracleMultiTapeTM`: deterministic multi-tape Turing machines with
  read-only input tape, `k_tapes` work tapes, and a write-only append-only binary oracle query tape
  erased after each query.
* `Cslib.Complexity.OracleMultiTapeTM.DecidesInLogSpace`,
  `Cslib.Complexity.LOracle`, `Cslib.Complexity.LModL`: relativized
  deterministic logarithmic space $\mathrm{L}^O$ and $\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}}$.

## Main results

* `Cslib.Complexity.walkVec_option_deterministic`: on `{0, 1}` indicator matrices of
  deterministic partial transitions, `walkVec` equals `Pi.single u 1` at the unique reached vertex
  (or `0` if none).
* `Cslib.Complexity.L_subset_LOracle`,
  `Cslib.Complexity.L_subset_LModL`,
  `Cslib.Complexity.self_mem_LOracle`,
  `Cslib.Complexity.ModL_encBits_subset_LModL`: structural inclusions into
  $\mathrm{L}^O$ and $\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}}$.
-/

public section

namespace Cslib.Complexity

open Cslib
open scoped Matrix
open _root_.Turing _root_.Turing.MultiTapeNTM _root_.Turing.MultiTapeNTM.ConfigurationGraph

/-! ### Deterministic partial-walk evaluation for `walkVec` -/

/-- Iterate a sequence of deterministic partial transitions `next : Fin T → Fin M → Option (Fin M)`
from `start : Fin M` for `s ≤ T` steps. -/
@[expose]
def iterOpt {T M : ℕ} (start : Fin M) (next : Fin T → Fin M → Option (Fin M)) :
    ∀ s ≤ T, Option (Fin M)
  | 0, _ => some start
  | s + 1, hs => (iterOpt start next s (Nat.le_of_succ_le hs)).bind (next ⟨s, hs⟩)

@[simp]
theorem iterOpt_zero {T M : ℕ} (start : Fin M) (next : Fin T → Fin M → Option (Fin M))
    (h0 : 0 ≤ T) :
    iterOpt start next 0 h0 = some start :=
  rfl

@[simp]
theorem iterOpt_succ {T M : ℕ} (start : Fin M) (next : Fin T → Fin M → Option (Fin M))
    (s : ℕ) (hs : s + 1 ≤ T) :
    iterOpt start next (s + 1) hs =
      (iterOpt start next s (Nat.le_of_succ_le hs)).bind (next ⟨s, hs⟩) :=
  rfl

/-- When each transition matrix `P t` is the `{0, 1}` indicator of a deterministic partial function
`next t`, `walkVec start P s hs` has weight `1` at the unique reached vertex (and `0` elsewhere). -/
theorem walkVec_option_deterministic {R : Type*} [CommRing R] {T M : ℕ}
    (start : Fin M) (next : Fin T → Fin M → Option (Fin M))
    (P : Fin T → Matrix (Fin M) (Fin M) R)
    (hP : ∀ (t : Fin T) (i j : Fin M), P t i j = if next t i = some j then 1 else 0)
    (s : ℕ) (hs : s ≤ T) :
    walkVec start P s hs =
      match iterOpt start next s hs with
      | some u => Pi.single u 1
      | none => 0 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [walkVec_succ, iterOpt_succ, ih (Nat.le_of_succ_le hs)]
    cases hcur : iterOpt start next s (Nat.le_of_succ_le hs) with
    | none =>
      ext j
      simp [Matrix.vecMul, dotProduct]
    | some u =>
      dsimp only [Option.bind]
      cases hnext : next ⟨s, hs⟩ u with
      | none =>
        ext j
        simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
        rw [Finset.sum_eq_single u]
        · simp [hP, hnext]
        · intro u' _ hne; simp [Pi.single_eq_of_ne hne]
        · simp
      | some v =>
        ext j
        simp only [Matrix.vecMul, dotProduct]
        rw [Finset.sum_eq_single u]
        · simp only [Pi.single_eq_same, one_mul, hP, hnext]
          by_cases hv : v = j
          · subst hv; simp
          · simp [hv]
        · intro u' _ hne; simp [Pi.single_eq_of_ne hne]
        · simp

/-! ### Deterministic oracle Turing machines and $\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}}$ -/

/-- One deterministic transition instruction of an oracle Turing machine: either a standard tape
step (optionally appending one bit to the write-only oracle query tape), an oracle query branching
on membership of the accumulated query word (and erasing the query tape), or a halting verdict. -/
inductive OracleInstruction (k_tapes : ℕ) (State : Type)
  | step (inputMove : SignType)
      (workMoves : Fin k_tapes → Option (Option Bool) × SignType)
      (emitQueryBit : Option Bool)
      (nextState : State)
  | query (onYes onNo : State)
  | halt (accept : Bool)

/-- Deterministic multi-tape binary oracle Turing machine with `k_tapes` work tapes. -/
structure OracleMultiTapeTM (k_tapes : ℕ) (State : Type) where
  /-- Initial control state. -/
  q₀ : State
  /-- Deterministic local transition table. -/
  tr : State → Option Bool → (Fin k_tapes → Option Bool) → OracleInstruction k_tapes State

namespace OracleMultiTapeTM

/-- Convert an `OracleInstruction` under oracle `O` and current query buffer `buf` into a native
`Turing.Action` on `Cfg` (keeping `Cfg.output = []` until `.halt`) and the updated query buffer. -/
@[expose]
noncomputable def instrToAction {k_tapes : ℕ} {State : Type} (O : Language Bool)
    (buf : List Bool) : OracleInstruction k_tapes State → Action k_tapes Bool State × List Bool
  | .step moveIn moveWork emit nextQ =>
      (⟨moveIn, moveWork, none, some nextQ⟩, buf ++ emit.toList)
  | .query onYes onNo =>
      let _ : Decidable (buf ∈ O) := Classical.propDecidable _
      (⟨.zero, fun _ ↦ (none, .zero), none, some (if buf ∈ O then onYes else onNo)⟩, [])
  | .halt acc =>
      (⟨.zero, fun _ ↦ (none, .zero), some acc, none⟩, [])

@[simp]
theorem instrToAction_step {k_tapes : ℕ} {State : Type} (O : Language Bool) (buf : List Bool)
    (moveIn : SignType) (moveWork : Fin k_tapes → Option (Option Bool) × SignType)
    (emit : Option Bool) (nextQ : State) :
    instrToAction O buf (.step moveIn moveWork emit nextQ) =
      (⟨moveIn, moveWork, none, some nextQ⟩, buf ++ emit.toList) :=
  rfl

@[simp]
theorem instrToAction_query {k_tapes : ℕ} {State : Type} (O : Language Bool) (buf : List Bool)
    [Decidable (buf ∈ O)] (onYes onNo : State) :
    instrToAction (k_tapes := k_tapes) O buf (.query onYes onNo) =
      (⟨.zero, fun _ ↦ (none, .zero), none, some (if buf ∈ O then onYes else onNo)⟩, []) := by
  dsimp only [instrToAction]
  split_ifs <;> rfl

@[simp]
theorem instrToAction_halt {k_tapes : ℕ} {State : Type} (O : Language Bool) (buf : List Bool)
    (acc : Bool) :
    instrToAction (k_tapes := k_tapes) (State := State) O buf (.halt acc) =
      (⟨.zero, fun _ ↦ (none, .zero), some acc, none⟩, []) :=
  rfl

/-- One deterministic step of `M` with oracle `O` on `(cfg, queryBuf)`. -/
noncomputable def stepCfg {k_tapes : ℕ} {State : Type} (M : OracleMultiTapeTM k_tapes State)
    (O : Language Bool) {w : List Bool}
    (st : Cfg k_tapes Bool State w × List Bool) : Cfg k_tapes Bool State w × List Bool :=
  match st.1.state with
  | none => st
  | some q =>
      let res := instrToAction O st.2 (M.tr q st.1.inputSymbol st.1.workTapeSymbols)
      (res.1.apply st.1, res.2)

theorem stepCfg_of_state_eq_none {k_tapes : ℕ} {State : Type}
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) {w : List Bool}
    {st : Cfg k_tapes Bool State w × List Bool} (h : st.1.state = none) :
    M.stepCfg O st = st := by
  simp [stepCfg, h]

theorem stepCfg_of_state_eq_some {k_tapes : ℕ} {State : Type}
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) {w : List Bool}
    {st : Cfg k_tapes Bool State w × List Bool} {q : State} (h : st.1.state = some q) :
    M.stepCfg O st =
      ((instrToAction O st.2 (M.tr q st.1.inputSymbol st.1.workTapeSymbols)).1.apply st.1,
       (instrToAction O st.2 (M.tr q st.1.inputSymbol st.1.workTapeSymbols)).2) := by
  simp [stepCfg, h]

/-- Deterministic `t`-step configuration and query buffer of `M` with oracle `O` on input `w`. -/
@[expose]
noncomputable def runCfg {k_tapes : ℕ} {State : Type} (M : OracleMultiTapeTM k_tapes State)
    (O : Language Bool) (w : List Bool) (t : ℕ) : Cfg k_tapes Bool State w × List Bool :=
  (M.stepCfg O)^[t] (Cfg.init M.q₀ w, [])

@[simp]
theorem runCfg_zero {k_tapes : ℕ} {State : Type} (M : OracleMultiTapeTM k_tapes State)
    (O : Language Bool) (w : List Bool) :
    M.runCfg O w 0 = (Cfg.init M.q₀ w, []) :=
  rfl

theorem runCfg_succ {k_tapes : ℕ} {State : Type} (M : OracleMultiTapeTM k_tapes State)
    (O : Language Bool) (w : List Bool) (t : ℕ) :
    M.runCfg O w (t + 1) = M.stepCfg O (M.runCfg O w t) :=
  Function.iterate_succ_apply' (M.stepCfg O) t (Cfg.init M.q₀ w, [])

/-- Nondeterministic envelope of `M` forgetting oracle answers and query-tape emissions, used to
record computation prefixes and measure work-tape space via `Turing.MultiTapeNTM.RunPath.space`.
-/
@[expose]
def envelopeNTM {k_tapes : ℕ} {State : Type} (M : OracleMultiTapeTM k_tapes State) :
    MultiTapeNTM k_tapes Bool State where
  q₀ := M.q₀
  Tr q sym work act :=
    ∃ (O : Language Bool) (buf : List Bool), (instrToAction O buf (M.tr q sym work)).1 = act

theorem step_envelopeNTM_stepCfg {k_tapes : ℕ} {State : Type}
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) {w : List Bool}
    (st : Cfg k_tapes Bool State w × List Bool) :
    M.envelopeNTM.Step st.1 (M.stepCfg O st).1 := by
  dsimp only [stepCfg]
  cases hs : st.1.state with
  | none => simp [MultiTapeNTM.Step, hs]
  | some q =>
    simp only [MultiTapeNTM.Step, hs]
    exact ⟨_, ⟨O, st.2, rfl⟩, rfl⟩

private noncomputable def runPathAux {k_tapes : ℕ} {State : Type}
    (M : OracleMultiTapeTM k_tapes State) (O : Language Bool) (w : List Bool) :
    ∀ t : ℕ, { p : M.envelopeNTM.ComputationPath w // p.toRunPath.last = (M.runCfg O w t).1 }
  | 0 => ⟨⟨RelSeries.singleton _ (Cfg.init M.q₀ w), rfl⟩, rfl⟩
  | t + 1 =>
    let ⟨p, hp⟩ := M.runPathAux O w t
    ⟨⟨p.toRunPath.snoc (M.stepCfg O (M.runCfg O w t)).1
      (by
        change M.envelopeNTM.Step p.toRunPath.last (M.stepCfg O (M.runCfg O w t)).1
        rw [hp]
        exact M.step_envelopeNTM_stepCfg O (M.runCfg O w t)),
     by simpa using p.head_eq⟩,
     by simp [RelSeries.last_snoc, M.runCfg_succ]⟩

/-- The `t`-step `ComputationPath` of `M.envelopeNTM` traced by `M.runCfg O w` on input `w`. -/
noncomputable def runPath {k_tapes : ℕ} {State : Type} (M : OracleMultiTapeTM k_tapes State)
    (O : Language Bool) (w : List Bool) (t : ℕ) : M.envelopeNTM.ComputationPath w :=
  (M.runPathAux O w t).1

@[simp]
theorem runPath_last {k_tapes : ℕ} {State : Type} (M : OracleMultiTapeTM k_tapes State)
    (O : Language Bool) (w : List Bool) (t : ℕ) :
    (M.runPath O w t).last = (M.runCfg O w t).1 :=
  (M.runPathAux O w t).2

/-- `M` decides `A` in deterministic logarithmic space relative to oracle `O` and encoding `enc`:
there is a constant `c` such that on every `enc a`, the deterministic run of `M^O` visits at most
`c * (log₂ |enc a| + 1)` work-tape cells on every prefix, halts, and accepts iff `a ∈ A`. -/
@[expose]
def DecidesInLogSpace {k_tapes : ℕ} {State : Type} (M : OracleMultiTapeTM k_tapes State)
    (O : Language Bool) {α : Type} (enc : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ c : ℕ, ∀ a : α,
    (∀ t : ℕ, RunPath.space (M.runPath O (enc a) t).toRunPath ≤
      c * (Nat.log2 (enc a).length + 1)) ∧
    (∃ t : ℕ, (M.runCfg O (enc a) t).1.Halted) ∧
    (a ∈ A ↔ ∃ t : ℕ, (M.runCfg O (enc a) t).1.Halted ∧
      (M.runCfg O (enc a) t).1.output = [true])

end OracleMultiTapeTM

/-- **$\mathrm{L}^O$**: problems decided in deterministic logarithmic space with oracle access to
`O : Language Bool`. -/
@[expose]
def LOracle (O : Language Bool) {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k_tapes : ℕ) (State : Type) (_ : Finite State)
    (M : OracleMultiTapeTM k_tapes State), M.DecidesInLogSpace O enc A}

/-- **$\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}}$**: problems decided in deterministic logarithmic space
with oracle access to a language in $\mathrm{Mod}_k\mathrm{L}$.
-/
@[expose]
def LModL (k : ℕ) {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ O ∈ Cslib.Complexity.ModL k MultiTapeTM.encBits, A ∈ LOracle O enc}

/-- Every problem in $\mathrm{L}$ lies in $\mathrm{L}^O$ for every oracle `O`. -/
theorem L_subset_LOracle (O : Language Bool) {α : Type} {enc : α ↪ List Bool} :
    Cslib.Complexity.L enc ⊆ LOracle O enc := by
  rintro A ⟨f, ⟨t, c, k_tapes, State, hfinite, tm, htm⟩, hA⟩
  let State' := (State × Fin 3) ⊕ Bool
  have hfin' : Finite State' := by infer_instance
  have houtputStep_lt (c : ℕ) (hc : c < 3) (x : Option Bool) : outputStep c x < 3 := by
    unfold outputStep
    cases x with
    | none => split_ifs <;> omega
    | some b => cases b <;> dsimp only [] <;> split_ifs <;> omega
  let M : OracleMultiTapeTM k_tapes State' :=
    { q₀ := Sum.inl (tm.q₀, ⟨0, by decide⟩)
      tr := fun st sym work ↦
        match st with
        | Sum.inl (q, o) =>
          let act := tm.tr q sym work
          let o' : Fin 3 := ⟨outputStep o.val act.output, houtputStep_lt o.val o.isLt act.output⟩
          match act.state with
          | some q' => .step act.inputTape act.workTapes none (Sum.inl (q', o'))
          | none => .step act.inputTape act.workTapes none (Sum.inr (o'.val == 1))
        | Sum.inr acc => .halt acc }
  let tmRun (w : List Bool) (s : ℕ) := tm.runFrom (tm.initCfg w) s
  have htrack (w : List Bool) (s : ℕ) :
      ((M.runCfg O w s).1.workTapes = (tmRun w s).workTapes ∧
       (M.runCfg O w s).1.workTapePos = (tmRun w s).workTapePos ∧
       (M.runCfg O w s).1.inputPos = (tmRun w s).inputPos) ∧
      (match (tmRun w s).state with
       | some q =>
         (M.runCfg O w s).1.state =
           some (Sum.inl (q, ⟨outputCode (tmRun w s).output, outputCode_lt _⟩)) ∧
         (M.runCfg O w s).1.output = []
       | none =>
         ((M.runCfg O w s).1.state =
            some (Sum.inr (outputCode (tmRun w s).output == 1)) ∧
          (M.runCfg O w s).1.output = []) ∨
         ((M.runCfg O w s).1.state = none ∧
          (M.runCfg O w s).1.output = [outputCode (tmRun w s).output == 1])) := by
    induction s with
    | zero =>
      refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
      change (Cfg.init M.q₀ w).state =
        some (Sum.inl (tm.q₀, ⟨outputCode ([] : List Bool), outputCode_lt _⟩)) ∧ _
      simp [M, outputCode]
    | succ s ih =>
      obtain ⟨⟨hwt, hwp, hip⟩, hst⟩ := ih
      have hsym_in : (M.runCfg O w s).1.inputSymbol = (tmRun w s).inputSymbol := by
        simp [Cfg.inputSymbol, hip]
      have hsym_wk : (M.runCfg O w s).1.workTapeSymbols = (tmRun w s).workTapeSymbols := by
        funext i; simp [Cfg.workTapeSymbols, hwt, hwp]
      rw [M.runCfg_succ]
      cases hts : (tmRun w s).state with
      | some q =>
        rw [hts] at hst
        obtain ⟨hm_st, hm_out⟩ := hst
        have htm_succ : tmRun w (s + 1) =
            (tm.tr q (tmRun w s).inputSymbol (tmRun w s).workTapeSymbols).apply (tmRun w s) := by
          dsimp only [tmRun]
          rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
            MultiTapeTM.step_of_state hts]
        rw [M.stepCfg_of_state_eq_some O hm_st, hsym_in, hsym_wk]
        set act := tm.tr q (tmRun w s).inputSymbol (tmRun w s).workTapeSymbols
        have hout_step : outputStep (outputCode (tmRun w s).output) act.output =
            outputCode ((tmRun w s).output ++ act.output.toList) := by
          rw [← outputCode_append, outputCode_summary]
        have hM_tr : M.tr (Sum.inl (q, ⟨outputCode (tmRun w s).output, outputCode_lt _⟩))
            (tmRun w s).inputSymbol (tmRun w s).workTapeSymbols =
            match act.state with
            | some q' => .step act.inputTape act.workTapes none
                (Sum.inl (q', ⟨outputStep (outputCode (tmRun w s).output) act.output,
                  houtputStep_lt _ (outputCode_lt _) _⟩))
            | none => .step act.inputTape act.workTapes none
                (Sum.inr (outputStep (outputCode (tmRun w s).output) act.output == 1)) := rfl
        rw [hM_tr]
        cases hact_st : act.state with
        | some q' =>
          simp only [OracleMultiTapeTM.instrToAction_step, htm_succ]
          refine ⟨⟨by ext i z; simp [hwt, hwp], by ext i; simp [hwp], by simp [hip]⟩, ?_⟩
          simp only [Action.apply_state, Action.apply_output, hact_st, hm_out,
            List.nil_append, Option.toList]
          exact ⟨by congr 3; ext; exact hout_step, trivial⟩
        | none =>
          simp only [OracleMultiTapeTM.instrToAction_step, htm_succ]
          refine ⟨⟨by ext i z; simp [hwt, hwp], by ext i; simp [hwp], by simp [hip]⟩, ?_⟩
          simp only [Action.apply_state, Action.apply_output, hact_st, hm_out,
            List.nil_append, Option.toList]
          exact Or.inl ⟨by rw [hout_step]; rfl, trivial⟩
      | none =>
        rw [hts] at hst
        have htm_succ : tmRun w (s + 1) = tmRun w s := by
          dsimp only [tmRun]
          rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
            MultiTapeTM.step_of_halt hts]
        rw [htm_succ, hts]
        rcases hst with ⟨hm_st, hm_out⟩ | ⟨hm_st, hm_out⟩
        · rw [M.stepCfg_of_state_eq_some O hm_st]
          have hM_tr : M.tr (Sum.inr (outputCode (tmRun w s).output == 1))
              (M.runCfg O w s).1.inputSymbol (M.runCfg O w s).1.workTapeSymbols =
              .halt (outputCode (tmRun w s).output == 1) := rfl
          rw [hM_tr, OracleMultiTapeTM.instrToAction_halt]
          refine ⟨⟨by ext i z; simp [hwt], by ext i; simp [hwp], by simp [hip]⟩,
            Or.inr ⟨rfl, by simp [hm_out]⟩⟩
        · rw [M.stepCfg_of_state_eq_none O hm_st]
          exact ⟨⟨hwt, hwp, hip⟩, Or.inr ⟨hm_st, hm_out⟩⟩
  have hspace_eq (w : List Bool) (s : ℕ) :
      RunPath.space (M.runPath O w s).toRunPath =
        RunPath.space (ComputationPath.ofDeterministic tm w s).toRunPath := by
    have hlen_M : ∀ r, (M.runPath O w r).toRunPath.length = r := by
      intro r
      induction r with
      | zero => rfl
      | succ r ih =>
        simpa [OracleMultiTapeTM.runPath, OracleMultiTapeTM.runPathAux] using ih
    have hget_M : ∀ r (k : ℕ) (hk : k < (M.runPath O w r).toRunPath.length + 1),
        (M.runPath O w r).toRunPath ⟨k, hk⟩ = (M.runCfg O w k).1 := by
      intro r
      induction r with
      | zero =>
        intro k hk
        have hk0 : k = 0 := by
          have h1 := hk.trans_eq (congrArg (· + 1) (hlen_M 0))
          omega
        subst hk0
        rfl
      | succ r ih =>
        intro k hk
        have hk_le : k ≤ r + 1 := by
          have h1 := hk.trans_eq (congrArg (· + 1) (hlen_M (r + 1)))
          omega
        rcases eq_or_lt_of_le hk_le with rfl | hk_lt
        · have hlast_idx :
              (⟨r + 1, hk⟩ : Fin ((M.runPath O w (r + 1)).toRunPath.length + 1)) =
              Fin.last _ := Fin.ext (hlen_M (r + 1)).symm
          rw [hlast_idx]
          exact M.runPath_last O w (r + 1)
        · have hk_r : k < (M.runPath O w r).toRunPath.length + 1 :=
            lt_of_lt_of_eq hk_lt (congrArg (· + 1) (hlen_M r).symm)
          have hsnoc : (M.runPath O w (r + 1)).toRunPath ⟨k, hk⟩ =
              (M.runPath O w r).toRunPath ⟨k, hk_r⟩ := by
            dsimp only [OracleMultiTapeTM.runPath, OracleMultiTapeTM.runPathAux] at hk ⊢
            have hk_r' : k < (M.runPathAux O w r).1.toRunPath.length + 1 := hk_r
            have hcast : ⟨k, hk⟩ =
                Fin.cast (by simp) (Fin.castSucc ⟨k, hk_r'⟩) := Fin.ext rfl
            rw [hcast, RelSeries.snoc_cast_castSucc]
          rw [hsnoc, ih k hk_r]
    have hget_D : ∀ (i : Fin ((ComputationPath.ofDeterministic tm w s).toRunPath.length + 1)),
        (ComputationPath.ofDeterministic tm w s).toRunPath i = tmRun w i.val := fun _ ↦ rfl
    unfold RunPath.space RunPath.spaceUsedByTape RunPath.visitedByTapeHead
    refine Finset.sum_congr rfl fun tape _ ↦ congrArg Finset.card <| Finset.ext fun z ↦ ?_
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      have hi_lt : i.val < (ComputationPath.ofDeterministic tm w s).toRunPath.length + 1 :=
        i.isLt.trans_eq (congrArg (· + 1) (hlen_M s))
      refine ⟨⟨i.val, hi_lt⟩, ?_⟩
      rw [hget_D ⟨i.val, hi_lt⟩, ← (htrack w i.val).1.2.1, ← hget_M s i.val i.isLt]
      exact hi
    · rintro ⟨j, hj⟩
      have hj_lt : j.val < (M.runPath O w s).toRunPath.length + 1 :=
        j.isLt.trans_eq (congrArg (· + 1) (hlen_M s).symm)
      refine ⟨⟨j.val, hj_lt⟩, ?_⟩
      rw [hget_M s j.val hj_lt, (htrack w j.val).1.2.1, ← hget_D j]
      exact hj
  refine ⟨k_tapes, State', hfin', M, c, fun a ↦ ?_⟩
  obtain ⟨⟨u, hhalt, hout⟩, -, hspace⟩ := htm a
  have hhalt_M (s : ℕ) (hs : (tmRun (enc a) s).Halted) :
      (M.runCfg O (enc a) (s + 1)).1.Halted ∧
      (M.runCfg O (enc a) (s + 1)).1.output =
        [outputCode (tmRun (enc a) s).output == 1] := by
    have htr_s := (htrack (enc a) s).2
    change (tmRun (enc a) s).state = none at hs
    rw [hs] at htr_s
    rw [M.runCfg_succ]
    rcases htr_s with ⟨hm_st, hm_out⟩ | ⟨hm_st, hm_out⟩
    · rw [M.stepCfg_of_state_eq_some O hm_st]
      have hM_tr : M.tr (Sum.inr (outputCode (tmRun (enc a) s).output == 1))
          (M.runCfg O (enc a) s).1.inputSymbol (M.runCfg O (enc a) s).1.workTapeSymbols =
          .halt (outputCode (tmRun (enc a) s).output == 1) := rfl
      rw [hM_tr, OracleMultiTapeTM.instrToAction_halt]
      exact ⟨rfl, by simp [hm_out]⟩
    · rw [M.stepCfg_of_state_eq_none O hm_st]
      exact ⟨hm_st, hm_out⟩
  have hstay_M : ∀ {s₁ s₂ : ℕ}, s₁ ≤ s₂ → (M.runCfg O (enc a) s₁).1.Halted →
      M.runCfg O (enc a) s₂ = M.runCfg O (enc a) s₁ := by
    intro s₁ s₂ hle hh₁
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [Nat.add_succ, M.runCfg_succ, ih (Nat.le_add_right _ _)]
      exact M.stepCfg_of_state_eq_none O hh₁
  refine ⟨fun s ↦ (hspace_eq (enc a) s).trans_le (hspace (ComputationPath.ofDeterministic tm _ s)),
    ⟨u + 1, (hhalt_M u hhalt).1⟩, ?_⟩
  rw [hA a]
  have hout_code : (outputCode (tmRun (enc a) u).output == 1) = f a := by
    rw [Bool.eq_iff_iff, beq_iff_eq, outputCode_eq_one_iff, hout]
    change MultiTapeTM.encBool (f a) = MultiTapeTM.encBool true ↔ f a = true
    exact MultiTapeTM.encBool.apply_eq_iff_eq (f a) true
  constructor
  · intro hfa
    refine ⟨u + 1, (hhalt_M u hhalt).1, ?_⟩
    rw [(hhalt_M u hhalt).2, hout_code, hfa]
  · rintro ⟨s, hhs, houts⟩
    have hmax1 := hstay_M (le_max_left s (u + 1)) hhs
    have hmax2 := hstay_M (le_max_right s (u + 1)) (hhalt_M u hhalt).1
    have heq_out : (M.runCfg O (enc a) s).1.output = (M.runCfg O (enc a) (u + 1)).1.output := by
      rw [← hmax1, hmax2]
    rw [heq_out, (hhalt_M u hhalt).2, hout_code] at houts
    simpa using houts

/-- Every problem in $\mathrm{L}$ lies in $\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}}$ for `k ≥ 2`. -/
theorem L_subset_LModL {k : ℕ} (hk : 2 ≤ k) {α : Type} {enc : α ↪ List Bool} :
    Cslib.Complexity.L enc ⊆ LModL k enc := by
  intro A hA
  let O₀ : Language Bool := (∅ : Set (List Bool))
  have hO₀_L : (O₀ : Set (List Bool)) ∈ Cslib.Complexity.L MultiTapeTM.encBits :=
    ⟨fun _ ↦ false, by fun_prop, fun _ ↦ by simp [O₀]⟩
  exact ⟨O₀, L_subset_ModL hk hO₀_L, L_subset_LOracle O₀ hA⟩

/-- Every oracle language `O : Language Bool` lies in its own $\mathrm{L}^O$ class via a single
query of the input word. -/
theorem self_mem_LOracle (O : Language Bool) :
    (O : Set (List Bool)) ∈ LOracle O MultiTapeTM.encBits := by
  let M : OracleMultiTapeTM 0 (Fin 3) :=
    { q₀ := 0
      tr := fun q sym _ ↦
        match q.val with
        | 0 =>
          match sym with
          | some b => .step .pos Fin.elim0 (some b) 0
          | none => .query 1 2
        | 1 => .halt true
        | _ => .halt false }
  refine ⟨0, Fin 3, inferInstance, M, 0, fun w ↦ ?_⟩
  simp only [MultiTapeTM.encBits_apply]
  have hscan : ∀ j ≤ w.length,
      (M.runCfg O w j).1.state = some 0 ∧
      (M.runCfg O w j).1.inputPos.val = j + 1 ∧
      (M.runCfg O w j).1.output = [] ∧
      (M.runCfg O w j).2 = w.take j := by
    intro j hj
    induction j with
    | zero => simp [M, Cfg.init]
    | succ j ih =>
      obtain ⟨hst, hpos, hout, hbuf⟩ := ih (Nat.le_of_succ_le hj)
      rw [M.runCfg_succ, M.stepCfg_of_state_eq_some O hst]
      have hsym : (M.runCfg O w j).1.inputSymbol = some (w[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      rw [hsym]
      have hM_tr : M.tr 0 (some (w[j]'(by omega))) (M.runCfg O w j).1.workTapeSymbols =
          .step .pos Fin.elim0 (some (w[j]'(by omega))) 0 := rfl
      rw [hM_tr, OracleMultiTapeTM.instrToAction_step]
      refine ⟨rfl, ?_, by simp [hout], ?_⟩
      · simp only [Action.apply_inputPos]
        have hmove := val_moveInputPos_eq (M.runCfg O w j).1.inputPos .pos
        rw [hpos] at hmove
        simp only [SignType.cast] at hmove
        omega
      · rw [hbuf, Option.toList, List.take_succ_eq_append_getElem (by omega)]
  obtain ⟨hst_n, hpos_n, hout_n, hbuf_n⟩ := hscan w.length le_rfl
  rw [List.take_of_length_le le_rfl] at hbuf_n
  classical
  have hq_step :
      (M.runCfg O w (w.length + 1)).1.state =
        some (if w ∈ O then 1 else 2) ∧
      (M.runCfg O w (w.length + 1)).1.output = [] := by
    rw [M.runCfg_succ, M.stepCfg_of_state_eq_some O hst_n]
    have hsym_none : (M.runCfg O w w.length).1.inputSymbol = none :=
      inputSymbol_eq_none_of_boundary (Or.inr hpos_n)
    rw [hsym_none]
    have hM_tr : M.tr 0 none (M.runCfg O w w.length).1.workTapeSymbols = .query 1 2 := rfl
    rw [hM_tr, hbuf_n, OracleMultiTapeTM.instrToAction_query]
    exact ⟨rfl, by simp [hout_n]⟩
  have hhalt_step :
      (M.runCfg O w (w.length + 2)).1.Halted ∧
      (M.runCfg O w (w.length + 2)).1.output = [decide (w ∈ O)] := by
    rw [show w.length + 2 = (w.length + 1) + 1 by omega, M.runCfg_succ,
      M.stepCfg_of_state_eq_some O hq_step.1]
    by_cases hw : w ∈ O
    · rw [ite_eq_left hw]
      have hM_tr : M.tr 1 (M.runCfg O w (w.length + 1)).1.inputSymbol
          (M.runCfg O w (w.length + 1)).1.workTapeSymbols = .halt true := rfl
      rw [hM_tr, OracleMultiTapeTM.instrToAction_halt]
      exact ⟨rfl, by simp [hq_step.2, hw]⟩
    · rw [ite_eq_right hw]
      have hM_tr : M.tr 2 (M.runCfg O w (w.length + 1)).1.inputSymbol
          (M.runCfg O w (w.length + 1)).1.workTapeSymbols = .halt false := rfl
      rw [hM_tr, OracleMultiTapeTM.instrToAction_halt]
      exact ⟨rfl, by simp [hq_step.2, hw]⟩
  have hstay : ∀ {s : ℕ}, w.length + 2 ≤ s →
      M.runCfg O w s = M.runCfg O w (w.length + 2) := by
    intro s hs
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [Nat.add_succ, M.runCfg_succ, ih (Nat.le_add_right _ _)]
      exact M.stepCfg_of_state_eq_none O hhalt_step.1
  refine ⟨fun _ ↦ by simp [RunPath.space], ⟨w.length + 2, hhalt_step.1⟩, ?_⟩
  change w ∈ O ↔ _
  constructor
  · intro hw
    refine ⟨w.length + 2, hhalt_step.1, ?_⟩
    rw [hhalt_step.2]
    simp [hw]
  · rintro ⟨t, hht, hout_t⟩
    rcases lt_or_ge t (w.length + 2) with hlt | hge
    · exfalso
      rcases le_or_gt t w.length with hle | hgt
      · have := (hscan t hle).1
        change (M.runCfg O w t).1.state = none at hht
        rw [this] at hht
        cases hht
      · have heq : t = w.length + 1 := by omega
        subst heq
        change (M.runCfg O w (w.length + 1)).1.state = none at hht
        rw [hq_step.1] at hht
        cases hht
    · rw [hstay hge, hhalt_step.2] at hout_t
      simpa using hout_t

/-- Every language in $\mathrm{Mod}_k\mathrm{L}$ lies in $\mathrm{L}^{\mathrm{Mod}_k\mathrm{L}}$. -/
theorem ModL_encBits_subset_LModL (k : ℕ) :
    Cslib.Complexity.ModL k MultiTapeTM.encBits ⊆ LModL k MultiTapeTM.encBits :=
  fun O hO ↦ ⟨O, hO, self_mem_LOracle O⟩

/-! ### Private sanity check -/

section Sanity

private example (O : Language Bool) : (O : Set (List Bool)) ∈ LOracle O MultiTapeTM.encBits :=
  self_mem_LOracle O

end Sanity

end Cslib.Complexity
