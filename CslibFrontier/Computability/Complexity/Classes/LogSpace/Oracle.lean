/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Modular
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Equivalence

/-!
# Logarithmic space relative to an oracle language and promise logarithmic space

`Cslib.Complexity.LWithOracle B enc` relativizes deterministic logarithmic space
(`Cslib.Complexity.L`) to a single-channel oracle language `B : Set (List Bool)` on
`Turing.MultiTapeMachine k Bool State Unit Id` following the unobstructed space-bounded oracle
convention of [Ruzzo, Simon and Tompa] and [Buntrock, Damm, Hertrampf and
Meinel][BuntrockDammHertrampfMeinel1992]: the read-only input tape, write-only output tape,
write-only query buffer, and read-only answer tape are not charged to work-tape space, while every
prefix of the execution visits at most `c * (Nat.log2 (enc a).length + 1)` cells across the `k`
work tapes.

`Cslib.Complexity.LWithModLOracle k enc` is the union of `LWithOracle B enc` over oracle languages
`B ∈ Cslib.Complexity.ModL k encBits`. Lifting `L` and `LWithModLOracle k` via
`Cslib.Complexity.promiseClass` yields `Cslib.Complexity.PromiseL` and
`Cslib.Complexity.PromiseLWithModLOracle`.

## Main definitions

* `Cslib.Complexity.stepOracle`, `Cslib.Complexity.runOracle`, `Cslib.Complexity.spaceOracle`:
  deterministic single-channel oracle machine step, iterated run, and work-tape cell count.
* `Cslib.Complexity.DecidesInLogSpaceWithOracle`: certification that a finite-control deterministic
  multi-tape oracle machine decides `A` relative to `B` within logarithmic workspace.
* `Cslib.Complexity.LWithOracle`: relativized deterministic logarithmic space `L^B`.
* `Cslib.Complexity.LWithModLOracle`: deterministic logarithmic space with a `ModL k` oracle.
* `Cslib.Complexity.PromiseL`, `Cslib.Complexity.PromiseLWithModLOracle`: promise lifts of `L` and
  `L^{Mod_k L}`.

## Main results

* `Cslib.Complexity.L_subset_LWithOracle`: `L enc ⊆ LWithOracle B enc`.
* `Cslib.Complexity.oracle_mem_LWithOracle`: `B ∈ LWithOracle B encBits`.
* `Cslib.Complexity.compl_mem_LWithOracle`: `LWithOracle B` is closed under complement.
* `Cslib.Complexity.L_subset_LWithModLOracle`, `Cslib.Complexity.ModL_subset_LWithModLOracle`,
  `Cslib.Complexity.compl_mem_LWithModLOracle`.
* `Cslib.Complexity.mem_PromiseL_iff`, `Cslib.Complexity.PromiseL_subset_PromiseLWithModLOracle`,
  `Cslib.Complexity.PromiseL_subset_PromiseP`, `Cslib.Complexity.compl_mem_PromiseL`.
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

section OracleMachine

variable {k : ℕ} {State : Type*}

/-- One deterministic transition of a single-channel multi-tape oracle Turing machine `M` against
an oracle language `B : Set (List Bool)`. -/
noncomputable def stepOracle (M : MultiTapeMachine k Bool State Unit Id)
    (B : Set (List Bool)) (input : List Bool)
    (cfg : MultiTapeMachine.Config k Bool State Unit input) :
    MultiTapeMachine.Config k Bool State Unit input :=
  match cfg.tapes.state with
  | none => cfg
  | some state =>
    match M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
    | .step action symbol move => cfg.step action symbol move
    | .query _ next =>
      cfg.receive () next [@decide ((cfg.channels ()).queryBuffer ∈ B) (Classical.propDecidable _)]

/-- Configuration of `M` against oracle `B` on `input` after `n` deterministic steps. -/
noncomputable def runOracle (M : MultiTapeMachine k Bool State Unit Id)
    (B : Set (List Bool)) (input : List Bool) (n : ℕ) :
    MultiTapeMachine.Config k Bool State Unit input :=
  (stepOracle M B input)^[n] (M.initialConfig input)

@[simp]
theorem runOracle_zero (M : MultiTapeMachine k Bool State Unit Id)
    (B : Set (List Bool)) (input : List Bool) :
    runOracle M B input 0 = M.initialConfig input := by
  unfold runOracle
  rfl

theorem runOracle_succ (M : MultiTapeMachine k Bool State Unit Id)
    (B : Set (List Bool)) (input : List Bool) (n : ℕ) :
    runOracle M B input (n + 1) = stepOracle M B input (runOracle M B input n) :=
  Function.iterate_succ_apply' _ _ _

private theorem stepOracle_of_none {M : MultiTapeMachine k Bool State Unit Id}
    {B : Set (List Bool)} {input : List Bool}
    {cfg : MultiTapeMachine.Config k Bool State Unit input}
    (h : cfg.tapes.state = none) :
    stepOracle M B input cfg = cfg := by
  simp [stepOracle, h]

private theorem stepOracle_of_state {M : MultiTapeMachine k Bool State Unit Id}
    {B : Set (List Bool)} {input : List Bool}
    {cfg : MultiTapeMachine.Config k Bool State Unit input} {q : State}
    (hq : cfg.tapes.state = some q) :
    stepOracle M B input cfg =
      match M.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
      | .step action symbol move => cfg.step action symbol move
      | .query _ next =>
        cfg.receive () next
          [@decide ((cfg.channels ()).queryBuffer ∈ B) (Classical.propDecidable _)] := by
  simp [stepOracle, hq]

/-- Number of distinct work-tape cells visited across all work tapes during the first `t` steps of
`M` against oracle `B` on `input`. -/
noncomputable def spaceOracle (M : MultiTapeMachine k Bool State Unit Id)
    (B : Set (List Bool)) (input : List Bool) (t : ℕ) : ℕ :=
  ∑ i : Fin k,
    ((Finset.range (t + 1)).image fun n ↦ (runOracle M B input n).tapes.workTapePos i).card

@[simp]
theorem spaceOracle_zero_tapes {State : Type*} (M : MultiTapeMachine 0 Bool State Unit Id)
    (B : Set (List Bool)) (input : List Bool) (t : ℕ) :
    spaceOracle M B input t = 0 := by
  simp [spaceOracle]

/-- A finite-state deterministic multi-tape oracle machine `M` decides `A` in logarithmic space
relative to `B`. -/
@[expose]
def DecidesInLogSpaceWithOracle {α : Type*} (M : MultiTapeMachine k Bool State Unit Id)
    (B : Set (List Bool)) (enc : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ c : ℕ, ∀ a : α,
    (∃ u : ℕ, (runOracle M B (enc a) u).tapes.state = none ∧
      (runOracle M B (enc a) u).tapes.output = [@decide (a ∈ A) (Classical.propDecidable _)]) ∧
    ∀ t : ℕ, spaceOracle M B (enc a) t ≤ c * (Nat.log2 (enc a).length + 1)

/-- The relativized deterministic logarithmic-space class `L^B`. -/
@[expose]
def LWithOracle {α : Type} (B : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapeMachine k Bool State Unit Id),
    DecidesInLogSpaceWithOracle M B enc A}

/-- Embed an ordinary deterministic `MultiTapeTM` into a single-channel oracle machine that never
queries the oracle. -/
noncomputable def liftTM {k : ℕ} {State : Type*} (tm : MultiTapeTM k Bool State) :
    MultiTapeMachine k Bool State Unit Id where
  initial := tm.q₀
  tr state sym work _ := .step (tm.tr state sym work) (fun _ ↦ none) (fun _ ↦ 0)

private theorem liftTM_tr {k : ℕ} {State : Type*} (tm : MultiTapeTM k Bool State)
    (state : State) (sym : Option Bool) (work : Fin k → Option Bool)
    (ans : Unit → Option Bool) :
    (liftTM tm).tr state sym work ans =
      .step (tm.tr state sym work) (fun _ ↦ none) (fun _ ↦ 0) :=
  rfl

private theorem runOracle_liftTM_tapes {k : ℕ} {State : Type*} (tm : MultiTapeTM k Bool State)
    (B : Set (List Bool)) (input : List Bool) (n : ℕ) :
    (runOracle (liftTM tm) B input n).tapes = tm.runFrom (tm.initCfg input) n := by
  induction n with
  | zero =>
    rw [runOracle_zero]
    rfl
  | succ n ih =>
    rw [runOracle_succ, MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom]
    cases hs : (runOracle (liftTM tm) B input n).tapes.state with
    | none =>
      have hs' : (tm.runFrom (tm.initCfg input) n).state = none := ih ▸ hs
      rw [stepOracle_of_none hs, ih, tm.step_of_halt hs']
    | some q =>
      have hs' : (tm.runFrom (tm.initCfg input) n).state = some q := ih ▸ hs
      rw [stepOracle_of_state hs, liftTM_tr]
      dsimp only [MultiTapeMachine.Config.step]
      rw [ih]
      exact (tm.step_of_state hs').symm

private theorem spaceOracle_liftTM_le {k : ℕ} {State : Type*} (tm : MultiTapeTM k Bool State)
    (B : Set (List Bool)) (input : List Bool) (t : ℕ) :
    spaceOracle (liftTM tm) B input t ≤
      (MultiTapeNTM.ComputationPath.ofDeterministic tm input t).space := by
  classical
  let cp := MultiTapeNTM.ComputationPath.ofDeterministic tm input t
  unfold spaceOracle MultiTapeNTM.ComputationPath.space MultiTapeNTM.RunPath.space
    MultiTapeNTM.RunPath.spaceUsedByTape
  refine Finset.sum_le_sum fun i _ ↦ Finset.card_le_card ?_
  intro z hz
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
  rw [runOracle_liftTM_tapes]
  have hlt : n < cp.toRunPath.length + 1 := Finset.mem_range.mp hn
  rw [MultiTapeNTM.RunPath.mem_visitedByTapeHead]
  exact ⟨cp.toRunPath ⟨n, hlt⟩, ⟨⟨n, hlt⟩, rfl⟩, rfl⟩

/-- **Deterministic logarithmic space is contained in `L^B`** for every oracle language `B`. -/
theorem L_subset_LWithOracle {α : Type} (B : Set (List Bool)) (enc : α ↪ List Bool) :
    L enc ⊆ LWithOracle B enc := by
  classical
  rintro A ⟨f, ⟨t, c, k, State, hFin, tm, htm⟩, hA⟩
  refine ⟨k, State, hFin, liftTM tm, c, fun a ↦ ?_⟩
  have ha := htm a
  obtain ⟨u, hu_halt, hu_out⟩ := ha.1
  refine ⟨⟨u, ?_, ?_⟩, fun n ↦ ?_⟩
  · rw [runOracle_liftTM_tapes]
    exact hu_halt
  · rw [runOracle_liftTM_tapes, hu_out]
    simp [encBool_apply, hA a]
  · exact (spaceOracle_liftTM_le tm B (enc a) n).trans
      (ha.2.2 (MultiTapeNTM.ComputationPath.ofDeterministic tm (enc a) n))

private def oracleForwardMachine : MultiTapeMachine 0 Bool Bool Unit Id where
  initial := false
  tr state inputSym _ ansSym :=
    match state, inputSym with
    | false, some b =>
      .step ⟨.pos, Fin.elim0, none, some false⟩ (fun _ ↦ some b) (fun _ ↦ 0)
    | false, none =>
      .query () true
    | true, _ =>
      .step ⟨0, Fin.elim0, some ((ansSym ()).getD false), none⟩ (fun _ ↦ none) (fun _ ↦ 0)

private theorem oracleForwardMachine_tr_copy_some (b : Bool) (w : Fin 0 → Option Bool)
    (ans : Unit → Option Bool) :
    oracleForwardMachine.tr false (some b) w ans =
      .step ⟨.pos, Fin.elim0, none, some false⟩ (fun _ ↦ some b) (fun _ ↦ 0) :=
  rfl

private theorem oracleForwardMachine_tr_copy_none (w : Fin 0 → Option Bool)
    (ans : Unit → Option Bool) :
    oracleForwardMachine.tr false none w ans = .query () true :=
  rfl

private theorem oracleForwardMachine_tr_emit (inp : Option Bool) (w : Fin 0 → Option Bool)
    (ans : Unit → Option Bool) :
    oracleForwardMachine.tr true inp w ans =
      .step ⟨0, Fin.elim0, some ((ans ()).getD false), none⟩ (fun _ ↦ none) (fun _ ↦ 0) :=
  rfl

private theorem runOracle_oracleForwardMachine_copy (B : Set (List Bool)) (input : List Bool) :
    ∀ j ≤ input.length,
      (runOracle oracleForwardMachine B input j).tapes.state = some false ∧
      ((runOracle oracleForwardMachine B input j).tapes.inputPos : ℕ) = 1 + j ∧
      (runOracle oracleForwardMachine B input j).tapes.output = [] ∧
      ((runOracle oracleForwardMachine B input j).channels ()).queryBuffer = input.take j := by
  intro j hj
  induction j with
  | zero =>
    rw [runOracle_zero]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨hst, hpos, hout, hbuf⟩ := ih (Nat.le_of_succ_le hj)
    have hlt : j < input.length := hj
    have hsym : (runOracle oracleForwardMachine B input j).tapes.inputSymbol = some input[j] :=
      inputSymbolInner j hpos hlt
    rw [runOracle_succ, stepOracle_of_state hst, hsym, oracleForwardMachine_tr_copy_some]
    have hne_right : ((runOracle oracleForwardMachine B input j).tapes.inputPos : ℕ) ≠
        input.length + 1 := by omega
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp only [MultiTapeMachine.Config.step, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ hne_right]
      dsimp only
      omega
    · simp [MultiTapeMachine.Config.step, Action.apply, hout]
    · change ((runOracle oracleForwardMachine B input j).channels ()).queryBuffer ++ [input[j]] =
        input.take (j + 1)
      rw [hbuf, List.take_succ_eq_append_getElem hlt]

/-- **Every oracle language `B` belongs to `L^B` on raw bit strings `encBits`.** -/
theorem oracle_mem_LWithOracle (B : Set (List Bool)) :
    B ∈ LWithOracle B encBits := by
  classical
  refine ⟨0, Bool, inferInstance, oracleForwardMachine, 0, fun w ↦ ?_⟩
  refine ⟨⟨w.length + 2, ?_⟩, fun t ↦ by simp⟩
  rw [encBits_apply]
  obtain ⟨hst, hpos, hout, hbuf⟩ :=
    runOracle_oracleForwardMachine_copy B w w.length le_rfl
  rw [List.take_length] at hbuf
  have hsym_end : (runOracle oracleForwardMachine B w w.length).tapes.inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (.inr (by omega))
  have hstep1 : runOracle oracleForwardMachine B w (w.length + 1) =
      (runOracle oracleForwardMachine B w w.length).receive () true [decide (w ∈ B)] := by
    rw [runOracle_succ, stepOracle_of_state hst, hsym_end, oracleForwardMachine_tr_copy_none, hbuf]
  have hst1 : (runOracle oracleForwardMachine B w (w.length + 1)).tapes.state = some true := by
    rw [hstep1]; rfl
  have hout1 : (runOracle oracleForwardMachine B w (w.length + 1)).tapes.output = [] := by
    rw [hstep1]; exact hout
  have hans1 : (runOracle oracleForwardMachine B w (w.length + 1)).answerSymbols () =
      some (decide (w ∈ B)) := by
    rw [hstep1]
    simp [MultiTapeMachine.Config.receive, MultiTapeMachine.Config.answerSymbols,
      MultiTapeMachine.Channel.answerSymbol]
  rw [show w.length + 2 = (w.length + 1) + 1 by omega, runOracle_succ, stepOracle_of_state hst1,
    oracleForwardMachine_tr_emit]
  simp [MultiTapeMachine.Config.step, Action.apply, hans1, hout1]

private def negateOutputMachine {k : ℕ} {State : Type*}
    (M : MultiTapeMachine k Bool State Unit Id) :
    MultiTapeMachine k Bool State Unit Id where
  initial := M.initial
  tr state inputSym workSym ansSym :=
    match M.tr state inputSym workSym ansSym with
    | .step act qSym aMove =>
      .step { act with output := act.output.map Bool.not } qSym aMove
    | .query u next => .query u next

private theorem negateOutputMachine_tr {k : ℕ} {State : Type*}
    (M : MultiTapeMachine k Bool State Unit Id) (q : State) (inp : Option Bool)
    (work : Fin k → Option Bool) (ans : Unit → Option Bool) :
    (negateOutputMachine M).tr q inp work ans =
      match M.tr q inp work ans with
      | .step act qSym aMove =>
        .step { act with output := act.output.map Bool.not } qSym aMove
      | .query u next => .query u next :=
  rfl

private theorem runOracle_negateOutputMachine {k : ℕ} {State : Type*}
    (M : MultiTapeMachine k Bool State Unit Id) (B : Set (List Bool)) (input : List Bool) (n : ℕ) :
    (runOracle (negateOutputMachine M) B input n).tapes.state =
        (runOracle M B input n).tapes.state ∧
      (runOracle (negateOutputMachine M) B input n).tapes.inputPos =
        (runOracle M B input n).tapes.inputPos ∧
      (runOracle (negateOutputMachine M) B input n).tapes.workTapes =
        (runOracle M B input n).tapes.workTapes ∧
      (runOracle (negateOutputMachine M) B input n).tapes.workTapePos =
        (runOracle M B input n).tapes.workTapePos ∧
      (runOracle (negateOutputMachine M) B input n).channels =
        (runOracle M B input n).channels ∧
      (runOracle (negateOutputMachine M) B input n).tapes.output =
        ((runOracle M B input n).tapes.output).map Bool.not := by
  induction n with
  | zero =>
    rw [runOracle_zero, runOracle_zero]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hst, hpos, hwt, hwpos, hch, hout⟩ := ih
    rw [runOracle_succ, runOracle_succ]
    cases hs : (runOracle M B input n).tapes.state with
    | none =>
      rw [stepOracle_of_none (hst.trans hs), stepOracle_of_none hs]
      exact ⟨hst, hpos, hwt, hwpos, hch, hout⟩
    | some q =>
      rw [stepOracle_of_state (hst.trans hs), stepOracle_of_state hs]
      have hinp : (runOracle (negateOutputMachine M) B input n).tapes.inputSymbol =
          (runOracle M B input n).tapes.inputSymbol := by
        simp [Cfg.inputSymbol, hpos]
      have hwsym : (runOracle (negateOutputMachine M) B input n).tapes.workTapeSymbols =
          (runOracle M B input n).tapes.workTapeSymbols := by
        ext i; simp [Cfg.workTapeSymbols, hwt, hwpos]
      have hasym : (runOracle (negateOutputMachine M) B input n).answerSymbols =
          (runOracle M B input n).answerSymbols := by
        ext u; simp [MultiTapeMachine.Config.answerSymbols, hch]
      rw [hinp, hwsym, hasym, negateOutputMachine_tr]
      cases M.tr q (runOracle M B input n).tapes.inputSymbol
          (runOracle M B input n).tapes.workTapeSymbols
          (runOracle M B input n).answerSymbols with
      | step act qSym aMove =>
        dsimp only
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
        · simp [MultiTapeMachine.Config.step, Action.apply, hpos]
        · ext i z; simp [MultiTapeMachine.Config.step, Action.apply, hwt, hwpos]
        · ext i; simp [MultiTapeMachine.Config.step, Action.apply, hwpos]
        · simp only [MultiTapeMachine.Config.step, hch]
        · dsimp only [MultiTapeMachine.Config.step, Action.apply]
          rw [hout, List.map_append]
          cases act.output <;> rfl
      | query u next =>
        dsimp only [MultiTapeMachine.Config.receive]
        refine ⟨rfl, hpos, hwt, hwpos, ?_, hout⟩
        rw [hch]

/-- **`L^B` is closed under complement** for every oracle language `B`. -/
theorem compl_mem_LWithOracle {α : Type} {B : Set (List Bool)} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ LWithOracle B enc) : Aᶜ ∈ LWithOracle B enc := by
  classical
  obtain ⟨k, State, hFin, M, c, hM⟩ := hA
  refine ⟨k, State, hFin, negateOutputMachine M, c, fun a ↦ ?_⟩
  obtain ⟨⟨u, hu_halt, hu_out⟩, hspace⟩ := hM a
  have hneg := runOracle_negateOutputMachine M B (enc a) u
  refine ⟨⟨u, hneg.1.trans hu_halt, ?_⟩, fun t ↦ ?_⟩
  · rw [hneg.2.2.2.2.2, hu_out]
    by_cases ha : a ∈ A <;> simp [ha]
  · have hsp : spaceOracle (negateOutputMachine M) B (enc a) t = spaceOracle M B (enc a) t := by
      unfold spaceOracle
      congr 1; funext i; congr 1; congr 1; funext n
      exact congrFun (runOracle_negateOutputMachine M B (enc a) n).2.2.2.1 i
    rw [hsp]
    exact hspace t

/-- **`L^{Mod_k L}`**: languages decidable in deterministic logarithmic space relative to some
oracle language `B ∈ ModL k encBits`. -/
@[expose]
def LWithModLOracle {α : Type} (k : ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ B ∈ ModL k encBits, A ∈ LWithOracle B enc}

/-- `ModL k` is nonempty for every `k`: the empty language has zero `#L` count. -/
theorem empty_mem_ModL (k : ℕ) {α : Type} (enc : α ↪ List Bool) :
    (∅ : Set α) ∈ ModL k enc := by
  have hzero : (fun _ : α ↦ 0) ∈ SharpL enc := by
    let M : MultiTapeCTM 0 Bool Unit :=
      { initial := ()
        tr := fun _ _ _ _ ↦ [.step ⟨0, Fin.elim0, some false, none⟩ Empty.elim Empty.elim] }
    refine ⟨0, Unit, inferInstance, M, 0, fun a ↦ ⟨by simp, 1, ?_, ?_⟩⟩
    · have hact : M.actions (Cfg.init M.initial (enc a)) =
          [⟨0, Fin.elim0, some false, none⟩] := rfl
      refine .step (by rw [hact]; exact List.cons_ne_nil _ _) fun idx ↦ .halt ?_
      rcases idx with ⟨val, hlt⟩
      have hval : val = 0 := by rw [hact] at hlt; exact Nat.lt_one_iff.mp hlt
      subst hval
      rfl
    · symm
      rw [MultiTapeCTM.acceptCount, MultiTapeCTM.branchCount, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro choices hmem
      cases choices with
      | nil =>
        have hh := (M.nil_mem_branches _ _).mp hmem
        simp [Cfg.init, Cfg.Halted] at hh
      | cons i rest =>
        obtain ⟨next, hstep, hrest⟩ := (M.cons_mem_branches _ 0 i rest).mp hmem
        have hact : M.actions (Cfg.init M.initial (enc a)) =
            [⟨0, Fin.elim0, some false, none⟩] := rfl
        obtain ⟨hi, hnext⟩ := (M.step?_eq_some_iff _ _ _).mp hstep
        have hi0 : i = 0 := by rw [hact] at hi; exact Nat.lt_one_iff.mp hi
        subst hi0
        have hlen0 : rest.length ≤ 0 := ((M.mem_branches_iff _ 0 rest).mp hrest).1
        have hrest_nil : rest = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen0)
        subst hrest_nil
        have hnext' : next = (⟨0, Fin.elim0, some false, none⟩ : Action 0 Bool Unit).apply
            (Cfg.init M.initial (enc a)) := by
          rw [← hnext]
          simp only [hact, List.getElem_cons_zero]
        rw [M.runBranch_cons, hstep, Option.bind_some, M.runBranch_nil, hnext']
        simp [Action.apply, Cfg.init]
  exact ⟨fun _ ↦ 0, hzero, fun _ ↦ by simp⟩

/-- **Deterministic logarithmic space is contained in `L^{Mod_k L}`** for every modulus `k`. -/
theorem L_subset_LWithModLOracle {α : Type} (k : ℕ) (enc : α ↪ List Bool) :
    L enc ⊆ LWithModLOracle k enc := fun _ hA ↦
  ⟨∅, empty_mem_ModL k encBits, L_subset_LWithOracle ∅ enc hA⟩

/-- **`Mod_k L` on bit strings is contained in `L^{Mod_k L}`.** -/
theorem ModL_subset_LWithModLOracle (k : ℕ) :
    ModL k encBits ⊆ LWithModLOracle k encBits := fun B hB ↦
  ⟨B, hB, oracle_mem_LWithOracle B⟩

/-- **`L^{Mod_k L}` is closed under complement.** -/
theorem compl_mem_LWithModLOracle {α : Type} {k : ℕ} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ LWithModLOracle k enc) : Aᶜ ∈ LWithModLOracle k enc := by
  obtain ⟨B, hB, hAB⟩ := hA
  exact ⟨B, hB, compl_mem_LWithOracle hAB⟩

end OracleMachine

section PromiseLogSpace

/-- **Promise-L**: promise problems solved in deterministic logarithmic space. -/
@[expose]
def PromiseL {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  promiseClass (L enc)

/-- **Promise-`L^{Mod_k L}`**: promise problems solved by a deterministic logspace Turing machine
with access to an oracle in `ModL k`. -/
@[expose]
def PromiseLWithModLOracle {α : Type} (k : ℕ) (enc : α ↪ List Bool) :
    Set (PromiseProblem α) :=
  promiseClass (LWithModLOracle k enc)

/-- **Goldreich's characterization of `PromiseL`**. -/
theorem mem_PromiseL_iff {α : Type} {enc : α ↪ List Bool} {Q : PromiseProblem α} :
    Q ∈ PromiseL enc ↔ ∃ f : α → Bool, ComputableInLogSpace f enc encBool ∧ Q.SolvedBy f :=
  mem_promiseClass_iff_solvedBy fun _ ↦ Iff.rfl

@[simp]
theorem ofSet_mem_PromiseL {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    PromiseProblem.ofSet A ∈ PromiseL enc ↔ A ∈ L enc :=
  ofSet_mem_promiseClass

/-- **`PromiseL` is contained in `PromiseLWithModLOracle k`** for every modulus `k`. -/
theorem PromiseL_subset_PromiseLWithModLOracle {α : Type} (k : ℕ) (enc : α ↪ List Bool) :
    PromiseL enc ⊆ PromiseLWithModLOracle k enc :=
  promiseClass_mono (L_subset_LWithModLOracle k enc)

/-- **`PromiseL` is contained in `PromiseP`.** -/
theorem PromiseL_subset_PromiseP {α : Type} (enc : α ↪ List Bool) :
    PromiseL enc ⊆ PromiseP enc :=
  promiseClass_mono L_subset_P

/-- **`PromiseL` is closed under complement.** -/
theorem compl_mem_PromiseL {α : Type} {enc : α ↪ List Bool} {Q : PromiseProblem α}
    (hQ : Q ∈ PromiseL enc) : Qᶜ ∈ PromiseL enc :=
  compl_mem_promiseClass (fun _ ↦ compl_mem_L) hQ

end PromiseLogSpace

end Cslib.Complexity
