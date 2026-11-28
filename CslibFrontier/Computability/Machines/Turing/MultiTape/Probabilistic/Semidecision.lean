module


public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Foundations.Data.Nat.LogStar
public import CslibFrontier.Languages.Probabilistic.Iteration
public import Mathlib.Algebra.Polynomial.Eval.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.IterateWhileLayout
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelIterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.Oracle.Normalization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.Oracle.Phase
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PrepareReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Composition.ExpectedTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExpectedTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.HaltedReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop.ExpectedTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential.CoinTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy.Redirect
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run.FirstStep
import CslibFrontier.Computability.Machines.Turing.MultiTape.Tactic.Step
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Foundations.Data.Fin.Tuple
import CslibFrontier.Probability.Option
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Native Multi-Tape PTM Primitives for Randomized Semidecision Procedures

This module provides three reusable native `Turing.MultiTapePTM` building blocks for
randomized semidecision procedures and saved-coin replay:

1. `computableInPolyTime_logStar`: `Nat.logStar` is computable in polynomial time in unary.
2. Tagged saved-coin replay (`replayTagOutput`, `replayHaltedAccept`): deterministic linear-time
   replay of any finite-state `MultiTapePTM k Bool State` that appends its final halted flag
   `state.isNone` to the emitted output word.
3. Unbounded round-by-round randomized semidecision machines (`hitProb`,
   `exists_semidecision_machine`): compiling any `IsPPTOn` round transition
   `round : σ → ProbComp (Option σ)` (where `none` denotes acceptance and halting) with a
   polynomially bounded reachable-state size invariant into a single fixed fair-coin
   `MultiTapePTM` via `Turing.MultiTapePTM.iterateWhile`, with exact eventual halting probability
   and polynomial per-round step overhead.
-/

public section

namespace CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic

open Cslib Cslib.Probability
open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
open _root_.Turing.MultiTapePTM _root_.Turing.MultiTapePTM.Internal.Oracle
open scoped ENNReal

/-! ### Polynomial-time computability of `Nat.logStar` -/

private theorem clog_two_lt_self {n : ℕ} (hn : 2 ≤ n) : Nat.clog 2 n < n := by
  have hle : Nat.clog 2 n ≤ n - 1 := (Nat.clog_le_iff_le_pow (by decide)).2
    (by have := Nat.lt_two_pow_self (n := n - 1); omega)
  omega

/-- The iterated logarithm `Nat.logStar` is computable in polynomial time on unary counters. -/
theorem computableInPolyTime_logStar :
    ComputableInPolyTime Nat.logStar encUnary encUnary := by
  let step (state : ℕ × ℕ) : ℕ × ℕ :=
    if state.1 ≤ 1 then state else (Nat.clog 2 state.1, state.2 + 1)
  have hstep : ComputableInPolyTime step (encPair encUnary encUnary)
      (encPair encUnary encUnary) := by
    unfold step
    fun_prop
  obtain ⟨heff, hspec⟩ := ComputableInPolyTime.iterate_spec
    (count := id) (init := fun n => (n, 0)) (encIn := encUnary)
    ComputableInPolyTime.id' (by fun_prop) hstep
    (fun n i state => state.1 ≤ n ∧ state.2 ≤ i ∧
      (state.1 ≤ 1 ∨ state.1 + i ≤ n) ∧
      Nat.logStar state.1 + state.2 = Nat.logStar n)
    (fun _ => by simp)
    (fun n i state _ h => by
      dsimp only [step]
      split
      · rename_i hle
        exact ⟨h.1, by omega, Or.inl hle, h.2.2.2⟩
      · rename_i hgt
        have h2 : 2 ≤ state.1 := by omega
        have hdrop : Nat.clog 2 state.1 < state.1 := clog_two_lt_self h2
        have hprog : state.1 + i ≤ n := h.2.2.1.resolve_left hgt
        have hls : Nat.logStar state.1 = Nat.logStar (Nat.clog 2 state.1) + 1 :=
          Nat.logStar_of_two_le h2
        dsimp only
        exact ⟨hdrop.le.trans h.1, by omega, Or.inr (by omega), by omega⟩)
    (size := fun n => 3 * n + 1)
    (ComputableInPolyTime.polyBounded (by fun_prop))
    (fun _ _ _ hi h => by
      simp only [length_encPair, encUnary_apply, List.length_replicate, id_eq] at hi ⊢
      omega)
  have hres (n : ℕ) : (step^[n] (n, 0)).2 = Nat.logStar n := by
    have h := hspec n
    have hle1 : (step^[n] (n, 0)).1 ≤ 1 := by
      rcases h.2.2.1 with h1 | h1 <;> simp only [id_eq] at * <;> omega
    simpa only [id_eq, Nat.logStar_of_le_one hle1, zero_add] using h.2.2.2
  simpa only [Function.comp_def, id_eq, hres] using heff.snd'

/-! ### Linear-time tagged saved-coin replay (`output ++ [state.isNone]`) -/

/-- Output of a saved-coin replay tagged with a trailing halted bit (`true` iff the machine
reached `state = none`). -/
def replayTagOutput {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)
    (coins input : List Bool) : List Bool :=
  let cfg := machine.runClosedConfigFromCoins coins (machine.initialConfig input)
  cfg.tapes.output ++ [cfg.tapes.state.isNone]

/-- Explicit expansion of `replayTagOutput`. -/
theorem replayTagOutput_eq {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)
    (coins input : List Bool) :
    replayTagOutput machine coins input =
      (machine.runClosedConfigFromCoins coins (machine.initialConfig input)).tapes.output ++
        [(machine.runClosedConfigFromCoins coins
          (machine.initialConfig input)).tapes.state.isNone] := by
  rfl

/-- Whether `machine` halts with output `[true]` on `input` under saved `coins`. -/
def replayHaltedAccept {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)
    (coins input : List Bool) : Bool :=
  let cfg := machine.runClosedConfigFromCoins coins (machine.initialConfig input)
  cfg.tapes.state.isNone && decide (cfg.tapes.output = [true])

/-- `replayHaltedAccept` is equivalent to `replayTagOutput` equaling `[true, true]`. -/
theorem replayHaltedAccept_iff_replayTagOutput {k : ℕ} {State : Type}
    (machine : MultiTapePTM k Bool State) (coins input : List Bool) :
    replayHaltedAccept machine coins input =
      decide (replayTagOutput machine coins input = [true, true]) := by
  unfold replayHaltedAccept replayTagOutput
  generalize machine.runClosedConfigFromCoins coins (machine.initialConfig input) = cfg
  rcases hst : cfg.tapes.state with _ | s
  · simp only [hst, Option.isNone_none, Bool.true_and]
    by_cases hout : cfg.tapes.output = [true]
    · simp [hout]
    · have hne : cfg.tapes.output ++ [true] ≠ [true, true] := by
        intro h
        exact hout (List.append_inj_left' h rfl)
      simp [hout, hne]
  · simp only [hst, Option.isNone_some, Bool.false_and]
    have hne : cfg.tapes.output ++ [false] ≠ [true, true] := by
      intro h
      have hlast := congrArg List.getLast? h
      simp at hlast
    simp [hne]

/-- `replayHaltedAccept` holds iff the replayed configuration halted with output `[true]`. -/
theorem replayHaltedAccept_eq_true_iff {k : ℕ} {State : Type}
    (machine : MultiTapePTM k Bool State) (coins input : List Bool) :
    replayHaltedAccept machine coins input = true ↔
      (machine.runClosedConfigFromCoins coins (machine.initialConfig input)).tapes.state = none ∧
      (machine.runClosedConfigFromCoins coins (machine.initialConfig input)).tapes.output =
        [true] := by
  simp [replayHaltedAccept, Option.isNone_iff_eq_none]

section ReplayTag

variable {k r : ℕ} {State PrepareState : Type}

private def replayTagStop (halted : Bool) : Turing.Action (k + 1) Bool (Option State) where
  inputTape := 0
  workTapes := Fin.lastCases (none, 0) (fun _ => (none, 0))
  output := some halted
  state := none

private def replayTag (machine : MultiTapePTM k Bool State) :
    MultiTapeTM (k + 1) Bool (Option State) :=
  MultiTapeTM.ofTr (some machine.initial) fun state symbol work =>
    match work (Fin.last k) with
    | none => replayTagStop state.isNone
    | some bit => match state with
      | none => Replay.idle (some none) 1
      | some state => Replay.liftAction
          (Action.emptyOracleEquiv
            (machine.tr state symbol (fun i => work i.castSucc) Empty.elim bit))

private def replayTagStopped {input : List Bool}
    (cfg : Config k Bool State Empty input) (tape : ℤ → Option Bool) (position : ℤ) :
    Cfg (k + 1) Bool (Option State) input :=
  { Replay.stopped cfg tape position with output := cfg.tapes.output ++ [cfg.tapes.state.isNone] }

private theorem apply_replayTagStop {input : List Bool}
    (cfg : Config k Bool State Empty input) (tape : ℤ → Option Bool) (position : ℤ) :
    (replayTagStop (k := k) (State := State) cfg.tapes.state.isNone).apply
        (Replay.config cfg tape position) =
      replayTagStopped cfg tape position := by
  tm_step [replayTagStop, replayTagStopped, Replay.stopped, Replay.config]

private theorem replayTag_step_some {input : List Bool}
    (machine : MultiTapePTM k Bool State) (cfg : Config k Bool State Empty input)
    (tape : ℤ → Option Bool) (position : ℤ) (bit : Bool) (hcell : tape position = some bit) :
    (replayTag machine).step (Replay.config cfg tape position) =
      Replay.config ((machine.withCoin bit).step cfg) tape (position + 1) := by
  rw [MultiTapeTM.step_of_state (show (Replay.config cfg tape position).state =
    some cfg.tapes.state from rfl)]
  have hread : cfg.answerSymbols = Empty.elim := funext fun oracle => oracle.elim
  simp only [replayTag, MultiTapeTM.tr_ofTr, Replay.config_inputSymbol,
    Replay.config_workTapeSymbols_last, hcell, Replay.config_workTapeSymbols_castSucc,
    MultiTapeMachine.step, withCoin]
  cases hs : cfg.tapes.state with
  | none => simpa only [hs] using Replay.apply_tick cfg tape position
  | some state =>
    simp only [hread]
    cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols Empty.elim bit with
    | step action symbol move => exact Replay.apply_liftAction cfg tape position action symbol move
    | query oracle _ => exact oracle.elim

private theorem replayTag_step_none {input : List Bool}
    (machine : MultiTapePTM k Bool State) (cfg : Config k Bool State Empty input)
    (tape : ℤ → Option Bool) (position : ℤ) (hcell : tape position = none) :
    (replayTag machine).step (Replay.config cfg tape position) =
      replayTagStopped cfg tape position := by
  rw [MultiTapeTM.step_of_state (show (Replay.config cfg tape position).state =
    some cfg.tapes.state from rfl)]
  simpa only [replayTag, MultiTapeTM.tr_ofTr, Replay.config_workTapeSymbols_last, hcell] using
    apply_replayTagStop cfg tape position

private theorem runFrom_replayTag_coins {input : List Bool}
    (machine : MultiTapePTM k Bool State) (cfg : Config k Bool State Empty input)
    (coins : List Bool) (tape : ℤ → Option Bool) (position : ℤ)
    (hcoins : ∀ i : ℕ, i < coins.length → tape (position + i) = coins[i]?)
    (hstop : tape (position + coins.length) = none) :
    (replayTag machine).runFrom (Replay.config cfg tape position) (coins.length + 1) =
      replayTagStopped (machine.runClosedConfigFromCoins coins cfg) tape
        (position + coins.length) := by
  induction coins generalizing cfg position with
  | nil =>
    simpa [MultiTapeTM.runFrom_one, runClosedConfigFromCoins] using
      replayTag_step_none machine cfg tape position (by simpa using hstop)
  | cons bit coins ih =>
    have hcell : tape position = some bit := by simpa using hcoins 0 (by simp)
    have htail (i : ℕ) (hi : i < coins.length) : tape (position + 1 + i) = coins[i]? := by
      have h := hcoins (i + 1) (by simp only [List.length_cons]; omega)
      simpa [Int.natCast_add, add_assoc, add_comm, add_left_comm] using h
    have hend : tape (position + 1 + coins.length) = none := by
      simpa [add_assoc, add_comm, add_left_comm] using hstop
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step,
      replayTag_step_some machine cfg tape position bit hcell, ih _ _ htail hend]
    simp [runClosedConfigFromCoins, add_comm, add_left_comm]

private theorem runFrom_replayTag (machine : MultiTapePTM k Bool State)
    (coins input : List Bool) :
    (replayTag machine).runFrom
        (Replay.config (machine.initialConfig input) (tapeOfList coins) 0) (coins.length + 1) =
      replayTagStopped (machine.runClosedConfigFromCoins coins (machine.initialConfig input))
        (tapeOfList coins) coins.length := by
  simpa using runFrom_replayTag_coins machine (machine.initialConfig input) coins
    (tapeOfList coins) 0 (by intros; simp) (by simp)

private def replayTapes (k r : ℕ) : Fin (k + 1) ↪ Fin (k + r + 1) :=
  Fin.Embedding.snoc ((Fin.castAddEmb r).trans Fin.castSuccEmb)
    (a := Fin.last (k + r)) (by
    rintro ⟨i, h⟩
    have : (i : ℕ) = k + r := congrArg Fin.val h
    omega)

private theorem replayTag_embed_initial (machine : MultiTapePTM k Bool State)
    (coins input : List Bool) :
    embed (replayTapes k r) (Replay.config (machine.initialConfig input) (tapeOfList coins) 0)
      (fun _ _ => none) (fun _ => 0) =
      MultiTapeTM.ReplayInput.initial k r coins input (some (some machine.initial)) := by
  have hcfg : Replay.config (machine.initialConfig input) (tapeOfList coins) 0 =
      wordsCfg input (some (some machine.initial)) (Fin.snoc (fun _ => []) coins) [] := by
    tm_step [Replay.config, MultiTapeMachine.initialConfig]
  rw [hcfg]
  simpa only [MultiTapeTM.ReplayInput.initial, tapeOfList_nil] using
    embed_wordsCfg (input := input) (replayTapes k r)
      (ws := fun _ => []) (q := some (some machine.initial)) (out := [])
      (v := Fin.snoc (fun _ => []) coins) (ws' := Fin.snoc (fun _ => []) coins)
      (fun j => by induction j using Fin.lastCases <;>
        simp [replayTapes, Fin.Embedding.snoc_last, Fin.Embedding.snoc_castSucc,
          Function.Embedding.trans_apply, Fin.castAddEmb_apply])
      (fun i hi => by induction i using Fin.lastCases with
        | last => exact (hi ⟨Fin.last k, by simp [replayTapes, Fin.Embedding.snoc_last]⟩).elim
        | cast => simp)

private theorem replayTag_runFrom_initial (machine : MultiTapePTM k Bool State)
    (coins input : List Bool) :
    ((replayTag machine).extendTapes (replayTapes k r)).runFrom
        (MultiTapeTM.ReplayInput.initial k r coins input (some (some machine.initial)))
        (coins.length + 1) =
      embed (replayTapes k r)
        (replayTagStopped (machine.runClosedConfigFromCoins coins (machine.initialConfig input))
          (tapeOfList coins) coins.length) (fun _ _ => none) (fun _ => 0) := by
  rw [← replayTag_embed_initial machine coins input, ← embedHom_apply (replayTag machine),
    runFrom_map, runFrom_replayTag, embedHom_apply]

private noncomputable def replayTagCompile (machine : MultiTapePTM k Bool State)
    (prepare : MultiTapeTM (r + 2) Bool PrepareState) :
    MultiTapeTM (k + r + 3) Bool (PrepareState ⊕ MarkWorkState ⊕ Option State) :=
  (prepare.extendTapes (MultiTapeTM.ReplayInput.prepareTapes k r)).seq
    ((MultiTapeTM.markFlag (k + r + 1) (some true)).seq
      ((replayTag machine).extendTapes (replayTapes k r)).inputFromTape)

private def replayTagFinish (machine : MultiTapePTM k Bool State)
    (coins input outer : List Bool) :
    Cfg (k + r + 3) Bool (PrepareState ⊕ MarkWorkState ⊕ Option State) outer :=
  ((inCfg true
    (embed (replayTapes k r)
      (replayTagStopped (machine.runClosedConfigFromCoins coins (machine.initialConfig input))
        (tapeOfList coins) coins.length) (fun _ _ => none) (fun _ => 0)) outer).mapState
    (Option.map .inr)).mapState (Option.map .inr)

private theorem runFrom_replayTagCompile (machine : MultiTapePTM k Bool State)
    (prepare : MultiTapeTM (r + 2) Bool PrepareState) (coins input outer : List Bool) (t s : ℕ)
    (h : TransformsTapes prepare (fun inp ws => inp = outer ∧ ws = fun _ => [])
      (fun _ _ ws' emitted =>
        ws' = Fin.append (fun _ : Fin r => []) ![coins, input] ∧ emitted = []) t s) :
    (replayTagCompile machine prepare).runFrom
        ((replayTagCompile machine prepare).initCfg outer)
        (t + (2 + (coins.length + 1))) = replayTagFinish machine coins input outer := by
  have hr := runFrom_map (((replayTag machine).extendTapes (replayTapes k r)).inCfgHom true outer)
    (MultiTapeTM.ReplayInput.initial k r coins input (some (some machine.initial)))
    (coins.length + 1)
  simp only [inCfgHom_apply, replayTag_runFrom_initial] at hr
  have hq : ((replayTag machine).extendTapes (replayTapes k r)).inputFromTape.q₀ =
      some machine.initial := by
    simp [MultiTapeTM.inputFromTape, MultiTapeTM.adapt, q₀_ofTr, replayTag]
  have hs := runFrom_seq (tm₁ := ((replayTag machine).extendTapes (replayTapes k r)).inputFromTape)
    (MultiTapeTM.ReplayInput.runFrom_mark (k := k) (r := r) coins input outer) rfl
    (by simpa only [hq, Cfg.withState, MultiTapeTM.ReplayInput.initial, wordsCfg, inCfg] using hr)
    rfl
  have hqseq : ((MultiTapeTM.markFlag (k + r + 1) (some true)).seq
      ((replayTag machine).extendTapes (replayTapes k r)).inputFromTape).q₀ =
        Sum.inl (MultiTapeTM.markWork Bool (some true)).q₀ := by
    simp [MultiTapeTM.seq, MultiTapeTM.combine, q₀_ofTr, MultiTapeTM.markFlag]
  have hc := runFrom_seq (tm₁ := (MultiTapeTM.markFlag (k + r + 1) (some true)).seq
      ((replayTag machine).extendTapes (replayTapes k r)).inputFromTape)
    (MultiTapeTM.ReplayInput.runFrom_prepare (k := k) prepare coins input outer t s h) rfl
    (by simpa [hqseq, Cfg.withState, Cfg.mapState, wordsCfg] using hs) rfl
  simpa [replayTagCompile, initCfg_eq_wordsCfg, Cfg.mapState, wordsCfg, MultiTapeTM.seq,
    MultiTapeTM.combine, q₀_ofTr, replayTagFinish, inCfg] using hc

/-- Tagged saved-coin replay (`output ++ [state.isNone]`) runs in linear time and linear space. -/
theorem computableInDegree_replayTagOutput [Finite State]
    (machine : MultiTapePTM k Bool State) :
    ComputableInDegree
      (fun p : List Bool × List Bool => replayTagOutput machine p.1 p.2)
      (encPair encBits encBits) encBits 1 1 := by
  obtain ⟨r, PrepareState, _, prepare, c, hp⟩ :=
    PairEncoding.exists_prepare encBits encBits (encPair encBits encBits)
  let size (p : List Bool × List Bool) := (encPair encBits encBits p).length + 1
  let time (p : List Bool × List Bool) := c * size p + (2 + (p.1.length + 1))
  let n := k + r + 3
  let b := (n + 1) * (c + 5)
  have hraw : ComputableInTimeAndSpace
      (fun p : List Bool × List Bool => replayTagOutput machine p.1 p.2)
      (encPair encBits encBits) encBits (fun p => b * size p) (fun p => b * size p) := by
    refine ⟨n, PrepareState ⊕ MarkWorkState ⊕ Option State, inferInstance,
      replayTagCompile machine prepare, fun p => ?_⟩
    have hr := runFrom_replayTagCompile machine prepare p.1 p.2 (encPair encBits encBits p)
      (c * size p) (c * size p) (hp p)
    have hh : ((replayTagCompile machine prepare).runFrom
        ((replayTagCompile machine prepare).initCfg (encPair encBits encBits p))
        (time p)).Halted := by
      rw [show time p = c * size p + (2 + (p.1.length + 1)) from rfl, hr]
      rfl
    have hlen := length_le_encPair_left encBits encBits p
    have ht₀ : time p + 1 ≤ (c + 5) * size p := by
      dsimp only [time, size]
      simp only [encBits_apply] at hlen
      nlinarith
    have ht : time p ≤ b * size p :=
      (Nat.le_succ _).trans (ht₀.trans
        (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left (c + 5) (Nat.succ_pos n))))
    have hs : n * (time p + 1) ≤ b * size p := by
      calc _ ≤ n * ((c + 5) * size p) := Nat.mul_le_mul_left n ht₀
        _ ≤ (n + 1) * ((c + 5) * size p) := Nat.mul_le_mul_right _ (Nat.le_succ n)
        _ = _ := (Nat.mul_assoc _ _ _).symm
    refine ⟨⟨time p, hh, ?_⟩, (runsInTime_of_halted hh).mono ht,
      runsInSpace_of_halted hh ?_⟩
    · change ((replayTagCompile machine prepare).runFrom _
        (c * size p + (2 + (p.1.length + 1)))).output = _
      rw [hr]
      rfl
    · exact (MultiTapeNTM.RunPath.ofDeterministic (replayTagCompile machine prepare)
        ((replayTagCompile machine prepare).initCfg (encPair encBits encBits p))
        (time p)).space_le_mul_time_add_one.trans hs
  exact ComputableInDegree.one_one_iff.mpr ⟨b, hraw⟩

/-- Tagged saved-coin replay is polynomial-time computable. -/
theorem computableInPolyTime_replayTagOutput [Finite State]
    (machine : MultiTapePTM k Bool State) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => replayTagOutput machine p.1 p.2)
      (encPair encBits encBits) encBits :=
  (computableInDegree_replayTagOutput machine).computableInPolyTime

/-- Checking whether `machine` halted with output `[true]` on saved coins is polynomial-time
computable. -/
theorem computableInPolyTime_replayHaltedAccept [Finite State]
    (machine : MultiTapePTM k Bool State) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => replayHaltedAccept machine p.1 p.2)
      (encPair encBits encBits) encBool := by
  have htag := computableInPolyTime_replayTagOutput machine
  have hfun : (fun p : List Bool × List Bool => replayHaltedAccept machine p.1 p.2) =
      fun p => decide (replayTagOutput machine p.1 p.2 = [true, true]) :=
    funext fun p => replayHaltedAccept_iff_replayTagOutput machine p.1 p.2
  rw [hfun]
  have hconst : ComputableInPolyTime (fun _ : List Bool × List Bool => ([true, true] : List Bool))
      (encPair encBits encBits) encBits := ComputableInPolyTime.const _
  exact ComputableInPolyTime.decide_eq' htag hconst

/-- On zero coins, a `MultiTapePTM` is in its initial non-halted state so `replayHaltedAccept` is
`false`. -/
@[simp]
theorem replayHaltedAccept_nil (machine : MultiTapePTM k Bool State) (input : List Bool) :
    replayHaltedAccept machine [] input = false := by
  simp [replayHaltedAccept, runClosedConfigFromCoins, MultiTapeMachine.initialConfig, Cfg.init]

/-- Once `replayHaltedAccept` returns `true` on `coins`, it stays `true` on every extension
`coins ++ ext`. -/
theorem replayHaltedAccept_append_of_eq_true (machine : MultiTapePTM k Bool State)
    (coins ext input : List Bool) (h : replayHaltedAccept machine coins input = true) :
    replayHaltedAccept machine (coins ++ ext) input = true := by
  rw [replayHaltedAccept_eq_true_iff] at h ⊢
  rw [machine.replay_append]
  have hstay := machine.tapes_runClosedConfigFromCoins_of_halted ext _ h.1
  rw [hstay]
  exact h

end ReplayTag

/-! ### Unbounded round-by-round randomized semidecision loop (`iterateWhile`) -/

/-- Probability that the Markov chain with transition `round : σ → ProbComp (Option σ)` hits
the accepting state `none` within `r` rounds starting from `s`. -/
noncomputable def hitProb {σ : Type} (round : σ → ProbComp (Option σ)) : ℕ → σ → ℝ≥0∞
  | 0, _ => 0
  | r + 1, s =>
      (ProbComp.eval (round s)) none +
        ∑' s', (ProbComp.eval (round s)) (some s') * hitProb round r s'

/-- `hitProb` at zero rounds is `0`. -/
@[simp]
theorem hitProb_zero {σ : Type} (round : σ → ProbComp (Option σ)) (s : σ) :
    hitProb round 0 s = 0 := by
  rfl

/-- One-step unfolding equation for `hitProb`. -/
theorem hitProb_succ {σ : Type} (round : σ → ProbComp (Option σ)) (r : ℕ) (s : σ) :
    hitProb round (r + 1) s =
      (ProbComp.eval (round s)) none +
        ∑' s', (ProbComp.eval (round s)) (some s') * hitProb round r s' := by
  rfl

/-- `hitProb round r s` is always at most `1`. -/
theorem hitProb_le_one {σ : Type} (round : σ → ProbComp (Option σ)) (r : ℕ) (s : σ) :
    hitProb round r s ≤ 1 := by
  induction r generalizing s with
  | zero => exact zero_le
  | succ r ih =>
    calc hitProb round (r + 1) s
        ≤ (ProbComp.eval (round s)) none + ∑' s', (ProbComp.eval (round s)) (some s') * 1 :=
          add_le_add le_rfl (tsum_le_tsum fun s' => mul_le_mul_of_nonneg_left (ih s') zero_le)
      _ = (ProbComp.eval (round s)) none + ∑' s', (ProbComp.eval (round s)) (some s') := by
          simp only [mul_one]
      _ = ∑' o : Option σ, (ProbComp.eval (round s)) o :=
          (tsum_option_eq _).symm
      _ = 1 := PMF.tsum_coe _

/-- `hitProb round r s` is monotone in the round budget `r`. -/
theorem hitProb_mono {σ : Type} (round : σ → ProbComp (Option σ)) (s : σ) :
    Monotone fun r => hitProb round r s := by
  refine monotone_nat_of_le_succ fun r => ?_
  induction r generalizing s with
  | zero => exact zero_le
  | succ r ih =>
    exact add_le_add le_rfl (tsum_le_tsum fun s' => mul_le_mul_of_nonneg_left (ih s') zero_le)

/-- `hitProb` equals the probability of landing at `none` after `r` steps of the absorbing
`Option σ` iteration. -/
theorem hitProb_eq_eval_iterate {σ : Type} (round : σ → ProbComp (Option σ)) (r : ℕ) (s : σ) :
    hitProb round r s =
      ProbComp.eval (OracleComp.iterate r (fun o : Option σ => o.elim (pure none) round) (some s))
        none := by
  have hnone (n : ℕ) :
      ProbComp.eval (OracleComp.iterate n (fun o : Option σ => o.elim (pure none) round) none)
        none = 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [OracleComp.iterate_succ_bind, ProbComp.eval_bind]
      simpa [ProbComp.eval_pure] using ih
  induction r generalizing s with
  | zero => simp [hitProb]
  | succ r ih =>
    rw [hitProb, OracleComp.iterate_succ_bind, ProbComp.eval_bind, PMF.bind_apply,
      tsum_option_eq]
    simp only [Option.elim_some, hnone, mul_one, ih]

/-- Eventual acceptance probability of the round-by-round Markov chain. -/
noncomputable def hitProbSup {σ : Type} (round : σ → ProbComp (Option σ)) (s : σ) : ℝ≥0∞ :=
  ⨆ r, hitProb round r s

/-- `hitProbSup` equals the supremum of `hitProb` over all round budgets. -/
theorem hitProbSup_eq_iSup {σ : Type} (round : σ → ProbComp (Option σ)) (s : σ) :
    hitProbSup round s = ⨆ r, hitProb round r s := by
  rfl

/-- `hitProbSup` satisfies the exact one-step harmonic equation. -/
theorem hitProbSup_eq {σ : Type} (round : σ → ProbComp (Option σ)) (s : σ) :
    hitProbSup round s =
      (ProbComp.eval (round s)) none +
        ∑' s', (ProbComp.eval (round s)) (some s') * hitProbSup round s' := by
  classical
  have hsup : hitProbSup round s = ⨆ r, hitProb round (r + 1) s := by
    refine le_antisymm (iSup_le fun r => ?_)
      (iSup_le fun r => le_iSup (fun k => hitProb round k s) (r + 1))
    exact (hitProb_mono round s (Nat.le_succ r)).trans
      (le_iSup (fun k => hitProb round (k + 1) s) r)
  rw [hsup]
  simp only [hitProb]
  rw [← ENNReal.add_iSup]
  congr 1
  have hrhs : ∑' s', (ProbComp.eval (round s)) (some s') * hitProbSup round s' =
      ∑' s', ⨆ k, (ProbComp.eval (round s)) (some s') * hitProb round k s' := by
    refine tsum_congr fun s' => ?_
    rw [hitProbSup, ENNReal.mul_iSup]
  rw [hrhs]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun r => ?_
    exact tsum_le_tsum fun s' => le_iSup (fun k => (ProbComp.eval (round s)) (some s') *
      hitProb round k s') r
  · rw [tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    have hfin : ∑ s' ∈ F, ⨆ k, (ProbComp.eval (round s)) (some s') * hitProb round k s' ≤
        ⨆ r, ∑ s' ∈ F, (ProbComp.eval (round s)) (some s') * hitProb round r s' := by
      induction F using Finset.induction_on with
      | empty => simp
      | @insert a F ha ih =>
        rw [Finset.sum_insert ha]
        calc (⨆ k, (ProbComp.eval (round s)) (some a) * hitProb round k a) +
              ∑ s' ∈ F, ⨆ k, (ProbComp.eval (round s)) (some s') * hitProb round k s'
            ≤ (⨆ k, (ProbComp.eval (round s)) (some a) * hitProb round k a) +
              ⨆ r, ∑ s' ∈ F, (ProbComp.eval (round s)) (some s') * hitProb round r s' :=
              add_le_add le_rfl ih
          _ = ⨆ k, ⨆ r, ((ProbComp.eval (round s)) (some a) * hitProb round k a +
                ∑ s' ∈ F, (ProbComp.eval (round s)) (some s') * hitProb round r s') := by
              rw [ENNReal.iSup_add]
              congr 1; ext k
              rw [ENNReal.add_iSup]
          _ ≤ ⨆ m, ∑ s' ∈ insert a F,
                (ProbComp.eval (round s)) (some s') * hitProb round m s' := by
              refine iSup_le fun k => iSup_le fun r => ?_
              refine le_trans ?_ (le_iSup _ (max k r))
              rw [Finset.sum_insert ha]
              exact add_le_add
                (mul_le_mul_of_nonneg_left (hitProb_mono round a (le_max_left k r)) zero_le)
                (Finset.sum_le_sum fun s' _ =>
                  mul_le_mul_of_nonneg_left (hitProb_mono round s' (le_max_right k r)) zero_le)
    refine hfin.trans (iSup_le fun r => ?_)
    exact (sum_le_tsum F).trans (le_iSup (fun k =>
      ∑' s', (ProbComp.eval (round s)) (some s') * hitProb round k s') r)

/-! #### Strong-Markov upper bound on `repeatUntilBlank` -/

private theorem toOuterMeasure_halted_repeatUntilBlank_le {k : ℕ} {State : Type} {x : List Bool}
    (i : Fin k) (body : MultiTapePTM k Bool State)
    {good : Set (Config k Bool (State ⊕ Unit) Empty x)}
    (hgood : ∀ c ∈ good, c.tapes.state = none) :
    ∀ (t S : ℕ) (c : Config k Bool State Empty x),
      (∀ r ∈ (ProbComp.eval (body.runClosedConfigFrom t c)).support, r.tapes.state = none) →
      (ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom S
          (RepeatUntilBlank.runConfig c))).toOuterMeasure good ≤
        ((ProbComp.eval (body.runClosedConfigFrom t c)).bind fun r =>
          ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom S
            (RepeatUntilBlank.runConfig r))).toOuterMeasure good
  | 0, S, c, _ => by
    have h0 : body.runClosedConfigFrom 0 c = pure c := by
      unfold runClosedConfigFrom MultiTapePTM.runConfigFrom
      exact MultiTapeMachine.runConfigFrom_zero _ _ _ c
    rw [h0, ProbComp.eval_pure, PMF.pure_bind]
  | t + 1, S, c, hhalt => by
    by_cases hc : c.tapes.state = none
    · rw [eval_runClosedConfigFrom_of_halted body (t + 1) c hc, PMF.pure_bind]
    · cases S with
      | zero =>
        have h0 : (MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom 0
            (RepeatUntilBlank.runConfig c) = pure (RepeatUntilBlank.runConfig c) := by
          unfold runClosedConfigFrom MultiTapePTM.runConfigFrom
          exact MultiTapeMachine.runConfigFrom_zero _ _ _ _
        rw [h0, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply]
        have hnot : RepeatUntilBlank.runConfig c ∉ good := by
          intro hmem
          have hs := hgood _ hmem
          obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
          simp [RepeatUntilBlank.runConfig, Cfg.mapState, hq] at hs
        rw [ite_eq_right hnot]
        exact zero_le
      | succ S' =>
        have hstep1 : ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom 1
            (RepeatUntilBlank.runConfig c)) =
            (ProbComp.eval (body.runClosedConfigFrom 1 c)).map RepeatUntilBlank.runConfig :=
          eval_runClosedConfigFrom_one_of_step _ _ c fun bit =>
            step_withCoin_repeatUntilBlank_live i body bit c hc
        rw [show S' + 1 = 1 + S' by omega, eval_runClosedConfigFrom_add, hstep1, PMF.bind_map,
          show t + 1 = 1 + t by omega, body.eval_runClosedConfigFrom_add, PMF.bind_bind,
          PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
        refine tsum_le_tsum fun c' => ?_
        by_cases hc' : c' ∈ (ProbComp.eval (body.runClosedConfigFrom 1 c)).support
        · refine mul_le_mul_of_nonneg_left ?_ zero_le
          have hhalt' : ∀ r ∈ (ProbComp.eval (body.runClosedConfigFrom t c')).support,
              r.tapes.state = none := by
            intro r hr
            refine hhalt r ?_
            rw [show t + 1 = 1 + t by omega, body.eval_runClosedConfigFrom_add]
            exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨c', hc', hr⟩
          have hih := toOuterMeasure_halted_repeatUntilBlank_le i body hgood t S' c' hhalt'
          refine hih.trans ?_
          rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
          refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
          exact (MultiTapePTM.repeatUntilBlank i body).toOuterMeasure_halted_monotone _ hgood
            (Nat.le_add_left S' 1)
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hc', zero_mul, zero_mul]

private theorem toOuterMeasure_halted_repeatUntilBlank_le_pred {k : ℕ} {State : Type}
    {x : List Bool} (i : Fin k) (body : MultiTapePTM k Bool State)
    {good : Set (Config k Bool (State ⊕ Unit) Empty x)}
    (hgood : ∀ c ∈ good, c.tapes.state = none)
    {t S' : ℕ} {c : Config k Bool State Empty x} (hc : c.tapes.state ≠ none)
    (hhalt : ∀ r ∈ (ProbComp.eval (body.runClosedConfigFrom t c)).support,
      r.tapes.state = none) :
    (ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom (S' + 1)
        (RepeatUntilBlank.runConfig c))).toOuterMeasure good ≤
      ((ProbComp.eval (body.runClosedConfigFrom t c)).bind fun r =>
        ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom S'
          (RepeatUntilBlank.runConfig r))).toOuterMeasure good := by
  cases t with
  | zero =>
    have h0 : body.runClosedConfigFrom 0 c = pure c := by
      unfold runClosedConfigFrom MultiTapePTM.runConfigFrom
      exact MultiTapeMachine.runConfigFrom_zero _ _ _ c
    have hmem : c ∈ (ProbComp.eval (body.runClosedConfigFrom 0 c)).support := by
      rw [h0, ProbComp.eval_pure]; simp
    exact absurd (hhalt c hmem) hc
  | succ t =>
    have hstep1 : ProbComp.eval ((MultiTapePTM.repeatUntilBlank i body).runClosedConfigFrom 1
        (RepeatUntilBlank.runConfig c)) =
        (ProbComp.eval (body.runClosedConfigFrom 1 c)).map RepeatUntilBlank.runConfig :=
      eval_runClosedConfigFrom_one_of_step _ _ c fun bit =>
        step_withCoin_repeatUntilBlank_live i body bit c hc
    rw [show S' + 1 = 1 + S' by omega, eval_runClosedConfigFrom_add, hstep1, PMF.bind_map,
      show t + 1 = 1 + t by omega, body.eval_runClosedConfigFrom_add, PMF.bind_bind,
      PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    refine tsum_le_tsum fun c' => ?_
    by_cases hc' : c' ∈ (ProbComp.eval (body.runClosedConfigFrom 1 c)).support
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      refine toOuterMeasure_halted_repeatUntilBlank_le i body hgood t S' c' fun r hr => ?_
      refine hhalt r ?_
      rw [show t + 1 = 1 + t by omega, body.eval_runClosedConfigFrom_add]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨c', hc', hr⟩
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hc', zero_mul, zero_mul]

private theorem toOuterMeasure_halted_seq_le {k : ℕ} {S₀ S₁ : Type} {x : List Bool}
    (first : MultiTapePTM k Bool S₀) (second : MultiTapePTM k Bool S₁)
    {good : Set (Config k Bool (S₀ ⊕ S₁) Empty x)}
    (hgood : ∀ c ∈ good, c.tapes.state = none) :
    ∀ (t S : ℕ) (c : Config k Bool S₀ Empty x),
      (∀ r ∈ (ProbComp.eval (first.runClosedConfigFrom t c)).support, r.tapes.state = none) →
      (ProbComp.eval ((first.seq second).runClosedConfigFrom S
          (MultiTapeMachine.Sequential.left second c))).toOuterMeasure good ≤
        ((ProbComp.eval (first.runClosedConfigFrom t c)).bind fun r =>
          ProbComp.eval (second.runClosedConfigFrom S
            (MultiTapeMachine.Sequential.start second r))).toOuterMeasure
            (MultiTapeMachine.Sequential.right ⁻¹' good)
  | 0, S, c, hhalt => by
    have h0 : first.runClosedConfigFrom 0 c = pure c := by
      unfold runClosedConfigFrom MultiTapePTM.runConfigFrom
      exact MultiTapeMachine.runConfigFrom_zero _ _ _ c
    have hc : c.tapes.state = none := hhalt c (by rw [h0, ProbComp.eval_pure]; simp)
    rw [h0, ProbComp.eval_pure, PMF.pure_bind,
      eval_runClosedConfigFrom_seq_left_of_halted first second S c hc,
      PMF.toOuterMeasure_map_apply]
  | t + 1, S, c, hhalt => by
    by_cases hc : c.tapes.state = none
    · rw [eval_runClosedConfigFrom_of_halted first (t + 1) c hc, PMF.pure_bind,
        eval_runClosedConfigFrom_seq_left_of_halted first second S c hc,
        PMF.toOuterMeasure_map_apply]
    · cases S with
      | zero =>
        have h0 : (first.seq second).runClosedConfigFrom 0
            (MultiTapeMachine.Sequential.left second c) =
            pure (MultiTapeMachine.Sequential.left second c) := by
          unfold runClosedConfigFrom MultiTapePTM.runConfigFrom
          exact MultiTapeMachine.runConfigFrom_zero _ _ _ _
        rw [h0, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply]
        have hnot : MultiTapeMachine.Sequential.left second c ∉ good := by
          intro hmem
          have hs := hgood _ hmem
          obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
          simp [MultiTapeMachine.Sequential.left, Cfg.mapState, hq] at hs
        rw [ite_eq_right hnot]
        exact zero_le
      | succ S' =>
        have hstep1 : ProbComp.eval ((first.seq second).runClosedConfigFrom 1
            (MultiTapeMachine.Sequential.left second c)) =
            (ProbComp.eval (first.runClosedConfigFrom 1 c)).map
              (MultiTapeMachine.Sequential.left second) := by
          rw [runClosedConfigFrom, MultiTapePTM.runConfigFrom, runClosedConfigFrom,
            MultiTapePTM.runConfigFrom, MultiTapeMachine.Sequential.runConfigFrom_one first second
              (fun choices => choices <$> ProbComp.uniform Bool)
              (fun _ _ => by rw [Functor.map_map]; rfl) _ c hc, ProbComp.eval_map]
        rw [show S' + 1 = 1 + S' by omega, eval_runClosedConfigFrom_add, hstep1, PMF.bind_map,
          show t + 1 = 1 + t by omega, first.eval_runClosedConfigFrom_add, PMF.bind_bind,
          PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
        refine tsum_le_tsum fun c' => ?_
        by_cases hc' : c' ∈ (ProbComp.eval (first.runClosedConfigFrom 1 c)).support
        · refine mul_le_mul_of_nonneg_left ?_ zero_le
          have hih := toOuterMeasure_halted_seq_le first second hgood t S' c' fun r hr => by
            refine hhalt r ?_
            rw [show t + 1 = 1 + t by omega, first.eval_runClosedConfigFrom_add]
            exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨c', hc', hr⟩
          refine hih.trans ?_
          rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
          refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
          refine second.toOuterMeasure_halted_monotone _ (fun z hz => ?_) (Nat.le_add_left S' 1)
          have := hgood _ hz
          simpa [MultiTapeMachine.Sequential.right, Cfg.mapState] using this
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hc', zero_mul, zero_mul]

private theorem toOuterMeasure_halted_seq_le_first {k : ℕ} {S₀ S₁ : Type} {x : List Bool}
    (first : MultiTapePTM k Bool S₀) (second : MultiTapePTM k Bool S₁)
    {good : Set (Config k Bool (S₀ ⊕ S₁) Empty x)}
    (hgood : ∀ c ∈ good, c.tapes.state = none) :
    ∀ (S : ℕ) (c : Config k Bool S₀ Empty x),
      (ProbComp.eval ((first.seq second).runClosedConfigFrom S
          (MultiTapeMachine.Sequential.left second c))).toOuterMeasure good ≤
        (ProbComp.eval (first.runClosedConfigFrom S c)).toOuterMeasure
          {r | r.tapes.state = none}
  | 0, c => by
    have h0 : (first.seq second).runClosedConfigFrom 0
        (MultiTapeMachine.Sequential.left second c) =
        pure (MultiTapeMachine.Sequential.left second c) := by
      unfold runClosedConfigFrom MultiTapePTM.runConfigFrom
      exact MultiTapeMachine.runConfigFrom_zero _ _ _ _
    have h0' : first.runClosedConfigFrom 0 c = pure c := by
      unfold runClosedConfigFrom MultiTapePTM.runConfigFrom
      exact MultiTapeMachine.runConfigFrom_zero _ _ _ _
    rw [h0, h0', ProbComp.eval_pure, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply,
      PMF.toOuterMeasure_pure_apply]
    by_cases hc : c.tapes.state = none
    · simp only [Set.mem_ofPred_eq, hc, ↓reduceIte]
      split_ifs <;> simp
    · have hnot : MultiTapeMachine.Sequential.left second c ∉ good := by
        intro hmem
        have hs := hgood _ hmem
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
        simp [MultiTapeMachine.Sequential.left, Cfg.mapState, hq] at hs
      rw [ite_eq_right hnot]
      exact zero_le
  | S + 1, c => by
    by_cases hc : c.tapes.state = none
    · rw [eval_runClosedConfigFrom_of_halted first (S + 1) c hc, PMF.toOuterMeasure_pure_apply,
        ite_eq_left (show c ∈ {r | r.tapes.state = none} from hc)]
      exact Cslib.Probability.PMF.toOuterMeasure_le_one _ _
    · have hstep1 : ProbComp.eval ((first.seq second).runClosedConfigFrom 1
          (MultiTapeMachine.Sequential.left second c)) =
          (ProbComp.eval (first.runClosedConfigFrom 1 c)).map
            (MultiTapeMachine.Sequential.left second) := by
        rw [runClosedConfigFrom, MultiTapePTM.runConfigFrom, runClosedConfigFrom,
          MultiTapePTM.runConfigFrom, MultiTapeMachine.Sequential.runConfigFrom_one first second
            (fun choices => choices <$> ProbComp.uniform Bool)
            (fun _ _ => by rw [Functor.map_map]; rfl) _ c hc, ProbComp.eval_map]
      rw [show S + 1 = 1 + S by omega, eval_runClosedConfigFrom_add, hstep1, PMF.bind_map,
        first.eval_runClosedConfigFrom_add, PMF.toOuterMeasure_bind_apply,
        PMF.toOuterMeasure_bind_apply]
      refine tsum_le_tsum fun c' =>
        mul_le_mul_of_nonneg_left (toOuterMeasure_halted_seq_le_first first second hgood S c')
          zero_le

private theorem acceptAll_runClosedConfigFrom_succ (y : List Bool) (n : ℕ) :
    ProbComp.eval (acceptAll.runClosedConfigFrom (n + 1) (acceptAll.initialConfig y)) =
      PMF.pure ⟨⟨none, 1, fun _ _ => none, fun _ => 0, [true]⟩, Empty.elim⟩ := by
  have h1 : ProbComp.eval (acceptAll.runClosedConfigFrom 1 (acceptAll.initialConfig y)) =
      PMF.pure ⟨⟨none, 1, fun _ _ => none, fun _ => 0, [true]⟩, Empty.elim⟩ := by
    refine eval_runClosedConfigFrom_one_of_step_eq acceptAll _ _ fun bit => ?_
    refine Config.ext ?_ (Subsingleton.elim _ _)
    tm_step [MultiTapeMachine.step, withCoin, acceptAll, MultiTapeMachine.initialConfig]
  rw [show n + 1 = 1 + n by omega, eval_runClosedConfigFrom_add, h1, PMF.pure_bind,
    eval_runClosedConfigFrom_of_halted acceptAll n _ rfl]

private theorem acceptAll_comp_output_eq_true {k₀ : ℕ} {State₀ : Type} {x : List Bool}
    (first : MultiTapePTM k₀ Bool State₀) (mark : Bool) (t : ℕ)
    (final : Config (0 + k₀ + 2) Bool
      (State₀ ⊕ ((MarkWorkState ⊕ RewindWorkState) ⊕ Unit)) Empty x)
    (hmem : final ∈ (ProbComp.eval ((acceptAll.comp first mark).runClosedConfigFrom t
        ((acceptAll.comp first mark).initialConfig x))).support)
    (hhalt : final.tapes.state = none) :
    final.tapes.output = [true] := by
  rw [eval_runClosedConfigFrom_eq_map_coins, PMF.mem_support_map_iff] at hmem
  obtain ⟨coins, _, rfl⟩ := hmem
  have hcases1 := replay_seq_cases (MultiTapePTM.Composition.source first 0)
    (MultiTapePTM.Composition.continuation acceptAll k₀ mark)
    ((MultiTapePTM.Composition.source first 0).initialConfig x) coins
  rcases hcases1 with ⟨c₁, h1⟩ | ⟨c₁, c₂, hr1, h1⟩
  · change (((MultiTapePTM.Composition.source first 0).seq
      (MultiTapePTM.Composition.continuation acceptAll k₀ mark)).runClosedConfigFromCoins coins
        (MultiTapeMachine.Sequential.left (MultiTapePTM.Composition.continuation acceptAll k₀ mark)
          ((MultiTapePTM.Composition.source first 0).initialConfig x))).tapes.state = none at hhalt
    rw [h1] at hhalt
    simp [MultiTapeMachine.Sequential.left, Cfg.mapState] at hhalt
  · have hr1_sup : (MultiTapePTM.Composition.source first 0).runClosedConfigFromCoins c₁
        ((MultiTapePTM.Composition.source first 0).initialConfig x) ∈
        (ProbComp.eval ((MultiTapePTM.Composition.source first 0).runClosedConfigFrom c₁.length
          ((MultiTapePTM.Composition.source first 0).initialConfig x))).support :=
      runClosedConfigFromCoins_mem_support _ c₁ _
    rw [MultiTapePTM.Composition.runClosedConfigFrom_source, ProbComp.eval_map,
      PMF.mem_support_map_iff] at hr1_sup
    obtain ⟨r₀, _, hr₀_eq⟩ := hr1_sup
    set prepIn := MultiTapeTM.prepareInput (0 + k₀) mark
    set prepPtm : MultiTapePTM (0 + k₀ + 2) Bool _ := ofDeterministic prepIn
    set initPrep := MultiTapeMachine.Sequential.start prepPtm
      (MultiTapeMachine.Composition.buffer 0 r₀)
    have hcases2 := replay_seq_cases prepPtm
      (MultiTapePTM.Composition.consumer acceptAll k₀) initPrep c₂
    change (((MultiTapePTM.Composition.source first 0).seq
      (MultiTapePTM.Composition.continuation acceptAll k₀ mark)).runClosedConfigFromCoins coins
        (MultiTapeMachine.Sequential.left (MultiTapePTM.Composition.continuation acceptAll k₀ mark)
          ((MultiTapePTM.Composition.source first 0).initialConfig x))).tapes.output = [true]
    change (((MultiTapePTM.Composition.source first 0).seq
      (MultiTapePTM.Composition.continuation acceptAll k₀ mark)).runClosedConfigFromCoins coins
        (MultiTapeMachine.Sequential.left (MultiTapePTM.Composition.continuation acceptAll k₀ mark)
          ((MultiTapePTM.Composition.source first 0).initialConfig x))).tapes.state = none at hhalt
    rw [h1, ← hr₀_eq] at hhalt ⊢
    rcases hcases2 with ⟨c₂a, h2⟩ | ⟨c₂a, c₂b, hr2, h2⟩
    · change (MultiTapeMachine.Sequential.right ((prepPtm.seq
        (MultiTapePTM.Composition.consumer acceptAll k₀)).runClosedConfigFromCoins c₂
          (MultiTapeMachine.Sequential.left (MultiTapePTM.Composition.consumer acceptAll k₀)
            initPrep))).tapes.state = none at hhalt
      rw [h2] at hhalt
      simp [MultiTapeMachine.Sequential.right, MultiTapeMachine.Sequential.left,
        Cfg.mapState] at hhalt
    · have hdet := MultiTapeMachine.Composition.runFrom_prepare mark 0 r₀
      change prepIn.runFrom initPrep.tapes (r₀.tapes.output.length + 4) = _ at hdet
      have hprep_eval : ProbComp.eval (prepPtm.runClosedConfigFrom
          (r₀.tapes.output.length + 4) initPrep) =
          PMF.pure (MultiTapeMachine.Composition.ready mark 0 r₀) := by
        rw [eval_runClosedConfigFrom_ofDeterministic, hdet]; rfl
      have hr2_mem := completed_replay_mem_support prepPtm initPrep
        (r₀.tapes.output.length + 4) (fun u hu => by
          rw [hprep_eval, PMF.mem_support_pure_iff] at hu; rw [hu]; rfl) c₂a hr2
      rw [hprep_eval, PMF.mem_support_pure_iff] at hr2_mem
      change (MultiTapeMachine.Sequential.right ((prepPtm.seq
        (MultiTapePTM.Composition.consumer acceptAll k₀)).runClosedConfigFromCoins c₂
          (MultiTapeMachine.Sequential.left (MultiTapePTM.Composition.consumer acceptAll k₀)
            initPrep))).tapes.output = [true]
      change (MultiTapeMachine.Sequential.right ((prepPtm.seq
        (MultiTapePTM.Composition.consumer acceptAll k₀)).runClosedConfigFromCoins c₂
          (MultiTapeMachine.Sequential.left (MultiTapePTM.Composition.consumer acceptAll k₀)
            initPrep))).tapes.state = none at hhalt
      rw [h2, hr2_mem, MultiTapeMachine.Composition.start_ready] at hhalt ⊢
      cases c₂b with
      | nil =>
        simp [runClosedConfigFromCoins, MultiTapeMachine.Sequential.right,
          MultiTapeMachine.Composition.consumerConfig, MultiTapeMachine.InputFromTape.config,
          Config.embed, inCfg, MultiTapeTM.embed, Cfg.mapState,
          MultiTapeMachine.initialConfig, Cfg.init] at hhalt
      | cons b rest =>
        have hsup := runClosedConfigFromCoins_mem_support
          (MultiTapePTM.Composition.consumer acceptAll k₀) (b :: rest)
          (MultiTapeMachine.Composition.consumerConfig mark r₀
            (acceptAll.initialConfig r₀.tapes.output))
        rw [List.length_cons, MultiTapePTM.Composition.runClosedConfigFrom_consumer,
          ProbComp.eval_map, acceptAll_runClosedConfigFrom_succ, PMF.pure_map,
          PMF.mem_support_pure_iff] at hsup
        rw [hsup]
        simp [MultiTapeMachine.Sequential.right, MultiTapeMachine.Composition.consumerConfig,
          MultiTapeMachine.InputFromTape.config, Config.embed, inCfg, MultiTapeTM.embed,
          Cfg.mapState]

private theorem eval_runClosedConfigFrom_of_computesTidily_pure {k : ℕ} {State : Type}
    {machine : MultiTapePTM k Bool State} {x w : List Bool} {t : ℕ}
    (h : machine.ComputesTidily x t (pure w)) :
    ProbComp.eval (machine.runClosedConfigFrom t (machine.initialConfig x)) =
      PMF.pure { tapes := wordsCfg x none (fun _ => []) w, channels := Empty.elim } := by
  rw [RunsWords.eval_runClosedConfigFrom (p := pure w) (h []) _ (Cfg.init_eq_wordsCfg _ _),
    ProbComp.eval_pure, PMF.pure_map]
  rfl

/-- **Unbounded round-by-round randomized semidecision compiler.**
Given an `IsPPTOn` round transition `round : σ → ProbComp (Option σ)` (where `none` signals
acceptance) with a polynomial-time initializer `init : α → σ` and a monotone polynomial bound
`L a r` on the encoded length of all states reachable after `r` rounds, there exists a single
fixed fair-coin multi-tape Turing machine `M` and a polynomial `Tpoly` such that on every
input `a`:
1. every halted execution outputs `[true]`;
2. within `Tpoly.eval ((encIn a).length + r)` steps, `M` halts with `[true]` with probability
   at least `hitProb round r (init a)`;
3. at every clock `t`, `M` halts with probability at most `hitProbSup round (init a)`. -/
theorem exists_semidecision_machine {α σ : Type} {encIn : α ↪ List Bool} {encσ : σ ↪ List Bool}
    (init : α → σ) (round : σ → ProbComp (Option σ))
    (hinit : ComputableInPolyTime init encIn encσ)
    (hround : IsPPTOn encσ (encOption encσ) round)
    (inv : α → ℕ → σ → Prop)
    (hinv0 : ∀ a, inv a 0 (init a))
    (hinv_step : ∀ a r s, inv a r s →
      ∀ s', some s' ∈ (ProbComp.eval (round s)).support → inv a (r + 1) s')
    (L : α → ℕ → ℕ)
    (hL_mono : ∀ a, Monotone (L a))
    (hL_poly : ∃ P : Polynomial ℕ, ∀ a r, L a r ≤ P.eval ((encIn a).length + r))
    (hL_bound : ∀ a r s, inv a r s → (encσ s).length ≤ L a r) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State)
      (Tpoly : Polynomial ℕ),
      (∀ a t final,
        final ∈ (ProbComp.eval (M.runClosedConfigFrom t (M.initialConfig (encIn a)))).support →
        final.tapes.state = none → final.tapes.output = [true]) ∧
      (∀ a r, hitProb round r (init a) ≤
        (ProbComp.eval (M.runClosedConfigFrom (Tpoly.eval ((encIn a).length + r))
          (M.initialConfig (encIn a)))).toOuterMeasure
            {c | c.tapes.state = none ∧ c.tapes.output = [true]}) ∧
      (∀ a t,
        (ProbComp.eval (M.runClosedConfigFrom t (M.initialConfig (encIn a)))).toOuterMeasure
          {c | c.tapes.state = none} ≤ hitProbSup round (init a)) := by
  classical
  by_cases hα : Nonempty α
  · let a₀ : α := Classical.choice hα
    let s₀ : σ := init a₀
    let encLoop : Option σ ↪ List Bool := encOption encσ
    let body (w : Option σ) : WordOracleComp Empty (List Bool) :=
      match w with
      | none => pure []
      | some s => encLoop <$> ProbOracleComp.sample (round s)
    have hencLoop_pt : ComputableInPolyTime (fun o : Option σ => encLoop o) encLoop encBits :=
      ComputableInPolyTime.of_eq fun _ => rfl
    have hround_tidy : IsTidyOraclePPTOn (Operation := Empty) encσ encLoop
        (fun s => ProbOracleComp.sample (round s)) :=
      (hround.isOraclePPTOn (Operation := Empty)).oraclePhase
    have hbody : IsTidyOraclePPTOn (Operation := Empty) encLoop encBits body := by
      have hisNone : ComputableInPolyTime (fun w : Option σ => w.isNone) encLoop encBool := by
        have hfun : (fun w : Option σ => w.isNone) = fun w => !w.isSome := by
          funext w; cases w <;> rfl
        rw [hfun]
        exact ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.optionIsSome
          (ComputableInPolyTime.id' (encIn := encLoop)))
      have hgetS : ComputableInPolyTime (fun w : Option σ => w.getD s₀) encLoop encσ :=
        ComputableInPolyTime.optionGetDWithInput (ComputableInPolyTime.id' (encIn := encLoop))
          (ComputableInPolyTime.const s₀)
      have hlive : IsTidyOraclePPTOn (Operation := Empty) encLoop encBits
          (fun w => encLoop <$> ProbOracleComp.sample (round (w.getD s₀))) :=
        (hround_tidy.preprocess hgetS).map hencLoop_pt
      refine (IsTidyOraclePPTOn.cond hisNone
        (IsTidyOraclePPTOn.of_computableInPolyTime (ComputableInPolyTime.const []))
        hlive).congr fun w _ _ _ => ?_
      cases w <;> simp [body]
    obtain ⟨cl, dl, hbody_len⟩ := IsTidyOraclePPTOn.length_le hbody
    obtain ⟨_, kb, StateB, hfinB, bodyM, cb, db, hbodyM⟩ := hbody
    have hbodyM_live (s : σ) :
        bodyM.ComputesTidily (encLoop (some s))
          (cb * ((encLoop (some s)).length + 1) ^ db)
          (ProbOracleComp.sample (encLoop <$> round s)) := by
      refine (hbodyM (some s)).congr fun OS oracle st => ?_
      simp [body, encBits, ProbOracleComp.runWith_map, ProbOracleComp.runWith_sample,
        PMF.map_comp, Function.comp_def]
    let prep : α → List Bool := fun a => encLoop (some (init a))
    have hprep_pt : ComputableInPolyTime prep encIn encBits :=
      hencLoop_pt.comp ((ComputableInPolyTime.optionSome encσ).comp hinit)
    obtain ⟨_, kp, StateP, hfinP, prepM, cp, dp, hprepM⟩ :=
      IsTidyOraclePPTOn.of_computableInPolyTime (Operation := Empty) hprep_pt
    let rnd := (ofDeterministic (MultiTapeTM.IterateWhile.prepareRound (k := kb) true)).seq
      (bodyM.onWords true)
    let U := MultiTapePTM.repeatUntilBlank (MultiTapeTM.IterateWhile.nextTape kb) rnd
    let load : MultiTapePTM (kb + 1 + 2) Bool _ :=
      ofDeterministic (loadWord Bool (MultiTapeTM.IterateWhile.nextTape kb))
    let IW := load.seq U
    let mid := IW.comp prepM true
    let Z := acceptAll.comp mid true
    have hrnd_spec (w₀ vp v : List Bool) {t l : ℕ} {p : ProbComp (List Bool)}
        (h : bodyM.ComputesTidily v t (ProbOracleComp.sample p))
        (hl : ∀ w' ∈ (ProbComp.eval p).support, w'.length ≤ l) :
        rnd.RunsWords w₀ (MultiTapeTM.IterateWhile.words vp v) []
          (3 * vp.length + 6 * v.length + 16 + (t + l + 6))
          (ProbOracleComp.sample p) (fun v' => MultiTapeTM.IterateWhile.words v v')
          (fun _ => []) := by
      have h₁ := RunsWords.of_transformsTapes (Operation := Empty) (x := w₀) (out₀ := [])
        (MultiTapeTM.IterateWhile.transformsTapes_prepareRound (k := kb) true vp v)
        rfl (ws' := MultiTapeTM.IterateWhile.words v []) (emitted := []) (fun _ _ hQ => hQ)
      have h₂ := h.onWords_of_le (x := w₀) true (l := l) (fun _ _ _ w' _ hw' => by
        rw [ProbOracleComp.runWith_sample, PMF.mem_support_map_iff] at hw'
        exact hw'.elim fun _ ⟨hw'', heq⟩ => (Prod.mk.inj heq).1 ▸ hl _ hw'') ([] ++ [])
      rw [← MultiTapeTM.IterateWhile.words_nil_next v] at h₂
      have h₂' : (bodyM.onWords true).RunsWords w₀ (MultiTapeTM.IterateWhile.words v []) ([] ++ [])
          (t + l + 6) (ProbOracleComp.sample p)
          (fun v' => MultiTapeTM.IterateWhile.words v v') (fun _ => []) := by
        simpa only [show (Fin.last kb).castAdd 2 = MultiTapeTM.IterateWhile.nextTape kb from rfl,
          MultiTapeTM.IterateWhile.update_words_next] using h₂
      exact h₁.seq_pure_left h₂'
    obtain ⟨P, hP⟩ := hL_poly
    let X : Polynomial ℕ := Polynomial.X
    let C := Polynomial.C (R := ℕ)
    let Lpoly : Polynomial ℕ := P + C 1
    let tbPoly : Polynomial ℕ := C cb * (Lpoly + C 1) ^ db
    let Rpoly : Polynomial ℕ := tbPoly + C 10 * Lpoly + C 22
    let tpPoly : Polynomial ℕ := C cp * (X + C 1) ^ dp
    let tIWPoly : Polynomial ℕ := (C 3 * Lpoly + C 6) + X * (Rpoly + C 1)
    let Tpoly : Polynomial ℕ := tpPoly + (tpPoly + C 4 + tIWPoly) + C 5
    refine ⟨0 + ((kb + 1 + 2) + kp + 2) + 2, _, inferInstance, Z, Tpoly, ?_, ?_, ?_⟩
    · -- Property 1: every halted configuration outputs `[true]`.
      intro a t final hmem hhalt
      exact acceptAll_comp_output_eq_true mid true t final hmem hhalt
    · -- Property 2: lower bound at `Tpoly.eval ((encIn a).length + r)`.
      intro a r
      let x := encIn a
      let w₀ := prep a
      let Lmax := L a r + 1
      let tb := cb * (Lmax + 1) ^ db
      let R := tb + 10 * Lmax + 22
      let tp := cp * (x.length + 1) ^ dp
      let tIW := (3 * Lmax + 6) + r * (R + 1)
      let tMid := tp + (tp + 4 + tIW)
      let tZ := tMid + (0 + 4 + 1)
      let CfgOf {m : ℕ} {S : Type} (_ : MultiTapePTM m Bool S) (inp : List Bool) : Type :=
        Config m Bool S Empty inp
      let startU (vp v : List Bool) : CfgOf U w₀ :=
        RepeatUntilBlank.runConfig
          ⟨wordsCfg w₀ (some rnd.initial) (MultiTapeTM.IterateWhile.words vp v) [], Empty.elim⟩
      let goodU : Set (CfgOf U w₀) :=
        {c | c.tapes.state = none ∧ c.tapes.output = []}
      have hgoodU : ∀ c ∈ goodU, c.tapes.state = none := fun _ hc => hc.1
      have hlen_live (j : ℕ) (hj : j ≤ r) (s : σ) (hs : inv a j s) :
          (encLoop (some s)).length ≤ Lmax := by
        have h1 : (encσ s).length ≤ L a j := hL_bound a j s hs
        have h2 : L a j ≤ L a r := hL_mono a hj
        change (true :: encσ s).length ≤ L a r + 1
        simp only [List.length_cons]
        omega
      have hU_bound (k : ℕ) : ∀ j s vp, k + j ≤ r → inv a j s → vp.length ≤ Lmax →
          (ProbComp.eval (U.runClosedConfigFrom (k * (R + 1))
            (startU vp (encLoop (some s))))).toOuterMeasure goodUᶜ ≤
            1 - hitProb round k s := by
        induction k with
        | zero =>
          intro _ _ _ _ _ _
          simp only [hitProb, tsub_zero]
          exact Cslib.Probability.PMF.toOuterMeasure_le_one _ _
        | succ k ih =>
          intro j s vp hkj hs hvp
          have hv_len : (encLoop (some s)).length ≤ Lmax := hlen_live j (by omega) s hs
          have htid : bodyM.ComputesTidily (encLoop (some s)) tb
              (ProbOracleComp.sample (encLoop <$> round s)) :=
            (hbodyM_live s).mono (Nat.mul_le_mul_left cb (Nat.pow_le_pow_left (by omega) db))
          have hrnd : rnd.RunsWords w₀
              (MultiTapeTM.IterateWhile.words vp (encLoop (some s))) [] R
              (ProbOracleComp.sample (encLoop <$> round s))
              (fun v' => MultiTapeTM.IterateWhile.words (encLoop (some s)) v')
              (fun _ => []) := by
            refine (hrnd_spec w₀ vp (encLoop (some s)) htid (l := Lmax) fun w' hw' => ?_).mono ?_
            · rw [ProbComp.eval_map, PMF.mem_support_map_iff] at hw'
              obtain ⟨o, ho, rfl⟩ := hw'
              cases o with
              | none => simp [encLoop, encOption]
              | some s' => exact hlen_live (j + 1) (by omega) s' (hinv_step a j s hs s' ho)
            · dsimp [R]; omega
          rw [show (k + 1) * (R + 1) = R + (1 + k * (R + 1)) by ring]
          refine (hrnd.toOuterMeasure_compl_repeatUntilBlank_le
            (MultiTapeTM.IterateWhile.nextTape kb) hgoodU _).trans ?_
          rw [ProbComp.eval_map, PMF.bind_map, PMF.toOuterMeasure_bind_apply, tsum_option_eq]
          dsimp only [Function.comp_apply]
          change (ProbComp.eval (round s)) none *
                (ProbComp.eval (U.runClosedConfigFrom (1 + k * (R + 1))
                  ⟨wordsCfg w₀ (some (.inr ()))
                      (MultiTapeTM.IterateWhile.words (encLoop (some s)) []) ([] ++ []),
                    Empty.elim⟩)).toOuterMeasure goodUᶜ +
              ∑' s', (ProbComp.eval (round s)) (some s') *
                (ProbComp.eval (U.runClosedConfigFrom (1 + k * (R + 1))
                  ⟨wordsCfg w₀ (some (.inr ()))
                      (MultiTapeTM.IterateWhile.words (encLoop (some s))
                        (encLoop (some s'))) ([] ++ []),
                    Empty.elim⟩)).toOuterMeasure goodUᶜ ≤ _
          have hnone_term :
              (ProbComp.eval (round s)) none *
                (ProbComp.eval (U.runClosedConfigFrom (1 + k * (R + 1))
                  ⟨wordsCfg w₀ (some (.inr ()))
                      (MultiTapeTM.IterateWhile.words (encLoop (some s)) []) ([] ++ []),
                    Empty.elim⟩)).toOuterMeasure goodUᶜ = 0 := by
            rw [List.nil_append, RepeatUntilBlank.eval_runClosedConfigFrom_check_nil _ _
              (MultiTapeTM.IterateWhile.words_next _ []) _, PMF.toOuterMeasure_pure_apply,
              ite_eq_right (fun h => h ⟨rfl, rfl⟩), mul_zero]
          rw [hnone_term, zero_add]
          have hsome_le :
              ∑' s', (ProbComp.eval (round s)) (some s') *
                (ProbComp.eval (U.runClosedConfigFrom (1 + k * (R + 1))
                  ⟨wordsCfg w₀ (some (.inr ()))
                      (MultiTapeTM.IterateWhile.words (encLoop (some s))
                        (encLoop (some s'))) ([] ++ []),
                    Empty.elim⟩)).toOuterMeasure goodUᶜ ≤
              ∑' s', (ProbComp.eval (round s)) (some s') * (1 - hitProb round k s') := by
            refine tsum_le_tsum fun s' => ?_
            by_cases hs' : some s' ∈ (ProbComp.eval (round s)).support
            · refine mul_le_mul_of_nonneg_left ?_ zero_le
              rw [List.nil_append, RepeatUntilBlank.eval_runClosedConfigFrom_check_ne_nil _ _
                (by rw [MultiTapeTM.IterateWhile.words_next]; simp [encLoop, encOption])]
              exact ih (j + 1) s' (encLoop (some s)) (by omega)
                (hinv_step a j s hs s' hs') hv_len
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hs', zero_mul, zero_mul]
          refine hsome_le.trans_eq ?_
          have hadd_one :
              (∑' s', (ProbComp.eval (round s)) (some s') * (1 - hitProb round k s')) +
                hitProb round (k + 1) s = 1 := by
            rw [hitProb, ← add_assoc, add_comm _ ((ProbComp.eval (round s)) none), add_assoc,
              ← tsum_add]
            have hterm (s' : σ) :
                (ProbComp.eval (round s)) (some s') * (1 - hitProb round k s') +
                  (ProbComp.eval (round s)) (some s') * hitProb round k s' =
                (ProbComp.eval (round s)) (some s') := by
              rw [← mul_add, tsub_add_cancel_of_le (hitProb_le_one round k s'), mul_one]
            simp_rw [hterm]
            rw [← tsum_option_eq]
            exact PMF.tsum_coe _
          exact ENNReal.eq_sub_of_add_eq
            (ne_top_of_le_ne_top ENNReal.one_ne_top (hitProb_le_one round (k + 1) s)) hadd_one
      -- Lift from `U` to `IW = load.seq U`.
      have hw₀_len : w₀.length ≤ Lmax := hlen_live 0 (Nat.zero_le r) (init a) (hinv0 a)
      have hload : ProbComp.eval (load.runClosedConfigFrom (3 * Lmax + 6) (load.initialConfig w₀)) =
          PMF.pure ⟨wordsCfg w₀ none (MultiTapeTM.IterateWhile.words [] w₀) [], Empty.elim⟩ := by
        have hrw := (RunsWords.of_transformsTapes (Operation := Empty) (x := w₀) (out₀ := [])
          (transformsTapes_loadWord (MultiTapeTM.IterateWhile.nextTape kb) w₀) ⟨rfl, rfl⟩
          (ws' := MultiTapeTM.IterateWhile.words (k := kb) [] w₀) (emitted := [])
          (fun _ _ h => ⟨h.1.trans (MultiTapeTM.IterateWhile.words_nil_cur w₀).symm, h.2⟩)).mono
            (time' := 3 * Lmax + 6) (by omega)
        exact (RunsWords.eval_runClosedConfigFrom (p := pure ()) hrw _
          (Cfg.init_eq_wordsCfg _ _)).trans (by simp [ProbComp.eval_pure])
      let goodIW : Set (CfgOf IW w₀) :=
        {c | c.tapes.state = none ∧ c.tapes.output = []}
      have hIW_miss :
          (ProbComp.eval (IW.runClosedConfigFrom tIW (IW.initialConfig w₀))).toOuterMeasure
            goodIWᶜ ≤ 1 - hitProb round r (init a) := by
        change (ProbComp.eval ((load.seq U).runClosedConfigFrom ((3 * Lmax + 6) + r * (R + 1))
          (MultiTapeMachine.Sequential.left U (load.initialConfig w₀)))).toOuterMeasure
            goodIWᶜ ≤ _
        refine (toOuterMeasure_compl_seq_le load U (good := goodIW) (fun _ hc => hc.1)
          _ _ _).trans ?_
        set r₀ : Config (kb + 1 + 2) Bool ((Unit ⊕ RewindState) ⊕ RewindWorkState) Empty w₀ :=
          ⟨wordsCfg w₀ none (MultiTapeTM.IterateWhile.words [] w₀) [], Empty.elim⟩
        have hr₀ : r₀.tapes.state = none := rfl
        rw [hload, tsum_eq_single r₀ fun q hq => by rw [PMF.pure_apply, ite_eq_right hq, zero_mul],
          PMF.pure_apply, ite_eq_left rfl, one_mul, ite_eq_left hr₀]
        have hstart : MultiTapeMachine.Sequential.start U r₀ = startU [] w₀ :=
          Config.ext (by
            simp [r₀, MultiTapeMachine.Sequential.start, startU, RepeatUntilBlank.runConfig, U,
              MultiTapePTM.repeatUntilBlank, withState_wordsCfg, mapState_wordsCfg, handOver])
            (Subsingleton.elim _ _)
        have hpre : MultiTapeMachine.Sequential.right ⁻¹' goodIWᶜ = goodUᶜ := by
          ext c
          change ¬ ((MultiTapeMachine.Sequential.right c).tapes.state = none ∧
              (MultiTapeMachine.Sequential.right c).tapes.output = []) ↔
            ¬ (c.tapes.state = none ∧ c.tapes.output = [])
          simp [MultiTapeMachine.Sequential.right, Cfg.mapState]
        rw [hstart, hpre]
        exact hU_bound r 0 (init a) [] (by omega) (hinv0 a) (by simp)
      -- Lift from `IW` to `mid = IW.comp prepM true`.
      let goodMid : Set (CfgOf mid x) :=
        {c | c.tapes.state = none ∧ c.tapes.output = []}
      have hprep_eval : ProbComp.eval (prepM.runClosedConfigFrom tp (prepM.initialConfig x)) =
          PMF.pure ⟨wordsCfg x none (fun _ => []) w₀, Empty.elim⟩ := by
        have hp' : prepM.ComputesTidily x tp (pure w₀) := by
          simpa [x, w₀, tp, encBits] using hprepM a
        exact eval_runClosedConfigFrom_of_computesTidily_pure hp'
      have hmid_miss :
          (ProbComp.eval (mid.runClosedConfigFrom tMid (mid.initialConfig x))).toOuterMeasure
            goodMidᶜ ≤ 1 - hitProb round r (init a) := by
        refine (toOuterMeasure_compl_comp_le_of_halted prepM IW true
          (good := goodMid) (fun _ hc => hc.1) tp tIW (fun u hu => by
            rw [hprep_eval, PMF.mem_support_pure_iff] at hu; rw [hu]; rfl)).trans ?_
        rw [hprep_eval, PMF.pure_bind, PMF.toOuterMeasure_map_apply]
        have hpre : MultiTapeMachine.Composition.finalConfig true
            (⟨wordsCfg x none (fun _ => []) w₀, Empty.elim⟩ : Config kp Bool StateP Empty x) ⁻¹'
              goodMidᶜ = goodIWᶜ := by
          ext c
          change ¬ ((MultiTapeMachine.Composition.finalConfig true
              (⟨wordsCfg x none (fun _ => []) w₀, Empty.elim⟩ : Config kp Bool StateP Empty x)
              c).tapes.state = none ∧
            (MultiTapeMachine.Composition.finalConfig true
              (⟨wordsCfg x none (fun _ => []) w₀, Empty.elim⟩ : Config kp Bool StateP Empty x)
              c).tapes.output = []) ↔
            ¬ (c.tapes.state = none ∧ c.tapes.output = [])
          simp [MultiTapeMachine.Composition.finalConfig,
            MultiTapeMachine.Composition.consumerConfig, MultiTapeMachine.Sequential.right,
            MultiTapeMachine.InputFromTape.config, Config.embed, inCfg, MultiTapeTM.embed,
            Cfg.mapState]
        rw [hpre]
        exact hIW_miss
      -- Lift from `mid` to `Z = acceptAll.comp mid true`.
      let goodZ : Set (CfgOf Z x) :=
        {c | c.tapes.state = none ∧ c.tapes.output = [true]}
      have hZ_miss :
          (ProbComp.eval (Z.runClosedConfigFrom tZ (Z.initialConfig x))).toOuterMeasure
            goodZᶜ ≤ 1 - hitProb round r (init a) := by
        refine (toOuterMeasure_compl_comp_le_of_good mid acceptAll true
          (good := goodZ) (fun _ hc => hc.1) (good₁ := goodMid) (L := 0)
          (fun u hu => ⟨hu.1, by simp [hu.2]⟩) 1 (fun u _ final hfinal => ?_) tMid).trans hmid_miss
        rw [acceptAll_runClosedConfigFrom_succ u.tapes.output 0, PMF.mem_support_pure_iff] at hfinal
        subst hfinal
        refine ⟨?_, ?_⟩ <;>
          simp [MultiTapeMachine.Composition.finalConfig,
            MultiTapeMachine.Composition.consumerConfig, MultiTapeMachine.Sequential.right,
            MultiTapeMachine.InputFromTape.config, Config.embed, inCfg, MultiTapeTM.embed,
            Cfg.mapState]
      have hhit_tZ : hitProb round r (init a) ≤
          (ProbComp.eval (Z.runClosedConfigFrom tZ (Z.initialConfig x))).toOuterMeasure goodZ := by
        have hcomp :
            (ProbComp.eval (Z.runClosedConfigFrom tZ (Z.initialConfig x))).toOuterMeasure goodZ +
            (ProbComp.eval (Z.runClosedConfigFrom tZ (Z.initialConfig x))).toOuterMeasure goodZᶜ =
            1 := PMF.toOuterMeasure_add_compl_ennreal _ _
        have hsum : hitProb round r (init a) +
            (ProbComp.eval (Z.runClosedConfigFrom tZ (Z.initialConfig x))).toOuterMeasure
              goodZᶜ ≤
            (ProbComp.eval (Z.runClosedConfigFrom tZ (Z.initialConfig x))).toOuterMeasure goodZ +
            (ProbComp.eval (Z.runClosedConfigFrom tZ (Z.initialConfig x))).toOuterMeasure
              goodZᶜ := by
          rw [hcomp]
          calc hitProb round r (init a) +
                (ProbComp.eval (Z.runClosedConfigFrom tZ (Z.initialConfig x))).toOuterMeasure goodZᶜ
              ≤ hitProb round r (init a) + (1 - hitProb round r (init a)) :=
                add_le_add le_rfl hZ_miss
            _ = 1 := add_tsub_cancel_of_le (hitProb_le_one round r (init a))
        exact ENNReal.le_of_add_le_add_right
          (ne_top_of_le_ne_top ENNReal.one_ne_top (Cslib.Probability.PMF.toOuterMeasure_le_one _ _))
          hsum
      have htZ_le : tZ ≤ Tpoly.eval (x.length + r) := by
        have hLle : Lmax ≤ Lpoly.eval (x.length + r) := by
          dsimp [Lmax, Lpoly, C, x]
          simp only [Polynomial.eval_add, Polynomial.eval_C]
          have := hP a r
          omega
        have htb_le : tb ≤ tbPoly.eval (x.length + r) := by
          dsimp [tb, tbPoly, C]
          simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
            Polynomial.eval_C]
          exact Nat.mul_le_mul_left cb (Nat.pow_le_pow_left (by omega) db)
        have hR_le : R ≤ Rpoly.eval (x.length + r) := by
          dsimp [R, Rpoly, C]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
          omega
        have htp_le : tp ≤ tpPoly.eval (x.length + r) := by
          dsimp [tp, tpPoly, X, C]
          simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
            Polynomial.eval_X, Polynomial.eval_C]
          exact Nat.mul_le_mul_left cp (Nat.pow_le_pow_left (by omega) dp)
        have htIW_le : tIW ≤ tIWPoly.eval (x.length + r) := by
          dsimp [tIW, tIWPoly, X, C]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
          have hmul : r * (R + 1) ≤ (x.length + r) * (Rpoly.eval (x.length + r) + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          omega
        dsimp [tZ, tMid, Tpoly, C]
        simp only [Polynomial.eval_add, Polynomial.eval_C]
        omega
      exact hhit_tZ.trans (Z.toOuterMeasure_halted_monotone _ (fun _ hc =>
        (Set.mem_ofPred.mp hc).1) htZ_le)
    · -- Property 3: upper bound at every clock `t`.
      intro a t
      let x := encIn a
      let w₀ := prep a
      let tp := cp * (x.length + 1) ^ dp
      -- Step 1: `Z = acceptAll.comp mid true` halts no more often than `mid`.
      have hZ_le_mid :
          (ProbComp.eval (Z.runClosedConfigFrom t (Z.initialConfig x))).toOuterMeasure
            {c | c.tapes.state = none} ≤
          (ProbComp.eval (mid.runClosedConfigFrom t (mid.initialConfig x))).toOuterMeasure
            {c | c.tapes.state = none} := by
        let srcZ := MultiTapePTM.Composition.source mid 0
        let contZ := MultiTapePTM.Composition.continuation acceptAll ((kb + 1 + 2) + kp + 2) true
        change (ProbComp.eval ((srcZ.seq contZ).runClosedConfigFrom t
            (MultiTapeMachine.Sequential.left contZ (srcZ.initialConfig x)))).toOuterMeasure _ ≤ _
        refine (toOuterMeasure_halted_seq_le_first srcZ
          contZ (fun _ hc => hc) t _).trans_eq ?_
        rw [MultiTapePTM.Composition.runClosedConfigFrom_source, ProbComp.eval_map,
          PMF.toOuterMeasure_map_apply]
        rfl
      -- Step 2: `mid = IW.comp prepM true` halts no more often than `IW` on `w₀`.
      have hprep_eval : ProbComp.eval (prepM.runClosedConfigFrom tp (prepM.initialConfig x)) =
          PMF.pure ⟨wordsCfg x none (fun _ => []) w₀, Empty.elim⟩ := by
        have hp' : prepM.ComputesTidily x tp (pure w₀) := by
          simpa [x, w₀, tp, encBits] using hprepM a
        exact eval_runClosedConfigFrom_of_computesTidily_pure hp'
      have hmid_le_IW :
          (ProbComp.eval (mid.runClosedConfigFrom t (mid.initialConfig x))).toOuterMeasure
            {c | c.tapes.state = none} ≤
          (ProbComp.eval (IW.runClosedConfigFrom t (IW.initialConfig w₀))).toOuterMeasure
            {c | c.tapes.state = none} := by
        let srcP := MultiTapePTM.Composition.source prepM (kb + 1 + 2)
        let contIW := MultiTapePTM.Composition.continuation IW kp true
        change (ProbComp.eval ((srcP.seq contIW).runClosedConfigFrom t
          (MultiTapeMachine.Sequential.left contIW (srcP.initialConfig x)))).toOuterMeasure _ ≤ _
        set r₀ : Config kp Bool StateP Empty x :=
          ⟨wordsCfg x none (fun _ => []) w₀, Empty.elim⟩
        have hsrc_eval : ProbComp.eval (srcP.runClosedConfigFrom tp (srcP.initialConfig x)) =
            PMF.pure (MultiTapeMachine.Composition.buffer (kb + 1 + 2) r₀) := by
          rw [MultiTapePTM.Composition.runClosedConfigFrom_source, ProbComp.eval_map, hprep_eval,
            PMF.pure_map]
        refine (toOuterMeasure_halted_seq_le srcP contIW (fun _ hc => hc) tp t _ (fun u hu => by
          rw [hsrc_eval, PMF.mem_support_pure_iff] at hu
          rw [hu, MultiTapeMachine.Composition.buffer_tapes]; rfl)).trans ?_
        rw [hsrc_eval, PMF.pure_bind]
        let prepIn := MultiTapeTM.prepareInput ((kb + 1 + 2) + kp) true
        let prepPtm : MultiTapePTM ((kb + 1 + 2) + kp + 2) Bool _ := ofDeterministic prepIn
        let consIW := MultiTapePTM.Composition.consumer IW kp
        let initPrep := MultiTapeMachine.Sequential.start prepPtm
          (MultiTapeMachine.Composition.buffer (kb + 1 + 2) r₀)
        have hdet := MultiTapeMachine.Composition.runFrom_prepare true (kb + 1 + 2) r₀
        change prepIn.runFrom initPrep.tapes (w₀.length + 4) = _ at hdet
        have hprepIn_eval : ProbComp.eval (prepPtm.runClosedConfigFrom (w₀.length + 4) initPrep) =
            PMF.pure (MultiTapeMachine.Composition.ready true (kb + 1 + 2) r₀) := by
          rw [eval_runClosedConfigFrom_ofDeterministic, hdet]
          rfl
        change (ProbComp.eval ((prepPtm.seq consIW).runClosedConfigFrom t
          (MultiTapeMachine.Sequential.left consIW initPrep))).toOuterMeasure _ ≤ _
        refine (toOuterMeasure_halted_seq_le prepPtm consIW (fun _ hc => by
          simpa [MultiTapeMachine.Sequential.right, Cfg.mapState] using hc)
          (w₀.length + 4) t initPrep (fun u hu => by
            rw [hprepIn_eval, PMF.mem_support_pure_iff] at hu; rw [hu]; rfl)).trans_eq ?_
        rw [hprepIn_eval, PMF.pure_bind, MultiTapeMachine.Composition.start_ready,
          MultiTapePTM.Composition.runClosedConfigFrom_consumer, ProbComp.eval_map,
          PMF.toOuterMeasure_map_apply]
        congr 1
        ext c
        change (MultiTapeMachine.Sequential.right (MultiTapeMachine.Sequential.right
            (MultiTapeMachine.Composition.consumerConfig true r₀ c))).tapes.state = none ↔
          c.tapes.state = none
        simp [MultiTapeMachine.Composition.consumerConfig, MultiTapeMachine.Sequential.right,
          MultiTapeMachine.InputFromTape.config, Config.embed, inCfg, MultiTapeTM.embed,
          Cfg.mapState]
      -- Step 3: `IW = load.seq U` halts no more often than `U` from `startU [] w₀`.
      let startU (vp v : List Bool) : Config (kb + 1 + 2) Bool _ Empty w₀ :=
        RepeatUntilBlank.runConfig
          ⟨wordsCfg w₀ (some rnd.initial) (MultiTapeTM.IterateWhile.words vp v) [], Empty.elim⟩
      have hload : ProbComp.eval (load.runClosedConfigFrom (3 * w₀.length + 6)
          (load.initialConfig w₀)) =
          PMF.pure ⟨wordsCfg w₀ none (MultiTapeTM.IterateWhile.words [] w₀) [], Empty.elim⟩ := by
        have hrw := RunsWords.of_transformsTapes (Operation := Empty) (x := w₀) (out₀ := [])
          (transformsTapes_loadWord (MultiTapeTM.IterateWhile.nextTape kb) w₀) ⟨rfl, rfl⟩
          (ws' := MultiTapeTM.IterateWhile.words (k := kb) [] w₀) (emitted := [])
          (fun _ _ h => ⟨h.1.trans (MultiTapeTM.IterateWhile.words_nil_cur w₀).symm, h.2⟩)
        exact (RunsWords.eval_runClosedConfigFrom (p := pure ()) hrw _
          (Cfg.init_eq_wordsCfg _ _)).trans (by simp [ProbComp.eval_pure])
      have hIW_le_U :
          (ProbComp.eval (IW.runClosedConfigFrom t (IW.initialConfig w₀))).toOuterMeasure
            {c | c.tapes.state = none} ≤
          (ProbComp.eval (U.runClosedConfigFrom t (startU [] w₀))).toOuterMeasure
            {c | c.tapes.state = none} := by
        change (ProbComp.eval ((load.seq U).runClosedConfigFrom t
          (MultiTapeMachine.Sequential.left U (load.initialConfig w₀)))).toOuterMeasure _ ≤ _
        refine (toOuterMeasure_halted_seq_le load U (fun _ hc => hc)
          (3 * w₀.length + 6) t _ (fun u hu => by
            rw [hload, PMF.mem_support_pure_iff] at hu; rw [hu]; rfl)).trans_eq ?_
        rw [hload, PMF.pure_bind]
        have hstart : MultiTapeMachine.Sequential.start U
            (⟨wordsCfg w₀ none (MultiTapeTM.IterateWhile.words [] w₀) [], Empty.elim⟩ :
              Config (kb + 1 + 2) Bool ((Unit ⊕ RewindState) ⊕ RewindWorkState) Empty w₀) =
            startU [] w₀ :=
          Config.ext (by
            simp [MultiTapeMachine.Sequential.start, startU, RepeatUntilBlank.runConfig, U,
              MultiTapePTM.repeatUntilBlank, withState_wordsCfg, mapState_wordsCfg, handOver])
            (Subsingleton.elim _ _)
        rw [hstart]
        congr 1
        ext c
        simp [MultiTapeMachine.Sequential.right, Cfg.mapState]
      -- Step 4: Induction on `S` shows `Pr[U halts in S from startU vp (some s)] ≤ hitProbSup`.
      have hU_le_sup : ∀ S vp s,
          (ProbComp.eval (U.runClosedConfigFrom S
            (startU vp (encLoop (some s))))).toOuterMeasure {c | c.tapes.state = none} ≤
            hitProbSup round s := by
        intro S
        induction S with
        | zero =>
          intro vp s
          have h0 : U.runClosedConfigFrom 0 (startU vp (encLoop (some s))) =
              pure (startU vp (encLoop (some s))) := by
            unfold runClosedConfigFrom MultiTapePTM.runConfigFrom
            exact MultiTapeMachine.runConfigFrom_zero _ _ _ _
          rw [h0, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply]
          have hnot : startU vp (encLoop (some s)) ∉
              {c : Config (kb + 1 + 2) Bool _ Empty w₀ | c.tapes.state = none} := by
            simp [startU, RepeatUntilBlank.runConfig, Cfg.mapState, wordsCfg, handOver]
          rw [ite_eq_right hnot]
          exact zero_le
        | succ S ih =>
          intro vp s
          let v := encLoop (some s)
          let ts := cb * (v.length + 1) ^ db
          let ls := cl * (v.length + 1) ^ dl
          let Rs := 3 * vp.length + 6 * v.length + 16 + (ts + ls + 6)
          have hrnd : rnd.RunsWords w₀ (MultiTapeTM.IterateWhile.words vp v) [] Rs
              (ProbOracleComp.sample (encLoop <$> round s))
              (fun v' => MultiTapeTM.IterateWhile.words v v') (fun _ => []) :=
            hrnd_spec w₀ vp v (hbodyM_live s) (l := ls) fun w' hw' => by
              have hsup := hbody_len (some s) Unit (fun q => q.1.elim) () () w'
                (by
                  simpa [body, ProbOracleComp.runWith_map, ProbOracleComp.runWith_sample,
                    PMF.map_comp, Function.comp_def] using
                    (PMF.mem_support_map_iff (fun z => (z, ())) _ _).mpr ⟨w', hw', rfl⟩)
              simpa [encBits, ls, v] using hsup
          let c₀ : Config (kb + 1 + 2) Bool _ Empty w₀ :=
            ⟨wordsCfg w₀ (some rnd.initial) (MultiTapeTM.IterateWhile.words vp v) [], Empty.elim⟩
          have hrnd_eval : ProbComp.eval (rnd.runClosedConfigFrom Rs c₀) =
              (ProbComp.eval (round s)).map fun o =>
                ⟨wordsCfg w₀ none (MultiTapeTM.IterateWhile.words v (encLoop o)) [],
                  Empty.elim⟩ := by
            rw [RunsWords.eval_runClosedConfigFrom hrnd c₀ rfl, ProbComp.eval_map, PMF.map_comp]
            congr 1
          refine (toOuterMeasure_halted_repeatUntilBlank_le_pred
            (MultiTapeTM.IterateWhile.nextTape kb) rnd (fun _ hc => hc) (t := Rs) (S' := S)
            (c := c₀) (by simp [c₀, wordsCfg]) (fun u hu => by
              rw [hrnd_eval, PMF.mem_support_map_iff] at hu
              obtain ⟨o, _, rfl⟩ := hu; rfl)).trans ?_
          rw [hrnd_eval, PMF.bind_map, PMF.toOuterMeasure_bind_apply, tsum_option_eq,
            hitProbSup_eq]
          refine add_le_add ?_ ?_
          · exact mul_le_of_le_one_right' (Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
          · refine tsum_le_tsum fun s' => mul_le_mul_of_nonneg_left ?_ zero_le
            dsimp only [Function.comp_apply]
            let StateOf {m S} (_ : MultiTapePTM m Bool S) : Type := S
            let c₁ : Config (kb + 1 + 2) Bool (StateOf rnd) Empty w₀ :=
              ⟨wordsCfg w₀ none (MultiTapeTM.IterateWhile.words v (encLoop (some s'))) [],
                Empty.elim⟩
            change (ProbComp.eval (U.runClosedConfigFrom S
              (RepeatUntilBlank.runConfig c₁))).toOuterMeasure {c | c.tapes.state = none} ≤
              hitProbSup round s'
            cases S with
            | zero =>
              have h0 : U.runClosedConfigFrom 0 (RepeatUntilBlank.runConfig c₁) =
                  pure (RepeatUntilBlank.runConfig c₁) := by
                unfold runClosedConfigFrom MultiTapePTM.runConfigFrom
                exact MultiTapeMachine.runConfigFrom_zero _ _ _ _
              rw [h0, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply]
              have hnot : RepeatUntilBlank.runConfig c₁ ∉
                  {c | c.tapes.state = none} := by
                simp [c₁, RepeatUntilBlank.runConfig, Cfg.mapState, wordsCfg, handOver]
              rw [ite_eq_right hnot]
              exact zero_le
            | succ S' =>
              have hchk : RepeatUntilBlank.runConfig c₁ =
                  ⟨wordsCfg w₀ (some (.inr ()))
                      (MultiTapeTM.IterateWhile.words v (encLoop (some s'))) [],
                    Empty.elim⟩ := by
                refine Config.ext ?_ (Subsingleton.elim _ _)
                simp [c₁, RepeatUntilBlank.runConfig, mapState_wordsCfg, handOver]
              rw [hchk, show S' + 1 = 1 + S' by omega,
                RepeatUntilBlank.eval_runClosedConfigFrom_check_ne_nil _ _
                  (by rw [MultiTapeTM.IterateWhile.words_next]; simp [encLoop, encOption])]
              exact (U.toOuterMeasure_halted_monotone _ (fun _ hc => hc) (Nat.le_succ S')).trans
                (ih v s')
      exact hZ_le_mid.trans (hmid_le_IW.trans (hIW_le_U.trans (hU_le_sup t [] (init a))))
  · exact ⟨0, Unit, inferInstance, acceptAll, 0,
      fun a => (hα ⟨a⟩).elim, fun a => (hα ⟨a⟩).elim, fun a => (hα ⟨a⟩).elim⟩

end CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic
