/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Comp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Cursor
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ReadInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WhileInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run.FirstStep
import CslibFrontier.Foundations.Data.Fin.Tuple
import CslibFrontier.Foundations.Data.List.Flatten
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Persistent-Tape Batch-Query Combinator for Multi-Tape Turing Machines

Given any deterministic multi-tape Turing machine computing `qry : List Bool × List Bool → β` on
`encPair encBits encBits (b, D) = frame b ++ D` in time `tq (b, D)`, this module constructs a
persistent-tape batch-query machine that reads the preprocessed structure `D` once onto a work tape
and answers a streamed list `B` of binary queries without re-copying `D` between queries.

The total running time is `O(|D| + |enc B| + 1 + ∑_{b ∈ B} (tq (b, D) + |b| + 1))`, avoiding any
`|B| · |D|` re-copying term.

## Main results

* `CslibFrontier.Computability.Machines.Turing.MultiTape.computableInTimeAndSpace_batchQuery`:
  persistent-tape batch execution of a query Turing machine over a list of binary query vectors.
-/

public section

namespace CslibFrontier.Computability.Machines.Turing.MultiTape

open _root_.Turing _root_.Turing.MultiTapeTM

/-! ### Unframing input reader -/

/-- Two-state input reader consuming one framed word `frame w` from the input tape and emitting the
unframed payload `w`. -/
private def unframeReader : InputReader Bool Bool where
  q₀ := false
  step
    | false, false => (none, none)
    | false, true => (some true, none)
    | true, b => (some false, some b)

private lemma read_unframeReader (w rest : List Bool) :
    unframeReader.read false (frame w ++ rest) = (w, (frame w).length) := by
  induction w with
  | nil => rfl
  | cons b ws ih =>
    simp only [frame_cons, List.cons_append, List.length_cons]
    rw [InputReader.read_cons_of_some unframeReader _ rfl,
      InputReader.read_cons_of_some unframeReader _ rfl, ih]
    simp [unframeReader]

/-! ### Work-tape translation invariance -/

/-- Translate a bi-infinite work tape by `d : ℤ` cells: cell `z` holds the old cell `z - d`. -/
private def shiftTape {α : Type*} (d : ℤ) (T : ℤ → Option α) : ℤ → Option α :=
  fun z ↦ T (z - d)

private lemma shiftTape_zero {α : Type*} (T : ℤ → Option α) : shiftTape 0 T = T := by
  funext z; simp [shiftTape]

private lemma update_shiftTape {α : Type*} (d p : ℤ) (T : ℤ → Option α) (v : Option α) :
    Function.update (shiftTape d T) (p + d) v = shiftTape d (Function.update T p v) := by
  funext z
  by_cases h : z = p + d
  · subst h; simp [shiftTape]
  · have h' : z - d ≠ p := fun he ↦ h (by omega)
    simp [shiftTape, Function.update_of_ne h, Function.update_of_ne h']

/-- Translate each work tape `i` and its head position by `δ i : ℤ`. -/
private def shiftCfg {k : ℕ} {Symbol State : Type*} (δ : Fin k → ℤ) {inp : List Symbol}
    (c : Cfg k Symbol State inp) : Cfg k Symbol State inp where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun i ↦ shiftTape (δ i) (c.workTapes i)
  workTapePos := fun i ↦ c.workTapePos i + δ i
  output := c.output

private lemma step_shiftCfg {k : ℕ} {Symbol State : Type*} (tm : MultiTapeTM k Symbol State)
    (δ : Fin k → ℤ) {inp : List Symbol} (c : Cfg k Symbol State inp) :
    tm.step (shiftCfg δ c) = shiftCfg δ (tm.step c) := by
  cases hq : c.state with
  | none =>
    rw [step_of_halt (show (shiftCfg δ c).state = none from hq), step_of_halt hq]
  | some q =>
    have hws : (shiftCfg δ c).workTapeSymbols = c.workTapeSymbols := by
      funext i; simp [Cfg.workTapeSymbols, shiftCfg, shiftTape]
    have his : (shiftCfg δ c).inputSymbol = c.inputSymbol := rfl
    rw [step_of_state (show (shiftCfg δ c).state = some q from hq), step_of_state hq]
    dsimp only [Cfg.headSymbols, Action.apply]
    change Cfg.mk _ _ _ _ _ = shiftCfg δ _
    rw [his, hws]
    set a := tm.tr q c.inputSymbol c.workTapeSymbols
    refine Cfg.ext rfl rfl (funext fun i ↦ ?_) (funext fun i ↦ ?_) rfl
    · dsimp only [shiftCfg]
      cases (a.workTapes i).1 with
      | none => rfl
      | some w => exact update_shiftTape (δ i) (c.workTapePos i) (c.workTapes i) w
    · dsimp only [shiftCfg]; omega

private lemma runFrom_shiftCfg {k : ℕ} {Symbol State : Type*} (tm : MultiTapeTM k Symbol State)
    (δ : Fin k → ℤ) {inp : List Symbol} (c : Cfg k Symbol State inp) (n : ℕ) :
    tm.runFrom (shiftCfg δ c) n = shiftCfg δ (tm.runFrom c n) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ_eq_step, runFrom_succ_eq_step, step_shiftCfg, ih]

private lemma prependOutput_runFrom {k : ℕ} {Symbol State : Type*}
    (tm : MultiTapeTM k Symbol State) {inp : List Symbol}
    (c : Cfg k Symbol State inp) (pre : List Symbol) (n : ℕ) :
    tm.runFrom { c with output := pre ++ c.output } n =
      { tm.runFrom c n with output := pre ++ (tm.runFrom c n).output } := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ_eq_step, runFrom_succ_eq_step]
    have hs : tm.step { c with output := pre ++ c.output } =
        { tm.step c with output := pre ++ (tm.step c).output } := by
      rcases c with ⟨st, ip, wt, wp, o⟩
      cases st with
      | none =>
        change tm.step ⟨none, ip, wt, wp, pre ++ o⟩ = _
        rw [step_of_halt rfl, step_of_halt rfl]
      | some q =>
        change tm.step ⟨some q, ip, wt, wp, pre ++ o⟩ = _
        rw [step_of_state rfl, step_of_state rfl]
        dsimp only [Action.apply, Cfg.headSymbols, Cfg.inputSymbol]
        have hws : Cfg.workTapeSymbols (input := inp) ⟨some q, ip, wt, wp, pre ++ o⟩ =
            Cfg.workTapeSymbols (input := inp) ⟨some q, ip, wt, wp, o⟩ := rfl
        rw [hws]
        exact Cfg.ext rfl rfl rfl rfl (by simp [List.append_assoc])
    rw [hs, ih]

private lemma space_shiftCfg_le {k : ℕ} {Symbol State : Type*} (tm : MultiTapeTM k Symbol State)
    (δ : Fin k → ℤ) {inp : List Symbol} (c : Cfg k Symbol State inp) (n : ℕ) :
    (MultiTapeNTM.RunPath.ofDeterministic tm (shiftCfg δ c) n).space ≤
      (MultiTapeNTM.RunPath.ofDeterministic tm c n).space := by
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hsub : (MultiTapeNTM.RunPath.ofDeterministic tm (shiftCfg δ c) n).visitedByTapeHead i ⊆
      ((MultiTapeNTM.RunPath.ofDeterministic tm c n).visitedByTapeHead i).image (· + δ i) := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.mp hz
    rw [runFrom_shiftCfg]
    exact Finset.mem_image_of_mem (· + δ i)
      (MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.mpr ⟨m, hm, rfl⟩)
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-! ### Negative-cell prefix preparation and cleanup on `(vip, flag, qryT, home)` -/

private lemma shiftTape_cons_append (b : Bool) (u D : List Bool) :
    Function.update (shiftTape (-(u.length : ℤ)) (tapeOfList (u ++ D)))
      (-(u.length : ℤ) - 1) (some b) =
      shiftTape (-((b :: u).length : ℤ)) (tapeOfList ((b :: u) ++ D)) := by
  funext z
  have hcl : ((b :: u).length : ℤ) = (u.length : ℤ) + 1 := by simp
  by_cases hz : z = -(u.length : ℤ) - 1
  · subst hz; rw [Function.update_self, shiftTape, hcl]
    have h0 : -(u.length : ℤ) - 1 - -((u.length : ℤ) + 1) = ((0 : ℕ) : ℤ) := by push_cast; omega
    rw [h0, tapeOfList_ofNat]; rfl
  · rw [Function.update_of_ne hz]; simp only [shiftTape, hcl, List.cons_append]
    rcases lt_or_ge (z + (u.length : ℤ)) 0 with hlt | hge
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, z - -((u.length : ℤ) + 1) = Int.negSucc m :=
        Int.eq_negSucc_of_lt_zero (by omega)
      obtain ⟨m', hm'⟩ : ∃ m' : ℕ, z - -(u.length : ℤ) = Int.negSucc m' :=
        Int.eq_negSucc_of_lt_zero (by omega)
      rw [hm, hm', tapeOfList_negSucc, tapeOfList_negSucc]
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, z + (u.length : ℤ) = (m : ℕ) := Int.eq_ofNat_of_zero_le hge
      have a1 : z - -(u.length : ℤ) = (m : ℕ) := by omega
      have a2 : z - -((u.length : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; omega
      rw [a1, a2, tapeOfList_ofNat, tapeOfList_ofNat, List.getElem?_cons_succ]

private lemma erase_shiftTape_cons_append (b : Bool) (u D : List Bool) :
    Function.update (shiftTape (-((b :: u).length : ℤ)) (tapeOfList ((b :: u) ++ D)))
      (-((b :: u).length : ℤ)) none =
      shiftTape (-(u.length : ℤ)) (tapeOfList (u ++ D)) := by
  funext z
  have hcl : ((b :: u).length : ℤ) = (u.length : ℤ) + 1 := by simp
  rw [← shiftTape_cons_append b u D, hcl, show -((u.length : ℤ) + 1) = -(u.length : ℤ) - 1 by omega,
    Function.update_idem]
  by_cases hz : z = -(u.length : ℤ) - 1
  · subst hz; rw [Function.update_self, shiftTape]
    have hn : -(u.length : ℤ) - 1 - -(u.length : ℤ) = Int.negSucc 0 := by omega
    rw [hn, tapeOfList_negSucc]
  · exact Function.update_of_ne hz _ _

private lemma tapeOfList_erase_last (u : List Bool) (b : Bool) :
    Function.update (tapeOfList (u ++ [b])) (u.length : ℤ) none = tapeOfList u := by
  funext z
  by_cases hz : z = (u.length : ℤ)
  · subst hz; simp [tapeOfList_ofNat]
  · rw [Function.update_of_ne hz]
    rcases lt_or_ge z 0 with hlt | hge
    · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero hlt
      simp [tapeOfList_negSucc]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hge
      have hne : m ≠ u.length := fun he ↦ hz (by omega)
      simp only [tapeOfList_ofNat]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [List.getElem?_append_left hlt]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- Control states for copying `u` from `qryT` (tape 2) into cells `-|u|, …, -1` of `vip` (tape 0),
marking `flag` (tape 1) at `-|u| - 1`, and marking `home` (tape 3) at `0`. -/
private inductive PrepNegState
  | seek
  | copy
  | put (b : Bool)
  | setFlag
  deriving DecidableEq

private instance instFinitePrepNegState : Finite PrepNegState :=
  Finite.of_injective
    (fun | .seek => (0 : Fin 5) | .copy => 1 | .put false => 2 | .put true => 3 | .setFlag => 4)
    (fun a b h ↦ by
      rcases a with _ | _ | (_ | _) | _ <;> rcases b with _ | _ | (_ | _) | _ <;> simp at h ⊢)

private noncomputable def prepNegTM : MultiTapeTM 4 Bool PrepNegState :=
  ofTr .seek fun q _ w ↦
    match q with
    | .seek =>
      match w 2 with
      | some _ =>
        { inputTape := 0, workTapes := ![(none, 0), (none, 0), (none, 1), (none, 0)],
          output := none, state := some .seek }
      | none =>
        { inputTape := 0,
          workTapes := ![(none, 0), (none, 0), (none, -1), (some (some true), 0)],
          output := none, state := some .copy }
    | .copy =>
      match w 2 with
      | some b =>
        { inputTape := 0,
          workTapes := ![(none, -1), (none, -1), (some none, 0), (none, -1)],
          output := none, state := some (.put b) }
      | none =>
        { inputTape := 0,
          workTapes := ![(none, 0), (none, -1), (none, 1), (none, 0)],
          output := none, state := some .setFlag }
    | .put b =>
      { inputTape := 0,
        workTapes := ![(some (some b), 0), (none, 0), (none, -1), (none, 0)],
        output := none, state := some .copy }
    | .setFlag =>
      { inputTape := 0,
        workTapes := ![(none, 0), (some (some true), 1), (none, 0), (none, 0)],
        output := none, state := none }

private def blankTape : ℤ → Option Bool := tapeOfList []

private lemma blankTape_apply (z : ℤ) : blankTape z = none := by
  rcases lt_or_ge z 0 with hlt | hge
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero hlt; exact tapeOfList_negSucc [] m
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hge; simp [blankTape, tapeOfList_ofNat]

private def shiftedReadyTapes (u D : List Bool) : Fin 4 → ℤ → Option Bool :=
  ![shiftTape (-(u.length : ℤ)) (tapeOfList (u ++ D)),
    shiftTape (-(u.length : ℤ)) (Function.update (fun _ ↦ none) (-1) (some true)),
    blankTape,
    Function.update blankTape 0 (some true)]

private def shiftedReadyPos (u : List Bool) : Fin 4 → ℤ :=
  ![-(u.length : ℤ), -(u.length : ℤ), 0, -(u.length : ℤ)]

private lemma moveInputPos_zero_eq {n : ℕ} (ip : Fin (n + 2)) : moveInputPos ip 0 = ip :=
  Fin.ext (by simp)

private lemma apply_inputPos_zero {k : ℕ} {State : Type*} {inp : List Bool}
    {ip : Fin (inp.length + 2)} {wt : Fin k → ℤ → Option Bool} {wp : Fin k → ℤ}
    {out : List Bool} {q : Option State} {a : Action k Bool State} (ha : a.inputTape = 0) :
    (a.apply (⟨q, ip, wt, wp, out⟩ : Cfg k Bool State inp)).inputPos = ip := by
  dsimp only [Action.apply]; rw [ha]; exact moveInputPos_zero_eq ip

private lemma runFrom_prepNegTM {inp : List Bool} (ip : Fin (inp.length + 2))
    (u D out : List Bool) :
    prepNegTM.runFrom
      ⟨some .seek, ip, ![tapeOfList D, blankTape, tapeOfList u, blankTape], fun _ ↦ 0, out⟩
      (3 * u.length + 3) =
      ⟨none, ip, shiftedReadyTapes u D, shiftedReadyPos u, out⟩ := by
  have hseek : ∀ j ≤ u.length,
      prepNegTM.runFrom
        ⟨some .seek, ip, ![tapeOfList D, blankTape, tapeOfList u, blankTape],
          ![0, 0, (j : ℤ), 0], out⟩ (u.length - j + 1) =
      ⟨some .copy, ip,
        ![tapeOfList D, blankTape, tapeOfList u, Function.update blankTape 0 (some true)],
        ![0, 0, (u.length : ℤ) - 1, 0], out⟩ := by
    intro j hj
    obtain ⟨m, hm⟩ : ∃ m, u.length - j = m := ⟨_, rfl⟩
    induction m generalizing j with
    | zero =>
      obtain rfl : j = u.length := by omega
      rw [Nat.sub_self, Nat.zero_add, runFrom_succ_eq_step]; dsimp only [runFrom]
      rw [step_of_state rfl]
      have hw2 : tapeOfList u (u.length : ℤ) = none := by simp [tapeOfList_ofNat]
      refine Cfg.ext (by simp [prepNegTM, Cfg.workTapeSymbols, hw2])
        (apply_inputPos_zero (by simp [prepNegTM, Cfg.workTapeSymbols, hw2]))
        (funext fun i ↦ ?_) (funext fun i ↦ ?_)
        (by simp [prepNegTM, Cfg.workTapeSymbols, hw2, Action.apply]) <;>
        fin_cases i <;> simp [prepNegTM, Cfg.workTapeSymbols, hw2, Action.apply, sub_eq_add_neg]
    | succ m ih =>
      have hlt : j < u.length := by omega
      have hsub : u.length - (j + 1) = m := by omega
      rw [show u.length - j + 1 = (m + 1) + 1 by omega, runFrom_succ_eq_step]
      have h1 : prepNegTM.step
          ⟨some .seek, ip, ![tapeOfList D, blankTape, tapeOfList u, blankTape],
            ![0, 0, (j : ℤ), 0], out⟩ =
          ⟨some .seek, ip, ![tapeOfList D, blankTape, tapeOfList u, blankTape],
            ![0, 0, ((j + 1 : ℕ) : ℤ), 0], out⟩ := by
        rw [step_of_state rfl]
        have hw2 : tapeOfList u (j : ℤ) = some u[j] := by
          simp [tapeOfList_ofNat, List.getElem?_eq_getElem hlt]
        refine Cfg.ext (by simp [prepNegTM, Cfg.workTapeSymbols, hw2])
          (apply_inputPos_zero (by simp [prepNegTM, Cfg.workTapeSymbols, hw2]))
          (funext fun i ↦ ?_) (funext fun i ↦ ?_)
          (by simp [prepNegTM, Cfg.workTapeSymbols, hw2, Action.apply]) <;>
          fin_cases i <;> simp [prepNegTM, Cfg.workTapeSymbols, hw2, Action.apply]
      rw [h1, ← hsub]
      exact ih (j + 1) (by omega) hsub
  have hcopy : ∀ (u₁ u₂ : List Bool),
      prepNegTM.runFrom
        ⟨some .copy, ip,
          ![shiftTape (-(u₂.length : ℤ)) (tapeOfList (u₂ ++ D)),
            blankTape, tapeOfList u₁, Function.update blankTape 0 (some true)],
          ![-(u₂.length : ℤ), -(u₂.length : ℤ), (u₁.length : ℤ) - 1, -(u₂.length : ℤ)], out⟩
        (2 * u₁.length + 2) =
      ⟨none, ip, shiftedReadyTapes (u₁ ++ u₂) D, shiftedReadyPos (u₁ ++ u₂), out⟩ := by
    intro u₁
    induction u₁ using List.reverseRecOn with
    | nil =>
      intro u₂
      have hw2 : tapeOfList ([] : List Bool) (-1) = none := tapeOfList_negSucc [] 0
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.nil_append,
        CharP.cast_eq_zero]
      change prepNegTM.step (prepNegTM.step _) = _
      have hs1 : prepNegTM.step
          ⟨some .copy, ip,
            ![shiftTape (-(u₂.length : ℤ)) (tapeOfList (u₂ ++ D)),
              blankTape, tapeOfList [], Function.update blankTape 0 (some true)],
            ![-(u₂.length : ℤ), -(u₂.length : ℤ), 0 - 1, -(u₂.length : ℤ)], out⟩ =
          ⟨some .setFlag, ip,
            ![shiftTape (-(u₂.length : ℤ)) (tapeOfList (u₂ ++ D)),
              blankTape, blankTape, Function.update blankTape 0 (some true)],
            ![-(u₂.length : ℤ), -(u₂.length : ℤ) - 1, 0, -(u₂.length : ℤ)], out⟩ := by
        rw [step_of_state rfl]
        refine Cfg.ext (by simp [prepNegTM, Cfg.workTapeSymbols])
          (apply_inputPos_zero (by simp [prepNegTM, Cfg.workTapeSymbols]))
          (funext fun i ↦ ?_) (funext fun i ↦ ?_)
          (by simp [prepNegTM, Cfg.workTapeSymbols, Action.apply]) <;>
          fin_cases i <;>
            simp [prepNegTM, Cfg.workTapeSymbols, Action.apply, blankTape, sub_eq_add_neg]
      rw [hs1, step_of_state rfl]
      have hflag : Function.update blankTape (-(u₂.length : ℤ) - 1) (some true) =
          shiftTape (-(u₂.length : ℤ)) (Function.update (fun _ ↦ none) (-1) (some true)) := by
        have hb0 : blankTape = shiftTape (-(u₂.length : ℤ)) (fun _ ↦ none) := by
          funext z; exact blankTape_apply z
        rw [hb0, show -(u₂.length : ℤ) - 1 = (-1 : ℤ) + -(u₂.length : ℤ) by omega,
          update_shiftTape]
      have hp1 : -(u₂.length : ℤ) - 1 + 1 = -(u₂.length : ℤ) := by omega
      refine Cfg.ext (by simp [prepNegTM]) (apply_inputPos_zero (by simp [prepNegTM]))
        (funext fun i ↦ ?_) (funext fun i ↦ ?_) (by simp [prepNegTM, Action.apply]) <;>
        fin_cases i <;>
          simp [prepNegTM, Action.apply, shiftedReadyTapes, shiftedReadyPos, hflag, hp1]
    | append_singleton u₁' b ih =>
      intro u₂
      have hlen1 : ((u₁' ++ [b]).length : ℤ) - 1 = (u₁'.length : ℤ) := by simp
      have hw2 : tapeOfList (u₁' ++ [b]) (u₁'.length : ℤ) = some b := by simp [tapeOfList_ofNat]
      have ht : 2 * (u₁' ++ [b]).length + 2 = (2 * u₁'.length + 2) + 1 + 1 := by
        rw [List.length_append, List.length_singleton]; omega
      rw [ht, runFrom_succ_eq_step, runFrom_succ_eq_step, hlen1]
      have hs1 : prepNegTM.step
          ⟨some .copy, ip,
            ![shiftTape (-(u₂.length : ℤ)) (tapeOfList (u₂ ++ D)),
              blankTape, tapeOfList (u₁' ++ [b]), Function.update blankTape 0 (some true)],
            ![-(u₂.length : ℤ), -(u₂.length : ℤ), (u₁'.length : ℤ), -(u₂.length : ℤ)], out⟩ =
          ⟨some (.put b), ip,
            ![shiftTape (-(u₂.length : ℤ)) (tapeOfList (u₂ ++ D)),
              blankTape, tapeOfList u₁', Function.update blankTape 0 (some true)],
            ![-(u₂.length : ℤ) - 1, -(u₂.length : ℤ) - 1, (u₁'.length : ℤ),
              -(u₂.length : ℤ) - 1], out⟩ := by
        rw [step_of_state rfl]
        refine Cfg.ext (by simp [prepNegTM, Cfg.workTapeSymbols, hw2])
          (apply_inputPos_zero (by simp [prepNegTM, Cfg.workTapeSymbols, hw2]))
          (funext fun i ↦ ?_) (funext fun i ↦ ?_)
          (by simp [prepNegTM, Cfg.workTapeSymbols, hw2, Action.apply]) <;>
          fin_cases i <;>
            simp [prepNegTM, Cfg.workTapeSymbols, hw2, Action.apply, tapeOfList_erase_last,
              sub_eq_add_neg]
      have hs2 : prepNegTM.step
          ⟨some (.put b), ip,
            ![shiftTape (-(u₂.length : ℤ)) (tapeOfList (u₂ ++ D)),
              blankTape, tapeOfList u₁', Function.update blankTape 0 (some true)],
            ![-(u₂.length : ℤ) - 1, -(u₂.length : ℤ) - 1, (u₁'.length : ℤ),
              -(u₂.length : ℤ) - 1], out⟩ =
          ⟨some .copy, ip,
            ![shiftTape (-((b :: u₂).length : ℤ)) (tapeOfList ((b :: u₂) ++ D)),
              blankTape, tapeOfList u₁', Function.update blankTape 0 (some true)],
            ![-((b :: u₂).length : ℤ), -((b :: u₂).length : ℤ), (u₁'.length : ℤ) - 1,
              -((b :: u₂).length : ℤ)], out⟩ := by
        rw [step_of_state rfl]
        have hvip' :
            Function.update (shiftTape (-(u₂.length : ℤ)) (tapeOfList (u₂ ++ D)))
              (-1 + -(u₂.length : ℤ)) (some b) =
            shiftTape (-1 + -(u₂.length : ℤ)) (tapeOfList (b :: (u₂ ++ D))) := by
          have h := shiftTape_cons_append b u₂ D
          have he : -((b :: u₂).length : ℤ) = -1 + -(u₂.length : ℤ) := by
            rw [List.length_cons]; push_cast; omega
          have he2 : -(u₂.length : ℤ) - 1 = -1 + -(u₂.length : ℤ) := by omega
          simpa [he, he2] using h
        have hp : -(u₂.length : ℤ) - 1 = -((b :: u₂).length : ℤ) := by
          rw [List.length_cons]; push_cast; omega
        refine Cfg.ext (by simp [prepNegTM]) (apply_inputPos_zero (by simp [prepNegTM]))
          (funext fun i ↦ by fin_cases i <;> simp [prepNegTM, Action.apply, hvip', hp])
          (funext fun i ↦ by
            fin_cases i <;> simp [prepNegTM, Action.apply, hp, sub_eq_add_neg])
          (by simp [prepNegTM, Action.apply])
      rw [hs1, hs2, ih (b :: u₂), List.append_assoc, List.singleton_append]
  have hpos0 : (fun _ : Fin 4 ↦ (0 : ℤ)) = ![0, 0, ((0 : ℕ) : ℤ), 0] := by
    funext i; fin_cases i <;> rfl
  rw [show 3 * u.length + 3 = (u.length - 0 + 1) + (2 * u.length + 2) by omega,
    runFrom_add, hpos0, hseek 0 (Nat.zero_le _)]
  simpa [shiftTape_zero] using hcopy u []

/-- Control states for erasing the flag mark and sweeping `vip, flag, home` right across
`[-|u|, -1]` back to cell `0` without touching `D` at `[0, |D| - 1]`. -/
private inductive ClearNegState
  | stepL
  | eraseF
  | walk
  deriving DecidableEq

private instance instFiniteClearNegState : Finite ClearNegState :=
  Finite.of_injective
    (fun | .stepL => (0 : Fin 3) | .eraseF => 1 | .walk => 2)
    (fun a b h ↦ by cases a <;> cases b <;> first | rfl | (simp at h))

private noncomputable def clearNegTM : MultiTapeTM 4 Bool ClearNegState :=
  ofTr .stepL fun q _ w ↦
    match q with
    | .stepL =>
      { inputTape := 0, workTapes := ![(none, 0), (none, -1), (none, 0), (none, 0)],
        output := none, state := some .eraseF }
    | .eraseF =>
      { inputTape := 0, workTapes := ![(none, 0), (some none, 1), (none, 0), (none, 0)],
        output := none, state := some .walk }
    | .walk =>
      match w 3 with
      | none =>
        { inputTape := 0, workTapes := ![(some none, 1), (none, 1), (none, 0), (none, 1)],
          output := none, state := some .walk }
      | some _ =>
        { inputTape := 0, workTapes := ![(none, 0), (none, 0), (none, 0), (some none, 0)],
          output := none, state := none }

private lemma runFrom_clearNegTM {inp : List Bool} (ip : Fin (inp.length + 2))
    (u D out : List Bool) :
    clearNegTM.runFrom
      ⟨some .stepL, ip, shiftedReadyTapes u D, shiftedReadyPos u, out⟩
      (u.length + 3) =
      ⟨none, ip, ![tapeOfList D, blankTape, blankTape, blankTape], fun _ ↦ 0, out⟩ := by
  have hwalk : ∀ v : List Bool,
      clearNegTM.runFrom
        ⟨some .walk, ip,
          ![shiftTape (-(v.length : ℤ)) (tapeOfList (v ++ D)),
            blankTape, blankTape, Function.update blankTape 0 (some true)],
          ![-(v.length : ℤ), -(v.length : ℤ), 0, -(v.length : ℤ)], out⟩
        (v.length + 1) =
      ⟨none, ip, ![tapeOfList D, blankTape, blankTape, blankTape], fun _ ↦ 0, out⟩ := by
    intro v; induction v with
    | nil =>
      simp only [List.length_nil, CharP.cast_eq_zero, neg_zero, Nat.zero_add, List.nil_append,
        shiftTape_zero, runFrom_one]
      rw [step_of_state rfl]
      have hclrH : Function.update (Function.update blankTape 0 (some true)) 0 none =
          blankTape := by
        rw [Function.update_idem]; funext z
        by_cases hz : z = 0
        · subst hz; simp [blankTape_apply]
        · exact Function.update_of_ne hz _ _
      refine Cfg.ext (by simp [clearNegTM, Cfg.workTapeSymbols])
        (apply_inputPos_zero (by simp [clearNegTM, Cfg.workTapeSymbols]))
        (funext fun i ↦ ?_) (funext fun i ↦ ?_)
        (by simp [clearNegTM, Cfg.workTapeSymbols, Action.apply]) <;>
        fin_cases i <;> simp [clearNegTM, Cfg.workTapeSymbols, Action.apply, hclrH]
    | cons b vs ih =>
      rw [show (b :: vs).length + 1 = (vs.length + 1) + 1 by simp, runFrom_succ_eq_step]
      set m : ℤ := -(((b :: vs).length : ℤ))
      have hne0 : m ≠ 0 := by dsimp [m]; omega
      have hw3 : Function.update blankTape 0 (some true) m = none := by
        rw [Function.update_of_ne hne0, blankTape_apply]
      have hvip : Function.update (shiftTape m (tapeOfList ((b :: vs) ++ D))) m none =
          shiftTape (-(vs.length : ℤ)) (tapeOfList (vs ++ D)) :=
        erase_shiftTape_cons_append b vs D
      have hp : m + 1 = -(vs.length : ℤ) := by
        dsimp only [m]; simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; omega
      have hs : clearNegTM.step
          ⟨some .walk, ip,
            ![shiftTape m (tapeOfList ((b :: vs) ++ D)),
              blankTape, blankTape, Function.update blankTape 0 (some true)],
            ![m, m, 0, m], out⟩ =
          ⟨some .walk, ip,
            ![shiftTape (-(vs.length : ℤ)) (tapeOfList (vs ++ D)),
              blankTape, blankTape, Function.update blankTape 0 (some true)],
            ![-(vs.length : ℤ), -(vs.length : ℤ), 0, -(vs.length : ℤ)], out⟩ := by
        rw [step_of_state rfl]
        have hvip' : Function.update (shiftTape m (tapeOfList (b :: (vs ++ D)))) m none =
            shiftTape (-(vs.length : ℤ)) (tapeOfList (vs ++ D)) := hvip
        refine Cfg.ext (by simp [clearNegTM, Cfg.workTapeSymbols, hw3])
          (apply_inputPos_zero (by simp [clearNegTM, Cfg.workTapeSymbols, hw3]))
          (funext fun i ↦ by
            fin_cases i <;> simp [clearNegTM, Cfg.workTapeSymbols, hw3, Action.apply, hvip'])
          (funext fun i ↦ by
            fin_cases i <;> simp [clearNegTM, Cfg.workTapeSymbols, hw3, Action.apply, hp])
          (by simp [clearNegTM, Cfg.workTapeSymbols, hw3, Action.apply])
      rw [hs, ih]
  rw [show u.length + 3 = (u.length + 1) + 1 + 1 by omega,
    runFrom_succ_eq_step, runFrom_succ_eq_step]
  have hs1 : clearNegTM.step ⟨some .stepL, ip, shiftedReadyTapes u D, shiftedReadyPos u, out⟩ =
      ⟨some .eraseF, ip, shiftedReadyTapes u D,
        ![-(u.length : ℤ), -(u.length : ℤ) - 1, 0, -(u.length : ℤ)], out⟩ := by
    rw [step_of_state rfl]
    refine Cfg.ext (by simp [clearNegTM]) (apply_inputPos_zero (by simp [clearNegTM]))
      (funext fun i ↦ ?_) (funext fun i ↦ ?_) (by simp [clearNegTM, Action.apply]) <;>
      fin_cases i <;>
        simp [clearNegTM, Action.apply, shiftedReadyTapes, shiftedReadyPos, sub_eq_add_neg]
  have hs2 : clearNegTM.step
      ⟨some .eraseF, ip, shiftedReadyTapes u D,
        ![-(u.length : ℤ), -(u.length : ℤ) - 1, 0, -(u.length : ℤ)], out⟩ =
      ⟨some .walk, ip,
        ![shiftTape (-(u.length : ℤ)) (tapeOfList (u ++ D)),
          blankTape, blankTape, Function.update blankTape 0 (some true)],
        ![-(u.length : ℤ), -(u.length : ℤ), 0, -(u.length : ℤ)], out⟩ := by
    rw [step_of_state rfl]
    have hclrF : Function.update
        (shiftTape (-(u.length : ℤ)) (Function.update (fun _ ↦ none) (-1) (some true)))
        (-(u.length : ℤ) - 1) none = blankTape := by
      funext z; rw [blankTape_apply]
      by_cases hz : z = -(u.length : ℤ) - 1
      · subst hz; simp
      · rw [Function.update_of_ne hz, shiftTape, Function.update_of_ne (by omega)]
    have hpos_m1 : -(u.length : ℤ) - 1 + 1 = -(u.length : ℤ) := by omega
    refine Cfg.ext (by simp [clearNegTM]) (apply_inputPos_zero (by simp [clearNegTM]))
      (funext fun i ↦ ?_) (funext fun i ↦ ?_) (by simp [clearNegTM, Action.apply]) <;>
      fin_cases i <;> simp [clearNegTM, Action.apply, shiftedReadyTapes, hclrF, hpos_m1]
  rw [hs1, hs2, hwalk u]

/-! ### Single-query execution against stationary `D` in time `tM + 4 |u| + 6` -/

/-- Execute a tidy machine `M` on `u ++ D` where `D` sits stationary on `vip = Fin.natAdd k 0` and
`u` sits on `qryT = Fin.natAdd k 2`, restoring `D` untouched on `vip` and clearing `qryT` in
`tM + 4 * u.length + 6` steps (with zero `D.length` term). -/
private noncomputable def prependRunClear {k : ℕ} {State : Type}
    (M : MultiTapeTM k Bool State) :=
  (prepNegTM.extendTapes (Fin.natAddEmb k)).seq
    (((M.inputFromTape).extendTapes (Fin.castAddEmb 2)).seq
      (clearNegTM.extendTapes (Fin.natAddEmb k)))

private lemma transformsTapes_prependRunClear {k : ℕ} {State : Type}
    (M : MultiTapeTM k Bool State) {u D emit : List Bool} {tM sM : ℕ}
    (hM : M.ComputesTidilyInTimeAndSpace (u ++ D) emit tM sM) :
    TransformsTapes (prependRunClear M)
      (fun _ ws ↦ ws = Function.update
        (Function.update (fun _ ↦ []) (Fin.natAdd k 0) D) (Fin.natAdd k 2) u)
      (fun _ _ ws' em ↦ ws' = Function.update (fun _ ↦ []) (Fin.natAdd k 0) D ∧ em = emit)
      ((3 * u.length + 3) + (tM + (u.length + 3)))
      (4 * (3 * u.length + 4) + (k + 4) +
        (sM + 2 * ((u ++ D).length + 2) + 2 + (4 * (u.length + 4) + (k + 4)))) := by
  refine transformsTapes_iff_runFrom.mpr fun outer ws out hws ↦ ?_
  subst hws
  let eAux : Fin 4 ↪ Fin (k + 4) := Fin.natAddEmb k
  let eM : Fin (k + 2) ↪ Fin (k + 4) := Fin.castAddEmb 2
  let blankK : Fin (k + 4) → ℤ → Option Bool := fun _ ↦ blankTape
  let zeroK : Fin (k + 4) → ℤ := fun _ ↦ 0
  let startAux : Cfg 4 Bool PrepNegState outer :=
    ⟨some .seek, 1, ![tapeOfList D, blankTape, tapeOfList u, blankTape], fun _ ↦ 0, out⟩
  let midTapes : Fin (k + 4) → ℤ → Option Bool :=
    Fin.append (fun _ : Fin k ↦ blankTape) (shiftedReadyTapes u D)
  let midPos : Fin (k + 4) → ℤ :=
    Fin.append (fun _ : Fin k ↦ (0 : ℤ)) (shiftedReadyPos u)
  -- Phase 1: `prepNegTM.extendTapes eAux`
  have hstart_eq :
      wordsCfg outer (some (prepNegTM.extendTapes eAux).q₀)
        (Function.update (Function.update (fun _ ↦ []) (Fin.natAdd k 0) D) (Fin.natAdd k 2) u)
        out =
      embed eAux startAux blankK zeroK := by
    refine Cfg.ext rfl rfl (funext fun l ↦ ?_) (funext fun l ↦ ?_) rfl
    · induction l using Fin.addCases with
      | left j =>
        have hnone : partialInv eAux (j.castAdd 4) = none :=
          partialInv_eq_none eAux fun ⟨r, hr⟩ ↦ by
            have := congrArg Fin.val hr; simp [eAux] at this; omega
        simp [embed, hnone, wordsCfg, blankK, blankTape,
          show j.castAdd 4 ≠ Fin.natAdd k 0 from fun h ↦ by
            have := congrArg Fin.val h; simp at this; omega,
          show j.castAdd 4 ≠ Fin.natAdd k 2 from fun h ↦ by
            have := congrArg Fin.val h; simp at this; omega]
      | right r =>
        have hpi : partialInv (Fin.natAddEmb k) (Fin.natAdd k r) = some r :=
          partialInv_embed (Fin.natAddEmb k) r
        simp only [embed, eAux, hpi]
        fin_cases r <;> simp [wordsCfg, startAux, Function.update_apply, blankTape]
    · simp only [wordsCfg, embed, zeroK]; cases partialInv eAux l <;> rfl
  have hrun1 : (prepNegTM.extendTapes eAux).runFrom (embed eAux startAux blankK zeroK)
      (3 * u.length + 3) = ⟨none, 1, midTapes, midPos, out⟩ := by
    have hmap := MultiTapeNTM.RunPath.map_ofDeterministic
      (embedHom prepNegTM eAux blankK zeroK) startAux (3 * u.length + 3)
    have hlast : (prepNegTM.extendTapes eAux).runFrom (embed eAux startAux blankK zeroK)
        (3 * u.length + 3) =
        embed eAux (prepNegTM.runFrom startAux (3 * u.length + 3)) blankK zeroK :=
      (congrArg RelSeries.last hmap).symm
    rw [hlast, show prepNegTM.runFrom startAux (3 * u.length + 3) = _ from
      runFrom_prepNegTM 1 u D out]
    refine Cfg.ext rfl rfl (funext fun l ↦ ?_) (funext fun l ↦ ?_) rfl <;>
      induction l using Fin.addCases with
      | left j =>
        have hnone : partialInv eAux (j.castAdd 4) = none :=
          partialInv_eq_none eAux fun ⟨r, hr⟩ ↦ by
            have := congrArg Fin.val hr; simp [eAux] at this; omega
        simp [embed, hnone, midTapes, midPos, blankK, zeroK]
      | right r =>
        have hpi : partialInv (Fin.natAddEmb k) (Fin.natAdd k r) = some r :=
          partialInv_embed (Fin.natAddEmb k) r
        simp [embed, eAux, hpi, midTapes, midPos]
  have hsp1 : (MultiTapeNTM.RunPath.ofDeterministic (prepNegTM.extendTapes eAux)
      (embed eAux startAux blankK zeroK) (3 * u.length + 3)).space ≤
      4 * (3 * u.length + 4) + (k + 4) := by
    refine (space_embed_le prepNegTM eAux startAux blankK zeroK _).trans ?_
    have h1 := (MultiTapeNTM.RunPath.ofDeterministic prepNegTM startAux
      (3 * u.length + 3)).space_le_mul_time_add_one
    have h2 : (MultiTapeNTM.RunPath.ofDeterministic prepNegTM startAux
      (3 * u.length + 3)).time = 3 * u.length + 3 := rfl
    omega
  -- Phase 2: `(M.inputFromTape).extendTapes eM` via tape shift `δ`
  obtain ⟨hMrun, hMsp⟩ := computesTidily_iff_runFrom.mp hM
  let cM0 : Cfg (k + 2) Bool State outer :=
    inCfg true (wordsCfg (u ++ D) (some M.q₀) (fun _ ↦ []) out) outer
  let cM1 : Cfg (k + 2) Bool State outer :=
    inCfg true (wordsCfg (u ++ D) none (fun _ ↦ []) (out ++ emit)) outer
  have hMrun_out : M.runFrom (wordsCfg (u ++ D) (some M.q₀) (fun _ ↦ []) out) tM =
      wordsCfg (u ++ D) none (fun _ ↦ []) (out ++ emit) := by
    have h := prependOutput_runFrom M (wordsCfg (u ++ D) (some M.q₀) (fun _ ↦ []) []) out tM
    rw [hMrun] at h; simpa [wordsCfg] using h
  have hMsp_out : (MultiTapeNTM.RunPath.ofDeterministic M
      (wordsCfg (u ++ D) (some M.q₀) (fun _ ↦ []) out) tM).space ≤ sM := by
    rw [space_eq_of_workTapePos (tm' := M)
      (wordsCfg (u ++ D) (some M.q₀) (fun _ ↦ []) out)
      (wordsCfg (u ++ D) (some M.q₀) (fun _ ↦ []) []) tM fun m _ ↦ by
        have h := prependOutput_runFrom M (wordsCfg (u ++ D) (some M.q₀) (fun _ ↦ []) []) out m
        simpa [wordsCfg] using congrArg Cfg.workTapePos h]
    exact hMsp
  have hin_run : M.inputFromTape.runFrom cM0 tM = cM1 := by
    have hlast : M.inputFromTape.runFrom cM0 tM =
        inCfg true (M.runFrom (wordsCfg (u ++ D) (some M.q₀) (fun _ ↦ []) out) tM) outer :=
      (congrArg RelSeries.last (MultiTapeNTM.RunPath.map_ofDeterministic
        (inCfgHom M true outer) (wordsCfg (u ++ D) (some M.q₀) (fun _ ↦ []) out) tM)).symm
    rw [hlast, hMrun_out]
  have hin_sp : (MultiTapeNTM.RunPath.ofDeterministic M.inputFromTape cM0 tM).space ≤
      sM + 2 * ((u ++ D).length + 2) := by
    have hmap := MultiTapeNTM.RunPath.map_ofDeterministic
      (inCfgHom M true outer) (wordsCfg (u ++ D) (some M.q₀) (fun _ ↦ []) out) tM
    simp only [inCfgHom_apply] at hmap
    rw [show cM0 = _ from rfl, ← hmap]
    exact (space_map_inCfgHom_le M true outer _).trans (Nat.add_le_add_right hMsp_out _)
  let δ : Fin (k + 2) → ℤ :=
    Fin.append (fun _ : Fin k ↦ (0 : ℤ)) ![-(u.length : ℤ), -(u.length : ℤ)]
  have hmid_eq : (⟨some ((M.inputFromTape).extendTapes eM).q₀, 1, midTapes, midPos, out⟩ :
      Cfg (k + 4) Bool State outer) = embed eM (shiftCfg δ cM0) midTapes midPos := by
    refine Cfg.ext rfl rfl (funext fun l ↦ ?_) (funext fun l ↦ ?_) rfl
    · rcases hl : partialInv eM l with _ | i
      · simp [embed, hl]
      · obtain rfl := partialInv_eq_some eM hl
        have hpi : partialInv eM (eM i) = some i := by simp
        simp only [embed, hpi]
        induction i using Fin.addCases with
        | left j =>
          change midTapes (j.castAdd 4) = _
          simp [midTapes, shiftCfg, δ, cM0, inCfg_wordsCfg, shiftTape_zero, blankTape]
        | right r =>
          fin_cases r
          · change midTapes (Fin.natAdd k 0) = _
            simp [midTapes, shiftedReadyTapes, shiftCfg, δ, cM0, inCfg_wordsCfg]
          · change midTapes (Fin.natAdd k 1) = _
            simp [midTapes, shiftedReadyTapes, shiftCfg, δ, cM0, inCfg_wordsCfg]
    · rcases hl : partialInv eM l with _ | i
      · simp [embed, hl]
      · obtain rfl := partialInv_eq_some eM hl
        have hpi : partialInv eM (eM i) = some i := by simp
        simp only [embed, hpi]
        induction i using Fin.addCases with
        | left j =>
          change midPos (j.castAdd 4) = _
          simp [midPos, shiftCfg, δ, cM0, inCfg_wordsCfg]
        | right r =>
          fin_cases r
          · change midPos (Fin.natAdd k 0) = _
            simp [midPos, shiftedReadyPos, shiftCfg, δ, cM0, inCfg_wordsCfg]
          · change midPos (Fin.natAdd k 1) = _
            simp [midPos, shiftedReadyPos, shiftCfg, δ, cM0, inCfg_wordsCfg]
  have hrun2 : ((M.inputFromTape).extendTapes eM).runFrom (input := outer)
      ⟨some ((M.inputFromTape).extendTapes eM).q₀, 1, midTapes, midPos, out⟩ tM =
      ⟨none, 1, midTapes, midPos, out ++ emit⟩ := by
    rw [hmid_eq]
    have hlast : ((M.inputFromTape).extendTapes eM).runFrom
        (embed eM (shiftCfg δ cM0) midTapes midPos) tM =
        embed eM (M.inputFromTape.runFrom (shiftCfg δ cM0) tM) midTapes midPos :=
      (congrArg RelSeries.last (MultiTapeNTM.RunPath.map_ofDeterministic
        (embedHom M.inputFromTape eM midTapes midPos) (shiftCfg δ cM0) tM)).symm
    rw [hlast, runFrom_shiftCfg, hin_run]
    refine Cfg.ext rfl rfl (funext fun l ↦ ?_) (funext fun l ↦ ?_) rfl
    · rcases hl : partialInv eM l with _ | i
      · simp [embed, hl]
      · obtain rfl := partialInv_eq_some eM hl
        have hpi : partialInv eM (eM i) = some i := by simp
        simp only [embed, hpi]
        induction i using Fin.addCases with
        | left j =>
          change _ = midTapes (j.castAdd 4)
          simp [midTapes, shiftCfg, δ, cM1, inCfg_wordsCfg, shiftTape_zero, blankTape]
        | right r =>
          fin_cases r
          · change _ = midTapes (Fin.natAdd k 0)
            simp [midTapes, shiftedReadyTapes, shiftCfg, δ, cM1, inCfg_wordsCfg]
          · change _ = midTapes (Fin.natAdd k 1)
            simp [midTapes, shiftedReadyTapes, shiftCfg, δ, cM1, inCfg_wordsCfg]
    · rcases hl : partialInv eM l with _ | i
      · simp [embed, hl]
      · obtain rfl := partialInv_eq_some eM hl
        have hpi : partialInv eM (eM i) = some i := by simp
        simp only [embed, hpi]
        induction i using Fin.addCases with
        | left j =>
          change _ = midPos (j.castAdd 4)
          simp [midPos, shiftCfg, δ, cM1, inCfg_wordsCfg]
        | right r =>
          fin_cases r
          · change _ = midPos (Fin.natAdd k 0)
            simp [midPos, shiftedReadyPos, shiftCfg, δ, cM1, inCfg_wordsCfg]
          · change _ = midPos (Fin.natAdd k 1)
            simp [midPos, shiftedReadyPos, shiftCfg, δ, cM1, inCfg_wordsCfg]
  have hsp2 : (MultiTapeNTM.RunPath.ofDeterministic ((M.inputFromTape).extendTapes eM)
      (⟨some ((M.inputFromTape).extendTapes eM).q₀, 1, midTapes, midPos, out⟩ :
        Cfg (k + 4) Bool State outer) tM).space ≤
      sM + 2 * ((u ++ D).length + 2) + 2 := by
    rw [hmid_eq]
    refine (space_embed_le M.inputFromTape eM (shiftCfg δ cM0) midTapes midPos tM).trans ?_
    have := (space_shiftCfg_le M.inputFromTape δ cM0 tM).trans hin_sp
    omega
  -- Phase 3: `clearNegTM.extendTapes eAux`
  let clrAux : Cfg 4 Bool ClearNegState outer :=
    ⟨some .stepL, 1, shiftedReadyTapes u D, shiftedReadyPos u, out ++ emit⟩
  have hclr_eq : (⟨some (clearNegTM.extendTapes eAux).q₀, 1, midTapes, midPos, out ++ emit⟩ :
      Cfg (k + 4) Bool ClearNegState outer) = embed eAux clrAux blankK zeroK := by
    refine Cfg.ext rfl rfl (funext fun l ↦ ?_) (funext fun l ↦ ?_) rfl <;>
      induction l using Fin.addCases with
      | left j =>
        have hnone : partialInv eAux (j.castAdd 4) = none :=
          partialInv_eq_none eAux fun ⟨r, hr⟩ ↦ by
            have := congrArg Fin.val hr; simp [eAux] at this; omega
        simp [embed, hnone, midTapes, midPos, blankK, zeroK]
      | right r =>
        have hpi : partialInv (Fin.natAddEmb k) (Fin.natAdd k r) = some r :=
          partialInv_embed (Fin.natAddEmb k) r
        simp [embed, eAux, hpi, midTapes, midPos, clrAux]
  let endWs : Fin (k + 4) → List Bool := Function.update (fun _ ↦ []) (Fin.natAdd k 0) D
  have hrun3 : (clearNegTM.extendTapes eAux).runFrom
      ⟨some (clearNegTM.extendTapes eAux).q₀, 1, midTapes, midPos, out ++ emit⟩
      (u.length + 3) = wordsCfg outer none endWs (out ++ emit) := by
    rw [hclr_eq]
    have hlast : (clearNegTM.extendTapes eAux).runFrom (embed eAux clrAux blankK zeroK)
        (u.length + 3) = embed eAux (clearNegTM.runFrom clrAux (u.length + 3)) blankK zeroK :=
      (congrArg RelSeries.last (MultiTapeNTM.RunPath.map_ofDeterministic
        (embedHom clearNegTM eAux blankK zeroK) clrAux (u.length + 3))).symm
    rw [hlast, show clearNegTM.runFrom clrAux (u.length + 3) = _ from
      runFrom_clearNegTM 1 u D (out ++ emit)]
    refine Cfg.ext rfl rfl (funext fun l ↦ ?_) (funext fun l ↦ ?_) rfl
    · induction l using Fin.addCases with
      | left j =>
        have hnone : partialInv eAux (j.castAdd 4) = none :=
          partialInv_eq_none eAux fun ⟨r, hr⟩ ↦ by
            have := congrArg Fin.val hr; simp [eAux] at this; omega
        have hne : j.castAdd 4 ≠ Fin.natAdd k 0 := fun h ↦ by
          have := congrArg Fin.val h; simp at this; omega
        simp [embed, hnone, wordsCfg, endWs, Function.update_of_ne hne, blankK, blankTape]
      | right r =>
        have hpi : partialInv eAux (eAux r) = some r := by simp
        change (embed eAux _ blankK zeroK).workTapes (eAux r) = tapeOfList (endWs (eAux r))
        simp only [embed, hpi]
        fin_cases r <;> simp [eAux, endWs, blankTape]
    · simp only [embed, wordsCfg, zeroK]; cases partialInv eAux l <;> rfl
  have hsp3 : (MultiTapeNTM.RunPath.ofDeterministic (clearNegTM.extendTapes eAux)
      (⟨some (clearNegTM.extendTapes eAux).q₀, 1, midTapes, midPos, out ++ emit⟩ :
        Cfg (k + 4) Bool ClearNegState outer)
      (u.length + 3)).space ≤ 4 * (u.length + 4) + (k + 4) := by
    rw [hclr_eq]
    refine (space_embed_le clearNegTM eAux clrAux blankK zeroK _).trans ?_
    have h1 := (MultiTapeNTM.RunPath.ofDeterministic clearNegTM clrAux
      (u.length + 3)).space_le_mul_time_add_one
    have h2 : (MultiTapeNTM.RunPath.ofDeterministic clearNegTM clrAux
      (u.length + 3)).time = u.length + 3 := rfl
    omega
  -- Compose Phase 2 + Phase 3, then Phase 1 + (Phase 2 + Phase 3)
  have hrun23 := runFrom_seq hrun2 rfl hrun3 rfl
  have hsp23 := (space_seq_le hrun2 rfl (by dsimp only [Cfg.withState]; rw [hrun3]; rfl)).trans
    (Nat.add_le_add hsp2 hsp3)
  have hrun1' := hstart_eq ▸ hrun1
  have hrun123 := runFrom_seq hrun1' rfl hrun23 rfl
  have hsp123 := (space_seq_le hrun1' rfl (by
    change (((M.inputFromTape).extendTapes eM).seq (clearNegTM.extendTapes eAux)).runFrom
      (Cfg.mapState (handOver (clearNegTM.extendTapes eAux).q₀)
        ⟨some ((M.inputFromTape).extendTapes eM).q₀, 1, midTapes, midPos, out⟩)
      (tM + (u.length + 3)) |>.Halted
    rw [hrun23]; rfl)).trans
    (Nat.add_le_add (hstart_eq ▸ hsp1) hsp23)
  exact ⟨endWs, emit, hrun123, ⟨rfl, rfl⟩, hsp123⟩

/-! ### Full persistent-tape batch-query machine -/

private noncomputable def batchQueryRound {k : ℕ} {State : Type}
    (M : MultiTapeTM k Bool State) :=
  (appendRead rawFrameReader (Fin.natAdd k 2)).seq (prependRunClear M).freezeInput

private noncomputable def batchQueryTM {k : ℕ} {State : Type}
    (M : MultiTapeTM k Bool State) :=
  (appendRead unframeReader (Fin.natAdd k 0)).seq
    ((whileInput (batchQueryRound M)).seq
      (((clearWork Bool).extendTapes (tapeEmb (Fin.natAdd k 0))).freezeInput.seq
        (rewindInputOn (k + 4) Bool)))

/-- **Persistent-tape batch-query theorem**: given any deterministic multi-tape Turing machine
computing `qry : List Bool × List Bool → β` on `encPair encBits encBits (b, D) = frame b ++ D` in
time `tq (b, D)` and space `sq (b, D)`, there is a deterministic multi-tape Turing machine
computing `fun (D, B) ↦ B.map fun b ↦ qry (b, D)` on `encPair encBits (encList encBits)` in total
time `O(|D| + |encList encBits B| + 1 + ∑_{b ∈ B} (tq (b, D) + |b| + 1))` — keeping `D` stationary
on a dedicated work tape across all `|B|` queries with **zero `|B| · |D|` re-copying overhead**. -/
theorem computableInTimeAndSpace_batchQuery {β : Type} {encOut : β ↪ List Bool}
    {qry : List Bool × List Bool → β} {tq sq : List Bool × List Bool → ℕ}
    (hqry : ComputableInTimeAndSpace qry (encPair encBits encBits) encOut tq sq) :
    ∃ (C : ℕ) (t s : List Bool × List (List Bool) → ℕ),
      ComputableInTimeAndSpace
        (fun p : List Bool × List (List Bool) ↦ p.2.map fun b ↦ qry (b, p.1))
        (encPair encBits (encList encBits)) (encList encOut) t s ∧
      ∀ (D : List Bool) (B : List (List Bool)),
        t (D, B) ≤ C * (D.length + (encList encBits B).length + 1 +
          ∑ j ∈ Finset.range B.length, (tq (B[j]?.getD [], D) + (B[j]?.getD []).length + 1)) := by
  -- Wrap `qry` to emit `frame (encOut (qry x))` in linear extra time `O(|encOut| + 1)` via a
  -- 1-state `Transducer`, composing tidily with `NormalForm.exactBounds hqry_raw`.
  have hfr_tidy : ComputableTidilyInTimeAndSpace id encBits (encFramed encBits)
      (fun w ↦ 4 * w.length + 8) (fun _ ↦ 0) := by
    let τ : Transducer Bool Unit :=
      { q₀ := ()
        step := fun _ b ↦ ((), [true, b])
        final := fun _ ↦ [false]
        length_step_le := fun _ _ ↦ le_rfl
        length_final_le := fun _ ↦ by decide }
    refine τ.computableTidilyInTimeAndSpace fun w ↦ ?_
    simp only [encFramed_apply, encBits_apply, id_eq]
    induction w with
    | nil => simp [Transducer.run, τ]
    | cons b bs ih => rw [frame_cons, ih]; simp [Transducer.run, τ]
  have hqry_raw : ComputableInTimeAndSpace (fun x ↦ encOut (qry x))
      (encPair encBits encBits) encBits tq sq :=
    let ⟨k0, S0, hf0, tm0, h0⟩ := hqry; ⟨k0, S0, hf0, tm0, h0⟩
  obtain ⟨CN, -, hqry_tidy⟩ := Internal.NormalForm.exactBounds hqry_raw
  obtain ⟨cF, k, State, hfin, M, hMtidy⟩ :=
    ComputableTidilyInTimeAndSpace.comp hfr_tidy hqry_tidy
  have hrun_out_le : ∀ {k' : ℕ} {St : Type} (tm : MultiTapeTM k' Bool St) {inp : List Bool}
      (c : Cfg k' Bool St inp) (n : ℕ), (tm.runFrom c n).output.length ≤ c.output.length + n := by
    intro k' St tm inp c n; induction n generalizing c with
    | zero => simp [runFrom]
    | succ n ih =>
      rw [runFrom_succ_eq_step]
      refine (ih (tm.step c)).trans ?_
      rcases hs : c.state with _ | q
      · rw [step_of_halt hs]; omega
      · rw [step_of_state hs]; dsimp only [Action.apply]
        cases (tm.tr q _ _).output <;>
          simp only [Option.toList_none, Option.toList_some, List.append_nil, List.length_append,
            List.length_singleton] <;> omega
  have hout_le : ∀ x, (encOut (qry x)).length ≤ CN * (tq x + 1) := by
    obtain ⟨kt, St, _, tmt, ht⟩ := hqry_tidy
    intro x
    obtain ⟨hr, -⟩ := computesTidily_iff_runFrom.mp (ht x)
    have h := hrun_out_le tmt (wordsCfg (encPair encBits encBits x) (some tmt.q₀) (fun _ ↦ []) [])
      (CN * (tq x + 1))
    rw [hr] at h; simpa [wordsCfg, encBits_apply] using h
  -- Exact time/space functions of `M` on `x = (b, D)`:
  set tM : List Bool × List Bool → ℕ := fun x ↦
    CN * (tq x + 1) + (4 * (encOut (qry x)).length + 8) + 4 * (encOut (qry x)).length + 9
  set sM : List Bool × List Bool → ℕ := fun x ↦
    CN * (sq x + 1) + 0 + 5 * (encOut (qry x)).length + cF
  let vip : Fin (k + 4) := Fin.natAdd k 0
  let qryT : Fin (k + 4) := Fin.natAdd k 2
  have hvq : vip ≠ qryT := fun h ↦ by have := congrArg Fin.val h; simp [vip, qryT] at this
  let rTime (D b : List Bool) : ℕ :=
    0 + 1 + (((frame b).length + 1) + ((frame b).length + 2)) +
      ((3 * (frame b).length + 3) + (tM (b, D) + ((frame b).length + 3)))
  let rSpace (D : List Bool) (B : List (List Bool)) : ℕ :=
    (B.map fun b ↦
      ((frame b).length + 2 + (k + 3)) +
        (4 * (3 * (frame b).length + 4) + (k + 4) +
          (sM (b, D) + 2 * ((frame b ++ D).length + 2) + 2 +
            (4 * ((frame b).length + 4) + (k + 4))))).foldl max (k + 4)
  let totalT (p : List Bool × List (List Bool)) : ℕ :=
    let D := p.1; let B := p.2
    let x := encPair encBits (encList encBits) p
    (0 + 1 + (((frame D).length + 1) + (D.length + 2))) +
      ((∑ j ∈ Finset.range B.length, (rTime D (B[j]?.getD []) + 1) + 1) +
        (3 * (D.length + 1) + (x.length + 2)))
  let totalS (p : List Bool × List (List Bool)) : ℕ :=
    let D := p.1; let B := p.2
    (D.length + 2 + (k + 3)) +
      ((2 * (k + 4) * rSpace D B + (k + 4)) + ((D.length + 1 + (k + 4)) + (k + 4)))
  have hfold_max : ∀ (l : List ℕ) (m z : ℕ), z ∈ l → z ≤ l.foldl max m := by
    intro l; induction l with
    | nil => intro _ _ hz; simp at hz
    | cons y ys ih =>
      intro m z hz; rcases List.mem_cons.mp hz with rfl | hm
      · have hle : ∀ (u : List ℕ) (a : ℕ), a ≤ u.foldl max a := by
          intro u; induction u with
          | nil => intro _; exact le_rfl
          | cons _ _ iu => intro a; exact (le_max_left _ _).trans (iu _)
        exact (le_max_right m z).trans (hle ys (max m z))
      · exact ih (max m y) z hm
  have htm_batch : (batchQueryTM M).ComputesFunInTimeAndSpace
      (encPair encBits (encList encBits)) (encList encOut)
      (fun p ↦ p.2.map fun b ↦ qry (b, p.1)) totalT totalS := by
    refine ComputesFunTidilyInTimeAndSpace.computesFunInTimeAndSpace fun ⟨D, B⟩ ↦ ?_
    let toks : List (List Bool) := B.map frame
    have hfl_enc : encList encBits B = toks.flatten := by
      dsimp [toks]; clear *-
      induction B with | nil => rfl | cons b bs ih => simp [encList_cons, ih]
    let x : List Bool := frame D ++ toks.flatten
    have hx_eq : encPair encBits (encList encBits) (D, B) = x := by
      simp [encPair_apply, encBits_apply, hfl_enc, x]
    have hfl_out : encList encOut (B.map fun b ↦ qry (b, D)) =
        ((List.range toks.length).map fun j ↦
          frame (encOut (qry (B[j]?.getD [], D)))).flatten := by
      have h1 : ∀ l : List β, encList encOut l = (l.map fun v ↦ frame (encOut v)).flatten := by
        intro l; induction l with | nil => rfl | cons v vs ih => simp [encList_cons, ih]
      rw [h1, List.map_map]; dsimp [toks]; rw [List.length_map]
      congr 1; apply List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
      have hj : j < B.length := by simpa using h1
      simp [List.getElem?_eq_getElem hj]
    -- Phase A: load `D` onto `vip`
    have hv1 : (1 : Fin (x.length + 2)).val = 1 := by
      change 1 % (x.length + 2) = 1; exact Nat.mod_eq_of_lt (by omega)
    have hpos1 : (1 : Fin (x.length + 2)).val ≠ 0 := by rw [hv1]; decide
    have hrd0 : unframeReader.read unframeReader.q₀
        (x.drop ((1 : Fin (x.length + 2)).val - 1)) = (D, (frame D).length) := by
      rw [hv1, Nat.sub_self, List.drop_zero]; exact read_unframeReader D toks.flatten
    have hA : TransformsTapesAt (appendRead unframeReader vip)
        (fun inp p ws ↦ inp = x ∧ p = 1 ∧ ws = fun _ ↦ [])
        (fun inp _ _ p' ws' em ↦ inp = x ∧ p'.val = 1 + (frame D).length ∧
          ws' = Function.update (fun _ ↦ []) vip D ∧ em = [])
        (0 + 1 + (((frame D).length + 1) + (D.length + 2)))
        (D.length + 2 + (k + 3)) := by
      have h := transformsTapesAt_appendRead (k := k + 4) unframeReader vip x 1 hpos1 []
      dsimp only at h; rw [hrd0, List.nil_append] at h
      exact h.imp (by rintro _ _ _ ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩)
        (fun _ _ ws p' ws' e ⟨hx, _, hws⟩ ⟨hp', hws', he⟩ ↦
          ⟨hx, by rw [hp', hv1], by rw [hws', hws], he⟩)
        (by simp) (by simp)
    -- Phase B: `whileInput (batchQueryRound M)`
    let L (j : ℕ) : ℕ := (frame D).length + (toks.take j).flatten.length
    have hposL (j : ℕ) : 1 + L j < x.length + 2 := by
      have := streamPos_lt toks j; simp only [x, L, List.length_append]; omega
    let es (j : ℕ) : List Bool := frame (encOut (qry (B[j]?.getD [], D)))
    let Pinv (n : ℕ) (inp : List Bool) (p : Fin (inp.length + 2))
        (ws : Fin (k + 4) → List Bool) (em : List Bool) : Prop :=
      inp = x ∧ p.val = 1 + L n ∧ ws = Function.update (fun _ ↦ []) vip D ∧
        em = ((List.range n).map es).flatten
    have hround : ∀ n < toks.length, ∀ acc, TransformsTapesAt (batchQueryRound M)
        (fun inp p ws ↦ Pinv n inp p ws acc)
        (fun inp _ _ p' ws' e ↦ Pinv (n + 1) inp p' ws' (acc ++ e))
        (rTime D (B[n]?.getD [])) (rSpace D B) := by
      intro n hn acc
      have hnB : n < B.length := by simpa [toks] using hn
      set b := B[n]
      have hbn : B[n]?.getD [] = b := by simp [List.getElem?_eq_getElem hnB, b]
      have htn : toks[n] = frame b := by simp [toks, b]
      let p₀ : Fin (x.length + 2) := ⟨1 + L n, hposL n⟩
      have hrd : rawFrameReader.read rawFrameReader.q₀ (x.drop (p₀.val - 1)) =
          (frame b, (frame b).length) := by
        have hdrop : x.drop (p₀.val - 1) = toks.flatten.drop (toks.take n).flatten.length := by
          simp only [p₀, L, x, Nat.add_sub_cancel_left]; rw [← List.drop_drop, List.drop_left]
        rw [hdrop, List.drop_flatten_take toks hn, htn]
        exact read_rawFrameReader b _
      have hr1 := transformsTapesAt_appendRead (k := k + 4) rawFrameReader qryT x p₀
        (by simp [p₀]) []
      dsimp only at hr1; rw [hrd, List.nil_append] at hr1
      have htidy : M.ComputesTidilyInTimeAndSpace (frame b ++ D) (es n)
          (tM (b, D)) (sM (b, D)) := by
        have h := hMtidy (b, D)
        simpa [encPair_apply, encBits_apply, encFramed_apply, es, hbn, tM, sM] using h
      have hr2 := (transformsTapes_prependRunClear M htidy).freezeInput
      have hsp_le : ((frame b).length + 2 + (k + 3)) +
          (4 * (3 * (frame b).length + 4) + (k + 4) +
            (sM (b, D) + 2 * ((frame b ++ D).length + 2) + 2 +
              (4 * ((frame b).length + 4) + (k + 4)))) ≤ rSpace D B :=
        hfold_max _ _ _ (List.mem_map.mpr ⟨b, List.getElem_mem hnB, rfl⟩)
      have hr1' : TransformsTapesAt (appendRead rawFrameReader qryT)
          (fun inp p ws ↦ Pinv n inp p ws acc)
          (fun inp _ _ p' ws' e ↦ inp = x ∧ p'.val = p₀.val + (frame b).length ∧
            ws' = Function.update (Function.update (fun _ ↦ []) vip D) qryT (frame b) ∧ e = [])
          (0 + 1 + (((frame b).length + 1) + ((frame b).length + 2)))
          ((frame b).length + 2 + (k + 3)) :=
        hr1.imp
          (fun _ _ ws ⟨hx, hp, hws, _⟩ ↦
            ⟨hx, hp, by rw [hws, Function.update_of_ne hvq.symm]⟩)
          (fun _ _ _ _ _ _ ⟨hx, _, hws, _⟩ ⟨hp', hws', he⟩ ↦
            ⟨hx, hp', by rw [hws', hws], he⟩)
          (by simp) (by simp)
      refine (transformsTapesAt_seq hr1' hr2
        fun _ _ _ _ _ _ _ ⟨_, _, hws', _⟩ ↦ hws').imp
        (fun _ _ _ h ↦ h)
        (fun _ _ _ p' ws' em hpre hpost ↦ ?_)
        (by simp [rTime, hbn])
        (by simpa using hsp_le)
      rcases hpre with ⟨rfl, _, _, rfl⟩
      obtain ⟨_, _, _, _, ⟨_, hp1, _, he1⟩, ⟨rfl, hws2, he2⟩, hem⟩ := hpost
      refine ⟨rfl, ?_, hws2, by simp [hem, he1, he2, List.range_succ]⟩
      rw [hp1]; dsimp [p₀, L]
      rw [List.length_flatten_take_succ toks hn, htn]; omega
    have hmore : ∀ n < toks.length, ∀ inp p ws em, Pinv n inp p ws em →
        inputSymbolAt inp p ≠ none := by
      rintro n hn _ p _ _ ⟨rfl, hp, -, -⟩
      have hnB : n < B.length := by simpa [toks] using hn
      have hlt : L n < x.length := by
        have h1 := List.length_flatten_take_succ toks hn
        have h2 := hposL (n + 1)
        have h3 : 0 < toks[n].length := by simp [toks, length_frame]
        simp only [x, L, List.length_append] at h2 ⊢; omega
      simp only [inputSymbolAt, hp]
      split_ifs
      · omega
      · rw [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlt]; simp
    have hLend : L toks.length = x.length := by
      simp only [L, x, List.take_length, List.length_append]
    have hB := (transformsTapesAt_whileInput hround hmore
      (R := fun inp p ws em ↦ Pinv toks.length inp p ws em)
      fun _ p _ _ h ↦ ⟨by obtain ⟨rfl, hp, -, -⟩ := h; simp [inputSymbolAt, hp, hLend], h⟩).imp
      (P' := fun inp p ws ↦ inp = x ∧ p.val = 1 + (frame D).length ∧
        ws = Function.update (fun _ ↦ []) vip D)
      (Q' := fun inp _ _ _ ws' em ↦ inp = x ∧ ws' = Function.update (fun _ ↦ []) vip D ∧
        em = encList encOut (B.map fun b ↦ qry (b, D)))
      (t' := ∑ j ∈ Finset.range B.length, (rTime D (B[j]?.getD []) + 1) + 1)
      (fun _ _ _ ⟨hx, hp, hws⟩ ↦ ⟨hx, by simpa [L] using hp, hws, rfl⟩)
      (fun _ _ _ _ _ _ _ ⟨hx, _, hws, hem⟩ ↦ ⟨hx, hws, hem.trans hfl_out.symm⟩)
      (by simp [toks]) le_rfl
    -- Phase C: clear `D` and rewind input
    have hclr := (transformsTapes_clearWork_only vip D).freezeInput
    have hrew := transformsTapesAt_rewindInput (k := k + 4) x
    have hC' : TransformsTapesAt
        (((clearWork Bool).extendTapes (tapeEmb vip)).freezeInput.seq (rewindInputOn (k + 4) Bool))
        (fun inp _ ws ↦ inp = x ∧ ws = Function.update (fun _ ↦ []) vip D)
        (fun _ _ _ p' ws' em ↦ p' = 1 ∧ ws' = (fun _ ↦ []) ∧ em = [])
        (3 * (D.length + 1) + (x.length + 2)) ((D.length + 1 + (k + 4)) + (k + 4)) := by
      have hclr' : TransformsTapesAt ((clearWork Bool).extendTapes (tapeEmb vip)).freezeInput
          (fun inp _ ws ↦ inp = x ∧ ws = Function.update (fun _ ↦ []) vip D)
          (fun inp _ _ _ ws' em ↦ inp = x ∧ ws' = (fun _ ↦ []) ∧ em = [])
          (3 * (D.length + 1)) (D.length + 1 + (k + 4)) :=
        hclr.imp (fun _ _ _ h ↦ h.2) (fun _ _ _ _ _ _ h1 ⟨_, h2, h3⟩ ↦ ⟨h1.1, h2, h3⟩)
          le_rfl le_rfl
      exact (transformsTapesAt_seq hclr' hrew fun _ _ _ _ _ _ _ h ↦ h.1).imp
        (fun _ _ _ h ↦ h)
        (fun _ _ _ _ _ _ _ h ↦ by
          obtain ⟨_, _, _, _, ⟨_, hws1, he1⟩, ⟨hp2, hws2, he2⟩, hem⟩ := h
          exact ⟨hp2, hws2.trans hws1, by simp [hem, he1, he2]⟩) le_rfl le_rfl
    have hBC := (transformsTapesAt_seq hB hC'
      fun _ _ _ _ _ _ _ h ↦ And.intro h.1 h.2.1).imp
      (P' := fun inp p ws ↦ inp = x ∧ p.val = 1 + (frame D).length ∧
        ws = Function.update (fun _ ↦ []) vip D)
      (Q' := fun _ _ _ p' ws' em ↦ p' = 1 ∧ ws' = (fun _ ↦ []) ∧
        em = encList encOut (B.map fun b ↦ qry (b, D)))
      (fun _ _ _ h ↦ h)
      (fun _ _ _ _ _ _ _ ⟨_, _, _, _, ⟨_, _, he1⟩, ⟨hp, hws, he2⟩, hem⟩ ↦
        ⟨hp, hws, by simp [hem, he1, he2]⟩) le_rfl le_rfl
    have hABC := (transformsTapesAt_seq hA hBC
      fun _ _ _ _ _ _ _ h ↦ And.intro h.1 (And.intro h.2.1 h.2.2.1)).transformsTapes
      fun _ _ _ _ _ _ ⟨_, _, _, _, _, ⟨hp, _, _⟩, _⟩ ↦ hp
    refine computesTidily_iff_runFrom.mpr ?_
    obtain ⟨ws', em, hrun, hpost, hsp⟩ :=
      transformsTapes_iff_runFrom.mp hABC x (fun _ ↦ []) [] ⟨rfl, rfl, rfl⟩
    obtain ⟨_, _, _, _, ⟨_, _, _, he1⟩, ⟨_, hws2, he2⟩, hem⟩ := hpost
    rw [hws2, hem, he1, he2, List.nil_append, List.nil_append] at hrun
    refine ⟨?_, ?_⟩
    · dsimp only [batchQueryTM, totalT]; simp only [hx_eq]; exact hrun
    · dsimp only [batchQueryTM, totalS]; exact hsp
  -- Clean big-O bound on `totalT (D, B)`:
  let C_out : ℕ := 9 * CN + 48
  refine ⟨C_out, totalT, totalS, ⟨k + 4, _, inferInstance, batchQueryTM M, htm_batch⟩,
    fun D B ↦ ?_⟩
  have hsum_le : ∑ j ∈ Finset.range B.length, (rTime D (B[j]?.getD []) + 1) ≤
      (9 * CN + 44) *
        ∑ j ∈ Finset.range B.length, (tq (B[j]?.getD [], D) + (B[j]?.getD []).length + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    set b := B[j]?.getD []
    have ho := hout_le (b, D)
    have htM_le : tM (b, D) ≤ (9 * CN + 18) * (tq (b, D) + 1) := by
      dsimp only [tM]; nlinarith
    dsimp only [rTime]; rw [length_frame]
    nlinarith
  have hx_len : (encPair encBits (encList encBits) (D, B)).length =
      2 * D.length + 1 + (encList encBits B).length := by
    rw [length_encPair, encBits_apply]
  dsimp only [totalT]; rw [length_frame, hx_len]
  set S := ∑ j ∈ Finset.range B.length, (tq (B[j]?.getD [], D) + (B[j]?.getD []).length + 1)
  dsimp only [C_out]
  nlinarith

end CslibFrontier.Computability.Machines.Turing.MultiTape
