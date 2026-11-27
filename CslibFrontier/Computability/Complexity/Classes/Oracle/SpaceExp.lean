/-
Copyright (c) 2026 The FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalPapers contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation

import CslibFrontier.Computability.Complexity.Classes.Oracle.Space
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.Oracle.Normalization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial Space and Exponential Time Relative to Oracle Languages

Oracle-relativized complexity classes `PSPACEWithOracle`, `PSPACEWithClass`, `EXPWithOracle`, and
`EXPWithClass`, establishing `PSPACE^PSPACE = PSPACE`, `PSPACE^P = PSPACE`, and `EXP^P = EXP`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib Cslib.Complexity Cslib.Probability
open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
open _root_.Turing.MultiTapePTM

/-- Total tape and channel storage of a finite one-channel oracle configuration. -/
def oracleConfigSpace {k : ℕ} {Control : Type}
    (cfg : FiniteConfig k Bool Control Unit) : ℕ :=
  (∑ tape : Fin k, (cfg.tapes.workTapes tape).spaceUsed) +
    (cfg.channels ()).1.length + (cfg.channels ()).2.spaceUsed

/-- The problems decidable in polynomial space relative to the oracle language `A`. -/
def PSPACEWithOracle {α : Type} (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : MultiTapePTM k Bool Control Unit) (t s : α → ℕ) (f : α → Bool),
    PolyBounded (fun a => (enc a).length) s ∧
    (∀ a, a ∈ L ↔ f a = true) ∧
    (∀ a, ∀ i ≤ t a,
      oracleConfigSpace
        ((machine.answerStep (languageOracle A))^[i]
          (FiniteConfig.init machine.initial (enc a))) ≤ s a) ∧
    ∀ a,
      let final := (machine.answerStep (languageOracle A))^[t a]
        (FiniteConfig.init machine.initial (enc a))
      final.tapes.state = none ∧ final.tapes.output = encBool (f a)}

/-- `PSPACE` relative to a class `𝒞` of oracle languages. -/
def PSPACEWithClass {α : Type} (𝒞 : Set (Set (List Bool))) (enc : α ↪ List Bool) :
    Set (Set α) :=
  ⋃ A ∈ 𝒞, PSPACEWithOracle A enc

/-- Strict stateful oracle realization under an exponential clock `c * 2 ^ (n ^ d)`. -/
def IsOracleEXPOn {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : MultiTapePTM k Bool Control Operation) (c d : ℕ),
    ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (output <$> program a) s =
      ProbOracleComp.runWith oracle
        (machine.runOracle (c * 2 ^ ((input a).length ^ d)) (input a)) s

/-- Computability in exponential time `2 ^ (n ^ O(1))` relative to `A`. -/
def ComputableInEXPWithOracle {α β : Type} (A : Set (List Bool)) (f : α → β)
    (input : α ↪ List Bool) (output : β ↪ List Bool) : Prop :=
  ∃ program : α → WordQueryComp Unit β,
    IsOracleEXPOn input output
        (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
      ∀ a, OracleComp.interpret (m := Id) (languageOracle A) (program a) = f a

/-- The problems decidable in exponential time `2 ^ (n ^ O(1))` relative to `A`. -/
def EXPWithOracle {α : Type} (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f : α → Bool, ComputableInEXPWithOracle A f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true}

/-- `EXP` relative to a class `𝒞` of oracle languages. -/
def EXPWithClass {α : Type} (𝒞 : Set (Set (List Bool))) (enc : α ↪ List Bool) :
    Set (Set α) :=
  ⋃ A ∈ 𝒞, EXPWithOracle A enc

private noncomputable def detFiniteStep {k : ℕ} {State : Type}
    (tm : MultiTapeTM k Bool State) (c : FiniteCfg k Bool State) : FiniteCfg k Bool State :=
  match c.state with
  | none => c
  | some q => c.step (tm.tr q c.inputSymbol c.workTapeSymbols)

private structure DetRep {k : ℕ} {State : Type} (x : List Bool)
    (c : FiniteCfg k Bool State) (cfg : Cfg k Bool State x) : Prop where
  input : c.input = x
  state : c.state = cfg.state
  inputPos : c.inputPos.val = cfg.inputPos.val
  workTapes : ∀ tape, (c.workTapes tape).Represents (cfg.workTapes tape) (cfg.workTapePos tape)
  output : c.output = cfg.output

private lemma detRep_init {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (x : List Bool) :
    DetRep x (FiniteCfg.init tm.q₀ x) (tm.initCfg x) :=
  ⟨rfl, rfl, rfl, fun _ => Cslib.Turing.BiTape.represents_nil _, rfl⟩

private lemma detRep_step {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    {x : List Bool} {c : FiniteCfg k Bool State} {cfg : Cfg k Bool State x}
    (h : DetRep x c cfg) :
    DetRep x (detFiniteStep tm c) (tm.step cfg) := by
  obtain ⟨hinp, hst, hpos, hwork, hout⟩ := h
  subst hinp
  have hrep : c.Represents cfg := ⟨hst, Fin.ext hpos, hwork, hout⟩
  rcases hs : cfg.state with _ | q
  · have hcs : c.state = none := hst.trans hs
    rw [MultiTapeTM.step_of_halt hs]
    simpa only [detFiniteStep, hcs] using ⟨rfl, hst, hpos, hwork, hout⟩
  · have hcs : c.state = some q := hst.trans hs
    rw [MultiTapeTM.step_of_state hs]
    have hstep := hrep.step (tm.tr q cfg.inputSymbol cfg.workTapeSymbols)
    simp only [detFiniteStep, hcs, hrep.inputSymbol, hrep.workTapeSymbols]
    exact ⟨rfl, hstep.state, congrArg Fin.val hstep.inputPos, hstep.workTapes, hstep.output⟩

private lemma detRep_iterate {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (x : List Bool) (i : ℕ) :
    DetRep x ((detFiniteStep tm)^[i] (FiniteCfg.init tm.q₀ x))
      (tm.runFrom (tm.initCfg x) i) := by
  induction i with
  | zero => exact detRep_init tm x
  | succ i ih =>
    rw [Function.iterate_succ_apply', MultiTapeTM.runFrom_succ]
    exact detRep_step tm ih

private lemma answerStep_ofDeterministic_iterate {k : ℕ} {State : Type}
    (tm : MultiTapeTM k Bool State) (ans : Unit × List Bool → List Bool)
    (x : List Bool) (i : ℕ) :
    (((ofDeterministic tm : MultiTapePTM k Bool State Unit).answerStep ans)^[i]
      (FiniteConfig.init tm.q₀ x)) =
      ⟨(detFiniteStep tm)^[i] (FiniteCfg.init tm.q₀ x), fun _ => ([],
        Cslib.Turing.BiTape.nil)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rcases (detFiniteStep tm)^[i] (FiniteCfg.init tm.q₀ x) with ⟨inp, _ | q, pos, work, out⟩
    · rfl
    · simp only [MultiTapePTM.answerStep, detFiniteStep, ofDeterministic, FiniteConfig.step,
        Option.toList_none, List.append_nil]
      rfl

/-- Every problem in `PSPACE` lies in `PSPACE` relative to every oracle language `A`. -/
theorem PSPACE_subset_PSPACEWithOracle {α : Type} (A : Set (List Bool)) (enc : α ↪ List Bool) :
    PSPACE enc ⊆ PSPACEWithOracle A enc := by
  intro L hL
  obtain ⟨t, s, hs, hdec⟩ := mem_PSPACE_iff.mp hL
  obtain ⟨f, ⟨k, State, hfin, tm, htm⟩, hfL⟩ := decidableInTimeAndSpace_iff.mp hdec
  refine ⟨k, State, hfin, ofDeterministic tm, t, fun a => k * (4 * s a + 1) + 1, f, ?_, hfL,
    ?_, ?_⟩
  · exact ((PolyBounded.const k).mul (((PolyBounded.const 4).mul hs).add (.const 1))).add
      (.const 1)
  · intro a i _
    rw [show (ofDeterministic tm : MultiTapePTM k Bool State Unit).initial = tm.q₀ from rfl,
      answerStep_ofDeterministic_iterate]
    have hrep := detRep_iterate tm (enc a) i
    let p := MultiTapeNTM.ComputationPath.ofDeterministic tm (enc a) i
    have hspace : MultiTapeNTM.RunPath.space p.toRunPath ≤ s a :=
      space_le_of_runsInSpace (htm a).2.2 i
    have hlast : p.toRunPath.last = tm.runFrom (tm.initCfg (enc a)) i :=
      MultiTapeTM.runPath_last_eq_runFrom _
    have htape (tape : Fin k) :
        ((((detFiniteStep tm)^[i] (FiniteCfg.init tm.q₀ (enc a))).workTapes tape)).spaceUsed ≤
          4 * s a + 1 := by
      have hle : MultiTapeNTM.RunPath.spaceUsedByTape p.toRunPath tape ≤ s a :=
        (Finset.single_le_sum (f := fun j => MultiTapeNTM.RunPath.spaceUsedByTape p.toRunPath j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ tape)).trans hspace
      obtain ⟨hhead, hcells⟩ := MultiTapeNTM.RunPath.natAbs_lt_spaceUsedByTape p.toRunPath
        (fun j z => by rw [p.head_eq]; rfl) (fun j => by rw [p.head_eq]; rfl) tape
      rw [hlast] at hhead hcells
      exact (hrep.workTapes tape).spaceUsed_le (hhead.trans_le hle)
        fun z hz => (hcells z hz).trans_le hle
    have hsum :
        (∑ tape : Fin k,
          (((detFiniteStep tm)^[i] (FiniteCfg.init tm.q₀ (enc a))).workTapes tape).spaceUsed) ≤
          k * (4 * s a + 1) := by
      calc
        _ ≤ ∑ _tape : Fin k, (4 * s a + 1) := Finset.sum_le_sum fun tape _ => htape tape
        _ = k * (4 * s a + 1) := by simp
    have hnil : (Cslib.Turing.BiTape.nil : Cslib.Turing.BiTape Bool).spaceUsed = 1 := by
      simp [Cslib.Turing.BiTape.spaceUsed, Cslib.Turing.BiTape.nil,
        Cslib.Turing.StackTape.length_nil]
    simpa only [oracleConfigSpace, List.length_nil, hnil, Nat.add_zero] using
      Nat.add_le_add_right hsum 1
  · intro a
    dsimp only
    rw [show (ofDeterministic tm : MultiTapePTM k Bool State Unit).initial = tm.q₀ from rfl,
      answerStep_ofDeterministic_iterate]
    have hrep := detRep_iterate tm (enc a) (t a)
    obtain ⟨hhalt, hout⟩ := (htm a).runFrom_of_le le_rfl
    exact ⟨hrep.state.trans hhalt, hrep.output.trans hout⟩

private lemma answerStep_input {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (ans : Unit × List Bool → List Bool)
    (cfg : FiniteConfig k Bool Control Unit) :
    (machine.answerStep ans cfg).tapes.input = cfg.tapes.input := by
  rcases cfg with ⟨⟨inp, _ | ctrl, pos, work, out⟩, ch⟩
  · rfl
  · unfold MultiTapePTM.answerStep
    dsimp only
    cases machine.tr ctrl _ _ _ false <;> rfl

private lemma iterate_answerStep_input {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (ans : Unit × List Bool → List Bool)
    (x : List Bool) (i : ℕ) :
    (((machine.answerStep ans)^[i] (FiniteConfig.init machine.initial x)).tapes.input) = x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', answerStep_input, ih]

private lemma answerStep_output_length_le {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (ans : Unit × List Bool → List Bool)
    (cfg : FiniteConfig k Bool Control Unit) :
    cfg.tapes.output.length ≤ (machine.answerStep ans cfg).tapes.output.length := by
  rcases cfg with ⟨⟨inp, _ | ctrl, pos, work, out⟩, ch⟩
  · exact le_rfl
  · unfold MultiTapePTM.answerStep
    dsimp only
    cases machine.tr ctrl _ _ _ false with
    | step action symbol move =>
      simp only [FiniteConfig.step, FiniteCfg.step, List.length_append]
      exact Nat.le_add_right _ _
    | query op next =>
      exact le_rfl

private lemma iterate_answerStep_output_length_mono {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (ans : Unit × List Bool → List Bool)
    (cfg : FiniteConfig k Bool Control Unit) {i j : ℕ} (hij : i ≤ j) :
    (((machine.answerStep ans)^[i] cfg).tapes.output.length) ≤
      (((machine.answerStep ans)^[j] cfg).tapes.output.length) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
    exact ih.trans (answerStep_output_length_le machine ans _)

private lemma answerStep_of_state_none {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (ans : Unit × List Bool → List Bool)
    {cfg : FiniteConfig k Bool Control Unit} (h : cfg.tapes.state = none) :
    machine.answerStep ans cfg = cfg := by
  unfold MultiTapePTM.answerStep
  rw [h]

private lemma spaceBound_of_oracleConfigSpace {k : ℕ} {Control : Type}
    {cfg : FiniteConfig k Bool Control Unit} {n s : ℕ}
    (hin : cfg.tapes.input.length ≤ n) (hout : cfg.tapes.output.length ≤ 1)
    (hsp : oracleConfigSpace cfg ≤ s) :
    FiniteConfig.SpaceBound n (s + 1) 0 cfg := by
  refine ⟨hin, ?_, by omega, ?_, ?_⟩
  · intro tape
    have hle : (cfg.tapes.workTapes tape).spaceUsed ≤
        ∑ j : Fin k, (cfg.tapes.workTapes j).spaceUsed :=
      Finset.single_le_sum (f := fun j => (cfg.tapes.workTapes j).spaceUsed)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ tape)
    unfold oracleConfigSpace at hsp
    omega
  · intro channel
    rw [show channel = () from Subsingleton.elim _ _]
    unfold oracleConfigSpace at hsp
    omega
  · intro channel
    rw [show channel = () from Subsingleton.elim _ _]
    unfold oracleConfigSpace at hsp
    omega

private lemma dropWhile_replicate_false_append (k : ℕ) (rest : List Bool) :
    (List.replicate k false ++ true :: rest).dropWhile (!·) = true :: rest := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append,
      List.dropWhile_cons_of_pos (show (!false) = true from rfl), ih]

private lemma card_words_le_two_pow {m B : ℕ} (f : Fin m → List Bool)
    (hf : Function.Injective f) (hlen : ∀ i, (f i).length ≤ B) :
    m ≤ 2 ^ (B + 1) := by
  let pad (w : List Bool) : List Bool := w ++ true :: List.replicate (B - w.length) false
  have hpad_len (i : Fin m) : (pad (f i)).length = B + 1 := by
    have := hlen i
    simp only [pad, List.length_append, List.length_cons, List.length_replicate]
    omega
  have hpad_unpad (w : List Bool) : ((pad w).reverse.dropWhile (!·)).tail.reverse = w := by
    have hrev : (pad w).reverse = List.replicate (B - w.length) false ++ true :: w.reverse := by
      simp [pad, List.reverse_append]
    rw [hrev, dropWhile_replicate_false_append, List.tail_cons, List.reverse_reverse]
  let φ : Fin m → (Fin (B + 1) → Bool) := fun i j => (pad (f i)).getD j.val false
  have hφ_inj : Function.Injective φ := by
    intro i₁ i₂ hφ
    have hpad_eq : pad (f i₁) = pad (f i₂) := by
      refine List.ext_getElem ((hpad_len i₁).trans (hpad_len i₂).symm) fun j hj₁ hj₂ => ?_
      have hj : j < B + 1 := hj₁.trans_eq (hpad_len i₁)
      have := congrFun hφ ⟨j, hj⟩
      simpa only [φ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₁,
        List.getElem?_eq_getElem hj₂, Option.getD_some] using this
    exact hf (by rw [← hpad_unpad (f i₁), hpad_eq, hpad_unpad (f i₂)])
  simpa using Fintype.card_le_of_injective φ hφ_inj

/-- **`PSPACE` relative to an oracle in `PSPACE` lies within `PSPACE`.** -/
theorem PSPACEWithOracle_subset_PSPACE {α : Type} {A : Set (List Bool)}
    (hA : A ∈ PSPACE encBits) (enc : α ↪ List Bool) :
    PSPACEWithOracle A enc ⊆ PSPACE enc := by
  intro L ⟨k, Control, hfin, machine, t, s, f, hs, hfL, hspace, hfinal⟩
  obtain ⟨TA, SA, hSA, g, hg, hgA⟩ := exists_computableInO_of_mem_PSPACE hA
  have hans_eq : (languageOracle A : Unit × List Bool → List Bool) = fun q => [g q.2] := by
    classical
    exact funext fun q => congrArg (· :: []) (Bool.eq_iff_iff.mpr
      ⟨fun h => (hgA q.2).mp (of_decide_eq_true h), fun h => decide_eq_true ((hgA q.2).mpr h)⟩)
  let step := machine.answerStep fun q : Unit × List Bool => [g q.2]
  let init (a : α) : FiniteConfig k Bool Control Unit :=
    FiniteConfig.init machine.initial (enc a)
  let _ : Inhabited (FiniteConfig k Bool Control Unit) := ⟨FiniteConfig.init machine.initial []⟩
  obtain ⟨e, hstep⟩ := machine.answerStep_inO hg
  obtain ⟨cs, ds, hcs⟩ := hs.exists_le
  obtain ⟨cg, dg, hSg⟩ := (by simpa [encBits] using hSA : PolyBounded List.length SA).exists_le
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  let Spoly (a : α) : ℕ := cs * ((enc a).length + 1) ^ ds
  let Bpoly (a : α) : ℕ := cf * ((enc a).length + (Spoly a + 1) + 0 + 1)
  have hbound_le (a : α) {i : ℕ} (hi : i ≤ t a) :
      (encFiniteConfig (step^[i] (init a))).length ≤ Bpoly a ∧
        (machine.pendingRequest (step^[i] (init a))).length ≤ Spoly a := by
    have hout_ta : (step^[t a] (init a)).tapes.output.length = 1 := by
      dsimp only [step, init]
      rw [← hans_eq, (hfinal a).2, encBool_apply, List.length_singleton]
    have hout_i : (step^[i] (init a)).tapes.output.length ≤ 1 :=
      (iterate_answerStep_output_length_mono machine _ (init a) hi).trans (le_of_eq hout_ta)
    have hin_i : (step^[i] (init a)).tapes.input.length ≤ (enc a).length := by
      rw [iterate_answerStep_input]
    have hsp_raw : oracleConfigSpace (step^[i] (init a)) ≤ s a := by
      simpa only [step, init, hans_eq] using hspace a i hi
    have hsp_i : oracleConfigSpace (step^[i] (init a)) ≤ Spoly a :=
      hsp_raw.trans (hcs a)
    have hsb := spaceBound_of_oracleConfigSpace hin_i hout_i hsp_i
    refine ⟨(hcf _ _ _ _ hsb).trans le_rfl, ?_⟩
    unfold MultiTapePTM.pendingRequest
    rcases machine.pendingQuery (step^[i] (init a)) with _ | ⟨op, _⟩
    · exact Nat.zero_le _
    · dsimp only
      rw [show op = () from Subsingleton.elim _ _]
      unfold oracleConfigSpace at hsp_i
      omega
  have hstabilize (a : α) :
      (∀ i ≤ 2 ^ (Bpoly a + 1),
        (encFiniteConfig (step^[i] (init a))).length ≤ Bpoly a ∧
          (machine.pendingRequest (step^[i] (init a))).length ≤ Spoly a) ∧
        (step^[2 ^ (Bpoly a + 1)] (init a)).tapes.output = encBool (f a) := by
    have _ := Classical.decPred fun m => (step^[m] (init a)).tapes.state = none
    have hex : ∃ m, (step^[m] (init a)).tapes.state = none :=
      ⟨t a, by simpa only [step, init, hans_eq] using (hfinal a).1⟩
    let t₀ := Nat.find hex
    have ht₀_state : (step^[t₀] (init a)).tapes.state = none := Nat.find_spec hex
    have ht₀_le_ta : t₀ ≤ t a := Nat.find_min' hex
      (by simpa only [step, init, hans_eq] using (hfinal a).1)
    have hfix_ge {m : ℕ} (hm : t₀ ≤ m) : step^[m] (init a) = step^[t₀] (init a) := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hm
      rw [Function.iterate_add_apply]
      exact Function.iterate_fixed (answerStep_of_state_none machine _ ht₀_state) r
    have hinj_cfg : Function.Injective
        (fun j : Fin (t₀ + 1) => encFiniteConfig (step^[j.val] (init a))) := by
      have hlt_false {j₁ j₂ : Fin (t₀ + 1)} (hlt : j₁.val < j₂.val)
          (hcfg_eq : step^[j₁.val] (init a) = step^[j₂.val] (init a)) : False := by
        have hj₂_le : j₂.val ≤ t₀ := Nat.lt_succ_iff.mp j₂.isLt
        have hshort : (step^[t₀ - j₂.val + j₁.val] (init a)).tapes.state = none := by
          rw [Function.iterate_add_apply, hcfg_eq, ← Function.iterate_add_apply,
            Nat.sub_add_cancel hj₂_le]
          exact ht₀_state
        exact Nat.find_min hex (by omega : t₀ - j₂.val + j₁.val < t₀) hshort
      intro j₁ j₂ heq
      have hcfg_eq := encFiniteConfig.injective heq
      rcases lt_trichotomy j₁.val j₂.val with hlt | hval | hlt
      · exact False.elim (hlt_false hlt hcfg_eq)
      · exact Fin.ext hval
      · exact False.elim (hlt_false hlt hcfg_eq.symm)
    have ht₀_card : t₀ + 1 ≤ 2 ^ (Bpoly a + 1) :=
      card_words_le_two_pow _ hinj_cfg fun j =>
        (hbound_le a ((Nat.lt_succ_iff.mp j.isLt).trans ht₀_le_ta)).1
    have ht₀_le_clock : t₀ ≤ 2 ^ (Bpoly a + 1) := by omega
    refine ⟨fun i _ => ?_, ?_⟩
    · rcases le_or_gt i t₀ with hi | hi
      · exact hbound_le a (hi.trans ht₀_le_ta)
      · rw [hfix_ge hi.le]
        exact hbound_le a ht₀_le_ta
    · rw [hfix_ge ht₀_le_clock, ← hfix_ge ht₀_le_ta]
      simpa only [step, init, hans_eq] using (hfinal a).2
  let pExp : Polynomial ℕ :=
    Polynomial.C cf * (Polynomial.X + (Polynomial.C cs * (Polynomial.X + 1) ^ ds + 1) + 1) + 1
  have hpExp_eval (a : α) : pExp.eval (enc a).length = Bpoly a + 1 := by
    simp [pExp, Bpoly, Spoly]
  let n (a : α) : ℕ := 2 ^ (Bpoly a + 1)
  have hn_pt : ComputableInPolyTime n enc encNat :=
    (ComputableInPolyTime.binary_two_pow.comp
      ((ComputableInPolyTime.unary_eval pExp).comp
        (ComputableInPolyTime.encoding_length enc))).of_enc_eq fun a => by
      simp [n, hpExp_eval]
  obtain ⟨dn, _, hn_deg⟩ := hn_pt.exists_degree
  have henc_pt : ComputableInPolyTime (fun a : α => enc a) enc encBits := .of_eq fun _ => rfl
  have hinit_pt : ComputableInPolyTime init enc encFiniteConfig :=
    ComputableInPolyTime.finiteConfig_init henc_pt machine.initial
  obtain ⟨di, _, hinit_deg⟩ := hinit_pt.exists_degree
  have hout_pt : ComputableInPolyTime
      (fun cfg : FiniteConfig k Bool Control Unit => cfg.tapes.output)
      encFiniteConfig encBits :=
    ComputableInPolyTime.finiteCfg_output.comp ComputableInPolyTime.finiteConfig_tapes
  obtain ⟨do', _, hout_deg⟩ := hout_pt.exists_degree
  have hit := ComputableInO.iterate hn_deg.inO hinit_deg.inO hstep
    (R := fun a => (Bpoly a + 1) ^ e + wordMax TA (Spoly a))
    (Q := fun a => (Bpoly a + 1) ^ e + cg * (Spoly a + 1) ^ dg) (B := Bpoly)
    (fun a i hi => Nat.add_le_add
      (Nat.pow_le_pow_left (Nat.add_le_add_right ((hstabilize a).1 i hi).1 1) e)
      (le_wordMax TA ((hstabilize a).1 i hi).2))
    (fun a i hi => Nat.add_le_add
      (Nat.pow_le_pow_left (Nat.add_le_add_right ((hstabilize a).1 i hi).1 1) e)
      ((hSg _).trans (Nat.mul_le_mul_left cg
        (Nat.pow_le_pow_left (Nat.add_le_add_right ((hstabilize a).1 i hi).2 1) dg))))
    (fun a i hi => ((hstabilize a).1 i hi).1)
  have hlen_encNat_n (a : α) : (encNat (n a)).length ≤ Bpoly a + 2 := by
    simp only [n, encNat_apply, Nat.size_eq_bits_len]
    refine Nat.size_le.mpr ?_
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  have hcomp := (hout_deg.inO.comp hit).mono_le
    (T' := fun a => _ + (Bpoly a + 1) ^ do')
    (S' := fun a => ((enc a).length + 1) ^ dn + ((enc a).length + 1) ^ di +
      ((Bpoly a + 1) ^ e + cg * (Spoly a + 1) ^ dg) + Bpoly a + (Bpoly a + 2) +
      (Bpoly a + 1) ^ do')
    (fun a => Nat.add_le_add_left
      (Nat.pow_le_pow_left (Nat.add_le_add_right ((hstabilize a).1 _ le_rfl).1 1) do') _)
    (fun a => by
      have h₁ := ((hstabilize a).1 _ le_rfl).1
      have h₂ := hlen_encNat_n a
      have h₃ := Nat.pow_le_pow_left (Nat.add_le_add_right h₁ 1) do'
      dsimp only [step, n] at *
      omega)
  have hf_inO : ComputableInO f enc encBool _ _ :=
    hcomp.of_enc_eq fun a => (hstabilize a).2.symm
  have hS_poly : PolyBounded (fun a => (enc a).length)
      (fun a => ((enc a).length + 1) ^ dn + ((enc a).length + 1) ^ di +
        ((Bpoly a + 1) ^ e + cg * (Spoly a + 1) ^ dg) + Bpoly a + (Bpoly a + 2) +
        (Bpoly a + 1) ^ do') := by
    dsimp only [Bpoly, Spoly]
    growth_poly
  exact mem_PSPACE_of_computableInO hf_inO hS_poly hfL

/-- **`PSPACE` relative to an oracle in `PSPACE` equals `PSPACE`.** -/
theorem PSPACEWithOracle_eq_PSPACE {α : Type} {A : Set (List Bool)}
    (hA : A ∈ PSPACE encBits) (enc : α ↪ List Bool) :
    PSPACEWithOracle A enc = PSPACE enc :=
  Set.Subset.antisymm (PSPACEWithOracle_subset_PSPACE hA enc)
    (PSPACE_subset_PSPACEWithOracle A enc)

/-- **`PSPACE^PSPACE = PSPACE`.** -/
theorem PSPACEWithClass_PSPACE_eq {α : Type} (enc : α ↪ List Bool) :
    PSPACEWithClass (PSPACE encBits) enc = PSPACE enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA => PSPACEWithOracle_subset_PSPACE hA enc
  · intro L hL
    exact Set.mem_biUnion (P_subset_PSPACE empty_mem_P)
      (PSPACE_subset_PSPACEWithOracle ∅ enc hL)

/-- **`PSPACE^P = PSPACE`.** -/
theorem PSPACEWithClass_P_eq {α : Type} (enc : α ↪ List Bool) :
    PSPACEWithClass (P encBits) enc = PSPACE enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA =>
      PSPACEWithOracle_subset_PSPACE (P_subset_PSPACE hA) enc
  · intro L hL
    exact Set.mem_biUnion empty_mem_P (PSPACE_subset_PSPACEWithOracle ∅ enc hL)

/-- Every problem in `EXP` lies in `EXP` relative to every oracle language `A`. -/
theorem EXP_subset_EXPWithOracle {α : Type} (A : Set (List Bool)) (enc : α ↪ List Bool) :
    EXP enc ⊆ EXPWithOracle A enc := by
  intro L hL
  obtain ⟨k, c₁, c₂, s, hdec⟩ := mem_EXP_iff.mp hL
  obtain ⟨f, ⟨kt, State, hfin, tm, htm⟩, hfL⟩ := decidableInTimeAndSpace_iff.mp hdec
  refine ⟨f, ⟨fun a => pure (f a), ⟨inferInstance, kt, State, hfin, ofDeterministic tm,
    c₁ + c₂ + 1, k, fun a OracleState oracle state => ?_⟩, fun _ => rfl⟩, hfL⟩
  dsimp only
  rw [OracleComp.interpret_pure, map_pure, ProbOracleComp.runWith_pure,
    MultiTapePTM.run_interpret_runOracle_ofDeterministic]
  have hpow_pos : 1 ≤ 2 ^ ((enc a).length ^ k) := Nat.one_le_two_pow
  have hle : c₁ * 2 ^ ((enc a).length ^ k) + c₂ ≤
      (c₁ + c₂ + 1) * 2 ^ ((enc a).length ^ k) := by nlinarith
  exact congrArg (fun w => PMF.pure (w, state)) ((htm a).runFrom_of_le hle).2.symm

/-- `P` relative to `A` lies inside `EXP` relative to `A`. -/
theorem PWithOracle_subset_EXPWithOracle {α : Type} (A : Set (List Bool))
    (enc : α ↪ List Bool) :
    PWithOracle A enc ⊆ EXPWithOracle A enc := by
  rintro L ⟨f, ⟨program, hcert, hprog⟩, hfL⟩
  obtain ⟨hops, k, Control, hfin, machine, c, d, hmachine⟩ := hcert.oraclePhase
  refine ⟨f, ⟨program, ⟨hops, k, Control, hfin, machine, c * 2 ^ (d ^ 2), 2,
    fun a State oracle s => ?_⟩, hprog⟩, hfL⟩
  have hle : c * ((enc a).length + 1) ^ d ≤ (c * 2 ^ (d ^ 2)) * 2 ^ ((enc a).length ^ 2) := by
    have h₁ : ((enc a).length + 1) ^ d ≤ 2 ^ (d * (enc a).length) := by
      rw [Nat.pow_mul']
      exact Nat.pow_le_pow_left Nat.lt_two_pow_self d
    have h₂ : d * (enc a).length ≤ d ^ 2 + (enc a).length ^ 2 := by nlinarith
    calc
      c * ((enc a).length + 1) ^ d ≤ c * 2 ^ (d * (enc a).length) :=
        Nat.mul_le_mul_left c h₁
      _ ≤ c * 2 ^ (d ^ 2 + (enc a).length ^ 2) :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by norm_num) h₂)
      _ = (c * 2 ^ (d ^ 2)) * 2 ^ ((enc a).length ^ 2) := by rw [Nat.pow_add]; ring
  exact (((hmachine a).mono hle).runOracle oracle s).symm

private theorem runWith_interpret_query_stateless {Operation β : Type}
    (answer : Operation × List Bool → List Bool) (program : WordQueryComp Operation β) :
    ProbOracleComp.runWith (fun q (s : Unit) => PMF.pure (answer q, s))
      (OracleComp.interpret ProbOracleComp.query program) () =
      PMF.pure (OracleComp.interpret (m := Id) answer program, ()) := by
  rw [ProbOracleComp.runWith_eq_run_interpret, OracleComp.interpret_interpret]
  simp only [ProbOracleComp.interpret_query]
  induction program using PFunctor.FreeM.induction with
  | pure b => rfl
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      PMF.monad_bind_eq_bind, OracleComp.interpret_bind, OracleComp.interpret_query]
    exact (PMF.pure_bind _ _).trans (ih _)

/-- **`EXP` relative to an oracle in `P` lies within `EXP`.** -/
theorem EXPWithOracle_subset_EXP {α : Type} {A : Set (List Bool)}
    (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    EXPWithOracle A enc ⊆ EXP enc := by
  rintro L ⟨f, ⟨program, ⟨_, k, Control, hfin, machine, c, d, hcert⟩, hprog⟩, hfL⟩
  obtain ⟨g, hg, hgA⟩ := hA
  let ans : Unit × List Bool → List Bool := fun q => [g q.2]
  have hans_eq : ans = languageOracle A := by
    classical
    exact funext fun q => congrArg (· :: []) (Bool.eq_iff_iff.mpr
      ⟨fun h => decide_eq_true ((hgA q.2).mpr h), fun h => (hgA q.2).mp (of_decide_eq_true h)⟩)
  let fuel (a : α) : ℕ := c * 2 ^ ((enc a).length ^ d)
  let step := machine.answerStep ans
  let init (a : α) : FiniteConfig k Bool Control Unit :=
    FiniteConfig.init machine.initial (enc a)
  let _ : Inhabited (FiniteConfig k Bool Control Unit) := ⟨FiniteConfig.init machine.initial []⟩
  have hdet_out (a : α) : (step^[fuel a] (init a)).tapes.output = encBool (f a) := by
    have hlaw := hcert a Unit (fun q s => PMF.pure (ans q, s)) ()
    rw [ProbOracleComp.runWith_map, runWith_interpret_query_stateless, PMF.pure_map] at hlaw
    have hmem := MultiTapePTM.mem_support_runConfigFrom_pure machine false ans () (fuel a)
      (machine.initialConfig (enc a))
    have hmem_out :
        (OracleComp.interpret (m := Id) ans
          (machine.run (pure false) (fun op word => OracleComp.query (op, word))
            (fuel a) (enc a)), ()) ∈
          (ProbOracleComp.runWith (fun q (s : Unit) => PMF.pure (ans q, s))
            (machine.runOracle (fuel a) (enc a)) ()).support := by
      simp only [MultiTapePTM.runOracle, MultiTapePTM.run, MultiTapePTM.runFrom,
        ProbOracleComp.runWith_map, OracleComp.interpret_map, PMF.mem_support_map_iff]
      exact ⟨_, hmem, rfl⟩
    rw [← hlaw, PMF.mem_support_pure_iff] at hmem_out
    have hrun_eq :
        OracleComp.interpret (m := Id) ans
          (machine.run (pure false) (fun op word => OracleComp.query (op, word))
            (fuel a) (enc a)) =
          encBool (OracleComp.interpret (m := Id) ans (program a)) :=
      congrArg Prod.fst hmem_out
    have hprog' : OracleComp.interpret (m := Id) ans (program a) = f a := by
      rw [hans_eq, hprog a]
    rw [machine.interpret_run_pure_false ans (fuel a) (enc a), hprog'] at hrun_eq
    exact hrun_eq
  have hpow_pt : ComputableInPolyTime (fun a : α => 2 ^ ((enc a).length ^ d)) enc encNat :=
    (ComputableInPolyTime.binary_two_pow.comp
      ((ComputableInPolyTime.unary_eval (Polynomial.X ^ d)).comp
        (ComputableInPolyTime.encoding_length enc))).of_enc_eq fun a => by simp
  have hfuel_pt : ComputableInPolyTime fuel enc encNat :=
    ComputableInPolyTime.binary_mul' (.const c) hpow_pt
  obtain ⟨dn, _, hfuel_deg⟩ := hfuel_pt.exists_degree
  have henc_pt : ComputableInPolyTime (fun a : α => enc a) enc encBits := .of_eq fun _ => rfl
  have hinit_pt : ComputableInPolyTime init enc encFiniteConfig :=
    ComputableInPolyTime.finiteConfig_init henc_pt machine.initial
  obtain ⟨di, _, hinit_deg⟩ := hinit_pt.exists_degree
  have hstep_pt : ComputableInPolyTime step encFiniteConfig encFiniteConfig :=
    machine.computableInPolyTime_answerStep hg
  obtain ⟨ds, _, hstep_deg⟩ := hstep_pt.exists_degree
  have hout_pt : ComputableInPolyTime
      (fun cfg : FiniteConfig k Bool Control Unit => cfg.tapes.output)
      encFiniteConfig encBits :=
    ComputableInPolyTime.finiteCfg_output.comp ComputableInPolyTime.finiteConfig_tapes
  obtain ⟨do', _, hout_deg⟩ := hout_pt.exists_degree
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  let B (a : α) : ℕ := cf * ((enc a).length + fuel a + 1 + 1)
  have hsb_iter (a : α) (i : ℕ) : FiniteConfig.SpaceBound (enc a).length i 1
      (step^[i] (init a)) := by
    induction i with
    | zero => exact FiniteConfig.spaceBound_init _ _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact machine.spaceBound_answerStep _ ih
  have hlen_iter (a : α) {i : ℕ} (hi : i ≤ fuel a) :
      (encFiniteConfig (step^[i] (init a))).length ≤ B a :=
    (hcf _ _ _ _ (hsb_iter a i)).trans (Nat.mul_le_mul_left cf (by omega))
  have hit := ComputableInO.iterate hfuel_deg.inO hinit_deg.inO hstep_deg.inO
    (R := fun a => (B a + 1) ^ ds)
    (Q := fun a => (B a + 1) ^ ds) (B := B)
    (fun a i hi => Nat.pow_le_pow_left (Nat.add_le_add_right (hlen_iter a hi) 1) ds)
    (fun a i hi => Nat.pow_le_pow_left (Nat.add_le_add_right (hlen_iter a hi) 1) ds)
    (fun a _ hi => hlen_iter a hi)
  have hlen_encNat_fuel (a : α) : (encNat (fuel a)).length ≤ fuel a + 1 := by
    simpa only [encNat_apply, Nat.size_eq_bits_len] using
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_succ _)
  let Tlen (n : ℕ) : ℕ :=
    let F := c * 2 ^ (n ^ d)
    let Bn := cf * (n + F + 1 + 1)
    (n + 1) ^ dn + (n + 1) ^ di +
      (F + 1) * ((Bn + 1) ^ ds + Bn + (F + 2) ^ 2) + (Bn + 1) ^ do'
  have hcomp := (hout_deg.inO.comp hit).mono_le
    (T' := fun a => Tlen (enc a).length)
    (S' := fun a => ((enc a).length + 1) ^ dn + ((enc a).length + 1) ^ di +
      (B a + 1) ^ ds + B a + (fuel a + 1) + (B a + 1) ^ do')
    (fun a => by
      have h₁ := Nat.pow_le_pow_left (Nat.add_le_add_right (hlen_iter a le_rfl) 1) do'
      have h₂ := Nat.pow_le_pow_left (Nat.add_le_add_right (hlen_encNat_fuel a) 1) 2
      dsimp only [Tlen, B, fuel] at *
      exact Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left h₂ _)) _) h₁)
    (fun a => by
      have h₁ := Nat.pow_le_pow_left (Nat.add_le_add_right (hlen_iter a le_rfl) 1) do'
      have h₂ := hlen_encNat_fuel a
      dsimp only [B, fuel] at *
      omega)
  have hf_inO : ComputableInO f enc encBool (fun a => Tlen (enc a).length) _ :=
    hcomp.of_enc_eq fun a => (hdet_out a).symm
  let E := dn + di + ds + do' + 4
  let C₀ := (cf + 1) * (c + 3)
  let hExp (n : ℕ) : ℕ := 6 * C₀ ^ E + E * (n ^ d + n + 1)
  have hTlen_le (n : ℕ) : Tlen n ≤ 2 ^ hExp n := by
    set M := 2 ^ (n ^ d + n + 1)
    have hM_pos : 1 ≤ M := Nat.one_le_two_pow
    have hn_le_M : n + 1 ≤ M :=
      Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hF_le_M : c * 2 ^ (n ^ d) ≤ c * M :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by norm_num) (by omega))
    let K := C₀ * M
    have hC₀_pos : 1 ≤ C₀ := Nat.mul_pos (Nat.succ_pos cf) (by omega)
    have hc3_le_C₀ : c + 3 ≤ C₀ := Nat.le_mul_of_pos_left _ (Nat.succ_pos cf)
    have hM_le_K : M ≤ K := Nat.le_mul_of_pos_left M hC₀_pos
    have hBn_le : cf * (n + c * 2 ^ (n ^ d) + 1 + 1) + 2 ≤ K := by
      dsimp only [K, C₀]
      nlinarith
    have hK_pos : 1 ≤ K := hM_pos.trans hM_le_K
    have hpow_E (r : ℕ) (hr : r ≤ E) : K ^ r ≤ K ^ E :=
      Nat.pow_le_pow_right hK_pos hr
    have h1 : (n + 1) ^ dn ≤ K ^ E :=
      (Nat.pow_le_pow_left (hn_le_M.trans hM_le_K) dn).trans
        (hpow_E dn (by dsimp only [E]; omega))
    have h2 : (n + 1) ^ di ≤ K ^ E :=
      (Nat.pow_le_pow_left (hn_le_M.trans hM_le_K) di).trans
        (hpow_E di (by dsimp only [E]; omega))
    have h3 : (cf * (n + c * 2 ^ (n ^ d) + 1 + 1) + 1) ^ do' ≤ K ^ E :=
      (Nat.pow_le_pow_left (by omega) do').trans
        (hpow_E do' (by dsimp only [E]; omega))
    have hF2 : c * 2 ^ (n ^ d) + 2 ≤ K :=
      (by linarith : c * 2 ^ (n ^ d) + 2 ≤ (c + 3) * M).trans (Nat.mul_le_mul_right M hc3_le_C₀)
    have hBn1 : cf * (n + c * 2 ^ (n ^ d) + 1 + 1) + 1 ≤ K := by omega
    have hprod :
        (c * 2 ^ (n ^ d) + 1) *
          ((cf * (n + c * 2 ^ (n ^ d) + 1 + 1) + 1) ^ ds +
            cf * (n + c * 2 ^ (n ^ d) + 1 + 1) + (c * 2 ^ (n ^ d) + 2) ^ 2) ≤
          3 * K ^ E := by
      have ha : (cf * (n + c * 2 ^ (n ^ d) + 1 + 1) + 1) ^ ds ≤ K ^ (ds + 2) :=
        (Nat.pow_le_pow_left hBn1 ds).trans (Nat.pow_le_pow_right hK_pos (by omega))
      have hb : cf * (n + c * 2 ^ (n ^ d) + 1 + 1) ≤ K ^ (ds + 2) :=
        (by omega : _ ≤ K).trans (Nat.le_self_pow (by omega) K)
      have hc2 : (c * 2 ^ (n ^ d) + 2) ^ 2 ≤ K ^ (ds + 2) :=
        (Nat.pow_le_pow_left hF2 2).trans (Nat.pow_le_pow_right hK_pos (by omega))
      calc
        _ ≤ K * (K ^ (ds + 2) + K ^ (ds + 2) + K ^ (ds + 2)) :=
          Nat.mul_le_mul (by omega) (Nat.add_le_add (Nat.add_le_add ha hb) hc2)
        _ = 3 * K ^ (ds + 3) := by ring
        _ ≤ 3 * K ^ E := Nat.mul_le_mul_left 3 (hpow_E (ds + 3) (by dsimp only [E]; omega))
    have htot : Tlen n ≤ 6 * K ^ E := by
      dsimp only [Tlen]
      linarith
    have hKE : 6 * K ^ E ≤ 2 ^ hExp n := by
      have hK_pow : 6 * K ^ E = (6 * C₀ ^ E) * 2 ^ (E * (n ^ d + n + 1)) := by
        dsimp only [K, M]
        rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm (n ^ d + n + 1) E]
        ring
      rw [hK_pow, show 2 ^ hExp n = 2 ^ (6 * C₀ ^ E) * 2 ^ (E * (n ^ d + n + 1)) by
        dsimp only [hExp]; rw [Nat.pow_add]]
      exact Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    exact htot.trans hKE
  have hDTIME : {a | f a = true} ∈ DTIME enc (fun n => 2 ^ hExp n) :=
    setOf_mem_DTIME_of_computableInO hf_inO fun a => hTlen_le (enc a).length
  have hL_eq : L = {a | f a = true} := Set.ext hfL
  rw [hL_eq]
  exact DTIME_two_pow_subset_EXP (by dsimp only [hExp]; fun_prop) hDTIME

/-- **`PSPACE` relative to the empty oracle class is empty.** -/
@[simp]
theorem PSPACEWithClass_empty {α : Type} (enc : α ↪ List Bool) :
    PSPACEWithClass ∅ enc = ∅ := by
  simp [PSPACEWithClass]

/-- **`PSPACE` relative to a singleton oracle class `{A}` equals `PSPACE^A`.** -/
@[simp]
theorem PSPACEWithClass_singleton {α : Type} (A : Set (List Bool)) (enc : α ↪ List Bool) :
    PSPACEWithClass {A} enc = PSPACEWithOracle A enc := by
  simp [PSPACEWithClass]

/-- **`EXP` relative to the empty oracle class is empty.** -/
@[simp]
theorem EXPWithClass_empty {α : Type} (enc : α ↪ List Bool) :
    EXPWithClass ∅ enc = ∅ := by
  simp [EXPWithClass]

/-- **`EXP` relative to a singleton oracle class `{A}` equals `EXP^A`.** -/
@[simp]
theorem EXPWithClass_singleton {α : Type} (A : Set (List Bool)) (enc : α ↪ List Bool) :
    EXPWithClass {A} enc = EXPWithOracle A enc := by
  simp [EXPWithClass]

/-- **`EXP` relative to an oracle in `P` equals `EXP`.** -/
theorem EXPWithOracle_eq_EXP {α : Type} {A : Set (List Bool)}
    (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    EXPWithOracle A enc = EXP enc :=
  Set.Subset.antisymm (EXPWithOracle_subset_EXP hA enc)
    (EXP_subset_EXPWithOracle A enc)

/-- **`EXP^P = EXP`.** -/
theorem EXPWithClass_P_eq {α : Type} (enc : α ↪ List Bool) :
    EXPWithClass (P encBits) enc = EXP enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA => EXPWithOracle_subset_EXP hA enc
  · intro L hL
    exact Set.mem_biUnion empty_mem_P (EXP_subset_EXPWithOracle ∅ enc hL)

end CslibFrontier.Complexity
