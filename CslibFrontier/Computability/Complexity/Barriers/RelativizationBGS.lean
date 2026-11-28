/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google LLC
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Encodable.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Oracle Machines, the Use Principle, and the Relativization Barrier

This module develops a self-contained deterministic step-bounded oracle machine model and proves
both halves of the relativization barrier for deterministic versus nondeterministic polynomial
time.

## Overview

1. **Deterministic oracle machines and enumeration**: `OracleMachine` is a finite-register
   multi-stack imperative machine with six binary stack registers and a dedicated oracle query
   tape that grows by at most one bit per step. It admits a computable Gödel encoding
   `encodeMachine` with left inverse `decodeMachineOpt`, yielding an `Encodable OracleMachine`
   instance and a total enumeration `decodeMachine : ℕ → OracleMachine`.
2. **Small-step semantics, query bounds, and the Use Principle**: `step`, `runSteps`, and
   `evalOracle` define deterministic step-bounded execution relative to an oracle
   `O : DecisionProblem`. Within `t` steps, a machine queries at most `t` strings
   (`queriedSet_card_le`), each of length strictly less than `t` (`queriedSet_length_lt`).
   By the Use Principle (`evalOracle_use_principle`), two oracles agreeing on all strings queried
   during a `t`-step run produce identical outputs and identical query sets (`queriedSet_congr`).
3. **Relativized polynomial-time classes**: Using the injective prefix-free pairing `pair`,
   `OracleP O` and `OracleNP O` formalize deterministic and nondeterministic polynomial-time
   decision problems relative to `O`. For every oracle `O`, `OracleP O` contains constant problems
   (`const_mem_OracleP`), contains `O` itself (`self_mem_OracleP`), is closed under complement
   (`compl_mem_OracleP`), and satisfies `OracleP O ⊆ OracleNP O` (`OracleP_subset_OracleNP`).
4. **Collapsing oracle**: A length-stratified computable self-encoding oracle `collapseOracle`
   decides padded bounded nondeterministic queries `encodeCollapseQuery e x t` using only oracle
   answers on strictly shorter strings. Combining the Use Principle with polynomial-time unary
   Horner evaluation in `OracleMachine` yields `OracleP collapseOracle = OracleNP collapseOracle`.
5. **Separating oracle**: For every oracle `B`, the unary length-membership language `unaryLang B`
   lies in `OracleNP B` (`unaryLang_mem_OracleNP`). A computable stage-by-stage diagonalization
   over all machine-polynomial pairs constructs an oracle `sepOracle` for which
   `unaryLang sepOracle ∉ OracleP sepOracle`, giving `OracleP sepOracle ⊂ OracleNP sepOracle`
   and `relativization_barrier`.

## Main definitions

* `Cslib.Complexity.Barriers.Relativization.OracleMachine`: deterministic multi-stack oracle
  machine syntax.
* `Cslib.Complexity.Barriers.Relativization.evalOracle`: universal step-bounded oracle evaluator.
* `Cslib.Complexity.Barriers.Relativization.queriedSet`: finite set of oracle queries made within
  a step budget.
* `Cslib.Complexity.Barriers.Relativization.OracleP`,
  `Cslib.Complexity.Barriers.Relativization.OracleNP`: relativized polynomial-time and
  nondeterministic polynomial-time complexity classes.
* `Cslib.Complexity.Barriers.Relativization.collapseOracle`: explicit computable self-encoding
  oracle collapsing `OracleP` and `OracleNP`.
* `Cslib.Complexity.Barriers.Relativization.unaryLang`: unary length-membership witness language
  associated with an oracle.
* `Cslib.Complexity.Barriers.Relativization.sepOracle`: explicit computable stage-diagonalized
  oracle separating `OracleP` and `OracleNP`.

## Main results

* `Cslib.Complexity.Barriers.Relativization.queriedSet_card_le`,
  `Cslib.Complexity.Barriers.Relativization.queriedSet_length_lt`: query cardinality and length
  bounds.
* `Cslib.Complexity.Barriers.Relativization.evalOracle_use_principle`,
  `Cslib.Complexity.Barriers.Relativization.queriedSet_congr`: the Use Principle.
* `Cslib.Complexity.Barriers.Relativization.self_mem_OracleP`,
  `Cslib.Complexity.Barriers.Relativization.compl_mem_OracleP`,
  `Cslib.Complexity.Barriers.Relativization.OracleP_subset_OracleNP`: structural properties of
  relativized polynomial time.
* `Cslib.Complexity.Barriers.Relativization.collapseOracle_encodeCollapseQuery`: self-encoding
  fixed-point characterization of `collapseOracle`.
* `Cslib.Complexity.Barriers.Relativization.OracleP_collapseOracle_eq_OracleNP`,
  `Cslib.Complexity.Barriers.Relativization.exists_oracle_OracleP_eq_OracleNP`: collapsing oracle
  for `OracleP = OracleNP`.
* `Cslib.Complexity.Barriers.Relativization.unaryLang_mem_OracleNP`,
  `Cslib.Complexity.Barriers.Relativization.unaryLang_not_mem_OracleP_sepOracle`,
  `Cslib.Complexity.Barriers.Relativization.OracleP_sepOracle_ssubset_OracleNP`,
  `Cslib.Complexity.Barriers.Relativization.exists_oracle_OracleP_ne_OracleNP`: separating oracle
  for `OracleP ⊂ OracleNP`.
* `Cslib.Complexity.Barriers.Relativization.relativization_barrier`: combined relativization
  barrier showing both `∃ A, OracleP A = OracleNP A` and `∃ B, OracleP B ≠ OracleNP B`.
-/

public section

namespace Cslib.Complexity.Barriers.Relativization

/-! ## 1. Decision Problems, Oracle Machines, and Gödel Enumeration -/

/-- A Boolean decision problem on finite binary strings. -/
abbrev DecisionProblem : Type := List Bool → Bool

/-- A complexity class modeled as a set of decision problems. -/
abbrev ComplexityClass : Type := Set DecisionProblem

/-- Six bitstring work registers (`0` holds the input initially; `1..5` start empty). -/
abbrev Reg : Type := Fin 6

/-- Syntax of a deterministic imperative multi-stack oracle machine.
Work registers act as binary stacks with `push`, `pop`, `pushHead`, `branchHead`, and
`whileNonEmpty`; a dedicated oracle query tape grows by at most one bit per step and queries
the oracle via `queryBranch`. -/
inductive OracleMachine : Type where
  /-- Do nothing and continue to the next instruction. -/
  | skip : OracleMachine
  /-- Halt immediately with the given Boolean output. -/
  | halt : Bool → OracleMachine
  /-- Empty a work register. -/
  | clear : Reg → OracleMachine
  /-- Push a constant bit onto the head of a work register. -/
  | push : Reg → Bool → OracleMachine
  /-- Pop the head bit of a work register (no-op if empty). -/
  | pop : Reg → OracleMachine
  /-- Copy the head bit of the source register onto the destination register (no-op if empty). -/
  | pushHead : Reg → Reg → OracleMachine
  /-- Empty the oracle query tape. -/
  | qClear : OracleMachine
  /-- Append a constant bit to the oracle query tape. -/
  | qPush : Bool → OracleMachine
  /-- Append the head bit of a work register to the oracle query tape (no-op if empty). -/
  | qPushHead : Reg → OracleMachine
  /-- Three-way branch on whether a register is empty, starts with `false`,
  or starts with `true`. -/
  | branchHead : Reg → OracleMachine → OracleMachine → OracleMachine → OracleMachine
  /-- Query the oracle on the current query tape and branch on `false` vs `true`. -/
  | queryBranch : OracleMachine → OracleMachine → OracleMachine
  /-- Sequential composition of two subprograms. -/
  | seq : OracleMachine → OracleMachine → OracleMachine
  /-- Execute a loop body repeatedly while the given register is nonempty. -/
  | whileNonEmpty : Reg → OracleMachine → OracleMachine

/-- Positive tag-payload pairing `Nat.pair t p + 1`, strictly exceeding `p`. -/
private def tagPair (t p : ℕ) : ℕ :=
  Nat.pair t p + 1

/-- Explicit computable Gödel number of an `OracleMachine`. -/
def encodeMachine : OracleMachine → ℕ
  | .skip => tagPair 0 0
  | .halt b => tagPair 1 (if b then 1 else 0)
  | .clear r => tagPair 2 r.val
  | .push r b => tagPair 3 (Nat.pair r.val (if b then 1 else 0))
  | .pop r => tagPair 4 r.val
  | .pushHead s d => tagPair 5 (Nat.pair s.val d.val)
  | .qClear => tagPair 6 0
  | .qPush b => tagPair 7 (if b then 1 else 0)
  | .qPushHead r => tagPair 8 r.val
  | .branchHead r p0 p1 p2 =>
      tagPair 9 (Nat.pair r.val (Nat.pair (encodeMachine p0)
        (Nat.pair (encodeMachine p1) (encodeMachine p2))))
  | .queryBranch p0 p1 => tagPair 10 (Nat.pair (encodeMachine p0) (encodeMachine p1))
  | .seq p1 p2 => tagPair 11 (Nat.pair (encodeMachine p1) (encodeMachine p2))
  | .whileNonEmpty r body => tagPair 12 (Nat.pair r.val (encodeMachine body))

/-- Fuel-bounded partial Gödel decoder for `OracleMachine`. -/
private def decodeMachineAux : ℕ → ℕ → Option OracleMachine
  | 0, _ => none
  | _ + 1, 0 => none
  | fuel + 1, code + 1 =>
      let (t, p) := Nat.unpair code
      match t with
      | 0 => if p = 0 then some .skip else none
      | 1 =>
          if p = 0 then some (.halt false)
          else if p = 1 then some (.halt true)
          else none
      | 2 => if h : p < 6 then some (.clear ⟨p, h⟩) else none
      | 3 =>
          let (rv, bv) := Nat.unpair p
          if h : rv < 6 then
            if bv = 0 then some (.push ⟨rv, h⟩ false)
            else if bv = 1 then some (.push ⟨rv, h⟩ true)
            else none
          else none
      | 4 => if h : p < 6 then some (.pop ⟨p, h⟩) else none
      | 5 =>
          let (sv, dv) := Nat.unpair p
          if hs : sv < 6 then
            if hd : dv < 6 then some (.pushHead ⟨sv, hs⟩ ⟨dv, hd⟩) else none
          else none
      | 6 => if p = 0 then some .qClear else none
      | 7 =>
          if p = 0 then some (.qPush false)
          else if p = 1 then some (.qPush true)
          else none
      | 8 => if h : p < 6 then some (.qPushHead ⟨p, h⟩) else none
      | 9 =>
          let (rv, rest1) := Nat.unpair p
          let (c0, rest2) := Nat.unpair rest1
          let (c1, c2) := Nat.unpair rest2
          if h : rv < 6 then
            match decodeMachineAux fuel c0, decodeMachineAux fuel c1, decodeMachineAux fuel c2 with
            | some m0, some m1, some m2 => some (.branchHead ⟨rv, h⟩ m0 m1 m2)
            | _, _, _ => none
          else none
      | 10 =>
          let (c0, c1) := Nat.unpair p
          match decodeMachineAux fuel c0, decodeMachineAux fuel c1 with
          | some m0, some m1 => some (.queryBranch m0 m1)
          | _, _ => none
      | 11 =>
          let (c0, c1) := Nat.unpair p
          match decodeMachineAux fuel c0, decodeMachineAux fuel c1 with
          | some m0, some m1 => some (.seq m0 m1)
          | _, _ => none
      | 12 =>
          let (rv, cb) := Nat.unpair p
          if h : rv < 6 then
            (decodeMachineAux fuel cb).map (.whileNonEmpty ⟨rv, h⟩)
          else none
      | _ => none

private theorem decodeMachineAux_encode (M : OracleMachine) :
    ∀ fuel : ℕ, encodeMachine M < fuel → decodeMachineAux fuel (encodeMachine M) = some M := by
  induction M with
  | skip =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f => simp [encodeMachine, tagPair, decodeMachineAux]
  | halt b =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f => cases b <;> simp [encodeMachine, tagPair, decodeMachineAux]
  | clear r =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f => simp [encodeMachine, tagPair, decodeMachineAux, r.isLt]
  | push r b =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f => cases b <;> simp [encodeMachine, tagPair, decodeMachineAux, r.isLt]
  | pop r =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f => simp [encodeMachine, tagPair, decodeMachineAux, r.isLt]
  | pushHead s d =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f => simp [encodeMachine, tagPair, decodeMachineAux, s.isLt, d.isLt]
  | qClear =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f => simp [encodeMachine, tagPair, decodeMachineAux]
  | qPush b =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f => cases b <;> simp [encodeMachine, tagPair, decodeMachineAux]
  | qPushHead r =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f => simp [encodeMachine, tagPair, decodeMachineAux, r.isLt]
  | branchHead r p0 p1 p2 ih0 ih1 ih2 =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f =>
          simp only [encodeMachine, tagPair] at hlt
          have hp : Nat.pair r.val (Nat.pair (encodeMachine p0)
              (Nat.pair (encodeMachine p1) (encodeMachine p2))) < f := by
            have := Nat.right_le_pair 9 (Nat.pair r.val (Nat.pair (encodeMachine p0)
              (Nat.pair (encodeMachine p1) (encodeMachine p2))))
            omega
          have h1 : Nat.pair (encodeMachine p0)
              (Nat.pair (encodeMachine p1) (encodeMachine p2)) ≤
              Nat.pair r.val (Nat.pair (encodeMachine p0)
                (Nat.pair (encodeMachine p1) (encodeMachine p2))) := Nat.right_le_pair _ _
          have hc0 : encodeMachine p0 < f := by
            have := Nat.left_le_pair (encodeMachine p0)
              (Nat.pair (encodeMachine p1) (encodeMachine p2))
            omega
          have h2 : Nat.pair (encodeMachine p1) (encodeMachine p2) ≤
              Nat.pair (encodeMachine p0)
                (Nat.pair (encodeMachine p1) (encodeMachine p2)) := Nat.right_le_pair _ _
          have hc1 : encodeMachine p1 < f := by
            have := Nat.left_le_pair (encodeMachine p1) (encodeMachine p2)
            omega
          have hc2 : encodeMachine p2 < f := by
            have := Nat.right_le_pair (encodeMachine p1) (encodeMachine p2)
            omega
          simp [encodeMachine, tagPair, decodeMachineAux, r.isLt,
            ih0 f hc0, ih1 f hc1, ih2 f hc2]
  | queryBranch p0 p1 ih0 ih1 =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f =>
          simp only [encodeMachine, tagPair] at hlt
          have hp : Nat.pair (encodeMachine p0) (encodeMachine p1) < f := by
            have := Nat.right_le_pair 10 (Nat.pair (encodeMachine p0) (encodeMachine p1))
            omega
          have hc0 : encodeMachine p0 < f := by
            have := Nat.left_le_pair (encodeMachine p0) (encodeMachine p1)
            omega
          have hc1 : encodeMachine p1 < f := by
            have := Nat.right_le_pair (encodeMachine p0) (encodeMachine p1)
            omega
          simp [encodeMachine, tagPair, decodeMachineAux, ih0 f hc0, ih1 f hc1]
  | seq p1 p2 ih1 ih2 =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f =>
          simp only [encodeMachine, tagPair] at hlt
          have hp : Nat.pair (encodeMachine p1) (encodeMachine p2) < f := by
            have := Nat.right_le_pair 11 (Nat.pair (encodeMachine p1) (encodeMachine p2))
            omega
          have hc1 : encodeMachine p1 < f := by
            have := Nat.left_le_pair (encodeMachine p1) (encodeMachine p2)
            omega
          have hc2 : encodeMachine p2 < f := by
            have := Nat.right_le_pair (encodeMachine p1) (encodeMachine p2)
            omega
          simp [encodeMachine, tagPair, decodeMachineAux, ih1 f hc1, ih2 f hc2]
  | whileNonEmpty r body ih =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f =>
          simp only [encodeMachine, tagPair] at hlt
          have hp : Nat.pair r.val (encodeMachine body) < f := by
            have := Nat.right_le_pair 12 (Nat.pair r.val (encodeMachine body))
            omega
          have hcb : encodeMachine body < f := by
            have := Nat.right_le_pair r.val (encodeMachine body)
            omega
          simp [encodeMachine, tagPair, decodeMachineAux, r.isLt, ih f hcb]

/-- Partial Gödel decoder inverting `encodeMachine`. -/
def decodeMachineOpt (e : ℕ) : Option OracleMachine :=
  decodeMachineAux (e + 1) e

/-- Decoding an encoded oracle machine recovers the original machine. -/
theorem decodeMachineOpt_encode (M : OracleMachine) :
    decodeMachineOpt (encodeMachine M) = some M :=
  decodeMachineAux_encode M (encodeMachine M + 1) (Nat.lt_succ_self _)

instance : Encodable OracleMachine where
  encode := encodeMachine
  decode := decodeMachineOpt
  encodek := decodeMachineOpt_encode

/-- Total Gödel enumeration `ℕ → OracleMachine` (mapping invalid codes to `.skip`). -/
@[expose] def decodeMachine (e : ℕ) : OracleMachine :=
  (decodeMachineOpt e).getD .skip

/-- Total decoding after encoding is the identity on `OracleMachine`. -/
@[simp]
theorem decodeMachine_encodeMachine (M : OracleMachine) :
    decodeMachine (encodeMachine M) = M := by
  simp [decodeMachine, decodeMachineOpt_encode]

/-! ## 2. Small-Step Operational Semantics, Query Bounds, and the Use Principle -/

/-- Instantaneous configuration of an `OracleMachine`: either halted with a Boolean output,
or actively executing `cur` with continuation stack `cont`, work registers `regs`, and
oracle query tape `qTape`. -/
inductive Config : Type where
  /-- Terminal halted configuration carrying a Boolean output. -/
  | halted : Bool → Config
  /-- Active execution state: current instruction, continuation stack, registers, query tape. -/
  | running : OracleMachine → List OracleMachine → (Reg → List Bool) → List Bool → Config

/-- Initial register bank: register `0` holds input `x`, registers `1..5` are empty. -/
@[expose] def initRegs (x : List Bool) : Reg → List Bool :=
  fun r => if r = 0 then x else []

/-- Initial configuration of `M` on input `x` with an empty query tape. -/
@[expose] def initConfig (M : OracleMachine) (x : List Bool) : Config :=
  .running M [] (initRegs x) []

/-- Single deterministic transition step of an `OracleMachine` relative to oracle `O`. -/
@[expose] def step (O : DecisionProblem) : Config → Config
  | .halted b => .halted b
  | .running .skip [] regs q => .running .skip [] regs q
  | .running .skip (c :: cs) regs q => .running c cs regs q
  | .running (.halt b) _ _ _ => .halted b
  | .running (.clear r) cs regs q =>
      .running .skip cs (Function.update regs r []) q
  | .running (.push r b) cs regs q =>
      .running .skip cs (Function.update regs r (b :: regs r)) q
  | .running (.pop r) cs regs q =>
      .running .skip cs (Function.update regs r (regs r).tail) q
  | .running (.pushHead src dst) cs regs q =>
      match regs src with
      | [] => .running .skip cs regs q
      | b :: _ => .running .skip cs (Function.update regs dst (b :: regs dst)) q
  | .running .qClear cs regs _q =>
      .running .skip cs regs []
  | .running (.qPush b) cs regs q =>
      .running .skip cs regs (q ++ [b])
  | .running (.qPushHead r) cs regs q =>
      match regs r with
      | [] => .running .skip cs regs q
      | b :: _ => .running .skip cs regs (q ++ [b])
  | .running (.branchHead r pNil pF pT) cs regs q =>
      match regs r with
      | [] => .running pNil cs regs q
      | false :: _ => .running pF cs regs q
      | true :: _ => .running pT cs regs q
  | .running (.queryBranch pF pT) cs regs q =>
      if O q then .running pT cs regs q else .running pF cs regs q
  | .running (.seq p1 p2) cs regs q =>
      .running p1 (p2 :: cs) regs q
  | .running (.whileNonEmpty r body) cs regs q =>
      match regs r with
      | [] => .running .skip cs regs q
      | _ :: _ => .running body (.whileNonEmpty r body :: cs) regs q

/-- Execute `t` deterministic steps relative to oracle `O`. -/
@[expose] def runSteps (O : DecisionProblem) : ℕ → Config → Config
  | 0, cfg => cfg
  | t + 1, cfg => runSteps O t (step O cfg)

/-- Step composition for `runSteps`. -/
theorem runSteps_add (O : DecisionProblem) (t₁ t₂ : ℕ) (cfg : Config) :
    runSteps O (t₁ + t₂) cfg = runSteps O t₂ (runSteps O t₁ cfg) := by
  induction t₁ generalizing cfg with
  | zero => simp [runSteps]
  | succ t₁ ih =>
      rw [Nat.succ_add]
      simp [runSteps, ih]

/-- Halted configurations remain fixed under further steps. -/
@[simp]
theorem runSteps_halted (O : DecisionProblem) (t : ℕ) (b : Bool) :
    runSteps O t (.halted b) = .halted b := by
  induction t with
  | zero => rfl
  | succ t ih => simp [runSteps, step, ih]

/-- Extract the Boolean output of a configuration if it has halted, otherwise `none`. -/
@[expose] def configOutput : Config → Option Bool
  | .halted b => some b
  | .running _ _ _ _ => none

/-- Universal step-bounded oracle evaluator for Gödel code `e`, oracle `O`, step budget `t`,
and input bitstring `x`. -/
@[expose] def evalOracle (e : ℕ) (O : DecisionProblem) (t : ℕ) (x : List Bool) : Option Bool :=
  configOutput (runSteps O t (initConfig (decodeMachine e) x))

/-- Once a machine halts within `t₁` steps, increasing the step budget preserves its output. -/
theorem evalOracle_mono {e : ℕ} {O : DecisionProblem} {t₁ t₂ : ℕ} {x : List Bool} {b : Bool}
    (h : evalOracle e O t₁ x = some b) (hle : t₁ ≤ t₂) :
    evalOracle e O t₂ x = some b := by
  unfold evalOracle at h ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [runSteps_add]
  cases hcfg : runSteps O t₁ (initConfig (decodeMachine e) x) with
  | halted b' =>
      rw [hcfg] at h
      simp only [configOutput, Option.some.injEq] at h
      subst h
      simp [configOutput]
  | running _ _ _ _ =>
      rw [hcfg] at h
      simp [configOutput] at h

/-- Query string inspected in a single configuration step, if any. -/
@[expose] def stepQuery : Config → Option (List Bool)
  | .running (.queryBranch _ _) _ _ q => some q
  | _ => none

/-- Finite set of oracle strings queried over `t` steps starting from `cfg`. -/
private def queriesAux (O : DecisionProblem) : ℕ → Config → Finset (List Bool)
  | 0, _ => ∅
  | t + 1, cfg =>
      (match stepQuery cfg with | some q => {q} | none => ∅) ∪ queriesAux O t (step O cfg)

/-- The finite set of strings on which machine `e` queries oracle `O` within `t` steps
on input `x`. -/
def queriedSet (e : ℕ) (O : DecisionProblem) (t : ℕ) (x : List Bool) : Finset (List Bool) :=
  queriesAux O t (initConfig (decodeMachine e) x)

private theorem queriesAux_subset_add (O : DecisionProblem) (t₁ t₂ : ℕ) (cfg : Config) :
    queriesAux O t₁ cfg ⊆ queriesAux O (t₁ + t₂) cfg := by
  induction t₁ generalizing cfg with
  | zero => simp [queriesAux]
  | succ t₁ ih =>
      rw [Nat.succ_add]
      unfold queriesAux
      exact Finset.union_subset_union_right (ih (step O cfg))

/-- The set of queried strings grows monotonically with the step budget. -/
theorem queriedSet_mono {e : ℕ} {O : DecisionProblem} {t₁ t₂ : ℕ} {x : List Bool}
    (hle : t₁ ≤ t₂) :
    queriedSet e O t₁ x ⊆ queriedSet e O t₂ x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact queriesAux_subset_add O t₁ d _

private theorem queriesAux_card_le (O : DecisionProblem) (t : ℕ) (cfg : Config) :
    (queriesAux O t cfg).card ≤ t := by
  induction t generalizing cfg with
  | zero => simp [queriesAux]
  | succ t ih =>
      unfold queriesAux
      have hsub := Finset.card_union_le
        (match stepQuery cfg with | some q => ({q} : Finset (List Bool)) | none => ∅)
        (queriesAux O t (step O cfg))
      have h1 :
          (match stepQuery cfg with | some q => ({q} : Finset (List Bool)) | none => ∅).card ≤
            1 := by
        cases stepQuery cfg <;> simp
      have h2 := ih (step O cfg)
      omega

/-- Machine `e` queries `O` on at most `t` distinct strings during `t` steps. -/
theorem queriedSet_card_le (e : ℕ) (O : DecisionProblem) (t : ℕ) (x : List Bool) :
    (queriedSet e O t x).card ≤ t :=
  queriesAux_card_le O t _

/-- Length of the active query tape in `cfg`. -/
private def configQTapeLen : Config → ℕ
  | .halted _ => 0
  | .running _ _ _ q => q.length

private theorem configQTapeLen_step_le (O : DecisionProblem) (cfg : Config) :
    configQTapeLen (step O cfg) ≤ configQTapeLen cfg + 1 := by
  cases cfg with
  | halted b => simp [step, configQTapeLen]
  | running cur cs regs q =>
      cases cur with
      | skip => cases cs <;> simp [step, configQTapeLen]
      | halt b => simp [step, configQTapeLen]
      | clear r => simp [step, configQTapeLen]
      | push r b => simp [step, configQTapeLen]
      | pop r => simp [step, configQTapeLen]
      | pushHead s d => cases h : regs s <;> simp [step, h, configQTapeLen]
      | qClear => simp [step, configQTapeLen]
      | qPush b => simp [step, configQTapeLen]
      | qPushHead r => cases h : regs r <;> simp [step, h, configQTapeLen]
      | branchHead r p0 p1 p2 =>
          cases h : regs r with
          | nil => simp [step, h, configQTapeLen]
          | cons b tl => cases b <;> simp [step, h, configQTapeLen]
      | queryBranch p0 p1 =>
          by_cases h : O q <;> simp [step, h, configQTapeLen]
      | seq p1 p2 => simp [step, configQTapeLen]
      | whileNonEmpty r body => cases h : regs r <;> simp [step, h, configQTapeLen]

private theorem queriesAux_length_lt (O : DecisionProblem) (t : ℕ) (cfg : Config) :
    ∀ q ∈ queriesAux O t cfg, q.length < configQTapeLen cfg + t := by
  induction t generalizing cfg with
  | zero => simp [queriesAux]
  | succ t ih =>
      intro q hq
      simp only [queriesAux, Finset.mem_union] at hq
      rcases hq with hnow | hrest
      · cases hsq : stepQuery cfg with
        | none => simp [hsq] at hnow
        | some q0 =>
            rw [hsq, Finset.mem_singleton] at hnow
            subst hnow
            cases cfg with
            | halted _ => simp [stepQuery] at hsq
            | running cur cs regs qt =>
                cases cur <;> simp only [stepQuery, reduceCtorEq, Option.some.injEq] at hsq
                subst hsq
                simp [configQTapeLen]
      · have hlt := ih (step O cfg) q hrest
        have hstep := configQTapeLen_step_le O cfg
        omega

/-- Every string queried within `t` steps has length strictly less than `t`. -/
theorem queriedSet_length_lt {e : ℕ} {O : DecisionProblem} {t : ℕ} {x q : List Bool}
    (hq : q ∈ queriedSet e O t x) : q.length < t := by
  have h := queriesAux_length_lt O t (initConfig (decodeMachine e) x) q hq
  simpa [initConfig, configQTapeLen] using h

/-- Every string queried within `t` steps on input `x` has length at most `max x.length t`. -/
theorem queriedSet_length_le_max {e : ℕ} {O : DecisionProblem} {t : ℕ} {x q : List Bool}
    (hq : q ∈ queriedSet e O t x) : q.length ≤ max x.length t := by
  have hlt := queriedSet_length_lt hq
  omega

private theorem runSteps_and_queriesAux_congr {O₁ O₂ : DecisionProblem} (t : ℕ) (cfg : Config)
    (hagree : ∀ q ∈ queriesAux O₁ t cfg, O₁ q = O₂ q) :
    runSteps O₁ t cfg = runSteps O₂ t cfg ∧ queriesAux O₁ t cfg = queriesAux O₂ t cfg := by
  induction t generalizing cfg with
  | zero => simp [runSteps, queriesAux]
  | succ t ih =>
      have hstep : step O₁ cfg = step O₂ cfg := by
        cases cfg with
        | halted b => rfl
        | running cur cs regs qt =>
            cases cur with
            | skip => cases cs <;> rfl
            | halt _ => rfl
            | clear _ => rfl
            | push _ _ => rfl
            | pop _ => rfl
            | pushHead s _ => cases regs s <;> rfl
            | qClear => rfl
            | qPush _ => rfl
            | qPushHead r => cases regs r <;> rfl
            | branchHead r _ _ _ =>
                cases regs r with
                | nil => rfl
                | cons b _ => cases b <;> rfl
            | queryBranch p0 p1 =>
                have hmem :
                    qt ∈ queriesAux O₁ (t + 1) (.running (.queryBranch p0 p1) cs regs qt) := by
                  simp [queriesAux, stepQuery]
                have heq := hagree qt hmem
                simp [step, heq]
            | seq _ _ => rfl
            | whileNonEmpty r _ => cases regs r <;> rfl
      have hsub : ∀ q ∈ queriesAux O₁ t (step O₁ cfg), O₁ q = O₂ q := by
        intro q hq
        apply hagree q
        simp [queriesAux, hq]
      obtain ⟨hrun, hqset⟩ := ih (step O₁ cfg) hsub
      refine ⟨?_, ?_⟩
      · change runSteps O₁ t (step O₁ cfg) = runSteps O₂ t (step O₂ cfg)
        rw [← hstep, hrun]
      · change (match stepQuery cfg with | some q => {q} | none => ∅) ∪
            queriesAux O₁ t (step O₁ cfg) =
          (match stepQuery cfg with | some q => {q} | none => ∅) ∪
            queriesAux O₂ t (step O₂ cfg)
        rw [← hstep, hqset]

/-- **The Use Principle**: if `O₁` and `O₂` agree on all strings in `queriedSet e O₁ t x`,
then machine `e` produces the same output in `t` steps on input `x` under both oracles. -/
theorem evalOracle_use_principle {e : ℕ} {O₁ O₂ : DecisionProblem} {t : ℕ} {x : List Bool}
    (hagree : ∀ q ∈ queriedSet e O₁ t x, O₁ q = O₂ q) :
    evalOracle e O₁ t x = evalOracle e O₂ t x := by
  unfold evalOracle
  rw [(runSteps_and_queriesAux_congr t _ hagree).1]

/-- Companion to the Use Principle: oracles agreeing on `queriedSet e O₁ t x` induce identical
query sets over `t` steps on input `x`. -/
theorem queriedSet_congr {e : ℕ} {O₁ O₂ : DecisionProblem} {t : ℕ} {x : List Bool}
    (hagree : ∀ q ∈ queriedSet e O₁ t x, O₁ q = O₂ q) :
    queriedSet e O₁ t x = queriedSet e O₂ t x :=
  (runSteps_and_queriesAux_congr t _ hagree).2

/-- Oracles agreeing on all strings of length `< t` induce identical outputs in `t` steps. -/
theorem evalOracle_congr_of_length_lt {e : ℕ} {O₁ O₂ : DecisionProblem} {t : ℕ} {x : List Bool}
    (hagree : ∀ q : List Bool, q.length < t → O₁ q = O₂ q) :
    evalOracle e O₁ t x = evalOracle e O₂ t x :=
  evalOracle_use_principle fun q hq => hagree q (queriedSet_length_lt hq)

/-! ## 3. Prefix-Free Bitstring Pairing and Relativized Classes `OracleP`, `OracleNP` -/

/-- Self-delimiting bit-doubling prefix encoding (`b ↦ [true, b]`, terminated by `[false]`). -/
@[expose] def encodePrefix : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: encodePrefix bs

/-- Length of the prefix-free encoding of `x`. -/
@[simp]
theorem encodePrefix_length (x : List Bool) :
    (encodePrefix x).length = 2 * x.length + 1 := by
  induction x with
  | nil => rfl
  | cons b bs ih =>
      simp only [encodePrefix, List.length_cons, ih]
      omega

/-- Injective bitstring pairing `(x, w) ↦ encodePrefix x ++ w`. -/
@[expose] def pair (x w : List Bool) : List Bool :=
  encodePrefix x ++ w

/-- Length of `pair x w`. -/
@[simp]
theorem pair_length (x w : List Bool) :
    (pair x w).length = 2 * x.length + 1 + w.length := by
  simp [pair]

private theorem encodePrefix_append_inj {x₁ x₂ w₁ w₂ : List Bool}
    (h : encodePrefix x₁ ++ w₁ = encodePrefix x₂ ++ w₂) : x₁ = x₂ ∧ w₁ = w₂ := by
  induction x₁ generalizing x₂ with
  | nil =>
      cases x₂ with
      | nil => simpa [encodePrefix] using h
      | cons b₂ bs₂ => simp [encodePrefix] at h
  | cons b₁ bs₁ ih =>
      cases x₂ with
      | nil => simp [encodePrefix] at h
      | cons b₂ bs₂ =>
          simp only [encodePrefix, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨rfl, hrest⟩ := h
          obtain ⟨rfl, rfl⟩ := ih hrest
          exact ⟨rfl, rfl⟩

/-- `pair` is injective on pairs of bitstrings. -/
theorem pair_injective {x₁ x₂ w₁ w₂ : List Bool} :
    pair x₁ w₁ = pair x₂ w₂ ↔ x₁ = x₂ ∧ w₁ = w₂ :=
  ⟨encodePrefix_append_inj, fun ⟨hx, hw⟩ => by subst hx; subst hw; rfl⟩

/-- Relativized deterministic polynomial time `P^O`. -/
@[expose] def OracleP (O : DecisionProblem) : ComplexityClass :=
  { L | ∃ (e : ℕ) (p : Polynomial ℕ),
      ∀ x : List Bool, evalOracle e O (p.eval x.length) x = some (L x) }

/-- Relativized nondeterministic polynomial time `NP^O`: polynomial-length witness `w` verified
in polynomial steps on `pair x w` relative to `O`. -/
@[expose] def OracleNP (O : DecisionProblem) : ComplexityClass :=
  { L | ∃ (e : ℕ) (p : Polynomial ℕ),
      ∀ x : List Bool, L x = true ↔
        ∃ w : List Bool, w.length ≤ p.eval x.length ∧
          evalOracle e O (p.eval x.length) (pair x w) = some true }

/-! ### Reusable Subprogram Verification Helpers -/

private theorem replicate_append_cons {α : Type*} (n : ℕ) (a : α) (l : List α) :
    List.replicate n a ++ a :: l = List.replicate (n + 1) a ++ l := by
  rw [List.replicate_add]
  simp

private theorem running_regs_congr (cur : OracleMachine) (cs : List OracleMachine)
    {regs₁ regs₂ : Reg → List Bool} (q : List Bool) (h : ∀ r, regs₁ r = regs₂ r) :
    Config.running cur cs regs₁ q = Config.running cur cs regs₂ q := by
  rw [funext h]

private theorem runSteps_seq_skip {O : DecisionProblem} {p₁ p₂ : OracleMachine}
    {cs : List OracleMachine} {regs regs₁ regs₂ : Reg → List Bool} {q q₁ q₂ : List Bool}
    {k₁ k₂ : ℕ}
    (h₁ : runSteps O k₁ (.running p₁ (p₂ :: cs) regs q) = .running .skip (p₂ :: cs) regs₁ q₁)
    (h₂ : runSteps O k₂ (.running p₂ cs regs₁ q₁) = .running .skip cs regs₂ q₂) :
    runSteps O (1 + k₁ + 1 + k₂) (.running (.seq p₁ p₂) cs regs q) =
      .running .skip cs regs₂ q₂ := by
  have s1 : runSteps O 1 (.running (.seq p₁ p₂) cs regs q) =
      .running p₁ (p₂ :: cs) regs q := rfl
  have s2 : runSteps O (1 + k₁) (.running (.seq p₁ p₂) cs regs q) =
      .running .skip (p₂ :: cs) regs₁ q₁ := by
    rw [runSteps_add, s1, h₁]
  have s3 : runSteps O (1 + k₁ + 1) (.running (.seq p₁ p₂) cs regs q) =
      .running p₂ cs regs₁ q₁ := by
    rw [runSteps_add, s2]; rfl
  rw [runSteps_add, s3, h₂]

private theorem runSteps_seq_halted {O : DecisionProblem} {p₁ p₂ : OracleMachine}
    {cs : List OracleMachine} {regs regs₁ : Reg → List Bool} {q q₁ : List Bool}
    {k₁ k₂ : ℕ} {b : Bool}
    (h₁ : runSteps O k₁ (.running p₁ (p₂ :: cs) regs q) = .running .skip (p₂ :: cs) regs₁ q₁)
    (h₂ : runSteps O k₂ (.running p₂ cs regs₁ q₁) = .halted b) :
    runSteps O (1 + k₁ + 1 + k₂) (.running (.seq p₁ p₂) cs regs q) = .halted b := by
  have s1 : runSteps O 1 (.running (.seq p₁ p₂) cs regs q) =
      .running p₁ (p₂ :: cs) regs q := rfl
  have s2 : runSteps O (1 + k₁) (.running (.seq p₁ p₂) cs regs q) =
      .running .skip (p₂ :: cs) regs₁ q₁ := by
    rw [runSteps_add, s1, h₁]
  have s3 : runSteps O (1 + k₁ + 1) (.running (.seq p₁ p₂) cs regs q) =
      .running p₂ cs regs₁ q₁ := by
    rw [runSteps_add, s2]; rfl
  rw [runSteps_add, s3, h₂]

/-! ### Structural Properties of `OracleP` and `OracleNP` -/

/-- Every constant Boolean function lies in `OracleP O` for every oracle `O`. -/
theorem const_mem_OracleP (O : DecisionProblem) (b : Bool) :
    (fun _ => b) ∈ OracleP O := by
  refine ⟨encodeMachine (.halt b), Polynomial.C 1, fun x => ?_⟩
  simp [evalOracle, decodeMachine_encodeMachine, initConfig, runSteps, step, configOutput]

/-- Machine that copies input register `0` to `qTape` and queries the oracle on it. -/
private def querySelfProg : OracleMachine :=
  .seq (.whileNonEmpty 0 (.seq (.qPushHead 0) (.pop 0)))
    (.queryBranch (.halt false) (.halt true))

private theorem runSteps_copyR0ToQTape (O : DecisionProblem) (l : List Bool)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool) (hr0 : regs 0 = l) :
    ∃ k ≤ 6 * l.length + 1,
      runSteps O k (.running (.whileNonEmpty 0 (.seq (.qPushHead 0) (.pop 0))) cs regs q) =
        .running .skip cs (Function.update regs 0 []) (q ++ l) := by
  induction l generalizing regs q with
  | nil =>
      refine ⟨1, by omega, ?_⟩
      simp only [runSteps, step, hr0, List.append_nil]
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [Function.update, hr0]
  | cons b bs ih =>
      let regs1 := Function.update regs 0 bs
      have hstep6 :
          runSteps O 6 (.running (.whileNonEmpty 0 (.seq (.qPushHead 0) (.pop 0))) cs regs q) =
            .running (.whileNonEmpty 0 (.seq (.qPushHead 0) (.pop 0))) cs regs1 (q ++ [b]) := by
        simp [runSteps, step, hr0, regs1]
      obtain ⟨k', hk', hrun'⟩ := ih regs1 (q ++ [b]) (by simp [regs1])
      refine ⟨6 + k', by simp only [List.length_cons]; omega, ?_⟩
      rw [runSteps_add, hstep6, hrun']
      simp [regs1, List.append_assoc]

/-- Every oracle `O` is itself decidable in polynomial time relative to `O`. -/
theorem self_mem_OracleP (O : DecisionProblem) : O ∈ OracleP O := by
  let e_self := encodeMachine querySelfProg
  let p_self : Polynomial ℕ := Polynomial.C 6 * Polynomial.X + Polynomial.C 5
  refine ⟨e_self, p_self, fun x => ?_⟩
  let qbr : OracleMachine := .queryBranch (.halt false) (.halt true)
  obtain ⟨k, hk, hcopy⟩ := runSteps_copyR0ToQTape O x [qbr] (initRegs x) [] (by simp [initRegs])
  have hq : runSteps O 2 (.running qbr [] (Function.update (initRegs x) 0 []) ([] ++ x)) =
      .halted (O x) := by
    by_cases ho : O x <;> simp [qbr, runSteps, step, ho]
  have htot := runSteps_seq_halted hcopy hq
  have hhalted : evalOracle e_self O (1 + k + 1 + 2) x = some (O x) := by
    unfold evalOracle
    simp only [e_self, decodeMachine_encodeMachine, initConfig, querySelfProg]
    rw [htot]
    rfl
  have hle : 1 + k + 1 + 2 ≤ p_self.eval x.length := by
    simp only [p_self, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  exact evalOracle_mono hhalted hle

/-- Syntactically negate all halting outputs of an `OracleMachine`. -/
private def negateMachine : OracleMachine → OracleMachine
  | .skip => .skip
  | .halt b => .halt (!b)
  | .clear r => .clear r
  | .push r b => .push r b
  | .pop r => .pop r
  | .pushHead s d => .pushHead s d
  | .qClear => .qClear
  | .qPush b => .qPush b
  | .qPushHead r => .qPushHead r
  | .branchHead r p0 p1 p2 =>
      .branchHead r (negateMachine p0) (negateMachine p1) (negateMachine p2)
  | .queryBranch p0 p1 => .queryBranch (negateMachine p0) (negateMachine p1)
  | .seq p1 p2 => .seq (negateMachine p1) (negateMachine p2)
  | .whileNonEmpty r body => .whileNonEmpty r (negateMachine body)

/-- Lift halt-output negation to configurations. -/
private def negateConfig : Config → Config
  | .halted b => .halted (!b)
  | .running cur cs regs q =>
      .running (negateMachine cur) (cs.map negateMachine) regs q

private theorem step_negateConfig (O : DecisionProblem) (cfg : Config) :
    step O (negateConfig cfg) = negateConfig (step O cfg) := by
  cases cfg with
  | halted b => rfl
  | running cur cs regs q =>
      cases cur with
      | skip => cases cs <;> rfl
      | halt b => rfl
      | clear r => rfl
      | push r b => rfl
      | pop r => rfl
      | pushHead s d => cases h : regs s <;> simp [negateConfig, negateMachine, step, h]
      | qClear => rfl
      | qPush b => rfl
      | qPushHead r => cases h : regs r <;> simp [negateConfig, negateMachine, step, h]
      | branchHead r p0 p1 p2 =>
          cases h : regs r with
          | nil => simp [negateConfig, negateMachine, step, h]
          | cons b tl => cases b <;> simp [negateConfig, negateMachine, step, h]
      | queryBranch p0 p1 =>
          by_cases ho : O q <;> simp [negateConfig, negateMachine, step, ho]
      | seq p1 p2 => rfl
      | whileNonEmpty r body => cases h : regs r <;> simp [negateConfig, negateMachine, step, h]

private theorem runSteps_negateConfig (O : DecisionProblem) (t : ℕ) (cfg : Config) :
    runSteps O t (negateConfig cfg) = negateConfig (runSteps O t cfg) := by
  induction t generalizing cfg with
  | zero => rfl
  | succ t ih =>
      simp only [runSteps, step_negateConfig, ih]

private theorem configOutput_negateConfig (cfg : Config) :
    configOutput (negateConfig cfg) = (configOutput cfg).map (!·) := by
  cases cfg <;> rfl

/-- `OracleP O` is closed under Boolean complement for every oracle `O`. -/
theorem compl_mem_OracleP {O L : DecisionProblem} (hL : L ∈ OracleP O) :
    (fun x => !L x) ∈ OracleP O := by
  obtain ⟨e, p, hp⟩ := hL
  refine ⟨encodeMachine (negateMachine (decodeMachine e)), p, fun x => ?_⟩
  unfold evalOracle
  rw [decodeMachine_encodeMachine]
  change configOutput
    (runSteps O (p.eval x.length) (negateConfig (initConfig (decodeMachine e) x))) = some (!L x)
  rw [runSteps_negateConfig, configOutput_negateConfig]
  have hx : configOutput (runSteps O (p.eval x.length) (initConfig (decodeMachine e) x)) =
      some (L x) := hp x
  rw [hx]
  rfl

/-- Concrete sensitivity witness for the Use Principle: there exists a machine whose query set
is `{[false]}` on every oracle, so it returns identical outputs on oracles agreeing at `[false]`
while distinguishing oracles that disagree at `[false]`. -/
theorem exists_machine_query_sensitivity :
    ∃ e : ℕ,
      (∀ O : DecisionProblem, queriedSet e O 10 [] = {[false]}) ∧
      (∀ O : DecisionProblem, evalOracle e O 10 [] = some (O [false])) := by
  let M : OracleMachine := .seq (.qPush false) (.queryBranch (.halt false) (.halt true))
  refine ⟨encodeMachine M, fun O => ?_, fun O => ?_⟩
  · unfold queriedSet
    simp only [decodeMachine_encodeMachine, initConfig, M]
    by_cases h : O [false] <;>
      simp [queriesAux, stepQuery, step, h]
  · unfold evalOracle
    simp only [decodeMachine_encodeMachine, initConfig, M]
    by_cases h : O [false] <;>
      simp [runSteps, step, configOutput, h]

/-- Body of the prefix-unpacking loop: reads `encodePrefix x ++ w` from register `0`, pushing
reversed bits of `x` onto `1`, using register `2` as the loop-active flag. -/
private def unpackPrefixLoopBody : OracleMachine :=
  .branchHead 0
    (.clear 2)
    (.seq (.pop 0) (.clear 2))
    (.seq (.pop 0) (.seq (.pushHead 0 1) (.pop 0)))

private theorem runSteps_unpackPrefixLoop (O : DecisionProblem) (x w acc : List Bool)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr0 : regs 0 = encodePrefix x ++ w) (hr1 : regs 1 = acc) (hr2 : regs 2 = [true]) :
    ∃ k ≤ 10 * x.length + 8,
      runSteps O k (.running (.whileNonEmpty 2 unpackPrefixLoopBody) cs regs q) =
        .running .skip cs
          (Function.update (Function.update (Function.update regs 0 w) 1 (x.reverse ++ acc)) 2 [])
          q := by
  induction x generalizing acc regs with
  | nil =>
      refine ⟨8, by omega, ?_⟩
      have h0 : regs 0 = false :: w := by simpa [encodePrefix] using hr0
      simp only [runSteps, step, hr2, unpackPrefixLoopBody, h0, List.reverse_nil, List.nil_append,
        Function.update_self, List.tail_cons]
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [Function.update, hr1]
  | cons b bs ih =>
      have h0 : regs 0 = true :: b :: (encodePrefix bs ++ w) := by
        simpa [encodePrefix] using hr0
      let regsA := Function.update regs 0 (b :: (encodePrefix bs ++ w))
      let regsB := Function.update regsA 1 (b :: acc)
      let regsC := Function.update regsB 0 (encodePrefix bs ++ w)
      have hstep10 : runSteps O 10 (.running (.whileNonEmpty 2 unpackPrefixLoopBody) cs regs q) =
          .running (.whileNonEmpty 2 unpackPrefixLoopBody) cs regsC q := by
        have ha0 : regsA 0 = b :: (encodePrefix bs ++ w) := by simp [regsA]
        have hb0 : regsB 0 = b :: (encodePrefix bs ++ w) := by simp [regsB, ha0]
        simp only [runSteps, step, hr2, unpackPrefixLoopBody, h0, List.tail_cons]
        change Config.running _ _
          (Function.update (Function.update regsA 1 (b :: regsA 1)) 0 (regsB 0).tail) q = _
        have ha1 : regsA 1 = acc := by simp [regsA, hr1]
        rw [ha1, hb0]
        rfl
      have hc0 : regsC 0 = encodePrefix bs ++ w := by simp [regsC]
      have hc1 : regsC 1 = b :: acc := by simp [regsC, regsB, Function.update]
      have hc2 : regsC 2 = [true] := by simp [regsC, regsB, regsA, Function.update, hr2]
      obtain ⟨k', hk', hrun'⟩ := ih (b :: acc) regsC hc0 hc1 hc2
      refine ⟨10 + k', by simp only [List.length_cons]; omega, ?_⟩
      rw [runSteps_add, hstep10, hrun']
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [regsC, regsB, regsA, Function.update, List.append_assoc]

/-- Move reversed contents of register `src` onto `dst`
(`dst := src.reverse ++ dst`, `src := []`). -/
private def revMoveProg (src dst : Reg) : OracleMachine :=
  .whileNonEmpty src (.seq (.pushHead src dst) (.pop src))

private theorem runSteps_revMoveProg (O : DecisionProblem) {src dst : Reg} (hne : src ≠ dst)
    (l acc : List Bool) (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hsrc : regs src = l) (hdst : regs dst = acc) :
    ∃ k ≤ 6 * l.length + 2,
      runSteps O k (.running (revMoveProg src dst) cs regs q) =
        .running .skip cs
          (Function.update (Function.update regs dst (l.reverse ++ acc)) src []) q := by
  induction l generalizing acc regs with
  | nil =>
      refine ⟨1, by omega, ?_⟩
      simp only [revMoveProg, runSteps, step, hsrc, List.reverse_nil, List.nil_append]
      refine running_regs_congr _ _ _ fun r => ?_
      by_cases hrs : r = src
      · subst hrs; simp [hsrc]
      · by_cases hrd : r = dst
        · subst hrd; simp [hrs, hdst]
        · simp [hrs, hrd]
  | cons b bs ih =>
      let regs1 := Function.update regs dst (b :: acc)
      let regs2 := Function.update regs1 src bs
      have hstep6 : runSteps O 6 (.running (revMoveProg src dst) cs regs q) =
          .running (revMoveProg src dst) cs regs2 q := by
        have h1s : regs1 src = b :: bs := by simp [regs1, hne, hsrc]
        simp [revMoveProg, runSteps, step, hsrc, hdst, regs1, regs2, h1s]
      have h2s : regs2 src = bs := by simp [regs2]
      have h2d : regs2 dst = b :: acc := by simp [regs2, regs1, hne.symm]
      obtain ⟨k', hk', hrun'⟩ := ih (b :: acc) regs2 h2s h2d
      refine ⟨6 + k', by simp only [List.length_cons]; omega, ?_⟩
      rw [runSteps_add, hstep6, hrun']
      refine running_regs_congr _ _ _ fun r => ?_
      by_cases hrs : r = src
      · subst hrs; simp [regs2, regs1]
      · by_cases hrd : r = dst
        · subst hrd; simp [hrs, regs2, regs1, List.append_assoc]
        · simp [hrs, hrd, regs2, regs1]

/-- Unpack `pair x w` in `initRegs (pair x w)` back to `initRegs x`, discarding `w`. -/
private def unpackFirstToInitProg : OracleMachine :=
  .seq (.push 2 true)
    (.seq (.whileNonEmpty 2 unpackPrefixLoopBody)
      (.seq (.clear 0) (revMoveProg 1 0)))

private theorem runSteps_unpackFirstToInitProg (O : DecisionProblem) (x w : List Bool)
    (cs : List OracleMachine) :
    ∃ k ≤ 16 * x.length + 20,
      runSteps O k (.running unpackFirstToInitProg cs (initRegs (pair x w)) []) =
        .running .skip cs (initRegs x) [] := by
  let regs0 := Function.update (initRegs (pair x w)) 2 [true]
  have hr0_1 : runSteps O 1
      (.running (.push 2 true)
        ([.seq (.whileNonEmpty 2 unpackPrefixLoopBody) (.seq (.clear 0) (revMoveProg 1 0))] ++ cs)
        (initRegs (pair x w)) []) =
      .running .skip
        ([.seq (.whileNonEmpty 2 unpackPrefixLoopBody) (.seq (.clear 0) (revMoveProg 1 0))] ++ cs)
        regs0 [] := rfl
  have h0_0 : regs0 0 = encodePrefix x ++ w := by simp [regs0, initRegs, pair]
  have h0_1 : regs0 1 = [] := by simp [regs0, initRegs]
  have h0_2 : regs0 2 = [true] := by simp [regs0]
  obtain ⟨k1, hk1, hrun1⟩ := runSteps_unpackPrefixLoop O x w []
    (.seq (.clear 0) (revMoveProg 1 0) :: cs) regs0 [] h0_0 h0_1 h0_2
  let regs1 :=
    Function.update (Function.update (Function.update regs0 0 w) 1 (x.reverse ++ [])) 2 []
  let regs2 := Function.update regs1 0 []
  have hr2_1 : regs2 1 = x.reverse := by simp [regs2, regs1, Function.update]
  have hr2_0 : regs2 0 = [] := by simp [regs2]
  have hne10 : (1 : Reg) ≠ 0 := by decide
  obtain ⟨k2, hk2, hrun2⟩ := runSteps_revMoveProg O hne10 x.reverse [] cs regs2 [] hr2_1 hr2_0
  have hcomb2 : runSteps O (1 + 1 + 1 + k2)
      (.running (.seq (.clear 0) (revMoveProg 1 0)) cs regs1 []) =
      .running .skip cs (initRegs x) [] := by
    have hc : runSteps O 1 (.running (.clear 0) (revMoveProg 1 0 :: cs) regs1 []) =
        .running .skip (revMoveProg 1 0 :: cs) regs2 [] := rfl
    have hs := runSteps_seq_skip hc hrun2
    rw [hs]
    refine running_regs_congr _ _ _ fun r => ?_
    fin_cases r <;> simp [regs2, regs1, regs0, initRegs, Function.update]
  have hcomb1 := runSteps_seq_skip hrun1 hcomb2
  have hcomb0 := runSteps_seq_skip hr0_1 hcomb1
  have hrev_len : x.reverse.length = x.length := List.length_reverse
  refine ⟨1 + 1 + 1 + (1 + k1 + 1 + (1 + 1 + 1 + k2)), by omega, ?_⟩
  simpa [unpackFirstToInitProg] using hcomb0

/-- Every language in `OracleP O` lies in `OracleNP O` for every oracle `O`. -/
theorem OracleP_subset_OracleNP (O : DecisionProblem) :
    OracleP O ⊆ OracleNP O := by
  intro L ⟨e, p, hp⟩
  let M_ver : OracleMachine := .seq unpackFirstToInitProg (decodeMachine e)
  let e_ver : ℕ := encodeMachine M_ver
  let q : Polynomial ℕ := p + Polynomial.C 16 * Polynomial.X + Polynomial.C 23
  refine ⟨e_ver, q, ?_⟩
  intro x
  have heval : ∀ w : List Bool,
      evalOracle e_ver O (q.eval x.length) (pair x w) = some (L x) := by
    intro w
    obtain ⟨k, hk, hrun⟩ := runSteps_unpackFirstToInitProg O x w [decodeMachine e]
    have hpre : runSteps O (1 + k + 1) (initConfig (decodeMachine e_ver) (pair x w)) =
        initConfig (decodeMachine e) x := by
      simp only [e_ver, decodeMachine_encodeMachine, initConfig, M_ver]
      have s1 : runSteps O 1 (.running (.seq unpackFirstToInitProg (decodeMachine e)) []
          (initRegs (pair x w)) []) =
          .running unpackFirstToInitProg [decodeMachine e] (initRegs (pair x w)) [] := rfl
      have s2 : runSteps O (1 + k) (.running (.seq unpackFirstToInitProg (decodeMachine e)) []
          (initRegs (pair x w)) []) =
          .running .skip [decodeMachine e] (initRegs x) [] := by
        rw [runSteps_add, s1, hrun]
      rw [runSteps_add, s2]
      rfl
    have hmain : evalOracle e O (p.eval x.length) x = some (L x) := hp x
    unfold evalOracle at hmain ⊢
    have htot_le : (1 + k + 1) + p.eval x.length ≤ q.eval x.length := by
      simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      omega
    obtain ⟨rem, hrem⟩ := Nat.exists_eq_add_of_le htot_le
    rw [hrem, runSteps_add, runSteps_add, hpre]
    cases hfin : runSteps O (p.eval x.length) (initConfig (decodeMachine e) x) with
    | halted b =>
        rw [hfin] at hmain
        simp only [configOutput, Option.some.injEq] at hmain
        subst hmain
        simp [configOutput]
    | running _ _ _ _ =>
        rw [hfin] at hmain
        simp [configOutput] at hmain
  constructor
  · intro hx
    refine ⟨[], Nat.zero_le _, ?_⟩
    rw [heval []]
    simp [hx]
  · rintro ⟨w, _, hw⟩
    rw [heval w] at hw
    simpa using hw

/-! ## 4. Collapsing Oracle Construction (`OracleP A = OracleNP A`) -/

/-- Enumerate all `2^n` bitstrings of exact length `n`. -/
private def bitstringsOfLen : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitstringsOfLen n).map (false :: ·) ++ (bitstringsOfLen n).map (true :: ·)

private theorem mem_bitstringsOfLen {n : ℕ} {w : List Bool} :
    w ∈ bitstringsOfLen n ↔ w.length = n := by
  induction n generalizing w with
  | zero =>
      cases w <;> simp [bitstringsOfLen]
  | succ n ih =>
      cases w with
      | nil => simp [bitstringsOfLen]
      | cons b bs =>
          cases b <;> simp [bitstringsOfLen, ih]

private theorem bitstringsOfLen_length (n : ℕ) :
    (bitstringsOfLen n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [bitstringsOfLen, List.length_append, List.length_map, ih, Nat.pow_succ]
      omega

private theorem bitstringsOfLen_nodup (n : ℕ) :
    (bitstringsOfLen n).Nodup := by
  induction n with
  | zero => simp [bitstringsOfLen]
  | succ n ih =>
      simp only [bitstringsOfLen]
      refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
      · exact ih.map fun _ _ h => (List.cons.inj h).2
      · exact ih.map fun _ _ h => (List.cons.inj h).2
      · intro x hx y hy hxy
        simp only [List.mem_map] at hx hy
        rcases hx with ⟨x', _, rfl⟩
        rcases hy with ⟨y', _, rfl⟩
        simp at hxy

/-- Enumerate all bitstrings of length at most `t`. -/
private def bitstringsLenLe (t : ℕ) : List (List Bool) :=
  (List.range (t + 1)).flatMap bitstringsOfLen

private theorem mem_bitstringsLenLe {t : ℕ} {w : List Bool} :
    w ∈ bitstringsLenLe t ↔ w.length ≤ t := by
  simp only [bitstringsLenLe, List.mem_flatMap, List.mem_range, mem_bitstringsOfLen]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro hw; exact ⟨w.length, by omega, rfl⟩

/-- Canonical padded self-encoding query `⟨e, x, 1^t⟩`:
`1^e ++ [0] ++ encodePrefix x ++ 1^(t+1)`, of length `e + 2 * x.length + t + 3 > t`. -/
@[expose] def encodeCollapseQuery (e : ℕ) (x : List Bool) (t : ℕ) : List Bool :=
  List.replicate e true ++ [false] ++ encodePrefix x ++ List.replicate (t + 1) true

/-- Every encoded collapse query is strictly longer than its step budget `t`. -/
theorem lt_encodeCollapseQuery_length (e : ℕ) (x : List Bool) (t : ℕ) :
    t < (encodeCollapseQuery e x t).length := by
  simp only [encodeCollapseQuery, List.length_append, List.length_replicate,
    List.length_singleton, encodePrefix_length]
  omega

/-- Parse leading `true` bits terminated by a single `false`. -/
private def parseUnaryFalse : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (parseUnaryFalse rest).map fun p => (p.1 + 1, p.2)

private theorem parseUnaryFalse_replicate (e : ℕ) (rest : List Bool) :
    parseUnaryFalse (List.replicate e true ++ false :: rest) = some (e, rest) := by
  induction e with
  | zero => rfl
  | succ e ih => simp [List.replicate_succ, parseUnaryFalse, ih]

/-- Parse `encodePrefix x` from the head of a bitstring. -/
private def parsePrefix : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => (parsePrefix rest).map fun p => (b :: p.1, p.2)
  | _ => none

private theorem parsePrefix_encodePrefix (x rest : List Bool) :
    parsePrefix (encodePrefix x ++ rest) = some (x, rest) := by
  induction x with
  | nil => rfl
  | cons b bs ih => simp [encodePrefix, parsePrefix, ih]

/-- Decode `encodeCollapseQuery e x t` uniquely into `some (e, x, t)`. -/
def decodeCollapseQuery (s : List Bool) : Option (ℕ × List Bool × ℕ) :=
  match parseUnaryFalse s with
  | none => none
  | some (e, r1) =>
      match parsePrefix r1 with
      | none => none
      | some (x, r2) =>
          match r2 with
          | true :: tl => if tl.all (· == true) then some (e, x, tl.length) else none
          | _ => none

/-- Decoding recovers the triple `(e, x, t)` from `encodeCollapseQuery e x t`. -/
@[simp]
theorem decodeCollapseQuery_encodeCollapseQuery (e : ℕ) (x : List Bool) (t : ℕ) :
    decodeCollapseQuery (encodeCollapseQuery e x t) = some (e, x, t) := by
  have h1 : encodeCollapseQuery e x t =
      List.replicate e true ++ false :: (encodePrefix x ++ List.replicate (t + 1) true) := by
    simp [encodeCollapseQuery, List.append_assoc]
  rw [h1]
  simp [decodeCollapseQuery, parseUnaryFalse_replicate, parsePrefix_encodePrefix,
    List.replicate_succ]

/-- Length-stratified stage construction of the collapsing oracle:
`collapseStage n` decides all strings of length `< n` by recursion on `n`. -/
private def collapseStage : ℕ → DecisionProblem
  | 0 => fun _ => false
  | n + 1 => fun s =>
      if s.length < n then collapseStage n s
      else if s.length = n then
        match decodeCollapseQuery s with
        | some (e, x, t) =>
            (bitstringsLenLe t).any fun w =>
              evalOracle e (collapseStage n) t (pair x w) == some true
        | none => false
      else false

private theorem collapseStage_stabilizes {n m : ℕ} {s : List Bool}
    (hs : s.length < n) (hnm : n ≤ m) :
    collapseStage m s = collapseStage n s := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
      · rfl
      · have hsm : s.length < m := by omega
        have hstep : collapseStage (m + 1) s = collapseStage m s := by
          simp [collapseStage, hsm]
        rw [hstep, ih (Nat.le_of_lt_succ hlt)]

/-- Explicit computable self-encoding oracle collapsing `OracleP` and `OracleNP`. -/
def collapseOracle (s : List Bool) : Bool :=
  collapseStage (s.length + 1) s

private theorem collapseOracle_eq_stage {n : ℕ} {s : List Bool} (hs : s.length < n) :
    collapseOracle s = collapseStage n s :=
  (collapseStage_stabilizes (Nat.lt_succ_self s.length) hs).symm

/-- Exact self-encoding fixed-point theorem for `collapseOracle`, proved via the Use Principle
and the strict query-length contraction `q.length < t < (encodeCollapseQuery e x t).length`. -/
theorem collapseOracle_encodeCollapseQuery (e : ℕ) (x : List Bool) (t : ℕ) :
    collapseOracle (encodeCollapseQuery e x t) = true ↔
      ∃ w : List Bool, w.length ≤ t ∧
        evalOracle e collapseOracle t (pair x w) = some true := by
  let s := encodeCollapseQuery e x t
  let n := s.length
  have hbgs : collapseOracle s =
      ((bitstringsLenLe t).any fun w =>
        evalOracle e (collapseStage n) t (pair x w) == some true) := by
    unfold collapseOracle
    change collapseStage (n + 1) s = _
    simp [collapseStage, n, s]
  rw [hbgs, List.any_eq_true]
  have hcongr : ∀ w : List Bool,
      evalOracle e (collapseStage n) t (pair x w) =
        evalOracle e collapseOracle t (pair x w) := fun w =>
    (evalOracle_congr_of_length_lt fun _ hqlt =>
      collapseOracle_eq_stage (Nat.lt_trans hqlt (lt_encodeCollapseQuery_length e x t))).symm
  constructor
  · rintro ⟨w, hwmem, hweval⟩
    rw [mem_bitstringsLenLe] at hwmem
    rw [beq_iff_eq, hcongr w] at hweval
    exact ⟨w, hwmem, hweval⟩
  · rintro ⟨w, hwlen, hweval⟩
    refine ⟨w, mem_bitstringsLenLe.mpr hwlen, ?_⟩
    rw [beq_iff_eq, hcongr w]
    exact hweval

/-! ### Unary Polynomial Evaluation and Query Construction in `OracleMachine` -/

/-- Push `c` copies of `true` onto register `r`. -/
private def pushNTrue (r : Reg) : ℕ → OracleMachine
  | 0 => .skip
  | c + 1 => .seq (.push r true) (pushNTrue r c)

private theorem runSteps_pushNTrue (O : DecisionProblem) (r : Reg) (c : ℕ)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool) :
    ∃ k ≤ 3 * c + 1,
      runSteps O k (.running (pushNTrue r c) cs regs q) =
        .running .skip cs (Function.update regs r (List.replicate c true ++ regs r)) q := by
  induction c generalizing regs with
  | zero =>
      refine ⟨0, by omega, ?_⟩
      simp [pushNTrue, runSteps]
  | succ c ih =>
      let regs1 := Function.update regs r (true :: regs r)
      have h1 : runSteps O 1 (.running (.push r true) (pushNTrue r c :: cs) regs q) =
          .running .skip (pushNTrue r c :: cs) regs1 q := rfl
      obtain ⟨k', hk', h2⟩ := ih regs1
      refine ⟨1 + 1 + 1 + k', by omega, ?_⟩
      rw [pushNTrue, runSteps_seq_skip h1 h2]
      refine running_regs_congr _ _ _ fun j => ?_
      by_cases hj : j = r
      · subst hj
        simpa [regs1] using replicate_append_cons c true (regs j)
      · simp [regs1, hj]

/-- Append `c` copies of `true` onto `qTape`. -/
private def qPushNTrue : ℕ → OracleMachine
  | 0 => .skip
  | c + 1 => .seq (.qPush true) (qPushNTrue c)

private theorem runSteps_qPushNTrue (O : DecisionProblem) (c : ℕ)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool) :
    ∃ k ≤ 3 * c + 1,
      runSteps O k (.running (qPushNTrue c) cs regs q) =
        .running .skip cs regs (q ++ List.replicate c true) := by
  induction c generalizing q with
  | zero =>
      refine ⟨0, by omega, ?_⟩
      simp [qPushNTrue, runSteps]
  | succ c ih =>
      have h1 : runSteps O 1 (.running (.qPush true) (qPushNTrue c :: cs) regs q) =
          .running .skip (qPushNTrue c :: cs) regs (q ++ [true]) := rfl
      obtain ⟨k', hk', h2⟩ := ih (q ++ [true])
      refine ⟨1 + 1 + 1 + k', by omega, ?_⟩
      rw [qPushNTrue, runSteps_seq_skip h1 h2, List.append_assoc]
      rfl

/-- Copy `x.length` in unary (`List.replicate x.length true`) into register `1` while keeping
register `0` equal to `x`, using register `3` as temporary reversal buffer. -/
private def copyLenToR1Prog : OracleMachine :=
  .seq
    (.whileNonEmpty 0 (.seq (.pushHead 0 3) (.seq (.push 1 true) (.pop 0))))
    (revMoveProg 3 0)

private theorem runSteps_copyLenLoop (O : DecisionProblem) (l acc1 acc3 : List Bool)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr0 : regs 0 = l) (hr1 : regs 1 = acc1) (hr3 : regs 3 = acc3) :
    ∃ k ≤ 9 * l.length + 2,
      runSteps O k
        (.running (.whileNonEmpty 0 (.seq (.pushHead 0 3) (.seq (.push 1 true) (.pop 0))))
          cs regs q) =
        .running .skip cs
          (Function.update (Function.update (Function.update regs 0 [])
            1 (List.replicate l.length true ++ acc1)) 3 (l.reverse ++ acc3)) q := by
  induction l generalizing acc1 acc3 regs with
  | nil =>
      refine ⟨1, by omega, ?_⟩
      simp only [runSteps, step, hr0, List.length_nil, List.replicate_zero,
        List.nil_append, List.reverse_nil]
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [Function.update, hr0, hr1, hr3]
  | cons b bs ih =>
      let regsA := Function.update regs 3 (b :: acc3)
      let regsB := Function.update regsA 1 (true :: acc1)
      let regsC := Function.update regsB 0 bs
      have hstep9 : runSteps O 9
          (.running (.whileNonEmpty 0 (.seq (.pushHead 0 3) (.seq (.push 1 true) (.pop 0))))
            cs regs q) =
          .running (.whileNonEmpty 0 (.seq (.pushHead 0 3) (.seq (.push 1 true) (.pop 0))))
            cs regsC q := by
        have ha1 : regsA 1 = acc1 := by simp [regsA, hr1]
        have hb0 : regsB 0 = b :: bs := by simp [regsB, regsA, hr0]
        simp only [runSteps, step, hr0, hr3]
        change Config.running _ _
          (Function.update (Function.update regsA 1 (true :: regsA 1)) 0 (regsB 0).tail) q = _
        rw [ha1, hb0]
        rfl
      have hc0 : regsC 0 = bs := by simp [regsC]
      have hc1 : regsC 1 = true :: acc1 := by simp [regsC, regsB]
      have hc3 : regsC 3 = b :: acc3 := by simp [regsC, regsB, regsA]
      obtain ⟨k', hk', hrun'⟩ := ih (true :: acc1) (b :: acc3) regsC hc0 hc1 hc3
      refine ⟨9 + k', by simp only [List.length_cons]; omega, ?_⟩
      rw [runSteps_add, hstep9, hrun']
      have hrep := replicate_append_cons bs.length true acc1
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [regsC, regsB, regsA, Function.update, hrep, List.append_assoc]

private theorem runSteps_copyLenToR1Prog (O : DecisionProblem) (x : List Bool)
    (cs : List OracleMachine) :
    ∃ k ≤ 15 * x.length + 8,
      runSteps O k (.running copyLenToR1Prog cs (initRegs x) []) =
        .running .skip cs (Function.update (initRegs x) 1 (List.replicate x.length true)) [] := by
  obtain ⟨k1, hk1, h1⟩ := runSteps_copyLenLoop O x [] [] (revMoveProg 3 0 :: cs)
    (initRegs x) [] (by simp [initRegs]) (by simp [initRegs]) (by simp [initRegs])
  let regsMid := Function.update (Function.update (Function.update (initRegs x) 0 [])
    1 (List.replicate x.length true ++ [])) 3 (x.reverse ++ [])
  have hne30 : (3 : Reg) ≠ 0 := by decide
  obtain ⟨k2, hk2, h2⟩ := runSteps_revMoveProg O hne30 x.reverse [] cs regsMid []
    (by simp [regsMid]) (by simp [regsMid])
  have hrev_len : x.reverse.length = x.length := List.length_reverse
  refine ⟨1 + k1 + 1 + k2, by omega, ?_⟩
  rw [copyLenToR1Prog, runSteps_seq_skip h1 h2]
  refine running_regs_congr _ _ _ fun r => ?_
  fin_cases r <;> simp [regsMid, initRegs, Function.update]

/-- Append `r1.length` copies of `true` onto `r2` while preserving `r1 = List.replicate n true`,
using `r4` as a temporary buffer. -/
private def appendR1UnaryToR2 : OracleMachine :=
  .seq
    (.whileNonEmpty 1 (.seq (.push 4 true) (.seq (.push 2 true) (.pop 1))))
    (.whileNonEmpty 4 (.seq (.push 1 true) (.pop 4)))

private theorem runSteps_drainR1ToR4R2 (O : DecisionProblem) (m : ℕ) (acc2 acc4 : List Bool)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr1 : regs 1 = List.replicate m true) (hr2 : regs 2 = acc2) (hr4 : regs 4 = acc4) :
    ∃ k ≤ 9 * m + 2,
      runSteps O k
        (.running (.whileNonEmpty 1 (.seq (.push 4 true) (.seq (.push 2 true) (.pop 1))))
          cs regs q) =
        .running .skip cs
          (Function.update (Function.update (Function.update regs 1 [])
            2 (List.replicate m true ++ acc2)) 4 (List.replicate m true ++ acc4)) q := by
  induction m generalizing acc2 acc4 regs with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [List.replicate_zero, List.nil_append, runSteps, step, hr1]
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [Function.update, hr1, hr2, hr4]
  | succ m ih =>
      let regsA := Function.update regs 4 (true :: acc4)
      let regsB := Function.update regsA 2 (true :: acc2)
      let regsC := Function.update regsB 1 (List.replicate m true)
      have hstep9 : runSteps O 9
          (.running (.whileNonEmpty 1 (.seq (.push 4 true) (.seq (.push 2 true) (.pop 1))))
            cs regs q) =
          .running (.whileNonEmpty 1 (.seq (.push 4 true) (.seq (.push 2 true) (.pop 1))))
            cs regsC q := by
        have hr1' : regs 1 = true :: List.replicate m true := by
          simpa [List.replicate_succ] using hr1
        have ha2 : regsA 2 = acc2 := by simp [regsA, hr2]
        have hb1 : regsB 1 = true :: List.replicate m true := by
          simp [regsB, regsA, hr1']
        simp only [runSteps, step, hr1', hr4]
        change Config.running _ _
          (Function.update (Function.update regsA 2 (true :: regsA 2)) 1 (regsB 1).tail) q = _
        rw [ha2, hb1]
        rfl
      obtain ⟨k', hk', hrun'⟩ := ih (true :: acc2) (true :: acc4) regsC
        (by simp [regsC]) (by simp [regsC, regsB])
        (by simp [regsC, regsB, regsA])
      refine ⟨9 + k', by omega, ?_⟩
      rw [runSteps_add, hstep9, hrun']
      have hrep2 := replicate_append_cons m true acc2
      have hrep4 := replicate_append_cons m true acc4
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [regsC, regsB, regsA, Function.update, hrep2, hrep4]

private theorem runSteps_moveUnary (O : DecisionProblem) {src dst : Reg} (hne : src ≠ dst)
    (m : ℕ) (acc : List Bool) (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hsrc : regs src = List.replicate m true) (hdst : regs dst = acc) :
    ∃ k ≤ 6 * m + 2,
      runSteps O k (.running (.whileNonEmpty src (.seq (.push dst true) (.pop src))) cs regs q) =
        .running .skip cs
          (Function.update (Function.update regs dst (List.replicate m true ++ acc)) src []) q := by
  induction m generalizing acc regs with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [List.replicate_zero, List.nil_append, runSteps, step, hsrc]
      refine running_regs_congr _ _ _ fun r => ?_
      by_cases hrs : r = src
      · subst hrs; simp [hsrc]
      · by_cases hrd : r = dst
        · subst hrd; simp [hrs, hdst]
        · simp [hrs, hrd]
  | succ m ih =>
      let regsA := Function.update regs dst (true :: acc)
      let regsB := Function.update regsA src (List.replicate m true)
      have hstep6 : runSteps O 6
          (.running (.whileNonEmpty src (.seq (.push dst true) (.pop src))) cs regs q) =
          .running (.whileNonEmpty src (.seq (.push dst true) (.pop src))) cs regsB q := by
        have hsrc' : regs src = true :: List.replicate m true := by
          simpa [List.replicate_succ] using hsrc
        have ha : regsA src = true :: List.replicate m true := by simp [regsA, hne, hsrc']
        simp [runSteps, step, hsrc', hdst, regsA, regsB, ha]
      obtain ⟨k', hk', hrun'⟩ := ih (true :: acc) regsB
        (by simp [regsB]) (by simp [regsB, regsA, hne.symm])
      refine ⟨6 + k', by omega, ?_⟩
      rw [runSteps_add, hstep6, hrun']
      have hrep := replicate_append_cons m true acc
      refine running_regs_congr _ _ _ fun r => ?_
      by_cases hrs : r = src
      · subst hrs; simp [regsB, regsA]
      · by_cases hrd : r = dst
        · subst hrd; simp [hrs, regsB, regsA, hrep]
        · simp [hrs, hrd, regsB, regsA]

private theorem runSteps_appendR1UnaryToR2 (O : DecisionProblem) (n : ℕ) (acc2 : List Bool)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr1 : regs 1 = List.replicate n true) (hr2 : regs 2 = acc2) (hr4 : regs 4 = []) :
    ∃ k ≤ 15 * n + 6,
      runSteps O k (.running appendR1UnaryToR2 cs regs q) =
        .running .skip cs (Function.update regs 2 (List.replicate n true ++ acc2)) q := by
  obtain ⟨k1, hk1, h1⟩ := runSteps_drainR1ToR4R2 O n acc2 []
    (.whileNonEmpty 4 (.seq (.push 1 true) (.pop 4)) :: cs) regs q hr1 hr2 hr4
  let regsMid := Function.update (Function.update (Function.update regs 1 [])
    2 (List.replicate n true ++ acc2)) 4 (List.replicate n true ++ [])
  have hne41 : (4 : Reg) ≠ 1 := by decide
  obtain ⟨k2, hk2, h2⟩ := runSteps_moveUnary O hne41 n [] cs regsMid q
    (by simp [regsMid]) (by simp [regsMid])
  refine ⟨1 + k1 + 1 + k2, by omega, ?_⟩
  rw [appendR1UnaryToR2, runSteps_seq_skip h1 h2]
  refine running_regs_congr _ _ _ fun r => ?_
  fin_cases r <;> simp [regsMid, Function.update, hr1, hr4]

/-- Horner step `r2 := replicate (c + n * acc) true` given `r1 = replicate n true`,
`r2 = replicate acc true`, and `r3 = r4 = []`. -/
private def hornerStepProg (c : ℕ) : OracleMachine :=
  .seq
    (.whileNonEmpty 2 (.seq (.push 3 true) (.pop 2)))
    (.seq
      (.whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2))
      (pushNTrue 2 c))

private theorem runSteps_mulLoopR3 (O : DecisionProblem) (n acc cur : ℕ)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr1 : regs 1 = List.replicate n true)
    (hr2 : regs 2 = List.replicate cur true)
    (hr3 : regs 3 = List.replicate acc true)
    (hr4 : regs 4 = []) :
    ∃ k ≤ acc * (15 * n + 11) + 2,
      runSteps O k (.running (.whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2)) cs regs q) =
        .running .skip cs
          (Function.update (Function.update regs 2 (List.replicate (acc * n + cur) true)) 3 [])
          q := by
  induction acc generalizing cur regs with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [List.replicate_zero, Nat.zero_mul, Nat.zero_add, runSteps, step, hr3]
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [Function.update, hr2, hr3]
  | succ acc ih =>
      have hr3' : regs 3 = true :: List.replicate acc true := by
        simpa [List.replicate_succ] using hr3
      let regsA := Function.update regs 3 (List.replicate acc true)
      have hpop : runSteps O 1
          (.running (.pop 3)
            (appendR1UnaryToR2 :: .whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2) :: cs)
            regs q) =
          .running .skip
            (appendR1UnaryToR2 :: .whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2) :: cs)
            regsA q := by
        simp [runSteps, step, hr3', regsA]
      obtain ⟨kB, hkB, hB⟩ := runSteps_appendR1UnaryToR2 O n (List.replicate cur true)
        (.whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2) :: cs) regsA q
        (by simp [regsA, hr1])
        (by simp [regsA, hr2])
        (by simp [regsA, hr4])
      have hbody := runSteps_seq_skip hpop hB
      let regsB := Function.update regsA 2 (List.replicate n true ++ List.replicate cur true)
      have hiter : runSteps O (1 + (1 + 1 + 1 + kB) + 1)
          (.running (.whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2)) cs regs q) =
          .running (.whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2)) cs regsB q := by
        have s1 : runSteps O 1
            (.running (.whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2)) cs regs q) =
            .running (.seq (.pop 3) appendR1UnaryToR2)
              (.whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2) :: cs) regs q := by
          simp [runSteps, step, hr3']
        have s2 : runSteps O (1 + (1 + 1 + 1 + kB))
            (.running (.whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2)) cs regs q) =
            .running .skip (.whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2) :: cs) regsB q := by
          rw [runSteps_add, s1, hbody]
        rw [runSteps_add, s2]
        rfl
      have hrep : List.replicate n true ++ List.replicate cur true =
          List.replicate (n + cur) true := (List.replicate_add n cur true).symm
      obtain ⟨k', hk', hrun'⟩ := ih (n + cur) regsB
        (by simp [regsB, regsA, hr1])
        (by simp [regsB, hrep])
        (by simp [regsB, regsA])
        (by simp [regsB, regsA, hr4])
      have hbound : (1 + (1 + 1 + 1 + kB) + 1) + k' ≤ (acc + 1) * (15 * n + 11) + 2 := by
        rw [Nat.succ_mul]
        omega
      refine ⟨(1 + (1 + 1 + 1 + kB) + 1) + k', hbound, ?_⟩
      rw [runSteps_add, hiter, hrun']
      have harith : acc * n + (n + cur) = (acc + 1) * n + cur := by
        rw [Nat.succ_mul]; omega
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [regsB, regsA, Function.update, harith]

private theorem runSteps_hornerStepProg (O : DecisionProblem) (c n acc : ℕ)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr1 : regs 1 = List.replicate n true)
    (hr2 : regs 2 = List.replicate acc true)
    (hr3 : regs 3 = []) (hr4 : regs 4 = []) :
    ∃ k ≤ acc * (15 * n + 17) + 3 * c + 12,
      runSteps O k (.running (hornerStepProg c) cs regs q) =
        .running .skip cs (Function.update regs 2 (List.replicate (c + n * acc) true)) q := by
  have hne23 : (2 : Reg) ≠ 3 := by decide
  obtain ⟨k1, hk1, h1⟩ := runSteps_moveUnary O hne23 acc []
    (.seq (.whileNonEmpty 3 (.seq (.pop 3) appendR1UnaryToR2)) (pushNTrue 2 c) :: cs) regs q
    hr2 hr3
  let regs1 := Function.update (Function.update regs 3 (List.replicate acc true ++ [])) 2 []
  obtain ⟨k2, hk2, h2⟩ := runSteps_mulLoopR3 O n acc 0 (pushNTrue 2 c :: cs) regs1 q
    (by simp [regs1, Function.update, hr1])
    (by simp [regs1])
    (by simp [regs1, Function.update])
    (by simp [regs1, Function.update, hr4])
  let regs2 := Function.update (Function.update regs1 2 (List.replicate (acc * n + 0) true)) 3 []
  obtain ⟨k3, hk3, h3⟩ := runSteps_pushNTrue O 2 c cs regs2 q
  have hcomb23 := runSteps_seq_skip h2 h3
  have hcomb123 := runSteps_seq_skip h1 hcomb23
  have hbound : 1 + k1 + 1 + (1 + k2 + 1 + k3) ≤ acc * (15 * n + 17) + 3 * c + 12 := by
    have hmul : 6 * acc + acc * (15 * n + 11) = acc * (15 * n + 17) := by
      rw [Nat.mul_add, Nat.mul_add]
      omega
    omega
  refine ⟨1 + k1 + 1 + (1 + k2 + 1 + k3), hbound, ?_⟩
  rw [hornerStepProg, hcomb123]
  have hrep : List.replicate c true ++ List.replicate (acc * n) true =
      List.replicate (c + n * acc) true := by
    rw [← List.replicate_add, Nat.mul_comm]
  refine running_regs_congr _ _ _ fun r => ?_
  fin_cases r <;> simp [regs2, regs1, Function.update, hr3, hrep]

/-- Horner evaluation of a coefficient list `[c₀, c₁, ..., c_{k-1}]` at `n`. -/
private def hornerVal : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, n => c + n * hornerVal cs n

private theorem hornerVal_append_singleton (l : List ℕ) (a n : ℕ) :
    hornerVal (l ++ [a]) n = hornerVal l n + a * n ^ l.length := by
  induction l with
  | nil => simp [hornerVal]
  | cons b bs ih =>
      simp only [List.cons_append, hornerVal, ih, List.length_cons, Nat.pow_succ]
      ring

private theorem hornerVal_map_range (f : ℕ → ℕ) (k n : ℕ) :
    hornerVal ((List.range k).map f) n = ∑ i ∈ Finset.range k, f i * n ^ i := by
  induction k with
  | zero => simp [hornerVal]
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton,
        hornerVal_append_singleton, List.length_map, List.length_range, ih,
        Finset.sum_range_succ]

private theorem hornerVal_polyCoeffs (p : Polynomial ℕ) (n : ℕ) :
    hornerVal ((List.range (p.natDegree + 1)).map p.coeff) n = p.eval n := by
  rw [hornerVal_map_range, Polynomial.eval_eq_sum_range]

/-- Synthesize an `OracleMachine` evaluating `hornerVal cs n` in unary on register `2`. -/
private def hornerProg : List ℕ → OracleMachine
  | [] => .clear 2
  | c :: cs => .seq (hornerProg cs) (hornerStepProg c)

/-- Polynomial representation of `hornerVal cs`. -/
private noncomputable def hornerValPoly : List ℕ → Polynomial ℕ
  | [] => 0
  | c :: cs => Polynomial.C c + Polynomial.X * hornerValPoly cs

private theorem hornerValPoly_eval (cs : List ℕ) (n : ℕ) :
    (hornerValPoly cs).eval n = hornerVal cs n := by
  induction cs with
  | nil => simp [hornerValPoly, hornerVal]
  | cons c cs ih => simp [hornerValPoly, hornerVal, ih]

/-- Polynomial step-count bound for `hornerProg cs` on unary input `n`. -/
private noncomputable def hornerBoundPoly : List ℕ → Polynomial ℕ
  | [] => Polynomial.C 2
  | c :: cs =>
      hornerBoundPoly cs +
        hornerValPoly cs * (Polynomial.C 15 * Polynomial.X + Polynomial.C 17) +
        Polynomial.C (3 * c + 15)

private theorem runSteps_hornerProg (O : DecisionProblem) (cs_coeff : List ℕ) (n : ℕ)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr1 : regs 1 = List.replicate n true)
    (hr3 : regs 3 = []) (hr4 : regs 4 = []) :
    ∃ k ≤ (hornerBoundPoly cs_coeff).eval n,
      runSteps O k (.running (hornerProg cs_coeff) cs regs q) =
        .running .skip cs
          (Function.update regs 2 (List.replicate (hornerVal cs_coeff n) true)) q := by
  induction cs_coeff generalizing cs regs with
  | nil =>
      refine ⟨1, ?_, ?_⟩
      · simp [hornerBoundPoly]
      · simp [hornerProg, hornerVal, runSteps, step]
  | cons c rest ih =>
      obtain ⟨k1, hk1, h1⟩ := ih (hornerStepProg c :: cs) regs hr1 hr3 hr4
      let regs1 := Function.update regs 2 (List.replicate (hornerVal rest n) true)
      obtain ⟨k2, hk2, h2⟩ := runSteps_hornerStepProg O c n (hornerVal rest n) cs regs1 q
        (by simp [regs1, hr1])
        (by simp [regs1])
        (by simp [regs1, hr3])
        (by simp [regs1, hr4])
      refine ⟨1 + k1 + 1 + k2, ?_, ?_⟩
      · simp only [hornerBoundPoly, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X, hornerValPoly_eval]
        omega
      · rw [hornerProg, runSteps_seq_skip h1 h2]
        simp [regs1, hornerVal]

/-- Append `encodePrefix x` from register `0` onto `qTape`, clearing register `0`. -/
private def qAppendPrefixFromR0 : OracleMachine :=
  .seq
    (.whileNonEmpty 0 (.seq (.qPush true) (.seq (.qPushHead 0) (.pop 0))))
    (.qPush false)

private theorem runSteps_qAppendPrefixLoop (O : DecisionProblem) (x : List Bool)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr0 : regs 0 = x) :
    ∃ k ≤ 9 * x.length + 2,
      runSteps O k
        (.running (.whileNonEmpty 0 (.seq (.qPush true) (.seq (.qPushHead 0) (.pop 0))))
          cs regs q) =
        .running .skip cs (Function.update regs 0 [])
          (q ++ x.flatMap fun b => [true, b]) := by
  induction x generalizing regs q with
  | nil =>
      refine ⟨1, by omega, ?_⟩
      simp only [runSteps, step, hr0, List.flatMap_nil, List.append_nil]
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [Function.update, hr0]
  | cons b bs ih =>
      let regsC := Function.update regs 0 bs
      have hstep9 : runSteps O 9
          (.running (.whileNonEmpty 0 (.seq (.qPush true) (.seq (.qPushHead 0) (.pop 0))))
            cs regs q) =
          .running (.whileNonEmpty 0 (.seq (.qPush true) (.seq (.qPushHead 0) (.pop 0))))
            cs regsC (q ++ [true, b]) := by
        simp [runSteps, step, hr0, regsC, List.append_assoc]
      obtain ⟨k', hk', hrun'⟩ := ih regsC (q ++ [true, b]) (by simp [regsC])
      refine ⟨9 + k', by simp only [List.length_cons]; omega, ?_⟩
      rw [runSteps_add, hstep9, hrun']
      simp [regsC, List.flatMap_cons, List.append_assoc]

private theorem flatMap_true_append_false (x : List Bool) :
    (x.flatMap fun b => [true, b]) ++ [false] = encodePrefix x := by
  induction x with
  | nil => rfl
  | cons b bs ih => simp [encodePrefix, List.flatMap_cons, ← ih]

private theorem runSteps_qAppendPrefixFromR0 (O : DecisionProblem) (x : List Bool)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr0 : regs 0 = x) :
    ∃ k ≤ 9 * x.length + 6,
      runSteps O k (.running qAppendPrefixFromR0 cs regs q) =
        .running .skip cs (Function.update regs 0 []) (q ++ encodePrefix x) := by
  obtain ⟨k1, hk1, h1⟩ := runSteps_qAppendPrefixLoop O x (.qPush false :: cs) regs q hr0
  have h2 : runSteps O 1
      (.running (.qPush false) cs (Function.update regs 0 [])
        (q ++ x.flatMap fun b => [true, b])) =
      .running .skip cs (Function.update regs 0 []) (q ++ encodePrefix x) := by
    simp [runSteps, step, List.append_assoc, flatMap_true_append_false]
  refine ⟨1 + k1 + 1 + 1, by omega, ?_⟩
  exact runSteps_seq_skip h1 h2

/-- Append `t` copies of `true` onto `qTape` by draining `r2 = List.replicate t true`. -/
private def qDrainR2True : OracleMachine :=
  .whileNonEmpty 2 (.seq (.qPush true) (.pop 2))

private theorem runSteps_qDrainR2True (O : DecisionProblem) (t : ℕ)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr2 : regs 2 = List.replicate t true) :
    ∃ k ≤ 6 * t + 2,
      runSteps O k (.running qDrainR2True cs regs q) =
        .running .skip cs (Function.update regs 2 []) (q ++ List.replicate t true) := by
  induction t generalizing regs q with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [List.replicate_zero, List.append_nil, qDrainR2True, runSteps, step, hr2]
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [Function.update, hr2]
  | succ t ih =>
      have hr2' : regs 2 = true :: List.replicate t true := by
        simpa [List.replicate_succ] using hr2
      let regs1 := Function.update regs 2 (List.replicate t true)
      have hstep6 : runSteps O 6 (.running qDrainR2True cs regs q) =
          .running qDrainR2True cs regs1 (q ++ [true]) := by
        simp [qDrainR2True, runSteps, step, hr2', regs1]
      obtain ⟨k', hk', hrun'⟩ := ih regs1 (q ++ [true]) (by simp [regs1])
      refine ⟨6 + k', by omega, ?_⟩
      rw [runSteps_add, hstep6, hrun', List.append_assoc]
      have hrep : [true] ++ List.replicate t true = List.replicate (t + 1) true := by
        simp [List.replicate_succ]
      simp [regs1, hrep]

/-- Assemble `encodeCollapseQuery e x t` onto `qTape` (given `r0 = x`, `r2 = replicate t true`)
and halt returning `O (encodeCollapseQuery e x t)`. -/
private def buildAndQueryCollapseProg (e : ℕ) : OracleMachine :=
  .seq .qClear
    (.seq (qPushNTrue e)
      (.seq (.qPush false)
        (.seq qAppendPrefixFromR0
          (.seq (.qPush true)
            (.seq qDrainR2True
              (.queryBranch (.halt false) (.halt true)))))))

private theorem runSteps_buildAndQueryCollapseProg (O : DecisionProblem) (e : ℕ) (x : List Bool)
    (t : ℕ) (regs : Reg → List Bool) (q0 : List Bool)
    (hr0 : regs 0 = x) (hr2 : regs 2 = List.replicate t true) :
    ∃ k ≤ 9 * x.length + 6 * t + 3 * e + 30,
      runSteps O k (.running (buildAndQueryCollapseProg e) [] regs q0) =
        .halted (O (encodeCollapseQuery e x t)) := by
  let m6 : OracleMachine := .queryBranch (.halt false) (.halt true)
  let m5 : OracleMachine := .seq qDrainR2True m6
  let m4 : OracleMachine := .seq (.qPush true) m5
  let m3 : OracleMachine := .seq qAppendPrefixFromR0 m4
  let m2 : OracleMachine := .seq (.qPush false) m3
  let m1 : OracleMachine := .seq (qPushNTrue e) m2
  have h_clear : runSteps O 1 (.running .qClear [m1] regs q0) =
      .running .skip [m1] regs [] := rfl
  obtain ⟨k_e, hk_e, h_e⟩ := runSteps_qPushNTrue O e [m2] regs []
  have h_false : runSteps O 1
      (.running (.qPush false) [m3] regs ([] ++ List.replicate e true)) =
      .running .skip [m3] regs (List.replicate e true ++ [false]) := by
    simp [runSteps, step]
  obtain ⟨k_x, hk_x, h_x⟩ := runSteps_qAppendPrefixFromR0 O x [m4] regs
    (List.replicate e true ++ [false]) hr0
  let regsX := Function.update regs 0 []
  have h_true : runSteps O 1
      (.running (.qPush true) [m5] regsX (List.replicate e true ++ [false] ++ encodePrefix x)) =
      .running .skip [m5] regsX (List.replicate e true ++ [false] ++ encodePrefix x ++ [true]) :=
    rfl
  have hr2X : regsX 2 = List.replicate t true := by simp [regsX, hr2]
  obtain ⟨k_t, hk_t, h_t⟩ := runSteps_qDrainR2True O t [m6] regsX
    (List.replicate e true ++ [false] ++ encodePrefix x ++ [true]) hr2X
  have hqeq : (List.replicate e true ++ [false] ++ encodePrefix x ++ [true]) ++
      List.replicate t true = encodeCollapseQuery e x t := by
    simp [encodeCollapseQuery, List.replicate_succ, List.append_assoc]
  rw [hqeq] at h_t
  have h_q : runSteps O 2
      (.running m6 [] (Function.update regsX 2 []) (encodeCollapseQuery e x t)) =
      .halted (O (encodeCollapseQuery e x t)) := by
    by_cases ho : O (encodeCollapseQuery e x t) <;> simp [m6, runSteps, step, ho]
  have s5 := runSteps_seq_halted h_t h_q
  have s4 := runSteps_seq_halted h_true s5
  have s3 := runSteps_seq_halted h_x s4
  have s2 := runSteps_seq_halted h_false s3
  have s1 := runSteps_seq_halted h_e s2
  have s0 := runSteps_seq_halted h_clear s1
  refine ⟨_, ?_, s0⟩
  omega

/-- Deterministic decider for an `OracleNP collapseOracle` language with verifier `(e, p)`. -/
private noncomputable def collapseDeciderProg (e : ℕ) (p : Polynomial ℕ) : OracleMachine :=
  .seq copyLenToR1Prog
    (.seq (hornerProg ((List.range (p.natDegree + 1)).map p.coeff))
      (buildAndQueryCollapseProg e))

/-- **Relativization Barrier, Collapse Half**: relative to the explicit computable self-encoding
oracle `collapseOracle`, deterministic and nondeterministic polynomial time coincide. -/
theorem OracleP_collapseOracle_eq_OracleNP :
    OracleP collapseOracle = OracleNP collapseOracle := by
  apply Set.Subset.antisymm (OracleP_subset_OracleNP collapseOracle)
  intro L ⟨e, p, hp⟩
  let coeffs := (List.range (p.natDegree + 1)).map p.coeff
  let M_dec := collapseDeciderProg e p
  let e_dec := encodeMachine M_dec
  let q_bound : Polynomial ℕ :=
    hornerBoundPoly coeffs + Polynomial.C 6 * p +
      Polynomial.C 24 * Polynomial.X + Polynomial.C (3 * e + 50)
  refine ⟨e_dec, q_bound, ?_⟩
  intro x
  let m_rest : OracleMachine := .seq (hornerProg coeffs) (buildAndQueryCollapseProg e)
  obtain ⟨k1, hk1, h1⟩ := runSteps_copyLenToR1Prog collapseOracle x [m_rest]
  let regs1 := Function.update (initRegs x) 1 (List.replicate x.length true)
  obtain ⟨k2, hk2, h2⟩ := runSteps_hornerProg collapseOracle coeffs x.length
    [buildAndQueryCollapseProg e] regs1 []
    (by simp [regs1])
    (by simp [regs1, initRegs])
    (by simp [regs1, initRegs])
  let regs2 := Function.update regs1 2 (List.replicate (hornerVal coeffs x.length) true)
  have hval : hornerVal coeffs x.length = p.eval x.length := hornerVal_polyCoeffs p x.length
  obtain ⟨k3, hk3, h3⟩ := runSteps_buildAndQueryCollapseProg collapseOracle e x (p.eval x.length)
    regs2 []
    (by simp [regs2, regs1, initRegs, Function.update])
    (by simp [regs2, hval])
  have s23 := runSteps_seq_halted h2 h3
  have s123 := runSteps_seq_halted h1 s23
  have htot_le : 1 + k1 + 1 + (1 + k2 + 1 + k3) ≤ q_bound.eval x.length := by
    simp only [q_bound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  have hhalted : evalOracle e_dec collapseOracle (1 + k1 + 1 + (1 + k2 + 1 + k3)) x =
      some (collapseOracle (encodeCollapseQuery e x (p.eval x.length))) := by
    unfold evalOracle
    simp only [e_dec, decodeMachine_encodeMachine, initConfig, M_dec, collapseDeciderProg]
    rw [s123]
    rfl
  have hmono := evalOracle_mono hhalted htot_le
  rw [hmono]
  congr 1
  symm
  apply Bool.eq_iff_iff.mpr
  rw [collapseOracle_encodeCollapseQuery, ← hp x]

/-- There exists an oracle `A` relative to which `OracleP A = OracleNP A`. -/
theorem exists_oracle_OracleP_eq_OracleNP :
    ∃ A : DecisionProblem, OracleP A = OracleNP A :=
  ⟨collapseOracle, OracleP_collapseOracle_eq_OracleNP⟩

/-! ## 5. Separating Oracle Construction (`OracleP B ≠ OracleNP B`) -/

/-- Computable unary length-membership language `unaryLang B x = true` iff there exists a
bitstring `w` of length `x.length` with `B w = true`. -/
def unaryLang (B : DecisionProblem) (x : List Bool) : Bool :=
  (bitstringsOfLen x.length).any B

/-- Characterization of acceptance for `unaryLang B`. -/
theorem unaryLang_eq_true_iff (B : DecisionProblem) (x : List Bool) :
    unaryLang B x = true ↔ ∃ w : List Bool, w.length = x.length ∧ B w = true := by
  simp only [unaryLang, List.any_eq_true, mem_bitstringsOfLen]

/-- Characterization of rejection for `unaryLang B`. -/
theorem unaryLang_eq_false_iff (B : DecisionProblem) (x : List Bool) :
    unaryLang B x = false ↔ ∀ w : List Bool, w.length = x.length → B w = false := by
  simp only [unaryLang, List.any_eq_false, mem_bitstringsOfLen, Bool.not_eq_true]

/-- Prefix-scanning body pushing `true` onto `r1` for each bit of `x` in `encodePrefix x ++ w`. -/
private def countPrefixLoopBody : OracleMachine :=
  .branchHead 0
    (.clear 2)
    (.seq (.pop 0) (.clear 2))
    (.seq (.pop 0) (.seq (.push 1 true) (.pop 0)))

private theorem runSteps_countPrefixLoop (O : DecisionProblem) (x w acc1 : List Bool)
    (cs : List OracleMachine) (regs : Reg → List Bool) (q : List Bool)
    (hr0 : regs 0 = encodePrefix x ++ w) (hr1 : regs 1 = acc1) (hr2 : regs 2 = [true]) :
    ∃ k ≤ 10 * x.length + 8,
      runSteps O k (.running (.whileNonEmpty 2 countPrefixLoopBody) cs regs q) =
        .running .skip cs
          (Function.update (Function.update (Function.update regs 0 w)
            1 (List.replicate x.length true ++ acc1)) 2 []) q := by
  induction x generalizing acc1 regs with
  | nil =>
      refine ⟨8, by omega, ?_⟩
      have h0 : regs 0 = false :: w := by simpa [encodePrefix] using hr0
      simp only [runSteps, step, hr2, countPrefixLoopBody, h0, List.length_nil,
        List.replicate_zero, List.nil_append, List.tail_cons, Function.update_self]
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [Function.update, hr1]
  | cons b bs ih =>
      have h0 : regs 0 = true :: b :: (encodePrefix bs ++ w) := by
        simpa [encodePrefix] using hr0
      let regsA := Function.update regs 0 (b :: (encodePrefix bs ++ w))
      let regsB := Function.update regsA 1 (true :: acc1)
      let regsC := Function.update regsB 0 (encodePrefix bs ++ w)
      have hstep10 : runSteps O 10 (.running (.whileNonEmpty 2 countPrefixLoopBody) cs regs q) =
          .running (.whileNonEmpty 2 countPrefixLoopBody) cs regsC q := by
        simp [runSteps, step, hr2, countPrefixLoopBody, h0, hr1, regsA, regsB, regsC]
      obtain ⟨k', hk', hrun'⟩ := ih (true :: acc1) regsC
        (by simp [regsC])
        (by simp [regsC, regsB, Function.update])
        (by simp [regsC, regsB, regsA, Function.update, hr2])
      refine ⟨10 + k', by simp only [List.length_cons]; omega, ?_⟩
      rw [runSteps_add, hstep10, hrun']
      have hrep := replicate_append_cons bs.length true acc1
      refine running_regs_congr _ _ _ fun r => ?_
      fin_cases r <;> simp [regsC, regsB, regsA, Function.update, hrep]

/-- Lockstep loop verifying `w` has at least `r1.length` bits while copying them onto `qTape`. -/
private def lockstepCopyBody : OracleMachine :=
  .branchHead 0
    (.halt false)
    (.seq (.qPush false) (.seq (.pop 0) (.pop 1)))
    (.seq (.qPush true) (.seq (.pop 0) (.pop 1)))

/-- Verifier machine for `unaryLang B`: unpacks `(x, w)`, checks `w.length = x.length` in
`O(x.length)` steps regardless of `w.length`, copies `w` onto `qTape`, and queries `B w`. -/
private def verifyUnaryLangProg : OracleMachine :=
  .seq (.push 2 true)
    (.seq (.whileNonEmpty 2 countPrefixLoopBody)
      (.seq (.whileNonEmpty 1 lockstepCopyBody)
        (.branchHead 0
          (.queryBranch (.halt false) (.halt true))
          (.halt false)
          (.halt false))))

private theorem runSteps_lockstepAndFinish (B : DecisionProblem) (m : ℕ) (w q : List Bool)
    (regs : Reg → List Bool)
    (hr0 : regs 0 = w) (hr1 : regs 1 = List.replicate m true) :
    ∃ k ≤ 11 * m + 6,
      runSteps B k
        (.running
          (.seq (.whileNonEmpty 1 lockstepCopyBody)
            (.branchHead 0 (.queryBranch (.halt false) (.halt true)) (.halt false) (.halt false)))
          [] regs q) =
        .halted (decide (w.length = m) && B (q ++ w)) := by
  let tailCheck : OracleMachine :=
    .branchHead 0 (.queryBranch (.halt false) (.halt true)) (.halt false) (.halt false)
  induction m generalizing w q regs with
  | zero =>
      have hr1_nil : regs 1 = [] := by simpa using hr1
      cases w with
      | nil =>
          refine ⟨6, by omega, ?_⟩
          by_cases hb : B q <;>
            simp [runSteps, step, hr0, hr1_nil, hb]
      | cons b bs =>
          refine ⟨5, by omega, ?_⟩
          cases b <;> simp [runSteps, step, hr0, hr1_nil]
  | succ m ih =>
      have hr1' : regs 1 = true :: List.replicate m true := by
        simpa [List.replicate_succ] using hr1
      cases w with
      | nil =>
          refine ⟨4, by omega, ?_⟩
          simp [lockstepCopyBody, runSteps, step, hr0, hr1']
      | cons b bs =>
          let regsA := Function.update regs 0 bs
          let regsB := Function.update regsA 1 (List.replicate m true)
          have hiter : runSteps B 11
              (.running (.seq (.whileNonEmpty 1 lockstepCopyBody) tailCheck) [] regs q) =
              .running (.whileNonEmpty 1 lockstepCopyBody) [tailCheck] regsB (q ++ [b]) := by
            cases b <;> simp [lockstepCopyBody, runSteps, step, hr0, hr1', regsA, regsB]
          obtain ⟨k', hk', hrun'⟩ := ih bs (q ++ [b]) regsB
            (by simp [regsB, regsA, Function.update])
            (by simp [regsB])
          cases k' with
          | zero =>
              simp [runSteps] at hrun'
          | succ k'' =>
              have hrun'' : runSteps B k''
                  (.running (.whileNonEmpty 1 lockstepCopyBody) [tailCheck] regsB (q ++ [b])) =
                  .halted (decide (bs.length = m) && B ((q ++ [b]) ++ bs)) := by
                simpa [runSteps, step] using hrun'
              refine ⟨11 + k'', by omega, ?_⟩
              rw [runSteps_add, hiter, hrun'']
              simp [List.append_assoc]

/-- For every oracle `B`, the unary length language `unaryLang B` belongs to `OracleNP B`. -/
theorem unaryLang_mem_OracleNP (B : DecisionProblem) :
    unaryLang B ∈ OracleNP B := by
  let e_LB := encodeMachine verifyUnaryLangProg
  let p_LB : Polynomial ℕ := Polynomial.C 21 * Polynomial.X + Polynomial.C 25
  refine ⟨e_LB, p_LB, ?_⟩
  intro x
  have heval : ∀ w : List Bool,
      evalOracle e_LB B (p_LB.eval x.length) (pair x w) =
        some (decide (w.length = x.length) && B w) := by
    intro w
    let tail2 : OracleMachine := .seq (.whileNonEmpty 1 lockstepCopyBody)
      (.branchHead 0 (.queryBranch (.halt false) (.halt true)) (.halt false) (.halt false))
    let tail1 : OracleMachine := .seq (.whileNonEmpty 2 countPrefixLoopBody) tail2
    let regs0 := Function.update (initRegs (pair x w)) 2 [true]
    have h0 : runSteps B 1 (.running (.push 2 true) [tail1] (initRegs (pair x w)) []) =
        .running .skip [tail1] regs0 [] := rfl
    obtain ⟨k1, hk1, h1⟩ := runSteps_countPrefixLoop B x w [] [tail2] regs0 []
      (by simp [regs0, initRegs, pair])
      (by simp [regs0, initRegs])
      (by simp [regs0])
    let regs1 := Function.update (Function.update (Function.update regs0 0 w)
      1 (List.replicate x.length true ++ [])) 2 []
    obtain ⟨k2, hk2, h2⟩ := runSteps_lockstepAndFinish B x.length w [] regs1
      (by simp [regs1, Function.update])
      (by simp [regs1, Function.update])
    have s12 := runSteps_seq_halted h1 h2
    have s012 := runSteps_seq_halted h0 s12
    have hhalted : evalOracle e_LB B (1 + 1 + 1 + (1 + k1 + 1 + k2)) (pair x w) =
        some (decide (w.length = x.length) && B w) := by
      unfold evalOracle
      simp only [e_LB, decodeMachine_encodeMachine, initConfig, verifyUnaryLangProg]
      rw [s012]
      simp [configOutput]
    have hle : 1 + 1 + 1 + (1 + k1 + 1 + k2) ≤ p_LB.eval x.length := by
      simp only [p_LB, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      omega
    exact evalOracle_mono hhalted hle
  rw [unaryLang_eq_true_iff]
  constructor
  · rintro ⟨w, hwlen, hbw⟩
    refine ⟨w, ?_, ?_⟩
    · simp only [p_LB, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      omega
    · rw [heval w]
      simp [hwlen, hbw]
  · rintro ⟨w, _, hacc⟩
    rw [heval w] at hacc
    simp only [Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at hacc
    exact ⟨w, hacc.1, hacc.2⟩

/-! ### Computable Enumeration of Machine-Polynomial Pairs and Stage-by-Stage Diagonalization -/

/-- Computable Gödel encoding of `List ℕ`. -/
private def encodeNatList : List ℕ → ℕ
  | [] => 0
  | h :: t => Nat.pair h (encodeNatList t) + 1

/-- Fuel-bounded computable decoder for `List ℕ`. -/
private def decodeNatListAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, code + 1 =>
      let (h, t) := Nat.unpair code
      h :: decodeNatListAux fuel t

private theorem decodeNatListAux_encode (l : List ℕ) :
    ∀ fuel : ℕ, encodeNatList l < fuel → decodeNatListAux fuel (encodeNatList l) = l := by
  induction l with
  | nil =>
      intro fuel hlt
      cases fuel <;> simp [encodeNatList, decodeNatListAux] at hlt ⊢
  | cons h t ih =>
      intro fuel hlt
      cases fuel with
      | zero => omega
      | succ f =>
          simp only [encodeNatList] at hlt
          have ht : encodeNatList t < f := by
            have := Nat.right_le_pair h (encodeNatList t)
            omega
          simp [encodeNatList, decodeNatListAux, ih f ht]

/-- Computable enumeration `ℕ → ℕ × List ℕ` covering all pairs `(e, coeffs)`. -/
private def enumMachineCoeffs (k : ℕ) : ℕ × List ℕ :=
  let (e, c) := Nat.unpair k
  (e, decodeNatListAux (c + 1) c)

private theorem enumMachineCoeffs_surjective (e : ℕ) (cs : List ℕ) :
    ∃ k : ℕ, enumMachineCoeffs k = (e, cs) := by
  let c := encodeNatList cs
  refine ⟨Nat.pair e c, ?_⟩
  simp [enumMachineCoeffs, c, decodeNatListAux_encode cs (c + 1) (Nat.lt_succ_self _)]

/-! ### Constructive Exponential Domination `hornerVal cs n < 2^n` -/

private theorem two_mul_le_two_pow : ∀ b : ℕ, 2 ≤ b → 2 * b ≤ 2 ^ b
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by decide
  | b + 3, _ => by
      have ih := two_mul_le_two_pow (b + 2) (by omega)
      have hpos : 2 ≤ 2 ^ (b + 2) := by
        have := Nat.lt_two_pow_self (n := b + 2)
        omega
      have hp : 2 ^ (b + 3) = 2 ^ (b + 2) * 2 := Nat.pow_succ 2 (b + 2)
      omega

private theorem hornerVal_le_sum_mul_pow (cs : List ℕ) {n : ℕ} (hn : 1 ≤ n) :
    hornerVal cs n ≤ cs.sum * n ^ cs.length := by
  induction cs with
  | nil => simp [hornerVal]
  | cons c rest ih =>
      simp only [hornerVal, List.sum_cons, List.length_cons]
      have hpow_pos : 1 ≤ n ^ (rest.length + 1) := Nat.one_le_pow _ _ hn
      have h1 : c ≤ c * n ^ (rest.length + 1) := Nat.le_mul_of_pos_right c hpow_pos
      have h2 : n * hornerVal rest n ≤ rest.sum * n ^ (rest.length + 1) := by
        calc
          n * hornerVal rest n ≤ n * (rest.sum * n ^ rest.length) := Nat.mul_le_mul_left n ih
          _ = rest.sum * (n ^ rest.length * n) := by ring
          _ = rest.sum * n ^ (rest.length + 1) := by rw [Nat.pow_succ]
      rw [Nat.add_mul]
      exact Nat.add_le_add h1 h2

/-- Explicit closed-form input length `n > M` at which `hornerVal cs n < 2^n`. -/
private def chooseNextLen (cs : List ℕ) (M : ℕ) : ℕ :=
  let b := cs.sum + cs.length + M + 3
  2 ^ (2 ^ b)

private theorem chooseNextLen_gt (cs : List ℕ) (M : ℕ) :
    M < chooseNextLen cs M := by
  unfold chooseNextLen
  dsimp only
  set b := cs.sum + cs.length + M + 3
  have h1 : M < b := by omega
  have h2 : b < 2 ^ b := Nat.lt_two_pow_self
  have h3 : 2 ^ b < 2 ^ (2 ^ b) := Nat.lt_two_pow_self
  exact lt_trans h1 (lt_trans h2 h3)

private theorem chooseNextLen_hornerVal_lt_two_pow (cs : List ℕ) (M : ℕ) :
    hornerVal cs (chooseNextLen cs M) < 2 ^ (chooseNextLen cs M) := by
  unfold chooseNextLen
  dsimp only
  set d := cs.length
  set C := cs.sum
  set b := C + d + M + 3
  set m := 2 ^ b
  set n := 2 ^ m
  have hn1 : 1 ≤ n := Nat.one_le_two_pow
  have hpeval : hornerVal cs n ≤ C * n ^ d := hornerVal_le_sum_mul_pow cs hn1
  have hC : C < 2 ^ C := Nat.lt_two_pow_self
  have hpow_eq : (2 ^ m) ^ d = 2 ^ (m * d) := (Nat.pow_mul 2 m d).symm
  have hCn : C * n ^ d < 2 ^ (C + m * d) := by
    calc
      C * n ^ d < 2 ^ C * n ^ d :=
        Nat.mul_lt_mul_of_pos_right hC (Nat.pow_pos hn1)
      _ = 2 ^ C * 2 ^ (m * d) := by rw [hpow_eq]
      _ = 2 ^ (C + m * d) := (Nat.pow_add 2 C (m * d)).symm
  have hCm : C < m := by
    have hb : C < b := by omega
    exact Nat.lt_trans hb Nat.lt_two_pow_self
  have hd_pow : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
  have hexp_le : C + m * d ≤ n := by
    have step1 : C + m * d ≤ m * (d + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have step2 : m * (d + 1) ≤ 2 ^ (b + d) := by
      calc
        m * (d + 1) ≤ 2 ^ b * 2 ^ d := Nat.mul_le_mul_left (2 ^ b) hd_pow
        _ = 2 ^ (b + d) := (Nat.pow_add 2 b d).symm
    have step3 : b + d ≤ m := by
      have h2b : 2 * b ≤ 2 ^ b := two_mul_le_two_pow b (by omega)
      omega
    have step4 : 2 ^ (b + d) ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by omega) step3
    exact le_trans step1 (le_trans step2 step4)
  exact lt_of_le_of_lt hpeval (lt_of_lt_of_le hCn (Nat.pow_le_pow_right (by omega) hexp_le))

/-- Single stage update of the computable diagonalization:
given `(Bk, boundk)` and stage index `k`, picks `nk = chooseNextLen csk boundk`, runs `ek` on
`1^nk` for `tk = hornerVal csk nk` steps against `Bk`, and if `ek` fails to accept, inserts the
first unqueried witness `w` of length `nk`. -/
private def diagStep (k : ℕ) (st : Finset (List Bool) × ℕ) : Finset (List Bool) × ℕ :=
  let Bk := st.1
  let boundk := st.2
  let (ek, csk) := enumMachineCoeffs k
  let nk := chooseNextLen csk boundk
  let tk := hornerVal csk nk
  let xk := List.replicate nk true
  let Bfn : DecisionProblem := fun s => decide (s ∈ Bk)
  let Qk := queriedSet ek Bfn tk xk
  let cands := (bitstringsOfLen nk).filter fun s => !decide (s ∈ Qk)
  let Bk' :=
    if evalOracle ek Bfn tk xk == some true then Bk
    else match cands with
      | w :: _ => insert w Bk
      | [] => Bk
  (Bk', max nk tk + 1)

/-- Cumulative stage `(B_k, bound_k)` of the diagonalization. -/
private def diagStage : ℕ → Finset (List Bool) × ℕ
  | 0 => (∅, 0)
  | k + 1 => diagStep k (diagStage k)

private theorem diagStage_bound_strictMono (k : ℕ) :
    (diagStage k).2 < (diagStage (k + 1)).2 := by
  simp only [diagStage, diagStep]
  have hgt := chooseNextLen_gt (enumMachineCoeffs k).2 (diagStage k).2
  omega

private theorem diagStage_bound_mono {a b : ℕ} (h : a ≤ b) :
    (diagStage a).2 ≤ (diagStage b).2 := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst ha; exact le_rfl
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · exact le_trans (ih (Nat.le_of_lt_succ hlt))
          (Nat.le_of_lt (diagStage_bound_strictMono b))

private theorem diagStage_idx_le_bound (k : ℕ) :
    k ≤ (diagStage k).2 := by
  induction k with
  | zero => simp [diagStage]
  | succ k ih =>
      have hlt := diagStage_bound_strictMono k
      omega

private theorem diagStage_mem_length_lt (k : ℕ) :
    ∀ s ∈ (diagStage k).1, s.length < (diagStage k).2 := by
  induction k with
  | zero => simp [diagStage]
  | succ k ih =>
      intro s hs
      simp only [diagStage, diagStep] at hs ⊢
      set st := diagStage k
      set ep := enumMachineCoeffs k
      set nk := chooseNextLen ep.2 st.2
      set tk := hornerVal ep.2 nk
      have hbound_lt : st.2 < nk := chooseNextLen_gt ep.2 st.2
      split_ifs at hs with hev
      · have hslt := ih s hs
        omega
      · split at hs
        · simp only [Finset.mem_insert] at hs
          rcases hs with rfl | hold
          · rename_i w ws hcw
            have hwmem : s ∈ (bitstringsOfLen nk).filter
                (fun z => !decide (z ∈ queriedSet ep.1 (fun u => decide (u ∈ st.1)) tk
                  (List.replicate nk true))) := by
              rw [hcw]; simp
            simp only [List.mem_filter, mem_bitstringsOfLen] at hwmem
            omega
          · have hslt := ih s hold
            omega
        · have hslt := ih s hs
          omega

private theorem diagStage_stabilizes {m r : ℕ} {s : List Bool}
    (hs : s.length < (diagStage m).2) (hmr : m ≤ r) :
    (s ∈ (diagStage r).1) ↔ (s ∈ (diagStage m).1) := by
  induction r with
  | zero =>
      have hm0 : m = 0 := by omega
      subst hm0; rfl
  | succ r ih =>
      rcases Nat.eq_or_lt_of_le hmr with rfl | hlt
      · rfl
      · have hle : m ≤ r := Nat.le_of_lt_succ hlt
        have hsr : s.length < (diagStage r).2 :=
          lt_of_lt_of_le hs (diagStage_bound_mono hle)
        have hstep : (s ∈ (diagStage (r + 1)).1) ↔ (s ∈ (diagStage r).1) := by
          simp only [diagStage, diagStep]
          set st := diagStage r
          set ep := enumMachineCoeffs r
          set nk := chooseNextLen ep.2 st.2
          have hnk : st.2 < nk := chooseNextLen_gt ep.2 st.2
          split_ifs with hev
          · rfl
          · split
            · rename_i w ws hcw
              have hwlen : w.length = nk := by
                have hwmem : w ∈ w :: ws := by simp
                rw [← hcw] at hwmem
                exact mem_bitstringsOfLen.mp (List.mem_filter.mp hwmem).1
              have hne : s ≠ w := by
                intro heq
                subst heq
                omega
              simp [hne]
            · rfl
        rw [hstep, ih hle]

/-- Explicit computable stage-diagonalized oracle separating `OracleP` and `OracleNP`. -/
def sepOracle (s : List Bool) : Bool :=
  decide (s ∈ (diagStage (s.length + 1)).1)

private theorem sepOracle_eq_stage {m : ℕ} {s : List Bool}
    (hs : s.length < (diagStage m).2) :
    sepOracle s = decide (s ∈ (diagStage m).1) := by
  unfold sepOracle
  have hs1 : s.length < (diagStage (s.length + 1)).2 := by
    have := diagStage_idx_le_bound (s.length + 1)
    omega
  rcases le_total m (s.length + 1) with hle | hge
  · simp [diagStage_stabilizes hs hle]
  · simp [(diagStage_stabilizes hs1 hge).symm]

/-- Existence of an unqueried bitstring of length `n` whenever `Q.card < 2^n`. -/
private theorem filter_not_mem_bitstringsOfLen_nonempty {n : ℕ} {Q : Finset (List Bool)}
    (hcard : Q.card < 2 ^ n) :
    (bitstringsOfLen n).filter (fun s => !decide (s ∈ Q)) ≠ [] := by
  let S : Finset (List Bool) := (bitstringsOfLen n).toFinset
  have hScard : S.card = 2 ^ n := by
    rw [List.toFinset_card_of_nodup (bitstringsOfLen_nodup n), bitstringsOfLen_length]
  have hdiff_pos : 0 < (S \ Q).card := by
    have := Finset.le_card_sdiff Q S
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hdiff_pos
  rw [Finset.mem_sdiff, List.mem_toFinset] at hw
  intro hemp
  have hwmem : w ∈ (bitstringsOfLen n).filter (fun s => !decide (s ∈ Q)) := by
    simp [hw.1, hw.2]
  rw [hemp] at hwmem
  simp at hwmem

/-- Diagonalization theorem: `unaryLang sepOracle ∉ OracleP sepOracle`. -/
theorem unaryLang_not_mem_OracleP_sepOracle :
    unaryLang sepOracle ∉ OracleP sepOracle := by
  rintro ⟨e, p, hp⟩
  let cs := (List.range (p.natDegree + 1)).map p.coeff
  obtain ⟨k, hk⟩ := enumMachineCoeffs_surjective e cs
  let st := diagStage k
  let Bk := st.1
  let boundk := st.2
  let nk := chooseNextLen cs boundk
  let tk := hornerVal cs nk
  let xk := List.replicate nk true
  let Bfn : DecisionProblem := fun s => decide (s ∈ Bk)
  let Qk := queriedSet e Bfn tk xk
  have htk_eq : tk = p.eval nk := hornerVal_polyCoeffs p nk
  have hboundk_lt_nk : boundk < nk := chooseNextLen_gt cs boundk
  have htk_lt_pow : tk < 2 ^ nk := chooseNextLen_hornerVal_lt_two_pow cs boundk
  have hQk_card : Qk.card < 2 ^ nk := lt_of_le_of_lt (queriedSet_card_le e Bfn tk xk) htk_lt_pow
  have hcands_ne : (bitstringsOfLen nk).filter (fun s => !decide (s ∈ Qk)) ≠ [] :=
    filter_not_mem_bitstringsOfLen_nonempty hQk_card
  have hstage_succ : diagStage (k + 1) =
      ((if evalOracle e Bfn tk xk == some true then Bk
        else match (bitstringsOfLen nk).filter (fun s => !decide (s ∈ Qk)) with
          | w :: _ => insert w Bk
          | [] => Bk),
       max nk tk + 1) := by
    simp [diagStage, diagStep, hk, st, Bk, boundk, nk, tk, xk, Bfn, Qk]
  have hbound_succ : (diagStage (k + 1)).2 = max nk tk + 1 := by
    rw [hstage_succ]
  have hagree : ∀ q ∈ Qk, Bfn q = sepOracle q := by
    intro q hq
    have hqlen : q.length < tk := queriedSet_length_lt hq
    have hqbound : q.length < (diagStage (k + 1)).2 := by rw [hbound_succ]; omega
    rw [sepOracle_eq_stage hqbound, hstage_succ]
    simp only
    split_ifs with hev
    · rfl
    · cases hfilt : (bitstringsOfLen nk).filter (fun s => !decide (s ∈ Qk)) with
      | nil => exact absurd hfilt hcands_ne
      | cons w ws =>
          have hwnot : w ∉ Qk := by
            have hwmem : w ∈ (bitstringsOfLen nk).filter (fun s => !decide (s ∈ Qk)) := by
              rw [hfilt]; simp
            simpa using (List.mem_filter.mp hwmem).2
          have hqne : q ≠ w := fun heq => hwnot (heq ▸ hq)
          simp [Bfn, hqne]
  have huse : evalOracle e sepOracle tk xk = evalOracle e Bfn tk xk :=
    (evalOracle_use_principle hagree).symm
  have hxlen : xk.length = nk := by simp [xk]
  have hdec := hp xk
  rw [hxlen, ← htk_eq] at hdec
  change evalOracle e sepOracle tk xk = some (unaryLang sepOracle xk) at hdec
  rw [huse] at hdec
  by_cases hev : evalOracle e Bfn tk xk = some true
  · have hfalse : unaryLang sepOracle xk = false := by
      rw [unaryLang_eq_false_iff]
      intro w hwlen
      rw [hxlen] at hwlen
      apply Bool.eq_false_iff.mpr
      intro hbw
      have hwbound : w.length < (diagStage (k + 1)).2 := by rw [hbound_succ]; omega
      rw [sepOracle_eq_stage hwbound, hstage_succ] at hbw
      simp only [hev, beq_self_eq_true, ↓reduceIte, decide_eq_true_eq] at hbw
      have hwlt : w.length < boundk := diagStage_mem_length_lt k w hbw
      omega
    rw [hev, hfalse] at hdec
    simp at hdec
  · have hbeq : (evalOracle e Bfn tk xk == some true) = false :=
      beq_false_of_ne hev
    cases hfilt : (bitstringsOfLen nk).filter (fun s => !decide (s ∈ Qk)) with
    | nil => exact absurd hfilt hcands_ne
    | cons w ws =>
        have hwmem : w ∈ (bitstringsOfLen nk).filter (fun s => !decide (s ∈ Qk)) := by
          rw [hfilt]; simp
        have hwlen : w.length = nk := mem_bitstringsOfLen.mp (List.mem_filter.mp hwmem).1
        have hwbound : w.length < (diagStage (k + 1)).2 := by rw [hbound_succ]; omega
        have hbw : sepOracle w = true := by
          rw [sepOracle_eq_stage hwbound, hstage_succ]
          simp [hbeq, hfilt]
        have htrue : unaryLang sepOracle xk = true := by
          rw [unaryLang_eq_true_iff, hxlen]
          exact ⟨w, hwlen, hbw⟩
        rw [htrue] at hdec
        exact hev hdec

/-- Relative to `sepOracle`, `OracleP` is strictly contained in `OracleNP`. -/
theorem OracleP_sepOracle_ssubset_OracleNP :
    OracleP sepOracle ⊂ OracleNP sepOracle :=
  Set.ssubset_iff_subset_ne.mpr
    ⟨OracleP_subset_OracleNP sepOracle, fun heq =>
      unaryLang_not_mem_OracleP_sepOracle (heq ▸ unaryLang_mem_OracleNP sepOracle)⟩

/-- Relative to `sepOracle`, `OracleP` and `OracleNP` are distinct. -/
theorem OracleP_sepOracle_ne_OracleNP :
    OracleP sepOracle ≠ OracleNP sepOracle :=
  OracleP_sepOracle_ssubset_OracleNP.ne

/-- **Relativization Barrier, Separation Half**: there exists an explicit computable oracle `B`
relative to which `OracleP B ≠ OracleNP B`. -/
theorem exists_oracle_OracleP_ne_OracleNP :
    ∃ B : DecisionProblem, OracleP B ≠ OracleNP B :=
  ⟨sepOracle, OracleP_sepOracle_ne_OracleNP⟩

/-- **Complete Relativization Barrier**: there exist oracles relative to which
`OracleP A = OracleNP A` and oracles relative to which `OracleP B ≠ OracleNP B`. -/
theorem relativization_barrier :
    (∃ A : DecisionProblem, OracleP A = OracleNP A) ∧
    (∃ B : DecisionProblem, OracleP B ≠ OracleNP B) :=
  ⟨exists_oracle_OracleP_eq_OracleNP, exists_oracle_OracleP_ne_OracleNP⟩

end Cslib.Complexity.Barriers.Relativization
