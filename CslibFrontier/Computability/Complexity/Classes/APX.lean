/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Complexity.Reduction.LinearApproximation
public import CslibFrontier.Computability.Complexity.Problems.SAT

import Mathlib.Tactic.Linarith
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.PCP.Approximation.Johnson
import CslibFrontier.Computability.PCP.Approximation.MaxThreeSAT.Approx
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# The Approximation Class `APX`, `PTAS`-Reductions, and Objective `NP`-Hardness

This module extends `Cslib.Complexity.NPOptimizationProblem` and `Cslib.Complexity.LReduction` with
constant-factor polynomial-time approximability (`InAPX`), `PTAS`-reductions (`PTASReducible`),
`APX`-hardness and `APX`-completeness (`APXHard`, `APXComplete`), and binary-threshold objective
`NP`-hardness (`OptUndergraph`, `IsNPHardObjective`), all proved under standard Lean axioms.

Building on Johnson's `1/2`-approximation algorithm and the PCP-based constant-factor
inapproximability of `MAX-3SAT` from `CslibFrontier`, we construct a canonical
`NPOptimizationProblem` formulation `maxThreeSATNPO`, prove `maxThreeSATNPO ∈ APX`, and prove that
any `APX`-hard problem admitting a `PTAS` implies `P = NP`.

## Main definitions

* `Cslib.Complexity.IsConstApprox`, `Cslib.Complexity.InAPX`: constant-factor approximation and
  the class `APX`.
* `Cslib.Complexity.PTASReducible`: `PTAS`-reductions between `NPO` problems.
* `Cslib.Complexity.APXHard`, `Cslib.Complexity.APXComplete`: `APX`-hardness and completeness.
* `Cslib.Complexity.OptUndergraph`, `Cslib.Complexity.IsNPHardObjective`: binary-threshold
  undergraph and objective `NP`-hardness.
* `Cslib.Complexity.maxThreeSATNPO`: canonical `NPO` formulation of `MAX-3SAT`.

## Main results

* `Cslib.Complexity.ptas_inAPX`: `PTAS ⊆ APX`.
* `Cslib.Complexity.ptasReducible_of_lReduction`: every `LReduction` induces a `PTAS`-reduction.
* `Cslib.Complexity.PTASReducible.ptas`, `Cslib.Complexity.APXHard.trans`: transfers.
* `Cslib.Complexity.inAPX_maxThreeSATNPO`: `MAX-3SAT ∈ APX` via Johnson's algorithm.
* `Cslib.Complexity.P_eq_NP_of_apxHard_of_ptas`: any `APX`-hard problem with a `PTAS` collapses
  `P = NP`.
* `Cslib.Complexity.P_eq_NP_of_isNPHardObjective_of_computableInPolyTime`: exact objective
  intractability.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-! ### Constant-Factor Approximation (`APX`) and `PTAS`-Reductions -/

/-- A feasible solution `b` for instance `a` achieves constant performance factor `r` (`1 ≤ r`)
without division: `value ≤ r * other` for minimization and `other ≤ r * value` for maximization. -/
def IsConstApprox {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (problem : NPOptimizationProblem encI encS) (r : ℕ) (a : α) (b : β) : Prop :=
  problem.Feasible a b ∧ ∀ other, problem.Feasible a other →
    match problem.goal with
    | .minimize => problem.value (a, b) ≤ r * problem.value (a, other)
    | .maximize => problem.value (a, other) ≤ r * problem.value (a, b)

/-- Characterization of `IsConstApprox`. -/
lemma isConstApprox_iff {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (problem : NPOptimizationProblem encI encS) (r : ℕ) (a : α) (b : β) :
    IsConstApprox problem r a b ↔
      problem.Feasible a b ∧ ∀ other, problem.Feasible a other →
        match problem.goal with
        | .minimize => problem.value (a, b) ≤ r * problem.value (a, other)
        | .maximize => problem.value (a, other) ≤ r * problem.value (a, b) := Iff.rfl

/-- Constant-factor polynomial-time approximability class `APX`. -/
def InAPX {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (problem : NPOptimizationProblem encI encS) : Prop :=
  ∃ r : ℕ, 1 ≤ r ∧ ∃ solve : α → β,
    ComputableInPolyTime solve encI encS ∧ ∀ a, IsConstApprox problem r a (solve a)

/-- Characterization of `InAPX`. -/
lemma inAPX_iff {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (problem : NPOptimizationProblem encI encS) :
    InAPX problem ↔
      ∃ r : ℕ, 1 ≤ r ∧ ∃ solve : α → β,
        ComputableInPolyTime solve encI encS ∧ ∀ a, IsConstApprox problem r a (solve a) := Iff.rfl

/-- Every `NPO` optimization problem admitting a `PTAS` belongs to `APX` (factor `2`). -/
theorem ptas_inAPX {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    {problem : NPOptimizationProblem encI encS} (h : problem.PTAS) : InAPX problem := by
  obtain ⟨solve, hsolve, happrox⟩ := h 2 (by decide)
  refine ⟨2, by decide, solve, hsolve, fun a ↦ ?_⟩
  obtain ⟨hfeas, hbound⟩ := happrox a
  refine ⟨hfeas, fun other hother ↦ ?_⟩
  have hb := hbound other hother
  cases hgoal : problem.goal <;> simp only [hgoal] at hb ⊢ <;> omega

/-- Polynomial-time approximation-scheme (`PTAS`) reducibility between `NPO` problems. -/
def PTASReducible {α₁ β₁ α₂ β₂ : Type}
    {encI₁ : α₁ ↪ List Bool} {encS₁ : β₁ ↪ List Bool}
    {encI₂ : α₂ ↪ List Bool} {encS₂ : β₂ ↪ List Bool}
    (A : NPOptimizationProblem encI₁ encS₁) (B : NPOptimizationProblem encI₂ encS₂) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ (m : ℕ) (f : α₁ → α₂) (g : α₁ × β₂ → β₁),
      0 < m ∧
      ComputableInPolyTime f encI₁ encI₂ ∧
      ComputableInPolyTime g (encPair encI₁ encS₂) encS₁ ∧
      ∀ a b, B.IsApproximate m (f a) b → A.IsApproximate k a (g (a, b))

/-- Characterization of `PTASReducible`. -/
lemma ptasReducible_iff {α₁ β₁ α₂ β₂ : Type}
    {encI₁ : α₁ ↪ List Bool} {encS₁ : β₁ ↪ List Bool}
    {encI₂ : α₂ ↪ List Bool} {encS₂ : β₂ ↪ List Bool}
    (A : NPOptimizationProblem encI₁ encS₁) (B : NPOptimizationProblem encI₂ encS₂) :
    PTASReducible A B ↔
      ∀ k : ℕ, 0 < k →
        ∃ (m : ℕ) (f : α₁ → α₂) (g : α₁ × β₂ → β₁),
          0 < m ∧
          ComputableInPolyTime f encI₁ encI₂ ∧
          ComputableInPolyTime g (encPair encI₁ encS₂) encS₁ ∧
          ∀ a b, B.IsApproximate m (f a) b → A.IsApproximate k a (g (a, b)) := Iff.rfl

/-- Reflexivity of `PTASReducible`. -/
theorem PTASReducible.refl {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (A : NPOptimizationProblem encI encS) : PTASReducible A A :=
  fun k hk ↦ ⟨k, id, Prod.snd, hk, id', snd encI encS, fun _ _ h ↦ h⟩

/-- Transitivity of `PTASReducible`. -/
theorem PTASReducible.trans {α₁ β₁ α₂ β₂ α₃ β₃ : Type}
    {encI₁ : α₁ ↪ List Bool} {encS₁ : β₁ ↪ List Bool}
    {encI₂ : α₂ ↪ List Bool} {encS₂ : β₂ ↪ List Bool}
    {encI₃ : α₃ ↪ List Bool} {encS₃ : β₃ ↪ List Bool}
    {A : NPOptimizationProblem encI₁ encS₁}
    {B : NPOptimizationProblem encI₂ encS₂}
    {C : NPOptimizationProblem encI₃ encS₃}
    (hAB : PTASReducible A B) (hBC : PTASReducible B C) : PTASReducible A C := by
  intro k hk
  obtain ⟨m₁, f₁, g₁, hm₁, hf₁, hg₁, hpres₁⟩ := hAB k hk
  obtain ⟨m₂, f₂, g₂, hm₂, hf₂, hg₂, hpres₂⟩ := hBC m₁ hm₁
  have hfst := fst encI₁ encS₃
  have hsnd := snd encI₁ encS₃
  refine ⟨m₂, f₂ ∘ f₁, fun p ↦ g₁ (p.1, g₂ (f₁ p.1, p.2)), hm₂, hf₂.comp hf₁,
    hg₁.comp (hfst.prod (hg₂.comp ((hf₁.comp hfst).prod hsnd))), fun a b hb ↦ ?_⟩
  exact hpres₁ a (g₂ (f₁ a, b)) (hpres₂ (f₁ a) b hb)

/-- Downward transfer of `PTAS` along a `PTAS`-reduction. -/
theorem PTASReducible.ptas {α₁ β₁ α₂ β₂ : Type}
    {encI₁ : α₁ ↪ List Bool} {encS₁ : β₁ ↪ List Bool}
    {encI₂ : α₂ ↪ List Bool} {encS₂ : β₂ ↪ List Bool}
    {A : NPOptimizationProblem encI₁ encS₁}
    {B : NPOptimizationProblem encI₂ encS₂}
    (hAB : PTASReducible A B) (hB : B.PTAS) : A.PTAS := by
  intro k hk
  obtain ⟨m, f, g, hm, hf, hg, hpres⟩ := hAB k hk
  obtain ⟨solve, hsolve, hgood⟩ := hB m hm
  exact ⟨fun a ↦ g (a, solve (f a)), hg.comp (id'.prod (hsolve.comp hf)),
    fun a ↦ hpres a (solve (f a)) (hgood (f a))⟩

/-- Every `Cslib.Complexity.LReduction` induces a `PTAS`-reduction. -/
theorem ptasReducible_of_lReduction {α₁ β₁ α₂ β₂ : Type}
    {encI₁ : α₁ ↪ List Bool} {encS₁ : β₁ ↪ List Bool}
    {encI₂ : α₂ ↪ List Bool} {encS₂ : β₂ ↪ List Bool}
    {A : NPOptimizationProblem encI₁ encS₁}
    {B : NPOptimizationProblem encI₂ encS₂}
    (r : LReduction A B) : PTASReducible A B := fun k hk ↦
  ⟨r.optimumFactor * (k * r.errorFactor), r.mapInstance, r.recover,
    Nat.mul_pos r.optimumFactor_pos (Nat.mul_pos hk r.errorFactor_pos),
    r.computableInPolyTime_mapInstance, r.computableInPolyTime_recover,
    fun _ _ hb ↦ r.isApproximate_recover hb⟩

/-- `APX`-hardness: every `NPO` problem in `APX` `PTAS`-reduces to `B`. -/
def APXHard {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (B : NPOptimizationProblem encI encS) : Prop :=
  ∀ {α' β' : Type} {encI' : α' ↪ List Bool} {encS' : β' ↪ List Bool}
    (A : NPOptimizationProblem encI' encS'), InAPX A → PTASReducible A B

/-- Characterization of `APXHard`. -/
lemma apxHard_iff {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (B : NPOptimizationProblem encI encS) :
    APXHard B ↔
      ∀ {α' β' : Type} {encI' : α' ↪ List Bool} {encS' : β' ↪ List Bool}
        (A : NPOptimizationProblem encI' encS'), InAPX A → PTASReducible A B := Iff.rfl

/-- Upward transfer of `APXHard` along a `PTAS`-reduction. -/
theorem APXHard.trans {α₁ β₁ α₂ β₂ : Type}
    {encI₁ : α₁ ↪ List Bool} {encS₁ : β₁ ↪ List Bool}
    {encI₂ : α₂ ↪ List Bool} {encS₂ : β₂ ↪ List Bool}
    {A : NPOptimizationProblem encI₁ encS₁}
    {B : NPOptimizationProblem encI₂ encS₂}
    (hA : APXHard A) (hAB : PTASReducible A B) : APXHard B :=
  fun Q hQ ↦ (((apxHard_iff A).mp hA) Q hQ).trans hAB

/-- Upward transfer of `APXHard` along an `LReduction`. -/
theorem APXHard.of_lReduction {α₁ β₁ α₂ β₂ : Type}
    {encI₁ : α₁ ↪ List Bool} {encS₁ : β₁ ↪ List Bool}
    {encI₂ : α₂ ↪ List Bool} {encS₂ : β₂ ↪ List Bool}
    {A : NPOptimizationProblem encI₁ encS₁}
    {B : NPOptimizationProblem encI₂ encS₂}
    (hA : APXHard A) (r : LReduction A B) : APXHard B :=
  hA.trans (ptasReducible_of_lReduction r)

/-- `APX`-completeness: membership in `APX` together with `APX`-hardness. -/
def APXComplete {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (B : NPOptimizationProblem encI encS) : Prop :=
  InAPX B ∧ APXHard B

/-- Characterization of `APXComplete`. -/
lemma apxComplete_iff {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    (B : NPOptimizationProblem encI encS) :
    APXComplete B ↔ InAPX B ∧ APXHard B := Iff.rfl

/-- Upward transfer of `APXComplete` along a `PTAS`-reduction given `InAPX B`. -/
theorem APXComplete.of_ptasReducible {α₁ β₁ α₂ β₂ : Type}
    {encI₁ : α₁ ↪ List Bool} {encS₁ : β₁ ↪ List Bool}
    {encI₂ : α₂ ↪ List Bool} {encS₂ : β₂ ↪ List Bool}
    {A : NPOptimizationProblem encI₁ encS₁}
    {B : NPOptimizationProblem encI₂ encS₂}
    (hA : APXComplete A) (hB : InAPX B) (hAB : PTASReducible A B) : APXComplete B :=
  ⟨hB, APXHard.trans hA.2 hAB⟩

/-- Upward transfer of `APXComplete` along an `LReduction` given `InAPX B`. -/
theorem APXComplete.of_lReduction {α₁ β₁ α₂ β₂ : Type}
    {encI₁ : α₁ ↪ List Bool} {encS₁ : β₁ ↪ List Bool}
    {encI₂ : α₂ ↪ List Bool} {encS₂ : β₂ ↪ List Bool}
    {A : NPOptimizationProblem encI₁ encS₁}
    {B : NPOptimizationProblem encI₂ encS₂}
    (hA : APXComplete A) (hB : InAPX B) (r : LReduction A B) : APXComplete B :=
  hA.of_ptasReducible hB (ptasReducible_of_lReduction r)

/-! ### Binary-Threshold Undergraph and Objective `NP`-Hardness -/

/-- Binary-threshold decision undergraph `{(a, k) | g a ≤ k}` of a natural-valued objective `g`. -/
def OptUndergraph {α : Type*} (g : α → ℕ) : Set (α × ℕ) :=
  {p | g p.1 ≤ p.2}

@[simp]
lemma mem_optUndergraph_iff {α : Type*} (g : α → ℕ) (p : α × ℕ) :
    p ∈ OptUndergraph g ↔ g p.1 ≤ p.2 := Iff.rfl

/-- Objective-function `NP`-hardness: the binary-threshold undergraph `{p | g p.1 ≤ p.2}` is
`NP`-hard under polynomial-time many-one reductions. -/
def IsNPHardObjective {α : Type} (encI : α ↪ List Bool) (g : α → ℕ) : Prop :=
  NPHard (encPair encI encNat) (OptUndergraph g)

/-- Characterization of `IsNPHardObjective`. -/
lemma isNPHardObjective_iff {α : Type} (encI : α ↪ List Bool) (g : α → ℕ) :
    IsNPHardObjective encI g ↔ NPHard (encPair encI encNat) (OptUndergraph g) := Iff.rfl

/-- Upward transfer of `IsNPHardObjective` along a cost-preserving polynomial-time map. -/
theorem IsNPHardObjective.of_costPreserving {α₁ α₂ : Type}
    {encI₁ : α₁ ↪ List Bool} {encI₂ : α₂ ↪ List Bool} {g₁ : α₁ → ℕ} {g₂ : α₂ → ℕ}
    {f : α₁ → α₂} (hhard : IsNPHardObjective encI₁ g₁)
    (hf : ComputableInPolyTime f encI₁ encI₂) (hcost : ∀ a, g₁ a = g₂ (f a)) :
    IsNPHardObjective encI₂ g₂ := by
  refine NPHard.trans hhard ⟨fun p ↦ (f p.1, p.2), ?_, fun p ↦ ?_⟩
  · exact (hf.comp (fst encI₁ encNat)).prod (snd encI₁ encNat)
  · simp [OptUndergraph, hcost]

/-- If an `NP`-hard objective `g` is computable in polynomial time into binary, then `P = NP`. -/
theorem P_eq_NP_of_isNPHardObjective_of_computableInPolyTime {α : Type}
    {encI : α ↪ List Bool} {g : α → ℕ}
    (hhard : IsNPHardObjective encI g) (hg : ComputableInPolyTime g encI encNat)
    {γ : Type} (enc : γ ↪ List Bool) : P enc = NP enc := by
  have hmem : OptUndergraph g ∈ P (encPair encI encNat) :=
    ⟨fun p ↦ decide (g p.1 ≤ p.2), binary_le' (hg.comp (fst encI encNat)) (snd encI encNat),
      fun p ↦ by simp [OptUndergraph]⟩
  exact Set.Subset.antisymm P_subset_NP fun A hA ↦
    (((isNPHardObjective_iff encI g).mp hhard) enc A hA).mem_P hmem

/-- Contrapositive exact intractability: under `P ≠ NP`, no `NP`-hard objective is computable in
polynomial time. -/
theorem not_computableInPolyTime_of_isNPHardObjective_of_P_ne_NP {α : Type}
    {encI : α ↪ List Bool} {g : α → ℕ} {γ : Type} {enc : γ ↪ List Bool}
    (hPneNP : P enc ≠ NP enc) (hhard : IsNPHardObjective encI g) :
    ¬ ComputableInPolyTime g encI encNat :=
  fun hg ↦ hPneNP (P_eq_NP_of_isNPHardObjective_of_computableInPolyTime hhard hg enc)

/-- Any polynomial-time exact witness solver for an `NPO` problem with `NP`-hard optimum collapses
`P = NP`. -/
theorem P_eq_NP_of_isNPHardObjective_of_exactSolver {α β : Type}
    {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    {problem : NPOptimizationProblem encI encS}
    (hhard : IsNPHardObjective encI problem.optimum)
    {solve : α → β} (hsolve : ComputableInPolyTime solve encI encS)
    (hexact : ∀ a, problem.Feasible a (solve a) ∧ problem.value (a, solve a) = problem.optimum a)
    {γ : Type} (enc : γ ↪ List Bool) : P enc = NP enc := by
  have hopt : ComputableInPolyTime problem.optimum encI encNat := by
    have hcomp := problem.computableInPolyTime_value.comp (id'.prod hsolve)
    exact hcomp.of_enc_eq fun a ↦ congrArg encNat (hexact a).2.symm
  exact P_eq_NP_of_isNPHardObjective_of_computableInPolyTime hhard hopt enc

/-! ### Canonical `MAX-3SAT` `NPO` Problem and `APX`-Hardness Collapse -/

/-- Extracts the nonempty clauses of length at most `3` from a CNF formula. -/
def threeClauses (φ : CNF ℕ) : CNF ℕ :=
  φ.filter fun c ↦ decide (c.length ≤ 3) && !c.isEmpty

@[simp]
lemma threeClauses_nil : threeClauses [] = [] := by
  unfold threeClauses; rfl

private lemma threeClauses_mem_iff (φ : CNF ℕ) (c : Clause ℕ) :
    c ∈ threeClauses φ ↔ c ∈ φ ∧ c.length ≤ 3 ∧ c ≠ [] := by
  simp [threeClauses]

private lemma countUnsat_filter_nonempty (φ : CNF ℕ) (σ : ℕ → Bool) :
    φ.length - φ.countUnsat σ =
      (φ.filter fun c ↦ !c.isEmpty).length -
        CNF.countUnsat σ (φ.filter fun c ↦ !c.isEmpty) := by
  induction φ with
  | nil => simp [CNF.countUnsat]
  | cons c φ ih =>
    have hle₁ : CNF.countUnsat σ φ ≤ φ.length := CNF.countUnsat_le_length σ φ
    have hle₂ : CNF.countUnsat σ (φ.filter fun c ↦ !c.isEmpty) ≤
        (φ.filter fun c ↦ !c.isEmpty).length :=
      CNF.countUnsat_le_length σ (φ.filter fun c ↦ !c.isEmpty)
    cases hc : c.isEmpty
    · simp only [CNF.countUnsat, List.filter_cons, hc, Bool.not_false, ↓reduceIte,
        List.countP_cons, List.length_cons] at ih hle₁ hle₂ ⊢
      cases c.eval σ <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> omega
    · have hemp : c = [] := List.isEmpty_iff.mp hc
      subst hemp
      simp only [CNF.countUnsat, List.filter_cons, List.isEmpty_nil, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, List.countP_cons, Clause.eval_nil, Bool.not_false,
        List.length_cons] at ih hle₁ ⊢
      omega

private lemma threeClauses_eq_filter_nonempty {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    threeClauses φ = φ.filter fun c ↦ !c.isEmpty := by
  unfold threeClauses
  refine List.filter_congr fun c hc ↦ ?_
  simp [h3 c hc]

private lemma countUnsat_selectDistinct_map (φ : CNF ℕ) (σ : ℕ → Bool) :
    φ.countUnsat (fun v ↦ decide (v ∈ selectDistinct φ.vars (φ.vars.map σ))) =
      φ.countUnsat σ := by
  refine CNF.countUnsat_congr fun v hv ↦ ?_
  have hmem : v ∈ selectDistinct φ.vars (φ.vars.map σ) ↔ σ v = true := by
    rw [mem_selectDistinct]
    have hidx : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_iff.mpr hv
    simp [hv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, List.getElem_idxOf]
  cases h : σ v <;> simp [hmem, h]

private lemma computableInPolyTime_threeClauses :
    ComputableInPolyTime threeClauses encCNF encCNF := by
  unfold threeClauses
  have hlen : ComputableInPolyTime
      (fun p : CNF ℕ × Clause ℕ ↦ p.2.length) (encPair encCNF (encClause encNat)) encUnary :=
    Clause.computableInPolyTime_length (snd encCNF (encClause encNat))
  have hpred : ComputableInPolyTime
      (fun p : CNF ℕ × Clause ℕ ↦ decide (p.2.length ≤ 3) && !p.2.isEmpty)
      (encPair encCNF (encClause encNat)) encBool :=
    bool_and' (unary_le' hlen (const 3))
      (bool_not.comp ((listIsEmpty' (encPair encNat encBool)).comp (snd encCNF (encClause encNat))))
  exact filterWithInput id' hpred

private lemma computableInPolyTime_maxThreeSATValue :
    ComputableInPolyTime
      (fun p : CNF ℕ × List Bool ↦
        (threeClauses p.1).length -
          (threeClauses p.1).countUnsat (fun v ↦ decide (v ∈ selectDistinct p.1.vars p.2)))
      (encPair encCNF encBits) encNat := by
  have h3c := computableInPolyTime_threeClauses
  have henc : encCNF = encCNFOver encNat := rfl
  rw [henc] at h3c ⊢
  have h3 := h3c.comp (fst (encCNFOver encNat) encBits)
  have hlen := CNF.computableInPolyTime_length h3
  have hsel := (computableInPolyTime_selectDistinct encNat).comp
    (((CNF.computableInPolyTime_vars encNat).comp (fst (encCNFOver encNat) encBits)).prod
      (snd (encCNFOver encNat) encBits))
  have hunsat := (computableInPolyTime_countUnsat_mem encNat).comp (h3.prod hsel)
  exact unary_to_binary.comp (unary_sub.comp (hlen.prod hunsat))

/-- Canonical `NPOptimizationProblem` formulation of `MAX-3SAT` on `CNF ℕ`, counting satisfied
nonempty clauses of length at most `3` under variable-mask solutions `s : List Bool`. -/
def maxThreeSATNPO : NPOptimizationProblem encCNF encBits where
  Feasible φ s := s.length ≤ φ.vars.length
  exists_feasible _ := ⟨[], Nat.zero_le _⟩
  feasible_mem_P := by
    refine ⟨fun p ↦ decide (p.2.length ≤ p.1.vars.length), ?_, fun p ↦ by simp⟩
    have hslen : ComputableInPolyTime (fun p : CNF ℕ × List Bool ↦ p.2.length)
        (encPair encCNF encBits) encUnary :=
      (length encBool).comp (snd encCNF encBits)
    have hvlen : ComputableInPolyTime (fun p : CNF ℕ × List Bool ↦ p.1.vars.length)
        (encPair encCNF encBits) encUnary :=
      CNF.computableInPolyTime_vars_length (fst encCNF encBits)
    exact unary_le' hslen hvlen
  solution_length_bound :=
    ⟨Polynomial.X, fun φ s hs ↦ by
      simpa only [encBits_apply, Polynomial.eval_X] using hs.trans (SAT.length_vars_le φ)⟩
  value p :=
    (threeClauses p.1).length -
      (threeClauses p.1).countUnsat (fun v ↦ decide (v ∈ selectDistinct p.1.vars p.2))
  computableInPolyTime_value := computableInPolyTime_maxThreeSATValue
  goal := .maximize

@[simp]
lemma maxThreeSATNPO_goal : maxThreeSATNPO.goal = .maximize := by
  unfold maxThreeSATNPO; rfl

/-- `MAX-3SAT` belongs unconditionally to `APX` (factor `2`) via Johnson's algorithm. -/
theorem inAPX_maxThreeSATNPO : InAPX maxThreeSATNPO := by
  obtain ⟨A, hA, happrox⟩ := exists_polyTime_maxSAT_approx
  let solve : CNF ℕ → List Bool := fun φ ↦ φ.vars.map fun v ↦ decide (v ∈ A (threeClauses φ))
  have hsolve : ComputableInPolyTime solve encCNF encBits := by
    have hA3 : ComputableInPolyTime (fun φ ↦ A (threeClauses φ)) encCNF (encList encNat) :=
      hA.comp computableInPolyTime_threeClauses
    have hvars : ComputableInPolyTime (CNF.vars (V := ℕ)) encCNF (encList encNat) :=
      CNF.computableInPolyTime_vars encNat
    have hmem : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ decide (p.2 ∈ A (threeClauses p.1)))
        (encPair encCNF encNat) encBool :=
      decide_mem (hA3.comp (fst encCNF encNat)) (snd encCNF encNat)
    have hmap := mapWithInput (f := fun φ v ↦ decide (v ∈ A (threeClauses φ))) hvars hmem
    exact (listToBits.comp hmap).of_enc_eq fun _ ↦ rfl
  refine ⟨2, by decide, solve, hsolve, fun φ ↦ ?_⟩
  refine ⟨by simp [maxThreeSATNPO, solve], fun other _ ↦ ?_⟩
  have hnonempty : ∀ c ∈ threeClauses φ, 1 ≤ c.toFinset.card := fun c hc ↦ by
    have hne : c ≠ [] := ((threeClauses_mem_iff φ c).mp hc).2.2
    exact Finset.card_pos.mpr ⟨c.head hne, List.mem_toFinset.mpr (List.head_mem hne)⟩
  have hj := (happrox 1 (threeClauses φ) hnonempty).1
  simp only [pow_one] at hj
  have hagree :
      (threeClauses φ).countUnsat (fun v ↦ decide (v ∈ selectDistinct φ.vars (solve φ))) =
        (threeClauses φ).countUnsat (fun v ↦ decide (v ∈ A (threeClauses φ))) := by
    refine CNF.countUnsat_congr fun v hv ↦ ?_
    have hv' : v ∈ φ.vars := by
      obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.mp hv
      exact CNF.mem_vars.mpr ⟨c, ((threeClauses_mem_iff φ c).mp hc).1, b, hb⟩
    have hidx : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_iff.mpr hv'
    rw [decide_eq_decide, mem_selectDistinct]
    simp only [solve, hv', true_and, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hidx, Option.map_some, List.getElem_idxOf, Option.getD_some,
      decide_eq_true_eq]
  change (threeClauses φ).length - _ ≤ 2 * ((threeClauses φ).length - _)
  rw [hagree]
  have hle_other := (threeClauses φ).countUnsat_le_length
    (fun v ↦ decide (v ∈ selectDistinct φ.vars other))
  omega

/-- Any `PTAS` for `maxThreeSATNPO` collapses `P = NP` (via the PCP constant-factor
inapproximability of `MAX-3SAT`). -/
theorem P_eq_NP_of_maxThreeSATNPO_ptas (hptas : maxThreeSATNPO.PTAS)
    {γ : Type} (enc : γ ↪ List Bool) : P enc = NP enc := by
  let k : ℕ := 3 * 2 ^ 78
  have hk : 0 < k := Nat.mul_pos (by decide) (Nat.two_pow_pos 78)
  obtain ⟨solve, hsolve, happrox⟩ := hptas k hk
  let A : CNF ℕ → List ℕ := fun φ ↦ selectDistinct φ.vars (solve φ)
  have hA : ComputableInPolyTime A encCNF (encList encNat) :=
    (computableInPolyTime_selectDistinct encNat).comp
      ((CNF.computableInPolyTime_vars encNat).prod hsolve)
  have hρ : 1 - 1 / (3 * 2 ^ 77 : ℝ) < (k - 1 : ℝ) / k := by
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
    have hpow : (0 : ℝ) < (2 : ℝ) ^ 77 := by exact_mod_cast (Nat.two_pow_pos 77)
    have hlt : (3 * 2 ^ 77 : ℝ) < k := by
      dsimp only [k]; push_cast; rw [pow_succ]; linarith
    have h77_pos : (0 : ℝ) < 3 * 2 ^ 77 := by linarith
    have hdiv : (1 : ℝ) / k < 1 / (3 * 2 ^ 77 : ℝ) := one_div_lt_one_div_of_lt h77_pos hlt
    have hsub : (k - 1 : ℝ) / k = 1 - 1 / k := by rw [sub_div, div_self hk_pos.ne']
    rw [hsub]; linarith
  refine P_eq_NP_of_maxThreeSAT_approx hρ hA (fun φ h3 ↦ ?_) enc
  obtain ⟨σ, hσ⟩ := φ.exists_countUnsat_div_eq_unsatVal
  let other : List Bool := φ.vars.map σ
  have hother : maxThreeSATNPO.Feasible φ other := by simp [maxThreeSATNPO, other]
  have hbound := (happrox φ).2 other hother
  simp only [maxThreeSATNPO] at hbound
  rw [threeClauses_eq_filter_nonempty h3, ← countUnsat_filter_nonempty,
    ← countUnsat_filter_nonempty, countUnsat_selectDistinct_map] at hbound
  have hcast : ((k - 1 : ℕ) : ℝ) * (φ.length - φ.countUnsat σ : ℕ) ≤
      (k : ℝ) * (φ.length - φ.countUnsat (fun v ↦ decide (v ∈ A φ)) : ℕ) := by
    exact_mod_cast hbound
  have hleσ : φ.countUnsat σ ≤ φ.length := φ.countUnsat_le_length σ
  have hleA : φ.countUnsat (fun v ↦ decide (v ∈ A φ)) ≤ φ.length := φ.countUnsat_le_length _
  rw [Nat.cast_sub hleσ, Nat.cast_sub hleA, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at hcast
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hopt_eq : (1 - φ.unsatVal) * φ.length = (φ.length : ℝ) - φ.countUnsat σ := by
    rcases Nat.eq_zero_or_pos φ.length with h0 | hpos
    · have hσ0 : φ.countUnsat σ = 0 := Nat.eq_zero_of_le_zero (h0 ▸ hleσ)
      simp [h0, hσ0]
    · have hlen_pos : (0 : ℝ) < φ.length := Nat.cast_pos.mpr hpos
      rw [← hσ, sub_mul, one_mul, div_mul_cancel₀ _ hlen_pos.ne']
  rw [mul_assoc, hopt_eq, div_mul_eq_mul_div, div_le_iff₀ hk_pos]
  linarith

/-- **Fundamental `APX`-hardness collapse**: if any `APX`-hard `NPO` optimization problem admits a
`PTAS`, then `P = NP` for every instance encoding. -/
theorem P_eq_NP_of_apxHard_of_ptas {α β : Type}
    {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    {problem : NPOptimizationProblem encI encS}
    (hhard : APXHard problem) (hptas : problem.PTAS)
    {γ : Type} (enc : γ ↪ List Bool) : P enc = NP enc :=
  P_eq_NP_of_maxThreeSATNPO_ptas
    ((((apxHard_iff problem).mp hhard) maxThreeSATNPO inAPX_maxThreeSATNPO).ptas hptas) enc

/-- Contrapositive `PTAS` impossibility: under `P ≠ NP`, no `APX`-hard `NPO` problem admits a
`PTAS`. -/
theorem not_ptas_of_apxHard_of_P_ne_NP {α β : Type}
    {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    {problem : NPOptimizationProblem encI encS}
    {γ : Type} {enc : γ ↪ List Bool}
    (hPneNP : P enc ≠ NP enc) (hhard : APXHard problem) : ¬ problem.PTAS :=
  fun hptas ↦ hPneNP (P_eq_NP_of_apxHard_of_ptas hhard hptas enc)

/-- Under `P ≠ NP`, no `NPO` problem admitting a `PTAS` is `APX`-hard. -/
theorem not_apxHard_of_ptas_of_P_ne_NP {α β : Type}
    {encI : α ↪ List Bool} {encS : β ↪ List Bool}
    {problem : NPOptimizationProblem encI encS}
    {γ : Type} {enc : γ ↪ List Bool}
    (hPneNP : P enc ≠ NP enc) (hptas : problem.PTAS) : ¬ APXHard problem :=
  fun hhard ↦ hPneNP (P_eq_NP_of_apxHard_of_ptas hhard hptas enc)

end Cslib.Complexity
