/-
Copyright (c) 2026 CslibFrontier Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CslibFrontier Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.Complexity.Problems.RealArithmetic

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# The Existential Theory of the Reals Complexity Class (`ExistsR`)

Defines the complexity class `ExistsR` ($\exists\mathbb{R}$) of decision problems polynomial-time
many-one reducible to the existential theory of the reals `Cslib.Complexity.ETR`, together with
decision-problem hardness (`ExistsRHard`), completeness (`ExistsRComplete`), and promise-problem
hardness (`PromiseExistsRHard`) under deterministic polynomial-time reductions.

## Main definitions

* `CslibFrontier.Complexity.ExistsR`: decision problems polynomial-time reducible to `ETR`.
* `CslibFrontier.Complexity.ExistsRHard`, `CslibFrontier.Complexity.ExistsRComplete`:
  polynomial-time hardness and completeness for `ExistsR`.
* `CslibFrontier.Complexity.PromiseExistsRHard`: promise-problem hardness for `ExistsR` under
  `PromiseProblem.PolyTimeReducible`.

## Main results

* `CslibFrontier.Complexity.ETR_existsRComplete`: `ETR` is complete for `ExistsR`.
* `CslibFrontier.Complexity.P_subset_ExistsR`: every polynomial-time decidable problem belongs to
  `ExistsR`.
* `CslibFrontier.Complexity.PolyTimeReducible.mem_ExistsR`,
  `CslibFrontier.Complexity.ExistsRHard.trans`,
  `CslibFrontier.Complexity.PromiseExistsRHard.trans`,
  `CslibFrontier.Complexity.PromiseExistsRHard.mono`: closure and transfer under polynomial-time
  reductions.
* `CslibFrontier.Complexity.PromiseExistsRHard.ExistsR_subset_NP_of_mem_PromiseNP`,
  `CslibFrontier.Complexity.PromiseExistsRHard.ExistsR_eq_P_of_mem_PromiseP`: collapse consequences
  when an `ExistsR`-hard promise problem lies in `PromiseNP` or `PromiseP`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.RealArithmetic Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-- The complexity class $\exists\mathbb{R}$: decision problems polynomial-time many-one reducible
to `Cslib.Complexity.ETR` with respect to the instance encoding `enc`. -/
@[expose]
def ExistsR {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | Cslib.Complexity.PolyTimeReducible enc encBits A Cslib.Complexity.ETR}

/-- Polynomial-time many-one hardness for `ExistsR`. -/
@[expose]
def ExistsRHard {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeHard (@ExistsR) encB B

/-- Polynomial-time many-one completeness for `ExistsR`. -/
@[expose]
def ExistsRComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete (@ExistsR) encB B

/-- Promise-problem hardness for `ExistsR` under deterministic polynomial-time reductions. -/
@[expose]
def PromiseExistsRHard {β : Type} (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  HardUnder (fun enc A Y ↦ PromiseProblem.PolyTimeReducible enc encB (PromiseProblem.ofSet A) Y)
    (@ExistsR) Y

/-- `ETR` belongs to `ExistsR encBits`. -/
theorem ETR_mem_ExistsR : Cslib.Complexity.ETR ∈ ExistsR encBits :=
  Cslib.Complexity.PolyTimeReducible.refl encBits Cslib.Complexity.ETR

/-- `ExistsR` is downward closed under polynomial-time many-one reductions. -/
theorem mem_ExistsR_of_polyTimeReducible {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hAB : Cslib.Complexity.PolyTimeReducible encA encB A B) (hB : B ∈ ExistsR encB) :
    A ∈ ExistsR encA :=
  hAB.trans hB

/-- A decision problem is `ExistsR`-hard iff `ETR` reduces to it in polynomial time. -/
theorem existsRHard_iff_polyTimeReducible_ETR {β : Type} {encB : β ↪ List Bool} {B : Set β} :
    ExistsRHard encB B ↔
      Cslib.Complexity.PolyTimeReducible encBits encB Cslib.Complexity.ETR B :=
  ⟨fun h ↦ h encBits Cslib.Complexity.ETR ETR_mem_ExistsR,
    fun h _ _ _ hA ↦ hA.trans h⟩

/-- `ETR` is complete for `ExistsR`. -/
theorem ETR_existsRComplete : ExistsRComplete encBits Cslib.Complexity.ETR :=
  ⟨ETR_mem_ExistsR, existsRHard_iff_polyTimeReducible_ETR.mpr (.refl encBits _)⟩

/-- `ExistsR`-hardness transfers along polynomial-time many-one reductions. -/
theorem ExistsRHard.trans {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β}
    (hA : ExistsRHard encA A) (hAB : Cslib.Complexity.PolyTimeReducible encA encB A B) :
    ExistsRHard encB B :=
  existsRHard_iff_polyTimeReducible_ETR.mpr
    ((existsRHard_iff_polyTimeReducible_ETR.mp hA).trans hAB)

/-- Every polynomial-time decidable language belongs to `ExistsR` (`P ⊆ ExistsR`). -/
theorem P_subset_ExistsR {α : Type} (enc : α ↪ List Bool) : P enc ⊆ ExistsR enc := by
  intro A hA
  obtain ⟨f, hf, hdec⟩ := mem_P.mp hA
  refine ⟨fun a ↦ if f a then encFormula 0 (.not .false) else encFormula 0 .false,
    ite hf (const (encFormula 0 (.not .false))) (const (encFormula 0 .false)), fun a ↦ ?_⟩
  rw [hdec a]
  by_cases hfa : f a = true
  · simp only [hfa, ↓reduceIte, true_iff, encFormula_mem_ETR]
    exact ⟨Fin.elim0, by simp [Formula.solutionSet]⟩
  · dsimp only; rw [ite_eq_right hfa]
    refine ⟨fun h ↦ absurd h hfa, fun h ↦ ?_⟩
    rw [encFormula_mem_ETR] at h
    rcases h with ⟨_, h⟩
    simp [Formula.solutionSet] at h

/-- A promise problem is `ExistsR`-hard iff `PromiseProblem.ofSet ETR` reduces to it in polynomial
time. -/
theorem promiseExistsRHard_iff_polyTimeReducible_ETR {β : Type} {encB : β ↪ List Bool}
    {Y : PromiseProblem β} :
    PromiseExistsRHard encB Y ↔
      PromiseProblem.PolyTimeReducible encBits encB
        (PromiseProblem.ofSet Cslib.Complexity.ETR) Y :=
  ⟨fun h ↦ h encBits Cslib.Complexity.ETR ETR_mem_ExistsR,
    fun h _ _ _ hA ↦ (PromiseProblem.polyTimeReducible_ofSet_iff.mpr hA).trans h⟩

/-- On decision problems viewed as promise problems, `PromiseExistsRHard` agrees with
`ExistsRHard`. -/
@[simp]
theorem promiseExistsRHard_ofSet_iff {β : Type} {encB : β ↪ List Bool} {B : Set β} :
    PromiseExistsRHard encB (PromiseProblem.ofSet B) ↔ ExistsRHard encB B := by
  rw [promiseExistsRHard_iff_polyTimeReducible_ETR, existsRHard_iff_polyTimeReducible_ETR,
    PromiseProblem.polyTimeReducible_ofSet_iff]

/-- Promise `ExistsR`-hardness transfers along polynomial-time promise reductions. -/
theorem PromiseExistsRHard.trans {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {X : PromiseProblem α} {Y : PromiseProblem β}
    (hX : PromiseExistsRHard encA X) (hXY : PromiseProblem.PolyTimeReducible encA encB X Y) :
    PromiseExistsRHard encB Y :=
  promiseExistsRHard_iff_polyTimeReducible_ETR.mpr
    ((promiseExistsRHard_iff_polyTimeReducible_ETR.mp hX).trans hXY)

/-- Relaxing a promise problem (enlarging its yes- and no-sets) preserves `PromiseExistsRHard`. -/
theorem PromiseExistsRHard.mono {β : Type} {encB : β ↪ List Bool}
    {Y Y' : PromiseProblem β} (hY : PromiseExistsRHard encB Y)
    (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) :
    PromiseExistsRHard encB Y' :=
  hY.trans (.of_subset hyes hno)

/-- Every language separating the yes- and no-instances of a `PromiseExistsRHard` promise problem
is `ExistsR`-hard. -/
theorem PromiseExistsRHard.existsRHard_of_subset {β : Type} {encB : β ↪ List Bool}
    {Y : PromiseProblem β} (hY : PromiseExistsRHard encB Y) {B : Set β}
    (hyes : Y.yes ⊆ B) (hno : Disjoint B Y.no) :
    ExistsRHard encB B := by
  rw [← promiseExistsRHard_ofSet_iff]
  exact hY.mono hyes fun b hb hbB ↦ Set.disjoint_left.mp hno hbB hb

/-- If a `PromiseExistsRHard` promise problem belongs to `PromiseNP`, then `ExistsR ⊆ NP` on every
instance encoding. -/
theorem PromiseExistsRHard.ExistsR_subset_NP_of_mem_PromiseNP {β : Type} {encB : β ↪ List Bool}
    {Y : PromiseProblem β} (hY : PromiseExistsRHard encB Y) (hNP : Y ∈ PromiseNP encB)
    {α : Type} (enc : α ↪ List Bool) : ExistsR enc ⊆ NP enc :=
  fun _ hA ↦ ofSet_mem_PromiseNP.mp ((hY enc _ hA).mem_PromiseNP hNP)

/-- If a `PromiseExistsRHard` promise problem belongs to `PromiseP`, then `ExistsR = P` on every
instance encoding. -/
theorem PromiseExistsRHard.ExistsR_eq_P_of_mem_PromiseP {β : Type} {encB : β ↪ List Bool}
    {Y : PromiseProblem β} (hY : PromiseExistsRHard encB Y) (hP : Y ∈ PromiseP encB)
    {α : Type} (enc : α ↪ List Bool) : ExistsR enc = P enc :=
  Set.Subset.antisymm
    (fun _ hA ↦ ofSet_mem_PromiseP.mp ((hY enc _ hA).mem_PromiseP hP))
    (P_subset_ExistsR enc)

end CslibFrontier.Complexity
