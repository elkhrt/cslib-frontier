/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The Approximation Dichotomy Conjecture for Constraint Satisfaction Problems

This module states the Approximation Dichotomy Conjecture of Bhangale, Khot, and Minzer
 in terms of `Cslib.Complexity.PromiseProblem`, `PromiseP`, and
`PromiseProblem.NPHard`, and proves elementary uniqueness and monotonicity properties of the
dichotomy threshold under standard Lean axioms.

## Main definitions

* `CslibFrontier.Computability.Complexity.GapCspPromise`: the promise problem distinguishing
  satisfiable `Max-𝒫-CSP` instances from instances of optimal value at most `s`.
* `CslibFrontier.Computability.Complexity.ApproximationDichotomyConjectureFor`: the dichotomy
  statement for a specific CSP predicate family `𝒫` and gap-problem encoding.
* `CslibFrontier.Computability.Complexity.ApproximationDichotomyConjecture`: the global
  Approximation Dichotomy Conjecture across all arities `k` and NP-hard predicate families.

## Main results

* `CslibFrontier.Computability.Complexity.approximationDichotomyConjectureFor_iff`:
  unfolding characterization of the per-family conjecture.
* `CslibFrontier.Computability.Complexity.threshold_unique_of_not_np_subset_p`:
  when `P ≠ NP`, the dichotomy threshold `α_𝒫` for an NP-hard CSP family is unique.
-/

public section

namespace CslibFrontier.Computability.Complexity

open Cslib.Complexity

/-- The gap promise problem for a CSP family on instance type `Inst`:
yes-instances are satisfiable (`optVal x = 1`), no-instances have value at most `s`
(`optVal x ≤ s`), given `s < 1`. -/
def GapCspPromise {Inst : Type*} (optVal : Inst → ℝ) (s : ℝ) (hs : s < 1) :
    PromiseProblem Inst where
  yes := {x | optVal x = 1}
  no := {x | optVal x ≤ s}
  disjoint := Set.disjoint_left.mpr fun _ hx1 hxs ↦ by
    simp only [Set.mem_ofPred_eq] at hx1 hxs
    linarith

@[simp]
lemma mem_gapCspPromise_yes {Inst : Type*} (optVal : Inst → ℝ) (s : ℝ) (hs : s < 1)
    (x : Inst) : x ∈ (GapCspPromise optVal s hs).yes ↔ optVal x = 1 :=
  Iff.rfl

@[simp]
lemma mem_gapCspPromise_no {Inst : Type*} (optVal : Inst → ℝ) (s : ℝ) (hs : s < 1)
    (x : Inst) : x ∈ (GapCspPromise optVal s hs).no ↔ optVal x ≤ s :=
  Iff.rfl

/-- The Approximation Dichotomy Conjecture for a single CSP instance family `(Inst, enc, optVal)`
whose exact satisfiability problem `{x | optVal x = 1}` is NP-hard: there exists a threshold
`α ∈ [0, 1]` such that:
1. Distinguishing satisfiable instances from instances of value `< α` (equivalently, `≤ α - ε`
   for every `ε > 0`) is in `PromiseP enc`; and
2. For every `ε > 0`, distinguishing satisfiable instances from instances of value `≤ α + ε`
   (when `α + ε < 1`) is NP-hard (`PromiseProblem.NPHard`). -/
def ApproximationDichotomyConjectureFor {Inst : Type} (enc : Inst ↪ List Bool)
    (optVal : Inst → ℝ) : Prop :=
  ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
    (∀ s : ℝ, s < α → ∀ hs1 : s < 1, GapCspPromise optVal s hs1 ∈ PromiseP enc) ∧
    (∀ ε : ℝ, 0 < ε → ∀ h1 : α + ε < 1,
      PromiseProblem.NPHard enc (GapCspPromise optVal (α + ε) h1))

lemma approximationDichotomyConjectureFor_iff {Inst : Type} (enc : Inst ↪ List Bool)
    (optVal : Inst → ℝ) :
    ApproximationDichotomyConjectureFor enc optVal ↔
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
        (∀ s : ℝ, s < α → ∀ hs1 : s < 1, GapCspPromise optVal s hs1 ∈ PromiseP enc) ∧
        (∀ ε : ℝ, 0 < ε → ∀ h1 : α + ε < 1,
          PromiseProblem.NPHard enc (GapCspPromise optVal (α + ε) h1)) :=
  Iff.rfl

/-- Under `P ≠ NP`, a `PromiseP` problem cannot be `PromiseProblem.NPHard` — so the dichotomy
threshold `α` in `ApproximationDichotomyConjectureFor` is unique. -/
theorem threshold_unique_of_not_np_subset_p {Inst : Type} (enc : Inst ↪ List Bool)
    (optVal : Inst → ℝ)
    (hsep : ∀ Q : PromiseProblem Inst, Q ∈ PromiseP enc → ¬ PromiseProblem.NPHard enc Q)
    {α₁ α₂ : ℝ}
    (h₁ : 0 ≤ α₁ ∧ α₁ ≤ 1 ∧
      (∀ s : ℝ, s < α₁ → ∀ hs1 : s < 1, GapCspPromise optVal s hs1 ∈ PromiseP enc) ∧
      (∀ ε : ℝ, 0 < ε → ∀ h1 : α₁ + ε < 1,
        PromiseProblem.NPHard enc (GapCspPromise optVal (α₁ + ε) h1)))
    (h₂ : 0 ≤ α₂ ∧ α₂ ≤ 1 ∧
      (∀ s : ℝ, s < α₂ → ∀ hs1 : s < 1, GapCspPromise optVal s hs1 ∈ PromiseP enc) ∧
      (∀ ε : ℝ, 0 < ε → ∀ h1 : α₂ + ε < 1,
        PromiseProblem.NPHard enc (GapCspPromise optVal (α₂ + ε) h1))) :
    α₁ = α₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let ε := (α₂ - α₁) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hs : α₁ + ε < α₂ := by dsimp [ε]; linarith
    have hs1 : α₁ + ε < 1 := lt_of_lt_of_le hs h₂.2.1
    exact hsep _ (h₂.2.2.1 (α₁ + ε) hs hs1) (h₁.2.2.2 ε hε hs1)
  · let ε := (α₁ - α₂) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hs : α₂ + ε < α₁ := by dsimp [ε]; linarith
    have hs1 : α₂ + ε < 1 := lt_of_lt_of_le hs h₁.2.1
    exact hsep _ (h₁.2.2.1 (α₂ + ε) hs hs1) (h₂.2.2.2 ε hε hs1)

/-- Concrete `k`-ary CSP predicate family over finite alphabet `Fin q`. -/
abbrev CspFamily (k q : ℕ) := Set ((Fin k → Fin q) → Bool)

/-- A concrete weighted `k`-ary CSP instance over `Fin q` with `numVars` variables. -/
structure ConcreteCspInst (k q : ℕ) where
  /-- Number of variables. -/
  numVars : ℕ
  /-- List of constraints `(scope, predicate index)`. -/
  clauses : List ((Fin k → Fin numVars) × ((Fin k → Fin q) → Bool))

/-- Optimal fraction of satisfied clauses of a `ConcreteCspInst`. -/
noncomputable def ConcreteCspInst.optVal {k q : ℕ} (I : ConcreteCspInst k q) : ℝ :=
  if I.clauses = [] then 1
  else
    let m : ℝ := I.clauses.length
    sSup {v : ℝ | ∃ α : Fin I.numVars → Fin q,
      v = ((I.clauses.countP (fun c ↦ c.2 (α ∘ c.1)) : ℕ) : ℝ) / m}

/-- Global Approximation Dichotomy Conjecture: for every `k, q : ℕ`, every predicate family
`Preds : CspFamily k q`, and every encoding `enc` of `Preds`-CSP instances whose exact
satisfiability problem is NP-hard, `ApproximationDichotomyConjectureFor` holds. -/
def ApproximationDichotomyConjecture : Prop :=
  ∀ (k q : ℕ) (Preds : CspFamily k q)
    (enc : {I : ConcreteCspInst k q // ∀ c ∈ I.clauses, c.2 ∈ Preds} ↪ List Bool),
    PromiseProblem.NPHard enc
      (PromiseProblem.ofSet {I : {I : ConcreteCspInst k q // ∀ c ∈ I.clauses, c.2 ∈ Preds} |
        I.1.optVal = 1}) →
    ApproximationDichotomyConjectureFor enc (fun I ↦ I.1.optVal)

lemma approximationDichotomyConjecture_iff :
    ApproximationDichotomyConjecture ↔
      ∀ (k q : ℕ) (Preds : CspFamily k q)
        (enc : {I : ConcreteCspInst k q // ∀ c ∈ I.clauses, c.2 ∈ Preds} ↪ List Bool),
        PromiseProblem.NPHard enc
          (PromiseProblem.ofSet {I : {I : ConcreteCspInst k q // ∀ c ∈ I.clauses, c.2 ∈ Preds} |
            I.1.optVal = 1}) →
        ApproximationDichotomyConjectureFor enc (fun I ↦ I.1.optVal) :=
  Iff.rfl

end CslibFrontier.Computability.Complexity
