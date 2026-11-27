/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PolyTime
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Binary Constraint Satisfaction Problems, List-Decoding Averaging, and Rectangular Relations

Combinatorial foundations for heterogeneous binary constraint satisfaction problems (`2-CSP`):

1. **Abstract heterogeneous `2-CSP`** (`BinaryConstraint`, `TwoCSP`): total and partial
   assignments, induced sub-instances (`TwoCSP.SatisfiesOn`, `TwoCSP.HasSatisfiableSubsetOfCard`),
   worst-case and average $r$-list satisfiability (`TwoCSP.IsListSatisfiable`,
   `TwoCSP.IsAvgListSatisfiable`), and the $1/r^2$ list-decoding averaging theorem
   (`TwoCSP.exists_assignment_numSatisfied_ge_of_isListSatisfiable`).
2. **Rectangular binary relations** (`IsRectangularRel`): equivalence between equality-test
   factorization $\pi(a) = \sigma(b)$ and $2 \times 2$ combinatorial grid closure
   (`isRectangularRel_iff_forall_mem`), canonical active-rectangle decomposition
   (`activeRectangles`), diagonal cardinality lower bound (`card_le_of_diagRel_factor`), and
   computable minimum-element factorization (`listRectRowRep`, `listRectColRep`).

## Main definitions

* `Cslib.Complexity.BinaryConstraint`, `Cslib.Complexity.TwoCSP`,
  `Cslib.Complexity.PartialAssignment`, `Cslib.Complexity.MultiAssignment`.
* `Cslib.Complexity.TwoCSP.Satisfies`, `Cslib.Complexity.TwoCSP.IsSatisfiable`,
  `Cslib.Complexity.TwoCSP.SatisfiesOn`,
  `Cslib.Complexity.TwoCSP.HasSatisfiableSubsetOfCard`.
* `Cslib.Complexity.TwoCSP.IsListSatisfiable`,
  `Cslib.Complexity.TwoCSP.IsAvgListSatisfiable`.
* `Cslib.Complexity.IsRectangularRel`, `Cslib.Complexity.activeRectangles`,
  `Cslib.Complexity.diagRel`, `Cslib.Complexity.listRectRowRep`,
  `Cslib.Complexity.listRectColRep`.

## Main results

* `Cslib.Complexity.TwoCSP.exists_assignment_numSatisfied_ge_of_isListSatisfiable`,
  `Cslib.Complexity.TwoCSP.exists_assignment_numViolated_div_le_of_isListSatisfiable`:
  the $1/r^2$ list-decoding averaging theorem.
* `Cslib.Complexity.isRectangularRel_iff_forall_mem`: equivalence between factorization and
  $2 \times 2$ grid closure.
* `Cslib.Complexity.card_activeRectangles_le_min`,
  `Cslib.Complexity.card_le_of_diagRel_factor`,
  `Cslib.Complexity.listRectRowRep_eq_listRectColRep_iff`: active-rectangle bounds and
  computable rectangular factorization.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

universe u v

/-! ### : Abstract Combinatorial Binary CSP, Partial Assignments, and List Decoding -/

/-- A binary constraint over variable index type `X` and heterogeneous domains `Domain : X → Type*`,
specifying an ordered variable pair `(fst, snd)` and allowed pairs `rel`. -/
structure BinaryConstraint (X : Type*) (Domain : X → Type*) where
  /-- First constrained variable. -/
  fst : X
  /-- Second constrained variable. -/
  snd : X
  /-- Finite set of allowed value pairs in `Domain fst × Domain snd`. -/
  rel : Finset (Domain fst × Domain snd)

/-- Extensionality for `BinaryConstraint`. -/
@[ext]
theorem BinaryConstraint.ext {X : Type*} {Domain : X → Type*}
    {c₁ c₂ : BinaryConstraint X Domain} (h₁ : c₁.fst = c₂.fst) (h₂ : c₁.snd = c₂.snd)
    (hr : HEq c₁.rel c₂.rel) : c₁ = c₂ := by
  cases c₁; cases c₂; simp only at h₁ h₂ hr; subst h₁; subst h₂; cases hr; rfl

/-- Decidable equality for `BinaryConstraint` over decidable variable and domain types. -/
instance BinaryConstraint.instDecidableEq {X : Type*} {Domain : X → Type*}
    [DecidableEq X] [∀ x, DecidableEq (Domain x)] : DecidableEq (BinaryConstraint X Domain) :=
  fun ⟨u₁, v₁, r₁⟩ ⟨u₂, v₂, r₂⟩ =>
    if hu : u₁ = u₂ then
      if hv : v₁ = v₂ then by
        subst hu; subst hv
        exact if hr : r₁ = r₂ then isTrue (by subst hr; rfl)
          else isFalse fun h => hr (heq_iff_eq.mp (BinaryConstraint.mk.inj h).2.2)
      else isFalse fun h => hv (BinaryConstraint.mk.inj h).2.1
    else isFalse fun h => hu (BinaryConstraint.mk.inj h).1

/-- A binary constraint satisfaction problem (`2-CSP`) instance over variable set `X` and
heterogeneous domains `Domain : X → Type*`, given by a finite list of binary constraints. -/
@[ext]
structure TwoCSP (X : Type*) (Domain : X → Type*) where
  /-- Finite list of binary constraints of the instance. -/
  constraints : List (BinaryConstraint X Domain)

/-- Decidable equality for `TwoCSP` over decidable variable and domain types. -/
instance TwoCSP.instDecidableEq {X : Type*} {Domain : X → Type*}
    [DecidableEq X] [∀ x, DecidableEq (Domain x)] : DecidableEq (TwoCSP X Domain) :=
  fun I₁ I₂ => decidable_of_iff (I₁.constraints = I₂.constraints) TwoCSP.ext_iff.symm

/-- A partial assignment assigning a value in `Domain x.1` to each `x` in `S : Finset X`. -/
abbrev PartialAssignment {X : Type*} (Domain : X → Type*) (S : Finset X) : Type _ :=
  ∀ x : S, Domain x.1

/-- Restricts a total assignment `σ : ∀ x : X, Domain x` to `S : Finset X`. -/
@[expose]
def restrictAssignment {X : Type*} {Domain : X → Type*} (S : Finset X)
    (σ : ∀ x : X, Domain x) : PartialAssignment Domain S :=
  fun x : S => σ x.1

/-- Restricts a partial assignment on `T` to a subset `S ⊆ T`. -/
@[expose]
def restrictPartialAssignment {X : Type*} {Domain : X → Type*} {S T : Finset X}
    (hST : S ⊆ T) (τ : PartialAssignment Domain T) : PartialAssignment Domain S :=
  fun x : S => τ ⟨x.1, hST x.2⟩

/-- A multi-assignment assigning a finite candidate list in `Domain x` to each variable `x : X`. -/
abbrev MultiAssignment (X : Type*) (Domain : X → Type*) : Type _ :=
  ∀ x : X, Finset (Domain x)

namespace MultiAssignment

section FintypeX

variable {X : Type*} {Domain : X → Type*} [Fintype X]

/-- Worst-case list size `max_{x ∈ X} |σ(x)|` of a multi-assignment (`0` if `X` is empty). -/
@[expose]
def maxCard (σ : MultiAssignment X Domain) : ℕ :=
  Finset.univ.sup fun x : X => (σ x).card

/-- Every variable's candidate list cardinality is bounded by `σ.maxCard`. -/
theorem card_le_maxCard (σ : MultiAssignment X Domain) (x : X) : (σ x).card ≤ σ.maxCard :=
  Finset.le_sup (f := fun y : X => (σ y).card) (Finset.mem_univ x)

/-- Total list size `∑_{x ∈ X} |σ(x)|` across all variables of `X`. -/
@[expose]
def totalCard (σ : MultiAssignment X Domain) : ℕ :=
  ∑ x : X, (σ x).card

/-- Total candidate list size is at most `σ.maxCard * Fintype.card X`. -/
theorem totalCard_le_maxCard_mul_card (σ : MultiAssignment X Domain) :
    σ.totalCard ≤ σ.maxCard * Fintype.card X := by
  have h : ∑ x : X, (σ x).card ≤ ∑ _x : X, σ.maxCard :=
    Finset.sum_le_sum fun x _ => σ.card_le_maxCard x
  simpa [totalCard, Finset.sum_const, smul_eq_mul, Nat.mul_comm] using h

/-- Splitting `σ.totalCard` across a decidable predicate `p` on variables. -/
theorem totalCard_eq_sum_filter_add (p : X → Prop) [DecidablePred p]
    (σ : MultiAssignment X Domain) :
    σ.totalCard = (∑ x ∈ Finset.univ.filter p, (σ x).card) +
      (∑ x ∈ Finset.univ.filter (fun x => ¬ p x), (σ x).card) :=
  (Finset.sum_filter_add_sum_filter_not Finset.univ p fun x => (σ x).card).symm

end FintypeX

end MultiAssignment

namespace BinaryConstraint

section Basic

variable {X : Type*} {Domain : X → Type*}

/-- A total assignment `σ` satisfies `c` if `(σ c.fst, σ c.snd) ∈ c.rel`. -/
@[expose]
def Satisfies (c : BinaryConstraint X Domain) (σ : ∀ x : X, Domain x) : Prop :=
  (σ c.fst, σ c.snd) ∈ c.rel

/-- Extract pair membership `(σ c.fst, σ c.snd) ∈ c.rel` from `c.Satisfies σ`. -/
theorem Satisfies.mem_rel {c : BinaryConstraint X Domain} {σ : ∀ x : X, Domain x}
    (h : c.Satisfies σ) : (σ c.fst, σ c.snd) ∈ c.rel := h

/-- Construct `c.Satisfies σ` from pair membership `(σ c.fst, σ c.snd) ∈ c.rel`. -/
theorem satisfies_of_mem_rel {c : BinaryConstraint X Domain} {σ : ∀ x : X, Domain x}
    (h : (σ c.fst, σ c.snd) ∈ c.rel) : c.Satisfies σ := h

/-- Decidability of `BinaryConstraint.Satisfies`. -/
instance instDecidableSatisfies [∀ x, DecidableEq (Domain x)]
    (c : BinaryConstraint X Domain) (σ : ∀ x : X, Domain x) : Decidable (c.Satisfies σ) :=
  inferInstanceAs (Decidable ((σ c.fst, σ c.snd) ∈ c.rel))

/-- Predicate asserting that both endpoints of `c` lie in `S : Finset X`. -/
@[expose]
def IsInducedBy (c : BinaryConstraint X Domain) (S : Finset X) : Prop :=
  c.fst ∈ S ∧ c.snd ∈ S

/-- Decidability of `BinaryConstraint.IsInducedBy`. -/
instance instDecidableIsInducedBy [DecidableEq X]
    (c : BinaryConstraint X Domain) (S : Finset X) : Decidable (c.IsInducedBy S) :=
  inferInstanceAs (Decidable (c.fst ∈ S ∧ c.snd ∈ S))

/-- A multi-assignment `σ` list-satisfies `c` if some pair in `σ c.fst ×ˢ σ c.snd` lies in
`c.rel`. -/
@[expose]
def ListSatisfies (c : BinaryConstraint X Domain) (σ : MultiAssignment X Domain) : Prop :=
  ∃ u ∈ σ c.fst, ∃ v ∈ σ c.snd, (u, v) ∈ c.rel

/-- Decidability of `BinaryConstraint.ListSatisfies`. -/
instance instDecidableListSatisfies [∀ x, DecidableEq (Domain x)]
    (c : BinaryConstraint X Domain) (σ : MultiAssignment X Domain) :
    Decidable (c.ListSatisfies σ) :=
  inferInstanceAs (Decidable (∃ u ∈ σ c.fst, ∃ v ∈ σ c.snd, (u, v) ∈ c.rel))

end Basic

end BinaryConstraint

namespace TwoCSP

section Basic

variable {X : Type*} {Domain : X → Type*}

/-- A total assignment to all variables of a `TwoCSP X Domain` instance. -/
abbrev Assignment (_ : TwoCSP X Domain) : Type _ :=
  ∀ x : X, Domain x

/-- A total assignment `σ` satisfies `I` if it satisfies every constraint in `I.constraints`. -/
@[expose]
def Satisfies (I : TwoCSP X Domain) (σ : I.Assignment) : Prop :=
  ∀ c ∈ I.constraints, c.Satisfies σ

/-- Decidability of `TwoCSP.Satisfies`. -/
instance instDecidableSatisfies [∀ x, DecidableEq (Domain x)]
    (I : TwoCSP X Domain) (σ : I.Assignment) : Decidable (I.Satisfies σ) :=
  inferInstanceAs (Decidable (∀ c ∈ I.constraints, c.Satisfies σ))

/-- A `TwoCSP` instance is satisfiable if some total assignment satisfies all its constraints. -/
@[expose]
def IsSatisfiable (I : TwoCSP X Domain) : Prop :=
  ∃ σ : I.Assignment, I.Satisfies σ

/-- Decidability of `TwoCSP.IsSatisfiable` over finite decidable variable and domain types. -/
instance instDecidableIsSatisfiable [Fintype X] [DecidableEq X]
    [∀ x, Fintype (Domain x)] [∀ x, DecidableEq (Domain x)] (I : TwoCSP X Domain) :
    Decidable I.IsSatisfiable :=
  inferInstanceAs (Decidable (∃ σ : I.Assignment, I.Satisfies σ))

/-- Number of constraints in `I.constraints` (with multiplicity) satisfied by `σ`. -/
def numSatisfied [∀ x, DecidableEq (Domain x)] (I : TwoCSP X Domain) (σ : I.Assignment) : ℕ :=
  I.constraints.countP fun c => decide (c.Satisfies σ)

/-- Number of constraints in `I.constraints` (with multiplicity) violated by `σ`. -/
def numViolated [∀ x, DecidableEq (Domain x)] (I : TwoCSP X Domain) (σ : I.Assignment) : ℕ :=
  I.constraints.countP fun c => !decide (c.Satisfies σ)

/-- Satisfied and violated constraint counts partition `I.constraints.length`. -/
@[simp]
theorem numSatisfied_add_numViolated [∀ x, DecidableEq (Domain x)]
    (I : TwoCSP X Domain) (σ : I.Assignment) :
    I.numSatisfied σ + I.numViolated σ = I.constraints.length :=
  (List.length_eq_countP_add_countP (l := I.constraints)
    (fun c : BinaryConstraint X Domain => decide (c.Satisfies σ))).symm

/-- `I.numViolated σ = 0` if and only if `σ` satisfies `I`. -/
@[simp]
theorem numViolated_eq_zero_iff_satisfies [∀ x, DecidableEq (Domain x)]
    {I : TwoCSP X Domain} {σ : I.Assignment} : I.numViolated σ = 0 ↔ I.Satisfies σ := by
  simp [numViolated, Satisfies, List.countP_eq_zero]

/-- `I.numSatisfied σ = I.constraints.length` if and only if `σ` satisfies `I`. -/
@[simp]
theorem numSatisfied_eq_length_iff_satisfies [∀ x, DecidableEq (Domain x)]
    {I : TwoCSP X Domain} {σ : I.Assignment} :
    I.numSatisfied σ = I.constraints.length ↔ I.Satisfies σ := by
  have := I.numSatisfied_add_numViolated σ
  rw [← numViolated_eq_zero_iff_satisfies]
  omega

/-- Real-valued fractional violation bound deduced from
`I.constraints.length ≤ r ^ 2 * I.numSatisfied τ`. -/
theorem numViolated_div_le_of_length_le [∀ x, DecidableEq (Domain x)] {I : TwoCSP X Domain}
    {r : ℕ} {τ : I.Assignment} (hr : 1 ≤ r) (hlen : 0 < I.constraints.length)
    (hsat : I.constraints.length ≤ r ^ 2 * I.numSatisfied τ) :
    (I.numViolated τ : ℝ) / (I.constraints.length : ℝ) ≤ 1 - 1 / (r : ℝ) ^ 2 := by
  have hm : (0 : ℝ) < (I.constraints.length : ℝ) := Nat.cast_pos.mpr hlen
  have hr2 : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr (by omega))
  have hpart : (I.numSatisfied τ : ℝ) + (I.numViolated τ : ℝ) = (I.constraints.length : ℝ) := by
    exact_mod_cast I.numSatisfied_add_numViolated τ
  have hsat_r : (I.constraints.length : ℝ) ≤ (r : ℝ) ^ 2 * (I.numSatisfied τ : ℝ) := by
    exact_mod_cast hsat
  rw [div_le_iff₀ hm]
  have hdiv : 1 / (r : ℝ) ^ 2 * (I.constraints.length : ℝ) ≤ (I.numSatisfied τ : ℝ) := by
    rwa [one_div, inv_mul_le_iff₀ hr2]
  linarith

/-- A partial assignment `τ` on `S` satisfies the induced sub-instance on `S` if every constraint
`c ∈ I.constraints` with both endpoints in `S` is satisfied by `τ`. -/
@[expose]
def SatisfiesOn (I : TwoCSP X Domain) (S : Finset X) (τ : PartialAssignment Domain S) : Prop :=
  ∀ c ∈ I.constraints, ∀ hc : c.IsInducedBy S, (τ ⟨c.fst, hc.1⟩, τ ⟨c.snd, hc.2⟩) ∈ c.rel

/-- Decidability of `TwoCSP.SatisfiesOn`. -/
instance instDecidableSatisfiesOn [DecidableEq X] [∀ x, DecidableEq (Domain x)]
    (I : TwoCSP X Domain) (S : Finset X) (τ : PartialAssignment Domain S) :
    Decidable (I.SatisfiesOn S τ) :=
  decidable_of_iff
    (∀ c ∈ I.constraints,
      if hc : c.IsInducedBy S then (τ ⟨c.fst, hc.1⟩, τ ⟨c.snd, hc.2⟩) ∈ c.rel else True)
    ⟨fun h c hmem hc => by have h' := h c hmem; rw [dite_eq_left hc] at h'; exact h',
      fun h c hmem => by
        by_cases hc : c.IsInducedBy S
        · rw [dite_eq_left hc]; exact h c hmem hc
        · rw [dite_eq_right hc]; trivial⟩

/-- Restricting a satisfying total assignment to any `S : Finset X` satisfies `I` on `S`. -/
theorem Satisfies.satisfiesOn_restrictAssignment {I : TwoCSP X Domain} {σ : I.Assignment}
    (hσ : I.Satisfies σ) (S : Finset X) : I.SatisfiesOn S (restrictAssignment S σ) :=
  fun c hmem _ => hσ c hmem

/-- Restricting a partial assignment satisfying `I` on `T` to `S ⊆ T` satisfies `I` on `S`. -/
theorem SatisfiesOn.mono {I : TwoCSP X Domain} {S T : Finset X} (hST : S ⊆ T)
    {τ : PartialAssignment Domain T} (hτ : I.SatisfiesOn T τ) :
    I.SatisfiesOn S (restrictPartialAssignment hST τ) :=
  fun c hmem hc => hτ c hmem ⟨hST hc.1, hST hc.2⟩

/-- `I` admits an induced satisfiable variable subset of exact cardinality `s`. -/
@[expose]
def HasSatisfiableSubsetOfCard (I : TwoCSP X Domain) (s : ℕ) : Prop :=
  ∃ S : Finset X, S.card = s ∧ ∃ τ : PartialAssignment Domain S, I.SatisfiesOn S τ

/-- Decidability of `TwoCSP.HasSatisfiableSubsetOfCard`. -/
instance instDecidableHasSatisfiableSubsetOfCard [Fintype X] [DecidableEq X]
    [∀ x, Fintype (Domain x)] [∀ x, DecidableEq (Domain x)]
    (I : TwoCSP X Domain) (s : ℕ) : Decidable (I.HasSatisfiableSubsetOfCard s) :=
  decidable_of_iff
    (∃ S ∈ (Finset.univ : Finset X).powerset,
      S.card = s ∧ ∃ τ : ∀ x : S, Domain x.1, I.SatisfiesOn S τ)
    ⟨fun ⟨S, _, hcard, τ, hτ⟩ => ⟨S, hcard, τ, hτ⟩,
      fun ⟨S, hcard, τ, hτ⟩ =>
        ⟨S, Finset.mem_powerset.mpr (Finset.subset_univ S), hcard, τ, hτ⟩⟩

/-- Every satisfiable `TwoCSP` over a finite variable set `X` has a satisfiable induced subset of
every cardinality `s ≤ Fintype.card X`. -/
theorem IsSatisfiable.hasSatisfiableSubsetOfCard [Fintype X] {I : TwoCSP X Domain}
    (h : I.IsSatisfiable) {s : ℕ} (hs : s ≤ Fintype.card X) :
    I.HasSatisfiableSubsetOfCard s := by
  rcases h with ⟨σ, hσ⟩
  obtain ⟨S, -, hcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset X))
    (by simpa using hs)
  exact ⟨S, hcard, restrictAssignment S σ, hσ.satisfiesOn_restrictAssignment S⟩

/-- Over a finite variable set `X`, `I` has a satisfiable induced subset of cardinality
`Fintype.card X` if and only if `I` is globally satisfiable. -/
theorem hasSatisfiableSubsetOfCard_card_iff_isSatisfiable [Fintype X] (I : TwoCSP X Domain) :
    I.HasSatisfiableSubsetOfCard (Fintype.card X) ↔ I.IsSatisfiable := by
  refine ⟨fun ⟨S, hcard, τ, hτ⟩ => ?_, fun h => h.hasSatisfiableSubsetOfCard le_rfl⟩
  have hmem : ∀ x : X, x ∈ S := fun x => Finset.eq_univ_of_card S hcard ▸ Finset.mem_univ x
  exact ⟨fun x => τ ⟨x, hmem x⟩, fun c hc => hτ c hc ⟨hmem c.fst, hmem c.snd⟩⟩

/-- Multi-assignment satisfaction of all constraints in `I`. -/
@[expose]
def ListSatisfies (I : TwoCSP X Domain) (σ : MultiAssignment X Domain) : Prop :=
  ∀ c ∈ I.constraints, c.ListSatisfies σ

/-- Decidability of `TwoCSP.ListSatisfies`. -/
instance instDecidableListSatisfies [∀ x, DecidableEq (Domain x)]
    (I : TwoCSP X Domain) (σ : MultiAssignment X Domain) : Decidable (I.ListSatisfies σ) :=
  inferInstanceAs (Decidable (∀ c ∈ I.constraints, c.ListSatisfies σ))

end Basic

section FiniteAlphabet

variable {X : Type*} {Domain : X → Type*} [Fintype X]

/-- Maximum domain cardinality across all variables of `I` (`0` if `X` is empty). -/
@[expose]
def alphabetSize [∀ x, Fintype (Domain x)] (_ : TwoCSP X Domain) : ℕ :=
  Finset.univ.sup fun x : X => Fintype.card (Domain x)

/-- Every variable domain has cardinality at most `I.alphabetSize`. -/
theorem card_domain_le_alphabetSize [∀ x, Fintype (Domain x)] (I : TwoCSP X Domain) (x : X) :
    Fintype.card (Domain x) ≤ I.alphabetSize :=
  Finset.le_sup (f := fun y : X => Fintype.card (Domain y)) (Finset.mem_univ x)

/-- Universal-property characterization of `I.alphabetSize ≤ n`. -/
theorem alphabetSize_le_iff [∀ x, Fintype (Domain x)] {I : TwoCSP X Domain} {n : ℕ} :
    I.alphabetSize ≤ n ↔ ∀ x : X, Fintype.card (Domain x) ≤ n := by
  simp [alphabetSize]

/-- Worst-case `r`-list satisfaction of `I` by `σ`: `σ.maxCard ≤ r` and `I.ListSatisfies σ`. -/
@[expose]
def IsListSatisfying (I : TwoCSP X Domain) (r : ℕ) (σ : MultiAssignment X Domain) : Prop :=
  σ.maxCard ≤ r ∧ I.ListSatisfies σ

/-- Decidability of `TwoCSP.IsListSatisfying`. -/
instance instDecidableIsListSatisfying [∀ x, DecidableEq (Domain x)]
    (I : TwoCSP X Domain) (r : ℕ) (σ : MultiAssignment X Domain) :
    Decidable (I.IsListSatisfying r σ) :=
  inferInstanceAs (Decidable (σ.maxCard ≤ r ∧ I.ListSatisfies σ))

/-- Worst-case `r`-list satisfiability of `I`: existence of `σ` with `I.IsListSatisfying r σ`. -/
@[expose]
def IsListSatisfiable (I : TwoCSP X Domain) (r : ℕ) : Prop :=
  ∃ σ : MultiAssignment X Domain, I.IsListSatisfying r σ

/-- Decidability of `TwoCSP.IsListSatisfiable` over finite decidable variable and domain types. -/
instance instDecidableIsListSatisfiable [DecidableEq X]
    [∀ x, Fintype (Domain x)] [∀ x, DecidableEq (Domain x)]
    (I : TwoCSP X Domain) (r : ℕ) : Decidable (I.IsListSatisfiable r) :=
  inferInstanceAs (Decidable (∃ σ : MultiAssignment X Domain, I.IsListSatisfying r σ))

/-- Average `r`-list satisfaction of `I` by `σ`: `σ.totalCard ≤ r * |X|` and
`I.ListSatisfies σ`. -/
@[expose]
def IsAvgListSatisfying (I : TwoCSP X Domain) (r : ℝ) (σ : MultiAssignment X Domain) : Prop :=
  (σ.totalCard : ℝ) ≤ r * (Fintype.card X : ℝ) ∧ I.ListSatisfies σ

/-- Average `r`-list satisfiability of `I`: existence of `σ` with `I.IsAvgListSatisfying r σ`. -/
@[expose]
def IsAvgListSatisfiable (I : TwoCSP X Domain) (r : ℝ) : Prop :=
  ∃ σ : MultiAssignment X Domain, I.IsAvgListSatisfying r σ

/-- Every satisfiable `TwoCSP` is `r`-list satisfiable for all `1 ≤ r` via singleton lists. -/
theorem IsSatisfiable.isListSatisfiable {I : TwoCSP X Domain} (h : I.IsSatisfiable)
    {r : ℕ} (hr : 1 ≤ r) : I.IsListSatisfiable r := by
  rcases h with ⟨τ, hτ⟩
  exact ⟨fun x => {τ x}, Finset.sup_le fun x _ => by simpa using hr, fun c hc =>
    ⟨τ c.fst, Finset.mem_singleton_self _, τ c.snd, Finset.mem_singleton_self _, hτ c hc⟩⟩

/-- Monotonicity of `IsListSatisfiable` in the list-size bound `r`. -/
theorem IsListSatisfiable.mono {I : TwoCSP X Domain} {r₁ r₂ : ℕ}
    (h : I.IsListSatisfiable r₁) (hr : r₁ ≤ r₂) : I.IsListSatisfiable r₂ := by
  rcases h with ⟨σ, hmax, hsat⟩
  exact ⟨σ, hmax.trans hr, hsat⟩

/-- Over nonempty variable domains, `1`-list satisfiability is equivalent to ordinary
satisfiability. -/
theorem isListSatisfiable_one_iff_isSatisfiable [∀ x, Nonempty (Domain x)]
    (I : TwoCSP X Domain) : I.IsListSatisfiable 1 ↔ I.IsSatisfiable := by
  refine ⟨fun ⟨σ, hmax, hsat⟩ => ?_, fun h => h.isListSatisfiable le_rfl⟩
  classical
  let τ : I.Assignment := fun x =>
    if hx : (σ x).Nonempty then hx.choose else Classical.arbitrary (Domain x)
  refine ⟨τ, fun c hc => ?_⟩
  rcases hsat c hc with ⟨u, hu, v, hv, huv⟩
  have hne₁ : (σ c.fst).Nonempty := ⟨u, hu⟩
  have hne₂ : (σ c.snd).Nonempty := ⟨v, hv⟩
  have hτ₁ : τ c.fst = u := by
    simp only [τ, hne₁, ↓reduceDIte]
    exact Finset.card_le_one_iff.mp ((σ.card_le_maxCard c.fst).trans hmax) hne₁.choose_spec hu
  have hτ₂ : τ c.snd = v := by
    simp only [τ, hne₂, ↓reduceDIte]
    exact Finset.card_le_one_iff.mp ((σ.card_le_maxCard c.snd).trans hmax) hne₂.choose_spec hv
  simpa [BinaryConstraint.Satisfies, hτ₁, hτ₂] using huv

/-- Worst-case `r`-list satisfiability implies `r`-average-list satisfiability. -/
theorem IsListSatisfiable.isAvgListSatisfiable {I : TwoCSP X Domain} {r : ℕ}
    (h : I.IsListSatisfiable r) : I.IsAvgListSatisfiable (r : ℝ) := by
  rcases h with ⟨σ, hmax, hsat⟩
  have hnat : σ.totalCard ≤ r * Fintype.card X :=
    σ.totalCard_le_maxCard_mul_card.trans (Nat.mul_le_mul_right _ hmax)
  exact ⟨σ, by exact_mod_cast hnat, hsat⟩

/-- Monotonicity of `IsAvgListSatisfiable` in the real average list-size bound `r`. -/
theorem IsAvgListSatisfiable.mono {I : TwoCSP X Domain} {r₁ r₂ : ℝ}
    (h : I.IsAvgListSatisfiable r₁) (hr : r₁ ≤ r₂) : I.IsAvgListSatisfiable r₂ := by
  rcases h with ⟨σ, htot, hsat⟩
  exact ⟨σ, htot.trans (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)), hsat⟩

/-- When `I.alphabetSize ≤ r`, `r`-list satisfiability is equivalent to every constraint relation
being nonempty. -/
theorem isListSatisfiable_of_alphabetSize_le [∀ x, Fintype (Domain x)] {I : TwoCSP X Domain}
    {r : ℕ} (hα : I.alphabetSize ≤ r) :
    I.IsListSatisfiable r ↔ ∀ c ∈ I.constraints, c.rel.Nonempty := by
  refine ⟨fun ⟨_, _, hsat⟩ c hc => ?_,
    fun hne => ⟨fun _ => Finset.univ, Finset.sup_le fun x _ => ?_, fun c hc => ?_⟩⟩
  · rcases hsat c hc with ⟨u, -, v, -, huv⟩; exact ⟨(u, v), huv⟩
  · simpa using (I.card_domain_le_alphabetSize x).trans hα
  · rcases hne c hc with ⟨⟨u, v⟩, huv⟩
    exact ⟨u, Finset.mem_univ u, v, Finset.mem_univ v, huv⟩

private lemma countP_eq_sum_fin {α : Type*} (p : α → Bool) :
    ∀ l : List α, l.countP p = ∑ i : Fin l.length, if p l[i.1] then 1 else 0
  | [] => rfl
  | a :: as => by
    rw [List.countP_cons, countP_eq_sum_fin p as]
    have h := Fin.sum_univ_succ fun i : Fin (as.length + 1) =>
      if p (a :: as)[i.1] then 1 else 0
    simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ] at h
    exact (Nat.add_comm _ _).trans h.symm

/-- **$1/r^2$ List-Decoding Averaging Theorem**: if `I` has no self-loop constraints, nonempty
variable domains, `1 ≤ r`, and `I.IsListSatisfiable r`, then some single assignment `τ` satisfies
at least a `1 / r^2` fraction of the constraints (`I.constraints.length ≤ r^2 * I.numSatisfied τ`).
-/
theorem exists_assignment_numSatisfied_ge_of_isListSatisfiable
    [∀ x, DecidableEq (Domain x)] [∀ x, Nonempty (Domain x)] {I : TwoCSP X Domain} {r : ℕ}
    (hr : 1 ≤ r) (hloop : ∀ c ∈ I.constraints, c.fst ≠ c.snd) (hlist : I.IsListSatisfiable r) :
    ∃ τ : I.Assignment, I.constraints.length ≤ r ^ 2 * I.numSatisfied τ := by
  classical
  rcases hlist with ⟨σ, hmax, hsat⟩
  let L : ∀ x : X, Finset (Domain x) := fun x =>
    if (σ x).Nonempty then σ x else {Classical.arbitrary (Domain x)}
  have hL_sub : ∀ x : X, σ x ⊆ L x := fun x d hd => by
    have hne : (σ x).Nonempty := ⟨d, hd⟩; simp [L, hne, hd]
  have hL_ne : ∀ x : X, (L x).Nonempty := fun x => by
    dsimp only [L]; split_ifs with hne <;> [exact hne; exact Finset.singleton_nonempty _]
  have hL_le : ∀ x : X, (L x).card ≤ r := fun x => by
    dsimp only [L]
    split_ifs with hne <;> [exact (σ.card_le_maxCard x).trans hmax; simpa using hr]
  let B : X → Type _ := fun x => {d : Domain x // d ∈ L x}
  let Box : Type _ := ∀ x : X, B x
  let toAssign : Box → I.Assignment := fun β x => (β x).1
  have _ : Nonempty Box := ⟨fun x => ⟨(hL_ne x).choose, (hL_ne x).choose_spec⟩⟩
  have hper : ∀ i : Fin I.constraints.length, Fintype.card Box ≤
      r ^ 2 * ∑ β : Box, if decide (I.constraints[i.1].Satisfies (toAssign β)) then 1 else 0 := by
    intro i
    let c := I.constraints[i.1]
    have hc_mem : c ∈ I.constraints := List.getElem_mem i.2
    rcases hsat c hc_mem with ⟨u, hu, v, hv, huv⟩
    let u₀ : B c.fst := ⟨u, hL_sub c.fst hu⟩
    let v₀ : B c.snd := ⟨v, hL_sub c.snd hv⟩
    let s₂ : {x : X // x ≠ c.fst} := ⟨c.snd, (hloop c hc_mem).symm⟩
    let Rest := ∀ z : {y : {x : X // x ≠ c.fst} // y ≠ s₂}, B z.1.1
    let e : Box ≃ B c.fst × (B c.snd × Rest) := (Equiv.piSplitAt c.fst B).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.piSplitAt s₂ fun y => B y.1))
    have hcard_box : Fintype.card Box ≤ r ^ 2 * Fintype.card Rest := by
      have hc1 : Fintype.card (B c.fst) ≤ r := by
        simpa [B, Fintype.card_coe] using hL_le c.fst
      have hc2 : Fintype.card (B c.snd) ≤ r := by
        simpa [B, Fintype.card_coe] using hL_le c.snd
      rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod]
      exact (Nat.mul_le_mul hc1 (Nat.mul_le_mul_right _ hc2)).trans_eq (by ring)
    let inj : Rest ↪ Box :=
      ⟨fun ρ => e.symm (u₀, (v₀, ρ)), fun _ _ h => by simpa using congrArg e h⟩
    have hinj_sat : ∀ ρ : Rest, c.Satisfies (toAssign (inj ρ)) := fun ρ => by
      have hev : e (inj ρ) = (u₀, (v₀, ρ)) := e.apply_symm_apply _
      have hfst : (inj ρ c.fst).1 = u := congrArg Subtype.val (congrArg Prod.fst hev)
      have hsnd : (inj ρ c.snd).1 = v := congrArg Subtype.val (congrArg (Prod.fst ∘ Prod.snd) hev)
      change ((inj ρ c.fst).1, (inj ρ c.snd).1) ∈ c.rel
      rwa [hfst, hsnd]
    have hsub_fin : Finset.univ.map inj ⊆
        Finset.univ.filter (fun β : Box => decide (c.Satisfies (toAssign β)) = true) :=
      fun β hβ => by
        rcases Finset.mem_map.mp hβ with ⟨ρ, -, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true (hinj_sat ρ)⟩
    have hrest_le : Fintype.card Rest ≤
        ∑ β : Box, if decide (c.Satisfies (toAssign β)) then 1 else 0 := by
      rw [← Finset.card_filter]
      exact (Fintype.card_eq_sum_ones.trans (by simp)).trans_le
        ((Finset.card_map inj).symm.trans_le (Finset.card_le_card hsub_fin))
    exact hcard_box.trans (Nat.mul_le_mul_left (r ^ 2) hrest_le)
  have hsum_total : I.constraints.length * Fintype.card Box ≤
      ∑ β : Box, r ^ 2 * I.numSatisfied (toAssign β) := calc
    I.constraints.length * Fintype.card Box =
        ∑ _i : Fin I.constraints.length, Fintype.card Box := by simp [Finset.sum_const]
    _ ≤ ∑ i : Fin I.constraints.length,
          r ^ 2 * ∑ β : Box,
            if decide (I.constraints[i.1].Satisfies (toAssign β)) then 1 else 0 :=
        Finset.sum_le_sum fun i _ => hper i
    _ = r ^ 2 * ∑ β : Box, ∑ i : Fin I.constraints.length,
          if decide (I.constraints[i.1].Satisfies (toAssign β)) then 1 else 0 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = ∑ β : Box, r ^ 2 * I.numSatisfied (toAssign β) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => by rw [numSatisfied, countP_eq_sum_fin]
  by_contra! hlt
  have hstrict : ∑ β : Box, r ^ 2 * I.numSatisfied (toAssign β) <
      ∑ _β : Box, I.constraints.length :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun β _ => hlt (toAssign β)
  have hcontra : ∑ _β : Box, I.constraints.length = I.constraints.length * Fintype.card Box := by
    simp [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

/-- Real-valued corollary of `exists_assignment_numSatisfied_ge_of_isListSatisfiable`: when
`0 < I.constraints.length`, some total assignment violates at most a `1 - 1 / r^2` fraction of the
constraints. -/
theorem exists_assignment_numViolated_div_le_of_isListSatisfiable
    [∀ x, DecidableEq (Domain x)] [∀ x, Nonempty (Domain x)] {I : TwoCSP X Domain} {r : ℕ}
    (hr : 1 ≤ r) (hlen : 0 < I.constraints.length)
    (hloop : ∀ c ∈ I.constraints, c.fst ≠ c.snd) (hlist : I.IsListSatisfiable r) :
    ∃ τ : I.Assignment,
      (I.numViolated τ : ℝ) / (I.constraints.length : ℝ) ≤ 1 - 1 / (r : ℝ) ^ 2 := by
  obtain ⟨τ, hτ⟩ := exists_assignment_numSatisfied_ge_of_isListSatisfiable hr hloop hlist
  exact ⟨τ, numViolated_div_le_of_length_le hr hlen hτ⟩

end FiniteAlphabet

end TwoCSP

/-! ### : Rectangular Binary Relations and Active-Rectangle Decomposition -/

/-- A finite binary relation `R : Finset (A × B)` is rectangular if it factors as an equality test
`π a = σ b` through some common codomain `C` and maps `π : A → C`, `σ : B → C`. -/
@[expose]
def IsRectangularRel {A : Type u} {B : Type v} (R : Finset (A × B)) : Prop :=
  ∃ (C : Type (max u v)) (π : A → C) (σ : B → C), ∀ a b, (a, b) ∈ R ↔ π a = σ b

/-- **Combinatorial Characterization of Rectangular Relations**: `R : Finset (A × B)` factors as
`π a = σ b` if and only if `R` is closed under completing $2 \times 2$ combinatorial rectangles:
whenever `(a, b), (a, b'), (a', b) ∈ R`, one also has `(a', b') ∈ R`. -/
theorem isRectangularRel_iff_forall_mem {A : Type u} {B : Type v} {R : Finset (A × B)} :
    IsRectangularRel R ↔
      ∀ a a' : A, ∀ b b' : B, (a, b) ∈ R → (a, b') ∈ R → (a', b) ∈ R → (a', b') ∈ R := by
  refine ⟨fun ⟨C, π, σ, hR⟩ a a' b b' hab hab' ha'b =>
    (hR a' b').mpr
      (((hR a' b).mp ha'b).trans (((hR a b).mp hab).symm.trans ((hR a b').mp hab'))),
    fun h4 => ?_⟩
  classical
  let C : Type (max u v) := ULift.{u} (Set B) ⊕ ULift.{max u v} Bool
  let π : A → C := fun a =>
    if ∃ b : B, (a, b) ∈ R then .inl ⟨{b' : B | (a, b') ∈ R}⟩ else .inr ⟨false⟩
  let σ : B → C := fun b =>
    if ∃ a : A, (a, b) ∈ R then .inl ⟨{b' : B | ∃ a' : A, (a', b) ∈ R ∧ (a', b') ∈ R}⟩
    else .inr ⟨true⟩
  refine ⟨C, π, σ, fun a b => ⟨fun hab => ?_, fun heq => ?_⟩⟩
  · dsimp only [π, σ]; rw [ite_eq_left ⟨b, hab⟩, ite_eq_left ⟨a, hab⟩]
    congr 2; ext b'
    exact ⟨fun hab' => ⟨a, hab, hab'⟩, fun ⟨a', ha'b, ha'b'⟩ => h4 a' a b b' ha'b ha'b' hab⟩
  · dsimp only [π, σ] at heq
    by_cases ha : ∃ b₀ : B, (a, b₀) ∈ R <;> by_cases hb : ∃ a₀ : A, (a₀, b) ∈ R <;>
      simp only [ha, hb, ↓reduceIte] at heq
    · injection heq with heq'; injection heq' with heq''
      rcases hb with ⟨a₀, ha₀b⟩
      have hb_mem : b ∈ {b' : B | ∃ a' : A, (a', b) ∈ R ∧ (a', b') ∈ R} := ⟨a₀, ha₀b, ha₀b⟩
      rwa [← heq''] at hb_mem
    · cases heq
    · cases heq
    · injection heq with heq'; injection heq' with heq''; cases heq''

/-- Decidability of `IsRectangularRel` over finite decidable domains. -/
instance instDecidableIsRectangularRel {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (R : Finset (A × B)) :
    Decidable (IsRectangularRel R) :=
  decidable_of_iff _ isRectangularRel_iff_forall_mem.symm

section RowNeighborhood

variable {A : Type u} {B : Type v} [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The row neighborhood `{b ∈ Finset.univ | (a, b) ∈ R}` of `a : A` under `R`. -/
def rowNeighborhood (R : Finset (A × B)) (a : A) : Finset B :=
  Finset.univ.filter fun b => (a, b) ∈ R

@[simp]
theorem mem_rowNeighborhood_iff {R : Finset (A × B)} {a : A} {b : B} :
    b ∈ rowNeighborhood R a ↔ (a, b) ∈ R := by
  simp [rowNeighborhood]

end RowNeighborhood

section ActiveRectangles

variable {A : Type u} {B : Type v} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Distinct nonempty row neighborhoods `{b : B | (a, b) ∈ R}` of `R : Finset (A × B)`. -/
def activeRectangles (R : Finset (A × B)) : Finset (Finset B) :=
  ((Finset.univ : Finset A).image (rowNeighborhood R)).filter Finset.Nonempty

theorem mem_activeRectangles_iff {R : Finset (A × B)} {S : Finset B} :
    S ∈ activeRectangles R ↔ (∃ a : A, rowNeighborhood R a = S) ∧ S.Nonempty := by
  simp [activeRectangles]

/-- For a rectangular relation `R`, distinct elements of `activeRectangles R` are pairwise
disjoint. -/
theorem pairwiseDisjoint_activeRectangles {R : Finset (A × B)} (hR : IsRectangularRel R) :
    (activeRectangles R : Set (Finset B)).PairwiseDisjoint id := by
  have h4 := isRectangularRel_iff_forall_mem.mp hR
  intro S₁ hS₁ S₂ hS₂ hne
  rcases mem_activeRectangles_iff.mp (Finset.mem_coe.mp hS₁) with ⟨⟨a₁, rfl⟩, -⟩
  rcases mem_activeRectangles_iff.mp (Finset.mem_coe.mp hS₂) with ⟨⟨a₂, rfl⟩, -⟩
  rw [Function.onFun, Finset.disjoint_left]
  intro b hb₁ hb₂
  apply hne
  ext b'
  simp only [id_eq, mem_rowNeighborhood_iff] at hb₁ hb₂ ⊢
  exact ⟨fun hb' => h4 a₁ a₂ b b' hb₁ hb' hb₂, fun hb' => h4 a₂ a₁ b b' hb₂ hb' hb₁⟩

/-- For a rectangular relation `R`, `(activeRectangles R).card ≤ min (Fintype.card A)
(Fintype.card B)`. -/
theorem card_activeRectangles_le_min {R : Finset (A × B)} (hR : IsRectangularRel R) :
    (activeRectangles R).card ≤ min (Fintype.card A) (Fintype.card B) := by
  refine le_min ((Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by simp))) ?_
  calc
    (activeRectangles R).card = ∑ _S ∈ activeRectangles R, 1 := by simp
    _ ≤ ∑ S ∈ activeRectangles R, S.card :=
        Finset.sum_le_sum fun S hS => (mem_activeRectangles_iff.mp hS).2.card_pos
    _ = ((activeRectangles R).biUnion id).card :=
        (Finset.card_biUnion (pairwiseDisjoint_activeRectangles hR)).symm
    _ ≤ Fintype.card B := Finset.card_le_univ _

/-- Characterization of membership `(a, b) ∈ R` via the unique active row neighborhood containing
`b`. -/
theorem mem_iff_exists_activeRectangles (R : Finset (A × B)) (a : A) (b : B) :
    (a, b) ∈ R ↔
      ∃ S ∈ activeRectangles R, Finset.univ.filter (fun b' : B => (a, b') ∈ R) = S ∧ b ∈ S := by
  refine ⟨fun hab => ⟨rowNeighborhood R a, ?_, rfl, by simpa using hab⟩,
    fun ⟨S, _, hS, hbS⟩ => ?_⟩
  · exact mem_activeRectangles_iff.mpr ⟨⟨a, rfl⟩, ⟨b, by simpa using hab⟩⟩
  · rw [← hS] at hbS; simpa using hbS

/-- Under `IsRectangularRel R`, for each active column block `S ∈ activeRectangles R`, row `a` has
exact neighborhood `S` if and only if `a` relates to at least one element of `S`. -/
theorem rowNeighborhood_eq_iff_exists_mem_of_mem_activeRectangles {R : Finset (A × B)}
    (hR : IsRectangularRel R) {S : Finset B} (hS : S ∈ activeRectangles R) (a : A) :
    rowNeighborhood R a = S ↔ ∃ b ∈ S, (a, b) ∈ R := by
  have h4 := isRectangularRel_iff_forall_mem.mp hR
  rcases mem_activeRectangles_iff.mp hS with ⟨⟨a₀, rfl⟩, ⟨b₀, hb₀⟩⟩
  refine ⟨fun heq => ?_, fun ⟨b, hb, hab⟩ => ?_⟩
  · rw [← heq] at hb₀; exact ⟨b₀, by simpa [heq] using hb₀, mem_rowNeighborhood_iff.mp hb₀⟩
  · have ha₀b : (a₀, b) ∈ R := mem_rowNeighborhood_iff.mp hb
    ext b'; simp only [mem_rowNeighborhood_iff]
    exact ⟨fun hab' => h4 a a₀ b b' hab hab' ha₀b, fun ha₀b' => h4 a₀ a b b' ha₀b ha₀b' hab⟩

end ActiveRectangles

section DiagonalLowerBound

/-- The finite diagonal equality relation `{(x, x) | x : α}` on a finite type `α`. -/
def diagRel (α : Type*) [Fintype α] : Finset (α × α) :=
  Finset.univ.map ⟨fun x : α => (x, x), fun _ _ h => (Prod.mk.inj h).1⟩

@[simp]
theorem mem_diagRel_iff {α : Type*} [Fintype α] {a b : α} :
    (a, b) ∈ diagRel α ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  rcases Finset.mem_map.mp h with ⟨x, -, hx⟩
  exact (Prod.mk.inj hx).1.symm.trans (Prod.mk.inj hx).2

/-- The diagonal relation `diagRel α` is rectangular. -/
theorem isRectangularRel_diagRel (α : Type u) [Fintype α] : IsRectangularRel (diagRel α) :=
  ⟨α, id, id, fun _ _ => mem_diagRel_iff⟩

/-- Any equality-test factorization `π a = σ b` of `diagRel α` forces `π` to be injective. -/
theorem injective_of_diagRel_factor {α : Type*} [Fintype α] {C : Type*}
    {π σ : α → C} (h : ∀ a b : α, (a, b) ∈ diagRel α ↔ π a = σ b) :
    Function.Injective π := fun a₁ a₂ heq =>
  mem_diagRel_iff.mp ((h a₁ a₂).mpr (heq.trans ((h a₂ a₂).mp (mem_diagRel_iff.mpr rfl))))

/-- Any finite codomain `C` factoring `diagRel α` as `π a = σ b` has `Fintype.card α ≤
Fintype.card C`, showing the active-rectangle bound cannot be compressed below `|α|`. -/
theorem card_le_of_diagRel_factor {α : Type*} [Fintype α] {C : Type*} [Fintype C]
    {π σ : α → C} (h : ∀ a b : α, (a, b) ∈ diagRel α ↔ π a = σ b) :
    Fintype.card α ≤ Fintype.card C :=
  Fintype.card_le_of_injective π (injective_of_diagRel_factor h)

end DiagonalLowerBound

section ListRectangularFactorization

/-- Explicit minimum-element row representative for a relation `rel : List (ℕ × ℕ)` on
`[0, m) × [0, n)`: returns the least `b < n` with `(a, b) ∈ rel`, or `n` if row `a` is inactive.
-/
@[expose]
def listRectRowRep (n : ℕ) (rel : List (ℕ × ℕ)) (a : ℕ) : ℕ :=
  ((List.range n).find? fun b => rel.any fun p => p.1 == a && p.2 == b).getD n

/-- Explicit minimum-element column representative for a relation `rel : List (ℕ × ℕ)` on
`[0, m) × [0, n)`: returns the least `b' < n` sharing an active row with `b`, or `n + 1` if column
`b` is inactive. -/
@[expose]
def listRectColRep (m n : ℕ) (rel : List (ℕ × ℕ)) (b : ℕ) : ℕ :=
  ((List.range n).find? fun b' =>
    (List.range m).any fun a' =>
      (rel.any fun p => p.1 == a' && p.2 == b) &&
        (rel.any fun p => p.1 == a' && p.2 == b')).getD (n + 1)

private lemma mem_rel_any_iff (rel : List (ℕ × ℕ)) (a b : ℕ) :
    (rel.any fun p => p.1 == a && p.2 == b) = true ↔ (a, b) ∈ rel := by
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun ⟨⟨x, y⟩, hmem, hx, hy⟩ => by dsimp only at hx hy; subst hx; subst hy; exact hmem,
    fun hmem => ⟨(a, b), hmem, rfl, rfl⟩⟩

private lemma find?_range_eq_some_iff {n k : ℕ} {P : ℕ → Bool} :
    (List.range n).find? P = some k ↔ k < n ∧ P k = true ∧ ∀ j < k, P j = false := by
  constructor
  · intro h
    rcases List.find?_eq_some_iff_append.mp h with ⟨hPk, as, bs, hrange, hbefore⟩
    have hlen : as.length < n := by
      have := congrArg List.length hrange
      simp at this
      omega
    have hk_eq : k = as.length := by
      have hidx : (List.range n)[as.length]? = some k := by
        rw [hrange, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
      rw [List.getElem?_range hlen] at hidx
      exact (Option.some.inj hidx).symm
    have has_eq : as = List.range k := by
      have htake := congrArg (List.take as.length) hrange
      rw [List.take_append_of_le_length le_rfl, List.take_length, List.take_range,
        min_eq_left hlen.le, ← hk_eq] at htake
      exact htake.symm
    refine ⟨hk_eq ▸ hlen, hPk, fun j hj => ?_⟩
    simpa using hbefore j (has_eq ▸ List.mem_range.mpr hj)
  · rintro ⟨hk, hPk, hmin⟩
    have hex : ∃ x ∈ List.range n, P x = true := ⟨k, List.mem_range.mpr hk, hPk⟩
    rcases Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex) with ⟨k', hk'⟩
    rcases List.find?_eq_some_iff_append.mp hk' with ⟨hPk', as, bs, hrange, hbefore⟩
    have hlen : as.length < n := by
      have := congrArg List.length hrange; simp at this; omega
    have hk'_eq : k' = as.length := by
      have hidx : (List.range n)[as.length]? = some k' := by
        rw [hrange, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
      rw [List.getElem?_range hlen] at hidx
      exact (Option.some.inj hidx).symm
    have has_eq : as = List.range k' := by
      have htake := congrArg (List.take as.length) hrange
      rw [List.take_append_of_le_length le_rfl, List.take_length, List.take_range,
        min_eq_left hlen.le, ← hk'_eq] at htake
      exact htake.symm
    have hle₁ : k' ≤ k := by
      by_contra! hlt
      have := hbefore k (has_eq ▸ List.mem_range.mpr hlt)
      rw [hPk] at this; cases this
    have hle₂ : k ≤ k' := by
      by_contra! hlt
      have := hmin k' hlt
      rw [hPk'] at this; cases this
    have : k' = k := le_antisymm hle₁ hle₂
    simpa [this] using hk'

/-- If `R : Finset (Fin m × Fin n)` is rectangular and matches `rel : List (ℕ × ℕ)` on
`Fin m × Fin n`, then `(a, b) ∈ R ↔ listRectRowRep n rel a = listRectColRep m n rel b`, and
active rows map strictly below `n`. -/
theorem listRectRowRep_eq_listRectColRep_iff {m n : ℕ} {rel : List (ℕ × ℕ)}
    {R : Finset (Fin m × Fin n)}
    (hR : IsRectangularRel R)
    (hrel : ∀ (a : Fin m) (b : Fin n), (a, b) ∈ R ↔ ((a : ℕ), (b : ℕ)) ∈ rel) :
    (∀ (a : Fin m) (b : Fin n),
      (a, b) ∈ R ↔ listRectRowRep n rel a.1 = listRectColRep m n rel b.1) ∧
    (∀ (a : Fin m) (b : Fin n), (a, b) ∈ R → listRectRowRep n rel a.1 < n) := by
  have h4 := isRectangularRel_iff_forall_mem.mp hR
  let PR : ℕ → ℕ → Bool := fun a b' => rel.any fun p => p.1 == a && p.2 == b'
  let PC : ℕ → ℕ → Bool := fun b b' =>
    (List.range m).any fun a' => PR a' b && PR a' b'
  have hPR : ∀ (a : Fin m) (b : Fin n), PR a.1 b.1 = true ↔ (a, b) ∈ R := fun a b =>
    (mem_rel_any_iff rel a.1 b.1).trans (hrel a b).symm
  have hPC : ∀ (b b' : Fin n), PC b.1 b'.1 = true ↔ ∃ a' : Fin m, (a', b) ∈ R ∧ (a', b') ∈ R := by
    intro b b'
    simp only [PC, List.any_eq_true, List.mem_range, Bool.and_eq_true]
    exact ⟨fun ⟨a', ha', h1, h2⟩ => ⟨⟨a', ha'⟩, (hPR ⟨a', ha'⟩ b).mp h1, (hPR ⟨a', ha'⟩ b').mp h2⟩,
      fun ⟨a', h1, h2⟩ => ⟨a'.1, a'.2, (hPR a' b).mpr h1, (hPR a' b').mpr h2⟩⟩
  have hrow_lt : ∀ (a : Fin m) (b : Fin n), (a, b) ∈ R → listRectRowRep n rel a.1 < n := by
    intro a b hab
    have hex : ∃ b' ∈ List.range n, PR a.1 b' = true :=
      ⟨b.1, List.mem_range.mpr b.2, (hPR a b).mpr hab⟩
    rcases Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex) with ⟨b₀, hb₀⟩
    have hlt := (find?_range_eq_some_iff.mp hb₀).1
    change (((List.range n).find? (PR a.1)).getD n) < n
    rw [hb₀]; simpa using hlt
  refine ⟨fun a b => ⟨fun hab => ?_, fun heq => ?_⟩, hrow_lt⟩
  · have hexR : ∃ b' ∈ List.range n, PR a.1 b' = true :=
      ⟨b.1, List.mem_range.mpr b.2, (hPR a b).mpr hab⟩
    rcases Option.isSome_iff_exists.mp (List.find?_isSome.mpr hexR) with ⟨b₀, hb₀⟩
    rcases find?_range_eq_some_iff.mp hb₀ with ⟨hb₀_lt, hb₀_PR, hb₀_min⟩
    have hPC_iff : ∀ j < n, PC b.1 j = PR a.1 j := fun j hj => by
      apply Bool.eq_iff_iff.mpr
      rw [hPC b ⟨j, hj⟩, hPR a ⟨j, hj⟩]
      exact ⟨fun ⟨a', ha'b, ha'j⟩ => h4 a' a b ⟨j, hj⟩ ha'b ha'j hab,
        fun haj => ⟨a, hab, haj⟩⟩
    have hb₀_findC : (List.range n).find? (PC b.1) = some b₀ :=
      find?_range_eq_some_iff.mpr
        ⟨hb₀_lt, (hPC_iff b₀ hb₀_lt).trans hb₀_PR, fun j hj =>
          (hPC_iff j (hj.trans hb₀_lt)).trans (hb₀_min j hj)⟩
    change ((List.range n).find? (PR a.1)).getD n = ((List.range n).find? (PC b.1)).getD (n + 1)
    rw [hb₀, hb₀_findC]; rfl
  · change ((List.range n).find? (PR a.1)).getD n = ((List.range n).find? (PC b.1)).getD (n + 1)
      at heq
    cases hRfind : (List.range n).find? (PR a.1) with
    | none =>
      rw [hRfind, Option.getD_none] at heq
      cases hCfind : (List.range n).find? (PC b.1) with
      | none => rw [hCfind, Option.getD_none] at heq; omega
      | some b₀ =>
        rw [hCfind, Option.getD_some] at heq
        have := (find?_range_eq_some_iff.mp hCfind).1
        omega
    | some b₀ =>
      rw [hRfind, Option.getD_some] at heq
      rcases find?_range_eq_some_iff.mp hRfind with ⟨hb₀_lt, hb₀_PR, -⟩
      cases hCfind : (List.range n).find? (PC b.1) with
      | none => rw [hCfind, Option.getD_none] at heq; omega
      | some b₁ =>
        rw [hCfind, Option.getD_some] at heq
        subst heq
        rcases find?_range_eq_some_iff.mp hCfind with ⟨-, hb₀_PC, -⟩
        have hab₀ : (a, ⟨b₀, hb₀_lt⟩) ∈ R := (hPR a ⟨b₀, hb₀_lt⟩).mp hb₀_PR
        rcases (hPC b ⟨b₀, hb₀_lt⟩).mp hb₀_PC with ⟨a', ha'b, ha'b₀⟩
        exact h4 a' a ⟨b₀, hb₀_lt⟩ b ha'b₀ ha'b hab₀

/-- Computing `listRectRowRep` is polynomial-time on unary inputs. -/
theorem computableInPolyTime_listRectRowRep {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {rel : γ → List (ℕ × ℕ)} {a : γ → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hrel : ComputableInPolyTime rel encIn (encList (encPair encUnary encUnary)))
    (ha : ComputableInPolyTime a encIn encUnary) :
    ComputableInPolyTime (fun x => listRectRowRep (n x) (rel x) (a x)) encIn encUnary := by
  unfold listRectRowRep
  polytime

/-- Computing `listRectColRep` is polynomial-time on unary inputs. -/
theorem computableInPolyTime_listRectColRep {γ : Type} {encIn : γ ↪ List Bool}
    {m n : γ → ℕ} {rel : γ → List (ℕ × ℕ)} {b : γ → ℕ}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hn : ComputableInPolyTime n encIn encUnary)
    (hrel : ComputableInPolyTime rel encIn (encList (encPair encUnary encUnary)))
    (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun x => listRectColRep (m x) (n x) (rel x) (b x)) encIn encUnary := by
  unfold listRectColRep
  polytime

end ListRectangularFactorization

namespace TwoCSP

/-- Predicate asserting that every constraint relation in `I.constraints` is rectangular. -/
@[expose]
def HasRectangularRelations {X : Type*} {Domain : X → Type*} (I : TwoCSP X Domain) : Prop :=
  ∀ c ∈ I.constraints, IsRectangularRel c.rel

/-- Decidability of `TwoCSP.HasRectangularRelations` over finite decidable domains. -/
instance instDecidableHasRectangularRelations {X : Type*} {Domain : X → Type*}
    [∀ x, Fintype (Domain x)] [∀ x, DecidableEq (Domain x)] (I : TwoCSP X Domain) :
    Decidable I.HasRectangularRelations :=
  inferInstanceAs (Decidable (∀ c ∈ I.constraints, IsRectangularRel c.rel))

end TwoCSP

end Cslib.Complexity
