/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module
-- upstream: candidate

public import Cslib.Probability.PMF
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Adaptive and Non-Adaptive Property Testers, Repetition Amplification, and Linear Reductions

This module develops foundational query-complexity and property-testing theory on finite domains
`D → α`, proved under standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. **Relative Hamming distance to a property**:
   `CslibFrontier.Computability.PropertyTesting.relHammingDist` and
   `CslibFrontier.Computability.PropertyTesting.relDistToSet`, achieving minimum relative Hamming
   distance on nonempty families over finite domains.
2. **Non-adaptive local testers, conjunction, and repetition amplification**:
   `CslibFrontier.Computability.PropertyTesting.QueryRule`,
   `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester`, conjunction
   `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.and`, and `k`-fold independent
   repetition `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.repeatAll`, amplifying
   one-sided soundness `ε · δ` to `δ / 2` in `k ≥ 1 / ε` repetitions.
3. **Adaptive query decision trees and testers**:
   `CslibFrontier.Computability.PropertyTesting.AdaptiveTree` and
   `CslibFrontier.Computability.PropertyTesting.AdaptiveTester`, together with the embedding of
   non-adaptive testers into adaptive testers of identical query budget and acceptance distribution.
4. **Ben-Sasson–Harsha–Raskhodnikova linear property testing reduction**: any one-sided adaptive
   `q`-query tester for a linear subspace `C : Submodule F (D → F)` over a finite field `F` reduces
   to a canonical one-sided non-adaptive `q`-query subspace-membership tester with at least the
   coset-averaged rejection probability.

## Main definitions

- `CslibFrontier.Computability.PropertyTesting.relHammingDist`,
  `CslibFrontier.Computability.PropertyTesting.relDistToSet`: normalized Hamming distance on `D → α`
  and minimum distance to a subset `C : Set (D → α)`.
- `CslibFrontier.Computability.PropertyTesting.QueryRule`,
  `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester`,
  `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.acceptProb`,
  `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.rejectProb`,
  `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.and`,
  `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.repeatAll`: non-adaptive `q`-query
  testers and their combinators.
- `CslibFrontier.Computability.PropertyTesting.AdaptiveTree`,
  `CslibFrontier.Computability.PropertyTesting.AdaptiveTree.eval`,
  `CslibFrontier.Computability.PropertyTesting.AdaptiveTester`,
  `CslibFrontier.Computability.PropertyTesting.AdaptiveTester.acceptProb`,
  `CslibFrontier.Computability.PropertyTesting.AdaptiveTester.rejectProb`,
  `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.toAdaptiveTester`: adaptive
  `q`-query decision-tree testers.
- `CslibFrontier.Computability.PropertyTesting.IsOneSidedNonAdaptiveTestable`,
  `CslibFrontier.Computability.PropertyTesting.IsOneSidedAdaptiveTestable`: `q`-query local
  testability predicates.

## Main results

- `CslibFrontier.Computability.PropertyTesting.exists_mem_relDistToSet_eq`: attainment of minimum
  relative distance on any nonempty property over a finite domain.
- `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.rejectProb_and_ge_left`,
  `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.rejectProb_and_ge_right`:
  soundness lower bounds for the conjunction of two testers.
- `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.acceptProb_repeatAll`,
  `CslibFrontier.Computability.PropertyTesting.NonAdaptiveTester.rejectProb_repeatAll_ge_half`:
  repetition amplification from `ε · δ` rejection probability to `δ / 2`.
- `CslibFrontier.Computability.PropertyTesting.IsOneSidedNonAdaptiveTestable.toAdaptive`: every
  non-adaptive one-sided `q`-locally testable family is adaptively `q`-locally testable.
- `CslibFrontier.Computability.PropertyTesting.exists_nonAdaptiveTester_of_adaptiveTester_submodule`
  and `CslibFrontier.Computability.PropertyTesting.isOneSidedAdaptiveTestable_submodule_iff`:
  the Ben-Sasson–Harsha–Raskhodnikova reduction of one-sided adaptive testers for linear subspaces
  over finite fields to one-sided non-adaptive subspace-membership testers, and the resulting
  equivalence of adaptive and non-adaptive one-sided `q`-local testability.

## Tags

property testing, locally testable codes, query complexity, adaptive vs non-adaptive, linear codes
-/

public section

noncomputable section

open Finset Function
open scoped BigOperators ENNReal

namespace CslibFrontier.Computability.PropertyTesting

universe u v

/-! ### 1. Normalized Hamming Distance on Finite Domains -/

section Distance

variable {D : Type u} {α : Type v} [Fintype D] [DecidableEq α]

/-- Relative Hamming distance `δ(f, g) = Pr_{x ~ D}[f(x) ≠ g(x)] ∈ [0, 1]` between two functions on
a finite domain `D`. -/
def relHammingDist (f g : D → α) : ℝ :=
  (hammingDist f g : ℝ) / (Fintype.card D : ℝ)

/-- Minimum relative Hamming distance `δ_C(f) = min_{g ∈ C} δ(f, g)` from `f` to a family
`C : Set (D → α)` (taking `0` if `C` is empty). -/
def relDistToSet (f : D → α) (C : Set (D → α)) : ℝ :=
  ((sInf (hammingDist f '' C) : ℕ) : ℝ) / (Fintype.card D : ℝ)

/-- Relative Hamming distance as normalized disagreement count. -/
theorem relHammingDist_eq_div (f g : D → α) :
    relHammingDist f g = (hammingDist f g : ℝ) / (Fintype.card D : ℝ) := by
  unfold relHammingDist; rfl

/-- Minimum relative distance to `C` as normalized infimum of Hamming distances. -/
theorem relDistToSet_eq_sInf_div (f : D → α) (C : Set (D → α)) :
    relDistToSet f C = ((sInf (hammingDist f '' C) : ℕ) : ℝ) / (Fintype.card D : ℝ) := by
  unfold relDistToSet; rfl

/-- Equality of `relDistToSet` across domains of equal cardinality and matching Hamming-distance
images. -/
theorem relDistToSet_congr {D₁ : Type*} {α₁ : Type*} {D₂ : Type*} {α₂ : Type*}
    [Fintype D₁] [DecidableEq α₁] [Fintype D₂] [DecidableEq α₂]
    {f₁ : D₁ → α₁} {C₁ : Set (D₁ → α₁)} {f₂ : D₂ → α₂} {C₂ : Set (D₂ → α₂)}
    (hset : hammingDist f₁ '' C₁ = hammingDist f₂ '' C₂)
    (hcard : Fintype.card D₁ = Fintype.card D₂) :
    relDistToSet f₁ C₁ = relDistToSet f₂ C₂ := by
  unfold relDistToSet
  rw [hset, hcard]

/-- Relative Hamming distance is nonnegative. -/
theorem relHammingDist_nonneg (f g : D → α) : 0 ≤ relHammingDist f g := by
  unfold relHammingDist; positivity

/-- Relative Hamming distance is at most `1`. -/
theorem relHammingDist_le_one [Nonempty D] (f g : D → α) : relHammingDist f g ≤ 1 := by
  unfold relHammingDist
  have hpos : (0 : ℝ) < (Fintype.card D : ℝ) := by exact_mod_cast Fintype.card_pos (α := D)
  rw [div_le_one hpos]
  exact_mod_cast hammingDist_le_card_fintype

/-- Relative Hamming distance is symmetric. -/
theorem relHammingDist_comm (f g : D → α) : relHammingDist f g = relHammingDist g f := by
  simp [relHammingDist, hammingDist_comm]

/-- Relative Hamming distance satisfies the triangle inequality. -/
theorem relHammingDist_triangle (f g h : D → α) :
    relHammingDist f h ≤ relHammingDist f g + relHammingDist g h := by
  unfold relHammingDist
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast hammingDist_triangle f g h

/-- Minimum relative distance to `C` is nonnegative. -/
theorem relDistToSet_nonneg (f : D → α) (C : Set (D → α)) : 0 ≤ relDistToSet f C := by
  unfold relDistToSet; positivity

/-- Minimum relative distance to a nonempty family `C` is at most `1`. -/
theorem relDistToSet_le_one [Nonempty D] (f : D → α) {C : Set (D → α)} (hC : C.Nonempty) :
    relDistToSet f C ≤ 1 := by
  obtain ⟨g, hg⟩ := hC
  have hle : sInf (hammingDist f '' C) ≤ hammingDist f g :=
    Nat.sInf_le ⟨g, hg, rfl⟩
  calc relDistToSet f C
    _ ≤ relHammingDist f g := by
        unfold relDistToSet relHammingDist
        exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg _)
    _ ≤ 1 := relHammingDist_le_one f g

/-- Minimum relative distance to `C` is bounded above by the distance to any `g ∈ C`. -/
theorem relDistToSet_le_of_mem (f : D → α) {C : Set (D → α)} {g : D → α} (hg : g ∈ C) :
    relDistToSet f C ≤ relHammingDist f g := by
  have hle : sInf (hammingDist f '' C) ≤ hammingDist f g := Nat.sInf_le ⟨g, hg, rfl⟩
  unfold relDistToSet relHammingDist
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg _)

/-- On a finite domain, minimum relative distance to any nonempty family `C` is attained by an
element `g ∈ C`. -/
theorem exists_mem_relDistToSet_eq (f : D → α) {C : Set (D → α)} (hC : C.Nonempty) :
    ∃ g ∈ C, relHammingDist f g = relDistToSet f C := by
  obtain ⟨g₀, hg₀⟩ := hC
  obtain ⟨g, hg, hEq⟩ := Nat.sInf_mem (s := hammingDist f '' C) ⟨hammingDist f g₀, g₀, hg₀, rfl⟩
  exact ⟨g, hg, by simp [relHammingDist, relDistToSet, hEq]⟩

/-- When `D` is nonempty and `C` is nonempty, `relDistToSet f C = 0` iff `f ∈ C`. -/
theorem relDistToSet_eq_zero_iff [Nonempty D] (f : D → α) {C : Set (D → α)} (hC : C.Nonempty) :
    relDistToSet f C = 0 ↔ f ∈ C := by
  have hpos : (0 : ℝ) < (Fintype.card D : ℝ) := by exact_mod_cast Fintype.card_pos (α := D)
  constructor
  · intro h0
    obtain ⟨g, hg, hEq⟩ := exists_mem_relDistToSet_eq f hC
    rw [← hEq, relHammingDist, div_eq_zero_iff] at h0
    rcases h0 with hdist | hcard
    · have hnat : hammingDist f g = 0 := by exact_mod_cast hdist
      rwa [hammingDist_eq_zero.mp hnat]
    · exact absurd hcard hpos.ne'
  · intro hf
    exact le_antisymm ((relDistToSet_le_of_mem f hf).trans_eq (by simp [relHammingDist]))
      (relDistToSet_nonneg f C)

end Distance

/-! ### 2. Non-Adaptive Local Testers, Conjunction, and Repetition Amplification -/

section NonAdaptive

/-- A deterministic non-adaptive `q`-query rule on `D → α`: specifies `q` query points in `D` and
a Boolean acceptance predicate on the `q` queried outputs. -/
@[ext]
structure QueryRule (D : Type u) (α : Type v) (q : ℕ) where
  /-- The `q` predetermined query points in `D`. -/
  queries : Fin q → D
  /-- Acceptance predicate on the `q`-tuple of queried values. -/
  decideView : (Fin q → α) → Bool

/-- Whether a deterministic query rule `R` accepts `f : D → α`. -/
@[expose]
def QueryRule.accepts {D : Type u} {α : Type v} {q : ℕ}
    (R : QueryRule D α q) (f : D → α) : Bool :=
  R.decideView (f ∘ R.queries)

@[simp]
theorem QueryRule.accepts_mk {D : Type u} {α : Type v} {q : ℕ}
    (queries : Fin q → D) (decideView : (Fin q → α) → Bool) (f : D → α) :
    (QueryRule.mk queries decideView).accepts f = decideView (f ∘ queries) := by
  unfold QueryRule.accepts; rfl

/-- Conjunction of a `q₁`-query rule and a `q₂`-query rule as a `(q₁ + q₂)`-query rule. -/
def QueryRule.and {D : Type u} {α : Type v} {q₁ q₂ : ℕ}
    (R₁ : QueryRule D α q₁) (R₂ : QueryRule D α q₂) : QueryRule D α (q₁ + q₂) where
  queries := Fin.append R₁.queries R₂.queries
  decideView v :=
    R₁.decideView (fun i ↦ v (Fin.castAdd q₂ i)) &&
      R₂.decideView (fun j ↦ v (Fin.natAdd q₁ j))

@[simp]
theorem QueryRule.accepts_and {D : Type u} {α : Type v} {q₁ q₂ : ℕ}
    (R₁ : QueryRule D α q₁) (R₂ : QueryRule D α q₂) (f : D → α) :
    (R₁.and R₂).accepts f = (R₁.accepts f && R₂.accepts f) := by
  simp only [QueryRule.accepts, QueryRule.and]
  congr 2 <;> ext i <;> simp [Function.comp_apply, Fin.append_left, Fin.append_right]

/-- A randomized non-adaptive `q`-query tester on `D → α`, modeled as a `PMF` over deterministic
`q`-query rules. -/
@[ext]
structure NonAdaptiveTester (D : Type u) (α : Type v) (q : ℕ) where
  /-- Probability distribution over deterministic `q`-query rules. -/
  dist : PMF (QueryRule D α q)

/-- Acceptance probability of a non-adaptive tester `T` on input `f : D → α`. -/
@[expose]
def NonAdaptiveTester.acceptProb {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) : ℝ :=
  ((T.dist.map fun R ↦ R.accepts f) true).toReal

/-- Rejection probability of a non-adaptive tester `T` on input `f : D → α`. -/
@[expose]
def NonAdaptiveTester.rejectProb {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) : ℝ :=
  ((T.dist.map fun R ↦ R.accepts f) false).toReal

/-- Acceptance probability of a non-adaptive tester is nonnegative. -/
theorem NonAdaptiveTester.acceptProb_nonneg {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) : 0 ≤ T.acceptProb f :=
  ENNReal.toReal_nonneg

/-- Rejection probability of a non-adaptive tester is nonnegative. -/
theorem NonAdaptiveTester.rejectProb_nonneg {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) : 0 ≤ T.rejectProb f :=
  ENNReal.toReal_nonneg

/-- Acceptance and rejection probabilities of a non-adaptive tester sum to `1`. -/
theorem NonAdaptiveTester.acceptProb_add_rejectProb {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) :
    T.acceptProb f + T.rejectProb f = 1 := by
  let p : PMF Bool := T.dist.map fun R ↦ R.accepts f
  have hsum : p true + p false = 1 := by
    have htsum : ∑' b : Bool, p b = 1 := p.tsum_coe
    rw [tsum_fintype, Fintype.sum_bool] at htsum
    exact htsum
  change (p true).toReal + (p false).toReal = 1
  rw [← ENNReal.toReal_add (p.apply_ne_top true) (p.apply_ne_top false), hsum,
    ENNReal.toReal_one]

/-- Rejection probability equals `1` minus acceptance probability. -/
theorem NonAdaptiveTester.rejectProb_eq_one_sub_acceptProb {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) :
    T.rejectProb f = 1 - T.acceptProb f := by
  linarith [T.acceptProb_add_rejectProb f]

/-- Acceptance probability of a non-adaptive tester is at most `1`. -/
theorem NonAdaptiveTester.acceptProb_le_one {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) : T.acceptProb f ≤ 1 := by
  linarith [T.acceptProb_add_rejectProb f, T.rejectProb_nonneg f]

/-- Rejection probability of a non-adaptive tester is at most `1`. -/
theorem NonAdaptiveTester.rejectProb_le_one {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) : T.rejectProb f ≤ 1 := by
  linarith [T.acceptProb_add_rejectProb f, T.acceptProb_nonneg f]

/-- `T.acceptProb f = 1` iff every rule in `T.dist.support` accepts `f`. -/
theorem NonAdaptiveTester.acceptProb_eq_one_iff {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) :
    T.acceptProb f = 1 ↔ ∀ R ∈ T.dist.support, R.accepts f = true := by
  let p : PMF Bool := T.dist.map fun R ↦ R.accepts f
  change (p true).toReal = 1 ↔ ∀ R ∈ T.dist.support, R.accepts f = true
  rw [← ENNReal.toReal_one,
    ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top true) ENNReal.one_ne_top,
    PMF.apply_eq_one_iff, PMF.support_map]
  constructor
  · intro hsupp R hR
    exact Set.mem_singleton_iff.mp (hsupp ▸ ⟨R, hR, rfl⟩)
  · intro hall
    ext b
    simp only [Set.mem_image, Set.mem_singleton_iff]
    refine ⟨fun ⟨R, hR, hb⟩ ↦ hb ▸ hall R hR, ?_⟩
    rintro rfl
    obtain ⟨R, hR⟩ := T.dist.support_nonempty
    exact ⟨R, hR, hall R hR⟩

/-- Acceptance probability of a deterministic tester `⟨PMF.pure R⟩` is `1` if `R` accepts and `0`
otherwise. -/
@[simp]
theorem NonAdaptiveTester.acceptProb_pure {D : Type u} {α : Type v} {q : ℕ}
    (R : QueryRule D α q) (f : D → α) :
    (⟨PMF.pure R⟩ : NonAdaptiveTester D α q).acceptProb f =
      if R.accepts f = true then 1 else 0 := by
  unfold NonAdaptiveTester.acceptProb
  rw [PMF.pure_map, PMF.pure_apply]
  cases R.accepts f <;> simp

/-- Acceptance probability of a tester pushed forward from a parameter distribution `p : PMF β`. -/
theorem NonAdaptiveTester.acceptProb_map_rule {β : Type*} {D : Type u} {α : Type v} {q : ℕ}
    (p : PMF β) (g : β → QueryRule D α q) (f : D → α) :
    (⟨p.map g⟩ : NonAdaptiveTester D α q).acceptProb f =
      ((p.map fun b ↦ (g b).accepts f) true).toReal := by
  unfold NonAdaptiveTester.acceptProb
  rw [PMF.map_comp]
  rfl

/-- Rejection probability of a tester pushed forward from a uniform finite parameter space `β`. -/
theorem NonAdaptiveTester.rejectProb_map_uniformOfFintype {β : Type*} [Fintype β] [Nonempty β]
    {D : Type u} {α : Type v} {q : ℕ}
    (g : β → QueryRule D α q) (f : D → α) :
    (⟨(Cslib.Probability.PMF.uniformOfFintype β).map g⟩ :
        NonAdaptiveTester D α q).rejectProb f =
      (1 / (Fintype.card β : ℝ)) *
        ∑ b : β, if (g b).accepts f = false then (1 : ℝ) else 0 := by
  unfold NonAdaptiveTester.rejectProb
  rw [PMF.map_comp, PMF.map_apply, tsum_fintype]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Function.comp_apply]
  rw [ENNReal.toReal_sum fun b _ ↦ by
    split_ifs
    · simp [Fintype.card_ne_zero]
    · simp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  by_cases h : (g b).accepts f = false <;> simp [h, eq_comm, ENNReal.toReal_inv, one_div]

/-- Rejection probability of a tester formed by binding a uniform finite choice `b : β` into
sub-testers `T b`. -/
theorem NonAdaptiveTester.rejectProb_bind_uniformOfFintype {β : Type*} [Fintype β] [Nonempty β]
    {D : Type u} {α : Type v} {q : ℕ}
    (T : β → NonAdaptiveTester D α q) (f : D → α) :
    (⟨(Cslib.Probability.PMF.uniformOfFintype β).bind fun b ↦ (T b).dist⟩ :
        NonAdaptiveTester D α q).rejectProb f =
      (1 / (Fintype.card β : ℝ)) * ∑ b : β, (T b).rejectProb f := by
  unfold NonAdaptiveTester.rejectProb
  rw [PMF.map_bind, PMF.bind_apply, tsum_fintype]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply]
  rw [ENNReal.toReal_sum fun b _ ↦ by
    refine ENNReal.mul_ne_top ?_ (PMF.apply_ne_top _ _)
    simp [Fintype.card_ne_zero], Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

/-- Finite-sum expansion of `T.rejectProb f` when the space of `q`-query rules is finite. -/
theorem NonAdaptiveTester.rejectProb_eq_sum_fintype {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) [Fintype (QueryRule D α q)] (f : D → α) :
    T.rejectProb f =
      ∑ R : QueryRule D α q,
        (T.dist R).toReal * (if R.accepts f = false then (1 : ℝ) else 0) := by
  unfold NonAdaptiveTester.rejectProb
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum fun R _ ↦ by
    split_ifs
    · exact T.dist.apply_ne_top R
    · simp]
  refine Finset.sum_congr rfl fun R _ ↦ ?_
  by_cases h : R.accepts f = false <;> simp [h, eq_comm]

/-- Independent conjunction of two non-adaptive testers, making `q₁ + q₂` queries and accepting iff
both component testers accept. -/
def NonAdaptiveTester.and {D : Type u} {α : Type v} {q₁ q₂ : ℕ}
    (T₁ : NonAdaptiveTester D α q₁) (T₂ : NonAdaptiveTester D α q₂) :
    NonAdaptiveTester D α (q₁ + q₂) where
  dist := T₁.dist.bind fun R₁ ↦ T₂.dist.map fun R₂ ↦ R₁.and R₂

/-- Acceptance probability of an independent conjunction factors as the product of the component
acceptance probabilities. -/
theorem NonAdaptiveTester.acceptProb_and {D : Type u} {α : Type v} {q₁ q₂ : ℕ}
    (T₁ : NonAdaptiveTester D α q₁) (T₂ : NonAdaptiveTester D α q₂) (f : D → α) :
    (T₁.and T₂).acceptProb f = T₁.acceptProb f * T₂.acceptProb f := by
  unfold NonAdaptiveTester.acceptProb NonAdaptiveTester.and
  have hmap : (T₁.dist.bind fun R₁ ↦ T₂.dist.map fun R₂ ↦ R₁.and R₂).map (fun R ↦ R.accepts f) =
      (T₁.dist.map fun R₁ ↦ R₁.accepts f).bind fun b₁ ↦
        (T₂.dist.map fun R₂ ↦ R₂.accepts f).map fun b₂ ↦ (b₁ && b₂) := by
    rw [PMF.map_bind, PMF.bind_map]
    refine congrArg T₁.dist.bind (funext fun R₁ ↦ ?_)
    dsimp only [Function.comp_apply]
    rw [PMF.map_comp, PMF.map_comp]
    congr 1
    ext R₂
    simp [Function.comp_apply]
  rw [hmap, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  have hfalse : ((T₂.dist.map fun R₂ ↦ R₂.accepts f).map fun b₂ ↦ (false && b₂)) true = 0 := by
    rw [PMF.map_apply]
    simp
  have htrue : ((T₂.dist.map fun R₂ ↦ R₂.accepts f).map fun b₂ ↦ (true && b₂)) true =
      (T₂.dist.map fun R₂ ↦ R₂.accepts f) true := by
    simp
  rw [hfalse, htrue, mul_zero, add_zero, ENNReal.toReal_mul]

/-- Rejection probability of `T₁.and T₂` is at least `T₁.rejectProb f`. -/
theorem NonAdaptiveTester.rejectProb_and_ge_left {D : Type u} {α : Type v} {q₁ q₂ : ℕ}
    (T₁ : NonAdaptiveTester D α q₁) (T₂ : NonAdaptiveTester D α q₂) (f : D → α) :
    T₁.rejectProb f ≤ (T₁.and T₂).rejectProb f := by
  rw [NonAdaptiveTester.rejectProb_eq_one_sub_acceptProb,
    NonAdaptiveTester.rejectProb_eq_one_sub_acceptProb,
    NonAdaptiveTester.acceptProb_and]
  have h1 := T₁.acceptProb_nonneg f
  have h2 := T₂.acceptProb_le_one f
  nlinarith

/-- Rejection probability of `T₁.and T₂` is at least `T₂.rejectProb f`. -/
theorem NonAdaptiveTester.rejectProb_and_ge_right {D : Type u} {α : Type v} {q₁ q₂ : ℕ}
    (T₁ : NonAdaptiveTester D α q₁) (T₂ : NonAdaptiveTester D α q₂) (f : D → α) :
    T₂.rejectProb f ≤ (T₁.and T₂).rejectProb f := by
  rw [NonAdaptiveTester.rejectProb_eq_one_sub_acceptProb,
    NonAdaptiveTester.rejectProb_eq_one_sub_acceptProb,
    NonAdaptiveTester.acceptProb_and]
  have h1 := T₁.acceptProb_le_one f
  have h2 := T₂.acceptProb_nonneg f
  nlinarith

/-- `k`-fold independent repetition of a `q`-query non-adaptive tester, making `k * q` queries and
accepting iff all `k` runs accept. -/
def NonAdaptiveTester.repeatAll {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) : ∀ k : ℕ, NonAdaptiveTester D α (k * q)
  | 0 => ⟨PMF.pure ⟨fun i ↦ Fin.elim0 (Fin.cast (Nat.zero_mul q) i), fun _ ↦ true⟩⟩
  | k + 1 =>
      let T' := (T.and (T.repeatAll k))
      ⟨(by rw [Nat.succ_mul, add_comm] : q + k * q = (k + 1) * q) ▸ T'.dist⟩

private lemma acceptProb_cast_queries {D : Type u} {α : Type v} {q₁ q₂ : ℕ} (h : q₁ = q₂)
    (d : PMF (QueryRule D α q₁)) (f : D → α) :
    (⟨h ▸ d⟩ : NonAdaptiveTester D α q₂).acceptProb f =
      (⟨d⟩ : NonAdaptiveTester D α q₁).acceptProb f := by
  subst h; rfl

/-- Acceptance probability of `k`-fold independent repetition is `(T.acceptProb f) ^ k`. -/
theorem NonAdaptiveTester.acceptProb_repeatAll {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (k : ℕ) (f : D → α) :
    (T.repeatAll k).acceptProb f = (T.acceptProb f) ^ k := by
  induction k with
  | zero =>
      unfold NonAdaptiveTester.repeatAll NonAdaptiveTester.acceptProb
      rw [PMF.pure_map]
      simp
  | succ k ih =>
      unfold NonAdaptiveTester.repeatAll
      rw [acceptProb_cast_queries, NonAdaptiveTester.acceptProb_and, ih, pow_succ']

/-- Repeating a one-sided tester `k` times with `1 / ε ≤ k` amplifies rejection probability
`≥ ε · δ` (for `0 ≤ δ ≤ 1` and `0 < ε`) to `≥ δ / 2`. -/
theorem NonAdaptiveTester.rejectProb_repeatAll_ge_half {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {k : ℕ} (hk : 1 / ε ≤ (k : ℝ)) {f : D → α} (hrej : ε * δ ≤ T.rejectProb f) :
    δ / 2 ≤ (T.repeatAll k).rejectProb f := by
  rw [NonAdaptiveTester.rejectProb_eq_one_sub_acceptProb,
    NonAdaptiveTester.acceptProb_repeatAll,
    show T.acceptProb f = 1 - T.rejectProb f by linarith [T.acceptProb_add_rejectProb f]]
  have h1 : (1 - T.rejectProb f) ^ k ≤ Real.exp (-(k : ℝ) * T.rejectProb f) := by
    calc (1 - T.rejectProb f) ^ k
      _ ≤ (Real.exp (-T.rejectProb f)) ^ k :=
          pow_le_pow_left₀ (by linarith [T.rejectProb_le_one f])
            (by linarith [Real.add_one_le_exp (-T.rejectProb f)]) k
      _ = Real.exp (-(k : ℝ) * T.rejectProb f) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hkε : 1 ≤ (k : ℝ) * ε := (div_le_iff₀ hε).mp hk
  have h2 : δ ≤ (k : ℝ) * T.rejectProb f := by
    calc δ = 1 * δ := (one_mul δ).symm
      _ ≤ ((k : ℝ) * ε) * δ := mul_le_mul_of_nonneg_right hkε hδ0
      _ = (k : ℝ) * (ε * δ) := mul_assoc _ _ _
      _ ≤ (k : ℝ) * T.rejectProb f := mul_le_mul_of_nonneg_left hrej (Nat.cast_nonneg k)
  have h3 : Real.exp (-(k : ℝ) * T.rejectProb f) ≤ Real.exp (-δ) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4 : Real.exp (-δ) ≤ 1 - δ / 2 := by
    have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
      (by linarith : 0 ≤ 1 - δ) hδ0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, mul_neg, mul_one, Real.exp_zero] at hconv
    have hexp_neg_one : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      have h2le : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      linarith
    nlinarith
  linarith

/-- Query budget monotonicity: any `q`-query non-adaptive tester on a nonempty domain `D` extends
to a `q'`-query non-adaptive tester for `q ≤ q'` with identical acceptance and rejection
probabilities. -/
def NonAdaptiveTester.padQueries {D : Type u} {α : Type v} [Nonempty D] {q q' : ℕ}
    (hq : q ≤ q') (T : NonAdaptiveTester D α q) : NonAdaptiveTester D α q' where
  dist := T.dist.map fun R ↦
    { queries := fun j ↦ if hj : j.1 < q then R.queries ⟨j.1, hj⟩ else Classical.arbitrary D
      decideView := fun v ↦ R.decideView (fun i ↦ v ⟨i.1, lt_of_lt_of_le i.2 hq⟩) }

@[simp]
theorem NonAdaptiveTester.acceptProb_padQueries {D : Type u} {α : Type v} [Nonempty D]
    {q q' : ℕ} (hq : q ≤ q') (T : NonAdaptiveTester D α q) (f : D → α) :
    (T.padQueries hq).acceptProb f = T.acceptProb f := by
  unfold NonAdaptiveTester.acceptProb NonAdaptiveTester.padQueries
  rw [PMF.map_comp]
  have hfg : ((fun R : QueryRule D α q' ↦ R.accepts f) ∘ fun R : QueryRule D α q ↦
      ({ queries := fun j ↦ if hj : j.1 < q then R.queries ⟨j.1, hj⟩ else Classical.arbitrary D
         decideView := fun v ↦ R.decideView (fun i ↦ v ⟨i.1, lt_of_lt_of_le i.2 hq⟩) } :
        QueryRule D α q')) = (fun R : QueryRule D α q ↦ R.accepts f) := by
    ext R
    simp only [Function.comp_apply, QueryRule.accepts]
    congr 1
    ext i
    simp [i.2]
  rw [hfg]

@[simp]
theorem NonAdaptiveTester.rejectProb_padQueries {D : Type u} {α : Type v} [Nonempty D]
    {q q' : ℕ} (hq : q ≤ q') (T : NonAdaptiveTester D α q) (f : D → α) :
    (T.padQueries hq).rejectProb f = T.rejectProb f := by
  rw [NonAdaptiveTester.rejectProb_eq_one_sub_acceptProb,
    NonAdaptiveTester.rejectProb_eq_one_sub_acceptProb,
    NonAdaptiveTester.acceptProb_padQueries]

/-- A family `C : Set (D → α)` is `q`-locally testable by a one-sided non-adaptive tester if there
exists `T : NonAdaptiveTester D α q` accepting every `f ∈ C` with probability `1` and rejecting
every `f ∉ C` with probability at least `relDistToSet f C / 2`. -/
@[expose]
def IsOneSidedNonAdaptiveTestable {D : Type u} {α : Type v} [Fintype D] [DecidableEq α]
    (C : Set (D → α)) (q : ℕ) : Prop :=
  ∃ T : NonAdaptiveTester D α q,
    (∀ f ∈ C, T.acceptProb f = 1) ∧
    (∀ f ∉ C, relDistToSet f C / 2 ≤ T.rejectProb f)

/-- One-sided non-adaptive local testability is monotone in the query budget `q ≤ q'`. -/
theorem IsOneSidedNonAdaptiveTestable.mono_queries {D : Type u} {α : Type v}
    [Fintype D] [Nonempty D] [DecidableEq α] {C : Set (D → α)} {q q' : ℕ}
    (h : IsOneSidedNonAdaptiveTestable C q) (hq : q ≤ q') :
    IsOneSidedNonAdaptiveTestable C q' := by
  obtain ⟨T, hcomp, hsound⟩ := h
  refine ⟨T.padQueries hq, fun f hf ↦ ?_, fun f hf ↦ ?_⟩
  · simp [hcomp f hf]
  · simpa using hsound f hf

end NonAdaptive

/-! ### 3. Adaptive Query Decision Trees and Testers -/

section Adaptive

/-- A deterministic adaptive query decision tree of depth at most `q` over oracle `D → α`. -/
inductive AdaptiveTree (D : Type u) (α : Type v) : ℕ → Type (max u v) where
  /-- Return Boolean decision `accept` without further queries. -/
  | leaf {q : ℕ} (accept : Bool) : AdaptiveTree D α q
  /-- Query `pos : D` and continue adaptively according to the oracle's answer in `α`. -/
  | query {q : ℕ} (pos : D) (next : α → AdaptiveTree D α q) : AdaptiveTree D α (q + 1)

/-- Evaluate an adaptive query tree `t` against oracle `f : D → α`. -/
def AdaptiveTree.eval {D : Type u} {α : Type v} :
    ∀ {q : ℕ}, AdaptiveTree D α q → (D → α) → Bool
  | _, .leaf b, _ => b
  | _, .query pos next, f => (next (f pos)).eval f

/-- Embed a deterministic non-adaptive `q`-query rule as a depth-`q` adaptive query tree. -/
def QueryRule.toAdaptiveTree {D : Type u} {α : Type v} :
    ∀ {q : ℕ}, QueryRule D α q → AdaptiveTree D α q
  | 0, R => .leaf (R.decideView Fin.elim0)
  | _ + 1, R =>
      .query (R.queries 0) fun a ↦
        QueryRule.toAdaptiveTree
          { queries := fun i ↦ R.queries i.succ
            decideView := fun v ↦ R.decideView (Fin.cons a v) }

@[simp]
theorem QueryRule.eval_toAdaptiveTree {D : Type u} {α : Type v} :
    ∀ {q : ℕ} (R : QueryRule D α q) (f : D → α),
      R.toAdaptiveTree.eval f = R.accepts f
  | 0, R, f => by
      simp only [QueryRule.toAdaptiveTree, AdaptiveTree.eval, QueryRule.accepts]
      congr 1
      ext i
      exact i.elim0
  | _ + 1, R, f => by
      simp only [QueryRule.toAdaptiveTree, AdaptiveTree.eval, QueryRule.eval_toAdaptiveTree,
        QueryRule.accepts]
      congr 1
      ext i
      cases i using Fin.cases <;> rfl

/-- A randomized adaptive `q`-query tester on `D → α`, modeled as a `PMF` over depth-`≤ q`
deterministic query decision trees. -/
@[ext]
structure AdaptiveTester (D : Type u) (α : Type v) (q : ℕ) where
  /-- Probability distribution over deterministic depth-`≤ q` query trees. -/
  dist : PMF (AdaptiveTree D α q)

/-- Acceptance probability of an adaptive tester `T` on input `f : D → α`. -/
def AdaptiveTester.acceptProb {D : Type u} {α : Type v} {q : ℕ}
    (T : AdaptiveTester D α q) (f : D → α) : ℝ :=
  ((T.dist.map fun t ↦ t.eval f) true).toReal

/-- Rejection probability of an adaptive tester `T` on input `f : D → α`. -/
def AdaptiveTester.rejectProb {D : Type u} {α : Type v} {q : ℕ}
    (T : AdaptiveTester D α q) (f : D → α) : ℝ :=
  ((T.dist.map fun t ↦ t.eval f) false).toReal

/-- Acceptance and rejection probabilities of an adaptive tester sum to `1`. -/
theorem AdaptiveTester.acceptProb_add_rejectProb {D : Type u} {α : Type v} {q : ℕ}
    (T : AdaptiveTester D α q) (f : D → α) :
    T.acceptProb f + T.rejectProb f = 1 := by
  let p : PMF Bool := T.dist.map fun t ↦ t.eval f
  have hsum : p true + p false = 1 := by
    have htsum : ∑' b : Bool, p b = 1 := p.tsum_coe
    rw [tsum_fintype, Fintype.sum_bool] at htsum
    exact htsum
  change (p true).toReal + (p false).toReal = 1
  rw [← ENNReal.toReal_add (p.apply_ne_top true) (p.apply_ne_top false), hsum,
    ENNReal.toReal_one]

/-- `T.acceptProb f = 1` iff every decision tree in `T.dist.support` accepts `f`. -/
theorem AdaptiveTester.acceptProb_eq_one_iff {D : Type u} {α : Type v} {q : ℕ}
    (T : AdaptiveTester D α q) (f : D → α) :
    T.acceptProb f = 1 ↔ ∀ t ∈ T.dist.support, t.eval f = true := by
  let p : PMF Bool := T.dist.map fun t ↦ t.eval f
  change (p true).toReal = 1 ↔ ∀ t ∈ T.dist.support, t.eval f = true
  rw [← ENNReal.toReal_one,
    ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top true) ENNReal.one_ne_top,
    PMF.apply_eq_one_iff, PMF.support_map]
  constructor
  · intro hsupp t ht
    exact Set.mem_singleton_iff.mp (hsupp ▸ ⟨t, ht, rfl⟩)
  · intro hall
    ext b
    simp only [Set.mem_image, Set.mem_singleton_iff]
    refine ⟨fun ⟨t, ht, hb⟩ ↦ hb ▸ hall t ht, ?_⟩
    rintro rfl
    obtain ⟨t, ht⟩ := T.dist.support_nonempty
    exact ⟨t, ht, hall t ht⟩

/-- Embed a non-adaptive `q`-query tester into an adaptive `q`-query tester. -/
def NonAdaptiveTester.toAdaptiveTester {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) : AdaptiveTester D α q where
  dist := T.dist.map QueryRule.toAdaptiveTree

@[simp]
theorem NonAdaptiveTester.acceptProb_toAdaptiveTester {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) :
    T.toAdaptiveTester.acceptProb f = T.acceptProb f := by
  unfold AdaptiveTester.acceptProb NonAdaptiveTester.toAdaptiveTester
    NonAdaptiveTester.acceptProb
  rw [PMF.map_comp]
  have hfg : ((fun t : AdaptiveTree D α q ↦ t.eval f) ∘
      (QueryRule.toAdaptiveTree : QueryRule D α q → AdaptiveTree D α q)) =
      (fun R : QueryRule D α q ↦ R.accepts f) := by
    ext R; simp
  rw [hfg]

@[simp]
theorem NonAdaptiveTester.rejectProb_toAdaptiveTester {D : Type u} {α : Type v} {q : ℕ}
    (T : NonAdaptiveTester D α q) (f : D → α) :
    T.toAdaptiveTester.rejectProb f = T.rejectProb f := by
  unfold AdaptiveTester.rejectProb NonAdaptiveTester.toAdaptiveTester
    NonAdaptiveTester.rejectProb
  rw [PMF.map_comp]
  have hfg : ((fun t : AdaptiveTree D α q ↦ t.eval f) ∘
      (QueryRule.toAdaptiveTree : QueryRule D α q → AdaptiveTree D α q)) =
      (fun R : QueryRule D α q ↦ R.accepts f) := by
    ext R; simp
  rw [hfg]

/-- A family `C : Set (D → α)` is `q`-locally testable (allowing adaptive `q`-query oracle access)
if there exists an adaptive `q`-query tester accepting every `f ∈ C` with probability `1` and
rejecting every `f ∉ C` with probability at least `relDistToSet f C / 2`. -/
@[expose]
def IsOneSidedAdaptiveTestable {D : Type u} {α : Type v} [Fintype D] [DecidableEq α]
    (C : Set (D → α)) (q : ℕ) : Prop :=
  ∃ T : AdaptiveTester D α q,
    (∀ f ∈ C, T.acceptProb f = 1) ∧
    (∀ f ∉ C, relDistToSet f C / 2 ≤ T.rejectProb f)

/-- Every one-sided non-adaptive `q`-locally testable family is adaptively `q`-locally testable. -/
theorem IsOneSidedNonAdaptiveTestable.toAdaptive {D : Type u} {α : Type v}
    [Fintype D] [DecidableEq α] {C : Set (D → α)} {q : ℕ}
    (h : IsOneSidedNonAdaptiveTestable C q) :
    IsOneSidedAdaptiveTestable C q := by
  obtain ⟨T, hcomp, hsound⟩ := h
  refine ⟨T.toAdaptiveTester, fun f hf ↦ ?_, fun f hf ↦ ?_⟩
  · simpa using hcomp f hf
  · simpa using hsound f hf

end Adaptive

/-! ### 4. Ben-Sasson–Harsha–Raskhodnikova Linear Property Testing Reduction -/

section LinearReduction

private def queriesAlong {D : Type u} {α : Type v} (d₀ : D) :
    ∀ {q : ℕ}, AdaptiveTree D α q → (D → α) → Fin q → D
  | _, .leaf _, _ => fun _ ↦ d₀
  | _, .query pos next, h => Fin.cons pos (queriesAlong d₀ (next (h pos)) h)

private lemma card_reject_coset_le_card_inconsistent {D : Type u} {F : Type v}
    [Field F] [Finite F] [DecidableEq F] (d₀ : D) :
    ∀ {q : ℕ} (t : AdaptiveTree D F q) (W : Submodule F (D → F)) [Fintype W]
      (c_base : D → F) (f : D → F),
      (∀ w : W, t.eval (c_base + w.1) = true) →
      ((Finset.univ.filter fun w : W ↦ t.eval (f + w.1) = false).card) ≤
        ((Finset.univ.filter fun w : W ↦
          ¬ ∃ w' : W,
            (c_base + w'.1) ∘ queriesAlong d₀ t (c_base + w.1) =
              f ∘ queriesAlong d₀ t (c_base + w.1)).card)
  | _, .leaf b, W, _, c_base, f, hcomp => by
      have hb : b = true := by
        simpa [AdaptiveTree.eval] using hcomp ⟨0, W.zero_mem⟩
      subst hb
      simp [AdaptiveTree.eval]
  | _ + 1, .query pos next, W, _, c_base, f, hcomp => by
      classical
      cases nonempty_fintype F
      by_cases hex : ∃ w₀ ∈ W, w₀ pos ≠ 0
      · obtain ⟨w₀, hw₀_mem, hw₀_ne⟩ := hex
        let u₀ : D → F := (w₀ pos)⁻¹ • w₀
        have hu₀_mem : u₀ ∈ W := W.smul_mem (w₀ pos)⁻¹ hw₀_mem
        have hu₀_pos : u₀ pos = 1 := by
          dsimp [u₀]; simp [inv_mul_cancel₀ hw₀_ne]
        let W' : Submodule F (D → F) :=
          { carrier := {w ∈ W | w pos = 0}
            add_mem' := fun {x y} hx hy ↦ ⟨W.add_mem hx.1 hy.1, by simp [hx.2, hy.2]⟩
            zero_mem' := ⟨W.zero_mem, rfl⟩
            smul_mem' := fun r {x} hx ↦ ⟨W.smul_mem r hx.1, by simp [hx.2]⟩ }
        let _ : Fintype W' :=
          Fintype.ofInjective (fun w' : W' ↦ (⟨w'.1, w'.2.1⟩ : W))
            (fun a b (h : (⟨a.1, a.2.1⟩ : W) = ⟨b.1, b.2.1⟩) ↦
              Subtype.ext (congrArg (Subtype.val : W → D → F) h))
        let e_lhs : F × W' ≃ W :=
          { toFun := fun ⟨a, w'⟩ ↦
              ⟨(a - f pos) • u₀ + w'.1, W.add_mem (W.smul_mem _ hu₀_mem) w'.2.1⟩
            invFun := fun w ↦
              (f pos + w.1 pos,
                ⟨w.1 - (w.1 pos) • u₀, W.sub_mem w.2 (W.smul_mem _ hu₀_mem), by
                  simp [hu₀_pos]⟩)
            left_inv := fun ⟨a, w'⟩ ↦ by
              have hw'0 : w'.1 pos = 0 := w'.2.2
              refine Prod.ext ?_ (Subtype.ext ?_)
              · simp [hu₀_pos, hw'0]
              · ext x
                simp [hu₀_pos, hw'0, sub_smul]
            right_inv := fun w ↦ Subtype.ext (by ext x; simp) }
        let e_rhs : F × W' ≃ W :=
          { toFun := fun ⟨a, w'⟩ ↦
              ⟨(a - c_base pos) • u₀ + w'.1, W.add_mem (W.smul_mem _ hu₀_mem) w'.2.1⟩
            invFun := fun w ↦
              (c_base pos + w.1 pos,
                ⟨w.1 - (w.1 pos) • u₀, W.sub_mem w.2 (W.smul_mem _ hu₀_mem), by
                  simp [hu₀_pos]⟩)
            left_inv := fun ⟨a, w'⟩ ↦ by
              have hw'0 : w'.1 pos = 0 := w'.2.2
              refine Prod.ext ?_ (Subtype.ext ?_)
              · simp [hu₀_pos, hw'0]
              · ext x
                simp [hu₀_pos, hw'0, sub_smul]
            right_inv := fun w ↦ Subtype.ext (by ext x; simp) }
        have hlhs_sum : (Finset.univ.filter fun w : W ↦
            (AdaptiveTree.query pos next).eval (f + w.1) = false).card =
            ∑ a : F, (Finset.univ.filter fun w' : W' ↦
              (next a).eval ((f + (a - f pos) • u₀) + w'.1) = false).card := by
          rw [Finset.card_eq_sum_ones]
          have h1 : (∑ x ∈ Finset.univ.filter (fun w : W ↦
              (AdaptiveTree.query pos next).eval (f + w.1) = false), 1) =
              ∑ p : F × W', if (AdaptiveTree.query pos next).eval (f + (e_lhs p).1) = false
                then 1 else 0 := by
            rw [Finset.sum_filter]
            exact (Fintype.sum_equiv e_lhs _ _ fun _ ↦ rfl).symm
          rw [h1, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          refine Finset.sum_congr rfl fun w' _ ↦ ?_
          have hpos_a : (f + (e_lhs (a, w')).1) pos = a := by
            have hw'0 : w'.1 pos = 0 := w'.2.2
            simp [e_lhs, hu₀_pos, hw'0]
          have hfun : f + (e_lhs (a, w')).1 = (f + (a - f pos) • u₀) + w'.1 := by
            ext x; simp [e_lhs, add_assoc]
          simp [AdaptiveTree.eval, hpos_a, hfun]
        have hrhs_sum : (Finset.univ.filter fun w : W ↦
            ¬ ∃ w' : W,
              (c_base + w'.1) ∘ queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + w.1) =
                f ∘ queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + w.1)).card =
            ∑ a : F, (Finset.univ.filter fun w' : W' ↦
              ¬ ∃ v' : W',
                ((c_base + (a - c_base pos) • u₀) + v'.1) ∘
                    queriesAlong d₀ (next a) ((c_base + (a - c_base pos) • u₀) + w'.1) =
                  (f + (a - f pos) • u₀) ∘
                    queriesAlong d₀ (next a) ((c_base + (a - c_base pos) • u₀) + w'.1)).card := by
          rw [Finset.card_eq_sum_ones]
          have h1 : (∑ x ∈ Finset.univ.filter (fun w : W ↦
              ¬ ∃ w' : W,
                (c_base + w'.1) ∘ queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + w.1) =
                  f ∘ queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + w.1)), 1) =
              ∑ p : F × W', if ¬ ∃ u_w : W,
                (c_base + u_w.1) ∘
                    queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + (e_rhs p).1) =
                  f ∘ queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + (e_rhs p).1)
                then 1 else 0 := by
            rw [Finset.sum_filter]
            exact (Fintype.sum_equiv e_rhs _ _ fun _ ↦ rfl).symm
          rw [h1, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          refine Finset.sum_congr rfl fun w' _ ↦ ?_
          have hpos_a : (c_base + (e_rhs (a, w')).1) pos = a := by
            have hw'0 : w'.1 pos = 0 := w'.2.2
            simp [e_rhs, hu₀_pos, hw'0]
          have hfun_c : c_base + (e_rhs (a, w')).1 =
              (c_base + (a - c_base pos) • u₀) + w'.1 := by
            ext x; simp [e_rhs, add_assoc]
          let Q := queriesAlong d₀ (next a) ((c_base + (a - c_base pos) • u₀) + w'.1)
          have hQ : queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + (e_rhs (a, w')).1) =
              Fin.cons pos Q := by
            simp [queriesAlong, hpos_a, hfun_c, Q]
          rw [hQ]
          have hequiv' : (∃ u_w : W, (c_base + u_w.1) ∘ Fin.cons pos Q = f ∘ Fin.cons pos Q) ↔
              (∃ v' : W', ((c_base + (a - c_base pos) • u₀) + v'.1) ∘ Q =
                (f + (a - f pos) • u₀) ∘ Q) := by
            constructor
            · rintro ⟨u_w, hu_w⟩
              have h0 : c_base pos + u_w.1 pos = f pos := by
                simpa [Function.comp_apply] using congrFun hu_w 0
              let v_vec : D → F := u_w.1 + (c_base pos - f pos) • u₀
              have hv_mem : v_vec ∈ W' := by
                refine ⟨W.add_mem u_w.2 (W.smul_mem _ hu₀_mem), ?_⟩
                dsimp [v_vec]
                simp only [hu₀_pos, mul_one]
                linear_combination h0
              refine ⟨⟨v_vec, hv_mem⟩, ?_⟩
              ext i
              have hi : c_base (Q i) + u_w.1 (Q i) = f (Q i) := by
                simpa [Function.comp_apply] using congrFun hu_w i.succ
              simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, v_vec]
              linear_combination hi
            · rintro ⟨v', hv'⟩
              let u_vec : D → F := ((f pos - c_base pos) • u₀) + v'.1
              have hu_mem : u_vec ∈ W := W.add_mem (W.smul_mem _ hu₀_mem) v'.2.1
              refine ⟨⟨u_vec, hu_mem⟩, ?_⟩
              ext i
              cases i using Fin.cases with
              | zero =>
                  have hv'0 : v'.1 pos = 0 := v'.2.2
                  simp only [Function.comp_apply, Fin.cons_zero, Pi.add_apply, Pi.smul_apply,
                    smul_eq_mul, u_vec, hu₀_pos, hv'0]
                  ring
              | succ j =>
                  have hj := congrFun hv' j
                  simp only [Function.comp_apply, Fin.cons_succ, Pi.add_apply, Pi.smul_apply,
                    smul_eq_mul, u_vec] at hj ⊢
                  linear_combination hj
          have hiff_neg :
              (¬ ∃ u_w : W, (c_base + u_w.1) ∘ Fin.cons pos Q = f ∘ Fin.cons pos Q) ↔
                ¬ ∃ v' : W', ((c_base + (a - c_base pos) • u₀) + v'.1) ∘ Q =
                  (f + (a - f pos) • u₀) ∘ Q := not_congr hequiv'
          by_cases hneg : ¬ ∃ u_w : W, (c_base + u_w.1) ∘ Fin.cons pos Q = f ∘ Fin.cons pos Q
          · have hneg' := hiff_neg.mp hneg
            dsimp only [Q] at hneg'
            simp only [eq_true hneg, eq_true hneg', ↓reduceIte]
          · have hneg' : ¬ ¬ ∃ v' : W', ((c_base + (a - c_base pos) • u₀) + v'.1) ∘ Q =
                (f + (a - f pos) • u₀) ∘ Q := mt hiff_neg.mpr hneg
            dsimp only [Q] at hneg'
            simp only [eq_false hneg, eq_false hneg', ↓reduceIte]
        rw [hlhs_sum, hrhs_sum]
        refine Finset.sum_le_sum fun a _ ↦ ?_
        refine card_reject_coset_le_card_inconsistent d₀ (next a) W'
          (c_base + (a - c_base pos) • u₀) (f + (a - f pos) • u₀) fun w' ↦ ?_
        have hpos_a : (c_base + (e_rhs (a, w')).1) pos = a := by
          have hw'0 : w'.1 pos = 0 := w'.2.2
          simp [e_rhs, hu₀_pos, hw'0]
        have hfun_c : c_base + (e_rhs (a, w')).1 =
            (c_base + (a - c_base pos) • u₀) + w'.1 := by
          ext x; simp [e_rhs, add_assoc]
        have hc := hcomp (e_rhs (a, w'))
        simpa [AdaptiveTree.eval, hpos_a, hfun_c] using hc
      · push Not at hex
        by_cases hfp : f pos = c_base pos
        · have hlhs : (Finset.univ.filter fun w : W ↦
              (AdaptiveTree.query pos next).eval (f + w.1) = false) =
              (Finset.univ.filter fun w : W ↦ (next (c_base pos)).eval (f + w.1) = false) := by
            ext w
            have hw0 : w.1 pos = 0 := hex w.1 w.2
            simp [AdaptiveTree.eval, hw0, hfp]
          have hrhs : (Finset.univ.filter fun w : W ↦
              ¬ ∃ w' : W,
                (c_base + w'.1) ∘ queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + w.1) =
                  f ∘ queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + w.1)) =
              (Finset.univ.filter fun w : W ↦
                ¬ ∃ w' : W,
                  (c_base + w'.1) ∘ queriesAlong d₀ (next (c_base pos)) (c_base + w.1) =
                    f ∘ queriesAlong d₀ (next (c_base pos)) (c_base + w.1)) := by
            ext w
            have hw0 : w.1 pos = 0 := hex w.1 w.2
            rw [Finset.mem_filter, Finset.mem_filter]
            refine and_congr_right fun _ ↦ not_congr ?_
            have hcw : (c_base + w.1) pos = c_base pos := by simp [hw0]
            dsimp only [queriesAlong]
            rw [hcw]
            constructor
            · rintro ⟨w', hw'⟩
              refine ⟨w', ?_⟩
              ext i
              simpa [Function.comp_apply] using congrFun hw' i.succ
            · rintro ⟨w', hw'⟩
              refine ⟨w', ?_⟩
              ext i
              cases i using Fin.cases with
              | zero =>
                  have hw'0 : w'.1 pos = 0 := hex w'.1 w'.2
                  simp [Function.comp_apply, hw'0, hfp]
              | succ j =>
                  simpa [Function.comp_apply] using congrFun hw' j
          rw [hlhs, hrhs]
          refine card_reject_coset_le_card_inconsistent d₀ (next (c_base pos)) W c_base f
            fun w ↦ ?_
          have hw0 : w.1 pos = 0 := hex w.1 w.2
          have hc := hcomp w
          simpa [AdaptiveTree.eval, hw0] using hc
        · have hrhs_all : (Finset.univ.filter fun w : W ↦
              ¬ ∃ w' : W,
                (c_base + w'.1) ∘ queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + w.1) =
                  f ∘ queriesAlong d₀ (AdaptiveTree.query pos next) (c_base + w.1)) =
              Finset.univ := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
            rintro ⟨w', hw'⟩
            have h0 : c_base pos + w'.1 pos = f pos := by
              simpa [queriesAlong, Function.comp_apply] using congrFun hw' 0
            rw [hex w'.1 w'.2, add_zero] at h0
            exact hfp h0.symm
          rw [hrhs_all]
          exact Finset.card_filter_le _ _

/-- **Ben-Sasson–Harsha–Raskhodnikova linear property testing reduction**
: any one-sided adaptive `q`-query tester `T` for a linear subspace
`C : Submodule F (D → F)` over a finite field `F` on a nonempty domain `D` reduces to a one-sided
non-adaptive `q`-query tester `T'` whose rules accept iff the queried restriction extends to `C` and
whose rejection probability on every `f : D → F` dominates the coset-averaged rejection probability
of `T`.
-/
theorem exists_nonAdaptiveTester_of_adaptiveTester_submodule
    {D : Type u} {F : Type v} [Nonempty D] [Field F] [Finite F]
    (C : Submodule F (D → F)) [Fintype C] {q : ℕ} (T : AdaptiveTester D F q)
    (hcomp : ∀ c ∈ C, T.acceptProb c = 1) :
    ∃ T' : NonAdaptiveTester D F q,
      (∀ R ∈ T'.dist.support, ∀ f : D → F,
        (∃ c ∈ C, c ∘ R.queries = f ∘ R.queries) → R.accepts f = true) ∧
      (∀ c ∈ C, T'.acceptProb c = 1) ∧
      (∀ f : D → F,
        (1 / (Fintype.card C : ℝ)) * ∑ c : C, T.rejectProb (f + c.1) ≤ T'.rejectProb f) := by
  classical
  obtain ⟨d₀⟩ := ‹Nonempty D›
  let ruleOf (t : AdaptiveTree D F q) (c : C) : QueryRule D F q :=
    { queries := queriesAlong d₀ t c.1
      decideView := fun v ↦ decide (∃ c' : C, c'.1 ∘ queriesAlong d₀ t c.1 = v) }
  let unifC : PMF C := Cslib.Probability.PMF.uniformOfFintype C
  let T' : NonAdaptiveTester D F q :=
    ⟨T.dist.bind fun t ↦ unifC.map fun c ↦ ruleOf t c⟩
  have hrule_sub : ∀ R ∈ T'.dist.support, ∀ f : D → F,
      (∃ c ∈ C, c ∘ R.queries = f ∘ R.queries) → R.accepts f = true := by
    intro R hR f ⟨c, hc, heq⟩
    simp only [T', PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hR
    obtain ⟨t, _, c₀, _, rfl⟩ := hR
    simp only [QueryRule.accepts, ruleOf, decide_eq_true_eq]
    exact ⟨⟨c, hc⟩, heq⟩
  have hT'_comp : ∀ c ∈ C, T'.acceptProb c = 1 := by
    intro c hc
    rw [NonAdaptiveTester.acceptProb_eq_one_iff]
    intro R hR
    exact hrule_sub R hR c ⟨c, hc, rfl⟩
  refine ⟨T', hrule_sub, hT'_comp, fun f ↦ ?_⟩
  have htree_comp : ∀ t ∈ T.dist.support, ∀ w : C, t.eval w.1 = true := by
    intro t ht w
    exact (T.acceptProb_eq_one_iff w.1).mp (hcomp w.1 w.2) t ht
  have hC_pos : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast Fintype.card_pos (α := C)
  have htsum_ne_top : (∑' t : AdaptiveTree D F q, T.dist t) ≠ ⊤ := by
    rw [T.dist.tsum_coe]
    exact ENNReal.one_ne_top
  have hlhs : (1 / (Fintype.card C : ℝ)) * ∑ c : C, T.rejectProb (f + c.1) =
      ∑' t : AdaptiveTree D F q, (T.dist t).toReal *
        (((Finset.univ.filter fun c : C ↦ t.eval (f + c.1) = false).card : ℝ) /
          (Fintype.card C : ℝ)) := by
    have hrej_c : ∀ c : C, T.rejectProb (f + c.1) =
        ∑' t : AdaptiveTree D F q,
          if t.eval (f + c.1) = false then (T.dist t).toReal else 0 := by
      intro c
      unfold AdaptiveTester.rejectProb
      rw [PMF.map_apply]
      rw [ENNReal.tsum_toReal_eq (by
        intro t; split_ifs
        · exact T.dist.apply_ne_top t
        · simp)]
      refine tsum_congr fun t ↦ ?_
      by_cases h : t.eval (f + c.1) = false <;> simp [h, eq_comm]
    simp_rw [hrej_c]
    have hsumm_c : ∀ c ∈ (Finset.univ : Finset C),
        Summable fun t : AdaptiveTree D F q ↦
          if t.eval (f + c.1) = false then (T.dist t).toReal else 0 := by
      intro c _
      refine Summable.of_nonneg_of_le (fun t ↦ by split_ifs <;> positivity)
        (fun t ↦ ?_) (ENNReal.summable_toReal htsum_ne_top)
      split_ifs
      · exact le_rfl
      · exact ENNReal.toReal_nonneg
    rw [← Summable.tsum_finsetSum hsumm_c, ← tsum_mul_left]
    refine tsum_congr fun t ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hrhs : T'.rejectProb f =
      ∑' t : AdaptiveTree D F q, (T.dist t).toReal *
        (((Finset.univ.filter fun c : C ↦
          ¬ ∃ c' : C,
            c'.1 ∘ queriesAlong d₀ t c.1 = f ∘ queriesAlong d₀ t c.1).card : ℝ) /
          (Fintype.card C : ℝ)) := by
    unfold NonAdaptiveTester.rejectProb
    have hmap : T'.dist.map (fun R ↦ R.accepts f) =
        T.dist.bind fun t ↦ (unifC.map fun c ↦ (ruleOf t c).accepts f) := by
      dsimp [T']
      rw [PMF.map_bind]
      congr 1
      ext t
      rw [PMF.map_comp]
      rfl
    rw [hmap, PMF.bind_apply]
    rw [ENNReal.tsum_toReal_eq (fun t ↦ ENNReal.mul_ne_top (T.dist.apply_ne_top t)
      (PMF.apply_ne_top _ false))]
    refine tsum_congr fun t ↦ ?_
    rw [ENNReal.toReal_mul]
    congr 1
    rw [PMF.map_apply, tsum_fintype]
    have hunif : ∀ c : C, unifC c = (Fintype.card C : ℝ≥0∞)⁻¹ :=
      fun c ↦ Cslib.Probability.PMF.uniformOfFintype_apply c
    have hsum_c : (∑ a : C,
        @ite ℝ≥0∞ (false = (ruleOf t a).accepts f) (Classical.propDecidable _) (unifC a) 0) =
        ((Finset.univ.filter fun c : C ↦
          ¬ ∃ c' : C, c'.1 ∘ queriesAlong d₀ t c.1 = f ∘ queriesAlong d₀ t c.1).card : ℝ≥0∞) *
        (Fintype.card C : ℝ≥0∞)⁻¹ := by
      trans (∑ c ∈ Finset.univ.filter (fun c : C ↦
          ¬ ∃ c' : C, c'.1 ∘ queriesAlong d₀ t c.1 = f ∘ queriesAlong d₀ t c.1),
          (Fintype.card C : ℝ≥0∞)⁻¹)
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        have hacc : (false = (ruleOf t c).accepts f) ↔
            ¬ ∃ c' : C, c'.1 ∘ queriesAlong d₀ t c.1 = f ∘ queriesAlong d₀ t c.1 := by
          simp [ruleOf, QueryRule.accepts, eq_comm]
        by_cases hc : ∃ c' : C, c'.1 ∘ queriesAlong d₀ t c.1 = f ∘ queriesAlong d₀ t c.1
        · have hnot_neg : ¬ ¬ ∃ c' : C,
              c'.1 ∘ queriesAlong d₀ t c.1 = f ∘ queriesAlong d₀ t c.1 := not_not.mpr hc
          have hc' : ¬ (false = (ruleOf t c).accepts f) := mt hacc.mp hnot_neg
          simp only [eq_false hnot_neg, eq_false hc', ↓reduceIte]
        · have hc' : false = (ruleOf t c).accepts f := hacc.mpr hc
          simp only [eq_true hc, eq_true hc', ↓reduceIte, hunif c]
      · rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum_c, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, div_eq_mul_inv]
  rw [hlhs, hrhs]
  have hsumm₁ : Summable fun t : AdaptiveTree D F q ↦
      (T.dist t).toReal *
        (((Finset.univ.filter fun c : C ↦ t.eval (f + c.1) = false).card : ℝ) /
          (Fintype.card C : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity)
      (fun t ↦ ?_) (ENNReal.summable_toReal htsum_ne_top)
    have hle : (((Finset.univ.filter fun c : C ↦ t.eval (f + c.1) = false).card : ℝ) /
        (Fintype.card C : ℝ)) ≤ 1 :=
      (div_le_one hC_pos).mpr (by exact_mod_cast Finset.card_le_univ _)
    nlinarith [ENNReal.toReal_nonneg (a := T.dist t)]
  have hsumm₂ : Summable fun t : AdaptiveTree D F q ↦
      (T.dist t).toReal *
        (((Finset.univ.filter fun c : C ↦
          ¬ ∃ c' : C,
            c'.1 ∘ queriesAlong d₀ t c.1 = f ∘ queriesAlong d₀ t c.1).card : ℝ) /
          (Fintype.card C : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity)
      (fun t ↦ ?_) (ENNReal.summable_toReal htsum_ne_top)
    have hle : (((Finset.univ.filter fun c : C ↦
        ¬ ∃ c' : C, c'.1 ∘ queriesAlong d₀ t c.1 = f ∘ queriesAlong d₀ t c.1).card : ℝ) /
        (Fintype.card C : ℝ)) ≤ 1 :=
      (div_le_one hC_pos).mpr (by exact_mod_cast Finset.card_le_univ _)
    nlinarith [ENNReal.toReal_nonneg (a := T.dist t)]
  refine hsumm₁.tsum_le_tsum (fun t ↦ ?_) hsumm₂
  by_cases ht : t ∈ T.dist.support
  · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    refine div_le_div_of_nonneg_right ?_ hC_pos.le
    have hcard := card_reject_coset_le_card_inconsistent d₀ t C 0 f
      (fun w ↦ by simpa using htree_comp t ht w)
    simpa using (Nat.cast_le (α := ℝ)).mpr hcard
  · have h0 : T.dist t = 0 := (T.dist.apply_eq_zero_iff t).mpr ht
    simp [h0]

/-- Corollary: a linear subspace `C : Submodule F (D → F)` over a finite field `F` on a nonempty
finite domain `D` is adaptively `q`-locally testable if and only if it is non-adaptively `q`-locally
testable by a canonical subspace-membership tester. -/
theorem isOneSidedAdaptiveTestable_submodule_iff
    {D : Type u} {F : Type v} [Fintype D] [Nonempty D] [Field F] [Finite F] [DecidableEq F]
    (C : Submodule F (D → F)) (q : ℕ) :
    IsOneSidedAdaptiveTestable (C : Set (D → F)) q ↔
      IsOneSidedNonAdaptiveTestable (C : Set (D → F)) q := by
  classical
  cases nonempty_fintype F
  refine ⟨fun ⟨T, hcomp, hsound⟩ ↦ ?_, fun h ↦ h.toAdaptive⟩
  obtain ⟨T', _, hT'_comp, hT'_rej⟩ :=
    exists_nonAdaptiveTester_of_adaptiveTester_submodule C T hcomp
  refine ⟨T', hT'_comp, fun f hf ↦ ?_⟩
  have hC_pos : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast Fintype.card_pos (α := C)
  have hshift_not_mem : ∀ c : C, f + c.1 ∉ (C : Set (D → F)) := by
    intro c hmem
    have : f = (f + c.1) - c.1 := by abel
    rw [this] at hf
    exact hf (C.sub_mem hmem c.2)
  have hshift_dist : ∀ c : C,
      relDistToSet (f + c.1) (C : Set (D → F)) = relDistToSet f (C : Set (D → F)) := by
    intro c
    have himg : hammingDist (f + c.1) '' (C : Set (D → F)) =
        hammingDist f '' (C : Set (D → F)) := by
      ext d
      simp only [Set.mem_image, SetLike.mem_coe]
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine ⟨g - c.1, C.sub_mem hg c.2, ?_⟩
        simp only [hammingDist]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.sub_apply]
        exact not_congr ⟨fun h ↦ by linear_combination h, fun h ↦ by linear_combination h⟩
      · rintro ⟨g, hg, rfl⟩
        refine ⟨g + c.1, C.add_mem hg c.2, ?_⟩
        simp only [hammingDist]
        congr 1
        ext x
        simp
    unfold relDistToSet
    rw [himg]
  calc relDistToSet f (C : Set (D → F)) / 2
    _ = (1 / (Fintype.card C : ℝ)) *
          ∑ c : C, relDistToSet (f + c.1) (C : Set (D → F)) / 2 := by
        simp_rw [hshift_dist]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
    _ ≤ (1 / (Fintype.card C : ℝ)) * ∑ c : C, T.rejectProb (f + c.1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun c _ ↦ hsound (f + c.1) (hshift_not_mem c)
    _ ≤ T'.rejectProb f := hT'_rej f

end LinearReduction

end CslibFrontier.Computability.PropertyTesting
