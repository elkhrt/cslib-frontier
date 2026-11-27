/-
Copyright (c) 2026 The PanMath contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PanMath contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Abelian Embeddings, Universal Embedding Groups, CSPs, and Basic SDP Relaxations

This module develops the algebraic theory of Abelian embeddings of $3$-ary relations, universal
standard embedding groups (and their finiteness under non-$\mathbb{Z}$-embeddability), mildly
symmetric $3$-ary CSP predicate families, and the basic semidefinite programming relaxation of
Max-CSP instances under standard Lean axioms.

## Main definitions

* `CslibFrontier.Computability.Complexity.IsAbelianEmbedding`, `IsNonconstTriple`,
  `IsAbelianEmbeddable`, `HasIntEmbedding`, `IsStandardEmbedding`: Abelian and $(\mathbb{Z},+)$-
  embeddings of ternary subsets $A \subseteq \Sigma_1 \times \Sigma_2 \times \Sigma_3$.
* `CslibFrontier.Computability.Complexity.IsPairwiseConnected`: pairwise connectivity of the three
  bipartite coordinate projection graphs of $A$.
* `CslibFrontier.Computability.Complexity.UniversalEmbeddingGroup`: the universal Abelian group
  carrying all standard embeddings of $S$.
* `CslibFrontier.Computability.Complexity.CspInstance`, `assignmentVal`, `optVal`, `IsSatisfiable`,
  `IsMildlySymmetric`: weighted $3$-ary CSP instances and mildly symmetric predicate families.
* `CslibFrontier.Computability.Complexity.BasicSdpSolution`, `integralSdpSolution`: the basic SDP
  relaxation and integral solutions.

## Main results

* `CslibFrontier.Computability.Complexity.isPairwiseConnected_of_not_hasIntEmbedding`:
  any nonempty ternary subset without a $(\mathbb{Z},+)$-embedding has full marginal supports and
  is pairwise connected.
* `CslibFrontier.Computability.Complexity.universalEmbeddingGroup_universal`:
  universal factorization of standard embeddings through `UniversalEmbeddingGroup`.
* `CslibFrontier.Computability.Complexity.finite_universalEmbeddingGroup_of_not_hasIntEmbedding`:
  if $S$ is nonempty and has no $(\mathbb{Z},+)$-embedding, its universal standard embedding
  group is finite.
* `CslibFrontier.Computability.Complexity.combineSdpSolutions`: convex/tensor combination of two
  value-$1$ SDP solutions takes the union of local supports.
* `CslibFrontier.Computability.Complexity.gram_dimension_reduction`: any basic SDP solution on
  $N$ variables over alphabet $\Sigma$ admits an inner-product-preserving realization in
  dimension $|\Sigma| N + 1$.
-/

public section

open Finset BigOperators

namespace CslibFrontier.Computability.Complexity

section AbelianEmbeddings

variable {A₁ A₂ A₃ : Type*}

/-- Maps `σ₁, σ₂, σ₃` into an Abelian group `G` form an Abelian embedding of
`A ⊆ A₁ × A₂ × A₃` if `σ₁ a + σ₂ b + σ₃ c = 0` for all `(a, b, c) ∈ A`. -/
@[expose] def IsAbelianEmbedding {G : Type*} [AddCommGroup G] (A : Set (A₁ × A₂ × A₃))
    (σ₁ : A₁ → G) (σ₂ : A₂ → G) (σ₃ : A₃ → G) : Prop :=
  ∀ x ∈ A, σ₁ x.1 + σ₂ x.2.1 + σ₃ x.2.2 = 0

lemma IsAbelianEmbedding.apply {G : Type*} [AddCommGroup G] {A : Set (A₁ × A₂ × A₃)}
    {σ₁ : A₁ → G} {σ₂ : A₂ → G} {σ₃ : A₃ → G}
    (h : IsAbelianEmbedding A σ₁ σ₂ σ₃) {x : A₁ × A₂ × A₃} (hx : x ∈ A) :
    σ₁ x.1 + σ₂ x.2.1 + σ₃ x.2.2 = 0 :=
  h x hx

lemma isAbelianEmbedding_iff {G : Type*} [AddCommGroup G] (A : Set (A₁ × A₂ × A₃))
    (σ₁ : A₁ → G) (σ₂ : A₂ → G) (σ₃ : A₃ → G) :
    IsAbelianEmbedding A σ₁ σ₂ σ₃ ↔ ∀ x ∈ A, σ₁ x.1 + σ₂ x.2.1 + σ₃ x.2.2 = 0 :=
  Iff.rfl

/-- At least one of `σ₁, σ₂, σ₃` is nonconstant. -/
@[expose] def IsNonconstTriple {G : Type*} (σ₁ : A₁ → G) (σ₂ : A₂ → G) (σ₃ : A₃ → G) : Prop :=
  (∃ a b : A₁, σ₁ a ≠ σ₁ b) ∨ (∃ a b : A₂, σ₂ a ≠ σ₂ b) ∨ (∃ a b : A₃, σ₃ a ≠ σ₃ b)

/-- `A` is Abelianly embeddable if it admits a nonconstant Abelian embedding into some Abelian
group `G` (equivalently in the same universe as the alphabets). -/
@[expose] def IsAbelianEmbeddable (A : Set (A₁ × A₂ × A₃)) : Prop :=
  ∃ (G : Type) (_ : AddCommGroup G) (σ₁ : A₁ → G) (σ₂ : A₂ → G) (σ₃ : A₃ → G),
    IsAbelianEmbedding A σ₁ σ₂ σ₃ ∧ IsNonconstTriple σ₁ σ₂ σ₃

/-- `A` admits a `(ℤ, +)`-embedding if it has a nonconstant Abelian embedding into `ℤ`. -/
@[expose] def HasIntEmbedding (A : Set (A₁ × A₂ × A₃)) : Prop :=
  ∃ (σ₁ : A₁ → ℤ) (σ₂ : A₂ → ℤ) (σ₃ : A₃ → ℤ),
    IsAbelianEmbedding A σ₁ σ₂ σ₃ ∧ IsNonconstTriple σ₁ σ₂ σ₃

/-- A standard embedding `((σ₁, σ₂, σ₃), g)` of `S` anchored at `(w₁, w₂, w₃)` sends
`w_j ↦ 0` and satisfies `σ₁ a + σ₂ b + σ₃ c = g` for all `(a, b, c) ∈ S`. -/
@[expose] def IsStandardEmbedding {G : Type*} [AddCommGroup G]
    (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) (S : Set (A₁ × A₂ × A₃))
    (σ₁ : A₁ → G) (σ₂ : A₂ → G) (σ₃ : A₃ → G) (g : G) : Prop :=
  σ₁ w₁ = 0 ∧ σ₂ w₂ = 0 ∧ σ₃ w₃ = 0 ∧ ∀ x ∈ S, σ₁ x.1 + σ₂ x.2.1 + σ₃ x.2.2 = g

/-- Non-`(ℤ, +)`-embeddability is monotone upward in the relation `A`. -/
lemma not_hasIntEmbedding_mono {A B : Set (A₁ × A₂ × A₃)} (hAB : A ⊆ B)
    (hA : ¬ HasIntEmbedding A) : ¬ HasIntEmbedding B := by
  rintro ⟨σ₁, σ₂, σ₃, hB, hnc⟩
  exact hA ⟨σ₁, σ₂, σ₃, fun x hx ↦ hB x (hAB hx), hnc⟩

/-- Converting any Abelian embedding into a standard embedding by affine shifting. -/
lemma isStandardEmbedding_shift {G : Type*} [AddCommGroup G]
    {A : Set (A₁ × A₂ × A₃)} {σ₁ : A₁ → G} {σ₂ : A₂ → G} {σ₃ : A₃ → G}
    (h : IsAbelianEmbedding A σ₁ σ₂ σ₃) (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) :
    IsStandardEmbedding w₁ w₂ w₃ A
      (fun a ↦ σ₁ a - σ₁ w₁) (fun b ↦ σ₂ b - σ₂ w₂) (fun c ↦ σ₃ c - σ₃ w₃)
      (-(σ₁ w₁ + σ₂ w₂ + σ₃ w₃)) := by
  refine ⟨sub_self _, sub_self _, sub_self _, fun x hx ↦ ?_⟩
  have hx0 := h x hx
  calc σ₁ x.1 - σ₁ w₁ + (σ₂ x.2.1 - σ₂ w₂) + (σ₃ x.2.2 - σ₃ w₃)
      = (σ₁ x.1 + σ₂ x.2.1 + σ₃ x.2.2) - (σ₁ w₁ + σ₂ w₂ + σ₃ w₃) := by abel
    _ = 0 - (σ₁ w₁ + σ₂ w₂ + σ₃ w₃) := by rw [hx0]
    _ = -(σ₁ w₁ + σ₂ w₂ + σ₃ w₃) := by abel

/-- Converting any standard embedding back into an Abelian embedding by absorbing `-g` into `σ₃`. -/
lemma isAbelianEmbedding_of_isStandardEmbedding {G : Type*} [AddCommGroup G]
    {w₁ : A₁} {w₂ : A₂} {w₃ : A₃} {S : Set (A₁ × A₂ × A₃)}
    {σ₁ : A₁ → G} {σ₂ : A₂ → G} {σ₃ : A₃ → G} {g : G}
    (h : IsStandardEmbedding w₁ w₂ w₃ S σ₁ σ₂ σ₃ g) :
    IsAbelianEmbedding S σ₁ σ₂ (fun c ↦ σ₃ c - g) := by
  intro x hx
  have h1 := h.2.2.2 x hx
  calc σ₁ x.1 + σ₂ x.2.1 + (σ₃ x.2.2 - g)
      = (σ₁ x.1 + σ₂ x.2.1 + σ₃ x.2.2) - g := by abel
    _ = g - g := by rw [h1]
    _ = 0 := sub_self g

/-- If `A` has no `(ℤ, +)`-embedding and is nonempty, every element of `A₁`, `A₂`, `A₃`
appears in the support of `A` (full marginal supports). -/
theorem full_marginal_of_not_hasIntEmbedding {A : Set (A₁ × A₂ × A₃)}
    (hne : A.Nonempty) (hno : ¬ HasIntEmbedding A) :
    (∀ a : A₁, ∃ b c, (a, b, c) ∈ A) ∧
    (∀ b : A₂, ∃ a c, (a, b, c) ∈ A) ∧
    (∀ c : A₃, ∃ a b, (a, b, c) ∈ A) := by
  classical
  obtain ⟨⟨a₀, b₀, c₀⟩, h₀⟩ := hne
  refine ⟨fun a ↦ ?_, fun b ↦ ?_, fun c ↦ ?_⟩
  · by_contra h
    push Not at h
    refine hno ⟨fun x ↦ if x = a then 1 else 0, fun _ ↦ 0, fun _ ↦ 0, ?_, ?_⟩
    · intro x hx
      have hne' : x.1 ≠ a := fun heq ↦ h x.2.1 x.2.2 (heq ▸ hx)
      simp [hne']
    · left; refine ⟨a, a₀, ?_⟩
      have hne' : a₀ ≠ a := fun heq ↦ h b₀ c₀ (heq ▸ h₀)
      simp [hne']
  · by_contra h
    push Not at h
    refine hno ⟨fun _ ↦ 0, fun y ↦ if y = b then 1 else 0, fun _ ↦ 0, ?_, ?_⟩
    · intro x hx
      have hne' : x.2.1 ≠ b := fun heq ↦ h x.1 x.2.2 (heq ▸ hx)
      simp [hne']
    · right; left; refine ⟨b, b₀, ?_⟩
      have hne' : b₀ ≠ b := fun heq ↦ h a₀ c₀ (heq ▸ h₀)
      simp [hne']
  · by_contra h
    push Not at h
    refine hno ⟨fun _ ↦ 0, fun _ ↦ 0, fun z ↦ if z = c then 1 else 0, ?_, ?_⟩
    · intro x hx
      have hne' : x.2.2 ≠ c := fun heq ↦ h x.1 x.2.1 (heq ▸ hx)
      simp [hne']
    · right; right; refine ⟨c, c₀, ?_⟩
      have hne' : c₀ ≠ c := fun heq ↦ h a₀ b₀ (heq ▸ h₀)
      simp [hne']

/-- Bipartite projection graph on `A₁ ⊕ A₂` induced by the `(1, 2)`-projection of `A`. -/
def projGraph12 (A : Set (A₁ × A₂ × A₃)) : SimpleGraph (A₁ ⊕ A₂) where
  Adj u v := match u, v with
    | Sum.inl a, Sum.inr b => ∃ c, (a, b, c) ∈ A
    | Sum.inr b, Sum.inl a => ∃ c, (a, b, c) ∈ A
    | _, _ => False
  symm := ⟨by rintro (a | b) (a' | b') h <;> exact h⟩
  loopless := ⟨by rintro (a | b) h <;> exact h⟩

/-- Bipartite projection graph on `A₁ ⊕ A₃` induced by the `(1, 3)`-projection of `A`. -/
def projGraph13 (A : Set (A₁ × A₂ × A₃)) : SimpleGraph (A₁ ⊕ A₃) where
  Adj u v := match u, v with
    | Sum.inl a, Sum.inr c => ∃ b, (a, b, c) ∈ A
    | Sum.inr c, Sum.inl a => ∃ b, (a, b, c) ∈ A
    | _, _ => False
  symm := ⟨by rintro (a | c) (a' | c') h <;> exact h⟩
  loopless := ⟨by rintro (a | c) h <;> exact h⟩

/-- Bipartite projection graph on `A₂ ⊕ A₃` induced by the `(2, 3)`-projection of `A`. -/
def projGraph23 (A : Set (A₁ × A₂ × A₃)) : SimpleGraph (A₂ ⊕ A₃) where
  Adj u v := match u, v with
    | Sum.inl b, Sum.inr c => ∃ a, (a, b, c) ∈ A
    | Sum.inr c, Sum.inl b => ∃ a, (a, b, c) ∈ A
    | _, _ => False
  symm := ⟨by rintro (b | c) (b' | c') h <;> exact h⟩
  loopless := ⟨by rintro (b | c) h <;> exact h⟩

/-- A ternary relation `A ⊆ A₁ × A₂ × A₃` is pairwise connected if all three bipartite projection
graphs on `A₁ ⊕ A₂`, `A₁ ⊕ A₃`, and `A₂ ⊕ A₃` are connected. -/
@[expose] def IsPairwiseConnected (A : Set (A₁ × A₂ × A₃)) : Prop :=
  (projGraph12 A).Connected ∧ (projGraph13 A).Connected ∧ (projGraph23 A).Connected

/-- Any nonempty ternary relation without a `(ℤ, +)`-embedding is automatically pairwise
connected! -/
theorem isPairwiseConnected_of_not_hasIntEmbedding {A : Set (A₁ × A₂ × A₃)}
    (hne : A.Nonempty) (hno : ¬ HasIntEmbedding A) : IsPairwiseConnected A := by
  classical
  obtain ⟨⟨a₀, b₀, c₀⟩, h₀⟩ := hne
  refine ⟨?_, ?_, ?_⟩
  · -- `projGraph12 A` is connected: if not, the component of `inl a₀` yields a `ℤ`-embedding.
    let : Nonempty (A₁ ⊕ A₂) := ⟨Sum.inl a₀⟩
    refine ⟨fun u v ↦ ?_⟩
    suffices hconn : ∀ w : A₁ ⊕ A₂, (projGraph12 A).Reachable (Sum.inl a₀) w from
      (hconn u).symm.trans (hconn v)
    intro w
    by_contra hnot
    let comp : Set (A₁ ⊕ A₂) := {u | (projGraph12 A).Reachable (Sum.inl a₀) u}
    refine hno ⟨fun a ↦ if Sum.inl a ∈ comp then 1 else 0,
      fun b ↦ if Sum.inr b ∈ comp then -1 else 0, fun _ ↦ 0, ?_, ?_⟩
    · intro x hx
      have hadj : (projGraph12 A).Adj (Sum.inl x.1) (Sum.inr x.2.1) := ⟨x.2.2, hx⟩
      have hiff : Sum.inl x.1 ∈ comp ↔ Sum.inr x.2.1 ∈ comp :=
        ⟨fun h ↦ h.trans hadj.reachable, fun h ↦ h.trans hadj.symm.reachable⟩
      by_cases h1 : Sum.inl x.1 ∈ comp
      · simp [h1, hiff.mp h1]
      · simp [h1, mt hiff.mpr h1]
    · cases w with
      | inl a =>
        left; refine ⟨a₀, a, ?_⟩
        have h1 : Sum.inl a₀ ∈ comp := SimpleGraph.Reachable.refl _
        have h2 : Sum.inl a ∉ comp := hnot
        simp [h1, h2]
      | inr b =>
        right; left; refine ⟨b₀, b, ?_⟩
        have h1 : Sum.inr b₀ ∈ comp :=
          SimpleGraph.Adj.reachable
            (show (projGraph12 A).Adj (Sum.inl a₀) (Sum.inr b₀) from ⟨c₀, h₀⟩)
        have h2 : Sum.inr b ∉ comp := hnot
        simp [h1, h2]
  · -- `projGraph13 A` is connected.
    let : Nonempty (A₁ ⊕ A₃) := ⟨Sum.inl a₀⟩
    refine ⟨fun u v ↦ ?_⟩
    suffices hconn : ∀ w : A₁ ⊕ A₃, (projGraph13 A).Reachable (Sum.inl a₀) w from
      (hconn u).symm.trans (hconn v)
    intro w
    by_contra hnot
    let comp : Set (A₁ ⊕ A₃) := {u | (projGraph13 A).Reachable (Sum.inl a₀) u}
    refine hno ⟨fun a ↦ if Sum.inl a ∈ comp then 1 else 0, fun _ ↦ 0,
      fun c ↦ if Sum.inr c ∈ comp then -1 else 0, ?_, ?_⟩
    · intro x hx
      have hadj : (projGraph13 A).Adj (Sum.inl x.1) (Sum.inr x.2.2) := ⟨x.2.1, hx⟩
      have hiff : Sum.inl x.1 ∈ comp ↔ Sum.inr x.2.2 ∈ comp :=
        ⟨fun h ↦ h.trans hadj.reachable, fun h ↦ h.trans hadj.symm.reachable⟩
      by_cases h1 : Sum.inl x.1 ∈ comp
      · simp [h1, hiff.mp h1]
      · simp [h1, mt hiff.mpr h1]
    · cases w with
      | inl a =>
        left; refine ⟨a₀, a, ?_⟩
        have h1 : Sum.inl a₀ ∈ comp := SimpleGraph.Reachable.refl _
        have h2 : Sum.inl a ∉ comp := hnot
        simp [h1, h2]
      | inr c =>
        right; right; refine ⟨c₀, c, ?_⟩
        have h1 : Sum.inr c₀ ∈ comp :=
          SimpleGraph.Adj.reachable
            (show (projGraph13 A).Adj (Sum.inl a₀) (Sum.inr c₀) from ⟨b₀, h₀⟩)
        have h2 : Sum.inr c ∉ comp := hnot
        simp [h1, h2]
  · -- `projGraph23 A` is connected.
    let : Nonempty (A₂ ⊕ A₃) := ⟨Sum.inl b₀⟩
    refine ⟨fun u v ↦ ?_⟩
    suffices hconn : ∀ w : A₂ ⊕ A₃, (projGraph23 A).Reachable (Sum.inl b₀) w from
      (hconn u).symm.trans (hconn v)
    intro w
    by_contra hnot
    let comp : Set (A₂ ⊕ A₃) := {u | (projGraph23 A).Reachable (Sum.inl b₀) u}
    refine hno ⟨fun _ ↦ 0, fun b ↦ if Sum.inl b ∈ comp then 1 else 0,
      fun c ↦ if Sum.inr c ∈ comp then -1 else 0, ?_, ?_⟩
    · intro x hx
      have hadj : (projGraph23 A).Adj (Sum.inl x.2.1) (Sum.inr x.2.2) := ⟨x.1, hx⟩
      have hiff : Sum.inl x.2.1 ∈ comp ↔ Sum.inr x.2.2 ∈ comp :=
        ⟨fun h ↦ h.trans hadj.reachable, fun h ↦ h.trans hadj.symm.reachable⟩
      by_cases h1 : Sum.inl x.2.1 ∈ comp
      · simp [h1, hiff.mp h1]
      · simp [h1, mt hiff.mpr h1]
    · cases w with
      | inl b =>
        right; left; refine ⟨b₀, b, ?_⟩
        have h1 : Sum.inl b₀ ∈ comp := SimpleGraph.Reachable.refl _
        have h2 : Sum.inl b ∉ comp := hnot
        simp [h1, h2]
      | inr c =>
        right; right; refine ⟨c₀, c, ?_⟩
        have h1 : Sum.inr c₀ ∈ comp :=
          SimpleGraph.Adj.reachable
            (show (projGraph23 A).Adj (Sum.inl b₀) (Sum.inr c₀) from ⟨a₀, h₀⟩)
        have h2 : Sum.inr c ∉ comp := hnot
        simp [h1, h2]

end AbelianEmbeddings

section UniversalEmbedding

variable {A₁ A₂ A₃ : Type*}

/-- Generating relation subgroup for the universal standard embedding group of `S`. -/
def universalRelSubgroup (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) (S : Set (A₁ × A₂ × A₃)) :
    AddSubgroup (FreeAbelianGroup ((A₁ ⊕ A₂) ⊕ A₃)) :=
  AddSubgroup.closure
    ({FreeAbelianGroup.of (Sum.inl (Sum.inl w₁)),
      FreeAbelianGroup.of (Sum.inl (Sum.inr w₂)),
      FreeAbelianGroup.of (Sum.inr w₃)} ∪
     {z | ∃ (x y : A₁ × A₂ × A₃), x ∈ S ∧ y ∈ S ∧
        z = (FreeAbelianGroup.of (Sum.inl (Sum.inl x.1)) +
             FreeAbelianGroup.of (Sum.inl (Sum.inr x.2.1)) +
             FreeAbelianGroup.of (Sum.inr x.2.2)) -
            (FreeAbelianGroup.of (Sum.inl (Sum.inl y.1)) +
             FreeAbelianGroup.of (Sum.inl (Sum.inr y.2.1)) +
             FreeAbelianGroup.of (Sum.inr y.2.2))})

/-- The universal standard embedding group `U(S)` anchored at `(w₁, w₂, w₃)`. -/
abbrev UniversalEmbeddingGroup (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) (S : Set (A₁ × A₂ × A₃)) : Type _ :=
  FreeAbelianGroup ((A₁ ⊕ A₂) ⊕ A₃) ⧸ universalRelSubgroup w₁ w₂ w₃ S

/-- Canonical first-coordinate embedding `A₁ → U(S)`. -/
def univEmbed₁ (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) (S : Set (A₁ × A₂ × A₃)) (a : A₁) :
    UniversalEmbeddingGroup w₁ w₂ w₃ S :=
  QuotientAddGroup.mk (FreeAbelianGroup.of (Sum.inl (Sum.inl a)))

/-- Canonical second-coordinate embedding `A₂ → U(S)`. -/
def univEmbed₂ (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) (S : Set (A₁ × A₂ × A₃)) (b : A₂) :
    UniversalEmbeddingGroup w₁ w₂ w₃ S :=
  QuotientAddGroup.mk (FreeAbelianGroup.of (Sum.inl (Sum.inr b)))

/-- Canonical third-coordinate embedding `A₃ → U(S)`. -/
def univEmbed₃ (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) (S : Set (A₁ × A₂ × A₃)) (c : A₃) :
    UniversalEmbeddingGroup w₁ w₂ w₃ S :=
  QuotientAddGroup.mk (FreeAbelianGroup.of (Sum.inr c))

/-- Canonical constant `g ∈ U(S)` of the universal standard embedding (for nonempty `S`). -/
noncomputable def univEmbedConst (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) (S : Set (A₁ × A₂ × A₃)) :
    UniversalEmbeddingGroup w₁ w₂ w₃ S := by
  classical
  exact if h : S.Nonempty then
    univEmbed₁ w₁ w₂ w₃ S h.some.1 + univEmbed₂ w₁ w₂ w₃ S h.some.2.1 +
      univEmbed₃ w₁ w₂ w₃ S h.some.2.2
  else 0

/-- The canonical maps into `UniversalEmbeddingGroup` form a standard embedding of `S`. -/
theorem isStandardEmbedding_univ (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) (S : Set (A₁ × A₂ × A₃)) :
    IsStandardEmbedding w₁ w₂ w₃ S
      (univEmbed₁ w₁ w₂ w₃ S) (univEmbed₂ w₁ w₂ w₃ S) (univEmbed₃ w₁ w₂ w₃ S)
      (univEmbedConst w₁ w₂ w₃ S) := by
  classical
  have h1 : univEmbed₁ w₁ w₂ w₃ S w₁ = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr
      (AddSubgroup.subset_closure (Or.inl (Set.mem_insert _ _)))
  have h2 : univEmbed₂ w₁ w₂ w₃ S w₂ = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr
      (AddSubgroup.subset_closure (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have h3 : univEmbed₃ w₁ w₂ w₃ S w₃ = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr
      (AddSubgroup.subset_closure (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))
  refine ⟨h1, h2, h3, fun x hx ↦ ?_⟩
  have hne : S.Nonempty := ⟨x, hx⟩
  simp only [univEmbedConst, hne, ↓reduceDIte]
  unfold univEmbed₁ univEmbed₂ univEmbed₃
  rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add,
      ← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add, QuotientAddGroup.eq]
  rw [neg_add_eq_sub]
  exact AddSubgroup.subset_closure (Or.inr ⟨hne.some, x, hne.some_mem, hx, rfl⟩)

/-- **Universal property of `UniversalEmbeddingGroup`**: every standard embedding of `S` into
any Abelian group `G` factors uniquely through `UniversalEmbeddingGroup w₁ w₂ w₃ S`. -/
theorem universalEmbeddingGroup_universal {G : Type*} [AddCommGroup G]
    (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) (S : Set (A₁ × A₂ × A₃))
    {σ₁ : A₁ → G} {σ₂ : A₂ → G} {σ₃ : A₃ → G} {g : G}
    (h : IsStandardEmbedding w₁ w₂ w₃ S σ₁ σ₂ σ₃ g) :
    ∃! ψ : UniversalEmbeddingGroup w₁ w₂ w₃ S →+ G,
      (∀ a, ψ (univEmbed₁ w₁ w₂ w₃ S a) = σ₁ a) ∧
      (∀ b, ψ (univEmbed₂ w₁ w₂ w₃ S b) = σ₂ b) ∧
      (∀ c, ψ (univEmbed₃ w₁ w₂ w₃ S c) = σ₃ c) := by
  let f : ((A₁ ⊕ A₂) ⊕ A₃) → G := Sum.elim (Sum.elim σ₁ σ₂) σ₃
  let φ : FreeAbelianGroup ((A₁ ⊕ A₂) ⊕ A₃) →+ G := FreeAbelianGroup.lift f
  have hker : universalRelSubgroup w₁ w₂ w₃ S ≤ φ.ker := by
    rw [universalRelSubgroup, AddSubgroup.closure_le]
    rintro z (hz | ⟨x, y, hx, hy, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · simp [φ, f, h.1]
      · simp [φ, f, h.2.1]
      · simp [φ, f, h.2.2.1]
    · change φ _ = 0
      rw [map_sub, map_add, map_add, map_add, map_add]
      have h1 : φ (FreeAbelianGroup.of (Sum.inl (Sum.inl x.1))) = σ₁ x.1 := by simp [φ, f]
      have h2 : φ (FreeAbelianGroup.of (Sum.inl (Sum.inr x.2.1))) = σ₂ x.2.1 := by simp [φ, f]
      have h3 : φ (FreeAbelianGroup.of (Sum.inr x.2.2)) = σ₃ x.2.2 := by simp [φ, f]
      have h4 : φ (FreeAbelianGroup.of (Sum.inl (Sum.inl y.1))) = σ₁ y.1 := by simp [φ, f]
      have h5 : φ (FreeAbelianGroup.of (Sum.inl (Sum.inr y.2.1))) = σ₂ y.2.1 := by simp [φ, f]
      have h6 : φ (FreeAbelianGroup.of (Sum.inr y.2.2)) = σ₃ y.2.2 := by simp [φ, f]
      rw [h1, h2, h3, h4, h5, h6, h.2.2.2 x hx, h.2.2.2 y hy, sub_self]
  let ψ : UniversalEmbeddingGroup w₁ w₂ w₃ S →+ G := QuotientAddGroup.lift _ φ hker
  refine ⟨ψ, ⟨fun a ↦ by simp [ψ, φ, f, univEmbed₁],
      fun b ↦ by simp [ψ, φ, f, univEmbed₂],
      fun c ↦ by simp [ψ, φ, f, univEmbed₃]⟩, ?_⟩
  rintro ψ' ⟨h1, h2, h3⟩
  apply QuotientAddGroup.addMonoidHom_ext
  ext t
  rcases t with ((a | b) | c)
  · simpa [ψ, φ, f, univEmbed₁] using h1 a
  · simpa [ψ, φ, f, univEmbed₂] using h2 b
  · simpa [ψ, φ, f, univEmbed₃] using h3 c

/-- **Finiteness of the universal embedding group**: if `A₁, A₂, A₃` are finite, `S` is nonempty,
and `S` admits no `(ℤ, +)`-embedding, then `UniversalEmbeddingGroup w₁ w₂ w₃ S` is finite. -/
theorem finite_universalEmbeddingGroup_of_not_hasIntEmbedding
    [Finite A₁] [Finite A₂] [Finite A₃]
    (w₁ : A₁) (w₂ : A₂) (w₃ : A₃) {S : Set (A₁ × A₂ × A₃)}
    (_hne : S.Nonempty) (hno : ¬ HasIntEmbedding S) :
    Finite (UniversalEmbeddingGroup w₁ w₂ w₃ S) := by
  classical
  let : Fintype A₁ := Fintype.ofFinite A₁
  let : Fintype A₂ := Fintype.ofFinite A₂
  let : Fintype A₃ := Fintype.ofFinite A₃
  -- Step 1: every `AddMonoidHom (UniversalEmbeddingGroup w₁ w₂ w₃ S) →+ ℤ` is zero.
  have hhom_zero : ∀ ψ : UniversalEmbeddingGroup w₁ w₂ w₃ S →+ ℤ, ψ = 0 := by
    intro ψ
    have hstd := isStandardEmbedding_univ w₁ w₂ w₃ S
    have hstd_ψ : IsStandardEmbedding w₁ w₂ w₃ S
        (fun a ↦ ψ (univEmbed₁ w₁ w₂ w₃ S a))
        (fun b ↦ ψ (univEmbed₂ w₁ w₂ w₃ S b))
        (fun c ↦ ψ (univEmbed₃ w₁ w₂ w₃ S c))
        (ψ (univEmbedConst w₁ w₂ w₃ S)) := by
      refine ⟨by dsimp; rw [hstd.1, map_zero], by dsimp; rw [hstd.2.1, map_zero],
        by dsimp; rw [hstd.2.2.1, map_zero], fun x hx ↦ ?_⟩
      dsimp; rw [← map_add, ← map_add, hstd.2.2.2 x hx]
    have hab := isAbelianEmbedding_of_isStandardEmbedding hstd_ψ
    have hconst : ¬ IsNonconstTriple
        (fun a ↦ ψ (univEmbed₁ w₁ w₂ w₃ S a))
        (fun b ↦ ψ (univEmbed₂ w₁ w₂ w₃ S b))
        (fun c ↦ ψ (univEmbed₃ w₁ w₂ w₃ S c) - ψ (univEmbedConst w₁ w₂ w₃ S)) :=
      fun hnc ↦ hno ⟨_, _, _, hab, hnc⟩
    simp only [IsNonconstTriple, not_or, not_exists, not_ne_iff] at hconst
    have h1 : ∀ a, ψ (univEmbed₁ w₁ w₂ w₃ S a) = 0 := fun a ↦
      (hconst.1 a w₁).trans (by rw [hstd.1, map_zero])
    have h2 : ∀ b, ψ (univEmbed₂ w₁ w₂ w₃ S b) = 0 := fun b ↦
      (hconst.2.1 b w₂).trans (by rw [hstd.2.1, map_zero])
    have h3 : ∀ c, ψ (univEmbed₃ w₁ w₂ w₃ S c) = 0 := fun c ↦ by
      have hc := hconst.2.2 c w₃
      have hw3 : ψ (univEmbed₃ w₁ w₂ w₃ S w₃) = 0 := by rw [hstd.2.2.1, map_zero]
      linarith
    apply QuotientAddGroup.addMonoidHom_ext
    ext t
    rcases t with ((a | b) | c)
    · simpa [univEmbed₁] using h1 a
    · simpa [univEmbed₂] using h2 b
    · simpa [univEmbed₃] using h3 c
  -- Step 2: `U(S)` is finitely generated by `gen : ((A₁ ⊕ A₂) ⊕ A₃) → U`.
  let U := UniversalEmbeddingGroup w₁ w₂ w₃ S
  let gen : ((A₁ ⊕ A₂) ⊕ A₃) → U := fun t ↦ QuotientAddGroup.mk (FreeAbelianGroup.of t)
  have hspan_U : Submodule.span ℤ (Set.range gen) = ⊤ := by
    rw [eq_top_iff]
    intro u hu
    clear hu
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective u
    induction z using FreeAbelianGroup.induction_on with
    | zero => exact zero_mem _
    | of t => exact Submodule.subset_span ⟨t, rfl⟩
    | neg t ih => exact neg_mem ih
    | add a b iha ihb => exact add_mem iha ihb
  -- Step 3: `Q = U ⧸ torsion ℤ U` is finitely generated torsion-free over `ℤ`, hence free;
  -- if its rank were `> 0`, a basis coordinate would give a nonzero `U →+ ℤ`.
  let Q := U ⧸ Submodule.torsion ℤ U
  let genQ : ((A₁ ⊕ A₂) ⊕ A₃) → Q := fun t ↦ Submodule.mkQ (Submodule.torsion ℤ U) (gen t)
  have hspan_Q : Submodule.span ℤ (Set.range genQ) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective (Submodule.torsion ℤ U) q
    have hu : u ∈ Submodule.span ℤ (Set.range gen) := by rw [hspan_U]; trivial
    refine Submodule.span_induction
      (p := fun u _ ↦ Submodule.mkQ _ u ∈ Submodule.span ℤ (Set.range genQ)) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨t, rfl⟩; exact Submodule.subset_span ⟨t, rfl⟩
    · simp
    · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
    · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ _ ha
  have hQ_free : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free hspan_Q
  have hQ_sub : Subsingleton Q := by
    refine ⟨fun x y ↦ ?_⟩
    by_contra hxy
    have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
    let b := Module.Free.chooseBasis ℤ Q
    have hex : ∃ i, b.repr (x - y) i ≠ 0 := by
      by_contra hall; push Not at hall
      have h0 : b.repr (x - y) = 0 := Finsupp.ext hall
      exact hd (b.repr.injective (by simpa using h0))
    obtain ⟨i, hi⟩ := hex
    let φ : U →ₗ[ℤ] ℤ := (Finsupp.lapply i).comp (b.repr.toLinearMap.comp (Submodule.mkQ _))
    have hφ0 := hhom_zero φ.toAddMonoidHom
    have hval : φ.toAddMonoidHom (Quotient.out x - Quotient.out y) = 0 := by
      rw [hφ0]; rfl
    have hmk :
        (Submodule.mkQ (Submodule.torsion ℤ U)) (Quotient.out x - Quotient.out y) = x - y := by
      simp [Submodule.mkQ_apply]
    have hval' : b.repr (x - y) i = 0 := by
      change (Finsupp.lapply (R := ℤ) i)
          (b.repr ((Submodule.mkQ (Submodule.torsion ℤ U)) (Quotient.out x - Quotient.out y))) = 0
        at hval
      rwa [hmk] at hval
    exact hi hval'
  -- Step 4: Every element of `U` is torsion; since `U` is generated by the finite set `gen`,
  -- the product of generator orders gives a finite surjection onto `U`.
  have htors : ∀ u : U, ∃ n : ℕ, 0 < n ∧ n • u = 0 := by
    intro u
    have hu : (Submodule.mkQ (Submodule.torsion ℤ U)) u = 0 := Subsingleton.elim _ _
    have hmem : u ∈ Submodule.torsion ℤ U := (Submodule.Quotient.mk_eq_zero _).mp hu
    obtain ⟨⟨k, hk⟩, hku⟩ := hmem
    have hk0 : k ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hk
    refine ⟨k.natAbs, Int.natAbs_pos.mpr hk0, ?_⟩
    rcases Int.natAbs_eq k with h | h
    · have h1 : (k.natAbs : ℤ) • u = 0 := by simpa [← h] using hku
      exact_mod_cast h1
    · have h1 : (k.natAbs : ℤ) • u = 0 := by
        have := congr_arg Neg.neg hku
        simp only [neg_zero] at this
        simpa [← h] using this
      exact_mod_cast h1
  choose ord hord_pos hord_zero using fun t ↦ htors (gen t)
  let M := ∏ t : (A₁ ⊕ A₂) ⊕ A₃, ord t
  have hM_pos : 0 < M := Finset.prod_pos fun t _ ↦ hord_pos t
  have hM_ann : ∀ u : U, M • u = 0 := by
    have hsub : ∀ u ∈ AddSubgroup.closure (Set.range gen), M • u = 0 := by
      intro u hu
      refine AddSubgroup.closure_induction ?_ (by simp) (fun a b _ _ ha hb ↦ by
        rw [smul_add, ha, hb, add_zero]) (fun a _ ha ↦ by rw [smul_neg, ha, neg_zero]) hu
      rintro _ ⟨t, rfl⟩
      have hdvd : ord t ∣ M := Finset.dvd_prod_of_mem ord (Finset.mem_univ t)
      obtain ⟨r, hr⟩ := hdvd
      rw [hr, mul_comm, mul_smul, hord_zero t, smul_zero]
    have htop : AddSubgroup.closure (Set.range gen) = ⊤ := by
      rw [eq_top_iff]
      intro u hu
      clear hu
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective u
      induction z using FreeAbelianGroup.induction_on with
      | zero => exact zero_mem _
      | of t => exact AddSubgroup.subset_closure ⟨t, rfl⟩
      | neg t h => exact neg_mem h
      | add a b ha hb => exact add_mem ha hb
    intro u
    exact hsub u (by rw [htop]; trivial)
  let surjMap : (((A₁ ⊕ A₂) ⊕ A₃) → Fin M) → U := fun c ↦ ∑ t, (c t).val • gen t
  have hsurj : Function.Surjective surjMap := by
    intro u
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective u
    let coeff : ((A₁ ⊕ A₂) ⊕ A₃) → ℤ := fun t ↦ FreeAbelianGroup.equivFinsupp _ z t
    have hz : QuotientAddGroup.mk z = ∑ t, coeff t • gen t := by
      have h1 : z = ∑ t, coeff t • FreeAbelianGroup.of t := by
        have heq := (FreeAbelianGroup.equivFinsupp ((A₁ ⊕ A₂) ⊕ A₃)).symm_apply_apply z
        conv_lhs => rw [← heq]
        rw [← Finsupp.univ_sum_single (FreeAbelianGroup.equivFinsupp _ z), map_sum]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        have hsingle : (FreeAbelianGroup.equivFinsupp _).symm (Finsupp.single t (coeff t)) =
            coeff t • FreeAbelianGroup.of t := by
          apply (FreeAbelianGroup.equivFinsupp _).injective
          simp [coeff]
        exact hsingle
      conv_lhs => rw [h1]
      change QuotientAddGroup.mk' (universalRelSubgroup w₁ w₂ w₃ S) _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [map_zsmul]; rfl
    refine ⟨fun t ↦ ⟨(coeff t % (M : ℤ)).toNat, by
      have hnonneg : 0 ≤ coeff t % (M : ℤ) := Int.emod_nonneg _ (by omega)
      have hlt : coeff t % (M : ℤ) < (M : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hM_pos)
      omega⟩, ?_⟩
    rw [hz]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have hmod : ((coeff t % (M : ℤ)).toNat : ℤ) • gen t = coeff t • gen t := by
      have hnonneg : 0 ≤ coeff t % (M : ℤ) := Int.emod_nonneg _ (by omega)
      rw [Int.toNat_of_nonneg hnonneg]
      have hdiv := Int.emod_add_mul_ediv (coeff t) (M : ℤ)
      have hM_z : (M : ℤ) • gen t = 0 := by exact_mod_cast hM_ann (gen t)
      calc (coeff t % (M : ℤ)) • gen t
          = (coeff t % (M : ℤ)) • gen t + (coeff t / (M : ℤ)) • ((M : ℤ) • gen t) := by
            rw [hM_z, smul_zero, add_zero]
        _ = (coeff t % (M : ℤ) + (M : ℤ) * (coeff t / (M : ℤ))) • gen t := by
            rw [smul_smul, mul_comm (coeff t / (M : ℤ)), ← add_smul]
        _ = coeff t • gen t := by rw [hdiv]
    rw [← natCast_zsmul, hmod]
  exact Finite.of_surjective surjMap hsurj

end UniversalEmbedding

section CspAndSdp

/-- A weighted `3`-ary CSP instance over finite alphabet `A` and finite variable set `V`,
whose constraints are drawn from a probability distribution `clauses : PMF (CspClause V A)`. -/
@[ext]
structure CspClause (V A : Type*) where
  /-- First variable of the constraint. -/
  v₁ : V
  /-- Second variable of the constraint. -/
  v₂ : V
  /-- Third variable of the constraint. -/
  v₃ : V
  /-- Predicate `P : A × A × A → Bool`. -/
  pred : A × A × A → Bool

/-- A `Max-Preds-CSP` instance with finite variable set `V` and distribution `clauses` over
constraints whose predicates lie in `Preds`. -/
structure CspInstance (V A : Type*) [Fintype V] [Fintype A] (Preds : Set (A × A × A → Bool)) where
  /-- Distribution over `3`-ary constraints. -/
  clauses : PMF (CspClause V A)
  /-- Finite support of the clause distribution. -/
  finite_support : clauses.support.Finite
  /-- Every clause in the support uses a predicate from `Preds`. -/
  mem_family : ∀ C ∈ clauses.support, C.pred ∈ Preds

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Value of an assignment `α : V → A` on a `CspInstance`: expected fraction of satisfied
clauses. -/
@[expose] noncomputable def assignmentVal {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    (inst : CspInstance V A Preds) (α : V → A) : ℝ :=
  ∑' C : CspClause V A,
    (inst.clauses C).toReal * if C.pred (α C.v₁, α C.v₂, α C.v₃) then 1 else 0

/-- Optimal value `OPT(inst)` of a `CspInstance`. -/
@[expose] noncomputable def optVal {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    (inst : CspInstance V A Preds) : ℝ :=
  sSup (Set.range (assignmentVal inst))

/-- A `CspInstance` is satisfiable if there is an assignment satisfying every clause in the
support of `inst.clauses`. -/
@[expose] def IsSatisfiable {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    (inst : CspInstance V A Preds) : Prop :=
  ∃ α : V → A, ∀ C ∈ inst.clauses.support, C.pred (α C.v₁, α C.v₂, α C.v₃) = true

/-- **Mildly-Symmetric predicates** (Definition `def:symm_p`): a family `Preds` of `3`-ary
predicates over `A` is mildly symmetric if there exists a nonempty finite family of actions
`τ : ι → A → A` preserving satisfying assignments of every `P ∈ Preds` such that every orbit
`{(τ i a, τ i b, τ i c) | i}` of a satisfying assignment `(a, b, c)` has no `(ℤ, +)`-embedding. -/
@[expose] def IsMildlySymmetric (Preds : Set (A × A × A → Bool)) : Prop :=
  ∃ (k : ℕ) (τ : Fin k → A → A), 0 < k ∧
    (∀ P ∈ Preds, ∀ (i : Fin k) (a b c : A), P (a, b, c) = true → P (τ i a, τ i b, τ i c) = true) ∧
    (∀ P ∈ Preds, ∀ (a b c : A), P (a, b, c) = true →
      ¬ HasIntEmbedding {t : A × A × A | ∃ i : Fin k, t = (τ i a, τ i b, τ i c)})

/-- Basic SDP relaxation solution (`fig:basicsdp1`) for a `CspInstance` in dimension `d`. -/
structure BasicSdpSolution {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    (inst : CspInstance V A Preds) (d : ℕ) where
  /-- Unit vector `b₀ ∈ ℝ^d`. -/
  b0 : EuclideanSpace ℝ (Fin d)
  /-- Variable-symbol vectors `b_{i,a} ∈ ℝ^d`. -/
  b : V → A → EuclideanSpace ℝ (Fin d)
  /-- Local distributions `μ_C` over `A³` for each constraint `C`. -/
  mu : CspClause V A → PMF (A × A × A)
  /-- `‖b₀‖² = 1`. -/
  b0_unit : ‖b0‖ ^ 2 = 1
  /-- `⟨b_{i,a}, b₀⟩ = ‖b_{i,a}‖²`. -/
  b_proj : ∀ (i : V) (a : A), @inner ℝ _ _ (b i a) b0 = ‖b i a‖ ^ 2
  /-- Pairwise inner products match local pairwise marginals on `(v₁, v₂)`, `(v₁, v₃)`,
  `(v₂, v₃)`, and diagonal `(v_r, v_r)`. -/
  inner_11 : ∀ C ∈ inst.clauses.support, ∀ a a' : A,
    @inner ℝ _ _ (b C.v₁ a) (b C.v₁ a') =
      ∑ t : A × A × A, (mu C t).toReal * if t.1 = a ∧ t.1 = a' then 1 else 0
  inner_22 : ∀ C ∈ inst.clauses.support, ∀ a a' : A,
    @inner ℝ _ _ (b C.v₂ a) (b C.v₂ a') =
      ∑ t : A × A × A, (mu C t).toReal * if t.2.1 = a ∧ t.2.1 = a' then 1 else 0
  inner_33 : ∀ C ∈ inst.clauses.support, ∀ a a' : A,
    @inner ℝ _ _ (b C.v₃ a) (b C.v₃ a') =
      ∑ t : A × A × A, (mu C t).toReal * if t.2.2 = a ∧ t.2.2 = a' then 1 else 0
  inner_12 : ∀ C ∈ inst.clauses.support, ∀ a a' : A,
    @inner ℝ _ _ (b C.v₁ a) (b C.v₂ a') =
      ∑ t : A × A × A, (mu C t).toReal * if t.1 = a ∧ t.2.1 = a' then 1 else 0
  inner_13 : ∀ C ∈ inst.clauses.support, ∀ a a' : A,
    @inner ℝ _ _ (b C.v₁ a) (b C.v₃ a') =
      ∑ t : A × A × A, (mu C t).toReal * if t.1 = a ∧ t.2.2 = a' then 1 else 0
  inner_23 : ∀ C ∈ inst.clauses.support, ∀ a a' : A,
    @inner ℝ _ _ (b C.v₂ a) (b C.v₃ a') =
      ∑ t : A × A × A, (mu C t).toReal * if t.2.1 = a ∧ t.2.2 = a' then 1 else 0

/-- Objective value of a basic SDP solution. -/
noncomputable def BasicSdpSolution.val {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    {inst : CspInstance V A Preds} {d : ℕ} (S : BasicSdpSolution inst d) : ℝ :=
  ∑' C : CspClause V A,
    (inst.clauses C).toReal *
      ∑ t : A × A × A, (S.mu C t).toReal * if C.pred t then 1 else 0

/-- Value `1` means every local distribution `μ_C` is supported on satisfying assignments of `C`. -/
@[expose] def BasicSdpSolution.HasValueOne {V : Type*} [Fintype V]
    {Preds : Set (A × A × A → Bool)} {inst : CspInstance V A Preds} {d : ℕ}
    (S : BasicSdpSolution inst d) : Prop :=
  ∀ C ∈ inst.clauses.support, ∀ t ∈ (S.mu C).support, C.pred t = true

/-- Integral SDP solution associated to a satisfying assignment `α : V → A`. -/
noncomputable def integralSdpSolution {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    (inst : CspInstance V A Preds) (α : V → A) : BasicSdpSolution inst 1 where
  b0 := WithLp.toLp 2 (fun _ : Fin 1 ↦ (1 : ℝ))
  b i a := if α i = a then WithLp.toLp 2 (fun _ : Fin 1 ↦ (1 : ℝ)) else 0
  mu C := PMF.pure (α C.v₁, α C.v₂, α C.v₃)
  b0_unit := by simp [EuclideanSpace.norm_eq]
  b_proj i a := by
    by_cases h : α i = a
    · simp [h, EuclideanSpace.norm_eq]
    · simp [h]
  inner_11 C _ a a' := by
    rw [Finset.sum_eq_single (α C.v₁, α C.v₂, α C.v₃)]
    · by_cases h1 : α C.v₁ = a <;> by_cases h2 : α C.v₁ = a'
      · subst h1; simp [h2, EuclideanSpace.norm_eq]
      · simp [h1, show a ≠ a' from fun h ↦ h2 (h ▸ h1)]
      · simp [h2, show a' ≠ a from fun h ↦ h1 (h ▸ h2)]
      · simp [h1, h2]
    · intro t _ ht; simp [ht]
    · intro h; exact (h (Finset.mem_univ _)).elim
  inner_22 C _ a a' := by
    rw [Finset.sum_eq_single (α C.v₁, α C.v₂, α C.v₃)]
    · by_cases h1 : α C.v₂ = a <;> by_cases h2 : α C.v₂ = a'
      · subst h1; simp [h2, EuclideanSpace.norm_eq]
      · simp [h1, show a ≠ a' from fun h ↦ h2 (h ▸ h1)]
      · simp [h2, show a' ≠ a from fun h ↦ h1 (h ▸ h2)]
      · simp [h1, h2]
    · intro t _ ht; simp [ht]
    · intro h; exact (h (Finset.mem_univ _)).elim
  inner_33 C _ a a' := by
    rw [Finset.sum_eq_single (α C.v₁, α C.v₂, α C.v₃)]
    · by_cases h1 : α C.v₃ = a <;> by_cases h2 : α C.v₃ = a'
      · subst h1; simp [h2, EuclideanSpace.norm_eq]
      · simp [h1, show a ≠ a' from fun h ↦ h2 (h ▸ h1)]
      · simp [h2, show a' ≠ a from fun h ↦ h1 (h ▸ h2)]
      · simp [h1, h2]
    · intro t _ ht; simp [ht]
    · intro h; exact (h (Finset.mem_univ _)).elim
  inner_12 C _ a a' := by
    rw [Finset.sum_eq_single (α C.v₁, α C.v₂, α C.v₃)]
    · by_cases h1 : α C.v₁ = a <;> by_cases h2 : α C.v₂ = a' <;>
        simp [h1, h2, EuclideanSpace.norm_eq]
    · intro t _ ht; simp [ht]
    · intro h; exact (h (Finset.mem_univ _)).elim
  inner_13 C _ a a' := by
    rw [Finset.sum_eq_single (α C.v₁, α C.v₂, α C.v₃)]
    · by_cases h1 : α C.v₁ = a <;> by_cases h2 : α C.v₃ = a' <;>
        simp [h1, h2, EuclideanSpace.norm_eq]
    · intro t _ ht; simp [ht]
    · intro h; exact (h (Finset.mem_univ _)).elim
  inner_23 C _ a a' := by
    rw [Finset.sum_eq_single (α C.v₁, α C.v₂, α C.v₃)]
    · by_cases h1 : α C.v₂ = a <;> by_cases h2 : α C.v₃ = a' <;>
        simp [h1, h2, EuclideanSpace.norm_eq]
    · intro t _ ht; simp [ht]
    · intro h; exact (h (Finset.mem_univ _)).elim

/-- Direct-sum helper scaling two vectors in `ℝ^{d₁}` and `ℝ^{d₂}` by `1 / √2` into
`ℝ^{d₁ + d₂}`. -/
private noncomputable def directSumVec {d₁ d₂ : ℕ}
    (u : EuclideanSpace ℝ (Fin d₁)) (v : EuclideanSpace ℝ (Fin d₂)) :
    EuclideanSpace ℝ (Fin (d₁ + d₂)) :=
  WithLp.toLp 2 (Fin.addCases (fun i ↦ (1 / Real.sqrt 2) * u i)
    (fun j ↦ (1 / Real.sqrt 2) * v j))

private lemma inner_directSumVec {d₁ d₂ : ℕ}
    (u₁ u₂ : EuclideanSpace ℝ (Fin d₁)) (v₁ v₂ : EuclideanSpace ℝ (Fin d₂)) :
    @inner ℝ _ _ (directSumVec u₁ v₁) (directSumVec u₂ v₂) =
      (1 / 2 : ℝ) * (@inner ℝ _ _ u₁ u₂ + @inner ℝ _ _ v₁ v₂) := by
  have hsq : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    rw [one_div_mul_one_div, ← sq, Real.sq_sqrt (by norm_num)]
  simp only [directSumVec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  have h1 : ∑ x : Fin d₁, (1 / Real.sqrt 2) * u₂ x * ((1 / Real.sqrt 2) * u₁ x) =
      (1 / 2 : ℝ) * ∑ x : Fin d₁, u₂ x * u₁ x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    calc (1 / Real.sqrt 2) * u₂ x * ((1 / Real.sqrt 2) * u₁ x)
        = (1 / Real.sqrt 2) * (1 / Real.sqrt 2) * (u₂ x * u₁ x) := by ring
      _ = (1 / 2 : ℝ) * (u₂ x * u₁ x) := by rw [hsq]
  have h2 : ∑ x : Fin d₂, (1 / Real.sqrt 2) * v₂ x * ((1 / Real.sqrt 2) * v₁ x) =
      (1 / 2 : ℝ) * ∑ x : Fin d₂, v₂ x * v₁ x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    calc (1 / Real.sqrt 2) * v₂ x * ((1 / Real.sqrt 2) * v₁ x)
        = (1 / Real.sqrt 2) * (1 / Real.sqrt 2) * (v₂ x * v₁ x) := by ring
      _ = (1 / 2 : ℝ) * (v₂ x * v₁ x) := by rw [hsq]
  rw [h1, h2, ← mul_add]

private lemma norm_sq_directSumVec {d₁ d₂ : ℕ}
    (u : EuclideanSpace ℝ (Fin d₁)) (v : EuclideanSpace ℝ (Fin d₂)) :
    ‖directSumVec u v‖ ^ 2 = (1 / 2 : ℝ) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  exact inner_directSumVec u u v v

/-- Uniform `1/2`-mixture of two PMFs, defined directly without extra imports. -/
private noncomputable def pmfHalf {α : Type*} (p q : PMF α) : PMF α :=
  ⟨fun a ↦ (2 : ENNReal)⁻¹ * p a + (2 : ENNReal)⁻¹ * q a, by
    refine CompleteLattice.summable.hasSum_iff.mpr ?_
    rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      p.tsum_coe, q.tsum_coe, mul_one, ENNReal.inv_two_add_inv_two]⟩

private lemma pmf_half_mix_apply {α : Type*} (p q : PMF α) (x : α) :
    (pmfHalf p q x).toReal = (1 / 2 : ℝ) * (p x).toReal + (1 / 2 : ℝ) * (q x).toReal := by
  change ((2 : ENNReal)⁻¹ * p x + (2 : ENNReal)⁻¹ * q x).toReal = _
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _))
      (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hhalf : ((2 : ENNReal)⁻¹).toReal = (1 / 2 : ℝ) := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div]
  rw [hhalf]

/-- **Combining SDP solutions (Claim `claim:combineSDP`)**: given two value-`1` SDP solutions
in dimensions `d₁, d₂`, their direct-sum combination in dimension `d₁ + d₂` has value `1` and
local support equal to the union of the two local supports. -/
noncomputable def combineSdpSolutions {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    {inst : CspInstance V A Preds} {d₁ d₂ : ℕ}
    (S₁ : BasicSdpSolution inst d₁) (S₂ : BasicSdpSolution inst d₂) :
    BasicSdpSolution inst (d₁ + d₂) where
  b0 := directSumVec S₁.b0 S₂.b0
  b v a := directSumVec (S₁.b v a) (S₂.b v a)
  mu C := pmfHalf (S₁.mu C) (S₂.mu C)
  b0_unit := by
    rw [norm_sq_directSumVec, S₁.b0_unit, S₂.b0_unit]; norm_num
  b_proj i a := by
    rw [inner_directSumVec, norm_sq_directSumVec, S₁.b_proj, S₂.b_proj]
  inner_11 C hC a a' := by
    rw [inner_directSumVec, S₁.inner_11 C hC a a', S₂.inner_11 C hC a a',
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [pmf_half_mix_apply]; ring
  inner_22 C hC a a' := by
    rw [inner_directSumVec, S₁.inner_22 C hC a a', S₂.inner_22 C hC a a',
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [pmf_half_mix_apply]; ring
  inner_33 C hC a a' := by
    rw [inner_directSumVec, S₁.inner_33 C hC a a', S₂.inner_33 C hC a a',
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [pmf_half_mix_apply]; ring
  inner_12 C hC a a' := by
    rw [inner_directSumVec, S₁.inner_12 C hC a a', S₂.inner_12 C hC a a',
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [pmf_half_mix_apply]; ring
  inner_13 C hC a a' := by
    rw [inner_directSumVec, S₁.inner_13 C hC a a', S₂.inner_13 C hC a a',
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [pmf_half_mix_apply]; ring
  inner_23 C hC a a' := by
    rw [inner_directSumVec, S₁.inner_23 C hC a a', S₂.inner_23 C hC a a',
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [pmf_half_mix_apply]; ring

/-- The local support of a combined SDP solution is the union of the two local supports. -/
theorem combineSdpSolutions_support {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    {inst : CspInstance V A Preds} {d₁ d₂ : ℕ}
    (S₁ : BasicSdpSolution inst d₁) (S₂ : BasicSdpSolution inst d₂) (C : CspClause V A) :
    ((combineSdpSolutions S₁ S₂).mu C).support = (S₁.mu C).support ∪ (S₂.mu C).support := by
  ext t
  simp only [combineSdpSolutions, pmfHalf, PMF.mem_support_iff, Set.mem_union]
  change (2 : ENNReal)⁻¹ * S₁.mu C t + (2 : ENNReal)⁻¹ * S₂.mu C t ≠ 0 ↔ _
  simp only [ne_eq, add_eq_zero, mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.ofNat_ne_top,
    false_or, not_and]
  tauto

/-- Combining two value-`1` SDP solutions preserves value `1`. -/
theorem combineSdpSolutions_hasValueOne {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    {inst : CspInstance V A Preds} {d₁ d₂ : ℕ}
    {S₁ : BasicSdpSolution inst d₁} {S₂ : BasicSdpSolution inst d₂}
    (h₁ : S₁.HasValueOne) (h₂ : S₂.HasValueOne) :
    (combineSdpSolutions S₁ S₂).HasValueOne := by
  intro C hC t ht
  rw [combineSdpSolutions_support] at ht
  rcases ht with ht | ht
  · exact h₁ C hC t ht
  · exact h₂ C hC t ht

/-- **Gram dimension reduction**: any basic SDP solution on `V` over alphabet `A` admits a
realization in dimension `|V| · |A| + 1` with the exact same local distributions and all inner
products preserved. -/
theorem gram_dimension_reduction {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    {inst : CspInstance V A Preds} {d : ℕ} (S : BasicSdpSolution inst d) :
    ∃ S' : BasicSdpSolution inst (Fintype.card V * Fintype.card A + 1),
      S'.mu = S.mu ∧
      (S'.HasValueOne ↔ S.HasValueOne) := by
  classical
  let f : Option (V × A) → EuclideanSpace ℝ (Fin d) := fun
    | none => S.b0
    | some p => S.b p.1 p.2
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℝ (Set.range f)
  have hfin : Module.finrank ℝ W ≤ Fintype.card V * Fintype.card A + 1 := by
    have h1 : Module.finrank ℝ W ≤ (Set.range f).toFinset.card := finrank_span_le_card (Set.range f)
    have h2 : (Set.range f).toFinset.card ≤ Fintype.card (Option (V × A)) := by
      rw [Set.toFinset_card]; exact Fintype.card_range_le f
    simpa [Fintype.card_option, Fintype.card_prod] using h1.trans h2
  let e := stdOrthonormalBasis ℝ W
  let T : W → EuclideanSpace ℝ (Fin (Fintype.card V * Fintype.card A + 1)) := fun w ↦
    WithLp.toLp 2 (fun k ↦
      if h : k.val < Module.finrank ℝ W then e.repr w ⟨k.val, h⟩ else 0)
  have hT_inner : ∀ w₁ w₂ : W, @inner ℝ _ _ (T w₁) (T w₂) = @inner ℝ _ _ w₁ w₂ := by
    intro w₁ w₂
    have hsum : @inner ℝ _ _ (T w₁) (T w₂) =
        ∑ j : Fin (Module.finrank ℝ W), e.repr w₂ j * e.repr w₁ j := by
      simp only [T, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
      let emb : Fin (Module.finrank ℝ W) ↪ Fin (Fintype.card V * Fintype.card A + 1) :=
        Fin.castLEEmb hfin
      have hzero : ∑ k ∈ Finset.univ \ Finset.univ.map emb,
          (if h : k.val < Module.finrank ℝ W then e.repr w₂ ⟨k.val, h⟩ else 0) *
          (if h : k.val < Module.finrank ℝ W then e.repr w₁ ⟨k.val, h⟩ else 0) = 0 := by
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        have hnot : ¬ k.val < Module.finrank ℝ W := by
          intro hlt
          have hmem : k ∈ Finset.univ.map emb :=
            Finset.mem_map.mpr ⟨⟨k.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
          exact (Finset.mem_sdiff.mp hk).2 hmem
        simp [hnot]
      have hsplit := Finset.sum_sdiff (Finset.subset_univ (Finset.univ.map emb))
        (f := fun k : Fin (Fintype.card V * Fintype.card A + 1) ↦
          (if h : k.val < Module.finrank ℝ W then e.repr w₂ ⟨k.val, h⟩ else 0) *
          (if h : k.val < Module.finrank ℝ W then e.repr w₁ ⟨k.val, h⟩ else 0))
      rw [← hsplit, hzero, zero_add, Finset.sum_map]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [emb, j.isLt]
    rw [hsum]
    have h1 : ∑ j : Fin (Module.finrank ℝ W), e.repr w₂ j * e.repr w₁ j =
        @inner ℝ _ _ (e.repr w₁) (e.repr w₂) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]; rfl
    rw [h1, e.repr.inner_map_map]
  have hT_norm : ∀ w : W, ‖T w‖ ^ 2 = ‖(w : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
    intro w
    rw [← real_inner_self_eq_norm_sq, hT_inner, real_inner_self_eq_norm_sq]; rfl
  have hb0_mem : S.b0 ∈ W := Submodule.subset_span ⟨none, rfl⟩
  have hb_mem : ∀ i a, S.b i a ∈ W := fun i a ↦ Submodule.subset_span ⟨some (i, a), rfl⟩
  let S' : BasicSdpSolution inst (Fintype.card V * Fintype.card A + 1) := {
    b0 := T ⟨S.b0, hb0_mem⟩
    b := fun i a ↦ T ⟨S.b i a, hb_mem i a⟩
    mu := S.mu
    b0_unit := by rw [hT_norm]; exact S.b0_unit
    b_proj := fun i a ↦ by rw [hT_inner, hT_norm]; exact S.b_proj i a
    inner_11 := fun C hC a a' ↦ by rw [hT_inner]; exact S.inner_11 C hC a a'
    inner_22 := fun C hC a a' ↦ by rw [hT_inner]; exact S.inner_22 C hC a a'
    inner_33 := fun C hC a a' ↦ by rw [hT_inner]; exact S.inner_33 C hC a a'
    inner_12 := fun C hC a a' ↦ by rw [hT_inner]; exact S.inner_12 C hC a a'
    inner_13 := fun C hC a a' ↦ by rw [hT_inner]; exact S.inner_13 C hC a a'
    inner_23 := fun C hC a a' ↦ by rw [hT_inner]; exact S.inner_23 C hC a a'
  }
  exact ⟨S', rfl, Iff.rfl⟩

/-- **Maximal-support value-`1` SDP solution** (subsuming Lemma `lemma:includes_all_sat_assignments`
and Claim `claim:combineSDP`): for any satisfiable CSP instance `inst`, there exists a value-`1`
SDP solution in dimension `|V| · |A| + 1` whose local support at every clause contains the local
support of every value-`1` SDP solution (in any dimension), and in particular contains every
satisfying assignment. -/
theorem exists_max_support_sdp {V : Type*} [Fintype V] {Preds : Set (A × A × A → Bool)}
    {inst : CspInstance V A Preds} (hsat : IsSatisfiable inst) :
    ∃ S : BasicSdpSolution inst (Fintype.card V * Fintype.card A + 1),
      S.HasValueOne ∧
      (∀ (d' : ℕ) (S' : BasicSdpSolution inst d'), S'.HasValueOne →
        ∀ C ∈ inst.clauses.support, (S'.mu C).support ⊆ (S.mu C).support) ∧
      (∀ α : V → A, (∀ C ∈ inst.clauses.support, C.pred (α C.v₁, α C.v₂, α C.v₃) = true) →
        ∀ C ∈ inst.clauses.support, (α C.v₁, α C.v₂, α C.v₃) ∈ (S.mu C).support) := by
  classical
  let : Fintype inst.clauses.support := inst.finite_support.fintype
  let M := Fintype.card V * Fintype.card A + 1
  let suppPairs (S : BasicSdpSolution inst M) :
      Finset (inst.clauses.support × (A × A × A)) :=
    Finset.univ.filter fun p ↦ p.2 ∈ (S.mu p.1.1).support
  have hne : ∃ S : BasicSdpSolution inst M, S.HasValueOne := by
    obtain ⟨α, hα⟩ := hsat
    obtain ⟨S₀, hmu, hval⟩ := gram_dimension_reduction (integralSdpSolution inst α)
    refine ⟨S₀, hval.mpr ?_⟩
    intro C hC t ht
    have hEq : t = (α C.v₁, α C.v₂, α C.v₃) := by
      simpa [integralSdpSolution] using ht
    rw [hEq]
    exact hα C hC
  let cards : Set ℕ := {n | ∃ S : BasicSdpSolution inst M, S.HasValueOne ∧ (suppPairs S).card = n}
  have hcards_ne : cards.Nonempty := by
    obtain ⟨S₀, hS₀⟩ := hne
    exact ⟨(suppPairs S₀).card, S₀, hS₀, rfl⟩
  have hcards_bdd : BddAbove cards :=
    ⟨Fintype.card (inst.clauses.support × (A × A × A)), by
      rintro n ⟨S, _, rfl⟩; exact Finset.card_le_univ _⟩
  let nMax := sSup cards
  have hnMax : nMax ∈ cards := Nat.sSup_mem hcards_ne hcards_bdd
  obtain ⟨S, hS, hScard⟩ := hnMax
  have hmax : ∀ (d' : ℕ) (S' : BasicSdpSolution inst d'), S'.HasValueOne →
      ∀ C ∈ inst.clauses.support, (S'.mu C).support ⊆ (S.mu C).support := by
    intro d' S' hS' C hC t ht
    by_contra ht_not
    obtain ⟨Scomb, hmu, hval⟩ := gram_dimension_reduction (combineSdpSolutions S S')
    have hScomb_val : Scomb.HasValueOne := hval.mpr (combineSdpSolutions_hasValueOne hS hS')
    have hsub : suppPairs S ⊂ suppPairs Scomb := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro p hp
        simp only [suppPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rw [hmu, combineSdpSolutions_support]
        exact Or.inl hp
      · intro heq
        have hmem : (⟨C, hC⟩, t) ∈ suppPairs Scomb := by
          simp only [suppPairs, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hmu, combineSdpSolutions_support]
          exact Or.inr ht
        rw [← heq] at hmem
        simp only [suppPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact ht_not hmem
    have hlt : (suppPairs S).card < (suppPairs Scomb).card := Finset.card_lt_card hsub
    have hle : (suppPairs Scomb).card ≤ nMax :=
      le_csSup hcards_bdd ⟨Scomb, hScomb_val, rfl⟩
    omega
  refine ⟨S, hS, hmax, ?_⟩
  intro α hα C hC
  have hint_val : (integralSdpSolution inst α).HasValueOne := by
    intro C' hC' t ht
    have hEq : t = (α C'.v₁, α C'.v₂, α C'.v₃) := by simpa [integralSdpSolution] using ht
    rw [hEq]
    exact hα C' hC'
  exact hmax 1 (integralSdpSolution inst α) hint_val C hC (by simp [integralSdpSolution])

/-- **Uniform finiteness bound for universal embedding groups**: for every alphabet size `m`,
there is a finite constant `B` such that every nonempty non-`(ℤ, +)`-embeddable subset
`S ⊆ Fin m × Fin m × Fin m` and basepoint `(w₁, w₂, w₃)` has
`Nat.card (UniversalEmbeddingGroup w₁ w₂ w₃ S) ≤ B`. -/
theorem exists_universal_group_bound (m : ℕ) :
    ∃ B : ℕ, 0 < B ∧
      ∀ (w₁ w₂ w₃ : Fin m) (S : Set (Fin m × Fin m × Fin m)),
        S.Nonempty → ¬ HasIntEmbedding S →
        Nat.card (UniversalEmbeddingGroup w₁ w₂ w₃ S) ≤ B := by
  classical
  let Key := Fin m × Fin m × Fin m × Finset (Fin m × Fin m × Fin m)
  let cardOf (k : Key) : ℕ :=
    Nat.card (UniversalEmbeddingGroup k.1 k.2.1 k.2.2.1 (k.2.2.2 : Set (Fin m × Fin m × Fin m)))
  let B := Finset.univ.sup cardOf + 1
  refine ⟨B, Nat.succ_pos _, fun w₁ w₂ w₃ S _ _ ↦ ?_⟩
  let Sf : Finset (Fin m × Fin m × Fin m) := Set.toFinset S
  have hSf : (Sf : Set (Fin m × Fin m × Fin m)) = S := Set.coe_toFinset S
  have hle : cardOf (w₁, w₂, w₃, Sf) ≤ Finset.univ.sup cardOf :=
    Finset.le_sup (f := cardOf) (Finset.mem_univ (w₁, w₂, w₃, Sf))
  have hEq : Nat.card (UniversalEmbeddingGroup w₁ w₂ w₃ S) = cardOf (w₁, w₂, w₃, Sf) := by
    simp only [cardOf, hSf]
  omega

end CspAndSdp

end CslibFrontier.Computability.Complexity
