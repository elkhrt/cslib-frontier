/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Submodular.Basic
public import CslibFrontier.Algorithms.Lean.Query.Submodular.ValueQuery
public import Mathlib.Data.Finset.Image

import Mathlib.Algebra.Order.Group.Defs

/-!
# Contraction, Pullback, and Value-Oracle Combinators for Submodular Functions

This module extends `CslibFrontier.Algorithms.Lean.Submodular.Basic` with standard closure
operations on submodular set functions and their value-oracle query trees:

1. **Submodular contraction (conditioning)**: `submodularShift f A X := f (A ∪ X) - f A` preserves
   monotonicity, nonnegativity, and submodularity, and satisfies the composition law
   `submodularShift (submodularShift f A) B = submodularShift f (A ∪ B)`.
2. **Partial-map pullback**: `partialImage φ X` lifts a partial map `φ : α → Option β` to
   `Finset α → Finset β`; pulling back any monotone submodular function along `partialImage φ`
   preserves monotonicity and submodularity.
3. **Value-oracle query combinators**: `liftPartialImage` and `reindexValueQuery` transport
   `FreeM (ValueQuery _ _)` programs across partial maps and equivalences while preserving
   exact evaluation semantics and query counts.

## Main definitions

* `CslibFrontier.Algorithms.Lean.Submodular.submodularShift`: contracted set function
  `X ↦ f (A ∪ X) - f A`.
* `CslibFrontier.Algorithms.Lean.Submodular.partialImage`: finset image under a partial map
  `α → Option β`.
* `CslibFrontier.Algorithms.Lean.Submodular.liftPartialImage`: lift a `ValueQuery` program
  along a partial map.
* `CslibFrontier.Algorithms.Lean.Submodular.reindexValueQuery`: reindex a `ValueQuery` program
  along an equivalence `α ≃ β`.

## Main results

* `monotone_submodularShift`, `nonneg_submodularShift`, `isSubmodular_submodularShift`,
  `submodularShift_submodularShift`: closure and composition of submodular contraction.
* `monotone_comp_partialImage`, `isSubmodular_comp_partialImage`: closure under partial-map
  pullback.
* `eval_liftPartialImage`, `countQueries_liftPartialImage`, `eval_reindexValueQuery`,
  `countQueries_reindexValueQuery`: exact semantics and query-count preservation.
-/

public section

namespace CslibFrontier.Algorithms.Lean.Submodular

open Cslib Cslib.Algorithms.Lean.Submodular Cslib.Query

section SubmodularClosure

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The contracted (conditioned) set function `g(X) = f(A ∪ X) - f(A)`. -/
@[expose] def submodularShift {γ : Type*} [Sub γ] (f : Finset α → γ) (A : Finset α)
    (X : Finset α) : γ :=
  f (A ∪ X) - f A

theorem submodularShift_apply {γ : Type*} [Sub γ] (f : Finset α → γ) (A X : Finset α) :
    submodularShift f A X = f (A ∪ X) - f A := rfl

@[simp]
theorem submodularShift_empty {γ : Type*} [AddGroup γ] (f : Finset α → γ) (A : Finset α) :
    submodularShift f A ∅ = 0 := by
  simp [submodularShift]

/-- Contracting a monotone set function preserves monotonicity. -/
theorem monotone_submodularShift {γ : Type*} [AddCommGroup γ] [PartialOrder γ]
    [IsOrderedAddMonoid γ] {f : Finset α → γ} (hmono : Monotone f) (A : Finset α) :
    Monotone (submodularShift f A) := by
  intro X Y hXY
  exact sub_le_sub_right (hmono (Finset.union_subset_union_right hXY)) (f A)

/-- Contracting a monotone set function yields a nonnegative set function. -/
theorem nonneg_submodularShift {γ : Type*} [AddCommGroup γ] [PartialOrder γ]
    [IsOrderedAddMonoid γ] {f : Finset α → γ} (hmono : Monotone f) (A X : Finset α) :
    0 ≤ submodularShift f A X :=
  sub_nonneg.mpr (hmono Finset.subset_union_left)

/-- Contracting a submodular set function preserves submodularity. -/
theorem isSubmodular_submodularShift {γ : Type*} [AddCommGroup γ] [PartialOrder γ]
    [IsOrderedAddMonoid γ] {f : Finset α → γ} (hf : IsSubmodular f) (A : Finset α) :
    IsSubmodular (submodularShift f A) := by
  intro X Y
  have h := hf (A ∪ X) (A ∪ Y)
  have hu : (A ∪ X) ∪ (A ∪ Y) = A ∪ (X ∪ Y) := by
    ext x
    simp [or_left_comm]
  have hi : (A ∪ X) ∩ (A ∪ Y) = A ∪ (X ∩ Y) := by
    ext x
    simp [or_and_left]
  rw [hu, hi] at h
  dsimp only [submodularShift]
  rw [sub_add_sub_comm, sub_add_sub_comm]
  exact sub_le_sub_right h (f A + f A)

/-- Composition of two contractions equals a single contraction by the union. -/
theorem submodularShift_submodularShift {γ : Type*} [AddCommGroup γ] (f : Finset α → γ)
    (A B X : Finset α) :
    submodularShift (submodularShift f A) B X = submodularShift f (A ∪ B) X := by
  simp only [submodularShift, ← Finset.union_assoc, sub_sub_sub_cancel_right]

/-- Image of a finset under a partial map `φ : α → Option β`. -/
@[expose] def partialImage (φ : α → Option β) (X : Finset α) : Finset β :=
  X.biUnion fun a => (φ a).toFinset

omit [DecidableEq α] in
@[simp]
theorem mem_partialImage {φ : α → Option β} {X : Finset α} {b : β} :
    b ∈ partialImage φ X ↔ ∃ a ∈ X, φ a = some b := by
  simp [partialImage]

omit [DecidableEq α] in
@[simp]
theorem partialImage_empty (φ : α → Option β) :
    partialImage φ ∅ = ∅ := by
  simp [partialImage]

@[simp]
theorem partialImage_union (φ : α → Option β) (X Y : Finset α) :
    partialImage φ (X ∪ Y) = partialImage φ X ∪ partialImage φ Y := by
  ext b
  simp only [mem_partialImage, Finset.mem_union]
  constructor
  · rintro ⟨a, ha | ha, hφ⟩
    · exact Or.inl ⟨a, ha, hφ⟩
    · exact Or.inr ⟨a, ha, hφ⟩
  · rintro (⟨a, ha, hφ⟩ | ⟨a, ha, hφ⟩)
    · exact ⟨a, Or.inl ha, hφ⟩
    · exact ⟨a, Or.inr ha, hφ⟩

theorem partialImage_inter_subset (φ : α → Option β) (X Y : Finset α) :
    partialImage φ (X ∩ Y) ⊆ partialImage φ X ∩ partialImage φ Y := by
  intro b hb
  rcases mem_partialImage.mp hb with ⟨a, ha, hφ⟩
  rcases Finset.mem_inter.mp ha with ⟨haX, haY⟩
  exact Finset.mem_inter.mpr
    ⟨mem_partialImage.mpr ⟨a, haX, hφ⟩, mem_partialImage.mpr ⟨a, haY, hφ⟩⟩

omit [DecidableEq α] in
theorem monotone_partialImage (φ : α → Option β) :
    Monotone (partialImage φ) := by
  intro X Y hXY b hb
  rcases mem_partialImage.mp hb with ⟨a, ha, hφ⟩
  exact mem_partialImage.mpr ⟨a, hXY ha, hφ⟩

omit [DecidableEq α] in
/-- Pulling back a monotone set function along `partialImage φ` preserves monotonicity. -/
theorem monotone_comp_partialImage {γ : Type*} [Preorder γ] {f : Finset β → γ}
    (hmono : Monotone f) (φ : α → Option β) :
    Monotone (fun X => f (partialImage φ X)) :=
  hmono.comp (monotone_partialImage φ)

/-- Pulling back a monotone submodular function along `partialImage φ` preserves submodularity. -/
theorem isSubmodular_comp_partialImage {γ : Type*} [AddCommMonoid γ] [Preorder γ]
    [IsOrderedAddMonoid γ] {f : Finset β → γ} (hf : IsSubmodular f) (hmono : Monotone f)
    (φ : α → Option β) :
    IsSubmodular (fun X => f (partialImage φ X)) := by
  intro X Y
  dsimp only
  rw [partialImage_union]
  exact (add_le_add_right (hmono (partialImage_inter_subset φ X Y)) _).trans
    (hf (partialImage φ X) (partialImage φ Y))

end SubmodularClosure

section ValueQueryCombinators

/-- Lift a `ValueQuery α δ` program to a `ValueQuery β δ` program along a partial map
`φ : α → Option β` by projecting each queried set with `partialImage φ`. -/
@[expose] def liftPartialImage {α β δ γ : Type} [DecidableEq β] (φ : α → Option β)
    (prog : FreeM (ValueQuery α δ) γ) : FreeM (ValueQuery β δ) γ :=
  prog.liftM fun op =>
    match op with
    | .value S => ValueQuery.ask (partialImage φ S)

theorem eval_liftPartialImage {α β δ γ : Type} [DecidableEq β] (φ : α → Option β)
    (f : Finset β → δ) (prog : FreeM (ValueQuery α δ) γ) :
    (liftPartialImage φ prog).eval (ValueQuery.oracleOf f) =
      prog.eval (ValueQuery.oracleOf (fun S => f (partialImage φ S))) := by
  induction prog with
  | pure a => rfl
  | lift_bind op cont ih =>
    cases op with
    | value S =>
      simp only [liftPartialImage, FreeM.bind_eq_bind, FreeM.liftM_bind, FreeM.liftM_lift,
        FreeM.eval_bind, ValueQuery.eval_ask, ValueQuery.oracleOf_value]
      exact ih _

theorem countQueries_liftPartialImage {α β δ γ : Type} [DecidableEq β] (φ : α → Option β)
    (f : Finset β → δ) (prog : FreeM (ValueQuery α δ) γ) :
    (liftPartialImage φ prog).countQueries (ValueQuery.oracleOf f) =
      prog.countQueries (ValueQuery.oracleOf (fun S => f (partialImage φ S))) := by
  induction prog with
  | pure a => rfl
  | lift_bind op cont ih =>
    cases op with
    | value S =>
      simp only [liftPartialImage, FreeM.bind_eq_bind, FreeM.liftM_bind, FreeM.liftM_lift,
        FreeM.countQueries_bind, ValueQuery.countQueries_ask, ValueQuery.eval_ask,
        ValueQuery.oracleOf_value]
      exact congrArg (1 + ·) (ih _)

/-- Reindex a `ValueQuery β δ` program along an equivalence `e : α ≃ β`. -/
@[expose] def reindexValueQuery {α β δ γ : Type} [DecidableEq α] (e : α ≃ β)
    (prog : FreeM (ValueQuery β δ) γ) : FreeM (ValueQuery α δ) γ :=
  prog.liftM fun op =>
    match op with
    | .value S => ValueQuery.ask (S.image e.symm)

theorem eval_reindexValueQuery {α β δ γ : Type} [DecidableEq α]
    (e : α ≃ β) (f : Finset α → δ) (prog : FreeM (ValueQuery β δ) γ) :
    (reindexValueQuery e prog).eval (ValueQuery.oracleOf f) =
      prog.eval (ValueQuery.oracleOf (fun S => f (S.image e.symm))) := by
  induction prog with
  | pure a => rfl
  | lift_bind op cont ih =>
    cases op with
    | value S =>
      simp only [reindexValueQuery, FreeM.bind_eq_bind, FreeM.liftM_bind, FreeM.liftM_lift,
        FreeM.eval_bind, ValueQuery.eval_ask, ValueQuery.oracleOf_value]
      exact ih _

theorem countQueries_reindexValueQuery {α β δ γ : Type} [DecidableEq α]
    (e : α ≃ β) (f : Finset α → δ) (prog : FreeM (ValueQuery β δ) γ) :
    (reindexValueQuery e prog).countQueries (ValueQuery.oracleOf f) =
      prog.countQueries (ValueQuery.oracleOf (fun S => f (S.image e.symm))) := by
  induction prog with
  | pure a => rfl
  | lift_bind op cont ih =>
    cases op with
    | value S =>
      simp only [reindexValueQuery, FreeM.bind_eq_bind, FreeM.liftM_bind, FreeM.liftM_lift,
        FreeM.countQueries_bind, ValueQuery.countQueries_ask, ValueQuery.eval_ask,
        ValueQuery.oracleOf_value]
      exact congrArg (1 + ·) (ih _)

end ValueQueryCombinators

end CslibFrontier.Algorithms.Lean.Submodular
