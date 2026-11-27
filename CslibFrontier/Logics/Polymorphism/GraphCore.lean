/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Combinatorics.SimpleGraph.Maps

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.OrderOfElement

/-!
# Graph Homomorphism Cores and Direct (Tensor) Products

This module provides basic textbook definitions and properties of graph homomorphism cores
(endomorphism-rigid graphs) and the direct (tensor / categorical) product of simple graphs.

## Main definitions

* `Cslib.Logic.SimpleGraph.IsEndoIso`: predicate that a graph endomorphism `f : G →g G` is
  induced by a graph automorphism `φ : G ≃g G`.
* `Cslib.Logic.SimpleGraph.IsHomCore`: predicate that every endomorphism of `G` is induced by an
  automorphism (i.e. `G` is a core graph).
* `Cslib.Logic.SimpleGraph.tensorProd`: the direct (tensor / categorical) product `G × H` of
  simple graphs.

## Main results

* `Cslib.Logic.SimpleGraph.isHomCore_iff_forall_bijective`,
  `Cslib.Logic.SimpleGraph.isHomCore_iff_forall_injective`,
  `Cslib.Logic.SimpleGraph.isHomCore_iff_forall_surjective`: on a finite vertex set, a simple
  graph is a core iff every endomorphism is bijective (equivalently injective, or surjective).
* `Cslib.Logic.SimpleGraph.isHomCore_top`: every finite complete graph is a core.
* `Cslib.Logic.SimpleGraph.isHomCore_iff_of_iso`: being a core is invariant under isomorphism.
-/

public section

namespace Cslib.Logic.SimpleGraph

variable {V W : Type*}

/-- An endomorphism `f : G →g G` is induced by an automorphism when there exists `φ : G ≃g G`
agreeing with `f` pointwise. -/
@[expose] def IsEndoIso {G : _root_.SimpleGraph V} (f : G →g G) : Prop :=
  ∃ φ : G ≃g G, ∀ x : V, f x = φ x

/-- A simple graph `G` is a **core** (homomorphism core) when every endomorphism `f : G →g G`
is induced by an automorphism. -/
@[expose] def IsHomCore (G : _root_.SimpleGraph V) : Prop :=
  ∀ f : G →g G, IsEndoIso f

/-- Every endomorphism induced by an automorphism is bijective. -/
theorem IsEndoIso.bijective {G : _root_.SimpleGraph V} {f : G →g G} (hf : IsEndoIso f) :
    Function.Bijective f := by
  rcases hf with ⟨φ, hφ⟩
  have hEq : (f : V → V) = (φ : V → V) := funext hφ
  rw [hEq]
  exact φ.bijective

private theorem iterate_map_rel {G : _root_.SimpleGraph V} (f : G →g G) :
    ∀ (k : ℕ) {u v : V}, G.Adj u v → G.Adj (f^[k] u) (f^[k] v)
  | 0, _, _, h => h
  | k + 1, _, _, h => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact f.map_rel (iterate_map_rel f k h)

/-- On a finite vertex set, every bijective graph endomorphism is induced by an automorphism. -/
theorem isEndoIso_of_bijective [Finite V] {G : _root_.SimpleGraph V} {f : G →g G}
    (hbij : Function.Bijective f) : IsEndoIso f := by
  have : Fintype V := Fintype.ofFinite V
  let e : Equiv.Perm V := Equiv.ofBijective f hbij
  have he_apply : ∀ x : V, (e : V → V) x = f x := fun _ => rfl
  have hpow : ∀ (k : ℕ) (x : V), ((e ^ k : Equiv.Perm V) : V → V) x = f^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, he_apply, Function.iterate_succ_apply', ih]
  have hpos : 0 < orderOf e := orderOf_pos e
  have hinv : e ^ (orderOf e - 1) * e = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  refine ⟨{ toEquiv := e, map_rel_iff' := fun {u v} => ?_ }, fun _ => rfl⟩
  refine ⟨fun h => ?_, fun h => f.map_rel h⟩
  have hstep := iterate_map_rel f (orderOf e - 1) h
  have hu : f^[orderOf e - 1] (f u) = u := by
    rw [← hpow (orderOf e - 1) (f u), ← he_apply u, ← Equiv.Perm.mul_apply, hinv]
    rfl
  have hv : f^[orderOf e - 1] (f v) = v := by
    rw [← hpow (orderOf e - 1) (f v), ← he_apply v, ← Equiv.Perm.mul_apply, hinv]
    rfl
  rwa [he_apply, he_apply, hu, hv] at hstep

/-- On a finite vertex set, `G` is a core iff every endomorphism of `G` is bijective. -/
theorem isHomCore_iff_forall_bijective [Finite V] {G : _root_.SimpleGraph V} :
    IsHomCore G ↔ ∀ f : G →g G, Function.Bijective f :=
  ⟨fun h f => (h f).bijective, fun h f => isEndoIso_of_bijective (h f)⟩

/-- On a finite vertex set, `G` is a core iff every endomorphism of `G` is injective. -/
theorem isHomCore_iff_forall_injective [Finite V] {G : _root_.SimpleGraph V} :
    IsHomCore G ↔ ∀ f : G →g G, Function.Injective f := by
  rw [isHomCore_iff_forall_bijective]
  exact ⟨fun h f => (h f).1, fun h f => Finite.injective_iff_bijective.mp (h f)⟩

/-- On a finite vertex set, `G` is a core iff every endomorphism of `G` is surjective. -/
theorem isHomCore_iff_forall_surjective [Finite V] {G : _root_.SimpleGraph V} :
    IsHomCore G ↔ ∀ f : G →g G, Function.Surjective f := by
  rw [isHomCore_iff_forall_bijective]
  exact ⟨fun h f => (h f).2, fun h f => Finite.surjective_iff_bijective.mp (h f)⟩

/-- Every finite complete graph is a core. -/
theorem isHomCore_top [Finite V] : IsHomCore (⊤ : _root_.SimpleGraph V) := by
  rw [isHomCore_iff_forall_injective]
  intro f u v huv
  by_contra hne
  have hadj : (⊤ : _root_.SimpleGraph V).Adj (f u) (f v) := f.map_rel hne
  rw [huv] at hadj
  exact (⊤ : _root_.SimpleGraph V).loopless.irrefl (f v) hadj

/-- Being a core is preserved by graph isomorphism. -/
theorem isHomCore_iff_of_iso {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    (e : G ≃g H) : IsHomCore G ↔ IsHomCore H := by
  constructor
  · intro hG f
    let g : G →g G := (e.symm.toHom.comp f).comp e.toHom
    rcases hG g with ⟨φ, hφ⟩
    refine ⟨(e.symm.trans φ).trans e, fun y => ?_⟩
    have h1 : e.symm (f (e (e.symm y))) = φ (e.symm y) := hφ (e.symm y)
    rw [e.apply_symm_apply] at h1
    have h2 := congrArg e h1
    simpa [e.apply_symm_apply] using h2
  · intro hH f
    let g : H →g H := (e.toHom.comp f).comp e.symm.toHom
    rcases hH g with ⟨φ, hφ⟩
    refine ⟨(e.trans φ).trans e.symm, fun x => ?_⟩
    have h1 : e (f (e.symm (e x))) = φ (e x) := hφ (e x)
    rw [e.symm_apply_apply] at h1
    have h2 := congrArg e.symm h1
    simpa [e.symm_apply_apply] using h2

/-- The direct (tensor / categorical) product `G × H` of simple graphs: `(u₁, v₁)` is adjacent to
`(u₂, v₂)` iff `G.Adj u₁ u₂` and `H.Adj v₁ v₂`. -/
@[expose] def tensorProd (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W) :
    _root_.SimpleGraph (V × W) where
  Adj p q := G.Adj p.1 q.1 ∧ H.Adj p.2 q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun p h => G.loopless.irrefl p.1 h.1⟩

/-- Adjacency in the direct (tensor) product of simple graphs. -/
@[simp] theorem tensorProd_adj (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (p q : V × W) : (tensorProd G H).Adj p q ↔ G.Adj p.1 q.1 ∧ H.Adj p.2 q.2 :=
  Iff.rfl

end Cslib.Logic.SimpleGraph
