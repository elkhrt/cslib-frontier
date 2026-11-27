/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Logics.Polymorphism.Minion
public import Mathlib.Data.ZMod.Basic

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

/-!
# Existential Pebble Games, Bounded Width, and Benchmark Relational Templates

This module defines partial homomorphisms (`CslibFrontier.Computability.Complexity.PartialHom`), the
existential
$k$-pebble winning condition (`CslibFrontier.Computability.Complexity.ExistentialPebbleWin`), and
the bounded-width
property (`CslibFrontier.Computability.Complexity.HasBoundedWidth`) for relational constraint
satisfaction templates,
together with benchmark relational languages and templates:

- Modulo-$n$ linear equations (`CslibFrontier.Computability.Complexity.LinRel`,
  `CslibFrontier.Computability.Complexity.linLang`,
  `CslibFrontier.Computability.Complexity.instLinStructureZMod`) over $\mathbb{Z}/n\mathbb{Z}$.
- Graph $2$-coloring (`CslibFrontier.Computability.Complexity.TwoColoringRel`,
  `CslibFrontier.Computability.Complexity.twoColoringLang`,
  `CslibFrontier.Computability.Complexity.instTwoColoringStructureBool`)
  over $K_2$, proving `CslibFrontier.Computability.Complexity.hasBoundedWidth_twoColoring` (width
  $3$) and
  strictness `CslibFrontier.Computability.Complexity.existentialPebbleWin_two_triangle_twoColoring`
  on $K_3$
  (width $2$ fails).

## Main definitions

- `CslibFrontier.Computability.Complexity.PartialHom`,
  `CslibFrontier.Computability.Complexity.PartialHom.restrict`,
  `CslibFrontier.Computability.Complexity.PartialHom.ofHom`: Partial homomorphisms on finite subsets
  of an
  `L`-structure and their restriction maps.
- `CslibFrontier.Computability.Complexity.ExistentialPebbleWin`,
  `CslibFrontier.Computability.Complexity.HasBoundedWidth`:
  Existential $k$-pebble winning families and bounded-width templates.
- `CslibFrontier.Computability.Complexity.LinRel`, `CslibFrontier.Computability.Complexity.linLang`,
  `CslibFrontier.Computability.Complexity.instLinStructureZMod`: Modulo-$n$ linear equation
  signature and
  structure on `ZMod n`.
- `CslibFrontier.Computability.Complexity.TwoColoringRel`,
  `CslibFrontier.Computability.Complexity.twoColoringLang`,
  `CslibFrontier.Computability.Complexity.instTwoColoringStructureBool`,
  `CslibFrontier.Computability.Complexity.twoColoringTriangleStructure`: Graph $2$-coloring
  signature,
  $K_2$ target structure on `Bool`, and $K_3$ triangle structure on `Fin 3`.

## Main results

- `CslibFrontier.Computability.Complexity.existentialPebbleWin_of_nonempty_hom`,
  `CslibFrontier.Computability.Complexity.hasBoundedWidth_punit`: Global-to-local pebble
  completeness and
  bounded width of `PUnit`.
- `CslibFrontier.Computability.Complexity.hasBoundedWidth_twoColoring`: Graph $2$-coloring (`K₂`)
  has bounded
  width $3$.
- `CslibFrontier.Computability.Complexity.existentialPebbleWin_two_triangle_twoColoring`: Duplicator
  wins the
  existential $2$-pebble game from $K_3$ to $K_2$ despite no global homomorphism existing.
-/

public section

universe u v w w'

namespace CslibFrontier.Computability.Complexity

open CslibFrontier.Logics.Polymorphism
open scoped CslibFrontier.Logics.Polymorphism

open FirstOrder Language Structure

/-! ### Partial Homomorphisms -/

section PartialHom

/-- A partial homomorphism `S → Y` on a finite subset `S : Finset X` of an `L`-structure `X`
into an `L`-structure `Y`, preserving all relation symbols of `L` on tuples in `S` (used for
relational languages `[L.IsRelational]`). -/
@[ext]
structure PartialHom (L : Language.{u, v}) {X : Type w} {Y : Type w'}
    [L.Structure X] [L.Structure Y] (S : Finset X) : Type (max w w') where
  /-- Underlying map from the finite subset `S` to `Y`. -/
  toFun : S → Y
  /-- Preservation of relation symbols on tuples taking values in `S`. -/
  map_rel' : ∀ {n : ℕ} (R : L.Relations n) (x : Fin n → S),
    RelMap R (fun i ↦ (x i : X)) → RelMap R (toFun ∘ x)

namespace PartialHom

variable {L : Language.{u, v}} {X : Type w} {Y : Type w'}
  [L.Structure X] [L.Structure Y]

/-- `FunLike` instance (inducing `CoeFun`) for `PartialHom L (Y := Y) S`. -/
instance instFunLike (S : Finset X) :
    FunLike (PartialHom L (Y := Y) S) S Y where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

/-- Underlying function `f.toFun` agrees with coercion to `S → Y`. -/
@[simp]
theorem toFun_eq_coe {S : Finset X} (f : PartialHom L (Y := Y) S) :
    f.toFun = ⇑f := by
  rfl

/-- Coercing a constructed `PartialHom.mk toFun map_rel'` to `S → Y` yields `toFun`. -/
@[simp]
theorem coe_mk {S : Finset X} (toFun : S → Y)
    (map_rel' : ∀ {n : ℕ} (R : L.Relations n) (x : Fin n → S),
      RelMap R (fun i ↦ (x i : X)) → RelMap R (toFun ∘ x)) :
    ⇑(PartialHom.mk toFun map_rel' : PartialHom L (Y := Y) S) = toFun := by
  rfl

/-- Pointwise extensionality for `PartialHom`. -/
theorem ext_apply {S : Finset X} {f g : PartialHom L (Y := Y) S} (h : ∀ x : S, f x = g x) :
    f = g :=
  DFunLike.ext f g h

/-- A partial homomorphism preserves relation symbols on tuples in `S`. -/
theorem map_rel {S : Finset X} (f : PartialHom L (Y := Y) S) {n : ℕ} (R : L.Relations n)
    (x : Fin n → S) (hx : RelMap R (fun i ↦ (x i : X))) :
    RelMap R (f ∘ x) :=
  f.map_rel' R x hx

/-- Restrict a partial homomorphism `f` on `S` to a subset `S' ⊆ S`. -/
def restrict {S' S : Finset X} (h : S' ⊆ S) (f : PartialHom L (Y := Y) S) :
    PartialHom L (Y := Y) S' where
  toFun x := f ⟨x.1, h x.2⟩
  map_rel' R x hx := f.map_rel' R (fun i ↦ ⟨(x i).1, h (x i).2⟩) hx

/-- Pointwise evaluation of a restricted partial homomorphism. -/
@[simp]
theorem restrict_apply {S' S : Finset X} (h : S' ⊆ S) (f : PartialHom L (Y := Y) S)
    (x : S') :
    f.restrict h x = f ⟨x.1, h x.2⟩ := by
  rfl

/-- Restricting a partial homomorphism along `Finset.Subset.rfl` yields the same partial
homomorphism. -/
@[simp]
theorem restrict_self {S : Finset X} (f : PartialHom L (Y := Y) S) :
    f.restrict Finset.Subset.rfl = f :=
  ext_apply fun _ ↦ rfl

/-- Iterated restriction of partial homomorphisms composes along subset transitivity. -/
theorem restrict_restrict {S'' S' S : Finset X} (h₁ : S'' ⊆ S') (h₂ : S' ⊆ S)
    (f : PartialHom L (Y := Y) S) :
    (f.restrict h₂).restrict h₁ = f.restrict (h₁.trans h₂) :=
  ext_apply fun _ ↦ rfl

/-- Restrict a global `L`-homomorphism `φ : X →[L] Y` to any finite subset `S : Finset X`. -/
def ofHom (φ : X →[L] Y) (S : Finset X) : PartialHom L (Y := Y) S where
  toFun x := φ x.1
  map_rel' R x hx := φ.map_rel R (fun i ↦ (x i : X)) hx

/-- Pointwise evaluation of `PartialHom.ofHom φ S`. -/
@[simp]
theorem ofHom_apply (φ : X →[L] Y) (S : Finset X) (x : S) :
    ofHom φ S x = φ x.1 := by
  rfl

end PartialHom

end PartialHom

/-! ### Existential Pebble Games and Bounded Width -/

section PebbleWidth

/-- Duplicator wins the existential `k`-pebble game from `X` to `Y` over language `L`: there is a
nonempty downward-closed family `ℋ` of partial homomorphisms of domain size at most `k` satisfying
the back-and-forth extension property below `k` pebbles. -/
def ExistentialPebbleWin (L : Language.{u, v}) (k : ℕ) (X : Type w) (Y : Type w')
    [L.Structure X] [L.Structure Y] : Prop :=
  let _ := Classical.decEq X
  ∃ ℋ : Set (Σ S : Finset X, PartialHom L (Y := Y) S),
    (∀ p ∈ ℋ, p.1.card ≤ k) ∧
    (∃ f : PartialHom L (Y := Y) ∅, ⟨∅, f⟩ ∈ ℋ) ∧
    (∀ {S S' : Finset X} (hsub : S' ⊆ S) {f : PartialHom L (Y := Y) S},
      ⟨S, f⟩ ∈ ℋ → ⟨S', f.restrict hsub⟩ ∈ ℋ) ∧
    (∀ {S : Finset X} {f : PartialHom L (Y := Y) S},
      ⟨S, f⟩ ∈ ℋ → S.card < k → ∀ x : X,
        ∃ g : PartialHom L (Y := Y) (insert x S),
          ⟨insert x S, g⟩ ∈ ℋ ∧ g.restrict (Finset.subset_insert x S) = f)

private theorem sigma_partialHom_eq_restrict {L : Language.{u, v}} {X : Type w} {Y : Type w'}
    [L.Structure X] [L.Structure Y] {S₁ S₂ : Finset X} (h : S₁ = S₂)
    (f : PartialHom L (Y := Y) S₂) :
    (⟨S₁, f.restrict h.subset⟩ : Σ T : Finset X, PartialHom L (Y := Y) T) = ⟨S₂, f⟩ := by
  subst h
  simp

/-- Characterization of `ExistentialPebbleWin` for any `[DecidableEq X]` instance. -/
theorem existentialPebbleWin_iff (L : Language.{u, v}) (k : ℕ) (X : Type w) (Y : Type w')
    [DecidableEq X] [L.Structure X] [L.Structure Y] :
    ExistentialPebbleWin L k X Y ↔
      ∃ ℋ : Set (Σ S : Finset X, PartialHom L (Y := Y) S),
        (∀ p ∈ ℋ, p.1.card ≤ k) ∧
        (∃ f : PartialHom L (Y := Y) ∅, ⟨∅, f⟩ ∈ ℋ) ∧
        (∀ {S S' : Finset X} (hsub : S' ⊆ S) {f : PartialHom L (Y := Y) S},
          ⟨S, f⟩ ∈ ℋ → ⟨S', f.restrict hsub⟩ ∈ ℋ) ∧
        (∀ {S : Finset X} {f : PartialHom L (Y := Y) S},
          ⟨S, f⟩ ∈ ℋ → S.card < k → ∀ x : X,
            ∃ g : PartialHom L (Y := Y) (insert x S),
              ⟨insert x S, g⟩ ∈ ℋ ∧ g.restrict (Finset.subset_insert x S) = f) := by
  unfold ExistentialPebbleWin
  have hInsEq (x : X) (S : Finset X) :
      @insert X (Finset X) (@Finset.instInsert X (Classical.decEq X)) x S = insert x S := by
    ext y; simp [Finset.mem_insert]
  constructor
  · rintro ⟨ℋ, h1, h2, h3, h4⟩
    refine ⟨ℋ, h1, h2, h3, fun {S f} hf hk x ↦ ?_⟩
    obtain ⟨g, hg, hgres⟩ := h4 hf hk x
    have hEq := hInsEq x S
    refine ⟨g.restrict hEq.symm.subset, ?_, ?_⟩
    · rwa [sigma_partialHom_eq_restrict hEq.symm g]
    · rw [PartialHom.restrict_restrict]
      exact hgres
  · rintro ⟨ℋ, h1, h2, h3, h4⟩
    refine ⟨ℋ, h1, h2, h3, fun {S f} hf hk x ↦ ?_⟩
    obtain ⟨g, hg, hgres⟩ := h4 hf hk x
    have hEq := hInsEq x S
    refine ⟨g.restrict hEq.subset, ?_, ?_⟩
    · rwa [sigma_partialHom_eq_restrict hEq g]
    · rw [PartialHom.restrict_restrict]
      exact hgres

/-- An `L`-structure `Y` has *bounded width* if there exists a pebble bound `k : ℕ` such that
every finite `L`-structure `X` admitting a winning existential `k`-pebble strategy into `Y` admits
a global homomorphism `X →[L] Y`. -/
def HasBoundedWidth (L : Language.{u, v}) (Y : Type w) [L.Structure Y] : Prop :=
  ∃ k : ℕ, ∀ (X : Type) [Finite X] [L.Structure X],
    ExistentialPebbleWin L k X Y → Nonempty (X →[L] Y)

/-- Characterization of `HasBoundedWidth`. -/
theorem hasBoundedWidth_iff (L : Language.{u, v}) (Y : Type w) [L.Structure Y] :
    HasBoundedWidth L Y ↔
      ∃ k : ℕ, ∀ (X : Type) [Finite X] [L.Structure X],
        ExistentialPebbleWin L k X Y → Nonempty (X →[L] Y) := by
  rfl

/-- Existence of a global homomorphism `X →[L] Y` implies an existential `k`-pebble winning
strategy for every pebble count `k : ℕ`. -/
theorem existentialPebbleWin_of_nonempty_hom {L : Language.{u, v}}
    {X : Type w} {Y : Type w'} [L.Structure X] [L.Structure Y]
    (h : Nonempty (X →[L] Y)) (k : ℕ) :
    ExistentialPebbleWin L k X Y := by
  classical
  rw [existentialPebbleWin_iff]
  obtain ⟨φ⟩ := h
  refine ⟨{p | p.1.card ≤ k ∧ p.2 = PartialHom.ofHom φ p.1}, ?_, ?_, ?_, ?_⟩
  · exact fun _ hp ↦ hp.1
  · exact ⟨PartialHom.ofHom φ ∅, ⟨by simp, rfl⟩⟩
  · intro S S' hsub f hf
    have hf2 : f = PartialHom.ofHom φ S := hf.2
    refine ⟨(Finset.card_le_card hsub).trans hf.1, PartialHom.ext_apply fun x ↦ ?_⟩
    rw [hf2]
    simp
  · intro S f hf hk x
    have hf2 : f = PartialHom.ofHom φ S := hf.2
    refine ⟨PartialHom.ofHom φ (insert x S),
      ⟨(Finset.card_insert_le x S).trans hk, rfl⟩,
      PartialHom.ext_apply fun y ↦ ?_⟩
    rw [hf2]
    simp

/-- The terminal one-element `L`-structure `PUnit` has bounded width (in fact width `0`). -/
theorem hasBoundedWidth_punit (L : Language.{u, v}) :
    let _ := punitStructure.{u, v, w} L
    HasBoundedWidth L PUnit.{w + 1} :=
  let _ := punitStructure.{u, v, w} L
  ⟨0, fun X _ _ _ ↦ ⟨homTerminal L X⟩⟩

end PebbleWidth

/-! ### Modulo-`n` Linear Equations Language and Structure -/

section LinearEquations

/-- Relation symbols for systems of modulo-`n` linear equations of width at most `3`:
a unary constraint `.zero` (`x₀ = 0`) and ternary constraints `.sumEq b` (`x₀ + x₁ + x₂ = b`). -/
inductive LinRel (n : ℕ) : ℕ → Type
  | zero : LinRel n 1
  | sumEq (b : ZMod n) : LinRel n 3
  deriving DecidableEq

/-- Purely relational first-order language for modulo-`n` linear equation systems. -/
@[expose]
def linLang (n : ℕ) : Language.{0, 0} :=
  relational (LinRel n)

/-- `linLang n` has `PEmpty` function symbols in every arity. -/
@[simp]
theorem linLang_functions (n k : ℕ) : (linLang n).Functions k = PEmpty :=
  rfl

/-- `linLang n` has `LinRel n k` as its type of `k`-ary relation symbols. -/
@[simp]
theorem linLang_relations (n k : ℕ) : (linLang n).Relations k = LinRel n k :=
  rfl

/-- `linLang n` is a relational language. -/
instance instIsRelationalLinLang (n : ℕ) : (linLang n).IsRelational :=
  instIsRelationalRelational (LinRel n)

/-- `linLang n` has no nullary relation symbols. -/
instance instIsEmptyLinLangZero (n : ℕ) : IsEmpty ((linLang n).Relations 0) :=
  ⟨fun r ↦ by cases r⟩

/-- Equivalence between `Σ k, LinRel n k` and `Unit ⊕ ZMod n`. -/
def linLangRelEquiv (n : ℕ) : (Σ k, LinRel n k) ≃ Unit ⊕ ZMod n where
  toFun
    | ⟨_, .zero⟩ => Sum.inl ()
    | ⟨_, .sumEq b⟩ => Sum.inr b
  invFun
    | Sum.inl () => ⟨1, .zero⟩
    | Sum.inr b => ⟨3, .sumEq b⟩
  left_inv
    | ⟨_, .zero⟩ => rfl
    | ⟨_, .sumEq _⟩ => rfl
  right_inv
    | Sum.inl () => rfl
    | Sum.inr _ => rfl

/-- Forward evaluation of `linLangRelEquiv` on `.zero`. -/
@[simp]
theorem linLangRelEquiv_apply_zero (n : ℕ) :
    linLangRelEquiv n ⟨1, LinRel.zero⟩ = Sum.inl () := by
  rfl

/-- Forward evaluation of `linLangRelEquiv` on `.sumEq b`. -/
@[simp]
theorem linLangRelEquiv_apply_sumEq (n : ℕ) (b : ZMod n) :
    linLangRelEquiv n ⟨3, LinRel.sumEq b⟩ = Sum.inr b := by
  rfl

/-- Inverse evaluation of `linLangRelEquiv` on `Sum.inl ()`. -/
@[simp]
theorem linLangRelEquiv_symm_apply_inl (n : ℕ) :
    (linLangRelEquiv n).symm (Sum.inl ()) = ⟨1, LinRel.zero⟩ := by
  rfl

/-- Inverse evaluation of `linLangRelEquiv` on `Sum.inr b`. -/
@[simp]
theorem linLangRelEquiv_symm_apply_inr (n : ℕ) (b : ZMod n) :
    (linLangRelEquiv n).symm (Sum.inr b) = ⟨3, LinRel.sumEq b⟩ := by
  rfl

/-- For `n ≠ 0`, `linLang n` has finitely many relation symbols across all arities. -/
instance instFiniteSigmaLinLangRelations (n : ℕ) [NeZero n] :
    Finite (Σ k, (linLang n).Relations k) :=
  Finite.of_equiv (Unit ⊕ ZMod n) (linLangRelEquiv n).symm

/-- Canonical `(linLang n)`-structure on `ZMod n`, interpreting `.zero` as `y 0 = 0` and
`.sumEq b` as `y 0 + y 1 + y 2 = b`. -/
instance instLinStructureZMod (n : ℕ) : (linLang n).Structure (ZMod n) where
  funMap {_} f := isEmptyElim f
  RelMap {_} r y :=
    match r with
    | .zero => y 0 = 0
    | .sumEq b => y 0 + y 1 + y 2 = b

/-- Interpretation of `LinRel.zero` in `ZMod n` is `y 0 = 0`. -/
@[simp]
theorem linLang_relMap_zero_iff (n : ℕ) (y : Fin 1 → ZMod n) :
    RelMap (L := linLang n) LinRel.zero y ↔ y 0 = 0 := by
  rfl

/-- Interpretation of `LinRel.sumEq b` in `ZMod n` is `y 0 + y 1 + y 2 = b`. -/
@[simp]
theorem linLang_relMap_sumEq_iff (n : ℕ) (b : ZMod n) (y : Fin 3 → ZMod n) :
    RelMap (L := linLang n) (LinRel.sumEq b) y ↔ y 0 + y 1 + y 2 = b := by
  rfl

end LinearEquations

/-! ### Graph 2-Coloring Language, Width 3 Upper Bound, and Width 2 Lower Bound -/

section TwoColoring

/-- Single binary disequality relation symbol for the $2$-coloring ($K_2$) CSP language. -/
inductive TwoColoringRel : ℕ → Type
  | ne : TwoColoringRel 2
  deriving DecidableEq

/-- Purely relational first-order language for graph $2$-coloring. -/
@[expose]
def twoColoringLang : Language.{0, 0} :=
  relational TwoColoringRel

/-- `twoColoringLang` has `PEmpty` function symbols in every arity. -/
@[simp]
theorem twoColoringLang_functions (k : ℕ) : twoColoringLang.Functions k = PEmpty :=
  rfl

/-- `twoColoringLang` has `TwoColoringRel k` as its type of `k`-ary relation symbols. -/
@[simp]
theorem twoColoringLang_relations (k : ℕ) :
    twoColoringLang.Relations k = TwoColoringRel k :=
  rfl

/-- `twoColoringLang` is a relational language. -/
instance instIsRelationalTwoColoringLang : twoColoringLang.IsRelational :=
  instIsRelationalRelational TwoColoringRel

/-- `twoColoringLang` has no nullary relation symbols. -/
instance instIsEmptyTwoColoringZero : IsEmpty (twoColoringLang.Relations 0) :=
  ⟨fun r ↦ by cases r⟩

/-- Equivalence between `Σ k, TwoColoringRel k` and `Unit`. -/
def twoColoringRelEquiv : (Σ k, TwoColoringRel k) ≃ Unit where
  toFun | ⟨_, .ne⟩ => ()
  invFun | () => ⟨2, .ne⟩
  left_inv | ⟨_, .ne⟩ => rfl
  right_inv | () => rfl

/-- Forward evaluation of `twoColoringRelEquiv`. -/
@[simp]
theorem twoColoringRelEquiv_apply :
    twoColoringRelEquiv ⟨2, TwoColoringRel.ne⟩ = () := by
  rfl

/-- Inverse evaluation of `twoColoringRelEquiv`. -/
@[simp]
theorem twoColoringRelEquiv_symm_apply :
    twoColoringRelEquiv.symm () = ⟨2, TwoColoringRel.ne⟩ := by
  rfl

/-- `twoColoringLang` has finitely many relation symbols across all arities. -/
instance instFiniteSigmaTwoColoring : Finite (Σ k, twoColoringLang.Relations k) :=
  Finite.of_equiv Unit twoColoringRelEquiv.symm

/-- Canonical $K_2$ (`twoColoringLang`) structure on `Bool`, interpreting `.ne` as `y 0 ≠ y 1`. -/
instance instTwoColoringStructureBool : twoColoringLang.Structure Bool where
  funMap {_} f := isEmptyElim f
  RelMap {_} r y := match r with | .ne => y 0 ≠ y 1

/-- Interpretation of `TwoColoringRel.ne` in `Bool` is `y 0 ≠ y 1`. -/
@[simp]
theorem twoColoringLang_relMap_ne_iff (y : Fin 2 → Bool) :
    RelMap (L := twoColoringLang) TwoColoringRel.ne y ↔ y 0 ≠ y 1 := by
  rfl

private inductive TwoColoringWalk {X : Type*} (Adj : X → X → Prop) (u : X) : X → ℕ → Prop
  | refl : TwoColoringWalk Adj u u 0
  | step {v w : X} {m : ℕ} :
      TwoColoringWalk Adj u v m → Adj v w → TwoColoringWalk Adj u w (m + 1)

private theorem twoColoringWalk_cons_left {X : Type*} {Adj : X → X → Prop}
    {u v w : X} {m : ℕ} (huv : Adj u v) (hvw : TwoColoringWalk Adj v w m) :
    TwoColoringWalk Adj u w (m + 1) := by
  induction hvw with
  | refl => exact TwoColoringWalk.step TwoColoringWalk.refl huv
  | step _ hxy ih => exact TwoColoringWalk.step ih hxy

private theorem twoColoringWalk_symm {X : Type*} {Adj : X → X → Prop}
    (hsymm : ∀ {a b : X}, Adj a b → Adj b a) {u v : X} {m : ℕ}
    (h : TwoColoringWalk Adj u v m) : TwoColoringWalk Adj v u m := by
  induction h with
  | refl => exact TwoColoringWalk.refl
  | step _ hxy ih => exact twoColoringWalk_cons_left (hsymm hxy) ih

private theorem twoColoringWalk_trans {X : Type*} {Adj : X → X → Prop}
    {u v w : X} {m₁ m₂ : ℕ}
    (h₁ : TwoColoringWalk Adj u v m₁) (h₂ : TwoColoringWalk Adj v w m₂) :
    TwoColoringWalk Adj u w (m₁ + m₂) := by
  induction h₂ with
  | refl => exact h₁
  | step _ hxy ih => exact TwoColoringWalk.step ih hxy

private theorem anchored_pebble_walk_invariant {X : Type} [DecidableEq X]
    [twoColoringLang.Structure X]
    {ℋ : Set (Σ S : Finset X, PartialHom twoColoringLang (Y := Bool) S)}
    (hDown : ∀ {S S' : Finset X} (hsub : S' ⊆ S)
      {f : PartialHom twoColoringLang (Y := Bool) S}, ⟨S, f⟩ ∈ ℋ → ⟨S', f.restrict hsub⟩ ∈ ℋ)
    (hUp : ∀ {S : Finset X} {f : PartialHom twoColoringLang (Y := Bool) S},
      ⟨S, f⟩ ∈ ℋ → S.card < 3 → ∀ x : X,
        ∃ g : PartialHom twoColoringLang (Y := Bool) (insert x S),
          ⟨insert x S, g⟩ ∈ ℋ ∧ g.restrict (Finset.subset_insert x S) = f)
    {u : X} (f₀ : PartialHom twoColoringLang (Y := Bool) {u}) (hf₀ : ⟨{u}, f₀⟩ ∈ ℋ) :
    ∀ {v : X} {m : ℕ}, TwoColoringWalk
      (fun a b : X ↦ RelMap (L := twoColoringLang) TwoColoringRel.ne ![a, b] ∨
        RelMap (L := twoColoringLang) TwoColoringRel.ne ![b, a]) u v m →
    ∃ f : PartialHom twoColoringLang (Y := Bool) {u, v},
      ⟨{u, v}, f⟩ ∈ ℋ ∧
      f ⟨u, Finset.mem_insert_self u {v}⟩ = f₀ ⟨u, Finset.mem_singleton_self u⟩ ∧
      f ⟨v, Finset.mem_insert_of_mem (Finset.mem_singleton_self v)⟩ =
        if m % 2 = 0 then f₀ ⟨u, Finset.mem_singleton_self u⟩
        else !(f₀ ⟨u, Finset.mem_singleton_self u⟩)
  | _, _, .refl => by
    have hsub : ({u, u} : Finset X) ⊆ {u} := by
      intro z hz
      rcases Finset.mem_insert.mp hz with hzu | hz'
      · rw [hzu]
        exact Finset.mem_singleton_self u
      · exact hz'
    refine ⟨f₀.restrict hsub, hDown hsub hf₀, ?_, ?_⟩ <;> simp
  | _, _, @TwoColoringWalk.step _ _ _ v w m' hw' hvw => by
    let c : Bool := f₀ ⟨u, Finset.mem_singleton_self u⟩
    obtain ⟨fm, hfm, hfm_u, hfm_v⟩ := anchored_pebble_walk_invariant hDown hUp f₀ hf₀ hw'
    have hcard : ({u, v} : Finset X).card < 3 := by
      have h1 : ({u, v} : Finset X).card ≤ ({v} : Finset X).card + 1 :=
        Finset.card_insert_le u {v}
      have h2 : ({v} : Finset X).card = 1 := Finset.card_singleton v
      omega
    obtain ⟨g, hg, hgres⟩ := hUp hfm hcard w
    let T : Finset X := insert w {u, v}
    have hgu : g ⟨u, Finset.mem_insert_of_mem (Finset.mem_insert_self u {v})⟩ = c := by
      have := DFunLike.congr_fun hgres ⟨u, Finset.mem_insert_self u {v}⟩
      simpa [PartialHom.restrict_apply, c] using this.trans hfm_u
    have hgv : g ⟨v, Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))⟩ =
        if m' % 2 = 0 then c else !c := by
      have := DFunLike.congr_fun hgres
        ⟨v, Finset.mem_insert_of_mem (Finset.mem_singleton_self v)⟩
      simpa [PartialHom.restrict_apply, c] using this.trans hfm_v
    have hgvw_ne :
        g ⟨v, Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))⟩ ≠
          g ⟨w, Finset.mem_insert_self w {u, v}⟩ := by
      let pv : T :=
        ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))⟩
      let pw : T := ⟨w, Finset.mem_insert_self w {u, v}⟩
      rcases hvw with hvw1 | hvw2
      · have hx : (fun i : Fin 2 ↦ ((![pv, pw] i : T) : X)) = ![v, w] :=
          funext fun i ↦ by fin_cases i <;> rfl
        have hrel := g.map_rel TwoColoringRel.ne ![pv, pw] (by rw [hx]; exact hvw1)
        exact (twoColoringLang_relMap_ne_iff (g ∘ ![pv, pw])).mp hrel
      · have hx : (fun i : Fin 2 ↦ ((![pw, pv] i : T) : X)) = ![w, v] :=
          funext fun i ↦ by fin_cases i <;> rfl
        have hrel := g.map_rel TwoColoringRel.ne ![pw, pv] (by rw [hx]; exact hvw2)
        exact ((twoColoringLang_relMap_ne_iff (g ∘ ![pw, pv])).mp hrel).symm
    have hgw : g ⟨w, Finset.mem_insert_self w {u, v}⟩ =
        if (m' + 1) % 2 = 0 then c else !c := by
      have hne' : (!g ⟨v, Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))⟩) =
          g ⟨w, Finset.mem_insert_self w {u, v}⟩ := by
        cases hv : g ⟨v, Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))⟩ <;>
          cases hw' : g ⟨w, Finset.mem_insert_self w {u, v}⟩ <;> simp_all
      rw [← hne', hgv]
      by_cases hm : m' % 2 = 0
      · have hm1 : (m' + 1) % 2 ≠ 0 := by omega
        simp [hm, hm1]
      · have hm1 : (m' + 1) % 2 = 0 := by omega
        simp [hm, hm1]
    have hsub' : ({u, w} : Finset X) ⊆ insert w {u, v} := by
      intro z hz
      rcases Finset.mem_insert.mp hz with hzu | hz'
      · rw [hzu]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self u {v})
      · rw [Finset.mem_singleton.mp hz']
        exact Finset.mem_insert_self w {u, v}
    refine ⟨g.restrict hsub', hDown hsub' hg, ?_, ?_⟩
    · simpa [PartialHom.restrict_apply] using hgu
    · simpa [PartialHom.restrict_apply] using hgw

/-- Graph $2$-coloring (`K₂`) has bounded width $3$: any finite structure admitting a winning
existential $3$-pebble strategy into `Bool` admits a global homomorphism into `Bool`. -/
theorem hasBoundedWidth_twoColoring : HasBoundedWidth twoColoringLang Bool := by
  classical
  refine ⟨3, fun X _ _ hWin ↦ ?_⟩
  obtain ⟨ℋ, _, ⟨fEmpty, hfEmpty⟩, hDown, hUp⟩ := (existentialPebbleWin_iff _ _ _ _).mp hWin
  let Adj (a b : X) : Prop :=
    RelMap (L := twoColoringLang) TwoColoringRel.ne ![a, b] ∨
      RelMap (L := twoColoringLang) TwoColoringRel.ne ![b, a]
  have hAdj_symm : ∀ {a b : X}, Adj a b → Adj b a := fun h ↦ h.symm
  let Connected (a b : X) : Prop := ∃ m : ℕ, TwoColoringWalk Adj a b m
  let s : Setoid X :=
    ⟨Connected, ⟨fun x ↦ ⟨0, TwoColoringWalk.refl⟩,
      fun ⟨m, hm⟩ ↦ ⟨m, twoColoringWalk_symm hAdj_symm hm⟩,
      fun ⟨m₁, h₁⟩ ⟨m₂, h₂⟩ ↦ ⟨m₁ + m₂, twoColoringWalk_trans h₁ h₂⟩⟩⟩
  let r (x : X) : X := Quotient.out (Quotient.mk s x)
  have hr_conn (x : X) : Connected (r x) x :=
    Quotient.exact (Quotient.out_eq (Quotient.mk s x))
  have hr_eq {a b : X} (h : Adj a b) : r a = r b :=
    congrArg Quotient.out (Quotient.sound ⟨1, TwoColoringWalk.step TwoColoringWalk.refl h⟩)
  have hSingle (u : X) : ∃ f : PartialHom twoColoringLang (Y := Bool) {u}, ⟨{u}, f⟩ ∈ ℋ := by
    obtain ⟨g, hg, _⟩ := hUp hfEmpty (by simp) u
    have hsub : ({u} : Finset X) ⊆ insert u ∅ := by simp
    exact ⟨g.restrict hsub, hDown hsub hg⟩
  choose fSingle hfSingle using hSingle
  let baseColor (u : X) : Bool := fSingle u ⟨u, Finset.mem_singleton_self u⟩
  let col (x : X) : Bool :=
    if ∃ m : ℕ, TwoColoringWalk Adj (r x) x m ∧ m % 2 = 0
    then baseColor (r x)
    else !(baseColor (r x))
  refine ⟨homOfRel col fun {n} rel y hy ↦ ?_⟩
  cases rel
  have hy_vec : y = ![y 0, y 1] := funext fun i ↦ by fin_cases i <;> rfl
  have hadj : Adj (y 0) (y 1) := Or.inl (by rw [← hy_vec]; exact hy)
  have hr0 : r (y 0) = r (y 1) := hr_eq hadj
  rw [twoColoringLang_relMap_ne_iff]
  change col (y 0) ≠ col (y 1)
  intro hcol_eq
  have hOddLoop : ∃ M : ℕ, TwoColoringWalk Adj (r (y 0)) (r (y 0)) M ∧ M % 2 = 1 := by
    by_cases h0 : ∃ m : ℕ, TwoColoringWalk Adj (r (y 0)) (y 0) m ∧ m % 2 = 0
    · have h1 : ∃ m : ℕ, TwoColoringWalk Adj (r (y 1)) (y 1) m ∧ m % 2 = 0 := by
        by_contra h1'
        have hbad : baseColor (r (y 0)) = (!baseColor (r (y 1))) := by
          simpa [col, h0, h1'] using hcol_eq
        rw [← hr0] at hbad
        cases hb : baseColor (r (y 0)) <;> simp [hb] at hbad
      obtain ⟨m₀, hw₀, hm₀⟩ := h0
      obtain ⟨m₁, hw₁, hm₁⟩ := h1
      rw [← hr0] at hw₁
      have hloop : TwoColoringWalk Adj (r (y 0)) (r (y 0)) ((m₀ + 1) + m₁) :=
        twoColoringWalk_trans (TwoColoringWalk.step hw₀ hadj)
          (twoColoringWalk_symm hAdj_symm hw₁)
      exact ⟨(m₀ + 1) + m₁, hloop, by omega⟩
    · have h1 : ¬ ∃ m : ℕ, TwoColoringWalk Adj (r (y 1)) (y 1) m ∧ m % 2 = 0 := by
        intro h1'
        have hbad : (!baseColor (r (y 0))) = baseColor (r (y 1)) := by
          simpa [col, h0, h1'] using hcol_eq
        rw [← hr0] at hbad
        cases hb : baseColor (r (y 0)) <;> simp [hb] at hbad
      obtain ⟨m₀, hw₀⟩ := hr_conn (y 0)
      obtain ⟨m₁, hw₁⟩ := hr_conn (y 1)
      have hm₀ : m₀ % 2 = 1 := by
        by_contra hne
        exact h0 ⟨m₀, hw₀, by omega⟩
      have hm₁ : m₁ % 2 = 1 := by
        by_contra hne
        exact h1 ⟨m₁, hw₁, by omega⟩
      rw [← hr0] at hw₁
      have hloop : TwoColoringWalk Adj (r (y 0)) (r (y 0)) ((m₀ + 1) + m₁) :=
        twoColoringWalk_trans (TwoColoringWalk.step hw₀ hadj)
          (twoColoringWalk_symm hAdj_symm hw₁)
      exact ⟨(m₀ + 1) + m₁, hloop, by omega⟩
  obtain ⟨M, hM, hM_odd⟩ := hOddLoop
  obtain ⟨fM, _, hM1, hM2⟩ :=
    anchored_pebble_walk_invariant hDown hUp (fSingle (r (y 0))) (hfSingle (r (y 0))) hM
  have hM_ne0 : M % 2 ≠ 0 := by omega
  have hpt :
      (⟨r (y 0), Finset.mem_insert_self (r (y 0)) {r (y 0)}⟩ :
        ({r (y 0), r (y 0)} : Finset X)) =
      ⟨r (y 0), Finset.mem_insert_of_mem (Finset.mem_singleton_self (r (y 0)))⟩ :=
    Subtype.ext rfl
  have hcontra : baseColor (r (y 0)) = (!baseColor (r (y 0))) := by
    calc baseColor (r (y 0))
        = fM ⟨r (y 0), Finset.mem_insert_self (r (y 0)) {r (y 0)}⟩ := hM1.symm
      _ = fM ⟨r (y 0), Finset.mem_insert_of_mem (Finset.mem_singleton_self (r (y 0)))⟩ := by
          rw [hpt]
      _ = (!baseColor (r (y 0))) := by
          rw [hM2, ite_eq_right_iff]
          intro hzero
          exact absurd hzero hM_ne0
  cases hb : baseColor (r (y 0)) <;> simp [hb] at hcontra

/-- The triangle ($K_3$) `twoColoringLang`-structure on `Fin 3`, interpreting `.ne` as
`y 0 ≠ y 1`. -/
@[instance_reducible]
def twoColoringTriangleStructure : twoColoringLang.Structure (Fin 3) where
  funMap {_} f := isEmptyElim f
  RelMap {_} r y := match r with | .ne => y 0 ≠ y 1

/-- Interpretation of `TwoColoringRel.ne` in `twoColoringTriangleStructure` is `y 0 ≠ y 1`. -/
@[simp]
theorem twoColoringTriangleStructure_relMap_ne_iff (y : Fin 2 → Fin 3) :
    @RelMap twoColoringLang (Fin 3) twoColoringTriangleStructure 2 TwoColoringRel.ne y ↔
      y 0 ≠ y 1 := by
  rfl

/-- Width $2$ is strictly too small for $2$-coloring: Duplicator wins the existential $2$-pebble
game from the triangle $K_3$ (`Fin 3`) to $K_2$ (`Bool`), even though no global homomorphism
`Fin 3 →[twoColoringLang] Bool` exists. -/
theorem existentialPebbleWin_two_triangle_twoColoring :
    let _ := twoColoringTriangleStructure
    ExistentialPebbleWin twoColoringLang 2 (Fin 3) Bool ∧
      IsEmpty (Fin 3 →[twoColoringLang] Bool) := by
  let _ := twoColoringTriangleStructure
  refine ⟨?_, ⟨fun φ ↦ ?_⟩⟩
  · rw [existentialPebbleWin_iff]
    refine ⟨{p | p.1.card ≤ 2}, ?_, ?_, ?_, ?_⟩
    · exact fun _ hp ↦ hp
    · refine ⟨⟨fun x ↦ absurd x.2 (Finset.notMem_empty x.1), fun {n} r x _ ↦ ?_⟩, by simp⟩
      cases r
      exact absurd (x 0).2 (Finset.notMem_empty _)
    · exact fun {_ _} hsub _ hp ↦ (Finset.card_le_card hsub).trans hp
    · intro S f hS hcard x
      by_cases hx : x ∈ S
      · refine ⟨⟨fun z ↦
            f ⟨z.1, (Finset.mem_insert.mp z.2).elim (fun h ↦ by rw [h]; exact hx) id⟩,
          fun {n} r y hy ↦ f.map_rel' r (fun i ↦ ⟨(y i).1, _⟩) hy⟩,
          (Finset.card_insert_le x S).trans hcard, PartialHom.ext_apply fun z ↦ rfl⟩
      · let T : Finset (Fin 3) := insert x S
        let c : Bool := if hne : S.Nonempty then !(f ⟨hne.choose, hne.choose_spec⟩) else true
        let gFun : T → Bool := fun z ↦
          if hzx : z.1 = x then c
          else f ⟨z.1, (Finset.mem_insert.mp z.2).resolve_left hzx⟩
        have hgRel : ∀ {n : ℕ} (r : twoColoringLang.Relations n) (y : Fin n → T),
            RelMap r (fun i ↦ (y i : Fin 3)) → RelMap r (gFun ∘ y) := by
          intro n r y hy
          cases r
          rw [twoColoringLang_relMap_ne_iff]
          have hyne : (y 0 : Fin 3) ≠ (y 1 : Fin 3) :=
            (twoColoringTriangleStructure_relMap_ne_iff _).mp hy
          have hS_sub : (S : Set (Fin 3)).Subsingleton :=
            Finset.card_le_one.mp (Nat.lt_succ_iff.mp hcard)
          by_cases h0 : (y 0).1 = x <;> by_cases h1 : (y 1).1 = x
          · exact absurd (h0.trans h1.symm) hyne
          · have hy1S : (y 1).1 ∈ S := (Finset.mem_insert.mp (y 1).2).resolve_left h1
            have hne : S.Nonempty := ⟨(y 1).1, hy1S⟩
            have hy1eq : (⟨(y 1).1, hy1S⟩ : S) = ⟨hne.choose, hne.choose_spec⟩ :=
              Subtype.ext (hS_sub hy1S hne.choose_spec)
            change gFun (y 0) ≠ gFun (y 1)
            simp [gFun, h0, h1, c, hne, hy1eq]
          · have hy0S : (y 0).1 ∈ S := (Finset.mem_insert.mp (y 0).2).resolve_left h0
            have hne : S.Nonempty := ⟨(y 0).1, hy0S⟩
            have hy0eq : (⟨(y 0).1, hy0S⟩ : S) = ⟨hne.choose, hne.choose_spec⟩ :=
              Subtype.ext (hS_sub hy0S hne.choose_spec)
            change gFun (y 0) ≠ gFun (y 1)
            simp [gFun, h0, h1, c, hne, hy0eq]
          · have hy0S : (y 0).1 ∈ S := (Finset.mem_insert.mp (y 0).2).resolve_left h0
            have hy1S : (y 1).1 ∈ S := (Finset.mem_insert.mp (y 1).2).resolve_left h1
            exact absurd (hS_sub hy0S hy1S) hyne
        refine ⟨⟨gFun, hgRel⟩, (Finset.card_insert_le x S).trans hcard,
          PartialHom.ext_apply fun z ↦ ?_⟩
        have hzx : z.1 ≠ x := fun h ↦ hx (h ▸ z.2)
        simp [PartialHom.restrict_apply, gFun, hzx]
  · have h01 : φ 0 ≠ φ 1 := by
      have h := φ.map_rel TwoColoringRel.ne ![0, 1]
        ((twoColoringTriangleStructure_relMap_ne_iff ![0, 1]).mpr (by decide))
      exact (twoColoringLang_relMap_ne_iff (φ ∘ ![0, 1])).mp h
    have h12 : φ 1 ≠ φ 2 := by
      have h := φ.map_rel TwoColoringRel.ne ![1, 2]
        ((twoColoringTriangleStructure_relMap_ne_iff ![1, 2]).mpr (by decide))
      exact (twoColoringLang_relMap_ne_iff (φ ∘ ![1, 2])).mp h
    have h02 : φ 0 ≠ φ 2 := by
      have h := φ.map_rel TwoColoringRel.ne ![0, 2]
        ((twoColoringTriangleStructure_relMap_ne_iff ![0, 2]).mpr (by decide))
      exact (twoColoringLang_relMap_ne_iff (φ ∘ ![0, 2])).mp h
    cases c0 : φ 0 <;> cases c1 : φ 1 <;> cases c2 : φ 2 <;> simp_all

end TwoColoring

end CslibFrontier.Computability.Complexity
