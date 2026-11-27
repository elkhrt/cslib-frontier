/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.ModelTheory.Basic
public import CslibFrontier.Logics.Polymorphism

/-!
# Abstract Minions and Polymorphism Minions of First-Order Structures

This module defines abstract minions (`CslibFrontier.Logics.Polymorphism.Minion`), minion
homomorphisms
(`CslibFrontier.Logics.Polymorphism.MinionHom`), homomorphism existence
(`CslibFrontier.Logics.Polymorphism.MinionHomExists`), and minion isomorphisms
(`CslibFrontier.Logics.Polymorphism.MinionIso`), together with direct-product and relational
first-order
structure helpers and the polymorphism minion (`CslibFrontier.Logics.Polymorphism.polMinion`) of a
first-order
structure, bridged to `Cslib.Logic.IsPolymorphism`.

## Main definitions

- `CslibFrontier.Logics.Polymorphism.Minion`: Arity-indexed family of nonempty operation sets for
  positive
  arities `0 < ℓ`, equipped with functorial minor operations along maps `Fin ℓ → Fin ℓ'`.
- `CslibFrontier.Logics.Polymorphism.MinionHom`,
  `CslibFrontier.Logics.Polymorphism.MinionHomExists`,
  `CslibFrontier.Logics.Polymorphism.MinionIso`: Minor-preserving arity-wise maps, the preorder of
  minion homomorphism existence, and invertible minion homomorphisms.
- `CslibFrontier.Logics.Polymorphism.relational`, `CslibFrontier.Logics.Polymorphism.piStructure`,
  `CslibFrontier.Logics.Polymorphism.punitStructure`: Relational language constructor,
  coordinatewise direct
  product structure, and terminal structure on `PUnit`.
- `CslibFrontier.Logics.Polymorphism.polMinion`,
  `CslibFrontier.Logics.Polymorphism.polMinionHomOfHom`,
  `CslibFrontier.Logics.Polymorphism.minionHomToPUnit`: Polymorphism minion of a first-order
  structure,
  conjugation functoriality, and terminality of the polymorphism minion of `PUnit`.

## Main results

- `CslibFrontier.Logics.Polymorphism.MinionHomExists.refl`,
  `CslibFrontier.Logics.Polymorphism.MinionHomExists.trans`: Preorder laws for minion homomorphism
  existence.
- `CslibFrontier.Logics.Polymorphism.MinionIso.inv_map_minor`: The inverse of a minion isomorphism
  commutes with minors.
- `CslibFrontier.Logics.Polymorphism.polMinion_hom_of_hom`,
  `CslibFrontier.Logics.Polymorphism.polMinion_retract_comp_id`:
  Functoriality of polymorphism minions under pairs of homomorphisms and retracts.
- `CslibFrontier.Logics.Polymorphism.minionHomExists_polMinion_punit`: Every minion maps to the
  polymorphism
  minion of `PUnit`.
- `CslibFrontier.Logics.Polymorphism.isPolymorphism_iff_exists_polMinion`: Bridge between
  `Cslib.Logic.IsPolymorphism` and relational polymorphisms in `polMinion`.
-/

public section

open FirstOrder Language Structure

universe u v w w' z

namespace CslibFrontier.Logics.Polymorphism

/-! ### Abstract Minions -/

/-- An abstract *minion* consists of a nonempty type `Carrier ℓ hℓ` of operations at each positive
arity `0 < ℓ`, equipped with a functorial minor operation along maps `Fin ℓ → Fin ℓ'`. -/
structure Minion : Type (u + 1) where
  /-- Operations of arity `ℓ` (for `0 < ℓ`). -/
  Carrier : (ℓ : ℕ) → 0 < ℓ → Type u
  /-- Every positive arity carries at least one operation. -/
  nonempty : ∀ (ℓ : ℕ) (hℓ : 0 < ℓ), Nonempty (Carrier ℓ hℓ)
  /-- Taking a minor along an index map `π : Fin ℓ → Fin ℓ'`. -/
  minor : ∀ {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ'),
    (Fin ℓ → Fin ℓ') → Carrier ℓ hℓ → Carrier ℓ' hℓ'
  /-- Taking the minor along the identity map fixes every operation. -/
  minor_id : ∀ {ℓ : ℕ} (hℓ : 0 < ℓ) (f : Carrier ℓ hℓ), minor hℓ hℓ id f = f
  /-- Taking minors respects composition of index maps. -/
  minor_comp : ∀ {ℓ ℓ' ℓ'' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (hℓ'' : 0 < ℓ'')
    (π₁ : Fin ℓ → Fin ℓ') (π₂ : Fin ℓ' → Fin ℓ'') (f : Carrier ℓ hℓ),
    minor hℓ' hℓ'' π₂ (minor hℓ hℓ' π₁ f) = minor hℓ hℓ'' (π₂ ∘ π₁) f

attribute [simp] Minion.minor_id Minion.minor_comp

/-- Every positive arity of a minion `M` has a nonempty carrier type. -/
instance instNonemptyMinionCarrier (M : Minion.{u}) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    Nonempty (M.Carrier ℓ hℓ) :=
  M.nonempty ℓ hℓ

/-! ### Minion Homomorphisms -/

/-- A *minion homomorphism* `φ : MinionHom M N` is an arity-preserving family of maps commuting
with taking minors along all maps `Fin ℓ → Fin ℓ'`. -/
@[ext]
structure MinionHom (M : Minion.{u}) (N : Minion.{v}) : Type (max u v) where
  /-- Underlying family of maps at each positive arity `0 < ℓ`. -/
  toFun : ∀ {ℓ : ℕ} (hℓ : 0 < ℓ), M.Carrier ℓ hℓ → N.Carrier ℓ hℓ
  /-- Commutativity with the minor operations of `M` and `N`. -/
  map_minor' : ∀ {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (π : Fin ℓ → Fin ℓ')
    (f : M.Carrier ℓ hℓ), toFun hℓ' (M.minor hℓ hℓ' π f) = N.minor hℓ hℓ' π (toFun hℓ f)

namespace MinionHom

/-- A minion homomorphism commutes with taking minors. -/
@[simp]
theorem map_minor {M : Minion.{u}} {N : Minion.{v}} (φ : MinionHom M N)
    {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (π : Fin ℓ → Fin ℓ') (f : M.Carrier ℓ hℓ) :
    φ.toFun hℓ' (M.minor hℓ hℓ' π f) = N.minor hℓ hℓ' π (φ.toFun hℓ f) :=
  φ.map_minor' hℓ hℓ' π f

/-- The identity minion homomorphism on `M`. -/
def id (M : Minion.{u}) : MinionHom M M where
  toFun _ f := f
  map_minor' _ _ _ _ := rfl

/-- Evaluation of the identity minion homomorphism `MinionHom.id M`. -/
@[simp]
theorem id_toFun (M : Minion.{u}) {ℓ : ℕ} (hℓ : 0 < ℓ) (f : M.Carrier ℓ hℓ) :
    (MinionHom.id M).toFun hℓ f = f := by
  rfl

/-- Composition `g.comp f` of minion homomorphisms `f : MinionHom M N` and `g : MinionHom N P`. -/
def comp {M : Minion.{u}} {N : Minion.{v}} {P : Minion.{w}}
    (g : MinionHom N P) (f : MinionHom M N) : MinionHom M P where
  toFun hℓ x := g.toFun hℓ (f.toFun hℓ x)
  map_minor' hℓ hℓ' π x := by rw [f.map_minor, g.map_minor]

/-- Evaluation of the composite minion homomorphism `g.comp f`. -/
@[simp]
theorem comp_toFun {M : Minion.{u}} {N : Minion.{v}} {P : Minion.{w}}
    (g : MinionHom N P) (f : MinionHom M N) {ℓ : ℕ} (hℓ : 0 < ℓ) (x : M.Carrier ℓ hℓ) :
    (g.comp f).toFun hℓ x = g.toFun hℓ (f.toFun hℓ x) := by
  rfl

/-- Composition of minion homomorphisms is associative. -/
theorem comp_assoc {M : Minion.{u}} {N : Minion.{v}} {P : Minion.{w}} {Q : Minion.{w'}}
    (h : MinionHom P Q) (g : MinionHom N P) (f : MinionHom M N) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  rfl

/-- Right identity law for minion homomorphism composition. -/
@[simp]
theorem comp_id {M : Minion.{u}} {N : Minion.{v}} (f : MinionHom M N) :
    f.comp (MinionHom.id M) = f := by
  rfl

/-- Left identity law for minion homomorphism composition. -/
@[simp]
theorem id_comp {M : Minion.{u}} {N : Minion.{v}} (f : MinionHom M N) :
    (MinionHom.id N).comp f = f := by
  rfl

end MinionHom

/-! ### Existence of Minion Homomorphisms -/

/-- Existence of a minion homomorphism from `M` to `N`. -/
def MinionHomExists (M : Minion.{u}) (N : Minion.{v}) : Prop :=
  Nonempty (MinionHom M N)

/-- `MinionHomExists M N` holds if and only if `Nonempty (MinionHom M N)`. -/
theorem minionHomExists_iff {M : Minion.{u}} {N : Minion.{v}} :
    MinionHomExists M N ↔ Nonempty (MinionHom M N) :=
  Iff.rfl

/-- Construct `MinionHomExists M N` from an explicit minion homomorphism. -/
theorem MinionHomExists.of_hom {M : Minion.{u}} {N : Minion.{v}} (f : MinionHom M N) :
    MinionHomExists M N :=
  ⟨f⟩

/-- Reflexivity of `MinionHomExists`. -/
@[refl]
theorem MinionHomExists.refl (M : Minion.{u}) : MinionHomExists M M :=
  ⟨MinionHom.id M⟩

/-- Transitivity of `MinionHomExists`. -/
@[trans]
theorem MinionHomExists.trans {M : Minion.{u}} {N : Minion.{v}} {P : Minion.{w}}
    (h₁ : MinionHomExists M N) (h₂ : MinionHomExists N P) : MinionHomExists M P :=
  let ⟨f⟩ := h₁
  let ⟨g⟩ := h₂
  ⟨g.comp f⟩

/-! ### Minion Isomorphisms -/

/-- A *minion isomorphism* `e : MinionIso M N` is an arity-wise bijection between `M` and `N`
whose forward map (and hence inverse map) commutes with taking minors. -/
@[ext]
structure MinionIso (M : Minion.{u}) (N : Minion.{v}) : Type (max u v) where
  /-- Forward family of maps at each positive arity. -/
  toFun : ∀ {ℓ : ℕ} (hℓ : 0 < ℓ), M.Carrier ℓ hℓ → N.Carrier ℓ hℓ
  /-- Inverse family of maps at each positive arity. -/
  invFun : ∀ {ℓ : ℕ} (hℓ : 0 < ℓ), N.Carrier ℓ hℓ → M.Carrier ℓ hℓ
  /-- Left inverse property at each positive arity. -/
  left_inv : ∀ {ℓ : ℕ} (hℓ : 0 < ℓ) (f : M.Carrier ℓ hℓ), invFun hℓ (toFun hℓ f) = f
  /-- Right inverse property at each positive arity. -/
  right_inv : ∀ {ℓ : ℕ} (hℓ : 0 < ℓ) (g : N.Carrier ℓ hℓ), toFun hℓ (invFun hℓ g) = g
  /-- Commutativity of the forward map with taking minors. -/
  map_minor' : ∀ {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (π : Fin ℓ → Fin ℓ')
    (f : M.Carrier ℓ hℓ), toFun hℓ' (M.minor hℓ hℓ' π f) = N.minor hℓ hℓ' π (toFun hℓ f)

namespace MinionIso

/-- Left-inverse cancellation `e.invFun hℓ (e.toFun hℓ f) = f` for a minion isomorphism. -/
@[simp]
theorem invFun_toFun {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (f : M.Carrier ℓ hℓ) :
    e.invFun hℓ (e.toFun hℓ f) = f :=
  e.left_inv hℓ f

/-- Right-inverse cancellation `e.toFun hℓ (e.invFun hℓ g) = g` for a minion isomorphism. -/
@[simp]
theorem toFun_invFun {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (g : N.Carrier ℓ hℓ) :
    e.toFun hℓ (e.invFun hℓ g) = g :=
  e.right_inv hℓ g

/-- The forward map of a minion isomorphism commutes with taking minors. -/
@[simp]
theorem map_minor {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N)
    {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (π : Fin ℓ → Fin ℓ') (f : M.Carrier ℓ hℓ) :
    e.toFun hℓ' (M.minor hℓ hℓ' π f) = N.minor hℓ hℓ' π (e.toFun hℓ f) :=
  e.map_minor' hℓ hℓ' π f

/-- The inverse map of a minion isomorphism commutes with taking minors. -/
@[simp]
theorem inv_map_minor {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N)
    {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (π : Fin ℓ → Fin ℓ') (g : N.Carrier ℓ hℓ) :
    e.invFun hℓ' (N.minor hℓ hℓ' π g) = M.minor hℓ hℓ' π (e.invFun hℓ g) := by
  rw [← e.invFun_toFun hℓ' (M.minor hℓ hℓ' π (e.invFun hℓ g)), e.map_minor, e.toFun_invFun]

/-- Underlying forward `MinionHom` of a `MinionIso`. -/
def toMinionHom {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N) : MinionHom M N where
  toFun := e.toFun
  map_minor' := e.map_minor'

/-- Evaluation of `e.toMinionHom` agrees with `e.toFun`. -/
@[simp]
theorem toMinionHom_toFun {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (f : M.Carrier ℓ hℓ) :
    e.toMinionHom.toFun hℓ f = e.toFun hℓ f := by
  rfl

/-- Inverse minion isomorphism `e.symm : MinionIso N M`. -/
def symm {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N) : MinionIso N M where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_minor' := e.inv_map_minor

/-- Forward map of `e.symm` agrees with `e.invFun`. -/
@[simp]
theorem symm_toFun {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (g : N.Carrier ℓ hℓ) :
    e.symm.toFun hℓ g = e.invFun hℓ g := by
  rfl

/-- Inverse map of `e.symm` agrees with `e.toFun`. -/
@[simp]
theorem symm_invFun {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (f : M.Carrier ℓ hℓ) :
    e.symm.invFun hℓ f = e.toFun hℓ f := by
  rfl

/-- Symmetry on `MinionIso` is an involution. -/
@[simp]
theorem symm_symm {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N) :
    e.symm.symm = e := by
  rfl

/-- The identity minion isomorphism on `M`. -/
def refl (M : Minion.{u}) : MinionIso M M where
  toFun _ f := f
  invFun _ f := f
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  map_minor' _ _ _ _ := rfl

/-- Evaluation of the forward map of `MinionIso.refl M`. -/
@[simp]
theorem refl_toFun (M : Minion.{u}) {ℓ : ℕ} (hℓ : 0 < ℓ) (f : M.Carrier ℓ hℓ) :
    (MinionIso.refl M).toFun hℓ f = f := by
  rfl

/-- Evaluation of the inverse map of `MinionIso.refl M`. -/
@[simp]
theorem refl_invFun (M : Minion.{u}) {ℓ : ℕ} (hℓ : 0 < ℓ) (f : M.Carrier ℓ hℓ) :
    (MinionIso.refl M).invFun hℓ f = f := by
  rfl

/-- Composition `e₁.trans e₂ : MinionIso M P` of minion isomorphisms `e₁ : MinionIso M N`
and `e₂ : MinionIso N P`. -/
def trans {M : Minion.{u}} {N : Minion.{v}} {P : Minion.{w}}
    (e₁ : MinionIso M N) (e₂ : MinionIso N P) : MinionIso M P where
  toFun hℓ x := e₂.toFun hℓ (e₁.toFun hℓ x)
  invFun hℓ z := e₁.invFun hℓ (e₂.invFun hℓ z)
  left_inv hℓ x := by rw [e₂.invFun_toFun, e₁.invFun_toFun]
  right_inv hℓ z := by rw [e₁.toFun_invFun, e₂.toFun_invFun]
  map_minor' hℓ hℓ' π x := by rw [e₁.map_minor, e₂.map_minor]

/-- Forward evaluation of `e₁.trans e₂`. -/
@[simp]
theorem trans_toFun {M : Minion.{u}} {N : Minion.{v}} {P : Minion.{w}}
    (e₁ : MinionIso M N) (e₂ : MinionIso N P) {ℓ : ℕ} (hℓ : 0 < ℓ) (x : M.Carrier ℓ hℓ) :
    (e₁.trans e₂).toFun hℓ x = e₂.toFun hℓ (e₁.toFun hℓ x) := by
  rfl

/-- Inverse evaluation of `e₁.trans e₂`. -/
@[simp]
theorem trans_invFun {M : Minion.{u}} {N : Minion.{v}} {P : Minion.{w}}
    (e₁ : MinionIso M N) (e₂ : MinionIso N P) {ℓ : ℕ} (hℓ : 0 < ℓ) (z : P.Carrier ℓ hℓ) :
    (e₁.trans e₂).invFun hℓ z = e₁.invFun hℓ (e₂.invFun hℓ z) := by
  rfl

/-- A minion isomorphism `M ≃ N` yields `MinionHomExists M N`. -/
theorem minionHomExists_of_iso {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N) :
    MinionHomExists M N :=
  ⟨e.toMinionHom⟩

/-- A minion isomorphism `M ≃ N` yields `MinionHomExists N M`. -/
theorem minionHomExists_symm_of_iso {M : Minion.{u}} {N : Minion.{v}} (e : MinionIso M N) :
    MinionHomExists N M :=
  ⟨e.symm.toMinionHom⟩

end MinionIso


/-! ### Relational Structures and Polymorphism Minions -/

/-! ### Relational Languages and Direct-Product Structures -/

/-- The purely relational first-order language with relation symbols `R`. -/
@[expose]
def relational (R : ℕ → Type v) : Language.{0, v} where
  Functions _ := PEmpty
  Relations := R

/-- Every language created by `relational` is relational. -/
instance instIsRelationalRelational (R : ℕ → Type v) : (relational R).IsRelational :=
  fun _ ↦ inferInstanceAs (IsEmpty PEmpty)

/-- Coordinatewise direct-product `L`-structure on a dependent product `∀ i, M i`. -/
@[expose, instance_reducible]
def piStructure (L : Language.{u, v}) {ι : Type*} (M : ι → Type w)
    [∀ i, L.Structure (M i)] : L.Structure (∀ i, M i) where
  funMap f x i := funMap f (fun j ↦ x j i)
  RelMap r x := ∀ i, RelMap r (fun j ↦ x j i)

scoped[CslibFrontier.Logics.Polymorphism] attribute [instance] piStructure

/-- Evaluation of `RelMap` on a direct-product structure `∀ i, M i`. -/
@[simp]
theorem pi_relMap {L : Language.{u, v}} {ι : Type*} {M : ι → Type w}
    [∀ i, L.Structure (M i)] {n : ℕ} (r : L.Relations n) (x : Fin n → ∀ i, M i) :
    @RelMap L (∀ i, M i) (piStructure L M) n r x ↔ ∀ i, RelMap r (fun j ↦ x j i) := by
  rfl

/-- Evaluation of `funMap` on a direct-product structure `∀ i, M i`. -/
@[simp]
theorem pi_funMap {L : Language.{u, v}} {ι : Type*} {M : ι → Type w}
    [∀ i, L.Structure (M i)] {n : ℕ} (f : L.Functions n) (x : Fin n → ∀ i, M i) (i : ι) :
    @funMap L (∀ i, M i) (piStructure L M) n f x i = funMap f (fun j ↦ x j i) := by
  rfl

/-- Coordinate projection homomorphism `(∀ i, M i) →[L] M i`. -/
def homProj (L : Language.{u, v}) {ι : Type*} (M : ι → Type w)
    [∀ i, L.Structure (M i)] (i : ι) :
    @Hom L (∀ j, M j) (M i) (piStructure L M) _ where
  toFun x := x i
  map_fun' _ _ := rfl
  map_rel' _ _ hx := hx i

/-- Evaluation of `homProj`. -/
@[simp]
theorem homProj_apply (L : Language.{u, v}) {ι : Type*} (M : ι → Type w)
    [∀ i, L.Structure (M i)] (i : ι) (x : ∀ j, M j) :
    homProj L M i x = x i := by
  rfl

/-- Universal pairing homomorphism `A →[L] ∀ i, M i` from a family of homomorphisms. -/
def homPi {L : Language.{u, v}} {ι : Type*} {A : Type w'} {M : ι → Type w}
    [L.Structure A] [∀ i, L.Structure (M i)] (f : ∀ i, A →[L] M i) :
    @Hom L A (∀ i, M i) _ (piStructure L M) where
  toFun a i := f i a
  map_fun' g x := funext fun i ↦ (f i).map_fun' g x
  map_rel' r x hx i := (f i).map_rel' r x hx

/-- Evaluation of `homPi`. -/
@[simp]
theorem homPi_apply {L : Language.{u, v}} {ι : Type*} {A : Type w'} {M : ι → Type w}
    [L.Structure A] [∀ i, L.Structure (M i)] (f : ∀ i, A →[L] M i) (a : A) (i : ι) :
    homPi f a i = f i a := by
  rfl

/-- Terminal `L`-structure on `PUnit`, where every relation holds universally. -/
@[expose, instance_reducible]
def punitStructure (L : Language.{u, v}) : L.Structure PUnit.{z + 1} where
  funMap _ _ := PUnit.unit
  RelMap _ _ := True

scoped[CslibFrontier.Logics.Polymorphism] attribute [instance] punitStructure

/-- Unique terminal homomorphism `X →[L] PUnit`. -/
def homTerminal (L : Language.{u, v}) (X : Type w) [L.Structure X] :
    @Hom L X PUnit.{z + 1} _ (punitStructure L) where
  toFun _ := PUnit.unit
  map_fun' _ _ := rfl
  map_rel' _ _ _ := trivial

/-- Evaluation of `homTerminal`. -/
@[simp]
theorem homTerminal_apply (L : Language.{u, v}) (X : Type w) [L.Structure X] (x : X) :
    homTerminal.{u, v, w, z} L X x = PUnit.unit := by
  rfl

/-- Construct a first-order homomorphism `A →[L] B` over a relational language `[L.IsRelational]`
from a bare function `f : A → B` and preservation of every relation symbol. -/
def homOfRel {L : Language.{u, v}} [L.IsRelational] {A : Type w} {B : Type w'}
    [L.Structure A] [L.Structure B] (f : A → B)
    (hf : ∀ {n : ℕ} (r : L.Relations n) (x : Fin n → A), RelMap r x → RelMap r (f ∘ x)) :
    A →[L] B where
  toFun := f
  map_fun' {_} fn := isEmptyElim fn
  map_rel' {_} r x hx := hf r x hx

/-- Evaluation of `homOfRel f hf` at `a : A`. -/
@[simp, grind =]
theorem homOfRel_apply {L : Language.{u, v}} [L.IsRelational] {A : Type w} {B : Type w'}
    [L.Structure A] [L.Structure B] (f : A → B)
    (hf : ∀ {n : ℕ} (r : L.Relations n) (x : Fin n → A), RelMap r x → RelMap r (f ∘ x)) (a : A) :
    homOfRel f hf a = f a := by
  rfl

/-! ### Polymorphism Minions of First-Order Structures -/

/-- The *polymorphism minion* `polMinion L Y` of a first-order `L`-structure `Y`, whose
`r`-ary elements (`0 < r`) are `L`-homomorphisms `(Fin r → Y) →[L] Y` (with respect to the
coordinatewise product structure `piStructure L (fun _ ↦ Y)`) and whose minor along
`π : Fin ℓ → Fin ℓ'` is precomposition with `homPi (fun i ↦ homProj L _ (π i))`. -/
@[expose]
def polMinion (L : Language.{u, v}) (Y : Type w) [L.Structure Y] :
    Minion.{w} where
  Carrier r _ := @Hom L (Fin r → Y) Y (piStructure L (fun _ ↦ Y)) _
  nonempty _ hr := ⟨homProj L (fun _ ↦ Y) ⟨0, hr⟩⟩
  minor _ _ π f := f.comp (homPi fun i ↦ homProj L (fun _ ↦ Y) (π i))
  minor_id _ _ := Hom.ext fun _ ↦ by
    congr 1
  minor_comp _ _ _ _ _ _ := Hom.ext fun _ ↦ by
    congr 1

/-- `FunLike` instance on `(polMinion L Y).Carrier r hr`, definitionally agreeing with
`FirstOrder.Language.Hom.instFunLike`. -/
instance instFunLikePolMinionCarrier {L : Language.{u, v}} {Y : Type w} [L.Structure Y]
    {r : ℕ} {hr : 0 < r} :
    FunLike ((polMinion L Y).Carrier r hr) (Fin r → Y) Y :=
  Hom.instFunLike

/-- Pointwise evaluation of taking a minor in `polMinion L Y`. -/
@[simp]
theorem polMinion_minor_apply {L : Language.{u, v}} {Y : Type w} [L.Structure Y]
    {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (π : Fin ℓ → Fin ℓ')
    (f : (polMinion L Y).Carrier ℓ hℓ) (x : Fin ℓ' → Y) :
    (polMinion L Y).minor hℓ hℓ' π f x = f (fun i ↦ x (π i)) := by
  change f ((homPi fun i ↦ homProj L (fun _ ↦ Y) (π i)) x) = _
  congr 1

/-- Taking a minor of a coordinate projection in `polMinion L Y` shifts the coordinate by `π`. -/
@[simp]
theorem polMinion_minor_proj {L : Language.{u, v}} {Y : Type w} [L.Structure Y]
    {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (π : Fin ℓ → Fin ℓ') (i : Fin ℓ) :
    (polMinion L Y).minor hℓ hℓ' π (homProj L (fun _ ↦ Y) i) =
      homProj L (fun _ ↦ Y) (π i) :=
  Hom.ext fun _ ↦ by rfl

/-- Over a relational language, a bare function `f : (Fin r → Y) → Y` is the underlying function of
a polymorphism in `polMinion L Y` if and only if `Cslib.Logic.IsPolymorphism f` holds for every
relation of `Y`. -/
theorem isPolymorphism_iff_exists_polMinion {L : Language.{u, v}} [L.IsRelational]
    {Y : Type w} [L.Structure Y] {r : ℕ} (hr : 0 < r) (f : (Fin r → Y) → Y) :
    (∀ {n : ℕ} (R : L.Relations n), Cslib.Logic.IsPolymorphism f {x | RelMap R x}) ↔
      ∃ φ : (polMinion L Y).Carrier r hr, ⇑φ = f := by
  constructor
  · intro hf
    let _ := piStructure L (fun _ : Fin r ↦ Y)
    refine ⟨homOfRel f (fun {n} R x hx ↦ ?_), rfl⟩
    have hcols : ∀ j : Fin r, (fun i : Fin n ↦ x i j) ∈ {y | RelMap R y} := fun j ↦
      (pi_relMap R x).mp hx j
    exact hf R (fun j i ↦ x i j) hcols
  · rintro ⟨φ, rfl⟩ n R a ha
    let _ := piStructure L (fun _ : Fin r ↦ Y)
    exact φ.map_rel' R (fun i j ↦ a j i) ((pi_relMap R _).mpr ha)

/-- Given `L`-homomorphisms `f : Y' →[L] Y` and `g : Y →[L] Y'`, conjugation `φ ↦ g ∘ φ ∘ f^ℓ`
defines a minion homomorphism `polMinion L Y → polMinion L Y'`. -/
def polMinionHomOfHom {L : Language.{u, v}} {Y : Type w} {Y' : Type w'}
    [L.Structure Y] [L.Structure Y'] (f : Y' →[L] Y) (g : Y →[L] Y') :
    MinionHom (polMinion L Y) (polMinion L Y') where
  toFun {ℓ} _ φ :=
    let _ := piStructure L (fun _ : Fin ℓ ↦ Y)
    let _ := piStructure L (fun _ : Fin ℓ ↦ Y')
    g.comp (φ.comp (homPi fun k ↦ f.comp (homProj L (fun _ : Fin ℓ ↦ Y') k)))
  map_minor' _ _ _ _ := Hom.ext fun _ ↦ by rfl

/-- Pointwise evaluation of `polMinionHomOfHom f g`. -/
@[simp]
theorem polMinionHomOfHom_toFun {L : Language.{u, v}} {Y : Type w} {Y' : Type w'}
    [L.Structure Y] [L.Structure Y'] (f : Y' →[L] Y) (g : Y →[L] Y')
    {ℓ : ℕ} (hℓ : 0 < ℓ) (φ : (polMinion L Y).Carrier ℓ hℓ) (x : Fin ℓ → Y') :
    (polMinionHomOfHom f g).toFun hℓ φ x = g (φ fun k ↦ f (x k)) := by
  change g (φ ((homPi fun k ↦ f.comp (homProj L (fun _ : Fin ℓ ↦ Y') k)) x)) = _
  congr 2

/-- Homomorphic equivalence (`Y' →[L] Y` and `Y →[L] Y'`) yields a minion homomorphism from
`polMinion L Y` to `polMinion L Y'`. -/
theorem polMinion_hom_of_hom {L : Language.{u, v}} {Y : Type w} {Y' : Type w'}
    [L.Structure Y] [L.Structure Y'] (f : Y' →[L] Y) (g : Y →[L] Y') :
    MinionHomExists (polMinion L Y) (polMinion L Y') :=
  ⟨polMinionHomOfHom f g⟩

/-- If `(i, r)` is a retraction (`∀ y', r (i y') = y'`), then conjugating `polMinionHomOfHom i r`
with `polMinionHomOfHom r i` yields the identity minion homomorphism on `polMinion L Y'`. -/
theorem polMinion_retract_comp_id {L : Language.{u, v}} {Y : Type w} {Y' : Type w'}
    [L.Structure Y] [L.Structure Y'] (i : Y' →[L] Y) (r : Y →[L] Y')
    (hr : ∀ y', r (i y') = y') :
    (polMinionHomOfHom i r).comp (polMinionHomOfHom r i) =
      MinionHom.id (polMinion L Y') := by
  refine MinionHom.ext (funext fun ℓ ↦ funext fun hℓ ↦ funext fun φ ↦ ?_)
  simp only [MinionHom.comp_toFun, MinionHom.id_toFun]
  apply Hom.ext
  intro x
  change ((polMinionHomOfHom i r).toFun hℓ ((polMinionHomOfHom r i).toFun hℓ φ)) x = φ x
  simp only [polMinionHomOfHom_toFun]
  have hx : (fun k ↦ r (i (x k))) = x := funext fun k ↦ hr (x k)
  rw [hx, hr]

/-- Canonical minion homomorphism from any minion `M` into the polymorphism minion of the
terminal one-point structure `PUnit`. -/
def minionHomToPUnit (M : Minion.{u}) (L : Language.{v, w}) :
    let _ := punitStructure.{v, w, z} L
    MinionHom M (polMinion L PUnit.{z + 1}) :=
  let _ := punitStructure.{v, w, z} L
  { toFun := fun {ℓ} _ _ ↦
      let _ := piStructure L (fun _ : Fin ℓ ↦ PUnit.{z + 1})
      homTerminal.{v, w, z, z} L (Fin ℓ → PUnit.{z + 1})
    map_minor' := fun _ _ _ _ ↦ Hom.ext fun _ ↦ rfl }

/-- Evaluation of `minionHomToPUnit M L`. -/
@[simp]
theorem minionHomToPUnit_toFun (M : Minion.{u}) (L : Language.{v, w})
    {ℓ : ℕ} (hℓ : 0 < ℓ) (f : M.Carrier ℓ hℓ) :
    let _ := punitStructure.{v, w, z} L
    (minionHomToPUnit.{u, v, w, z} M L).toFun hℓ f =
      (let _ := piStructure L (fun _ : Fin ℓ ↦ PUnit.{z + 1})
       homTerminal.{v, w, z, z} L (Fin ℓ → PUnit.{z + 1})) := by
  rfl

/-- Every minion admits a minion homomorphism into the polymorphism minion of `PUnit`. -/
theorem minionHomExists_polMinion_punit (M : Minion.{u}) (L : Language.{v, w}) :
    let _ := punitStructure.{v, w, z} L
    MinionHomExists M (polMinion L PUnit.{z + 1}) :=
  ⟨minionHomToPUnit M L⟩

end CslibFrontier.Logics.Polymorphism
