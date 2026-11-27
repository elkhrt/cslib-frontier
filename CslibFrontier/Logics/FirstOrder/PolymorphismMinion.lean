/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Logics.FirstOrder.Encoding
public import Mathlib.Data.Fintype.Basic
public import Mathlib.ModelTheory.Basic
public import Mathlib.ModelTheory.Substructures

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Logics.FirstOrder.Encoding.PolyTime
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic.FinCases

/-!
# Polymorphism Minions, Cores, Naked Sets, and Fixed-Template CSP Base Cases

This module develops universal-algebraic tools for fixed-template Constraint Satisfaction Problems
(CSPs) over Mathlib's `FirstOrder.Language` and `Cslib.Logic.Vocabulary`:

1. **Abstract minions and minion homomorphisms (`CslibFrontier.Minion`,
   `CslibFrontier.Minion.Hom`, `CslibFrontier.idMinion`)**: covariant functors from finite index
   sets `Fin n` to types, natural transformations preserving minor operations, and the projection
   minion `idMinion`.
2. **Cartesian powers and polymorphism minions (`CslibFrontier.FirstOrder.Power`,
   `CslibFrontier.FirstOrder.polymorphismMinion`,
   `CslibFrontier.FirstOrder.idempotentPolymorphismMinion`)**: extensional structure wrappers for
   `M^ι`, unary minors, idempotent polymorphisms, cores (`IsCore`) of finite relational structures,
   existence of homomorphically equivalent induced core retracts (`exists_inducedCore_retract`),
   and the canonical minion homomorphism `Pol(A) → Pol(A)_idem` on cores.
3. **Naked sets and the Boolean naked-set theorem (`CslibFrontier.FirstOrder.NakedSet`,
   `CslibFrontier.FirstOrder.exists_nakedSet_of_card_le_two`)**: pairs `(S, θ)` preserved by
   `Pol(A)_idem` with two equivalence classes on which every idempotent polymorphism acts as a
   coordinate projection, inducing `Pol(A)_idem → idMinion`, and the unconditional proof that every
   structure of cardinality at most `2` admitting `Pol(A)_idem → idMinion` possesses a naked set.
4. **Fixed-template CSP languages and polynomial-time base cases
   (`CslibFrontier.Complexity.cspLanguage`,
   `CslibFrontier.Complexity.cspLanguage_eq_of_homEquiv`,
   `CslibFrontier.Complexity.cspLanguage_mem_P_of_zeroAry_polymorphism`,
   `CslibFrontier.Complexity.cspLanguage_mem_P_of_subsingleton`)**.
-/

public section

namespace CslibFrontier

universe u v w

/-! ### Abstract minions and minion homomorphisms -/

/-- A **minion** assigns an operation type `op n` to each arity `n : ℕ` and a minor map
`minor σ : op m → op n` to each coordinate map `σ : Fin m → Fin n`, preserving identities and
composition. -/
structure Minion : Type (u + 1) where
  /-- Operations of arity `n`. -/
  op : ℕ → Type u
  /-- Minor operation induced by `σ : Fin m → Fin n`. -/
  minor : ∀ {m n : ℕ}, (Fin m → Fin n) → op m → op n
  /-- Identity coordinate maps act as the identity. -/
  minor_id : ∀ {n : ℕ} (x : op n), minor id x = x
  /-- Minor maps respect composition of coordinate maps. -/
  minor_comp : ∀ {k m n : ℕ} (τ : Fin m → Fin n) (σ : Fin k → Fin m) (x : op k),
    minor (τ ∘ σ) x = minor τ (minor σ x)

attribute [simp] Minion.minor_id

namespace Minion

/-- A **minion homomorphism** `M → N` is a family of arity-preserving maps commuting with all minor
operations. -/
@[ext]
structure Hom (M : Minion.{u}) (N : Minion.{v}) : Type (max u v) where
  /-- Underlying map at arity `n`. -/
  app : ∀ {n : ℕ}, M.op n → N.op n
  /-- Naturality with respect to minor operations. -/
  naturality : ∀ {m n : ℕ} (σ : Fin m → Fin n) (x : M.op m),
    app (M.minor σ x) = N.minor σ (app x)

/-- The identity minion homomorphism on `M`. -/
@[expose, simps]
def Hom.id (M : Minion.{u}) : Hom M M where
  app x := x
  naturality _ _ := rfl

/-- Composition of minion homomorphisms `M → N` and `N → P`. -/
@[expose, simps]
def Hom.comp {M : Minion.{u}} {N : Minion.{v}} {P : Minion.{w}}
    (β : Hom N P) (α : Hom M N) : Hom M P where
  app x := β.app (α.app x)
  naturality σ x := by rw [α.naturality, β.naturality]

end Minion

/-- The **identity (projection) minion** `idMinion`, with `op n = Fin n` and `minor σ i = σ i`. -/
abbrev idMinion : Minion.{0} where
  op n := Fin n
  minor σ i := σ i
  minor_id _ := rfl
  minor_comp _ _ _ := rfl

namespace Minion.Hom

/-- Any minion homomorphism to `idMinion` forces the `0`-ary operation set to be empty. -/
theorem isEmpty_op_zero {M : Minion.{u}} (α : Minion.Hom M idMinion) : IsEmpty (M.op 0) :=
  ⟨fun x ↦ Fin.elim0 (α.app x)⟩

/-- Any minion homomorphism to `idMinion` maps every unary operation to `0 : Fin 1`. -/
@[simp]
theorem app_one_eq_zero {M : Minion.{u}} (α : Minion.Hom M idMinion) (x : M.op 1) :
    α.app x = 0 :=
  Subsingleton.elim _ _

/-- A binary operation invariant under coordinate swap precludes a minion homomorphism to
`idMinion`. -/
theorem false_of_swap_fixed {M : Minion.{u}} (α : Minion.Hom M idMinion) (x : M.op 2)
    (hswap : M.minor (![1, 0] : Fin 2 → Fin 2) x = x) : False := by
  have h := α.naturality (![1, 0] : Fin 2 → Fin 2) x
  rw [hswap] at h
  change α.app x = (![1, 0] : Fin 2 → Fin 2) (α.app x) at h
  rcases Fin.exists_fin_two.mp ⟨α.app x, rfl⟩ with hidx | hidx <;>
    rw [hidx] at h <;> exact absurd h (by decide)

end Minion.Hom

/-! ### Cartesian powers, polymorphism minions, cores, and naked sets -/

namespace FirstOrder

open _root_.FirstOrder _root_.FirstOrder.Language

/-- The `ι`-indexed Cartesian power `M^ι` of an `L`-structure domain `M`. -/
@[ext]
structure Power (ι : Type*) (M : Type*) where
  /-- Construct a tuple in `Power ι M` from a coordinate map `ι → M`. -/
  ofFun ::
  /-- Underlying coordinate map `ι → M`. -/
  toFun : ι → M

instance instFunLikePower (ι : Type*) (M : Type*) : DFunLike (Power ι M) ι (fun _ ↦ M) where
  coe := Power.toFun
  coe_injective _ _ h := Power.ext h

@[simp]
theorem Power.coe_ofFun {ι M : Type*} (f : ι → M) : ⇑(Power.ofFun f) = f := rfl

@[expose, simps]
def Power.equivFun (ι M : Type*) : Power ι M ≃ (ι → M) where
  toFun x := ⇑x
  invFun := Power.ofFun
  left_inv _ := rfl
  right_inv _ := rfl

instance instFinitePower {ι M : Type*} [Finite ι] [Finite M] : Finite (Power ι M) :=
  Finite.of_equiv (ι → M) (Power.equivFun ι M).symm

instance instFintypePower {ι M : Type*} [DecidableEq ι] [Fintype ι] [Fintype M] :
    Fintype (Power ι M) :=
  Fintype.ofEquiv (ι → M) (Power.equivFun ι M).symm

instance instStructurePower {L : Language} {ι M : Type*} [L.Structure M] :
    L.Structure (Power ι M) where
  funMap f x := ⟨fun i ↦ Structure.funMap f (fun j ↦ x j i)⟩
  RelMap r x := ∀ i : ι, Structure.RelMap r (fun j ↦ x j i)

/-- Coordinate projection `Power ι M →[L] M`. -/
@[expose, simps]
def Power.proj {L : Language} {ι M : Type*} [L.Structure M] (i : ι) : Power ι M →[L] M where
  toFun x := x i
  map_fun' _ _ := rfl
  map_rel' _ _ h := h i

/-- Coordinate relabeling `Power κ M →[L] Power ι M` induced by `σ : ι → κ`. -/
@[expose, simps]
def Power.relabel {L : Language} {ι κ M : Type*} [L.Structure M] (σ : ι → κ) :
    Power κ M →[L] Power ι M where
  toFun x := ⟨fun i ↦ x (σ i)⟩
  map_fun' _ _ := rfl
  map_rel' _ _ h i := h (σ i)

/-- Diagonal homomorphism `M →[L] Power ι M`. -/
@[expose, simps]
def Power.diagonal {L : Language} (ι : Type*) {M : Type*} [L.Structure M] :
    M →[L] Power ι M where
  toFun a := ⟨fun _ ↦ a⟩
  map_fun' _ _ := rfl
  map_rel' _ _ h _ := h

/-- Functorial postcomposition `Power ι M →[L] Power ι N`. -/
@[expose, simps]
def Power.mapHom {L : Language} {ι M N : Type*} [L.Structure M] [L.Structure N]
    (φ : M →[L] N) : Power ι M →[L] Power ι N where
  toFun x := ⟨fun i ↦ φ (x i)⟩
  map_fun' f x := by ext i; exact φ.map_fun f (fun j ↦ x j i)
  map_rel' r x h i := φ.map_rel r (fun j ↦ x j i) (h i)

/-- Universal property of `Power ι M`: assemble `ι → (X →[L] M)` into `X →[L] Power ι M`. -/
@[expose, simps]
def Power.piHom {L : Language} {ι X M : Type*} [L.Structure X] [L.Structure M]
    (fs : ι → (X →[L] M)) : X →[L] Power ι M where
  toFun x := ⟨fun i ↦ fs i x⟩
  map_fun' f x := by ext i; exact (fs i).map_fun f x
  map_rel' r x h i := (fs i).map_rel r x h

/-- The **polymorphism minion** `Pol(A)` of an `L`-structure `A`. -/
abbrev polymorphismMinion (L : Language.{u, v}) (A : Type w) [L.Structure A] : Minion.{w} where
  op n := Power (Fin n) A →[L] A
  minor σ f := f.comp (Power.relabel σ)
  minor_id _ := Language.Hom.ext fun _ ↦ rfl
  minor_comp _ _ _ := Language.Hom.ext fun _ ↦ rfl

/-- Minion homomorphism `Pol(A) → Pol(B)` induced by `ι : B →[L] A` and `ψ : A →[L] B`. -/
@[expose]
def minionHomOfHomPair {L : Language.{u, v}} {A : Type w} {B : Type*}
    [L.Structure A] [L.Structure B] (ι : B →[L] A) (ψ : A →[L] B) :
    Minion.Hom (polymorphismMinion L A) (polymorphismMinion L B) where
  app f := ψ.comp (f.comp (Power.mapHom ι))
  naturality _ _ := Language.Hom.ext fun _ ↦ rfl

/-- Unary minor `e_f(a) = f(a, …, a)` of an `n`-ary polymorphism `f`. -/
@[expose]
def unaryMinor {L : Language.{u, v}} {A : Type w} [L.Structure A] {n : ℕ}
    (f : Power (Fin n) A →[L] A) : A →[L] A :=
  f.comp (Power.diagonal (Fin n))

/-- An `n`-ary polymorphism `f` is **idempotent** if `f(a, …, a) = a` for all `a : A`. -/
@[expose]
def IsIdempotentPolymorphism {L : Language.{u, v}} {A : Type w} [L.Structure A] {n : ℕ}
    (f : Power (Fin n) A →[L] A) : Prop :=
  ∀ a : A, f ⟨fun _ ↦ a⟩ = a

theorem IsIdempotentPolymorphism.minor {L : Language.{u, v}} {A : Type w} [L.Structure A]
    {m n : ℕ} {f : Power (Fin m) A →[L] A} (hf : IsIdempotentPolymorphism f)
    (σ : Fin m → Fin n) :
    IsIdempotentPolymorphism ((polymorphismMinion L A).minor σ f) :=
  fun a ↦ hf a

theorem isIdempotentPolymorphism_proj {L : Language.{u, v}} {A : Type w} [L.Structure A]
    {n : ℕ} (i : Fin n) :
    IsIdempotentPolymorphism (Power.proj (L := L) (M := A) i) :=
  fun _ ↦ rfl

/-- The **idempotent polymorphism minion** `Pol(A)_idem` of `A`. -/
abbrev idempotentPolymorphismMinion (L : Language.{u, v}) (A : Type w) [L.Structure A] :
    Minion.{w} where
  op n := { f : Power (Fin n) A →[L] A // IsIdempotentPolymorphism f }
  minor σ f := ⟨(polymorphismMinion L A).minor σ f.1, f.2.minor σ⟩
  minor_id _ := Subtype.ext (Language.Hom.ext fun _ ↦ rfl)
  minor_comp _ _ _ := Subtype.ext (Language.Hom.ext fun _ ↦ rfl)

/-- Inclusion minion homomorphism `Pol(A)_idem → Pol(A)`. -/
@[expose, simps]
def idempotentMinionInclusion (L : Language.{u, v}) (A : Type w) [L.Structure A] :
    Minion.Hom (idempotentPolymorphismMinion L A) (polymorphismMinion L A) where
  app f := f.1
  naturality _ _ := rfl

/-- No structure of cardinality at most `1` admits a minion homomorphism
`Pol(A)_idem → idMinion`. -/
theorem not_nonempty_idempotentMinionHom_id_of_subsingleton {L : Language.{u, v}} {A : Type w}
    [L.Structure A] [Subsingleton A] :
    ¬ Nonempty (Minion.Hom (idempotentPolymorphismMinion L A) idMinion) := by
  rintro ⟨α⟩
  let p₀ : (idempotentPolymorphismMinion L A).op 2 :=
    ⟨Power.proj 0, isIdempotentPolymorphism_proj 0⟩
  have hswap : (idempotentPolymorphismMinion L A).minor (![1, 0] : Fin 2 → Fin 2) p₀ = p₀ := by
    apply Subtype.ext; apply Language.Hom.ext; intro x; exact Subsingleton.elim _ _
  exact Minion.Hom.false_of_swap_fixed α p₀ hswap

/-- An `L`-structure `A` is a **core** if every endomorphism `A →[L] A` extends to an automorphism
`A ≃[L] A`. -/
@[expose]
def IsCore (L : Language.{u, v}) (A : Type w) [L.Structure A] : Prop :=
  ∀ e : A →[L] A, ∃ φ : A ≃[L] A, ⇑φ = ⇑e

/-- Iterate an endomorphism `e : A →[L] A` `k` times. -/
@[expose]
def iterateHom {L : Language.{u, v}} {A : Type w} [L.Structure A] (e : A →[L] A) :
    ℕ → (A →[L] A)
  | 0 => Language.Hom.id L A
  | k + 1 => e.comp (iterateHom e k)

@[simp]
theorem coe_iterateHom {L : Language.{u, v}} {A : Type w} [L.Structure A]
    (e : A →[L] A) (k : ℕ) :
    ⇑(iterateHom e k) = (⇑e)^[k] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    ext x
    rw [iterateHom, Language.Hom.comp_apply, ih, Function.iterate_succ_apply']

/-- On a finite relational structure, every bijective endomorphism is an `L`-automorphism. -/
theorem equivOfBijectiveHom {L : Language.{u, v}} [L.IsRelational] {A : Type w}
    [Finite A] [L.Structure A] {e : A →[L] A} (hbij : Function.Bijective e) :
    ∃ φ : A ≃[L] A, ⇑φ = ⇑e := by
  classical
  cases nonempty_fintype A
  let σ : Equiv.Perm A := Equiv.ofBijective e hbij
  have hpow : σ ^ Fintype.card (Equiv.Perm A) = 1 := pow_card_eq_one
  set M := Fintype.card (Equiv.Perm A)
  have hM : 1 ≤ M := Fintype.card_pos
  let invHom : A →[L] A := iterateHom e (M - 1)
  have hleft : ∀ x : A, invHom (e x) = x := by
    intro x
    have h1 : (⇑σ)^[M] x = x := by
      have := Equiv.Perm.coe_pow σ M
      rw [hpow] at this
      exact congrFun this.symm x
    change iterateHom e (M - 1) (e x) = x
    have hM' : (M - 1).succ = M := by omega
    rw [coe_iterateHom, ← Function.iterate_succ_apply, hM']
    exact h1
  refine ⟨{
    toEquiv := σ
    map_fun' := fun f ↦ isEmptyElim f
    map_rel' := fun r x ↦ ⟨fun h ↦ by
      have h' := invHom.map_rel r (σ ∘ x) h
      have heq : invHom ∘ (σ ∘ x) = x := by ext i; exact hleft (x i)
      rwa [heq] at h',
      fun h ↦ e.map_rel r x h⟩
  }, rfl⟩

theorem isCore_iff_forall_hom_injective {L : Language.{u, v}} [L.IsRelational] {A : Type w}
    [Finite A] [L.Structure A] :
    IsCore L A ↔ ∀ e : A →[L] A, Function.Injective e :=
  ⟨fun h e ↦ by obtain ⟨φ, hφ⟩ := h e; rw [← hφ]; exact φ.toEquiv.injective,
   fun h e ↦ equivOfBijectiveHom (Finite.injective_iff_bijective.mp (h e))⟩

/-- Automorphism associated with an endomorphism of a core structure. -/
noncomputable def IsCore.endEquiv {L : Language.{u, v}} {A : Type w} [L.Structure A]
    (hCore : IsCore L A) (e : A →[L] A) : A ≃[L] A :=
  (hCore e).choose

@[simp]
theorem IsCore.endEquiv_symm_apply_apply {L : Language.{u, v}} {A : Type w} [L.Structure A]
    (hCore : IsCore L A) (e : A →[L] A) (a : A) :
    (hCore.endEquiv e).symm (e a) = a := by
  have heq : hCore.endEquiv e a = e a := congrFun (hCore e).choose_spec a
  rw [← heq]
  exact (hCore.endEquiv e).symm_apply_apply a

/-- Canonical minion homomorphism `Pol(A) → Pol(A)_idem` on a core `A`. -/
@[expose]
noncomputable def IsCore.toIdempotentMinionHom {L : Language.{u, v}} {A : Type w} [L.Structure A]
    (hCore : IsCore L A) :
    Minion.Hom (polymorphismMinion L A) (idempotentPolymorphismMinion L A) where
  app f := ⟨(hCore.endEquiv (unaryMinor f)).symm.toHom.comp f,
    fun a ↦ hCore.endEquiv_symm_apply_apply (unaryMinor f) a⟩
  naturality σ f := by
    apply Subtype.ext
    refine Language.Hom.ext fun x ↦ ?_
    have heq : unaryMinor ((polymorphismMinion L A).minor σ f) = unaryMinor f :=
      Language.Hom.ext fun _ ↦ rfl
    change (hCore.endEquiv (unaryMinor ((polymorphismMinion L A).minor σ f))).symm
        (f (Power.relabel σ x)) =
      (hCore.endEquiv (unaryMinor f)).symm (f (Power.relabel σ x))
    rw [heq]

/-- Induced `L.Substructure` on any subset `C` of a relational `L`-structure. -/
@[expose]
def relationalSubstructure {L : Language.{u, v}} [L.IsRelational] {A : Type w} [L.Structure A]
    (C : Set A) : L.Substructure A where
  carrier := C
  fun_mem f := isEmptyElim f

/-- Every finite relational structure `A` possesses an induced core substructure `S` together with
a retraction `ψ : A →[L] S`. -/
theorem exists_inducedCore_retract {L : Language.{u, v}} [L.IsRelational] (A : Type w)
    [Finite A] [L.Structure A] :
    ∃ (C : Set A),
      IsCore L (relationalSubstructure (L := L) C) ∧
      ∃ ψ : A →[L] relationalSubstructure (L := L) C,
        ∀ x : relationalSubstructure (L := L) C, ψ x.1 = x := by
  classical
  cases nonempty_fintype A
  let imgCard : (A →[L] A) → ℕ := fun e ↦ (Finset.univ.image ⇑e).card
  have hFinHom : Finite (A →[L] A) :=
    Finite.of_injective (fun e : A →[L] A ↦ (⇑e : A → A)) fun _ _ h ↦ DFunLike.coe_injective h
  cases nonempty_fintype (A →[L] A)
  obtain ⟨e, _, he_min⟩ := Finset.exists_min_image Finset.univ imgCard ⟨Language.Hom.id L A,
    Finset.mem_univ _⟩
  let C : Set A := Set.range ⇑e
  let S := relationalSubstructure (L := L) C
  let eCorest : A →[L] S :=
    { toFun := fun a ↦ ⟨e a, a, rfl⟩
      map_fun' := fun f ↦ isEmptyElim f
      map_rel' := fun r x h ↦ e.map_rel r x h }
  have hCore : IsCore L S := by
    rw [isCore_iff_forall_hom_injective]
    intro u
    let compEnd : A →[L] A := S.subtype.toHom.comp (u.comp eCorest)
    have hsub : Finset.univ.image ⇑compEnd =
        (Finset.univ.image ⇑u).map ⟨Subtype.val, Subtype.val_injective⟩ := by
      ext a
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      refine ⟨?_, ?_⟩
      · rintro ⟨x, rfl⟩
        exact ⟨u (eCorest x), ⟨eCorest x, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
        obtain ⟨x, hx⟩ := z.2
        have hzx : eCorest x = z := Subtype.ext hx
        exact ⟨x, by simp [compEnd, hzx]⟩
    have hcardS : Fintype.card S = imgCard e := by
      have hSC : (Finset.univ : Finset S).map ⟨Subtype.val, Subtype.val_injective⟩ =
          (Finset.univ.image ⇑e : Finset A) := by
        ext a; simp [S, C]; rfl
      rw [← Finset.card_univ (α := S),
        ← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩, hSC]
    have hle : imgCard e ≤ ((Finset.univ : Finset S).image ⇑u).card := by
      have h1 := he_min compEnd (Finset.mem_univ _)
      simpa [imgCard, hsub] using h1
    have hcard_eq : ((Finset.univ : Finset S).image ⇑u).card = (Finset.univ : Finset S).card := by
      apply le_antisymm Finset.card_image_le
      rw [Finset.card_univ, hcardS]
      exact hle
    have hinjOn := Finset.card_image_iff.mp hcard_eq
    exact fun x y hxy ↦ hinjOn (Finset.mem_univ x) (Finset.mem_univ y) hxy
  let u₀ : S →[L] S := eCorest.comp S.subtype.toHom
  let φ₀ : S ≃[L] S := hCore.endEquiv u₀
  refine ⟨C, hCore, φ₀.symm.toHom.comp eCorest, fun x ↦ ?_⟩
  exact hCore.endEquiv_symm_apply_apply u₀ x

/-- A **naked set** `(S, θ)` of `Pol(A)_idem`: an invariant subset `carrier` and invariant
equivalence relation `setoid` with two equivalence classes on which every idempotent polymorphism
acts as a coordinate projection. -/
structure NakedSet (L : Language.{u, v}) (A : Type w) [L.Structure A] where
  /-- Invariant subset `S ⊆ A`. -/
  carrier : Set A
  /-- Closure of `carrier` under `Pol(A)_idem`. -/
  mem_carrier : ∀ {n : ℕ} (f : (idempotentPolymorphismMinion L A).op n) (x : Fin n → carrier),
    f.1 ⟨fun i ↦ (x i).1⟩ ∈ carrier
  /-- Equivalence relation `θ` on `carrier`. -/
  setoid : Setoid carrier
  /-- Componentwise invariance of `setoid` under `Pol(A)_idem`. -/
  rel_preserved : ∀ {n : ℕ} (f : (idempotentPolymorphismMinion L A).op n)
    (x y : Fin n → carrier), (∀ i, setoid.r (x i) (y i)) →
      setoid.r ⟨f.1 ⟨fun i ↦ (x i).1⟩, mem_carrier f x⟩ ⟨f.1 ⟨fun i ↦ (y i).1⟩, mem_carrier f y⟩
  /-- `carrier / setoid` has two equivalence classes. -/
  two_classes : Nonempty (Quotient setoid ≃ Bool)
  /-- Every idempotent polymorphism acts on `carrier / setoid` as a coordinate projection. -/
  acts_as_projection : ∀ {n : ℕ} (f : (idempotentPolymorphismMinion L A).op n),
    ∃ i : Fin n, ∀ x : Fin n → carrier,
      setoid.r ⟨f.1 ⟨fun j ↦ (x j).1⟩, mem_carrier f x⟩ (x i)

/-- **Boolean / Two-Element Naked-Set Theorem**: for every structure `A` of cardinality at most `2`,
if `Pol(A)_idem` admits a minion homomorphism to `idMinion`, then `Pol(A)_idem` possesses a naked
set `(Set.univ, =)`. -/
theorem exists_nakedSet_of_card_le_two {L : Language.{u, v}} {A : Type w} [Fintype A]
    [L.Structure A] (hcard : Fintype.card A ≤ 2)
    (hHom : Nonempty (Minion.Hom (idempotentPolymorphismMinion L A) idMinion)) :
    Nonempty (NakedSet L A) := by
  classical
  obtain ⟨ξ⟩ := hHom
  by_cases hle1 : Fintype.card A ≤ 1
  · have : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp hle1
    exact False.elim (not_nonempty_idempotentMinionHom_id_of_subsingleton ⟨ξ⟩)
  · have hcard2 : Fintype.card A = 2 := by omega
    obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hcard2 |> Trunc.nonempty
    let eB : A ≃ Bool := e.trans finTwoEquiv
    have hproj : ∀ {n : ℕ} (f : (idempotentPolymorphismMinion L A).op n) (x : Fin n → A),
        f.1 ⟨x⟩ = x (ξ.app f) := by
      intro n f x
      set i₀ := ξ.app f
      let σ : Fin n → Fin 2 := fun j ↦ if x j = x i₀ then 0 else 1
      let b := (idempotentPolymorphismMinion L A).minor σ f
      have hb_app : ξ.app b = 0 := by
        rw [ξ.naturality]
        change σ i₀ = 0
        simp [σ]
      let a₀ := eB.symm false
      let a₁ := eB.symm true
      have ha_ne : a₀ ≠ a₁ := fun h ↦ Bool.false_ne_true (by simpa [a₀, a₁] using congrArg eB h)
      have ha_cases : ∀ a : A, a = a₀ ∨ a = a₁ := by
        intro a
        cases h : eB a
        · exact Or.inl (eB.injective (by simpa [a₀] using h))
        · exact Or.inr (eB.injective (by simpa [a₁] using h))
      have hb00 : b.1 ⟨![a₀, a₀]⟩ = a₀ := by
        have hdiag : (⟨![a₀, a₀]⟩ : Power (Fin 2) A) = ⟨fun _ ↦ a₀⟩ := by
          apply Power.ext; funext i; fin_cases i <;> rfl
        rw [hdiag]; exact b.2 a₀
      have hb11 : b.1 ⟨![a₁, a₁]⟩ = a₁ := by
        have hdiag : (⟨![a₁, a₁]⟩ : Power (Fin 2) A) = ⟨fun _ ↦ a₁⟩ := by
          apply Power.ext; funext i; fin_cases i <;> rfl
        rw [hdiag]; exact b.2 a₁
      have hb_not_sym : b.1 ⟨![a₀, a₁]⟩ ≠ b.1 ⟨![a₁, a₀]⟩ := by
        intro hsym_eq
        refine Minion.Hom.false_of_swap_fixed ξ b ?_
        apply Subtype.ext
        refine Language.Hom.ext fun u ↦ ?_
        rcases ha_cases (u 0) with hu0 | hu0 <;> rcases ha_cases (u 1) with hu1 | hu1
        · have h1 : (Power.relabel (L := L) (![1, 0] : Fin 2 → Fin 2) u) = u := by
            apply Power.ext; funext k; fin_cases k <;> dsimp [Power.relabel]
            · exact hu1.trans hu0.symm
            · exact hu0.trans hu1.symm
          change b.1 (Power.relabel (![1, 0] : Fin 2 → Fin 2) u) = b.1 u; rw [h1]
        · have hl : (Power.relabel (L := L) (![1, 0] : Fin 2 → Fin 2) u) = ⟨![a₁, a₀]⟩ := by
            apply Power.ext; funext k; fin_cases k <;> dsimp [Power.relabel]
            · exact hu1
            · exact hu0
          have hr : u = ⟨![a₀, a₁]⟩ := by
            apply Power.ext; funext k; fin_cases k
            · exact hu0
            · exact hu1
          change b.1 (Power.relabel (![1, 0] : Fin 2 → Fin 2) u) = b.1 u
          rw [hl, hr, hsym_eq.symm]
        · have hl : (Power.relabel (L := L) (![1, 0] : Fin 2 → Fin 2) u) = ⟨![a₀, a₁]⟩ := by
            apply Power.ext; funext k; fin_cases k <;> dsimp [Power.relabel]
            · exact hu1
            · exact hu0
          have hr : u = ⟨![a₁, a₀]⟩ := by
            apply Power.ext; funext k; fin_cases k
            · exact hu0
            · exact hu1
          change b.1 (Power.relabel (![1, 0] : Fin 2 → Fin 2) u) = b.1 u
          rw [hl, hr, hsym_eq]
        · have h1 : (Power.relabel (L := L) (![1, 0] : Fin 2 → Fin 2) u) = u := by
            apply Power.ext; funext k; fin_cases k <;> dsimp [Power.relabel]
            · exact hu1.trans hu0.symm
            · exact hu0.trans hu1.symm
          change b.1 (Power.relabel (![1, 0] : Fin 2 → Fin 2) u) = b.1 u; rw [h1]
      have hb_not_p1 : ¬ (b.1 ⟨![a₀, a₁]⟩ = a₁ ∧ b.1 ⟨![a₁, a₀]⟩ = a₀) := by
        rintro ⟨h01, h10⟩
        let idOp : (idempotentPolymorphismMinion L A).op 1 :=
          ⟨Power.proj 0, isIdempotentPolymorphism_proj 0⟩
        have hb_eq_p1 : b = (idempotentPolymorphismMinion L A).minor (fun _ : Fin 1 ↦ (1 : Fin 2))
            idOp := by
          apply Subtype.ext; refine Language.Hom.ext fun u ↦ ?_; change b.1 u = u 1
          rcases ha_cases (u 0) with hu0 | hu0 <;> rcases ha_cases (u 1) with hu1 | hu1
          · have hr : u = ⟨![a₀, a₀]⟩ := by
              apply Power.ext; funext k; fin_cases k
              · exact hu0
              · exact hu1
            rw [hr, hb00]; rfl
          · have hr : u = ⟨![a₀, a₁]⟩ := by
              apply Power.ext; funext k; fin_cases k
              · exact hu0
              · exact hu1
            rw [hr, h01]; rfl
          · have hr : u = ⟨![a₁, a₀]⟩ := by
              apply Power.ext; funext k; fin_cases k
              · exact hu0
              · exact hu1
            rw [hr, h10]; rfl
          · have hr : u = ⟨![a₁, a₁]⟩ := by
              apply Power.ext; funext k; fin_cases k
              · exact hu0
              · exact hu1
            rw [hr, hb11]; rfl
        have h1 : ξ.app b = (1 : Fin 2) := by
          rw [hb_eq_p1, ξ.naturality, Minion.Hom.app_one_eq_zero ξ idOp]
        rw [hb_app] at h1
        exact Fin.zero_ne_one h1
      have hb_p0 : ∀ u v : A, b.1 ⟨![u, v]⟩ = u := by
        have h01 : b.1 ⟨![a₀, a₁]⟩ = a₀ := by
          rcases ha_cases (b.1 ⟨![a₀, a₁]⟩) with h | h
          · exact h
          · rcases ha_cases (b.1 ⟨![a₁, a₀]⟩) with h' | h'
            · exact False.elim (hb_not_p1 ⟨h, h'⟩)
            · exact False.elim (hb_not_sym (h.trans h'.symm))
        have h10 : b.1 ⟨![a₁, a₀]⟩ = a₁ := by
          rcases ha_cases (b.1 ⟨![a₁, a₀]⟩) with h' | h'
          · exact False.elim (hb_not_sym (h01.trans h'.symm))
          · exact h'
        intro u v
        rcases ha_cases u with rfl | rfl <;> rcases ha_cases v with rfl | rfl
        · exact hb00
        · exact h01
        · exact h10
        · exact hb11
      let other : A := if x i₀ = a₀ then a₁ else a₀
      have hpair : (Power.relabel (L := L) σ ⟨![x i₀, other]⟩ : Power (Fin n) A) = ⟨x⟩ := by
        apply Power.ext; funext j
        change (![x i₀, other] : Fin 2 → A) (σ j) = x j
        by_cases hxj : x j = x i₀
        · simp [σ, hxj]
        · simp only [σ, hxj, ↓reduceIte]
          change other = x j
          rcases ha_cases (x i₀) with hi | hi <;> rcases ha_cases (x j) with hj | hj
          · exact False.elim (hxj (hj.trans hi.symm))
          · simp [other, hi, hj]
          · simp [other, hi, hj, ha_ne.symm]
          · exact False.elim (hxj (hj.trans hi.symm))
      have heval : b.1 ⟨![x i₀, other]⟩ = f.1 ⟨x⟩ := by
        change f.1 (Power.relabel σ ⟨![x i₀, other]⟩) = f.1 ⟨x⟩
        rw [hpair]
      rw [← heval, hb_p0]
    let eqSetoid : Setoid (Set.univ : Set A) := ⟨Eq, eq_equivalence⟩
    let eqvUniv : (Set.univ : Set A) ≃ Bool := (Equiv.Set.univ A).trans eB
    let qEquiv : Quotient eqSetoid ≃ (Set.univ : Set A) :=
      { toFun := Quotient.lift id (fun _ _ h ↦ h)
        invFun := Quotient.mk'
        left_inv := fun q ↦ Quotient.inductionOn' q (fun _ ↦ rfl)
        right_inv := fun _ ↦ rfl }
    exact ⟨{
      carrier := Set.univ
      mem_carrier := fun _ _ ↦ trivial
      setoid := eqSetoid
      rel_preserved := fun f x y hxy ↦ by
        have hx : (fun i ↦ (x i).1) = (fun i ↦ (y i).1) :=
          funext fun i ↦ congrArg Subtype.val (hxy i)
        exact Subtype.ext (by simp [hx])
      two_classes := ⟨qEquiv.trans eqvUniv⟩
      acts_as_projection := fun f ↦ ⟨ξ.app f, fun x ↦ Subtype.ext (hproj f (fun j ↦ (x j).1))⟩
    }⟩

end FirstOrder

/-! ### Fixed-template CSP languages and polynomial-time base cases -/

namespace Complexity

open _root_.FirstOrder _root_.FirstOrder.Language _root_.CategoryTheory
open Cslib.Logic Cslib.Complexity Turing.MultiTapeTM

/-- Fixed-template **Constraint Satisfaction Problem** `CSP(A)` over `EncodedStructure`. -/
def cspLanguage {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L) (A : Type w)
    [L.Structure A] : Set EncodedStructure :=
  v.queryLanguage { X | Nonempty (X →[L] A) }

/-- Homomorphically equivalent templates define identical CSP decision languages. -/
theorem cspLanguage_eq_of_homEquiv {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L)
    {A : Type w} {B : Type*} [L.Structure A] [L.Structure B]
    (f : A →[L] B) (g : B →[L] A) :
    cspLanguage v A = cspLanguage v B := by
  ext a
  rw [cspLanguage, cspLanguage, Vocabulary.mem_queryLanguage, Vocabulary.mem_queryLanguage]
  exact and_congr_right fun _ ↦ ⟨fun ⟨h⟩ ↦ ⟨f.comp h⟩, fun ⟨h⟩ ↦ ⟨g.comp h⟩⟩

/-- Any template `A` admitting a `0`-ary polymorphism has `cspLanguage v A ∈ P encStructure`. -/
theorem cspLanguage_mem_P_of_zeroAry_polymorphism {L : Language.{u, v}} [L.IsRelational]
    (v : Vocabulary L) (A : Type w) [L.Structure A]
    (hZero : Nonempty ((FirstOrder.polymorphismMinion L A).op 0)) :
    cspLanguage v A ∈ P encStructure := by
  obtain ⟨c⟩ := hZero
  refine ⟨v.checkShape, v.computableInPolyTime_checkShape, fun a ↦ ?_⟩
  rw [cspLanguage, Vocabulary.mem_queryLanguage, v.checkShape_eq_true_iff]
  exact ⟨fun h ↦ h.1, fun hWF ↦ ⟨hWF, ⟨c.comp (FirstOrder.Power.piHom Fin.elim0)⟩⟩⟩

private theorem all_not_table_eq_true_iff {L : Language.{u, v}} [L.IsRelational]
    {v : Vocabulary L} {a : EncodedStructure} (hWF : v.WellFormed a) (i : Fin v.count) :
    ((v.table a (v.symbol i)).all fun b ↦ !b) = true ↔
      ∀ x : Fin (v.symbol i).1 → Fin a.1, ¬ (v.decode a).RelMap (v.symbol i).2 x := by
  let r := v.symbol i
  have hlen : (v.table a r).length = a.1 ^ r.1 := hWF.length_table v r
  simp only [List.all_eq_true, Bool.not_eq_true']
  refine ⟨?_, ?_⟩
  · intro hall x hrel
    have hget : (v.table a r).getD (tupleIndex x) false = true :=
      (v.relMap_decode a r.2 x).mp hrel
    have hlt : tupleIndex x < (v.table a r).length := hlen ▸ tupleIndex_lt x
    rw [List.getD_eq_getElem _ _ hlt] at hget
    exact Bool.false_ne_true ((hall _ (List.getElem_mem hlt)).symm.trans hget)
  · intro hnone b hb
    obtain ⟨idx, hlt, rfl⟩ := List.mem_iff_getElem.mp hb
    have hlt' : idx < a.1 ^ r.1 := hlen ▸ hlt
    let x : Fin r.1 → Fin a.1 := finFunctionFinEquiv.symm ⟨idx, hlt'⟩
    have hidx : tupleIndex x = idx := tupleIndex_symm ⟨idx, hlt'⟩
    by_contra htrue
    have hbt : (v.table a r)[idx] = true := Bool.eq_true_of_not_eq_false htrue
    refine hnone x ((v.relMap_decode a r.2 x).mpr ?_)
    rw [hidx, List.getD_eq_getElem _ _ hlt]
    exact hbt

/-- Every subsingleton template `A` (`|A| ≤ 1`) has `cspLanguage v A ∈ P encStructure`. -/
theorem cspLanguage_mem_P_of_subsingleton {L : Language.{u, v}} [L.IsRelational]
    (v : Vocabulary L) (A : Type w) [L.Structure A] [Subsingleton A] :
    cspLanguage v A ∈ P encStructure := by
  classical
  rcases isEmpty_or_nonempty A with hEmpty | ⟨⟨a₀⟩⟩
  · let holdsEmpty : Fin v.count → Bool := fun i ↦
      decide (∃ h0 : (v.symbol i).1 = 0,
        Structure.RelMap (M := A) (v.symbol i).2 (fun j ↦ Fin.elim0 (Fin.cast h0 j)))
    let dec : EncodedStructure → Bool := fun a ↦
      v.checkShape a && (a.1 == 0) &&
        (List.finRange v.count).all fun i ↦
          holdsEmpty i || (v.table a (v.symbol i)).all fun b ↦ !b
    have hdecPoly : ComputableInPolyTime dec encStructure encBool := by
      refine ComputableInPolyTime.bool_and'
        (ComputableInPolyTime.bool_and' v.computableInPolyTime_checkShape
          (ComputableInPolyTime.unary_beq' (ComputableInPolyTime.fst encUnary (encList encBits))
            (.const 0)))
        (ComputableInPolyTime.allConst (List.finRange v.count) fun i _ ↦
          ComputableInPolyTime.bool_or' (.const (holdsEmpty i))
            (ComputableInPolyTime.allWithEncoding (encA := encBool) (encL := encBits)
              (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.snd encBool encBool))
              (.const false) (v.computableInPolyTime_table (v.symbol i) .id')))
    refine ⟨dec, hdecPoly, fun a ↦ ?_⟩
    simp only [dec, cspLanguage, Vocabulary.mem_queryLanguage, Bool.and_eq_true,
      v.checkShape_eq_true_iff, beq_iff_eq]
    rw [List.all_eq_true]
    simp only [List.mem_finRange, forall_true_left, Bool.or_eq_true]
    refine ⟨?_, ?_⟩
    · rintro ⟨hWF, ⟨hom⟩⟩
      have ha0 : a.1 = 0 := by
        by_contra hpos
        exact isEmptyElim (hom ⟨0, Nat.pos_of_ne_zero hpos⟩)
      refine ⟨⟨hWF, ha0⟩, fun i ↦ ?_⟩
      by_cases hh : holdsEmpty i = true
      · exact Or.inl hh
      · right
        rw [all_not_table_eq_true_iff hWF i]
        intro x hrel
        by_cases h0 : (v.symbol i).1 = 0
        · have himg := hom.map_rel (v.symbol i).2 x hrel
          have hfn : hom ∘ x = (fun j ↦ Fin.elim0 (Fin.cast h0 j)) :=
            funext fun j ↦ isEmptyElim (hom (x j))
          rw [hfn] at himg
          exact hh (decide_eq_true ⟨h0, himg⟩)
        · exact Fin.elim0 (Fin.cast ha0 (x ⟨0, Nat.pos_of_ne_zero h0⟩))
    · rintro ⟨⟨hWF, ha0⟩, hall⟩
      refine ⟨hWF, ⟨{
        toFun := fun x ↦ Fin.elim0 (Fin.cast ha0 x)
        map_fun' := fun f ↦ isEmptyElim f
        map_rel' := fun {k} r x hrel ↦ ?_
      }⟩⟩
      let i := v.symbol.symm ⟨k, r⟩
      have hi : v.symbol i = ⟨k, r⟩ := v.symbol.apply_symm_apply ⟨k, r⟩
      rcases hall i with hh | hnone
      · dsimp only [holdsEmpty] at hh
        rcases hsym : v.symbol i with ⟨k', r'⟩
        rw [hsym] at hh hi
        simp only [decide_eq_true_eq] at hh
        obtain ⟨h0, hA⟩ := hh
        rcases Sigma.mk.inj_iff.mp hi with ⟨rfl, hr'⟩
        cases hr'
        subst h0
        exact Eq.mp (congrArg (Structure.RelMap r') (funext fun j ↦ Fin.elim0 j).symm) hA
      · rw [all_not_table_eq_true_iff hWF i] at hnone
        exfalso
        rcases hsym : v.symbol i with ⟨k', r'⟩
        rw [hsym] at hi hnone
        rcases Sigma.mk.inj_iff.mp hi with ⟨rfl, hr'⟩
        cases hr'
        exact hnone x hrel
  · let holdsUnit : Fin v.count → Bool := fun i ↦
      decide (Structure.RelMap (M := A) (v.symbol i).2 (fun _ ↦ a₀))
    let dec : EncodedStructure → Bool := fun a ↦
      v.checkShape a &&
        (List.finRange v.count).all fun i ↦
          holdsUnit i || (v.table a (v.symbol i)).all fun b ↦ !b
    have hdecPoly : ComputableInPolyTime dec encStructure encBool := by
      refine ComputableInPolyTime.bool_and' v.computableInPolyTime_checkShape
        (ComputableInPolyTime.allConst (List.finRange v.count) fun i _ ↦
          ComputableInPolyTime.bool_or' (.const (holdsUnit i))
            (ComputableInPolyTime.allWithEncoding (encA := encBool) (encL := encBits)
              (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.snd encBool encBool))
              (.const false) (v.computableInPolyTime_table (v.symbol i) .id')))
    refine ⟨dec, hdecPoly, fun a ↦ ?_⟩
    simp only [dec, cspLanguage, Vocabulary.mem_queryLanguage, Bool.and_eq_true,
      v.checkShape_eq_true_iff]
    rw [List.all_eq_true]
    simp only [List.mem_finRange, forall_true_left, Bool.or_eq_true]
    refine ⟨?_, ?_⟩
    · rintro ⟨hWF, ⟨hom⟩⟩
      refine ⟨hWF, fun i ↦ ?_⟩
      by_cases hh : holdsUnit i = true
      · exact Or.inl hh
      · right
        rw [all_not_table_eq_true_iff hWF i]
        intro x hrel
        have himg := hom.map_rel (v.symbol i).2 x hrel
        have hfn : hom ∘ x = (fun _ ↦ a₀) := funext fun _ ↦ Subsingleton.elim _ _
        rw [hfn] at himg
        exact hh (decide_eq_true himg)
    · rintro ⟨hWF, hall⟩
      refine ⟨hWF, ⟨{
        toFun := fun _ ↦ a₀
        map_fun' := fun f ↦ isEmptyElim f
        map_rel' := fun {k} r x hrel ↦ ?_
      }⟩⟩
      let i := v.symbol.symm ⟨k, r⟩
      have hi : v.symbol i = ⟨k, r⟩ := v.symbol.apply_symm_apply ⟨k, r⟩
      rcases hall i with hh | hnone
      · simp only [holdsUnit, decide_eq_true_eq] at hh
        rcases hsym : v.symbol i with ⟨k', r'⟩
        rw [hsym] at hi hh
        rcases Sigma.mk.inj_iff.mp hi with ⟨rfl, hr'⟩
        cases hr'
        exact hh
      · rw [all_not_table_eq_true_iff hWF i] at hnone
        exfalso
        rcases hsym : v.symbol i with ⟨k', r'⟩
        rw [hsym] at hi hnone
        rcases Sigma.mk.inj_iff.mp hi with ⟨rfl, hr'⟩
        cases hr'
        exact hnone x hrel

end Complexity

end CslibFrontier
