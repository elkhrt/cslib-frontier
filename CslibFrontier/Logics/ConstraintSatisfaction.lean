/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Polymorphism
public import Mathlib.Data.Set.Card
public import Mathlib.ModelTheory.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

/-!
# Constraint Satisfaction Problems, Polymorphisms, and Bounded Pathwidth Duality

Over a finite positive-arity relational first-order language `L` and an `L`-structure `A`, the
non-uniform Constraint Satisfaction Problem `CSP(A)` asks whether a finite instance `I = (V, C)` of
relational constraints admits a satisfying assignment `V → A`. This module formalizes polymorphisms,
cores, primitive-positive definability and the finite Geiger /
Bodnarchuk–Kaluzhnin–Kotov–Romov Galois connection, finite CSP instances, pathwidth, bounded
pathwidth duality, and the injective-scope pigeonhole cover, all under standard Lean axioms.

## Main definitions

* `CslibFrontier.Logics.IsFinitePosRelational`: finite relational signature with no nullary
  relations.
* `CslibFrontier.Logics.IsStructurePolymorphism`, `CslibFrontier.Logics.IsCore`,
  `CslibFrontier.Logics.IsPPDefinable`: polymorphisms, cores, and primitive-positive
  definability.
* `CslibFrontier.Logics.CSPConstraint`, `CslibFrontier.Logics.CSPInstance`,
  `CslibFrontier.Logics.CSPInstance.HasPathwidthAtMost`,
  `CslibFrontier.Logics.HasPathwidthDualityAtMost`,
  `CslibFrontier.Logics.HasBoundedPathwidthDuality`: finite CSP instances, pathwidth, and
  bounded pathwidth duality.

## Main results

* `CslibFrontier.Logics.isPPDefinable_iff_forall_polymorphism`: finite Inv–Pol Galois
  connection of Geiger and Bodnarchuk–Kaluzhnin–Kotov–Romov.
* `CslibFrontier.Logics.isPPDefinable_of_gadget`: closure of primitive-positive definability
  under existential quantification of finite conjunctions with variable equalities.
* `CslibFrontier.Logics.CSPInstance.exists_injective_scope_cover`: pigeonhole variable-cloud
  cover eliminating repeated variables from constraint scopes of an unsatisfiable instance.

## Tags

constraint satisfaction, polymorphism, relational clone, core structure, pathwidth duality
-/

public section

namespace CslibFrontier.Logics

open FirstOrder FirstOrder.Language Cslib.Logic

section RelationalClone

/-- A first-order language `L` is finite positive-arity relational when it has no function
symbols, no nullary relation symbols, and only finitely many relation symbols across all arities. -/
class IsFinitePosRelational (L : FirstOrder.Language) : Prop where
  /-- Every function-symbol sort (including constants) is empty. -/
  isEmpty_functions : ∀ n : ℕ, IsEmpty (L.Functions n)
  /-- Nullary relations are excluded. -/
  isEmpty_relations_zero : IsEmpty (L.Relations 0)
  /-- The total set of basic relation symbols across all arities is finite. -/
  finite_sigma_relations : Finite (Σ n : ℕ, L.Relations n)

/-- Every `IsFinitePosRelational` language is relational (`L.IsRelational`). -/
scoped instance IsFinitePosRelational.instIsRelational (L : FirstOrder.Language)
    [h : IsFinitePosRelational L] : L.IsRelational :=
  h.isEmpty_functions

/-- Every basic relation symbol of an `IsFinitePosRelational` language has positive arity. -/
theorem IsFinitePosRelational.arity_pos {L : FirstOrder.Language} [IsFinitePosRelational L]
    {n : ℕ} (R : L.Relations n) : 0 < n := by
  rcases n with _ | n
  · exact (IsFinitePosRelational.isEmpty_relations_zero (L := L)).elim R
  · exact Nat.succ_pos n

/-- Every arity slice `L.Relations n` of an `IsFinitePosRelational` language is finite. -/
theorem IsFinitePosRelational.finite_relations (L : FirstOrder.Language) [IsFinitePosRelational L]
    (n : ℕ) : Finite (L.Relations n) :=
  have := IsFinitePosRelational.finite_sigma_relations (L := L)
  Finite.of_injective (fun R : L.Relations n ↦ (⟨n, R⟩ : Σ k, L.Relations k))
    fun _ _ h ↦ eq_of_heq (Sigma.mk.inj h).2

/-- Every `IsFinitePosRelational` language has a uniform upper bound on the arities of its basic
relation symbols. -/
theorem IsFinitePosRelational.exists_max_arity (L : FirstOrder.Language)
    [IsFinitePosRelational L] :
    ∃ M : ℕ, ∀ ⦃n : ℕ⦄, L.Relations n → n ≤ M := by
  classical
  have := IsFinitePosRelational.finite_sigma_relations (L := L)
  let _ : Fintype (Σ k : ℕ, L.Relations k) := Fintype.ofFinite _
  let l : List (Σ k : ℕ, L.Relations k) := (Finset.univ : Finset _).toList
  have hle_fold : ∀ (xs : List (Σ k : ℕ, L.Relations k)) (s : Σ k : ℕ, L.Relations k),
      s ∈ xs → s.1 ≤ xs.foldr (fun x acc ↦ max x.1 acc) 0 := by
    intro xs s hs
    induction xs with
    | nil => cases hs
    | cons x tl ih =>
      rcases List.mem_cons.mp hs with rfl | htl
      · exact le_max_left _ _
      · exact (ih htl).trans (le_max_right _ _)
  exact ⟨l.foldr (fun x acc ↦ max x.1 acc) 0, fun n R ↦
    hle_fold l ⟨n, R⟩ (Finset.mem_toList.mpr (Finset.mem_univ _))⟩

/-- Interpretation of an `n`-ary relation symbol `R : L.Relations n` in `A` as a subset of
`Fin n → A`. -/
@[expose]
def relSet {L : FirstOrder.Language} (A : Type*) [L.Structure A] {n : ℕ}
    (R : L.Relations n) : Set (Fin n → A) :=
  {t | Structure.RelMap R t}

@[simp]
theorem mem_relSet {L : FirstOrder.Language} {A : Type*} [L.Structure A] {n : ℕ}
    (R : L.Relations n) (t : Fin n → A) :
    t ∈ relSet A R ↔ Structure.RelMap R t :=
  Iff.rfl

/-- An operation `f : (J → A) → A` is a polymorphism of the `L`-structure `A` if it preserves
every basic relation symbol of `L`. -/
@[expose]
def IsStructurePolymorphism (L : FirstOrder.Language) (A : Type*) [L.Structure A]
    {J : Type*} (f : (J → A) → A) : Prop :=
  ∀ ⦃n : ℕ⦄ (R : L.Relations n), IsPolymorphism f (relSet A R)

/-- Characterization of `IsStructurePolymorphism`. -/
theorem isStructurePolymorphism_iff {L : FirstOrder.Language} {A : Type*} [L.Structure A]
    {J : Type*} {f : (J → A) → A} :
    IsStructurePolymorphism L A f ↔
      ∀ ⦃n : ℕ⦄ (R : L.Relations n), IsPolymorphism f (relSet A R) :=
  Iff.rfl

/-- Every coordinate projection is a polymorphism of every `L`-structure. -/
theorem isStructurePolymorphism_proj (L : FirstOrder.Language) (A : Type*) [L.Structure A]
    {J : Type*} (j : J) :
    IsStructurePolymorphism L A (fun x : J → A ↦ x j) :=
  fun _ R ↦ isPolymorphism_projection j (relSet A R)

/-- Polymorphisms of an `L`-structure are closed under composition. -/
theorem IsStructurePolymorphism.comp {L : FirstOrder.Language} {A : Type*} [L.Structure A]
    {J K : Type*} {f : (K → A) → A} {g : K → (J → A) → A}
    (hf : IsStructurePolymorphism L A f) (hg : ∀ k, IsStructurePolymorphism L A (g k)) :
    IsStructurePolymorphism L A (fun x ↦ f (fun k ↦ g k x)) :=
  fun _ R ↦ (hf R).comp fun k ↦ hg k R

/-- An operation `f : (J → A) → A` is idempotent if `f (fun _ ↦ a) = a` for all `a : A`. -/
@[expose]
def IsIdempotentOp {A J : Type*} (f : (J → A) → A) : Prop :=
  ∀ a : A, f (fun _ ↦ a) = a

/-- A relational `L`-structure `A` is a core if every unary polymorphism `f : (Fin 1 → A) → A`
arises from an `L`-automorphism `A ≃[L] A`. -/
@[expose]
def IsCore (L : FirstOrder.Language) (A : Type*) [L.Structure A] : Prop :=
  ∀ f : A → A, IsStructurePolymorphism L A (fun x : Fin 1 → A ↦ f (x 0)) →
    ∃ e : A ≃[L] A, ∀ a : A, e a = f a

/-- Every unary polymorphism of a finite core relational structure has a two-sided inverse that
also preserves and reflects all basic relations. -/
theorem IsCore.exists_equiv {L : FirstOrder.Language} {A : Type*} [L.Structure A]
    (hcore : IsCore L A) {f : A → A}
    (hf : ∀ ⦃n : ℕ⦄ (R : L.Relations n) (t : Fin n → A),
      Structure.RelMap R t → Structure.RelMap R (f ∘ t)) :
    ∃ e : A ≃[L] A, ∀ a : A, e a = f a := by
  refine hcore f fun n R a ha ↦ ?_
  simpa [Function.comp_def] using hf R (a 0) (ha 0)

/-- On a finite relational `L`-structure `A`, `IsCore L A` holds if and only if every unary
relation-preserving map `f : A → A` is bijective. -/
theorem isCore_iff_bijective {L : FirstOrder.Language} [L.IsRelational]
    {A : Type*} [L.Structure A] [Finite A] :
    IsCore L A ↔
      ∀ f : A → A,
        (∀ ⦃n : ℕ⦄ (R : L.Relations n) (t : Fin n → A),
          Structure.RelMap R t → Structure.RelMap R (f ∘ t)) →
        Function.Bijective f := by
  classical
  constructor
  · intro hcore f hf
    obtain ⟨e, he⟩ := hcore.exists_equiv hf
    have hfeq : f = e := funext fun a ↦ (he a).symm
    rw [hfeq]
    exact e.toEquiv.bijective
  · intro hbij f hf
    have hpres : ∀ ⦃n : ℕ⦄ (R : L.Relations n) (t : Fin n → A),
        Structure.RelMap R t → Structure.RelMap R (f ∘ t) := fun n R t ht ↦
      hf R (fun _ ↦ t) fun _ ↦ ht
    let eqv : A ≃ A := Equiv.ofBijective f (hbij f hpres)
    refine ⟨{ toEquiv := eqv
              map_fun' := fun {n} fn _ ↦ IsEmpty.elim' inferInstance fn
              map_rel' := fun {n} R t ↦ ?_ }, fun _ ↦ rfl⟩
    refine ⟨fun hft ↦ ?_, fun ht ↦ hpres R t ht⟩
    -- Finite bijection mapping `relSet A R` into itself is surjective onto `relSet A R`.
    let _ : Fintype (Fin n → A) := Fintype.ofFinite _
    let S : Finset (Fin n → A) := (relSet A R).toFinset
    let φ : (Fin n → A) ↪ (Fin n → A) :=
      ⟨fun u ↦ eqv ∘ u, fun u v h ↦ funext fun i ↦ eqv.injective (congrFun h i)⟩
    have hmap_sub : S.map φ ⊆ S := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
      exact Set.mem_toFinset.mpr (hpres R u (Set.mem_toFinset.mp hu))
    have hmap_eq : S.map φ = S :=
      Finset.eq_of_subset_of_card_le hmap_sub (by rw [Finset.card_map])
    have hmem : φ t ∈ S.map φ := by
      rw [hmap_eq]
      exact Set.mem_toFinset.mpr hft
    rcases Finset.mem_map.mp hmem with ⟨u, hu, hut⟩
    cases φ.injective hut
    exact Set.mem_toFinset.mp hu

/-- An atomic clause inside a primitive-positive formula with `n` free and `m` existentially
quantified variables. -/
structure PPAtom (L : FirstOrder.Language) (n m : ℕ) where
  /-- Arity of the basic relation symbol. -/
  arity : ℕ
  /-- Basic relation symbol applied in this atom. -/
  rel : L.Relations arity
  /-- Tuple of free (`Sum.inl`) and existential (`Sum.inr`) variables. -/
  scope : Fin arity → Fin n ⊕ Fin m

/-- A relation `S : Set (Fin n → A)` lies in the relational clone of `A` (is primitive-positively
definable in `A`) if it is cut out by an existential quantification of a finite conjunction of
basic relation atoms of `L` and variable equalities. -/
@[expose]
def IsPPDefinable (L : FirstOrder.Language) (A : Type*) [L.Structure A] {n : ℕ}
    (S : Set (Fin n → A)) : Prop :=
  ∃ (m : ℕ) (atoms : List (PPAtom L n m)) (eqs : List ((Fin n ⊕ Fin m) × (Fin n ⊕ Fin m))),
    ∀ a : Fin n → A, a ∈ S ↔
      ∃ b : Fin m → A,
        (∀ c ∈ atoms, Structure.RelMap c.rel (Sum.elim a b ∘ c.scope)) ∧
        (∀ p ∈ eqs, Sum.elim a b p.1 = Sum.elim a b p.2)

/-- Every basic relation of `A` lies in the relational clone of `A`. -/
theorem isPPDefinable_relSet {L : FirstOrder.Language} (A : Type*) [L.Structure A]
    {n : ℕ} (R : L.Relations n) :
    IsPPDefinable L A (relSet A R) := by
  refine ⟨0, [⟨n, R, Sum.inl⟩], [], fun a ↦ ?_⟩
  constructor
  · intro ha
    refine ⟨Fin.elim0, ?_, by simp⟩
    simp only [List.mem_singleton, forall_eq]
    exact ha
  · rintro ⟨_, hat, _⟩
    exact hat ⟨n, R, Sum.inl⟩ (List.mem_singleton.mpr rfl)

/-- Every primitive-positively definable relation is preserved by every polymorphism of `A`. -/
theorem IsPPDefinable.isPolymorphism {L : FirstOrder.Language} {A : Type*} [L.Structure A]
    {n : ℕ} {S : Set (Fin n → A)} (hS : IsPPDefinable L A S)
    {J : Type*} {f : (J → A) → A} (hf : IsStructurePolymorphism L A f) :
    IsPolymorphism f S := by
  classical
  rcases hS with ⟨m, atoms, eqs, hiff⟩
  intro a ha
  have hex : ∀ j : J, ∃ b : Fin m → A,
      (∀ c ∈ atoms, Structure.RelMap c.rel (Sum.elim (a j) b ∘ c.scope)) ∧
      (∀ p ∈ eqs, Sum.elim (a j) b p.1 = Sum.elim (a j) b p.2) :=
    fun j ↦ (hiff (a j)).mp (ha j)
  choose b hbat hbeq using hex
  rw [hiff]
  let b' : Fin m → A := fun k ↦ f (fun j ↦ b j k)
  have hsum : ∀ v : Fin n ⊕ Fin m,
      Sum.elim (fun i ↦ f (fun j ↦ a j i)) b' v = f (fun j ↦ Sum.elim (a j) (b j) v) := by
    rintro (i | k) <;> rfl
  refine ⟨b', ?_, ?_⟩
  · intro c hc
    have hpol := hf c.rel (fun j ↦ Sum.elim (a j) (b j) ∘ c.scope) fun j ↦ hbat j c hc
    have harg : Sum.elim (fun i ↦ f (fun j ↦ a j i)) b' ∘ c.scope =
        fun i ↦ f (fun j ↦ (Sum.elim (a j) (b j) ∘ c.scope) i) := by
      ext i
      exact hsum (c.scope i)
    rw [harg]
    exact hpol
  · intro p hp
    rw [hsum p.1, hsum p.2]
    congr 1
    ext j
    exact hbeq j p hp

/-- **Geiger / Bodnarchuk–Kaluzhnin–Kotov–Romov Galois Connection**: over a finite
`L`-structure `A` with `[IsFinitePosRelational L]`, a nonempty relation `S : Set (Fin n → A)` is
primitive-positively definable in `A` if and only if it is preserved by every positive-arity
polymorphism `f : (Fin k → A) → A` of `A`.
-/
theorem isPPDefinable_iff_forall_polymorphism {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {n : ℕ} {S : Set (Fin n → A)} (hne : S.Nonempty) :
    IsPPDefinable L A S ↔
      ∀ (k : ℕ), 0 < k → ∀ f : (Fin k → A) → A,
        IsStructurePolymorphism L A f → IsPolymorphism f S := by
  classical
  refine ⟨fun hS _ _ _ hf ↦ hS.isPolymorphism hf, fun hinv ↦ ?_⟩
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype S := Fintype.ofFinite S
  have hSpos : 0 < Fintype.card S := @Fintype.card_pos S _ hne.to_subtype
  -- Auxiliary variables enumerate all columns `S → A`.
  let Col := S → A
  let _ : Fintype Col := Fintype.ofFinite Col
  let eCol : Col ≃ Fin (Fintype.card Col) := Fintype.equivFin Col
  have := IsFinitePosRelational.finite_sigma_relations (L := L)
  let _ : Fintype (Σ r : ℕ, L.Relations r) := Fintype.ofFinite _
  obtain ⟨M, hM⟩ := IsFinitePosRelational.exists_max_arity L
  -- Enumerate every tuple of columns belonging pointwise to a basic relation `R`.
  let ValidScope :=
    {x : (sig : Σ r : ℕ, L.Relations r) × (Fin sig.1 → Col) //
      ∀ t : S, Structure.RelMap x.1.2 (fun i ↦ x.2 i t)}
  let _ : Fintype ValidScope := Fintype.ofFinite ValidScope
  let atoms : List (PPAtom L n (Fintype.card Col)) :=
    (Finset.univ : Finset ValidScope).toList.map fun x ↦
      ⟨x.1.1.1, x.1.1.2, fun i ↦ Sum.inr (eCol (x.1.2 i))⟩
  let eqs : List ((Fin n ⊕ Fin (Fintype.card Col)) × (Fin n ⊕ Fin (Fintype.card Col))) :=
    (List.finRange n).map fun i ↦ (Sum.inl i, Sum.inr (eCol fun t : S ↦ t.1 i))
  refine ⟨Fintype.card Col, atoms, eqs, fun a ↦ ?_⟩
  constructor
  · intro ha
    let t₀ : S := ⟨a, ha⟩
    refine ⟨fun j ↦ (eCol.symm j) t₀, ?_, ?_⟩
    · intro c hc
      rcases List.mem_map.mp hc with ⟨x, _, rfl⟩
      simpa [Function.comp_def] using x.2 t₀
    · intro p hp
      rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
      simp [t₀]
  · rintro ⟨b, hbat, hbeq⟩
    let eS : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
    let f : (Fin (Fintype.card S) → A) → A := fun v ↦ b (eCol (v ∘ eS))
    have hf : IsStructurePolymorphism L A f := by
      intro r R u hu
      let x : ValidScope :=
        ⟨⟨⟨r, R⟩, fun i t ↦ u (eS t) i⟩, fun t ↦ hu (eS t)⟩
      have hmem : (⟨r, R, fun i ↦ Sum.inr (eCol (x.1.2 i))⟩ : PPAtom L n (Fintype.card Col)) ∈
          atoms :=
        List.mem_map.mpr ⟨x, Finset.mem_toList.mpr (Finset.mem_univ x), rfl⟩
      simpa [f, x, Function.comp_def] using hbat _ hmem
    have hres := hinv (Fintype.card S) hSpos f hf (fun j ↦ (eS.symm j).1)
      fun j ↦ (eS.symm j).2
    convert hres using 1
    ext i
    have hpmem : (Sum.inl i, Sum.inr (eCol fun t : S ↦ t.1 i)) ∈ eqs :=
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have hi : a i = b (eCol fun t : S ↦ t.1 i) := hbeq _ hpmem
    rw [hi]
    change b (eCol fun t : S ↦ t.1 i) = b (eCol ((fun j ↦ (eS.symm j).1 i) ∘ eS))
    congr 2
    ext t
    simp

/-- Adding equality constraints is preserved under finite conjunctions of primitive-positively
definable relations, so the relational clone is closed under variable-identified conjunctions and
existential projections. -/
theorem isPPDefinable_of_gadget {L : FirstOrder.Language} {A : Type*} [L.Structure A]
    {n m : ℕ} (clauses : List ((k : ℕ) × Set (Fin k → A) × (Fin k → Fin n ⊕ Fin m)))
    (eqs : List ((Fin n ⊕ Fin m) × (Fin n ⊕ Fin m)))
    (hcl : ∀ c ∈ clauses, IsPPDefinable L A c.2.1) :
    IsPPDefinable L A
      {a : Fin n → A | ∃ b : Fin m → A,
        (∀ c ∈ clauses, Sum.elim a b ∘ c.2.2 ∈ c.2.1) ∧
        (∀ p ∈ eqs, Sum.elim a b p.1 = Sum.elim a b p.2)} := by
  classical
  let cls := clauses
  have hex : ∀ idx : Fin cls.length,
      ∃ (mc : ℕ) (atc : List (PPAtom L (cls.get idx).1 mc))
        (eqc : List ((Fin (cls.get idx).1 ⊕ Fin mc) × (Fin (cls.get idx).1 ⊕ Fin mc))),
        ∀ u : Fin (cls.get idx).1 → A, u ∈ (cls.get idx).2.1 ↔
          ∃ bc : Fin mc → A,
            (∀ at₀ ∈ atc, Structure.RelMap at₀.rel (Sum.elim u bc ∘ at₀.scope)) ∧
            (∀ p ∈ eqc, Sum.elim u bc p.1 = Sum.elim u bc p.2) :=
      fun idx ↦ hcl (cls.get idx) (List.get_mem cls idx)
  choose mc atc eqc hspec using hex
  let Aux := Fin m ⊕ (Σ idx : Fin cls.length, Fin (mc idx))
  let _ : Fintype Aux := inferInstance
  let eAux : Aux ≃ Fin (Fintype.card Aux) := Fintype.equivFin Aux
  let mapVar (idx : Fin cls.length) :
      Fin (cls.get idx).1 ⊕ Fin (mc idx) → Fin n ⊕ Fin (Fintype.card Aux)
    | Sum.inl i => match (cls.get idx).2.2 i with
      | Sum.inl x => Sum.inl x
      | Sum.inr y => Sum.inr (eAux (Sum.inl y))
    | Sum.inr z => Sum.inr (eAux (Sum.inr ⟨idx, z⟩))
  let mapBase : Fin n ⊕ Fin m → Fin n ⊕ Fin (Fintype.card Aux)
    | Sum.inl x => Sum.inl x
    | Sum.inr y => Sum.inr (eAux (Sum.inl y))
  let allAtoms : List (PPAtom L n (Fintype.card Aux)) :=
    (List.finRange cls.length).flatMap fun idx ↦
      (atc idx).map fun a₀ ↦ ⟨a₀.arity, a₀.rel, mapVar idx ∘ a₀.scope⟩
  let allEqs : List ((Fin n ⊕ Fin (Fintype.card Aux)) × (Fin n ⊕ Fin (Fintype.card Aux))) :=
    (eqs.map fun p ↦ (mapBase p.1, mapBase p.2)) ++
    ((List.finRange cls.length).flatMap fun idx ↦
      (eqc idx).map fun p ↦ (mapVar idx p.1, mapVar idx p.2))
  refine ⟨Fintype.card Aux, allAtoms, allEqs, fun a ↦ ?_⟩
  constructor
  · rintro ⟨b, hcb, heqb⟩
    have hbc : ∀ idx : Fin cls.length, ∃ bc : Fin (mc idx) → A,
        (∀ a₀ ∈ atc idx,
          Structure.RelMap a₀.rel (Sum.elim (Sum.elim a b ∘ (cls.get idx).2.2) bc ∘ a₀.scope)) ∧
        (∀ p ∈ eqc idx,
          Sum.elim (Sum.elim a b ∘ (cls.get idx).2.2) bc p.1 =
            Sum.elim (Sum.elim a b ∘ (cls.get idx).2.2) bc p.2) :=
      fun idx ↦ (hspec idx _).mp (hcb (cls.get idx) (List.get_mem cls idx))
    choose bc hbc_at hbc_eq using hbc
    let B : Fin (Fintype.card Aux) → A := fun j ↦
      match eAux.symm j with
      | Sum.inl y => b y
      | Sum.inr ⟨idx, z⟩ => bc idx z
    have hmv : ∀ (idx : Fin cls.length) (v : Fin (cls.get idx).1 ⊕ Fin (mc idx)),
        Sum.elim a B (mapVar idx v) =
          Sum.elim (Sum.elim a b ∘ (cls.get idx).2.2) (bc idx) v := by
      intro idx v
      cases v with
      | inl i =>
        dsimp [mapVar]
        cases h : (cls.get idx).2.2 i with
        | inl x => simp
        | inr y => simp [B]
      | inr z => simp [mapVar, B]
    have hmb : ∀ v : Fin n ⊕ Fin m, Sum.elim a B (mapBase v) = Sum.elim a b v := by
      rintro (x | y) <;> simp [mapBase, B]
    refine ⟨B, ?_, ?_⟩
    · intro c hc
      rcases List.mem_flatMap.mp hc with ⟨idx, _, hc'⟩
      rcases List.mem_map.mp hc' with ⟨a₀, ha₀, rfl⟩
      have hrel := hbc_at idx a₀ ha₀
      convert hrel using 1
      ext i
      exact hmv idx (a₀.scope i)
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_map.mp hp with ⟨p₀, hp₀, rfl⟩
        rw [hmb p₀.1, hmb p₀.2]
        exact heqb p₀ hp₀
      · rcases List.mem_flatMap.mp hp with ⟨idx, _, hp'⟩
        rcases List.mem_map.mp hp' with ⟨p₀, hp₀, rfl⟩
        rw [hmv idx p₀.1, hmv idx p₀.2]
        exact hbc_eq idx p₀ hp₀
  · rintro ⟨B, hBat, hBeq⟩
    let b : Fin m → A := fun y ↦ B (eAux (Sum.inl y))
    let bc : (idx : Fin cls.length) → Fin (mc idx) → A :=
      fun idx z ↦ B (eAux (Sum.inr ⟨idx, z⟩))
    have hmv : ∀ (idx : Fin cls.length) (v : Fin (cls.get idx).1 ⊕ Fin (mc idx)),
        Sum.elim (Sum.elim a b ∘ (cls.get idx).2.2) (bc idx) v =
          Sum.elim a B (mapVar idx v) := by
      intro idx v
      cases v with
      | inl i =>
        dsimp [mapVar]
        cases h : (cls.get idx).2.2 i with
        | inl x => simp
        | inr y => simp [b]
      | inr z => simp [mapVar, bc]
    have hmb : ∀ v : Fin n ⊕ Fin m, Sum.elim a b v = Sum.elim a B (mapBase v) := by
      rintro (x | y) <;> simp [mapBase, b]
    refine ⟨b, ?_, ?_⟩
    · intro c hc
      obtain ⟨idx, rfl⟩ := List.mem_iff_get.mp hc
      rw [hspec idx]
      refine ⟨bc idx, ?_, ?_⟩
      · intro a₀ ha₀
        have hmem : (⟨a₀.arity, a₀.rel, mapVar idx ∘ a₀.scope⟩ :
            PPAtom L n (Fintype.card Aux)) ∈ allAtoms :=
          List.mem_flatMap.mpr ⟨idx, List.mem_finRange idx, List.mem_map.mpr ⟨a₀, ha₀, rfl⟩⟩
        have hrel := hBat _ hmem
        convert hrel using 1
        ext i
        exact hmv idx (a₀.scope i)
      · intro p₀ hp₀
        have hmem : (mapVar idx p₀.1, mapVar idx p₀.2) ∈ allEqs :=
          List.mem_append_right _ (List.mem_flatMap.mpr
            ⟨idx, List.mem_finRange idx, List.mem_map.mpr ⟨p₀, hp₀, rfl⟩⟩)
        rw [hmv idx p₀.1, hmv idx p₀.2]
        exact hBeq _ hmem
    · intro p₀ hp₀
      have hmem : (mapBase p₀.1, mapBase p₀.2) ∈ allEqs :=
        List.mem_append_left _ (List.mem_map.mpr ⟨p₀, hp₀, rfl⟩)
      rw [hmb p₀.1, hmb p₀.2]
      exact hBeq _ hmem

end RelationalClone

/-! ### CSP instances, solutions, subinstances, pathwidth, and bounded pathwidth duality -/

section CSP

/-- A single relational constraint `(σ, R)` over language `L` and variable carrier `V`, consisting
of an arity `arity`, a basic relation symbol `rel : L.Relations arity`, and a scope tuple
`scope : Fin arity → V`. -/
structure CSPConstraint (L : FirstOrder.Language) (V : Type*) where
  /-- Arity of the constraint relation. -/
  arity : ℕ
  /-- The basic relation symbol of `L`. -/
  rel : L.Relations arity
  /-- The tuple of variables constrained by `rel`. -/
  scope : Fin arity → V

namespace CSPConstraint

variable {L : FirstOrder.Language} {V W : Type*}

/-- Push a constraint forward along a variable map `h : V → W`. -/
@[expose, simps]
def map (h : V → W) (c : CSPConstraint L V) : CSPConstraint L W where
  arity := c.arity
  rel := c.rel
  scope := h ∘ c.scope

/-- Pushing a constraint forward along `id` is the identity. -/
@[simp]
theorem map_id (c : CSPConstraint L V) : c.map id = c :=
  rfl

/-- Pushing a constraint forward along a composition equals sequential pushforward. -/
theorem map_comp {U : Type*} (g : W → U) (h : V → W) (c : CSPConstraint L V) :
    (c.map h).map g = c.map (g ∘ h) :=
  rfl

/-- Equivalence of `CSPConstraint L V` with the sigma type `Σ n, L.Relations n × (Fin n → V)`. -/
def equivSigma (L : FirstOrder.Language) (V : Type*) :
    CSPConstraint L V ≃ Σ n : ℕ, L.Relations n × (Fin n → V) where
  toFun c := ⟨c.arity, c.rel, c.scope⟩
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv c := by cases c; rfl
  right_inv s := by rcases s with ⟨_, _, _⟩; rfl

end CSPConstraint

/-- A finite instance `I = (V, C)` of `CSP(A)` over language `L` on ambient variable carrier `V`:
a finite set `vars : Set V` of variables and a finite set `constraints` of `L`-constraints whose
scopes all take values in `vars`. -/
@[ext]
structure CSPInstance (L : FirstOrder.Language) (V : Type*) where
  /-- The finite set of variables of the instance. -/
  vars : Set V
  /-- The finite set of constraints of the instance. -/
  constraints : Set (CSPConstraint L V)
  /-- Finiteness of `vars`. -/
  finite_vars : vars.Finite
  /-- Finiteness of `constraints`. -/
  finite_constraints : constraints.Finite
  /-- Every variable appearing in a constraint scope belongs to `vars`. -/
  scope_mem : ∀ ⦃c : CSPConstraint L V⦄, c ∈ constraints → ∀ i : Fin c.arity, c.scope i ∈ vars

namespace CSPInstance

variable {L : FirstOrder.Language} {V W : Type*}

/-- The empty CSP instance on ambient variable carrier `V`. -/
def empty (L : FirstOrder.Language) (V : Type*) : CSPInstance L V where
  vars := ∅
  constraints := ∅
  finite_vars := Set.finite_empty
  finite_constraints := Set.finite_empty
  scope_mem _ hc := False.elim hc

instance : Inhabited (CSPInstance L V) :=
  ⟨empty L V⟩

/-- A mapping `f : I.vars → A` is a solution of `I` in `A` if every constraint `(σ, R)` of `I`
satisfies `f(σ) ∈ R^A`. -/
@[expose]
def IsSolution (A : Type*) [L.Structure A] (I : CSPInstance L V) (f : I.vars → A) : Prop :=
  ∀ ⦃c : CSPConstraint L V⦄ (hc : c ∈ I.constraints),
    Structure.RelMap c.rel (fun i ↦ f ⟨c.scope i, I.scope_mem hc i⟩)

/-- A total map `f : V → A` satisfies all constraints of `I` on `V`. -/
@[expose]
def IsTotalSolution (A : Type*) [L.Structure A] (I : CSPInstance L V) (f : V → A) : Prop :=
  ∀ ⦃c : CSPConstraint L V⦄, c ∈ I.constraints → Structure.RelMap c.rel (f ∘ c.scope)

/-- Restricting a total solution `f : V → A` to `I.vars` gives a solution of `I`. -/
theorem IsTotalSolution.toIsSolution {A : Type*} [L.Structure A] {I : CSPInstance L V}
    {f : V → A} (hf : I.IsTotalSolution A f) :
    I.IsSolution A (fun v ↦ f v.1) :=
  fun _ hc ↦ hf hc

/-- Extending a partial assignment `f : I.vars → A` by a default element `a₀ : A` outside
`I.vars` produces a total map `V → A`. -/
noncomputable def IsSolution.extend {A : Type*} {I : CSPInstance L V}
    (f : I.vars → A) (a₀ : A) : V → A := by
  classical
  exact fun v ↦ if hv : v ∈ I.vars then f ⟨v, hv⟩ else a₀

@[simp]
theorem IsSolution.extend_apply_mem {A : Type*} {I : CSPInstance L V}
    (f : I.vars → A) (a₀ : A) {v : V} (hv : v ∈ I.vars) :
    IsSolution.extend f a₀ v = f ⟨v, hv⟩ := by
  simp [IsSolution.extend, hv]

theorem IsSolution.isTotalSolution_extend {A : Type*} [L.Structure A] {I : CSPInstance L V}
    {f : I.vars → A} (hf : I.IsSolution A f) (a₀ : A) :
    I.IsTotalSolution A (IsSolution.extend f a₀) := by
  intro c hc
  convert hf hc using 1
  ext i
  exact IsSolution.extend_apply_mem f a₀ (I.scope_mem hc i)

/-- An instance `I` is satisfiable in `A` if it admits at least one solution `f : I.vars → A`. -/
@[expose]
def Satisfiable (A : Type*) [L.Structure A] (I : CSPInstance L V) : Prop :=
  ∃ f : I.vars → A, I.IsSolution A f

/-- Over a nonempty structure `A`, satisfiability is equivalent to existence of a total map
`f : V → A` satisfying every constraint of `I`. -/
theorem satisfiable_iff_exists_total (A : Type*) [L.Structure A] [Nonempty A]
    (I : CSPInstance L V) :
    I.Satisfiable A ↔ ∃ f : V → A, I.IsTotalSolution A f := by
  refine ⟨?_, fun ⟨f, hf⟩ ↦ ⟨fun v ↦ f v.1, hf.toIsSolution⟩⟩
  rintro ⟨f, hf⟩
  exact ⟨IsSolution.extend f (Classical.arbitrary A), hf.isTotalSolution_extend _⟩

/-- Every instance with empty variable set and empty constraint set is satisfiable (even in an
empty domain). -/
theorem satisfiable_of_vars_eq_empty (A : Type*) [L.Structure A] {I : CSPInstance L V}
    (hv : I.vars = ∅) (hc : I.constraints = ∅) :
    I.Satisfiable A := by
  refine ⟨fun v ↦ False.elim (by simpa [hv] using v.2), fun c hmem ↦ ?_⟩
  simp [hc] at hmem

/-- Over `[IsFinitePosRelational L]`, every unsatisfiable instance has a nonempty variable set. -/
theorem vars_nonempty_of_not_satisfiable [IsFinitePosRelational L] {A : Type*} [L.Structure A]
    {I : CSPInstance L V} (hunsat : ¬ I.Satisfiable A) :
    I.vars.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hv
  apply hunsat
  apply satisfiable_of_vars_eq_empty A hv
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hc
  have hpos := IsFinitePosRelational.arity_pos c.rel
  have hmem := I.scope_mem hc ⟨0, hpos⟩
  simp [hv] at hmem

/-- `J` is a subinstance of `I` when `J.vars ⊆ I.vars` and `J.constraints ⊆ I.constraints`. -/
@[expose]
def IsSubinstance (J I : CSPInstance L V) : Prop :=
  J.vars ⊆ I.vars ∧ J.constraints ⊆ I.constraints

/-- The subinstance `I ↾ U` of `I` induced by a subset `U : Set V`, retaining variables in
`I.vars ∩ U` and all constraints of `I` whose entire scope lies in `U`. -/
def induce (I : CSPInstance L V) (U : Set V) : CSPInstance L V where
  vars := I.vars ∩ U
  constraints := {c ∈ I.constraints | ∀ i, c.scope i ∈ U}
  finite_vars := I.finite_vars.subset Set.inter_subset_left
  finite_constraints := I.finite_constraints.subset fun _ h ↦ h.1
  scope_mem _ hc i := ⟨I.scope_mem hc.1 i, hc.2 i⟩

/-- Variable set of an induced subinstance `I.induce U`. -/
@[simp]
theorem induce_vars (I : CSPInstance L V) (U : Set V) : (I.induce U).vars = I.vars ∩ U := by
  rw [induce]

/-- Constraint set of an induced subinstance `I.induce U`. -/
@[simp]
theorem induce_constraints (I : CSPInstance L V) (U : Set V) :
    (I.induce U).constraints = {c ∈ I.constraints | ∀ i, c.scope i ∈ U} := by
  rw [induce]

/-- Every induced subinstance `I.induce U` is a subinstance of `I`. -/
theorem induce_isSubinstance (I : CSPInstance L V) (U : Set V) :
    (I.induce U).IsSubinstance I :=
  ⟨by rw [induce_vars]; exact Set.inter_subset_left,
    by rw [induce_constraints]; exact fun _ h ↦ h.1⟩

/-- Extend the variable set of an instance `I` to a larger finite set `U ⊇ I.vars` while keeping
the same constraints. -/
def extendVars (I : CSPInstance L V) {U : Set V} (hU : U.Finite) (hsub : I.vars ⊆ U) :
    CSPInstance L V where
  vars := U
  constraints := I.constraints
  finite_vars := hU
  finite_constraints := I.finite_constraints
  scope_mem _ hc i := hsub (I.scope_mem hc i)

/-- Variable set of `I.extendVars hU hsub`. -/
@[simp]
theorem extendVars_vars (I : CSPInstance L V) {U : Set V} (hU : U.Finite) (hsub : I.vars ⊆ U) :
    (I.extendVars hU hsub).vars = U := by
  rw [extendVars]

/-- Constraint set of `I.extendVars hU hsub`. -/
@[simp]
theorem extendVars_constraints (I : CSPInstance L V) {U : Set V} (hU : U.Finite)
    (hsub : I.vars ⊆ U) :
    (I.extendVars hU hsub).constraints = I.constraints := by
  rw [extendVars]

/-- Extending the variable set yields a superinstance of `I`. -/
theorem isSubinstance_extendVars (I : CSPInstance L V) {U : Set V} (hU : U.Finite)
    (hsub : I.vars ⊆ U) :
    I.IsSubinstance (I.extendVars hU hsub) :=
  ⟨by simpa using hsub, by simp⟩

/-- Image of a CSP instance `J` along a variable-identification map `h : V → W`. -/
def map (h : V → W) (J : CSPInstance L V) : CSPInstance L W where
  vars := h '' J.vars
  constraints := CSPConstraint.map h '' J.constraints
  finite_vars := J.finite_vars.image h
  finite_constraints := J.finite_constraints.image _
  scope_mem := by
    rintro _ ⟨c, hc, rfl⟩ i
    exact ⟨c.scope i, J.scope_mem hc i, rfl⟩

/-- Variable set of a mapped instance `J.map h`. -/
@[simp]
theorem map_vars (h : V → W) (J : CSPInstance L V) : (J.map h).vars = h '' J.vars := by
  rw [map]

/-- Constraint set of a mapped instance `J.map h`. -/
@[simp]
theorem map_constraints (h : V → W) (J : CSPInstance L V) :
    (J.map h).constraints = CSPConstraint.map h '' J.constraints := by
  rw [map]

/-- Restricting a solution of `I` along a subinstance `J` yields a solution of `J`. -/
theorem Satisfiable.of_isSubinstance {A : Type*} [L.Structure A] {J I : CSPInstance L V}
    (hsub : J.IsSubinstance I) (hI : I.Satisfiable A) :
    J.Satisfiable A := by
  rcases hI with ⟨f, hf⟩
  exact ⟨fun v ↦ f ⟨v.1, hsub.1 v.2⟩, fun c hc ↦ hf (hsub.2 hc)⟩

/-- Pulling back a solution of `I` along a variable-identifying map `h : V → W` with
`(J.map h).IsSubinstance I` yields a solution of `J`. -/
theorem Satisfiable.of_map_isSubinstance {A : Type*} [L.Structure A]
    {J : CSPInstance L V} {I : CSPInstance L W} {h : V → W}
    (hsub : (J.map h).IsSubinstance I) (hI : I.Satisfiable A) :
    J.Satisfiable A := by
  rcases hI with ⟨f, hf⟩
  refine ⟨fun v ↦ f ⟨h v.1, hsub.1 (by rw [map_vars]; exact ⟨v.1, v.2, rfl⟩)⟩, fun c hc ↦ ?_⟩
  exact hf (hsub.2 (by rw [map_constraints]; exact ⟨c, hc, rfl⟩))

/-- Relabeling an instance along a bijection on `vars` preserves satisfiability. -/
theorem satisfiable_map_iff_of_injOn {A : Type*} [L.Structure A]
    {J : CSPInstance L V} {h : V → W} (hinj : Set.InjOn h J.vars) :
    (J.map h).Satisfiable A ↔ J.Satisfiable A := by
  classical
  refine ⟨Satisfiable.of_map_isSubinstance ⟨Set.Subset.rfl, Set.Subset.rfl⟩, ?_⟩
  rintro ⟨f, hf⟩
  have hmem : ∀ w : (J.map h).vars, ∃ v ∈ J.vars, h v = w.1 := fun w ↦ by
    have hw : w.1 ∈ h '' J.vars := map_vars h J ▸ w.2
    exact hw
  choose pre hpre_mem hpre_eq using hmem
  refine ⟨fun w ↦ f ⟨pre w, hpre_mem w⟩, fun c' hc' ↦ ?_⟩
  rw [map_constraints] at hc'
  rcases hc' with ⟨c, hc, rfl⟩
  have harg : (fun i ↦ f ⟨pre ⟨h (c.scope i),
        by rw [map_vars]; exact ⟨c.scope i, J.scope_mem hc i, rfl⟩⟩,
      hpre_mem _⟩) = fun i ↦ f ⟨c.scope i, J.scope_mem hc i⟩ := by
    ext i
    congr 1
    apply Subtype.ext
    exact hinj (hpre_mem _) (J.scope_mem hc i) (hpre_eq _)
  exact harg.symm ▸ hf hc

/-- Every finite CSP instance `I` on any variable type `V` is isomorphic to an instance on
`Fin n` for `n = I.vars.ncard`. -/
theorem exists_fin_iso (I : CSPInstance L V) :
    ∃ (n : ℕ) (I₀ : CSPInstance L (Fin n)) (g : Fin n → V),
      I₀.vars = Set.univ ∧ Function.Injective g ∧ I₀.map g = I := by
  classical
  let _ : Fintype I.vars := I.finite_vars.fintype
  let e : Fin (Fintype.card I.vars) ≃ I.vars := (Fintype.equivFin I.vars).symm
  let g : Fin (Fintype.card I.vars) → V := fun i ↦ (e i).1
  have hginj : Function.Injective g := fun i j h ↦ e.injective (Subtype.ext h)
  let pullConstraint : (c : CSPConstraint L V) → c ∈ I.constraints →
      CSPConstraint L (Fin (Fintype.card I.vars)) :=
    fun c hc ↦ ⟨c.arity, c.rel, fun i ↦ e.symm ⟨c.scope i, I.scope_mem hc i⟩⟩
  let _ : Fintype I.constraints := I.finite_constraints.fintype
  let C₀ : Set (CSPConstraint L (Fin (Fintype.card I.vars))) :=
    Set.range fun x : I.constraints ↦ pullConstraint x.1 x.2
  let I₀ : CSPInstance L (Fin (Fintype.card I.vars)) :=
    { vars := Set.univ
      constraints := C₀
      finite_vars := Set.finite_univ
      finite_constraints := by
        simpa only [C₀, Set.image_univ] using
          (Set.finite_univ.image fun x : I.constraints ↦ pullConstraint x.1 x.2)
      scope_mem := fun _ _ _ ↦ trivial }
  refine ⟨Fintype.card I.vars, I₀, g, rfl, hginj, ?_⟩
  ext v
  · rw [map_vars]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact (e i).2
    · intro hv
      exact ⟨e.symm ⟨v, hv⟩, trivial, by simp [g]⟩
  · rw [map_constraints]
    constructor
    · rintro ⟨_, ⟨⟨c, hc⟩, rfl⟩, rfl⟩
      have heq : (pullConstraint c hc).map g = c := by
        cases c
        simp only [pullConstraint, CSPConstraint.map, Function.comp_def, g, Equiv.apply_symm_apply]
      rwa [heq]
    · intro hc
      refine ⟨pullConstraint v hc, ⟨⟨v, hc⟩, rfl⟩, ?_⟩
      cases v
      simp only [pullConstraint, CSPConstraint.map, Function.comp_def, g, Equiv.apply_symm_apply]

/-- A CSP instance `I = (V, C)` has pathwidth at most `k` if `I.vars` can be covered by finitely
many finite sets `U₀, …, U_{m-1}` of cardinality at most `k + 1` satisfying the running
intersection property on `I.vars` and covering the scope of every constraint in `I.constraints`. -/
@[expose]
def HasPathwidthAtMost (I : CSPInstance L V) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (U : Fin m → Set V),
    I.vars ⊆ ⋃ i, U i ∧
    (∀ i, (U i).Finite ∧ (U i).ncard ≤ k + 1) ∧
    (∀ ⦃i l j : Fin m⦄, i < l → l < j → ∀ ⦃v : V⦄, v ∈ I.vars → v ∈ U i → v ∈ U j → v ∈ U l) ∧
    (∀ ⦃c : CSPConstraint L V⦄, c ∈ I.constraints → ∃ i, Set.range c.scope ⊆ U i)

/-- Pathwidth at most `k` is monotone in `k`. -/
theorem HasPathwidthAtMost.mono {I : CSPInstance L V} {k k' : ℕ}
    (h : I.HasPathwidthAtMost k) (hle : k ≤ k') :
    I.HasPathwidthAtMost k' := by
  rcases h with ⟨m, U, hcov, hcard, hrun, hsc⟩
  exact ⟨m, U, hcov, fun i ↦ ⟨(hcard i).1, (hcard i).2.trans (by omega)⟩, hrun, hsc⟩

/-- Restricting the bags of a path decomposition of `I` to `I.vars` preserves pathwidth at most
`k` and ensures `U i ⊆ I.vars` for every bag `U i`. -/
theorem HasPathwidthAtMost.exists_subset_vars {I : CSPInstance L V} {k : ℕ}
    (h : I.HasPathwidthAtMost k) :
    ∃ (m : ℕ) (U : Fin m → Set V),
      (∀ i, U i ⊆ I.vars) ∧
      (⋃ i, U i) = I.vars ∧
      (∀ i, (U i).Finite ∧ (U i).ncard ≤ k + 1) ∧
      (∀ ⦃i l j : Fin m⦄, i ≤ l → l ≤ j → U i ∩ U j ⊆ U l) ∧
      (∀ ⦃c : CSPConstraint L V⦄, c ∈ I.constraints → ∃ i, Set.range c.scope ⊆ U i) := by
  rcases h with ⟨m, U, hcov, hcard, hrun, hsc⟩
  refine ⟨m, fun i ↦ I.vars ∩ U i, fun _ ↦ Set.inter_subset_left, ?_, ?_, ?_, ?_⟩
  · ext v
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    refine ⟨fun ⟨_, hv, _⟩ ↦ hv, fun hv ↦ ?_⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hv)
    exact ⟨i, hv, hi⟩
  · intro i
    have hfin : (I.vars ∩ U i).Finite := I.finite_vars.subset Set.inter_subset_left
    exact ⟨hfin, (Set.ncard_le_ncard Set.inter_subset_right (hcard i).1).trans (hcard i).2⟩
  · intro i l j hil hlj v ⟨hvi, hvj⟩
    rcases eq_or_lt_of_le hil with rfl | hil'
    · exact hvi
    · rcases eq_or_lt_of_le hlj with rfl | hlj'
      · exact hvj
      · exact ⟨hvi.1, hrun hil' hlj' hvi.1 hvi.2 hvj.2⟩
  · intro c hc
    obtain ⟨i, hi⟩ := hsc hc
    refine ⟨i, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact ⟨I.scope_mem hc r, hi ⟨r, rfl⟩⟩

/-- Pathwidth at most `k` is preserved along injective relabelings. -/
theorem HasPathwidthAtMost.map_of_injOn {I : CSPInstance L V} {k : ℕ}
    (h : I.HasPathwidthAtMost k) {g : V → W} (hg : Set.InjOn g I.vars) :
    (I.map g).HasPathwidthAtMost k := by
  obtain ⟨m, U, hsub, hcov, hcard, hrun, hsc⟩ := h.exists_subset_vars
  refine ⟨m, fun i ↦ g '' U i, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [← hcov] at hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    exact Set.mem_iUnion.mpr ⟨i, v, hi, rfl⟩
  · intro i
    refine ⟨(hcard i).1.image g, (Set.ncard_image_le (hcard i).1).trans (hcard i).2⟩
  · rintro i l j hil hlj _ ⟨v, hv, rfl⟩ ⟨v₁, hv₁, he₁⟩ ⟨v₂, hv₂, he₂⟩
    have hv₁' : v ∈ U i := hg (hsub i hv₁) hv he₁ ▸ hv₁
    have hv₂' : v ∈ U j := hg (hsub j hv₂) hv he₂ ▸ hv₂
    exact ⟨v, hrun (le_of_lt hil) (le_of_lt hlj) ⟨hv₁', hv₂'⟩, rfl⟩
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨i, hi⟩ := hsc hc
    refine ⟨i, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact ⟨c.scope r, hi ⟨r, rfl⟩, rfl⟩

/-- **Pigeonhole Cloud Blowup**: for any unsatisfiable instance `I` over a finite nonempty
`L`-structure `A` with `[IsFinitePosRelational L]`, there exist a finite unsatisfiable instance
`Ĩ` and a variable projection `π` such that `(Ĩ.map π).IsSubinstance I` and every constraint of
`Ĩ` has an injective scope (no repeated variables). -/
theorem exists_injective_scope_cover [IsFinitePosRelational L] {A : Type*} [L.Structure A]
    [Finite A] [Nonempty A] {I : CSPInstance L V} (hunsat : ¬ I.Satisfiable A) :
    ∃ (N : ℕ) (Itilde : CSPInstance L (Fin N)) (π : Fin N → V),
      ¬ Itilde.Satisfiable A ∧
      (Itilde.map π).IsSubinstance I ∧
      ∀ c ∈ Itilde.constraints, Function.Injective c.scope := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  obtain ⟨M, hM⟩ := IsFinitePosRelational.exists_max_arity L
  -- Replace each variable `v ∈ I.vars` by a cloud `Fin K` of size `M * |A| + 1`.
  let K : ℕ := M * Fintype.card A + 1
  let W₀ := I.vars × Fin K
  let _ : Fintype I.vars := I.finite_vars.fintype
  let _ : Fintype W₀ := inferInstance
  let π₀ : W₀ → V := fun p ↦ p.1.1
  let C₀ : Set (CSPConstraint L W₀) :=
    {d | Function.Injective d.scope ∧ d.map π₀ ∈ I.constraints}
  have hC₀_fin : C₀.Finite := by
    have := IsFinitePosRelational.finite_sigma_relations (L := L)
    have hfin_sig : Finite (Σ n : ℕ, L.Relations n × (Fin n → W₀)) := by
      let _ : Fintype (Σ n : ℕ, L.Relations n) := Fintype.ofFinite _
      exact Finite.of_equiv (Σ s : (Σ n : ℕ, L.Relations n), Fin s.1 → W₀)
        { toFun := fun ⟨⟨n, R⟩, sc⟩ ↦ ⟨n, R, sc⟩
          invFun := fun ⟨n, R, sc⟩ ↦ ⟨⟨n, R⟩, sc⟩
          left_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl
          right_inv := fun ⟨_, _, _⟩ ↦ rfl }
    have : Finite (CSPConstraint L W₀) :=
      Finite.of_equiv _ (CSPConstraint.equivSigma L W₀).symm
    exact Set.toFinite C₀
  let J₀ : CSPInstance L W₀ :=
    { vars := Set.univ
      constraints := C₀
      finite_vars := Set.finite_univ
      finite_constraints := hC₀_fin
      scope_mem := fun _ _ _ ↦ trivial }
  have hJ₀_sub : (J₀.map π₀).IsSubinstance I := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨p, _, rfl⟩
      exact p.1.2
    · rintro _ ⟨d, hd, rfl⟩
      exact hd.2
  have hJ₀_unsat : ¬ J₀.Satisfiable A := by
    intro hsat
    rw [satisfiable_iff_exists_total] at hsat
    rcases hsat with ⟨g, hg⟩
    -- By pigeonhole, for each `v ∈ I.vars` some color `f v ∈ A` occurs `> M` times in `v`'s cloud.
    have hpig : ∀ v : I.vars, ∃ a : A,
        M < ((Finset.univ : Finset (Fin K)).filter fun t ↦ g (v, t) = a).card := by
      intro v
      have hlt : Fintype.card A * M < (Finset.univ : Finset (Fin K)).card := by
        simp only [Finset.card_univ, Fintype.card_fin, K, Nat.mul_comm (Fintype.card A) M]
        omega
      obtain ⟨a, _, ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := fun t : Fin K ↦ g (v, t)) (s := Finset.univ) (t := Finset.univ)
        (fun _ _ ↦ Finset.mem_univ _) hlt
      exact ⟨a, ha⟩
    choose f hf using hpig
    apply hunsat
    refine ⟨f, fun c hc ↦ ?_⟩
    have hle : c.arity ≤ M := hM c.rel
    -- Choose distinct cloud indices `idx i : Fin K` with `g (c.scope i, idx i) = f (c.scope i)`.
    have hpick : ∀ i : Fin c.arity,
        ∃ emb : Fin (i.1 + 1) ↪ Fin K,
          ∀ j : Fin (i.1 + 1),
            g (⟨c.scope ⟨j.1, by omega⟩, I.scope_mem hc ⟨j.1, by omega⟩⟩, emb j) =
              f ⟨c.scope ⟨j.1, by omega⟩, I.scope_mem hc ⟨j.1, by omega⟩⟩ := by
      intro ⟨i, hi⟩
      induction i with
      | zero =>
        let v₀ : I.vars := ⟨c.scope ⟨0, hi⟩, I.scope_mem hc ⟨0, hi⟩⟩
        have hpos : 0 < (Finset.univ.filter fun t : Fin K ↦ g (v₀, t) = f v₀).card :=
          Nat.lt_of_le_of_lt (Nat.zero_le M) (hf v₀)
        obtain ⟨t₀, ht₀⟩ := Finset.card_pos.mp hpos
        refine ⟨⟨fun _ ↦ t₀, fun a b _ ↦ Fin.ext (by
          have ha : a.1 < 1 := a.2
          have hb : b.1 < 1 := b.2
          omega)⟩, fun j ↦ ?_⟩
        have hjlt : j.1 < 1 := j.2
        have hj0 : j = 0 := Fin.ext (by change j.1 = 0; omega)
        subst hj0
        exact (Finset.mem_filter.mp ht₀).2
      | succ i ih =>
        obtain ⟨emb₀, hemb₀⟩ := ih (by omega)
        let vi : I.vars := ⟨c.scope ⟨i + 1, hi⟩, I.scope_mem hc ⟨i + 1, hi⟩⟩
        let fib := Finset.univ.filter fun t : Fin K ↦ g (vi, t) = f vi
        let used := (Finset.univ : Finset (Fin (i + 1))).map emb₀
        have hcard_lt : used.card < fib.card := by
          rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
          exact lt_of_le_of_lt (by omega : i + 1 ≤ M) (hf vi)
        obtain ⟨t_new, htfib, htnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
        let fn : Fin (i + 2) → Fin K := Fin.lastCases t_new emb₀
        have hfn_inj : Function.Injective fn := by
          intro a b hab
          cases a using Fin.lastCases <;> cases b using Fin.lastCases
          · rfl
          · rename_i b'
            have heq : t_new = emb₀ b' := by
              simpa only [fn, Fin.lastCases_last, Fin.lastCases_castSucc] using hab
            exact False.elim (htnot (heq ▸ Finset.mem_map_of_mem emb₀ (Finset.mem_univ b')))
          · rename_i a'
            have heq : emb₀ a' = t_new := by
              simpa only [fn, Fin.lastCases_last, Fin.lastCases_castSucc] using hab
            exact False.elim (htnot (heq ▸ Finset.mem_map_of_mem emb₀ (Finset.mem_univ a')))
          · rename_i a' b'
            have heq : emb₀ a' = emb₀ b' := by
              simpa only [fn, Fin.lastCases_castSucc] using hab
            exact congrArg Fin.castSucc (emb₀.injective heq)
        refine ⟨⟨fn, hfn_inj⟩, fun j ↦ ?_⟩
        cases j using Fin.lastCases with
        | last =>
          change g (vi, fn (Fin.last (i + 1))) = f vi
          have hfl : fn (Fin.last (i + 1)) = t_new := Fin.lastCases_last
          rw [hfl]
          exact (Finset.mem_filter.mp htfib).2
        | cast j' =>
          change g (⟨c.scope ⟨j'.1, by omega⟩, I.scope_mem hc ⟨j'.1, by omega⟩⟩,
            fn j'.castSucc) = f ⟨c.scope ⟨j'.1, by omega⟩, I.scope_mem hc ⟨j'.1, by omega⟩⟩
          have hfc : fn j'.castSucc = emb₀ j' := Fin.lastCases_castSucc j'
          rw [hfc]
          exact hemb₀ j'
    by_cases hca : c.arity = 0
    · exact False.elim (Nat.ne_of_gt (IsFinitePosRelational.arity_pos c.rel) hca)
    · obtain ⟨emb, hemb⟩ := hpick ⟨c.arity - 1, by omega⟩
      have hidx_lt : ∀ i : Fin c.arity, i.1 < (⟨c.arity - 1, by omega⟩ : Fin c.arity).1 + 1 := by
        intro i
        have hi := i.2
        change i.1 < c.arity - 1 + 1
        omega
      let sc : Fin c.arity → W₀ := fun i ↦
        (⟨c.scope i, I.scope_mem hc i⟩, emb ⟨i.1, hidx_lt i⟩)
      have hsc_inj : Function.Injective sc := by
        intro i j hij
        have he : (⟨i.1, hidx_lt i⟩ : Fin _) = ⟨j.1, hidx_lt j⟩ :=
          emb.injective (Prod.mk.inj hij).2
        exact Fin.ext (by simpa using congrArg Fin.val he)
      let d : CSPConstraint L W₀ := ⟨c.arity, c.rel, sc⟩
      have hd_map : d.map π₀ = c := by
        cases c
        rfl
      have hd : d ∈ C₀ := ⟨hsc_inj, hd_map.symm ▸ hc⟩
      have hrel := hg hd
      have harg : (fun i ↦ f ⟨c.scope i, I.scope_mem hc i⟩) = g ∘ sc := by
        ext i
        exact (hemb ⟨i.1, hidx_lt i⟩).symm
      exact harg.symm ▸ hrel
  obtain ⟨N, Itilde, e, _, heinj, hmap⟩ := J₀.exists_fin_iso
  refine ⟨N, Itilde, π₀ ∘ e, ?_, ?_, ?_⟩
  · rwa [← satisfiable_map_iff_of_injOn (heinj.injOn), hmap]
  · have hcomp : Itilde.map (π₀ ∘ e) = (Itilde.map e).map π₀ := by
      ext x
      · simp [Set.image_image]
      · simp [Set.image_image, CSPConstraint.map_comp]
    rwa [hcomp, hmap]
  · intro c hc i j hij
    have hcmem : c.map e ∈ J₀.constraints := by
      rw [← hmap, map_constraints]
      exact ⟨c, hc, rfl⟩
    exact hcmem.1 (congrArg e hij)

end CSPInstance

/-- A relational structure `A` has pathwidth duality at most `k` if every unsatisfiable instance
`I` of `CSP(A)` receives a constraint-preserving variable-identification map from some finite
unsatisfiable instance `J` of pathwidth at most `k`. -/
@[expose]
def HasPathwidthDualityAtMost (L : FirstOrder.Language) (A : Type*) [L.Structure A]
    (k : ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄ (I : CSPInstance L (Fin n)), ¬ I.Satisfiable A →
    ∃ (m : ℕ) (J : CSPInstance L (Fin m)) (h : Fin m → Fin n),
      ¬ J.Satisfiable A ∧ J.HasPathwidthAtMost k ∧ (J.map h).IsSubinstance I

/-- Universe-polymorphic elimination for `HasPathwidthDualityAtMost`: applies to any unsatisfiable
CSP instance `I` on an arbitrary variable carrier `V : Type*`. -/
theorem HasPathwidthDualityAtMost.exists_obstruction {L : FirstOrder.Language} {A : Type*}
    [L.Structure A] {k : ℕ} (hdual : HasPathwidthDualityAtMost L A k)
    {V : Type*} (I : CSPInstance L V) (hI : ¬ I.Satisfiable A) :
    ∃ (m : ℕ) (J : CSPInstance L (Fin m)) (h : Fin m → V),
      ¬ J.Satisfiable A ∧ J.HasPathwidthAtMost k ∧ (J.map h).IsSubinstance I := by
  obtain ⟨n, I₀, g, _, hginj, hmap⟩ := I.exists_fin_iso
  have hI₀ : ¬ I₀.Satisfiable A := by
    rw [← CSPInstance.satisfiable_map_iff_of_injOn hginj.injOn, hmap]
    exact hI
  obtain ⟨m, J, h, hJunsat, hJpw, hsub⟩ := hdual I₀ hI₀
  refine ⟨m, J, g ∘ h, hJunsat, hJpw, ?_⟩
  rw [← hmap]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨h v, hsub.1 ⟨v, hv, rfl⟩, rfl⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨c.map h, hsub.2 ⟨c, hc, rfl⟩, CSPConstraint.map_comp g h c⟩

/-- Introduction rule for `HasPathwidthDualityAtMost` allowing obstruction instances on any
variable type. -/
theorem HasPathwidthDualityAtMost.of_forall {L : FirstOrder.Language} {A : Type*} [L.Structure A]
    {k : ℕ}
    (H : ∀ ⦃n : ℕ⦄ (I : CSPInstance L (Fin n)), ¬ I.Satisfiable A →
      ∃ (W : Type*) (J : CSPInstance L W) (h : W → Fin n),
        ¬ J.Satisfiable A ∧ J.HasPathwidthAtMost k ∧ (J.map h).IsSubinstance I) :
    HasPathwidthDualityAtMost L A k := by
  intro n I hI
  obtain ⟨W, J, h, hJunsat, hJpw, hsub⟩ := H I hI
  obtain ⟨m, J₀, g, hJ₀vars, hginj, hmap⟩ := J.exists_fin_iso
  refine ⟨m, J₀, h ∘ g, ?_, ?_, ?_⟩
  · rwa [← CSPInstance.satisfiable_map_iff_of_injOn hginj.injOn, hmap]
  · -- Pull pathwidth back along the injective isomorphism `g : Fin m → W`.
    obtain ⟨b, U, hUsub, hUcov, hUcard, hUrun, hUsc⟩ := hJpw.exists_subset_vars
    refine ⟨b, fun i ↦ g ⁻¹' U i, ?_, ?_, ?_, ?_⟩
    · intro x _
      have hgx : g x ∈ J.vars := by
        rw [← hmap, CSPInstance.map_vars]
        exact ⟨x, hJ₀vars.symm ▸ Set.mem_univ x, rfl⟩
      rw [← hUcov] at hgx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hgx
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro i
      refine ⟨Set.toFinite _, ?_⟩
      have hsub_img : g '' (g ⁻¹' U i) ⊆ U i := Set.image_preimage_subset g (U i)
      rw [← Set.ncard_image_of_injective _ hginj]
      exact (Set.ncard_le_ncard hsub_img (hUcard i).1).trans (hUcard i).2
    · intro i l j hil hlj x _ hxi hxj
      exact hUrun (le_of_lt hil) (le_of_lt hlj) ⟨hxi, hxj⟩
    · intro c hc
      have hcm : c.map g ∈ J.constraints := by
        rw [← hmap]
        exact ⟨c, hc, rfl⟩
      obtain ⟨i, hi⟩ := hUsc hcm
      refine ⟨i, ?_⟩
      rintro _ ⟨r, rfl⟩
      exact hi ⟨r, rfl⟩
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply hsub.1
      refine ⟨g x, ?_, rfl⟩
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩
      apply hsub.2
      refine ⟨c.map g, ?_, CSPConstraint.map_comp h g c⟩
      rw [← hmap]
      exact ⟨c, hc, rfl⟩

/-- Monotonicity of `HasPathwidthDualityAtMost` in the width bound `k`. -/
theorem HasPathwidthDualityAtMost.mono {L : FirstOrder.Language} {A : Type*} [L.Structure A]
    {k k' : ℕ} (h : HasPathwidthDualityAtMost L A k) (hle : k ≤ k') :
    HasPathwidthDualityAtMost L A k' :=
  fun _ I hI ↦
    let ⟨m, J, g, hJ, hpw, hsub⟩ := h I hI
    ⟨m, J, g, hJ, hpw.mono hle, hsub⟩

/-- A relational structure `A` has bounded pathwidth duality if it has pathwidth duality at most
`k` for some `k : ℕ`. -/
@[expose]
def HasBoundedPathwidthDuality (L : FirstOrder.Language) (A : Type*) [L.Structure A] : Prop :=
  ∃ k : ℕ, HasPathwidthDualityAtMost L A k

end CSP

end CslibFrontier.Logics
