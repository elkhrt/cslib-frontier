/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.ConstraintSatisfaction
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma

/-!
# Datalog, Linear Datalog, and Symmetric Datalog for Constraint Satisfaction

This module formalizes finite Datalog programs for deciding Constraint Satisfaction Problems
`CSP(A)` over finite positive-arity relational signatures, their linear and symmetric fragments
, the computation digraph of a linear/symmetric
derivation, and the `r`-ary maximal symmetric and canonical linear Datalog programs consistent with
a finite structure `A`, together with their symmetry, consistency soundness, semantic rule
introduction lemmas, and width monotonicity, proved under standard Lean axioms.

## Main definitions

* `CslibFrontier.Logics.DatalogAtom`, `CslibFrontier.Logics.DatalogRule`,
  `CslibFrontier.Logics.DatalogProgram`: Datalog rules and finite programs over a relational
  language `L`.
* `CslibFrontier.Logics.DatalogProgram.IsLinear`,
  `CslibFrontier.Logics.DatalogProgram.IsSymmetric`,
  `CslibFrontier.Logics.DatalogProgram.Derives`,
  `CslibFrontier.Logics.DatalogProgram.Decides`: linear and symmetric fragments, derivation
  semantics, and CSP decision.
* `CslibFrontier.Logics.maximalSymProgram`,
  `CslibFrontier.Logics.canonicalLinearProgram`,
  `CslibFrontier.Logics.MaxSymDerives`,
  `CslibFrontier.Logics.MaxSymDerivesGoal`: the `r`-ary maximal symmetric Datalog program
  `P_A^r` and canonical linear Datalog program `L_A^r`.

## Main results

* `CslibFrontier.Logics.DatalogProgram.DerivationStep.symm`: symmetry of the one-step
  derivation relation of a symmetric Datalog program.
* `CslibFrontier.Logics.DatalogProgram.IsLinear.derives_iff_chain`: linear derivations are
  equivalent to directed paths from `0`-IDB initializations in the computation digraph.
* `CslibFrontier.Logics.maximalSymProgram_isSymmetric`,
  `CslibFrontier.Logics.maximalSymProgram_sound`,
  `CslibFrontier.Logics.maximalSymProgram_unsatisfiable_of_derivesGoal`: symmetry and
  consistency soundness of `maximalSymProgram`.
* `CslibFrontier.Logics.MaxSymDerives.of_init`,
  `CslibFrontier.Logics.MaxSymDerives.of_symm_step`,
  `CslibFrontier.Logics.MaxSymDerives.mono`: semantic derivation rules and width
  monotonicity.

## Tags

Datalog, linear Datalog, symmetric Datalog, constraint satisfaction, finite model theory
-/

public section

namespace CslibFrontier.Logics

open FirstOrder FirstOrder.Language

section Datalog

/-- An atom in the body of a Datalog rule over language `L`, intensional predicate type `IDB` with
arity function `idbArity`, and rule-variable type `Var`: either an intensional predicate atom
`idb R σ` or an extensional (basic-relation) atom `edb n T τ`. -/
inductive DatalogAtom (L : FirstOrder.Language) {IDB : Type*} (idbArity : IDB → ℕ) (Var : Type*)
  /-- An intensional database (IDB) atom `S(σ)`. -/
  | idb (pred : IDB) (scope : Fin (idbArity pred) → Var)
  /-- An extensional database (EDB) atom `T(τ)` for a basic relation `T` of `L`. -/
  | edb (arity : ℕ) (rel : L.Relations arity) (scope : Fin arity → Var)

/-- Predicate identifying IDB atoms in a rule body. -/
def DatalogAtom.isIdb {L : FirstOrder.Language} {IDB : Type*} {idbArity : IDB → ℕ} {Var : Type*} :
    DatalogAtom L idbArity Var → Bool
  | .idb _ _ => true
  | .edb _ _ _ => false

/-- An extensional atom `(n, T, τ)` over rule-variable type `Var`. -/
structure EDBAtom (L : FirstOrder.Language) (Var : Type*) where
  /-- Arity of the basic relation symbol. -/
  arity : ℕ
  /-- Basic relation symbol of `L`. -/
  rel : L.Relations arity
  /-- Variable scope in `Var`. -/
  scope : Fin arity → Var

/-- Convert an `EDBAtom` into a `DatalogAtom`. -/
@[expose]
def EDBAtom.toAtom {L : FirstOrder.Language} {IDB : Type*} {idbArity : IDB → ℕ} {Var : Type*}
    (e : EDBAtom L Var) : DatalogAtom L idbArity Var :=
  .edb e.arity e.rel e.scope

/-- A Datalog rule `R(τ) ← α₁, …, α_ℓ` with an IDB head predicate `head`, head variable tuple
`headScope`, and finite body list `body` of IDB and EDB atoms. -/
structure DatalogRule (L : FirstOrder.Language) {IDB : Type*} (idbArity : IDB → ℕ)
    (Var : Type*) where
  /-- Intensional predicate symbol on the left-hand side. -/
  head : IDB
  /-- Variable tuple of the head atom. -/
  headScope : Fin (idbArity head) → Var
  /-- List of body atoms on the right-hand side. -/
  body : List (DatalogAtom L idbArity Var)

/-- A rule is linear if at most one atom in its body is an IDB atom. -/
@[expose]
def DatalogRule.IsLinear {L : FirstOrder.Language} {IDB : Type*} {idbArity : IDB → ℕ}
    {Var : Type*} (r : DatalogRule L idbArity Var) : Prop :=
  (r.body.filter fun a ↦ a.isIdb = true).length ≤ 1

/-- Construct a `0`-IDB (initialization) rule `R(τ) ← T₁(σ₁), …, T_k(σ_k)`. -/
@[expose]
def DatalogRule.mkInit {L : FirstOrder.Language} {IDB : Type*} {idbArity : IDB → ℕ}
    {Var : Type*} (R : IDB) (τ : Fin (idbArity R) → Var) (edbs : List (EDBAtom L Var)) :
    DatalogRule L idbArity Var where
  head := R
  headScope := τ
  body := edbs.map EDBAtom.toAtom

/-- Construct a `1`-IDB linear rule `R(ρ) ← S(σ), T₁(τ₁), …, T_k(τ_k)`. -/
@[expose]
def DatalogRule.mkStep {L : FirstOrder.Language} {IDB : Type*} {idbArity : IDB → ℕ}
    {Var : Type*} (R : IDB) (ρ : Fin (idbArity R) → Var) (S : IDB)
    (σ : Fin (idbArity S) → Var) (edbs : List (EDBAtom L Var)) :
    DatalogRule L idbArity Var where
  head := R
  headScope := ρ
  body := .idb S σ :: edbs.map EDBAtom.toAtom

/-- A finite Datalog program `P` for solving `CSP(A)` over signature `L`, consisting of finitely
many positive-arity IDB predicates, a finite set `Var` of rule variables, a finite set `rules` of
Datalog rules over `Var`, and a designated subset `isGoal` of goal predicates. -/
structure DatalogProgram.{w, u₁, u₂} (L : FirstOrder.Language.{u₁, u₂}) where
  /-- Type of intensional database (IDB) predicate symbols. -/
  IDB : Type w
  /-- Type of variables appearing in the rules of the program. -/
  Var : Type
  /-- Finiteness of the set of IDB predicates. -/
  finite_idb : Finite IDB
  /-- Finiteness of the set of rule variables. -/
  finite_var : Finite Var
  /-- Positive arity assigned to each IDB predicate. -/
  idbArity : IDB → ℕ
  /-- Nullary IDB predicates are excluded. -/
  idbArity_pos : ∀ R : IDB, 0 < idbArity R
  /-- Finite set of rules of the program. -/
  rules : Set (DatalogRule L idbArity Var)
  /-- Finiteness of `rules`. -/
  finite_rules : rules.Finite
  /-- Designated goal predicates. -/
  isGoal : Set IDB

namespace DatalogProgram

variable {L : FirstOrder.Language}

/-- A Datalog program `P` is linear if every rule has at most one IDB atom in its body. -/
@[expose]
def IsLinear (P : DatalogProgram L) : Prop :=
  ∀ r ∈ P.rules, r.IsLinear

/-- Extract the list of EDB atoms from a rule body. -/
@[expose]
def bodyEdbs {IDB Var : Type*} {idbArity : IDB → ℕ} :
    List (DatalogAtom L idbArity Var) → List (EDBAtom L Var)
  | [] => []
  | .idb _ _ :: tl => bodyEdbs tl
  | .edb n T τ :: tl => ⟨n, T, τ⟩ :: bodyEdbs tl

/-- Extract the list of IDB atoms from a rule body. -/
@[expose]
def bodyIdbs {IDB Var : Type*} {idbArity : IDB → ℕ} :
    List (DatalogAtom L idbArity Var) → List ((S : IDB) × (Fin (idbArity S) → Var))
  | [] => []
  | .idb S σ :: tl => ⟨S, σ⟩ :: bodyIdbs tl
  | .edb _ _ _ :: tl => bodyIdbs tl

@[simp]
theorem length_bodyIdbs {IDB Var : Type*} {idbArity : IDB → ℕ} :
    ∀ l : List (DatalogAtom L idbArity Var),
      (bodyIdbs l).length = (l.filter fun a ↦ a.isIdb = true).length
  | [] => rfl
  | .idb _ _ :: tl => by simp [bodyIdbs, DatalogAtom.isIdb, length_bodyIdbs tl]
  | .edb _ _ _ :: tl => by simp [bodyIdbs, DatalogAtom.isIdb, length_bodyIdbs tl]

@[simp]
theorem bodyIdbs_map_toAtom {IDB Var : Type*} {idbArity : IDB → ℕ}
    (edbs : List (EDBAtom L Var)) :
    bodyIdbs (idbArity := idbArity) (edbs.map EDBAtom.toAtom) = [] := by
  induction edbs with
  | nil => rfl
  | cons e tl ih => exact ih

@[simp]
theorem bodyEdbs_map_toAtom {IDB Var : Type*} {idbArity : IDB → ℕ}
    (edbs : List (EDBAtom L Var)) :
    bodyEdbs (idbArity := idbArity) (edbs.map EDBAtom.toAtom) = edbs := by
  induction edbs with
  | nil => rfl
  | cons e tl ih =>
    cases e
    simp [bodyEdbs, EDBAtom.toAtom, ih]

theorem mem_body_iff {IDB Var : Type*} {idbArity : IDB → ℕ}
    (l : List (DatalogAtom L idbArity Var)) :
    (∀ S σ, DatalogAtom.idb S σ ∈ l ↔ (⟨S, σ⟩ : (T : IDB) × (Fin (idbArity T) →
      Var)) ∈ bodyIdbs l) ∧
    (∀ n T τ, DatalogAtom.edb n T τ ∈ l ↔ (⟨n, T, τ⟩ : EDBAtom L Var) ∈ bodyEdbs l) := by
  induction l with
  | nil => simp [bodyIdbs, bodyEdbs]
  | cons a tl ih =>
    cases a with
    | idb S₀ σ₀ =>
      refine ⟨fun S σ ↦ ?_, fun n T τ ↦ by simp [bodyEdbs, ih.2]⟩
      simp only [List.mem_cons, bodyIdbs, ih.1, Sigma.mk.inj_iff]
      constructor
      · rintro (h | h)
        · cases h; exact Or.inl ⟨rfl, HEq.rfl⟩
        · exact Or.inr h
      · rintro (⟨rfl, hσ⟩ | h)
        · cases eq_of_heq hσ; exact Or.inl rfl
        · exact Or.inr h
    | edb n₀ T₀ τ₀ =>
      refine ⟨fun S σ ↦ by simp [bodyIdbs, ih.1], fun n T τ ↦ ?_⟩
      simp only [List.mem_cons, bodyEdbs, ih.2]
      constructor
      · rintro (h | h)
        · cases h; exact Or.inl rfl
        · exact Or.inr h
      · rintro (h | h)
        · cases h; exact Or.inl rfl
        · exact Or.inr h

/-- A Datalog program `P` is symmetric if it is linear and for every rule `r ∈ P.rules` having a
unique IDB atom `S(σ)` in its body and EDB atoms `T₁(τ₁), …, T_k(τ_k)`, the program `P` also
contains a mirror rule `r' ∈ P.rules` with head `S(σ)`, unique body IDB atom `r.head(r.headScope)`,
and the same EDB atoms. -/
@[expose]
def IsSymmetric (P : DatalogProgram L) : Prop :=
  P.IsLinear ∧
    ∀ r ∈ P.rules, ∀ (S : P.IDB) (σ : Fin (P.idbArity S) → P.Var),
      bodyIdbs r.body = [⟨S, σ⟩] →
      ∃ r' ∈ P.rules,
        r'.head = S ∧
        HEq r'.headScope σ ∧
        bodyIdbs r'.body = [⟨r.head, r.headScope⟩] ∧
        ∀ e : EDBAtom L P.Var, e ∈ bodyEdbs r'.body ↔ e ∈ bodyEdbs r.body

/-- Every symmetric Datalog program is a linear Datalog program. -/
theorem IsSymmetric.isLinear {P : DatalogProgram L} (hP : P.IsSymmetric) : P.IsLinear :=
  hP.1

/-- Inductive derivation relation `P(I) ⊢ R(ρ)` for an IDB predicate `R : P.IDB` and variable
tuple `ρ : Fin (P.idbArity R) → V` when running Datalog program `P` on CSP instance `I`. -/
inductive Derives (P : DatalogProgram L) {V : Type*} (I : CSPInstance L V) :
    (R : P.IDB) → (Fin (P.idbArity R) → V) → Prop
  | step (r : DatalogRule L P.idbArity P.Var) (hr : r ∈ P.rules)
      (ω : P.Var → V) (hω : ∀ x, ω x ∈ I.vars)
      (hedb : ∀ ⦃n : ℕ⦄ (T : L.Relations n) (τ : Fin n → P.Var),
        DatalogAtom.edb n T τ ∈ r.body → (⟨n, T, ω ∘ τ⟩ : CSPConstraint L V) ∈ I.constraints)
      (hidb : ∀ (S : P.IDB) (σ : Fin (P.idbArity S) → P.Var),
        DatalogAtom.idb S σ ∈ r.body → Derives P I S (ω ∘ σ)) :
      Derives P I r.head (ω ∘ r.headScope)

/-- `P(I) ⊢ G`: running `P` on `I` derives at least one designated goal predicate. -/
@[expose]
def DerivesGoal (P : DatalogProgram L) {V : Type*} (I : CSPInstance L V) : Prop :=
  ∃ (R : P.IDB) (ρ : Fin (P.idbArity R) → V), R ∈ P.isGoal ∧ P.Derives I R ρ

/-- Every tuple derived by `P` on `I` takes values in `I.vars`. -/
theorem Derives.scope_mem {P : DatalogProgram L} {V : Type*} {I : CSPInstance L V}
    {R : P.IDB} {ρ : Fin (P.idbArity R) → V} (hd : P.Derives I R ρ) (i : Fin (P.idbArity R)) :
    ρ i ∈ I.vars := by
  cases hd with
  | step _ _ ω hω _ _ => exact hω _

/-- Derivations push forward along variable-identifying maps `(J.map h).IsSubinstance I`. -/
theorem Derives.map {P : DatalogProgram L} {V W : Type*} {J : CSPInstance L V}
    {I : CSPInstance L W} {h : V → W} (hsub : (J.map h).IsSubinstance I)
    {R : P.IDB} {ρ : Fin (P.idbArity R) → V} (hd : P.Derives J R ρ) :
    P.Derives I R (h ∘ ρ) := by
  induction hd with
  | step r hr ω hω hedb hidb ih =>
    exact Derives.step r hr (h ∘ ω)
      (fun x ↦ hsub.1 (by rw [CSPInstance.map_vars]; exact ⟨ω x, hω x, rfl⟩))
      (fun n T τ hmem ↦ hsub.2 (by
        rw [CSPInstance.map_constraints]
        exact ⟨⟨n, T, ω ∘ τ⟩, hedb T τ hmem, rfl⟩))
      (fun S σ hmem ↦ ih S σ hmem)

/-- Goal derivations push forward along variable-identifying maps `(J.map h).IsSubinstance I`. -/
theorem DerivesGoal.map {P : DatalogProgram L} {V W : Type*} {J : CSPInstance L V}
    {I : CSPInstance L W} {h : V → W} (hsub : (J.map h).IsSubinstance I)
    (hd : P.DerivesGoal J) : P.DerivesGoal I := by
  rcases hd with ⟨R, ρ, hgoal, hder⟩
  exact ⟨R, h ∘ ρ, hgoal, hder.map hsub⟩

/-- Derivations are monotone under subinstance inclusion `J.IsSubinstance I`. -/
theorem Derives.of_isSubinstance {P : DatalogProgram L} {V : Type*} {J I : CSPInstance L V}
    (hsub : J.IsSubinstance I) {R : P.IDB} {ρ : Fin (P.idbArity R) → V}
    (hd : P.Derives J R ρ) : P.Derives I R ρ := by
  have hmap : (J.map id).IsSubinstance I := by
    refine ⟨by simpa using hsub.1, ?_⟩
    rw [CSPInstance.map_constraints]
    rintro _ ⟨c, hc, rfl⟩
    exact hsub.2 hc
  exact hd.map hmap

/-- Goal derivations are monotone under subinstance inclusion `J.IsSubinstance I`. -/
theorem DerivesGoal.of_isSubinstance {P : DatalogProgram L} {V : Type*}
    {J I : CSPInstance L V} (hsub : J.IsSubinstance I) (hd : P.DerivesGoal J) :
    P.DerivesGoal I := by
  rcases hd with ⟨R, ρ, hg, hd⟩
  exact ⟨R, ρ, hg, hd.of_isSubinstance hsub⟩

/-- Goal derivations are invariant under injective variable relabelings. -/
theorem derivesGoal_map_iff_of_injOn {P : DatalogProgram L} {V W : Type*}
    {J : CSPInstance L V} {h : V → W} (hinj : Set.InjOn h J.vars) :
    P.DerivesGoal (J.map h) ↔ P.DerivesGoal J := by
  classical
  refine ⟨?_, DerivesGoal.map ⟨Set.Subset.rfl, Set.Subset.rfl⟩⟩
  by_cases hne : J.vars.Nonempty
  · obtain ⟨v₀, hv₀⟩ := hne
    let inv : W → V := fun w ↦ if hw : ∃ v ∈ J.vars, h v = w then hw.choose else v₀
    have hinv_eq : ∀ {v : V}, v ∈ J.vars → inv (h v) = v := by
      intro v hv
      have hex : ∃ u ∈ J.vars, h u = h v := ⟨v, hv, rfl⟩
      simp only [inv, hex, ↓reduceDIte]
      exact hinj hex.choose_spec.1 hv hex.choose_spec.2
    have hsub : ((J.map h).map inv).IsSubinstance J := by
      refine ⟨?_, ?_⟩
      · rw [CSPInstance.map_vars, CSPInstance.map_vars]
        rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        rw [hinv_eq hv]
        exact hv
      · rw [CSPInstance.map_constraints, CSPInstance.map_constraints]
        rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
        have heq : (c.map h).map inv = c := by
          rcases c with ⟨m, R, sc⟩
          change (⟨m, R, inv ∘ h ∘ sc⟩ : CSPConstraint L V) = ⟨m, R, sc⟩
          congr 1; ext i; exact hinv_eq (J.scope_mem hc i)
        rw [heq]
        exact hc
    exact DerivesGoal.map hsub
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rintro ⟨R, ρ, _, hd⟩
    have hm := hd.scope_mem ⟨0, P.idbArity_pos R⟩
    simp [CSPInstance.map_vars, hne] at hm

/-- A Datalog program `P` decides `CSP(A)` if `P(I) ⊢ G` holds if and only if `I` is
unsatisfiable in `A`, for every finite CSP instance `I`. -/
@[expose]
def Decides (P : DatalogProgram L) (A : Type*) [L.Structure A] : Prop :=
  ∀ ⦃n : ℕ⦄ (I : CSPInstance L (Fin n)), P.DerivesGoal I ↔ ¬ I.Satisfiable A

/-- Universe-polymorphic elimination for `DatalogProgram.Decides`: applies to any finite CSP
instance `I` on an arbitrary variable type `V : Type*`. -/
theorem Decides.derivesGoal_iff {P : DatalogProgram L} {A : Type*} [L.Structure A]
    (hP : P.Decides A) {V : Type*} (I : CSPInstance L V) :
    P.DerivesGoal I ↔ ¬ I.Satisfiable A := by
  obtain ⟨n, I₀, g, _, hginj, hmap⟩ := I.exists_fin_iso
  rw [← hmap, derivesGoal_map_iff_of_injOn hginj.injOn,
    CSPInstance.satisfiable_map_iff_of_injOn hginj.injOn]
  exact hP I₀

/-- One-step initialization `P(I) ⊢₀ R(ρ)` without using any intermediate IDB atoms. -/
@[expose]
def DerivesInit (P : DatalogProgram L) {V : Type*} (I : CSPInstance L V)
    (R : P.IDB) (ρ : Fin (P.idbArity R) → V) : Prop :=
  ∃ r ∈ P.rules, ∃ ω : P.Var → V,
    (∀ x, ω x ∈ I.vars) ∧
    bodyIdbs r.body = [] ∧
    (∀ e ∈ bodyEdbs r.body, (⟨e.arity, e.rel, ω ∘ e.scope⟩ : CSPConstraint L V) ∈ I.constraints) ∧
    r.head = R ∧ HEq (ω ∘ r.headScope) ρ

/-- One-step transition `DerivationStep P I ⟨S, σ⟩ ⟨R, ρ⟩` in the computation digraph `G(P, I)`:
`P` contains a `1`-IDB rule `R(τ) ← S(η), T₁(τ₁), …, T_k(τ_k)` and an evaluation `ω` mapping
`P.Var` into `I.vars`, `η` to `σ`, `τ` to `ρ`, and each `T_j(τ_j)` into `I.constraints`. -/
@[expose]
def DerivationStep (P : DatalogProgram L) {V : Type*} (I : CSPInstance L V)
    (u v : (R : P.IDB) × (Fin (P.idbArity R) → V)) : Prop :=
  ∃ r ∈ P.rules, ∃ (ω : P.Var → V) (S : P.IDB) (η : Fin (P.idbArity S) → P.Var),
    (∀ x, ω x ∈ I.vars) ∧
    bodyIdbs r.body = [⟨S, η⟩] ∧
    (∀ e ∈ bodyEdbs r.body, (⟨e.arity, e.rel, ω ∘ e.scope⟩ : CSPConstraint L V) ∈ I.constraints) ∧
    (⟨S, ω ∘ η⟩ : (R : P.IDB) × (Fin (P.idbArity R) → V)) = u ∧
    (⟨r.head, ω ∘ r.headScope⟩ : (R : P.IDB) × (Fin (P.idbArity R) → V)) = v

/-- When `P` is a symmetric Datalog program, the computation digraph `DerivationStep P I` is
symmetric on every instance `I`. -/
theorem DerivationStep.symm {P : DatalogProgram L} (hP : P.IsSymmetric) {V : Type*}
    {I : CSPInstance L V} {u v : (R : P.IDB) × (Fin (P.idbArity R) → V)}
    (hstep : P.DerivationStep I u v) :
    P.DerivationStep I v u := by
  rcases hstep with ⟨r, hr, ω, S, η, hω, hbidb, hbedb, hu, hv⟩
  obtain ⟨r', hr', hhead, hsc, hbidb', hbedb'⟩ := hP.2 r hr S η hbidb
  refine ⟨r', hr', ω, r.head, r.headScope, hω, hbidb',
    fun e he ↦ hbedb e ((hbedb' e).mp he), hv, ?_⟩
  rw [← hu]
  cases hhead
  cases eq_of_heq hsc
  rfl

/-- For any linear Datalog program `P`, `P(I) ⊢ R(ρ)` holds if and only if there is a `0`-IDB
derived statement `u₀` and a directed path from `u₀` to `⟨R, ρ⟩` in `DerivationStep P I`. -/
theorem IsLinear.derives_iff_chain {P : DatalogProgram L} (hlin : P.IsLinear)
    {V : Type*} (I : CSPInstance L V) (R : P.IDB) (ρ : Fin (P.idbArity R) → V) :
    P.Derives I R ρ ↔
      ∃ u₀ : (S : P.IDB) × (Fin (P.idbArity S) → V),
        P.DerivesInit I u₀.1 u₀.2 ∧
        Relation.ReflTransGen (P.DerivationStep I) u₀ ⟨R, ρ⟩ := by
  constructor
  · intro hd
    induction hd with
    | step r hr ω hω hedb hidb ih =>
      have hlen : (bodyIdbs r.body).length ≤ 1 := by
        rw [length_bodyIdbs]
        exact hlin r hr
      have hmem := mem_body_iff r.body
      have hbedb : ∀ e ∈ bodyEdbs r.body,
          (⟨e.arity, e.rel, ω ∘ e.scope⟩ : CSPConstraint L V) ∈ I.constraints :=
        fun e he ↦ hedb e.rel e.scope ((hmem.2 e.arity e.rel e.scope).mpr he)
      rcases hbi : bodyIdbs r.body with _ | ⟨⟨S, η⟩, tl⟩
      · refine ⟨⟨r.head, ω ∘ r.headScope⟩,
          ⟨r, hr, ω, hω, hbi, hbedb, rfl, HEq.rfl⟩, Relation.ReflTransGen.refl⟩
      · have htl : tl = [] := by
          rw [hbi, List.length_cons] at hlen
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst htl
        have hSmem : DatalogAtom.idb S η ∈ r.body := (hmem.1 S η).mpr (by simp [hbi])
        obtain ⟨u₀, hinit, hpath⟩ := ih S η hSmem
        refine ⟨u₀, hinit, hpath.tail ?_⟩
        exact ⟨r, hr, ω, S, η, hω, hbi, hbedb, rfl, rfl⟩
  · rintro ⟨u₀, hinit, hpath⟩
    have hd₀ : P.Derives I u₀.1 u₀.2 := by
      rcases u₀ with ⟨S₀, σ₀⟩
      rcases hinit with ⟨r, hr, ω, hω, hbi, hbedb, hhead, hsc⟩
      cases hhead
      cases eq_of_heq hsc
      have hmem := mem_body_iff r.body
      exact Derives.step r hr ω hω
        (fun n T τ h ↦ hbedb ⟨n, T, τ⟩ ((hmem.2 n T τ).mp h))
        (fun S σ h ↦ by
          have := (hmem.1 S σ).mp h
          simp [hbi] at this)
    have hgo : ∀ {v : (S : P.IDB) × (Fin (P.idbArity S) → V)},
        Relation.ReflTransGen (P.DerivationStep I) u₀ v → P.Derives I v.1 v.2 := by
      intro v hp
      induction hp with
      | refl => exact hd₀
      | tail _ hst ih =>
        rcases hst with ⟨r, hr, ω, S, η, hω, hbi, hbedb, hu, hv⟩
        rw [← hv]
        have hmem := mem_body_iff r.body
        refine Derives.step r hr ω hω
          (fun n T τ h ↦ hbedb ⟨n, T, τ⟩ ((hmem.2 n T τ).mp h))
          (fun S' σ' h ↦ ?_)
        have hm := (hmem.1 S' σ').mp h
        rw [hbi, List.mem_singleton] at hm
        cases hm
        have hdS : P.Derives I (⟨S, ω ∘ η⟩ : (T : P.IDB) × (Fin (P.idbArity T) → V)).1
            (⟨S, ω ∘ η⟩ : (T : P.IDB) × (Fin (P.idbArity T) → V)).2 := by
          rwa [hu]
        exact hdS
    exact hgo hpath

end DatalogProgram

end Datalog

/-! ### Canonical linear and `r`-ary maximal symmetric Datalog programs -/

section MaximalPrograms

/-- An IDB predicate of the `r`-ary canonical/maximal Datalog program over `A`: a relation
`rel : Set (Fin arity → A)` of arity `1 ≤ arity ≤ r`. -/
@[ext]
structure BoundedRel (A : Type*) (r : ℕ) where
  /-- Positive arity of the predicate. -/
  arity : ℕ
  /-- Positivity of `arity`. -/
  arity_pos : 0 < arity
  /-- Arity upper bound `arity ≤ r`. -/
  arity_le : arity ≤ r
  /-- Underlying relation on `A`. -/
  rel : Set (Fin arity → A)

instance {A : Type*} [Finite A] (r : ℕ) : Finite (BoundedRel A r) := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  let S := Σ n : Fin (r + 1), Set (Fin n.1 → A)
  have : Finite S := inferInstance
  refine Finite.of_injective
    (fun R : BoundedRel A r ↦ (⟨⟨R.arity, Nat.lt_succ_of_le R.arity_le⟩, R.rel⟩ : S)) ?_
  intro R₁ R₂ h
  rcases R₁ with ⟨n₁, hp₁, hl₁, rel₁⟩
  rcases R₂ with ⟨n₂, hp₂, hl₂, rel₂⟩
  dsimp at h
  have hn : n₁ = n₂ := congrArg Fin.val (Sigma.mk.inj h).1
  subst hn
  have hrel : rel₁ = rel₂ := eq_of_heq (Sigma.mk.inj h).2
  subst hrel
  rfl

/-- An atom over `BoundedRel A r` satisfies semantic consistency at assignment `f : Var → A`. -/
@[expose]
def DatalogAtom.HoldsIn {L : FirstOrder.Language} {A : Type*} [L.Structure A] {r : ℕ}
    {Var : Type*} (f : Var → A) :
    DatalogAtom L (fun R : BoundedRel A r ↦ R.arity) Var → Prop
  | .idb S σ => f ∘ σ ∈ S.rel
  | .edb _ T τ => Structure.RelMap T (f ∘ τ)

/-- A rule over `BoundedRel A r` is consistent with the `L`-structure `A` if for every assignment
`f : Fin r → A`, satisfaction of all body atoms implies satisfaction of the head atom. -/
@[expose]
def DatalogRule.IsConsistentWith {L : FirstOrder.Language} (A : Type*) [L.Structure A] {r : ℕ}
    (α : DatalogRule L (fun R : BoundedRel A r ↦ R.arity) (Fin r)) : Prop :=
  ∀ f : Fin r → A, (∀ a ∈ α.body, a.HoldsIn f) → f ∘ α.headScope ∈ α.head.rel

/-- Mirror consistency of a linear rule over `BoundedRel A r`: whenever the body contains an IDB
atom `S(σ)`, every `f : Fin r → A` satisfying the head atom and all EDB body atoms satisfies
`S(σ)`. -/
@[expose]
def DatalogRule.IsMirrorConsistentWith {L : FirstOrder.Language} (A : Type*) [L.Structure A]
    {r : ℕ} (α : DatalogRule L (fun R : BoundedRel A r ↦ R.arity) (Fin r)) : Prop :=
  ∀ (S : BoundedRel A r) (σ : Fin S.arity → Fin r),
    DatalogAtom.idb S σ ∈ α.body →
    ∀ f : Fin r → A,
      f ∘ α.headScope ∈ α.head.rel →
      (∀ e ∈ DatalogProgram.bodyEdbs α.body, Structure.RelMap e.rel (f ∘ e.scope)) →
      f ∘ σ ∈ S.rel

/-- Every EDB atom in a rule has arity at most `r`. -/
@[expose]
def DatalogRule.HasBoundedEdbArity {L : FirstOrder.Language} {IDB Var : Type*}
    {idbArity : IDB → ℕ} (r : ℕ) (α : DatalogRule L idbArity Var) : Prop :=
  ∀ e ∈ DatalogProgram.bodyEdbs α.body, e.arity ≤ r

/-- Repetition-free Datalog rules over `BoundedRel A r` and variable set `Fin r` form a finite
set. -/
theorem finite_nodup_rules (L : FirstOrder.Language) [IsFinitePosRelational L]
    (A : Type*) [Finite A] (r : ℕ) :
    ({α : DatalogRule L (fun R : BoundedRel A r ↦ R.arity) (Fin r) |
      α.body.Nodup} : Set _).Finite := by
  classical
  let idbAr : BoundedRel A r → ℕ := fun R ↦ R.arity
  let Atom := DatalogAtom L idbAr (Fin r)
  have hAtomFin : Finite Atom := by
    have := IsFinitePosRelational.finite_sigma_relations (L := L)
    let _ : Fintype (BoundedRel A r) := Fintype.ofFinite _
    let _ : Fintype (Σ n : ℕ, L.Relations n) := Fintype.ofFinite _
    let E := (Σ R : BoundedRel A r, Fin R.arity → Fin r) ⊕
      (Σ s : (Σ n : ℕ, L.Relations n), Fin s.1 → Fin r)
    have : Finite E := inferInstance
    refine Finite.of_surjective (fun x : E ↦ match x with
      | Sum.inl ⟨R, σ⟩ => DatalogAtom.idb R σ
      | Sum.inr ⟨⟨n, T⟩, τ⟩ => DatalogAtom.edb n T τ) ?_
    rintro (⟨R, σ⟩ | ⟨n, T, τ⟩)
    · exact ⟨Sum.inl ⟨R, σ⟩, rfl⟩
    · exact ⟨Sum.inr ⟨⟨n, T⟩, τ⟩, rfl⟩
  let _ : Fintype Atom := Fintype.ofFinite Atom
  let _ : Fintype (BoundedRel A r) := Fintype.ofFinite _
  let NodupBody := {l : List Atom // l.Nodup}
  have hNodupFin : Finite NodupBody := by
    have hbd : ∀ l : NodupBody, l.1.length < Fintype.card Atom + 1 :=
      fun l ↦ Nat.lt_succ_of_le l.2.length_le_card
    refine Finite.of_injective
      (fun l : NodupBody ↦ (⟨⟨l.1.length, hbd l⟩, l.1.get⟩ :
        Σ k : Fin (Fintype.card Atom + 1), Fin k.1 → Atom)) ?_
    intro l₁ l₂ h
    apply Subtype.ext
    apply List.ext_get (congrArg Fin.val (Sigma.mk.inj h).1)
    intro i hi₁ hi₂
    have hfn : HEq l₁.1.get l₂.1.get := (Sigma.mk.inj h).2
    have hlen : l₁.1.length = l₂.1.length := congrArg Fin.val (Sigma.mk.inj h).1
    cases l₁ with | mk a ha =>
    cases l₂ with | mk b hb =>
    dsimp at hlen hfn hi₁ hi₂ ⊢
    have hget : ∀ (m₁ m₂ : ℕ) (f₁ : Fin m₁ → Atom) (f₂ : Fin m₂ → Atom),
        m₁ = m₂ → HEq f₁ f₂ → ∀ (j : ℕ) (hj₁ : j < m₁) (hj₂ : j < m₂),
          f₁ ⟨j, hj₁⟩ = f₂ ⟨j, hj₂⟩ := by
      rintro m _ f₁ f₂ rfl hf j hj₁ _
      cases eq_of_heq hf
      rfl
    exact hget a.length b.length a.get b.get hlen hfn i hi₁ hi₂
  let _ : Fintype NodupBody := Fintype.ofFinite NodupBody
  let Rep := Σ R : BoundedRel A r, (Fin R.arity → Fin r) × NodupBody
  let _ : Fintype Rep := Fintype.ofFinite Rep
  let fRep : Rep → DatalogRule L idbAr (Fin r) := fun x ↦ ⟨x.1, x.2.1, x.2.2.1⟩
  exact (Set.finite_univ.image fRep).subset
    fun α hα ↦ ⟨⟨α.head, α.headScope, ⟨α.body, hα⟩⟩, Set.mem_univ _, rfl⟩

/-- The `r`-ary maximal symmetric Datalog program `P_A^r` consistent with a finite `L`-structure
`A`: its IDBs are all positive-arity relations on `A` of arity at most `r`, its EDBs are the basic
relations of `L` of arity at most `r`, its rules are all repetition-free linear rules over `Fin r`
that are consistent and mirror-consistent with `A`, and its goal predicates are all empty relations
of arity at most `r`. -/
@[expose]
def maximalSymProgram (L : FirstOrder.Language) [IsFinitePosRelational L]
    (A : Type*) [L.Structure A] [Finite A] (r : ℕ) : DatalogProgram L where
  IDB := BoundedRel A r
  Var := Fin r
  finite_idb := inferInstance
  finite_var := inferInstance
  idbArity R := R.arity
  idbArity_pos R := R.arity_pos
  rules := {α | α.IsLinear ∧ α.body.Nodup ∧ α.HasBoundedEdbArity r ∧
    α.IsConsistentWith A ∧ α.IsMirrorConsistentWith A}
  finite_rules := (finite_nodup_rules L A r).subset fun _ h ↦ h.2.1
  isGoal := {R | R.rel = ∅}

/-- The `r`-ary canonical linear Datalog program `L_A^r` consistent with a finite `L`-structure `A`,
obtained from `maximalSymProgram` by omitting the mirror-consistency requirement. -/
@[expose]
def canonicalLinearProgram (L : FirstOrder.Language) [IsFinitePosRelational L]
    (A : Type*) [L.Structure A] [Finite A] (r : ℕ) : DatalogProgram L where
  IDB := BoundedRel A r
  Var := Fin r
  finite_idb := inferInstance
  finite_var := inferInstance
  idbArity R := R.arity
  idbArity_pos R := R.arity_pos
  rules := {α | α.IsLinear ∧ α.body.Nodup ∧ α.HasBoundedEdbArity r ∧ α.IsConsistentWith A}
  finite_rules := (finite_nodup_rules L A r).subset fun _ h ↦ h.2.1
  isGoal := {R | R.rel = ∅}

/-- `canonicalLinearProgram L A r` is a linear Datalog program. -/
theorem canonicalLinearProgram_isLinear (L : FirstOrder.Language) [IsFinitePosRelational L]
    (A : Type*) [L.Structure A] [Finite A] (r : ℕ) :
    (canonicalLinearProgram L A r).IsLinear :=
  fun _ hα ↦ hα.1

/-- `maximalSymProgram L A r` is a symmetric Datalog program. -/
theorem maximalSymProgram_isSymmetric (L : FirstOrder.Language) [IsFinitePosRelational L]
    (A : Type*) [L.Structure A] [Finite A] (r : ℕ) :
    (maximalSymProgram L A r).IsSymmetric := by
  classical
  refine ⟨fun _ hα ↦ hα.1, ?_⟩
  intro α hα S σ hbidb
  rcases hα with ⟨_, hnodup, hbd, hcons, hmir⟩
  let edbs := (DatalogProgram.bodyEdbs α.body).dedup
  let α' : DatalogRule L (fun R : BoundedRel A r ↦ R.arity) (Fin r) :=
    DatalogRule.mkStep (idbArity := fun R : BoundedRel A r ↦ R.arity) S σ α.head α.headScope edbs
  have hα'idbs : DatalogProgram.bodyIdbs α'.body = [⟨α.head, α.headScope⟩] := by
    change DatalogProgram.bodyIdbs (.idb α.head α.headScope :: edbs.map EDBAtom.toAtom) = _
    rw [DatalogProgram.bodyIdbs, DatalogProgram.bodyIdbs_map_toAtom]
    rfl
  have hα'edbs : DatalogProgram.bodyEdbs α'.body = edbs := by
    change DatalogProgram.bodyEdbs (.idb α.head α.headScope :: edbs.map EDBAtom.toAtom) = _
    rw [DatalogProgram.bodyEdbs, DatalogProgram.bodyEdbs_map_toAtom]
  have hmem := DatalogProgram.mem_body_iff α.body
  have hSmem : DatalogAtom.idb S σ ∈ α.body := (hmem.1 S σ).mpr (by simp [hbidb])
  have hedb_iff : ∀ e : EDBAtom L (Fin r), e ∈ edbs ↔ e ∈ DatalogProgram.bodyEdbs α.body :=
    fun _ ↦ List.mem_dedup
  have hα'_mem : α'.IsLinear ∧ α'.body.Nodup ∧ α'.HasBoundedEdbArity r ∧
      α'.IsConsistentWith A ∧ α'.IsMirrorConsistentWith A := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change (α'.body.filter fun a ↦ a.isIdb = true).length ≤ 1
      rw [← DatalogProgram.length_bodyIdbs, hα'idbs]
      exact le_rfl
    · refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro h
        rcases List.mem_map.mp h with ⟨e, _, he⟩
        cases he
      · refine (DatalogProgram.bodyEdbs α.body).nodup_dedup.map ?_
        intro e₁ e₂ h
        rcases e₁ with ⟨n₁, T₁, τ₁⟩
        rcases e₂ with ⟨n₂, T₂, τ₂⟩
        cases h
        rfl
    · intro e he
      rw [hα'edbs] at he
      exact hbd e ((hedb_iff e).mp he)
    · intro f hf
      apply hmir S σ hSmem f
      · exact hf (.idb α.head α.headScope) List.mem_cons_self
      · intro e he
        have h1 : e.toAtom ∈ α'.body :=
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, (hedb_iff e).mpr he, rfl⟩)
        exact hf e.toAtom h1
    · intro S' σ' hS' f hhead hedb'
      have hS'eq : (⟨S', σ'⟩ : (R : BoundedRel A r) × (Fin R.arity → Fin r)) =
          ⟨α.head, α.headScope⟩ := by
        rcases List.mem_cons.mp hS' with h | h
        · cases h; rfl
        · rcases List.mem_map.mp h with ⟨e, _, he⟩
          cases he
      cases hS'eq
      apply hcons f
      intro a ha
      cases a with
      | idb T η =>
        have hm := (hmem.1 T η).mp ha
        rw [hbidb, List.mem_singleton] at hm
        cases hm
        exact hhead
      | edb n T τ =>
        have hm : (⟨n, T, τ⟩ : EDBAtom L (Fin r)) ∈ edbs :=
          (hedb_iff _).mpr ((hmem.2 n T τ).mp ha)
        apply hedb' ⟨n, T, τ⟩
        rwa [hα'edbs]
  exact ⟨α', hα'_mem, rfl, HEq.rfl, hα'idbs, fun e ↦ by
    change e ∈ DatalogProgram.bodyEdbs α'.body ↔ e ∈ DatalogProgram.bodyEdbs α.body
    rw [hα'edbs]
    exact hedb_iff e⟩

/-- Convenience abbreviation: `(maximalSymProgram L A r)` derives `S(ρ)` on `I` for a relation
`S : Set (Fin n → A)` with `1 ≤ n ≤ r`. -/
@[expose]
def MaxSymDerives (L : FirstOrder.Language) [IsFinitePosRelational L]
    (A : Type*) [L.Structure A] [Finite A] (r : ℕ) {V : Type*} (I : CSPInstance L V)
    {n : ℕ} (S : Set (Fin n → A)) (ρ : Fin n → V) : Prop :=
  ∃ (hpos : 0 < n) (hle : n ≤ r),
    (maximalSymProgram L A r).Derives I ⟨n, hpos, hle, S⟩ ρ

/-- Convenience abbreviation: `(maximalSymProgram L A r)(I) ⊢ G`. -/
@[expose]
def MaxSymDerivesGoal (L : FirstOrder.Language) [IsFinitePosRelational L]
    (A : Type*) [L.Structure A] [Finite A] (r : ℕ) {V : Type*} (I : CSPInstance L V) : Prop :=
  (maximalSymProgram L A r).DerivesGoal I

/-- An empty derived relation yields `MaxSymDerivesGoal`. -/
theorem MaxSymDerives.derivesGoal {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    {n : ℕ} {S : Set (Fin n → A)} {ρ : Fin n → V}
    (hd : MaxSymDerives L A r I S ρ) (hempty : S = ∅) :
    MaxSymDerivesGoal L A r I := by
  rcases hd with ⟨hpos, hle, h⟩
  exact ⟨⟨n, hpos, hle, S⟩, ρ, hempty, h⟩

/-- Every relation derived by `canonicalLinearProgram L A r` holds on every solution of `I`. -/
theorem canonicalLinearProgram_sound {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    {R : (canonicalLinearProgram L A r).IDB}
    {ρ : Fin ((canonicalLinearProgram L A r).idbArity R) → V}
    (hd : (canonicalLinearProgram L A r).Derives I R ρ)
    {f : I.vars → A} (hf : I.IsSolution A f) :
    (fun i ↦ f ⟨ρ i, hd.scope_mem i⟩) ∈ (R : BoundedRel A r).rel := by
  refine @DatalogProgram.Derives.rec L (canonicalLinearProgram L A r) V I
    (fun S σ h ↦ (fun i ↦ f ⟨σ i, h.scope_mem i⟩) ∈ (S : BoundedRel A r).rel)
    (fun α hα ω hω hedb _ ih ↦ ?_) R ρ hd
  apply hα.2.2.2 (fun x ↦ f ⟨ω x, hω x⟩)
  intro a ha
  cases a with
  | idb S σ => exact ih S σ ha
  | edb n T τ => exact hf (hedb T τ ha)

/-- If `canonicalLinearProgram L A r` reaches a goal predicate on `I`, then `I` is unsatisfiable. -/
theorem canonicalLinearProgram_unsatisfiable_of_derivesGoal
    {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    (hd : (canonicalLinearProgram L A r).DerivesGoal I) :
    ¬ I.Satisfiable A := by
  rintro ⟨f, hf⟩
  rcases hd with ⟨R, ρ, hempty, hder⟩
  have hmem := canonicalLinearProgram_sound hder hf
  rw [hempty] at hmem
  exact hmem

/-- Every derivation in `maximalSymProgram L A r` is also a derivation in
`canonicalLinearProgram L A r`. -/
theorem maximalSymProgram_derives_to_canonical {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    {R : BoundedRel A r} {ρ : Fin R.arity → V}
    (hd : (maximalSymProgram L A r).Derives I R ρ) :
    (canonicalLinearProgram L A r).Derives I R ρ :=
  @DatalogProgram.Derives.rec L (maximalSymProgram L A r) V I
    (fun S σ _ ↦ (canonicalLinearProgram L A r).Derives I S σ)
    (fun α hα ω hω hedb _ ih ↦ by
      have hα' : α ∈ (canonicalLinearProgram L A r).rules :=
        ⟨hα.1, hα.2.1, hα.2.2.1, hα.2.2.2.1⟩
      exact DatalogProgram.Derives.step (P := canonicalLinearProgram L A r) α hα' ω hω hedb ih)
    R ρ hd

/-- **Consistency Soundness of `maximalSymProgram`**: if `P_A^r(I) ⊢ R(ρ)`, then every solution
`f` of `I` satisfies `f(ρ) ∈ R`. -/
theorem maximalSymProgram_sound {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    {n : ℕ} {S : Set (Fin n → A)} {ρ : Fin n → V}
    (hd : MaxSymDerives L A r I S ρ)
    {f : I.vars → A} (hf : I.IsSolution A f) :
    ∃ hmem : ∀ i, ρ i ∈ I.vars, (fun i ↦ f ⟨ρ i, hmem i⟩) ∈ S := by
  rcases hd with ⟨hpos, hle, hder⟩
  have hcan := maximalSymProgram_derives_to_canonical hder
  exact ⟨hcan.scope_mem, canonicalLinearProgram_sound hcan hf⟩

/-- If `P_A^r(I) ⊢ G`, then `I` is unsatisfiable in `A`. -/
theorem maximalSymProgram_unsatisfiable_of_derivesGoal
    {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    (hd : (maximalSymProgram L A r).DerivesGoal I) :
    ¬ I.Satisfiable A := by
  rcases hd with ⟨R, ρ, hg, hder⟩
  exact canonicalLinearProgram_unsatisfiable_of_derivesGoal
    ⟨R, ρ, hg, maximalSymProgram_derives_to_canonical hder⟩

/-- Semantic `0`-IDB introduction rule for `MaxSymDerives`: if a finite set `U ⊆ I.vars` has
`U.ncard ≤ r`, `R : Set (Fin n → A)` has `1 ≤ n ≤ r`, `ρ` lands in `U`, and `cs` is a finite list
of constraints of `I` of arity `≤ r` with scopes in `U` that semantically imply `R(ρ)` in `A`,
then `P_A^r(I) ⊢ R(ρ)`. -/
theorem MaxSymDerives.of_init {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    {U : Set V} (hUsub : U ⊆ I.vars) (hUcard : U.ncard ≤ r)
    {n : ℕ} (hn_pos : 0 < n) (hn_le : n ≤ r) (R : Set (Fin n → A))
    (ρ : Fin n → V) (hρ : Set.range ρ ⊆ U)
    (cs : List (CSPConstraint L V))
    (hcs_mem : ∀ c ∈ cs, c ∈ I.constraints)
    (hcs_ar : ∀ c ∈ cs, c.arity ≤ r)
    (hcs_sc : ∀ c ∈ cs, Set.range c.scope ⊆ U)
    (himp : ∀ f : V → A,
      (∀ c ∈ cs, Structure.RelMap c.rel (f ∘ c.scope)) → f ∘ ρ ∈ R) :
    MaxSymDerives L A r I R ρ := by
  classical
  have hUfin : U.Finite := I.finite_vars.subset hUsub
  have hUne : U.Nonempty := ⟨ρ ⟨0, hn_pos⟩, hρ ⟨⟨0, hn_pos⟩, rfl⟩⟩
  have hr_pos : 0 < r := lt_of_lt_of_le hn_pos hn_le
  let _ : Fintype U := hUfin.fintype
  have hcard : Fintype.card U ≤ r := by
    rwa [Set.ncard_eq_toFinset_card U hUfin, Set.Finite.card_toFinset] at hUcard
  let eU : Fin (Fintype.card U) ≃ U := (Fintype.equivFin U).symm
  let v₀ : V := hUne.some
  have hv₀ : v₀ ∈ U := hUne.some_mem
  let ω : Fin r → V := fun x ↦ if hx : x.1 < Fintype.card U then (eU ⟨x.1, hx⟩).1 else v₀
  let idx : (v : V) → v ∈ U → Fin r := fun v hv ↦
    let j := eU.symm ⟨v, hv⟩
    ⟨j.1, lt_of_lt_of_le j.2 hcard⟩
  have hω_idx : ∀ (v : V) (hv : v ∈ U), ω (idx v hv) = v := by
    intro v hv
    have hj : (eU.symm ⟨v, hv⟩).1 < Fintype.card U := (eU.symm ⟨v, hv⟩).2
    simp only [ω, idx, hj, ↓reduceDIte, Fin.eta, Equiv.apply_symm_apply]
  have hω_mem : ∀ x : Fin r, ω x ∈ I.vars := by
    intro x
    apply hUsub
    dsimp [ω]
    split_ifs with hx
    · exact (eU ⟨x.1, hx⟩).2
    · exact hv₀
  let τ : Fin n → Fin r := fun i ↦ idx (ρ i) (hρ ⟨i, rfl⟩)
  let rawEdbs : List (EDBAtom L (Fin r)) :=
    cs.attach.map fun ⟨c, hc⟩ ↦ ⟨c.arity, c.rel, fun i ↦ idx (c.scope i) (hcs_sc c hc ⟨i, rfl⟩)⟩
  let edbs := rawEdbs.dedup
  let headRel : BoundedRel A r := ⟨n, hn_pos, hn_le, R⟩
  let α : DatalogRule L (fun R : BoundedRel A r ↦ R.arity) (Fin r) :=
    DatalogRule.mkInit (idbArity := fun R : BoundedRel A r ↦ R.arity) headRel τ edbs
  have hα_mem : α ∈ (maximalSymProgram L A r).rules := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change (α.body.filter fun a ↦ a.isIdb = true).length ≤ 1
      rw [← DatalogProgram.length_bodyIdbs]
      change (DatalogProgram.bodyIdbs (edbs.map EDBAtom.toAtom)).length ≤ 1
      rw [DatalogProgram.bodyIdbs_map_toAtom]
      exact Nat.zero_le 1
    · refine rawEdbs.nodup_dedup.map ?_
      intro e₁ e₂ h
      rcases e₁ with ⟨n₁, T₁, τ₁⟩
      rcases e₂ with ⟨n₂, T₂, τ₂⟩
      cases h
      rfl
    · intro e he
      change e ∈ DatalogProgram.bodyEdbs (edbs.map EDBAtom.toAtom) at he
      rw [DatalogProgram.bodyEdbs_map_toAtom] at he
      rcases List.mem_map.mp (List.mem_dedup.mp he) with ⟨⟨c, hc⟩, _, rfl⟩
      exact hcs_ar c hc
    · intro f hf
      by_cases hA : IsEmpty A
      · exact hA.elim (f ⟨0, hr_pos⟩)
      · rw [not_isEmpty_iff] at hA
        let a₀ : A := Classical.arbitrary A
        let F : V → A := fun v ↦ if hv : v ∈ U then f (idx v hv) else a₀
        have hFρ : F ∘ ρ = f ∘ τ := by
          ext i
          simp only [Function.comp_def, F, τ, hρ ⟨i, rfl⟩, ↓reduceDIte]
        change f ∘ τ ∈ R
        rw [← hFρ]
        apply himp F
        intro c hc
        let e : EDBAtom L (Fin r) :=
          ⟨c.arity, c.rel, fun i ↦ idx (c.scope i) (hcs_sc c hc ⟨i, rfl⟩)⟩
        have hemem : e.toAtom ∈ α.body :=
          List.mem_map.mpr ⟨e, List.mem_dedup.mpr (List.mem_map.mpr
            ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩), rfl⟩
        have hrel : Structure.RelMap c.rel (f ∘ e.scope) := hf e.toAtom hemem
        have harg : F ∘ c.scope = f ∘ e.scope := by
          ext i
          simp only [Function.comp_def, F, e, hcs_sc c hc ⟨i, rfl⟩, ↓reduceDIte]
        rwa [harg]
    · intro S σ hS
      rcases List.mem_map.mp hS with ⟨e, _, he⟩
      cases he
  have hωτ : ω ∘ τ = ρ := funext fun i ↦ hω_idx (ρ i) (hρ ⟨i, rfl⟩)
  refine ⟨hn_pos, hn_le, ?_⟩
  rw [← hωτ]
  refine DatalogProgram.Derives.step (P := maximalSymProgram L A r) α hα_mem ω hω_mem ?_ ?_
  · intro m T η hmem
    rcases List.mem_map.mp hmem with ⟨e, he, heq⟩
    rcases e with ⟨m', T', η'⟩
    cases heq
    rcases List.mem_map.mp (List.mem_dedup.mp he) with ⟨⟨c, hc⟩, _, hce⟩
    have hc_eq : (⟨c.arity, c.rel, ω ∘ fun i ↦ idx (c.scope i) (hcs_sc c hc ⟨i, rfl⟩)⟩ :
        CSPConstraint L V) = c := by
      cases c
      simp only [Function.comp_def, hω_idx]
    cases hce
    exact hc_eq.symm ▸ hcs_mem c hc
  · intro S σ hmem
    rcases List.mem_map.mp hmem with ⟨e, _, he⟩
    cases he

/-- Semantic symmetric `1`-IDB transition rule for `MaxSymDerives`: if `P_A^r(I) ⊢ S(σ)`, a finite
set `U ⊆ I.vars` with `U.ncard ≤ r` contains `range σ`, `range ρ`, and the scopes of constraints
`cs` of `I` (all of arity `≤ r`), and `S(σ) ↔ R(ρ)` holds under `cs` for all assignments `V → A`,
then `P_A^r(I) ⊢ R(ρ)`. -/
theorem MaxSymDerives.of_symm_step {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    {U : Set V} (hUsub : U ⊆ I.vars) (hUcard : U.ncard ≤ r)
    {s : ℕ} {S : Set (Fin s → A)} {σ : Fin s → V} (hdS : MaxSymDerives L A r I S σ)
    (hσ : Set.range σ ⊆ U)
    {n : ℕ} (hn_pos : 0 < n) (hn_le : n ≤ r) (R : Set (Fin n → A))
    (ρ : Fin n → V) (hρ : Set.range ρ ⊆ U)
    (cs : List (CSPConstraint L V))
    (hcs_mem : ∀ c ∈ cs, c ∈ I.constraints)
    (hcs_ar : ∀ c ∈ cs, c.arity ≤ r)
    (hcs_sc : ∀ c ∈ cs, Set.range c.scope ⊆ U)
    (hfwd : ∀ f : V → A, f ∘ σ ∈ S →
      (∀ c ∈ cs, Structure.RelMap c.rel (f ∘ c.scope)) → f ∘ ρ ∈ R)
    (hbwd : ∀ f : V → A, f ∘ ρ ∈ R →
      (∀ c ∈ cs, Structure.RelMap c.rel (f ∘ c.scope)) → f ∘ σ ∈ S) :
    MaxSymDerives L A r I R ρ := by
  classical
  rcases hdS with ⟨hs_pos, hs_le, hderS⟩
  have hUfin : U.Finite := I.finite_vars.subset hUsub
  have hUne : U.Nonempty := ⟨ρ ⟨0, hn_pos⟩, hρ ⟨⟨0, hn_pos⟩, rfl⟩⟩
  have hr_pos : 0 < r := lt_of_lt_of_le hn_pos hn_le
  let _ : Fintype U := hUfin.fintype
  have hcard : Fintype.card U ≤ r := by
    rwa [Set.ncard_eq_toFinset_card U hUfin, Set.Finite.card_toFinset] at hUcard
  let eU : Fin (Fintype.card U) ≃ U := (Fintype.equivFin U).symm
  let v₀ : V := hUne.some
  have hv₀ : v₀ ∈ U := hUne.some_mem
  let ω : Fin r → V := fun x ↦ if hx : x.1 < Fintype.card U then (eU ⟨x.1, hx⟩).1 else v₀
  let idx : (v : V) → v ∈ U → Fin r := fun v hv ↦
    let j := eU.symm ⟨v, hv⟩
    ⟨j.1, lt_of_lt_of_le j.2 hcard⟩
  have hω_idx : ∀ (v : V) (hv : v ∈ U), ω (idx v hv) = v := by
    intro v hv
    have hj : (eU.symm ⟨v, hv⟩).1 < Fintype.card U := (eU.symm ⟨v, hv⟩).2
    simp only [ω, idx, hj, ↓reduceDIte, Fin.eta, Equiv.apply_symm_apply]
  have hω_mem : ∀ x : Fin r, ω x ∈ I.vars := by
    intro x
    apply hUsub
    dsimp [ω]
    split_ifs with hx
    · exact (eU ⟨x.1, hx⟩).2
    · exact hv₀
  let τR : Fin n → Fin r := fun i ↦ idx (ρ i) (hρ ⟨i, rfl⟩)
  let τS : Fin s → Fin r := fun i ↦ idx (σ i) (hσ ⟨i, rfl⟩)
  let rawEdbs : List (EDBAtom L (Fin r)) :=
    cs.attach.map fun ⟨c, hc⟩ ↦ ⟨c.arity, c.rel, fun i ↦ idx (c.scope i) (hcs_sc c hc ⟨i, rfl⟩)⟩
  let edbs := rawEdbs.dedup
  let headRel : BoundedRel A r := ⟨n, hn_pos, hn_le, R⟩
  let bodyRel : BoundedRel A r := ⟨s, hs_pos, hs_le, S⟩
  let α : DatalogRule L (fun R : BoundedRel A r ↦ R.arity) (Fin r) :=
    DatalogRule.mkStep (idbArity := fun R : BoundedRel A r ↦ R.arity) headRel τR bodyRel τS edbs
  have hα_mem : α ∈ (maximalSymProgram L A r).rules := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change (α.body.filter fun a ↦ a.isIdb = true).length ≤ 1
      rw [← DatalogProgram.length_bodyIdbs]
      change (DatalogProgram.bodyIdbs (.idb bodyRel τS :: edbs.map EDBAtom.toAtom)).length ≤ 1
      rw [DatalogProgram.bodyIdbs, DatalogProgram.bodyIdbs_map_toAtom]
      exact le_rfl
    · refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro h
        rcases List.mem_map.mp h with ⟨e, _, he⟩
        cases he
      · refine rawEdbs.nodup_dedup.map ?_
        intro e₁ e₂ h
        rcases e₁ with ⟨_, _, _⟩
        rcases e₂ with ⟨_, _, _⟩
        cases h; rfl
    · intro e he
      simp only [α, DatalogRule.mkStep, DatalogProgram.bodyEdbs,
        DatalogProgram.bodyEdbs_map_toAtom] at he
      rcases List.mem_map.mp (List.mem_dedup.mp he) with ⟨⟨c, hc⟩, _, rfl⟩
      exact hcs_ar c hc
    · intro f hf
      by_cases hA : IsEmpty A
      · exact hA.elim (f ⟨0, hr_pos⟩)
      · rw [not_isEmpty_iff] at hA
        let F : V → A := fun v ↦ if hv : v ∈ U then f (idx v hv) else Classical.arbitrary A
        have hFρ : F ∘ ρ = f ∘ τR := funext fun i ↦ by simp [F, τR, hρ ⟨i, rfl⟩]
        have hFσ : F ∘ σ = f ∘ τS := funext fun i ↦ by simp [F, τS, hσ ⟨i, rfl⟩]
        change f ∘ τR ∈ R
        rw [← hFρ]
        apply hfwd F
        · rw [hFσ]
          exact hf (.idb bodyRel τS) List.mem_cons_self
        · intro c hc
          let e : EDBAtom L (Fin r) :=
            ⟨c.arity, c.rel, fun i ↦ idx (c.scope i) (hcs_sc c hc ⟨i, rfl⟩)⟩
          have hemem : e.toAtom ∈ α.body :=
            List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, List.mem_dedup.mpr
              (List.mem_map.mpr ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩), rfl⟩)
          have harg : F ∘ c.scope = f ∘ e.scope := by
            ext i
            simp only [Function.comp_def, F, e, hcs_sc c hc ⟨i, rfl⟩, ↓reduceDIte]
          rw [harg]
          exact hf e.toAtom hemem
    · intro S' σ' hS' f hhead hedb'
      have heq : (⟨S', σ'⟩ : (T : BoundedRel A r) × (Fin T.arity → Fin r)) = ⟨bodyRel, τS⟩ := by
        rcases List.mem_cons.mp hS' with h | h
        · cases h; rfl
        · rcases List.mem_map.mp h with ⟨e, _, he⟩
          cases he
      cases heq
      by_cases hA : IsEmpty A
      · exact hA.elim (f ⟨0, hr_pos⟩)
      · rw [not_isEmpty_iff] at hA
        let F : V → A := fun v ↦ if hv : v ∈ U then f (idx v hv) else Classical.arbitrary A
        have hFρ : F ∘ ρ = f ∘ τR := funext fun i ↦ by simp [F, τR, hρ ⟨i, rfl⟩]
        have hFσ : F ∘ σ = f ∘ τS := funext fun i ↦ by simp [F, τS, hσ ⟨i, rfl⟩]
        rw [← hFσ]
        apply hbwd F (hFρ.symm ▸ hhead)
        intro c hc
        let e : EDBAtom L (Fin r) :=
          ⟨c.arity, c.rel, fun i ↦ idx (c.scope i) (hcs_sc c hc ⟨i, rfl⟩)⟩
        have hemem : e ∈ DatalogProgram.bodyEdbs α.body := by
          simp only [α, DatalogRule.mkStep, DatalogProgram.bodyEdbs,
            DatalogProgram.bodyEdbs_map_toAtom]
          exact List.mem_dedup.mpr (List.mem_map.mpr ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩)
        convert hedb' e hemem using 1
        ext i
        simp [F, e, hcs_sc c hc ⟨i, rfl⟩]
  have hωR : ω ∘ τR = ρ := funext fun i ↦ hω_idx (ρ i) (hρ ⟨i, rfl⟩)
  have hωS : ω ∘ τS = σ := funext fun i ↦ hω_idx (σ i) (hσ ⟨i, rfl⟩)
  refine ⟨hn_pos, hn_le, ?_⟩
  rw [← hωR]
  refine DatalogProgram.Derives.step (P := maximalSymProgram L A r) α hα_mem ω hω_mem ?_ ?_
  · intro m T η hmem
    rcases List.mem_cons.mp hmem with h | h
    · cases h
    · rcases List.mem_map.mp h with ⟨e, he, heq⟩
      rcases e with ⟨_, _, _⟩
      cases heq
      rcases List.mem_map.mp (List.mem_dedup.mp he) with ⟨⟨c, hc⟩, _, hce⟩
      have hc_eq : (⟨c.arity, c.rel, ω ∘ fun i ↦ idx (c.scope i) (hcs_sc c hc ⟨i, rfl⟩)⟩ :
          CSPConstraint L V) = c := by
        cases c
        simp only [Function.comp_def, hω_idx]
      cases hce
      exact hc_eq.symm ▸ hcs_mem c hc
  · intro S' σ' hmem
    rcases List.mem_cons.mp hmem with h | h
    · cases h
      exact hωS.symm ▸ hderS
    · rcases List.mem_map.mp h with ⟨e, _, he⟩
      cases he

/-- Monotonicity of `MaxSymDerives` in the program width `r ≤ r'`. -/
theorem MaxSymDerives.mono {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r r' : ℕ} (hle : r ≤ r')
    {V : Type*} {I : CSPInstance L V} {n : ℕ} {S : Set (Fin n → A)} {ρ : Fin n → V}
    (hd : MaxSymDerives L A r I S ρ) :
    MaxSymDerives L A r' I S ρ := by
  classical
  rcases hd with ⟨hpos, hnle, hder⟩
  have hgo : ∀ (R : BoundedRel A r) (φ : Fin R.arity → V),
      (maximalSymProgram L A r).Derives I R φ →
      MaxSymDerives L A r' I R.rel φ :=
    @DatalogProgram.Derives.rec L (maximalSymProgram L A r) V I
      (fun R φ _ ↦ MaxSymDerives L A r' I (R : BoundedRel A r).rel φ)
      (fun α hα ω hω hedb _ ih ↦ by
        rcases hα with ⟨hlin, _, hbd, hcons, hmir⟩
        let U : Set V := Set.range (ω : Fin r → V)
        have hUsub : U ⊆ I.vars := by rintro _ ⟨x, rfl⟩; exact hω x
        have hUcard : U.ncard ≤ r' := by
          dsimp only [U]
          rw [← Set.image_univ]
          have hfin : (Set.univ : Set (Fin r)).Finite := Set.finite_univ
          exact (Set.ncard_image_le hfin).trans
            (by simpa [Set.ncard_univ, Nat.card_fin] using hle)
        let edbs := DatalogProgram.bodyEdbs α.body
        let cs : List (CSPConstraint L V) := edbs.map fun e ↦ ⟨e.arity, e.rel, ω ∘ e.scope⟩
        have hmem := DatalogProgram.mem_body_iff α.body
        have hcs_mem : ∀ c ∈ cs, c ∈ I.constraints := by
          intro c hc
          rcases List.mem_map.mp hc with ⟨e, he, rfl⟩
          exact hedb e.rel e.scope ((hmem.2 e.arity e.rel e.scope).mpr he)
        have hcs_ar : ∀ c ∈ cs, c.arity ≤ r' := by
          intro c hc
          rcases List.mem_map.mp hc with ⟨e, he, rfl⟩
          exact (hbd e he).trans hle
        have hcs_sc : ∀ c ∈ cs, Set.range c.scope ⊆ U := by
          intro c hc
          rcases List.mem_map.mp hc with ⟨e, _, rfl⟩
          rintro _ ⟨i, rfl⟩
          exact ⟨e.scope i, rfl⟩
        have hlen : (DatalogProgram.bodyIdbs α.body).length ≤ 1 := by
          rw [DatalogProgram.length_bodyIdbs]; exact hlin
        rcases hbi : DatalogProgram.bodyIdbs α.body with _ | ⟨⟨S₀, σ₀⟩, tl⟩
        · refine MaxSymDerives.of_init hUsub hUcard α.head.arity_pos (α.head.arity_le.trans hle)
            α.head.rel (ω ∘ α.headScope) (by rintro _ ⟨i, rfl⟩; exact ⟨α.headScope i, rfl⟩)
            cs hcs_mem hcs_ar hcs_sc ?_
          intro f hf
          apply hcons (f ∘ ω)
          intro a ha
          cases a with
          | idb T η =>
            have := (hmem.1 T η).mp ha
            simp [hbi] at this
          | edb m T τ =>
            exact hf ⟨m, T, ω ∘ τ⟩ (List.mem_map.mpr ⟨⟨m, T, τ⟩, (hmem.2 m T τ).mp ha, rfl⟩)
        · have htl : tl = [] := by
            rw [hbi, List.length_cons] at hlen
            exact List.eq_nil_of_length_eq_zero (by omega)
          subst htl
          have hSmem : DatalogAtom.idb S₀ σ₀ ∈ α.body := (hmem.1 S₀ σ₀).mpr (by simp [hbi])
          have hdS := ih S₀ σ₀ hSmem
          refine MaxSymDerives.of_symm_step hUsub hUcard hdS
            (by rintro _ ⟨i, rfl⟩; exact ⟨σ₀ i, rfl⟩)
            α.head.arity_pos (α.head.arity_le.trans hle) α.head.rel (ω ∘ α.headScope)
            (by rintro _ ⟨i, rfl⟩; exact ⟨α.headScope i, rfl⟩)
            cs hcs_mem hcs_ar hcs_sc ?_ ?_
          · intro f hfS hfcs
            apply hcons (f ∘ ω)
            intro a ha
            cases a with
            | idb T η =>
              have hm := (hmem.1 T η).mp ha
              rw [hbi, List.mem_singleton] at hm
              cases hm
              exact hfS
            | edb m T τ =>
              exact hfcs ⟨m, T, ω ∘ τ⟩ (List.mem_map.mpr ⟨⟨m, T, τ⟩, (hmem.2 m T τ).mp ha, rfl⟩)
          · intro f hfR hfcs
            exact hmir S₀ σ₀ hSmem (f ∘ ω) hfR fun e he ↦
              hfcs ⟨e.arity, e.rel, ω ∘ e.scope⟩ (List.mem_map.mpr ⟨e, he, rfl⟩))
  exact hgo ⟨n, hpos, hnle, S⟩ ρ hder

/-- Monotonicity of `MaxSymDerivesGoal` in the program width `r ≤ r'`. -/
theorem MaxSymDerivesGoal.mono {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r r' : ℕ} (hle : r ≤ r')
    {V : Type*} {I : CSPInstance L V} (hd : MaxSymDerivesGoal L A r I) :
    MaxSymDerivesGoal L A r' I := by
  rcases hd with ⟨R, ρ, hempty, hder⟩
  have hd' : MaxSymDerives L A r' I R.rel ρ :=
    MaxSymDerives.mono hle ⟨R.arity_pos, R.arity_le, hder⟩
  exact hd'.derivesGoal hempty

/-- Any basic constraint `c ∈ I.constraints` of arity `≤ r` is derived in one step by
`maximalSymProgram L A r`. -/
theorem MaxSymDerives.of_constraint {L : FirstOrder.Language} [IsFinitePosRelational L]
    {A : Type*} [L.Structure A] [Finite A] {r : ℕ} {V : Type*} {I : CSPInstance L V}
    {c : CSPConstraint L V} (hc : c ∈ I.constraints) (har : c.arity ≤ r) :
    MaxSymDerives L A r I (relSet A c.rel) c.scope :=
  MaxSymDerives.of_init
    (U := Set.range c.scope)
    (by rintro _ ⟨i, rfl⟩; exact I.scope_mem hc i)
    (by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans
        (by simpa [Set.ncard_univ, Nat.card_fin] using har))
    (IsFinitePosRelational.arity_pos c.rel) har (relSet A c.rel) c.scope Set.Subset.rfl
    [c] (by simp [hc]) (by simp [har]) (by simp) (by simp)

end MaximalPrograms

end CslibFrontier.Logics
