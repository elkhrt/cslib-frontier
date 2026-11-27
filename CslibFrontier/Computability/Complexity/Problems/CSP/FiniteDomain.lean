/-
Copyright (c) 2026 The CslibFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CslibFrontier contributors
-/
module

public import CslibFrontier.Computability.Complexity.Problems.CSP.Basic
public import CslibFrontier.Computability.Complexity.Reduction.Equiv
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum

import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Problems.CSP.Schaefer
import CslibFrontier.Computability.Complexity.Reduction.Guard
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Foundations.Data.List.OfFnGetD
import CslibFrontier.Logics.Polymorphism.BooleanClone
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Finite-Domain Constraint Satisfaction Problems and Weak Near-Unanimity Polymorphisms

This module generalizes fixed-template Constraint Satisfaction Problems (`CSP(Γ)`) from Boolean
domains to arbitrary finite domains `D`, building directly on `Cslib.Logic.PL.CSP`,
`Cslib.Logic.IsPolymorphism`, and the multi-tape Turing-machine complexity classes `P`, `NP`,
`NPComplete`, `PolyTimeReducible`, and `PolyTimeEquiv` from `CslibFrontier`.

## Main definitions

* `CslibFrontier.Complexity.FiniteCSP.IsWeakNearUnanimity`: weak near-unanimity (WNU) operations
  `f : (Fin m → A) → A` (`m ≥ 2` and `f(y, x, …, x) = f(x, y, …, x) = ⋯ = f(x, …, x, y)`).
* `CslibFrontier.Complexity.FiniteCSP.Language`: fixed-arity constraint language `(arity, sem)` on
  domain `D` indexed by relation alphabet `Rel`.
* `CslibFrontier.Complexity.FiniteCSP.Language.withUnarySingletons`,
  `CslibFrontier.Complexity.FiniteCSP.Language.withConstants`,
  `CslibFrontier.Complexity.FiniteCSP.Language.power`: unary-singleton expansions, full constant
  expansions `Γ*`, and direct-power constraint languages `Γ^m`.
* `CslibFrontier.Complexity.FiniteCSP.Language.cspsat`: exact-arity decision problem `CSP(Γ)`.
* `CslibFrontier.Complexity.FiniteCSP.Language.boolNAE3`: positive ternary Boolean not-all-equal
  constraint language.

## Main results

* `CslibFrontier.Complexity.FiniteCSP.npComplete_of_polyTimeEquiv`,
  `CslibFrontier.Complexity.FiniteCSP.npComplete_iff_of_polyTimeEquiv`: invariance of
  `NPComplete` under polynomial-time many-one equivalence.
* `CslibFrontier.Complexity.FiniteCSP.Language.isPolymorphism_solutions`: polymorphisms of `Γ`
  preserve solution sets of all well-formed conjunctive CSP formulas over `Γ`.
* `CslibFrontier.Complexity.FiniteCSP.Language.withConstants_cspsat_polyTimeReducible`:
  `CSP(Γ*) ≤_m^p CSP(Γ)` whenever `Γ` contains all constant relations.
* `CslibFrontier.Complexity.FiniteCSP.Language.cspsat_mem_NP`: `CSP(Γ) ∈ NP` for every finite
  nonempty domain `D` and finite relation alphabet `Rel`, via polynomial-time one-hot compilation
  into Boolean `CSPSAT`.
* `CslibFrontier.Complexity.FiniteCSP.Language.cspsat_mem_P_of_unaryConst`,
  `CslibFrontier.Complexity.FiniteCSP.Language.cspsat_mem_P_of_subsingleton`: tractability under a
  constant unary polymorphism and on 1-element domains.
* `CslibFrontier.Complexity.FiniteCSP.Language.bool_admitsWNU_iff_hasSchaefer`,
  `CslibFrontier.Complexity.FiniteCSP.Language.bool_cspsat_dichotomy`: equivalence of Boolean WNU
  and Schaefer polymorphisms and the resulting Boolean WNU complexity dichotomy.
* `CslibFrontier.Complexity.FiniteCSP.Language.not_admitsWNU_boolNAE3`,
  `CslibFrontier.Complexity.FiniteCSP.Language.cspsat_npComplete_boolNAE3`: `NAE₃` admits no WNU
  polymorphism and is `NP`-complete.
-/

public section

namespace CslibFrontier.Complexity.FiniteCSP

open Cslib.Complexity Cslib.Logic Cslib.Logic.PL Turing.MultiTapeTM

universe u v w

/-! ### Invariance of `NPComplete` under polynomial-time equivalence -/

/-- `NP`-completeness transfers along polynomial-time many-one equivalence. -/
theorem npComplete_of_polyTimeEquiv {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (heq : PolyTimeEquiv encA encB A B) (hB : NPComplete encB B) :
    NPComplete encA A :=
  ⟨heq.mem_NP_iff.mpr hB.1, hB.2.trans heq.2⟩

/-- Two polynomial-time many-one equivalent problems are simultaneously `NP`-complete or not. -/
theorem npComplete_iff_of_polyTimeEquiv {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {A : Set α} {B : Set β} (heq : PolyTimeEquiv encA encB A B) :
    NPComplete encA A ↔ NPComplete encB B :=
  ⟨npComplete_of_polyTimeEquiv heq.symm, npComplete_of_polyTimeEquiv heq⟩

/-! ### Weak near-unanimity (WNU) operations -/

/-- An operation `f : (Fin m → A) → A` is a *weak near-unanimity* (WNU) operation if `m ≥ 2` and
`f(y, x, …, x) = f(x, y, …, x) = ⋯ = f(x, …, x, y)` for all `x y : A`. -/
def IsWeakNearUnanimity {A : Type u} {m : ℕ} (f : (Fin m → A) → A) : Prop :=
  2 ≤ m ∧ ∀ (x y : A) (i j : Fin m),
    f (Function.update (fun _ ↦ x) i y) = f (Function.update (fun _ ↦ x) j y)

theorem isWeakNearUnanimity_iff {A : Type u} {m : ℕ} (f : (Fin m → A) → A) :
    IsWeakNearUnanimity f ↔
      2 ≤ m ∧ ∀ (x y : A) (i j : Fin m),
        f (Function.update (fun _ ↦ x) i y) = f (Function.update (fun _ ↦ x) j y) :=
  Iff.rfl

theorem IsWeakNearUnanimity.two_le {A : Type u} {m : ℕ} {f : (Fin m → A) → A}
    (hf : IsWeakNearUnanimity f) : 2 ≤ m :=
  hf.1

theorem IsWeakNearUnanimity.pos {A : Type u} {m : ℕ} {f : (Fin m → A) → A}
    (hf : IsWeakNearUnanimity f) : 0 < m :=
  lt_of_lt_of_le Nat.zero_lt_two hf.1

theorem IsWeakNearUnanimity.update_eq {A : Type u} {m : ℕ} {f : (Fin m → A) → A}
    (hf : IsWeakNearUnanimity f) (x y : A) (i j : Fin m) :
    f (Function.update (fun _ ↦ x) i y) = f (Function.update (fun _ ↦ x) j y) :=
  hf.2 x y i j

/-- Any constant operation of arity `m ≥ 2` is a WNU operation. -/
theorem isWeakNearUnanimity_const {A : Type u} {m : ℕ} (hm : 2 ≤ m) (c : A) :
    IsWeakNearUnanimity (fun _ : Fin m → A ↦ c) :=
  ⟨hm, fun _ _ _ _ ↦ rfl⟩

/-- Any commutative binary operation defines a 2-ary WNU operation. -/
theorem isWeakNearUnanimity_binary_of_comm {A : Type u} (op : A → A → A)
    (hcomm : ∀ x y, op x y = op y x) :
    IsWeakNearUnanimity (fun a : Fin 2 → A ↦ op (a 0) (a 1)) := by
  rw [isWeakNearUnanimity_iff]
  refine ⟨le_rfl, fun x y i j ↦ ?_⟩
  fin_cases i <;> fin_cases j <;> simp [hcomm]

/-- Any ternary majority operation is a WNU operation. -/
theorem isWeakNearUnanimity_of_majority {A : Type u} {f : (Fin 3 → A) → A}
    (h0 : ∀ x y, f ![y, x, x] = x) (h1 : ∀ x y, f ![x, y, x] = x)
    (h2 : ∀ x y, f ![x, x, y] = x) :
    IsWeakNearUnanimity f := by
  have hval : ∀ (x y : A) (i : Fin 3), f (Function.update (fun _ ↦ x) i y) = x := by
    intro x y i
    fin_cases i
    · convert h0 x y; ext k; fin_cases k <;> rfl
    · convert h1 x y; ext k; fin_cases k <;> rfl
    · convert h2 x y; ext k; fin_cases k <;> rfl
  exact ⟨by omega, fun x y i j ↦ (hval x y i).trans (hval x y j).symm⟩

/-- Any ternary minority operation is a WNU operation. -/
theorem isWeakNearUnanimity_of_minority {A : Type u} {f : (Fin 3 → A) → A}
    (h0 : ∀ x y, f ![y, x, x] = y) (h1 : ∀ x y, f ![x, y, x] = y)
    (h2 : ∀ x y, f ![x, x, y] = y) :
    IsWeakNearUnanimity f := by
  have hval : ∀ (x y : A) (i : Fin 3), f (Function.update (fun _ ↦ x) i y) = y := by
    intro x y i
    fin_cases i
    · convert h0 x y; ext k; fin_cases k <;> rfl
    · convert h1 x y; ext k; fin_cases k <;> rfl
    · convert h2 x y; ext k; fin_cases k <;> rfl
  exact ⟨by omega, fun x y i j ↦ (hval x y i).trans (hval x y j).symm⟩

/-- No coordinate projection on a nontrivial carrier is a WNU operation. -/
theorem not_isWeakNearUnanimity_proj {A : Type u} [Nontrivial A] {m : ℕ} (i : Fin m) :
    ¬ IsWeakNearUnanimity (fun a : Fin m → A ↦ a i) := by
  intro hf
  have hm := hf.two_le
  obtain ⟨x, y, hxy⟩ := exists_pair_ne A
  let j : Fin m := if i.1 = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hji : j ≠ i := by
    intro h
    have hv : j.1 = i.1 := congrArg Fin.val h
    by_cases hi0 : i.1 = 0 <;> simp [j, hi0] at hv
    exact hi0 hv.symm
  have heq := hf.update_eq x y i j
  simp only [Function.update_self, Function.update_of_ne hji.symm] at heq
  exact hxy heq.symm

/-- No negated Boolean coordinate projection is a WNU operation. -/
theorem not_isWeakNearUnanimity_negProj {m : ℕ} (i : Fin m) :
    ¬ IsWeakNearUnanimity (fun a : Fin m → Bool ↦ !(a i)) := by
  intro hf
  have hm := hf.two_le
  let j : Fin m := if i.1 = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hji : j ≠ i := by
    intro h
    have hv : j.1 = i.1 := congrArg Fin.val h
    by_cases hi0 : i.1 = 0 <;> simp [j, hi0] at hv
    exact hi0 hv.symm
  have heq := hf.update_eq false true i j
  simp only [Function.update_self, Function.update_of_ne hji.symm] at heq
  exact Bool.false_ne_true heq

/-! ### Fixed-template finite-domain constraint languages -/

/-- A fixed-arity constraint language on domain `D` indexed by relation alphabet `Rel`. -/
@[ext]
structure Language (D : Type u) (Rel : Type v) where
  /-- Declared arity of each relation symbol. -/
  arity : Rel → ℕ
  /-- Boolean semantics evaluated on lists of length `arity r`. -/
  sem : Rel → List D → Bool

namespace Language

section General

variable {D : Type u} {Rel : Type v}

instance instInhabited : Inhabited (Language D Rel) :=
  ⟨⟨fun _ ↦ 0, fun _ _ ↦ true⟩⟩

/-- The `arity r`-ary relation on `D` interpreted by symbol `r : Rel`. -/
def relation (Γ : Language D Rel) (r : Rel) : Set (Fin (Γ.arity r) → D) :=
  {a | Γ.sem r (List.ofFn a) = true}

theorem mem_relation_iff (Γ : Language D Rel) (r : Rel) (a : Fin (Γ.arity r) → D) :
    a ∈ Γ.relation r ↔ Γ.sem r (List.ofFn a) = true :=
  Iff.rfl

/-- Evaluation of a well-formed constraint agrees with membership in `Γ.relation c.rel`. -/
theorem constraint_eval_eq_true_iff {V : Type*} (Γ : Language D Rel) {c : Constraint Rel V}
    (hc : c.scope.length = Γ.arity c.rel) (σ : V → D) (v₀ : V) :
    c.eval Γ.sem σ = true ↔
      (fun i : Fin (Γ.arity c.rel) ↦ σ (c.scope.getD i.1 v₀)) ∈ Γ.relation c.rel := by
  change Γ.sem c.rel (c.scope.map σ) = true ↔
    Γ.sem c.rel (List.ofFn fun i : Fin (Γ.arity c.rel) ↦ σ (c.scope.getD i.1 v₀)) = true
  rw [List.ofFn_getD_eq_map_of_length σ v₀ hc]

/-- Evaluation of a well-formed CSP agrees with membership in every constraint relation. -/
theorem csp_eval_eq_true_iff {V : Type*} (Γ : Language D Rel) {F : CSP Rel V}
    (hF : F.WellFormed Γ.arity) (σ : V → D) (v₀ : V) :
    F.eval Γ.sem σ = true ↔
      ∀ c ∈ F, (fun i : Fin (Γ.arity c.rel) ↦ σ (c.scope.getD i.1 v₀)) ∈ Γ.relation c.rel := by
  simp only [Cslib.Logic.PL.CSP.eval, List.all_eq_true]
  exact forall₂_congr fun c hc ↦ Γ.constraint_eval_eq_true_iff (hF c hc) σ v₀

/-- `Γ.HasPolymorphism f` asserts that `f : (J → D) → D` preserves every relation of `Γ`. -/
def HasPolymorphism (Γ : Language D Rel) {J : Type*} (f : (J → D) → D) : Prop :=
  ∀ r : Rel, IsPolymorphism f (Γ.relation r)

/-- Every polymorphism of `Γ` preserves the solution set of every well-formed CSP over `Γ`. -/
theorem isPolymorphism_solutions {V J : Type*} (Γ : Language D Rel)
    {f : (J → D) → D} (hf : Γ.HasPolymorphism f) {F : CSP Rel V} (hF : F.WellFormed Γ.arity) :
    IsPolymorphism f {σ : V → D | F.eval Γ.sem σ = true} := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
  · intro a ha
    rw [Set.mem_ofPred_eq]
    simp only [Cslib.Logic.PL.CSP.eval, List.all_eq_true]
    intro c hc
    have hnil : c.scope = [] := List.eq_nil_iff_forall_not_mem.mpr fun v _ ↦ hV.false v
    have h0 : Γ.arity c.rel = 0 := by rw [← hF c hc, hnil]; rfl
    have hmem := hf c.rel (fun _ i ↦ (Nat.not_lt_zero i.1 (h0 ▸ i.2)).elim) fun j ↦ by
      have hj := (List.all_eq_true.mp (ha j)) c hc
      change Γ.sem c.rel (List.ofFn fun i : Fin (Γ.arity c.rel) ↦ _) = true
      have hof : (List.ofFn fun i : Fin (Γ.arity c.rel) ↦
          (Nat.not_lt_zero i.1 (h0 ▸ i.2)).elim) = ([] : List D) := by
        rw [List.ofFn_eq_nil_iff]; exact h0
      rw [hof]; simpa [Constraint.eval, hnil] using hj
    change Γ.sem c.rel (c.scope.map _) = true
    have hof : (List.ofFn fun i : Fin (Γ.arity c.rel) ↦
        f fun _ ↦ (Nat.not_lt_zero i.1 (h0 ▸ i.2)).elim) = ([] : List D) := by
      rw [List.ofFn_eq_nil_iff]; exact h0
    change Γ.sem c.rel (List.ofFn _) = true at hmem
    rw [hof] at hmem; simpa [hnil] using hmem
  · intro a ha
    rw [Set.mem_ofPred_eq, Γ.csp_eval_eq_true_iff hF _ v₀]
    intro c hc
    exact hf c.rel (fun j i ↦ a j (c.scope.getD i.1 v₀)) fun j ↦
      (Γ.csp_eval_eq_true_iff hF (a j) v₀).mp (ha j) c hc

/-- A constraint language `Γ` admits a WNU polymorphism if some WNU operation preserves `Γ`. -/
def AdmitsWNU (Γ : Language D Rel) : Prop :=
  ∃ (m : ℕ) (f : (Fin m → D) → D), IsWeakNearUnanimity f ∧ Γ.HasPolymorphism f

/-- `Γ` contains all constant relations if every singleton `{a}` is represented in `Γ`. -/
def ContainsConstants (Γ : Language D Rel) : Prop :=
  ∀ a : D, ∃ r : Rel, ∃ _ : Γ.arity r = 1,
    ∀ x : Fin (Γ.arity r) → D, x ∈ Γ.relation r ↔ x ⟨0, by omega⟩ = a

/-- Expand `Γ` by indexed unary singleton relations `{(x) | x = c i}`. -/
noncomputable def withUnarySingletons (Γ : Language D Rel) {ι : Type w} (c : ι → D) :
    Language D (Rel ⊕ ι) where
  arity := Sum.elim Γ.arity fun _ ↦ 1
  sem := by
    classical
    exact Sum.elim Γ.sem fun i l ↦
      match l with
      | [x] => decide (x = c i)
      | _ => false

@[simp]
theorem withUnarySingletons_sem_inl (Γ : Language D Rel) {ι : Type w} (c : ι → D)
    (r : Rel) (l : List D) :
    (Γ.withUnarySingletons c).sem (.inl r) l = Γ.sem r l := by
  classical simp [withUnarySingletons]

@[simp]
theorem withUnarySingletons_sem_inr_singleton (Γ : Language D Rel) {ι : Type w} (c : ι → D)
    (i : ι) (x : D) :
    ((Γ.withUnarySingletons c).sem (.inr i) [x] = true) ↔ x = c i := by
  classical simp [withUnarySingletons]

/-- The full constant expansion `Γ* = Γ ∪ {(x = a) | a ∈ D}`. -/
noncomputable def withConstants (Γ : Language D Rel) : Language D (Rel ⊕ D) :=
  Γ.withUnarySingletons id

/-- `Γ*` contains all constant relations on `D`. -/
theorem containsConstants_withConstants (Γ : Language D Rel) :
    Γ.withConstants.ContainsConstants := fun a ↦
  ⟨.inr a, rfl, fun x ↦ by
    rw [mem_relation_iff]
    have hof : List.ofFn x = [x ⟨0, by simp [withConstants, withUnarySingletons]⟩] := rfl
    rw [hof]; exact Γ.withUnarySingletons_sem_inr_singleton id a _⟩

/-- The `m`-th direct-power constraint language `Γ^m = {R^m | R ∈ Γ}` on domain `Fin m → D`. -/
def power (Γ : Language D Rel) (m : ℕ) : Language (Fin m → D) Rel where
  arity := Γ.arity
  sem r l := (List.finRange m).all fun i ↦ Γ.sem r (l.map fun α ↦ α i)

@[simp]
theorem power_arity (Γ : Language D Rel) (m : ℕ) (r : Rel) :
    (Γ.power m).arity r = Γ.arity r := by
  rfl

/-- Coordinatewise characterization of `R^m`. -/
theorem mem_power_relation_iff (Γ : Language D Rel) (m : ℕ) (r : Rel)
    (a : Fin ((Γ.power m).arity r) → Fin m → D) :
    a ∈ (Γ.power m).relation r ↔
      ∀ i : Fin m, (fun j : Fin (Γ.arity r) ↦ a ⟨j.1, by simp [j.2]⟩ i) ∈ Γ.relation r := by
  rw [mem_relation_iff]
  change ((List.finRange m).all fun i ↦ Γ.sem r ((List.ofFn a).map fun α ↦ α i)) = true ↔ _
  simp only [List.all_eq_true, List.mem_finRange, forall_const]
  exact forall_congr' fun i ↦ by rw [List.map_ofFn, mem_relation_iff]; rfl

end General

/-! ### Decision problem `CSP(Γ)` and computational complexity -/

section Complexity

variable {D : Type u} {Rel : Type}

/-- Exact-arity decision problem `CSP(Γ)`; coincides with `CSPSAT` when `D = Bool`. -/
def cspsat (Γ : Language D Rel) : Set (CSP Rel ℕ) :=
  {F | F.WellFormed Γ.arity ∧ F.Satisfiable Γ.sem}

theorem mem_cspsat_iff (Γ : Language D Rel) (F : CSP Rel ℕ) :
    F ∈ Γ.cspsat ↔ F.WellFormed Γ.arity ∧ F.Satisfiable Γ.sem :=
  Iff.rfl

theorem bool_cspsat_eq (Γ : Language Bool Rel) :
    Γ.cspsat = CSPSAT Γ.arity Γ.sem := by
  rfl

/-- Guarded polynomial-time compilation out of `Γ.cspsat`. -/
theorem cspsat_polyTimeReducible_of_guard [Finite Rel] (Γ : Language D Rel)
    (encRel : Rel ↪ List Bool) {β : Type} {encB : β ↪ List Bool} {B : Set β}
    {compile : CSP Rel ℕ → β} (reject : β)
    (hcompile : ComputableInPolyTime compile (encCSP encRel encNat) encB)
    (hcorrect : ∀ F, F.WellFormed Γ.arity → (F.Satisfiable Γ.sem ↔ compile F ∈ B))
    (hreject : reject ∉ B) :
    PolyTimeReducible (encCSP encRel encNat) encB Γ.cspsat B :=
  .of_guard reject (Cslib.Complexity.CSP.computableInPolyTime_validArity encRel Γ.arity)
    hcompile hreject fun F ↦ by
      rw [mem_cspsat_iff, Cslib.Logic.PL.CSP.validArity_eq_true_iff]
      exact and_congr_right (hcorrect F)

/-- When `Γ` contains all constant relations, `CSP(Γ*) ≤_m^p CSP(Γ)`. -/
theorem withConstants_cspsat_polyTimeReducible {D : Type} [Finite D] [Nonempty D] [Finite Rel]
    (Γ : Language D Rel) (hconst : Γ.ContainsConstants)
    (encRel : Rel ↪ List Bool) (encD : D ↪ List Bool) :
    PolyTimeReducible (encCSP (encSum encRel encD) encNat) (encCSP encRel encNat)
      Γ.withConstants.cspsat Γ.cspsat := by
  classical
  choose sym hsym_ar hsym_rel using hconst
  obtain ⟨d₀⟩ := ‹Nonempty D›
  let mapRel : Rel ⊕ D → Rel := Sum.elim id sym
  let compile : CSP (Rel ⊕ D) ℕ → CSP Rel ℕ := List.map fun c ↦ ⟨mapRel c.rel, c.scope⟩
  have hcompile : ComputableInPolyTime compile
      (encCSP (encSum encRel encD) encNat) (encCSP encRel encNat) :=
    ComputableInPolyTime.mapWithInput ComputableInPolyTime.id'
      (encConstraint_mk_polyTime
        ((ComputableInPolyTime.of_finite mapRel).comp
          (encConstraint_rel_polyTime (ComputableInPolyTime.snd _ _)))
        (encConstraint_scope_polyTime (ComputableInPolyTime.snd _ _)))
  let reject : CSP Rel ℕ := [⟨sym d₀, List.replicate (Γ.arity (sym d₀) + 1) 0⟩]
  have hrej : reject ∉ Γ.cspsat := fun ⟨hF, _⟩ ↦ by
    have h := hF ⟨sym d₀, List.replicate (Γ.arity (sym d₀) + 1) 0⟩ (List.mem_singleton.mpr rfl)
    simp at h
  refine Γ.withConstants.cspsat_polyTimeReducible_of_guard (encSum encRel encD)
    reject hcompile ?_ hrej
  intro F hF
  have hWF : (compile F).WellFormed Γ.arity := by
    intro c hc
    obtain ⟨⟨r | a, vs⟩, hc₀, rfl⟩ := List.mem_map.mp hc
    · exact hF _ hc₀
    · simpa [mapRel, hsym_ar a, withConstants, withUnarySingletons] using hF _ hc₀
  rw [mem_cspsat_iff, and_iff_right hWF]
  refine exists_congr fun σ ↦ ?_
  simp only [compile, Cslib.Logic.PL.CSP.eval, List.all_map, List.all_eq_true]
  refine forall₂_congr fun c hc ↦ ?_
  have hlen := hF c hc
  rcases c with ⟨r | a, vs⟩
  · simp [Constraint.eval, mapRel, withConstants]
  · rcases vs with _ | ⟨v, _ | _⟩ <;>
      simp [withConstants, withUnarySingletons] at hlen
    have hrel := hsym_rel a fun _ ↦ σ v
    rw [mem_relation_iff] at hrel
    have hof : List.ofFn (fun _ : Fin (Γ.arity (sym a)) ↦ σ v) = [σ v] := by simp [hsym_ar a]
    rw [hof] at hrel
    simp only [Constraint.eval, List.map_cons, List.map_nil, mapRel, withConstants,
      withUnarySingletons_sem_inr_singleton, id_eq]
    exact hrel.symm

private def decodeOneHot (s : ℕ) (bits : List Bool) : Option (Fin s) :=
  if bits.length = s ∧ bits.count true = 1 then
    let idx := bits.idxOf true
    if h : idx < s then some ⟨idx, h⟩ else none
  else
    none

private lemma filter_range_eq_singleton {s m : ℕ} (hm : m < s) :
    (List.range s).filter (fun j ↦ decide (m = j)) = [m] := by
  induction s with
  | zero => omega
  | succ s ih =>
    rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hm) with rfl | hlt
    · have hnil : (List.range m).filter (fun j ↦ decide (m = j)) = [] :=
        List.filter_eq_nil_iff.mpr fun j hj ↦ by simp [Nat.ne_of_gt (List.mem_range.mp hj)]
      simp [hnil]
    · simp [ih hlt, show ¬ m = s by omega]

private lemma idxOf_true_range_eq {s m : ℕ} (hm : m < s) :
    ((List.range s).map fun j ↦ decide (m = j)).idxOf true = m := by
  have haux : ∀ (k len : ℕ), k ≤ m → m < k + len →
      (((List.range len).map fun t ↦ decide (m = k + t)).idxOf true) = m - k := by
    intro k len
    induction len generalizing k with
    | zero => intro _ h; omega
    | succ len ih =>
      intro hkm hlt
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      rcases eq_or_lt_of_le hkm with rfl | hgt
      · simp
      · rw [List.idxOf_cons_ne _ (by simp [Nat.ne_of_gt hgt])]
        have hfn : ((fun t ↦ decide (m = k + t)) ∘ Nat.succ) =
            fun t ↦ decide (m = (k + 1) + t) :=
          funext fun t ↦ Bool.eq_iff_iff.mpr ⟨fun h ↦ by simp at h ⊢; omega,
            fun h ↦ by simp at h ⊢; omega⟩
        rw [hfn, ih (k + 1) (by omega) (by omega)]; omega
  simpa using haux 0 s (Nat.zero_le m) (by simpa using hm)

private lemma decodeOneHot_tabulate {s : ℕ} (i : Fin s) :
    decodeOneHot s ((List.range s).map fun j ↦ decide (i.1 = j)) = some i := by
  have hcount : ((List.range s).map fun j ↦ decide (i.1 = j)).count true = 1 := by
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    have hfilt : (List.range s).filter ((· == true) ∘ fun j ↦ decide (i.1 = j)) =
        (List.range s).filter (fun j ↦ decide (i.1 = j)) :=
      List.filter_congr fun j _ ↦ by simp
    rw [hfilt, filter_range_eq_singleton i.2]; rfl
  simp [decodeOneHot, hcount, idxOf_true_range_eq i.2, i.2]

private def decodeOneHotTuple (s : ℕ) : ℕ → List Bool → Option (List (Fin s))
  | 0, [] => some []
  | 0, _ :: _ => none
  | k + 1, bits =>
      match decodeOneHot s (bits.take s), decodeOneHotTuple s k (bits.drop s) with
      | some d, some ds => some (d :: ds)
      | _, _ => none

private lemma decodeOneHotTuple_map_block {s : ℕ} (vs : List ℕ) (τ : ℕ → Bool)
    (d : ℕ → Fin s)
    (hd : ∀ v ∈ vs, decodeOneHot s ((List.range s).map fun j ↦ τ (s * v + j)) = some (d v)) :
    decodeOneHotTuple s vs.length
      ((vs.flatMap fun v ↦ (List.range s).map fun j ↦ s * v + j).map τ) =
      some (vs.map d) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hhd := hd v List.mem_cons_self
    have htl := ih fun u hu ↦ hd u (List.mem_cons_of_mem v hu)
    let chunk : List Bool := (List.range s).map fun j ↦ τ (s * v + j)
    let rest : List Bool := (vs.flatMap fun u ↦ (List.range s).map fun j ↦ s * u + j).map τ
    have hlen : chunk.length = s := by simp [chunk]
    have hmap : ((v :: vs).flatMap fun u ↦ (List.range s).map fun j ↦ s * u + j).map τ =
        chunk ++ rest := by simp [chunk, rest, List.map_map, Function.comp_def]
    rw [hmap, List.length_cons, List.map_cons]
    change (match decodeOneHot s ((chunk ++ rest).take s),
        decodeOneHotTuple s vs.length ((chunk ++ rest).drop s) with
      | some a, some as => some (a :: as)
      | _, _ => none) = some (d v :: vs.map d)
    rw [List.take_left' hlen, List.drop_left' hlen, hhd, htl]

/-- Every fixed-template CSP over a finite nonempty domain `D` and finite relation alphabet `Rel`
belongs to `NP`, via polynomial-time one-hot compilation into Boolean `CSPSAT`. -/
theorem cspsat_mem_NP [Finite D] [Nonempty D] [Finite Rel] (Γ : Language D Rel)
    (encRel : Rel ↪ List Bool) :
    Γ.cspsat ∈ NP (encCSP encRel encNat) := by
  classical
  have := Fintype.ofFinite D
  let s := Fintype.card D
  have hs : 0 < s := Fintype.card_pos
  let eD : D ≃ Fin s := Fintype.equivFin D
  obtain ⟨d₀⟩ := ‹Nonempty D›
  let bArity : Rel ⊕ Unit → ℕ := Sum.elim (fun r ↦ s * Γ.arity r) (fun _ ↦ s)
  let bSem : Rel ⊕ Unit → List Bool → Bool := Sum.elim
    (fun r bits ↦ match decodeOneHotTuple s (Γ.arity r) bits with
      | some ds => Γ.sem r (ds.map eD.symm)
      | none => false)
    (fun _ bits ↦ (decodeOneHot s bits).isSome)
  let encBRel : Rel ⊕ Unit ↪ List Bool := encSum encRel (encFinite Unit)
  let block : ℕ → List ℕ := fun v ↦ (List.range s).map fun j ↦ s * v + j
  have hblock : ComputableInPolyTime block encNat (encList encNat) :=
    ComputableInPolyTime.mapConst (List.range s) fun j _ ↦
      ComputableInPolyTime.binary_add'
        (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const s) ComputableInPolyTime.id')
        (ComputableInPolyTime.const j)
  let compileConstraint : Constraint Rel ℕ → List (Constraint (Rel ⊕ Unit) ℕ) := fun c ↦
    ⟨Sum.inl c.rel, c.scope.flatMap block⟩ :: c.scope.map fun v ↦ ⟨Sum.inr (), block v⟩
  have hcompC : ComputableInPolyTime compileConstraint
      (encConstraint encRel encNat) (encCSP encBRel encNat) := by
    have hscope := encConstraint_scope_polyTime
      (ComputableInPolyTime.id' (encIn := encConstraint encRel encNat))
    have hrel : ComputableInPolyTime (fun c : Constraint Rel ℕ ↦ (Sum.inl c.rel : Rel ⊕ Unit))
        (encConstraint encRel encNat) encBRel :=
      (ComputableInPolyTime.sumInl encRel (encFinite Unit)).comp
        (encConstraint_rel_polyTime ComputableInPolyTime.id')
    have hflat : ComputableInPolyTime (fun c : Constraint Rel ℕ ↦ c.scope.flatMap block)
        (encConstraint encRel encNat) (encList encNat) :=
      ComputableInPolyTime.flatMapWithInput hscope
        (hblock.comp (ComputableInPolyTime.snd _ _))
    have hhead := encConstraint_mk_polyTime (encRel := encBRel) (encV := encNat) hrel hflat
    have hconstInr : ComputableInPolyTime
        (fun _ : Constraint Rel ℕ × ℕ ↦ (Sum.inr () : Rel ⊕ Unit))
        (encPair (encConstraint encRel encNat) encNat) encBRel :=
      ComputableInPolyTime.const (Sum.inr ())
    have htail : ComputableInPolyTime
        (fun c : Constraint Rel ℕ ↦
          c.scope.map fun v ↦ (⟨Sum.inr (), block v⟩ : Constraint (Rel ⊕ Unit) ℕ))
        (encConstraint encRel encNat) (encCSP encBRel encNat) :=
      ComputableInPolyTime.mapWithInput hscope
        (encConstraint_mk_polyTime hconstInr (hblock.comp (ComputableInPolyTime.snd _ _)))
    exact (ComputableInPolyTime.cons _).comp (hhead.prod htail)
  let compile : CSP Rel ℕ → CSP (Rel ⊕ Unit) ℕ := fun F ↦ F.flatMap compileConstraint
  have hcompile : ComputableInPolyTime compile (encCSP encRel encNat) (encCSP encBRel encNat) :=
    ComputableInPolyTime.flatMapWithInput ComputableInPolyTime.id'
      (hcompC.comp (ComputableInPolyTime.snd _ _))
  let reject : CSP (Rel ⊕ Unit) ℕ := [⟨Sum.inr (), []⟩]
  have hreject : reject ∉ CSPSAT bArity bSem := fun ⟨hWF, _⟩ ↦ by
    have h : 0 = s := hWF ⟨Sum.inr (), []⟩ (List.mem_singleton.mpr rfl)
    omega
  have hred : PolyTimeReducible (encCSP encRel encNat) (encCSP encBRel encNat)
      Γ.cspsat (CSPSAT bArity bSem) := by
    refine Γ.cspsat_polyTimeReducible_of_guard encRel reject hcompile ?_ hreject
    intro F hF
    have hWF : (compile F).WellFormed bArity := by
      intro c' hc'
      simp only [compile, List.mem_flatMap, compileConstraint, List.mem_cons,
        List.mem_map] at hc'
      obtain ⟨c, hc, rfl | ⟨v, _, rfl⟩⟩ := hc'
      · have hlen : (c.scope.flatMap block).length = s * c.scope.length := by
          induction c.scope with
          | nil => simp
          | cons _ _ ih =>
            simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, block,
              List.length_map, List.length_range]; ring
        rw [hlen, hF c hc]; rfl
      · simp [bArity, block]
    rw [CSPSAT.mem_iff, and_iff_right hWF]
    constructor
    · rintro ⟨σ, hσ⟩
      let τ : ℕ → Bool := fun n ↦ decide ((eD (σ (n / s))).1 = n % s)
      refine ⟨τ, ?_⟩
      simp only [Cslib.Logic.PL.CSP.eval, List.all_eq_true] at hσ ⊢
      have hchunk : ∀ v, (List.range s).map (fun j ↦ τ (s * v + j)) =
          (List.range s).map fun j ↦ decide ((eD (σ v)).1 = j) := fun v ↦
        List.map_congr_left fun j hj ↦ by
          have hjs := List.mem_range.mp hj
          have hd : (s * v + j) / s = v := by
            rw [add_comm, Nat.add_mul_div_left j v hs, Nat.div_eq_of_lt hjs, zero_add]
          have hm : (s * v + j) % s = j := by
            rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjs]
          simp only [τ, hd, hm]
      intro c' hc'
      simp only [compile, List.mem_flatMap, compileConstraint, List.mem_cons,
        List.mem_map] at hc'
      obtain ⟨c, hc, rfl | ⟨v, _, rfl⟩⟩ := hc'
      · simp only [Constraint.eval, bSem, Sum.elim_inl, ← hF c hc]
        have hdec := decodeOneHotTuple_map_block c.scope τ (fun v ↦ eD (σ v)) fun v _ ↦ by
          rw [hchunk v, decodeOneHot_tabulate]
        change (match decodeOneHotTuple s c.scope.length
              ((c.scope.flatMap fun v ↦ (List.range s).map fun j ↦ s * v + j).map τ) with
            | some ds => Γ.sem c.rel (ds.map eD.symm)
            | none => false) = true
        rw [hdec]; dsimp only; rw [List.map_map]
        rw [show List.map (eD.symm ∘ fun v ↦ eD (σ v)) c.scope = c.scope.map σ from
          List.map_congr_left fun v _ ↦ eD.symm_apply_apply (σ v)]
        exact hσ c hc
      · have hbm : (block v).map τ = (List.range s).map fun j ↦ τ (s * v + j) := by
          simp [block, List.map_map, Function.comp_def]
        change (decodeOneHot s ((block v).map τ)).isSome = true
        rw [hbm, hchunk v, decodeOneHot_tabulate]; rfl
    · rintro ⟨τ, hτ⟩
      simp only [Cslib.Logic.PL.CSP.eval, List.all_eq_true] at hτ
      let pick : ℕ → Fin s := fun v ↦
        (decodeOneHot s ((List.range s).map fun j ↦ τ (s * v + j))).getD (eD d₀)
      refine ⟨fun v ↦ eD.symm (pick v), ?_⟩
      simp only [Cslib.Logic.PL.CSP.eval, List.all_eq_true]
      intro c hc
      have hpick : ∀ v ∈ c.scope,
          decodeOneHot s ((List.range s).map fun j ↦ τ (s * v + j)) = some (pick v) := by
        intro v hv
        have his := hτ ⟨Sum.inr (), block v⟩
          (List.mem_flatMap.mpr ⟨c, hc, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨v, hv, rfl⟩)⟩)
        have hbm : (block v).map τ = (List.range s).map fun j ↦ τ (s * v + j) := by
          simp [block, List.map_map, Function.comp_def]
        change (decodeOneHot s ((block v).map τ)).isSome = true at his
        rw [hbm] at his
        obtain ⟨idx, hidx⟩ := Option.isSome_iff_exists.mp his
        simp only [pick, hidx, Option.getD_some]
      have hmain := hτ ⟨Sum.inl c.rel, c.scope.flatMap block⟩
        (List.mem_flatMap.mpr ⟨c, hc, List.mem_cons_self⟩)
      have hdec := decodeOneHotTuple_map_block c.scope τ pick hpick
      change (match decodeOneHotTuple s (Γ.arity c.rel)
            ((c.scope.flatMap fun v ↦ (List.range s).map fun j ↦ s * v + j).map τ) with
          | some ds => Γ.sem c.rel (ds.map eD.symm)
          | none => false) = true at hmain
      rw [← hF c hc, hdec] at hmain
      simpa only [Constraint.eval, List.map_map, Function.comp_def] using hmain
  exact hred.mem_NP (CSPSAT.mem_NP encBRel bArity bSem)

/-- Every fixed-template CSP preserved by a common unary constant lies in `P`. -/
theorem cspsat_mem_P_of_unaryConst [Finite Rel] (Γ : Language D Rel)
    (encRel : Rel ↪ List Bool) (b : D)
    (hb : Γ.HasPolymorphism (fun _ : Fin 1 → D ↦ b)) :
    Γ.cspsat ∈ P (encCSP encRel encNat) := by
  classical
  let possible : Rel → Bool := fun r ↦ decide (Γ.relation r).Nonempty
  let solver : CSP Rel ℕ → Bool := fun F ↦ F.validArity Γ.arity && F.all fun c ↦ possible c.rel
  have hpoly : ComputableInPolyTime solver (encCSP encRel encNat) encBool :=
    ComputableInPolyTime.bool_and.comp
      ((Cslib.Complexity.CSP.computableInPolyTime_validArity encRel Γ.arity).prod
        (ComputableInPolyTime.allWithInput ComputableInPolyTime.id'
          ((ComputableInPolyTime.of_finite possible).comp
            (encConstraint_rel_polyTime (ComputableInPolyTime.snd _ _)))))
  refine ⟨solver, hpoly, fun F ↦ ?_⟩
  simp only [mem_cspsat_iff, solver, Bool.and_eq_true, Cslib.Logic.PL.CSP.validArity_eq_true_iff,
    List.all_eq_true, possible, decide_eq_true_eq]
  refine ⟨fun ⟨hF, σ, hσ⟩ ↦ ⟨hF, fun c hc ↦
    ⟨_, (Γ.csp_eval_eq_true_iff hF σ 0).mp hσ c hc⟩⟩, ?_⟩
  rintro ⟨hF, hpos⟩
  refine ⟨hF, fun _ ↦ b, (Γ.csp_eval_eq_true_iff hF (fun _ ↦ b) 0).mpr fun c hc ↦ ?_⟩
  obtain ⟨a, ha⟩ := hpos c hc
  exact hb c.rel (fun _ ↦ a) fun _ ↦ ha

/-- Every fixed-template CSP on a 1-element domain admits a WNU polymorphism and lies in `P`. -/
theorem cspsat_mem_P_of_subsingleton [Subsingleton D] [Nonempty D] [Finite Rel]
    (Γ : Language D Rel) (encRel : Rel ↪ List Bool) :
    Γ.AdmitsWNU ∧ Γ.cspsat ∈ P (encCSP encRel encNat) := by
  obtain ⟨b⟩ := ‹Nonempty D›
  have hpol : ∀ m : ℕ, 0 < m → Γ.HasPolymorphism (fun _ : Fin m → D ↦ b) := by
    intro m hm r a ha
    rw [show (fun _ : Fin (Γ.arity r) ↦ b) = a ⟨0, hm⟩ from
      funext fun _ ↦ Subsingleton.elim _ _]
    exact ha ⟨0, hm⟩
  exact ⟨⟨2, fun _ ↦ b, isWeakNearUnanimity_const le_rfl b, hpol 2 Nat.zero_lt_two⟩,
    Γ.cspsat_mem_P_of_unaryConst encRel b (hpol 1 Nat.zero_lt_one)⟩

/-- On `Bool`, admitting a WNU polymorphism is equivalent to admitting a Schaefer polymorphism. -/
theorem bool_admitsWNU_iff_hasSchaefer {Rel : Type v} (Γ : Language Bool Rel) :
    Γ.AdmitsWNU ↔ Cslib.Logic.PL.CSP.HasSchaeferPolymorphism Γ.arity Γ.sem := by
  constructor
  · rintro ⟨m, f, hwnu, hpol⟩
    by_contra hns
    obtain ⟨i, rfl | rfl⟩ :=
      Cslib.Logic.PL.CSP.projection_or_negation_of_not_hasSchaeferPolymorphism
        Γ.arity Γ.sem hns hwnu.pos hpol
    · exact not_isWeakNearUnanimity_proj i hwnu
    · exact not_isWeakNearUnanimity_negProj i hwnu
  · rintro (h | h | h | h | h | h)
    · exact ⟨2, fun _ ↦ false, isWeakNearUnanimity_const le_rfl false,
        fun r a ha ↦ h r (fun _ ↦ a 0) fun _ ↦ ha 0⟩
    · exact ⟨2, fun _ ↦ true, isWeakNearUnanimity_const le_rfl true,
        fun r a ha ↦ h r (fun _ ↦ a 0) fun _ ↦ ha 0⟩
    · exact ⟨2, fun a ↦ a 0 && a 1,
        isWeakNearUnanimity_binary_of_comm Bool.and Bool.and_comm, h⟩
    · exact ⟨2, fun a ↦ a 0 || a 1,
        isWeakNearUnanimity_binary_of_comm Bool.or Bool.or_comm, h⟩
    · refine ⟨3, Cslib.majority 3, isWeakNearUnanimity_of_majority ?_ ?_ ?_, h⟩ <;>
        (intro x y; cases x <;> cases y <;> decide)
    · refine ⟨3, Cslib.parity 3, isWeakNearUnanimity_of_minority ?_ ?_ ?_, h⟩ <;>
        (intro x y; cases x <;> cases y <;> decide)

/-- Complete Boolean WNU complexity dichotomy via Schaefer's theorem. -/
theorem bool_cspsat_dichotomy [Finite Rel] (Γ : Language Bool Rel) (encRel : Rel ↪ List Bool) :
    (Γ.AdmitsWNU → Γ.cspsat ∈ P (encCSP encRel encNat)) ∧
      (¬ Γ.AdmitsWNU → NPComplete (encCSP encRel encNat) Γ.cspsat) := by
  rw [Γ.bool_admitsWNU_iff_hasSchaefer, Γ.bool_cspsat_eq]
  exact CSPSAT.schaefer_dichotomy encRel Γ.arity Γ.sem

/-- The positive ternary Boolean not-all-equal language `NAE₃`. -/
def boolNAE3 : Language Bool Unit where
  arity _ := 3
  sem _ l :=
    match l with
    | [x, y, z] => !(x == y && y == z)
    | _ => false

/-- `boolNAE3` admits no weak near-unanimity polymorphism. -/
theorem not_admitsWNU_boolNAE3 : ¬ boolNAE3.AdmitsWNU := by
  rw [boolNAE3.bool_admitsWNU_iff_hasSchaefer]
  have hmem : ∀ x y z : Bool,
      ![x, y, z] ∈ Cslib.Logic.PL.CSP.booleanRelation boolNAE3.arity boolNAE3.sem () ↔
        (!(x == y && y == z)) = true := fun _ _ _ ↦ Iff.rfl
  rintro (h | h | h | h | h | h)
  · exact Bool.false_ne_true (h () (fun _ ↦ ![true, false, false]) fun _ ↦ (hmem _ _ _).mpr rfl)
  · exact Bool.false_ne_true (h () (fun _ ↦ ![true, false, false]) fun _ ↦ (hmem _ _ _).mpr rfl)
  · exact Bool.false_ne_true (h () ![![true, false, false], ![false, true, false]] fun i ↦ by
      fin_cases i <;> exact (hmem _ _ _).mpr rfl)
  · exact Bool.false_ne_true (h () ![![true, true, false], ![true, false, true]] fun i ↦ by
      fin_cases i <;> exact (hmem _ _ _).mpr rfl)
  · exact Bool.false_ne_true (h () ![![true, true, false], ![true, false, true],
      ![false, true, true]] fun i ↦ by fin_cases i <;> exact (hmem _ _ _).mpr rfl)
  · exact Bool.false_ne_true (h () ![![true, false, false], ![false, true, false],
      ![false, false, true]] fun i ↦ by fin_cases i <;> exact (hmem _ _ _).mpr rfl)

/-- `CSP(boolNAE3)` is `NP`-complete. -/
theorem cspsat_npComplete_boolNAE3 (encRel : Unit ↪ List Bool) :
    NPComplete (encCSP encRel encNat) boolNAE3.cspsat :=
  (boolNAE3.bool_cspsat_dichotomy encRel).2 not_admitsWNU_boolNAE3

end Complexity

end Language

end CslibFrontier.Complexity.FiniteCSP
