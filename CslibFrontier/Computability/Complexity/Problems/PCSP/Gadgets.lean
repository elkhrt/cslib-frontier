/-
Copyright (c) 2026 PanMath Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Complexity.Problems.PCSP.Minion

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FunProp

/-!
# Primitive-Positive Constructions and Gadget Reductions for Promise CSPs

This module formalizes finite relational instances of fixed-template promise constraint satisfaction
problems (`FinStructure`, `pcsp`), primitive-positive formulas (`PPFormula`), primitive-positive
constructions (`PPConstructible`), and the two fundamental theorems of Barto, Bulín, Krokhin, and
Opršal:

* **Algebraic characterization**: for
  finite templates `A, A'` and nonempty `B'`, `(A', B')` is pp-constructible from `(A, B)` if and
  only if there is a minion homomorphism `Pol(A, B) → Pol(A', B')`.
* **Gadget reductions**: a
  pp-construction from `(A, B)` to `(A', B')` induces a deterministic polynomial-time reduction
  from `PCSP(A', B')` to `PCSP(A, B)`, realized by gadget substitution and polynomial-time
  synchronous min-propagation to collapse equality atoms.

All results are proved under standard Lean axioms.

## Main definitions

* `Cslib.Complexity.PCSP.FinStructure`: an executable finite `r`-ary relational structure.
* `Cslib.Complexity.PCSP.encFinStructure`: unary-vertex, framed-tuple encoding of `FinStructure r`.
* `Cslib.Complexity.PCSP.pcsp`: the fixed-template promise CSP `PCSP(A, B)`.
* `Cslib.Complexity.PCSP.PPFormula`: a primitive-positive formula defining an `r'`-ary relation on
  a `d`-th power of an `r`-ary template.
* `Cslib.Complexity.PCSP.PPConstructible`: `(A', B')` is pp-constructible from `(A, B)`.
* `Cslib.Complexity.PCSP.gadgetReduce`: the polynomial-time gadget reduction induced by a
  `PPFormula`.

## Main results

* `Cslib.Complexity.PCSP.ppConstructible_iff_polMinion_hasHom`: `(A', B')` is pp-constructible from
  `(A, B)` iff `Pol(A, B) → Pol(A', B')`.
* `Cslib.Complexity.PCSP.polyTimeReducible_pcsp_of_ppConstructible`: a pp-construction yields a
  polynomial-time reduction `PCSP(A', B') ≤_p PCSP(A, B)`.
* `Cslib.Complexity.PCSP.polyTimeReducible_pcsp_of_polMinion_hasHom`: a minion homomorphism
  `Pol(A, B) → Pol(A', B')` yields a polynomial-time reduction `PCSP(A', B') ≤_p PCSP(A, B)`.
-/

public section

namespace Cslib.Complexity.PCSP

open Cslib.Complexity
open Turing.MultiTapeTM

universe u v u' v'

/-- An executable finite `r`-ary relational structure with declared vertex count `numVerts`
and tuple list `tuples`. -/
@[ext]
structure FinStructure (r : ℕ) where
  /-- Declared vertex count. -/
  numVerts : ℕ
  /-- Listed `r`-ary constraint tuples. -/
  tuples : List (Fin r → ℕ)
  deriving DecidableEq

/-- Canonical polynomial-time encoding of `FinStructure r`: unary vertex count and framed list of
canonical-order `Fin r → ℕ` unary tuples. -/
def encFinStructure (r : ℕ) : FinStructure r ↪ List Bool where
  toFun I := encPair encUnary (encList (encFinFn r encUnary)) (I.numVerts, I.tuples)
  inj' := by
    intro I J h
    have h' := (encPair encUnary (encList (encFinFn r encUnary))).injective h
    exact FinStructure.ext (congrArg Prod.fst h') (congrArg Prod.snd h')

private theorem isPolyTime_toPair_finStructure (r : ℕ) :
    ComputableInPolyTime (fun I : FinStructure r => (I.numVerts, I.tuples))
      (encFinStructure r) (encPair encUnary (encList (encFinFn r encUnary))) :=
  .of_eq fun _ => rfl

/-- Reading `FinStructure.numVerts` is polynomial-time. -/
@[fun_prop]
theorem encFinStructure_numVerts_polyTime {r : ℕ} {Input : Type}
    {encIn : Input ↪ List Bool} {f : Input → FinStructure r}
    (hf : ComputableInPolyTime f encIn (encFinStructure r)) :
    ComputableInPolyTime (fun x => (f x).numVerts) encIn encUnary :=
  ((ComputableInPolyTime.fst _ _).comp (isPolyTime_toPair_finStructure r)).comp hf

/-- Reading `FinStructure.tuples` is polynomial-time. -/
@[fun_prop]
theorem encFinStructure_tuples_polyTime {r : ℕ} {Input : Type}
    {encIn : Input ↪ List Bool} {f : Input → FinStructure r}
    (hf : ComputableInPolyTime f encIn (encFinStructure r)) :
    ComputableInPolyTime (fun x => (f x).tuples) encIn (encList (encFinFn r encUnary)) :=
  ((ComputableInPolyTime.snd _ _).comp (isPolyTime_toPair_finStructure r)).comp hf

/-- Constructing a `FinStructure r` from polynomial-time components is polynomial-time. -/
@[fun_prop]
theorem encFinStructure_mk_polyTime {r : ℕ} {Input : Type} {encIn : Input ↪ List Bool}
    {nv : Input → ℕ} {ts : Input → List (Fin r → ℕ)}
    (hnv : ComputableInPolyTime nv encIn encUnary)
    (hts : ComputableInPolyTime ts encIn (encList (encFinFn r encUnary))) :
    ComputableInPolyTime (fun x => FinStructure.mk (nv x) (ts x)) encIn (encFinStructure r) :=
  (hnv.prod hts).of_enc_eq fun _ => rfl

namespace FinStructure

/-- Interpret a `FinStructure r` as a `Template r` on `ℕ` whose relation is its tuple list. -/
@[expose]
def toTemplate {r : ℕ} (I : FinStructure r) : Template.{0} r where
  Domain := ℕ
  rel := {t | t ∈ I.tuples}

@[simp]
theorem toTemplate_domain {r : ℕ} (I : FinStructure r) : I.toTemplate.Domain = ℕ := rfl

@[simp]
theorem toTemplate_rel {r : ℕ} (I : FinStructure r) (t : Fin r → ℕ) :
    t ∈ I.toTemplate.rel ↔ t ∈ I.tuples := Iff.rfl

/-- All tuple entries of `I` lie below `I.numVerts`. -/
def WellFormed {r : ℕ} (I : FinStructure r) : Prop :=
  ∀ t ∈ I.tuples, ∀ i : Fin r, t i < I.numVerts

/-- The finite-domain template on `Fin I.numVerts` associated with a well-formed `FinStructure`. -/
@[expose]
def toFinTemplate {r : ℕ} (I : FinStructure r) : Template.{0} r where
  Domain := Fin I.numVerts
  rel := {t | (fun i => (t i).1) ∈ I.tuples}

/-- For a well-formed instance `I` and nonempty template `A`, homomorphisms from `I.toTemplate`
agree with homomorphisms from `I.toFinTemplate`. -/
theorem hasHom_toTemplate_iff_fin {r : ℕ} {I : FinStructure r} {A : Template.{u} r}
    (hWF : I.WellFormed) [Nonempty A.Domain] :
    I.toTemplate.HasHom A ↔ I.toFinTemplate.HasHom A := by
  constructor
  · rintro ⟨h⟩
    exact ⟨{ toFun := fun v => h v.1, map_rel' := fun t ht => h.map_rel' ht }⟩
  · rintro ⟨h⟩
    let d₀ : A.Domain := Classical.arbitrary A.Domain
    refine ⟨Template.Hom.mk
      (fun (v : ℕ) => if hv : v < I.numVerts then h ⟨v, hv⟩ else d₀)
      (fun (t : Fin r → ℕ) ht => by
        have hwf_t : ∀ i, t i < I.numVerts := hWF t ht
        have hmem : (fun i => (⟨t i, hwf_t i⟩ : Fin I.numVerts)) ∈ I.toFinTemplate.rel := ht
        have hmap := h.map_rel' hmem
        convert hmap using 1
        funext i
        change (if hv : t i < I.numVerts then h ⟨t i, hv⟩ else d₀) = h ⟨t i, hwf_t i⟩
        simp only [hwf_t i, ↓reduceDIte])⟩

end FinStructure

/-- The fixed-template promise constraint satisfaction problem `PCSP(A, B)`: yes-instances have a
homomorphism to `A`, and no-instances have no homomorphism to `B`. -/
def pcsp {r : ℕ} (A : Template.{u} r) (B : Template.{v} r) (hAB : A.HasHom B) :
    PromiseProblem (FinStructure r) where
  yes := {I | I.toTemplate.HasHom A}
  no := {I | ¬ I.toTemplate.HasHom B}
  disjoint := Set.disjoint_left.mpr fun _ hyes hno => hno (hyes.trans hAB)

@[simp]
theorem mem_yes_pcsp {r : ℕ} {A : Template.{u} r} {B : Template.{v} r} {hAB : A.HasHom B}
    {I : FinStructure r} :
    I ∈ (pcsp A B hAB).yes ↔ I.toTemplate.HasHom A :=
  Iff.rfl

@[simp]
theorem mem_no_pcsp {r : ℕ} {A : Template.{u} r} {B : Template.{v} r} {hAB : A.HasHom B}
    {I : FinStructure r} :
    I ∈ (pcsp A B hAB).no ↔ ¬ I.toTemplate.HasHom B :=
  Iff.rfl

/-- A primitive-positive formula defining an `r'`-ary relation on a `d`-th power of an `r`-ary
template, via `numExist` existential variables, relational atoms `relAtoms`, and equality atoms
`eqAtoms`. -/
structure PPFormula (r r' d : ℕ) where
  /-- Number of existentially quantified variables. -/
  numExist : ℕ
  /-- Relational atoms over free variables `Fin r' × Fin d` and existential variables. -/
  relAtoms : List (Fin r → Sum (Fin r' × Fin d) (Fin numExist))
  /-- Equality atoms over free variables and existential variables. -/
  eqAtoms : List (Sum (Fin r' × Fin d) (Fin numExist) × Sum (Fin r' × Fin d) (Fin numExist))

namespace PPFormula

/-- The `r'`-ary relation defined by `φ` on the `d`-th power `Fin d → A.Domain` of `A`. -/
def eval {r r' d : ℕ} (φ : PPFormula r r' d) (A : Template.{u} r) :
    Set (Fin r' → Fin d → A.Domain) :=
  {X | ∃ y : Fin φ.numExist → A.Domain,
    let val := Sum.elim (Function.uncurry X) y
    (∀ a ∈ φ.relAtoms, (val ∘ a) ∈ A.rel) ∧
    (∀ p ∈ φ.eqAtoms, val p.1 = val p.2)}

/-- The `r'`-ary template `(Fin d → A.Domain, φ.eval A)` defined by `φ` over `A`. -/
@[expose]
def toTemplate {r r' d : ℕ} (φ : PPFormula r r' d) (A : Template.{u} r) : Template.{u} r' where
  Domain := Fin d → A.Domain
  rel := φ.eval A

/-- Primitive-positive formulas are monotone under template homomorphisms. -/
def mapHom {r r' d : ℕ} (φ : PPFormula r r' d) {A : Template.{u} r} {B : Template.{v} r}
    (h : A.Hom B) : (φ.toTemplate A).Hom (φ.toTemplate B) where
  toFun (u : Fin d → A.Domain) j := h (u j)
  map_rel' := by
    rintro (X : Fin r' → Fin d → A.Domain) ⟨y, hrel, heq⟩
    refine ⟨fun e => h (y e), ?_, ?_⟩
    · intro a ha
      have hcomp : (Sum.elim (Function.uncurry fun i j => h (X i j))
          (fun e => h (y e)) ∘ a) = (h ∘ (Sum.elim (Function.uncurry X) y ∘ a)) := by
        funext idx
        dsimp only [Function.comp_apply]
        cases a idx <;> rfl
      change (Sum.elim (Function.uncurry fun i j => h (X i j)) (fun e => h (y e)) ∘ a) ∈ B.rel
      rw [hcomp]
      exact h.map_rel' (hrel a ha)
    · intro p hp
      have hp' := heq p hp
      rcases p with ⟨⟨i₁, j₁⟩ | e₁, ⟨i₂, j₂⟩ | e₂⟩
      all_goals exact congrArg h hp'

end PPFormula

/-- `(A', B')` is **pp-constructible** from `(A, B)` if there is a primitive-positive formula `φ`
such that `A' → φ(A)` and `φ(B) → B'`. -/
def PPConstructible {r r' : ℕ} (A : Template.{u} r) (B : Template.{v} r)
    (A' : Template.{u'} r') (B' : Template.{v'} r') : Prop :=
  ∃ (d : ℕ) (φ : PPFormula r r' d),
    A'.HasHom (φ.toTemplate A) ∧ (φ.toTemplate B).HasHom B'

/-- **Algebraic characterization of pp-constructibility**
: for finite `A, A'` and nonempty `B'`, `(A', B')` is pp-constructible from `(A, B)`
if and only if there is a minion homomorphism `Pol(A, B) → Pol(A', B')`.
-/
theorem ppConstructible_iff_polMinion_hasHom {r r' : ℕ}
    (A : Template.{u} r) (B : Template.{v} r)
    (A' : Template.{u'} r') (B' : Template.{v'} r')
    [Finite A.Domain] [Finite A'.Domain] [Finite A'.rel] [Nonempty B'.Domain] :
    PPConstructible A B A' B' ↔ (polMinion A B).HasHom (polMinion A' B') := by
  classical
  have : Fintype A.Domain := Fintype.ofFinite _
  have : Fintype A'.Domain := Fintype.ofFinite _
  have : Fintype A'.rel := Fintype.ofFinite _
  constructor
  · rintro ⟨d, φ, ⟨h₁⟩, ⟨h₂⟩⟩
    refine ⟨Minion.Hom.mk (fun p f => Template.Hom.mk
      (fun x' => h₂ (fun j => Template.Hom.toFun f (fun l => h₁ (x' l) j)))
      (fun X' hX' => by
        have hex : ∀ l : Fin p, ∃ y : Fin φ.numExist → A.Domain,
            let val := Sum.elim (Function.uncurry (fun i => h₁ (X' i l))) y
            (∀ a ∈ φ.relAtoms, (val ∘ a) ∈ A.rel) ∧
            (∀ eq ∈ φ.eqAtoms, val eq.1 = val eq.2) :=
          fun l => h₁.map_rel' (hX' l)
        choose y hy using hex
        let U : Fin r' → Fin d → B.Domain :=
          fun i j => Template.Hom.toFun f (fun l => h₁ (X' i l) j)
        let E : Fin φ.numExist → B.Domain :=
          fun e => Template.Hom.toFun f (fun l => y l e)
        have hU : U ∈ φ.eval B := by
          refine ⟨E, ?_, ?_⟩
          · intro a ha
            have hcol : ∀ l : Fin p,
                (fun idx => Sum.elim (Function.uncurry (fun i => h₁ (X' i l))) (y l) (a idx)) ∈
                  A.rel :=
              fun l => (hy l).1 a ha
            have hmap := f.map_rel' hcol
            convert hmap using 1
            funext idx
            change Sum.elim (Function.uncurry U) E (a idx) =
              f.toFun (fun l => Sum.elim (Function.uncurry fun i => h₁ (X' i l)) (y l) (a idx))
            rcases a idx with ⟨i, j⟩ | e <;> rfl
          · intro eq heq
            have hval : ∀ l : Fin p,
                Sum.elim (Function.uncurry (fun i => h₁ (X' i l))) (y l) eq.1 =
                Sum.elim (Function.uncurry (fun i => h₁ (X' i l))) (y l) eq.2 :=
              fun l => (hy l).2 eq heq
            rcases eq with ⟨⟨i₁, j₁⟩ | e₁, ⟨i₂, j₂⟩ | e₂⟩
            all_goals
              exact congrArg (Template.Hom.toFun f) (funext fun l => hval l)
        exact h₂.map_rel' hU))
      (fun _ _ => rfl)⟩
  · intro hξ
    let n := Fintype.card A'.Domain
    let k := Fintype.card A'.rel
    let eA' : A'.Domain ≃ Fin n := Fintype.equivFin A'.Domain
    let eR' : A'.rel ≃ Fin k := Fintype.equivFin A'.rel
    let hAdj : (freeStructureWith (polMinion A B) A' eA' eR').Hom B' :=
      (freeStructureWithHomEquiv (polMinion A B) A' B' eA' eR').symm hξ.some
    let d := Fintype.card (Fin n → A.Domain)
    let eD : (Fin n → A.Domain) ≃ Fin d := Fintype.equivFin (Fin n → A.Domain)
    let m := Fintype.card (Fin k → A.Domain)
    let eE : (Fin k → A.Domain) ≃ Fin m := Fintype.equivFin (Fin k → A.Domain)
    have : Finite (A.power n).Domain := by change Finite (Fin n → A.Domain); infer_instance
    have : Finite (A.power k).Domain := by change Finite (Fin k → A.Domain); infer_instance
    have : Fintype (A.power n).rel := Fintype.ofFinite _
    have : Fintype (A.power k).rel := Fintype.ofFinite _
    let atomsN : List (Fin r → Sum (Fin r' × Fin d) (Fin m)) :=
      (Finset.univ : Finset (Fin r')).toList.flatMap fun i =>
        (Finset.univ : Finset (A.power n).rel).toList.map fun X a =>
          Sum.inl (i, eD (X.1 a))
    let atomsK : List (Fin r → Sum (Fin r' × Fin d) (Fin m)) :=
      (Finset.univ : Finset (A.power k).rel).toList.map fun Y a =>
        Sum.inr (eE (Y.1 a))
    let eqs : List (Sum (Fin r' × Fin d) (Fin m) × Sum (Fin r' × Fin d) (Fin m)) :=
      (Finset.univ : Finset (Fin r')).toList.flatMap fun i =>
        (Finset.univ : Finset (Fin n → A.Domain)).toList.map fun x =>
          (Sum.inl (i, eD x), Sum.inr (eE fun j => x (eA' ((eR'.symm j).1 i))))
    let φ : PPFormula r r' d :=
      { numExist := m
        relAtoms := atomsN ++ atomsK
        eqAtoms := eqs }
    refine ⟨d, φ, ⟨?_⟩, ⟨?_⟩⟩
    · -- Homomorphism `A' → φ(A)` sending `a` to the evaluation projection `x ↦ x (eA' a)`.
      refine Template.Hom.mk (fun a (j : Fin d) => (eD.symm j) (eA' a)) fun t ht => ?_
      let j₀ : Fin k := eR' ⟨t, ht⟩
      refine ⟨fun e => (eE.symm e) j₀, ?_, ?_⟩
      · intro atom hatom
        rcases List.mem_append.mp hatom with hN | hK
        · rw [List.mem_flatMap] at hN
          obtain ⟨i, _, hmem⟩ := hN
          rw [List.mem_map] at hmem
          obtain ⟨X, _, rfl⟩ := hmem
          convert X.2 (eA' (t i)) using 1
          funext a
          exact congrFun (eD.symm_apply_apply (X.1 a)) (eA' (t i))
        · rw [List.mem_map] at hK
          obtain ⟨Y, _, rfl⟩ := hK
          convert Y.2 j₀ using 1
          funext a
          exact congrFun (eE.symm_apply_apply (Y.1 a)) j₀
      · intro p hp
        rw [List.mem_flatMap] at hp
        obtain ⟨i, _, hmem⟩ := hp
        rw [List.mem_map] at hmem
        obtain ⟨x, _, rfl⟩ := hmem
        change (eD.symm (eD x)) (eA' (t i)) =
          (eE.symm (eE fun j => x (eA' ((eR'.symm j).1 i)))) j₀
        simp only [Equiv.symm_apply_apply, j₀]
    · -- Homomorphism `φ(B) → B'` using `hAdj : F_{Pol(A,B)}(A') → B'`.
      let b₀ : B'.Domain := Classical.arbitrary B'.Domain
      refine Template.Hom.mk (fun (u : Fin d → B.Domain) =>
        if hu : (A.power n).IsHom B (u ∘ eD) then hAdj ⟨u ∘ eD, hu⟩ else b₀)
        fun (U : Fin r' → Fin d → B.Domain) hU => ?_
      obtain ⟨E, hrel, heq⟩ := hU
      have hU_hom : ∀ i : Fin r', (A.power n).IsHom B (U i ∘ eD) := by
        intro i X hX
        have hmem : (fun a => Sum.inl (i, eD (X a))) ∈ φ.relAtoms := by
          refine List.mem_append_left _ ?_
          rw [List.mem_flatMap]
          refine ⟨i, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
          rw [List.mem_map]
          exact ⟨⟨X, hX⟩, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
        exact hrel _ hmem
      have hE_hom : (A.power k).IsHom B (E ∘ eE) := by
        intro Y hY
        have hmem : (fun a => Sum.inr (eE (Y a))) ∈ φ.relAtoms := by
          refine List.mem_append_right _ ?_
          rw [List.mem_map]
          exact ⟨⟨Y, hY⟩, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
        exact hrel _ hmem
      let fE : (polMinion A B).carrier k := ⟨E ∘ eE, hE_hom⟩
      have hfree : (fun i : Fin r' => (⟨U i ∘ eD, hU_hom i⟩ : (polMinion A B).carrier n)) ∈
          (freeStructureWith (polMinion A B) A' eA' eR').rel := by
        refine ⟨fE, fun i => ?_⟩
        apply Template.Hom.ext
        funext x
        have hmem : (Sum.inl (i, eD x),
            Sum.inr (eE fun j => x (eA' ((eR'.symm j).1 i)))) ∈ φ.eqAtoms := by
          rw [List.mem_flatMap]
          refine ⟨i, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
          rw [List.mem_map]
          exact ⟨x, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
        exact heq _ hmem
      have hmap := hAdj.map_rel' hfree
      convert hmap using 1
      funext i
      change (if hu : (A.power n).IsHom B (U i ∘ eD) then hAdj ⟨U i ∘ eD, hu⟩ else b₀) =
        hAdj ⟨U i ∘ eD, hU_hom i⟩
      simp only [hU_hom i, ↓reduceDIte]

/-! ### Polynomial-time equality collapsing and gadget reduction -/

private def maxTupleVert {r : ℕ} (t : Fin r → ℕ) : ℕ :=
  (List.ofFn t).foldl max 0

private def maxEntry {r : ℕ} (ts : List (Fin r → ℕ)) : ℕ :=
  ts.foldl (fun acc t => max acc (maxTupleVert t)) 0

private theorem le_foldl_max {α : Type*} (l : List α) (f : α → ℕ) (acc : ℕ) :
    acc ≤ l.foldl (fun a x => max a (f x)) acc ∧
      ∀ x ∈ l, f x ≤ l.foldl (fun a y => max a (f y)) acc := by
  induction l generalizing acc with
  | nil => exact ⟨le_rfl, fun _ h => nomatch h⟩
  | cons y ys ih =>
    have ⟨h1, h2⟩ := ih (max acc (f y))
    refine ⟨(le_max_left acc (f y)).trans h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right acc (f x)).trans h1
    · exact h2 x hx

private theorem le_maxEntry {r : ℕ} {ts : List (Fin r → ℕ)} {t : Fin r → ℕ}
    (ht : t ∈ ts) (i : Fin r) : t i ≤ maxEntry ts := by
  have h1 : t i ≤ maxTupleVert t :=
    (le_foldl_max (List.ofFn t) id 0).2 (t i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact h1.trans ((le_foldl_max ts maxTupleVert 0).2 t ht)

private theorem foldl_max_le_bound {α : Type*} (l : List α) (f : α → ℕ) (acc B : ℕ)
    (hacc : acc ≤ B) (hf : ∀ x ∈ l, f x ≤ B) :
    l.foldl (fun a x => max a (f x)) acc ≤ B := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons y ys ih =>
    exact ih (max acc (f y)) (max_le hacc (hf y List.mem_cons_self))
      (fun x hx => hf x (List.mem_cons_of_mem _ hx))

private theorem computableInPolyTime_maxTupleVert (r : ℕ) :
    ComputableInPolyTime (maxTupleVert (r := r)) (encFinFn r encUnary) encUnary := by
  have hstep : ComputableInPolyTime (fun p : ℕ × ℕ => max p.1 p.2)
      (encPair encUnary encUnary) encUnary := ComputableInPolyTime.unary_max
  refine ComputableInPolyTime.foldl'
    (encA := encUnary) (encB := encUnary) (encL := encList encUnary)
    (list := List.ofFn) (init := fun _ => 0) (step := max)
    (ComputableInPolyTime.ofFn_finFn .id') (.const 0) hstep
    (B := fun t => (encFinFn r encUnary t).length) .self ?_
  intro t i _
  simp only [encUnary_apply, List.length_replicate]
  refine foldl_max_le_bound _ id 0 _ (Nat.zero_le _) fun x hx => ?_
  have hmem : x ∈ List.ofFn t := List.mem_of_mem_take hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hmem
  have hle := SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary)
    (List.ofFn t) (t j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
  dsimp only [id]
  simpa only [encFinFn_apply, encUnary_apply, List.length_replicate] using hle

private theorem computableInPolyTime_maxEntry (r : ℕ) :
    ComputableInPolyTime (maxEntry (r := r)) (encList (encFinFn r encUnary)) encUnary := by
  have hstep : ComputableInPolyTime (fun p : ℕ × (Fin r → ℕ) => max p.1 (maxTupleVert p.2))
      (encPair encUnary (encFinFn r encUnary)) encUnary :=
    ComputableInPolyTime.unary_max.comp
      ((ComputableInPolyTime.fst _ _).prod
        ((computableInPolyTime_maxTupleVert r).comp (ComputableInPolyTime.snd _ _)))
  refine ComputableInPolyTime.foldl'
    (encA := encFinFn r encUnary) (encB := encUnary) (encL := encList (encFinFn r encUnary))
    (list := id) (init := fun _ => 0) (step := fun acc t => max acc (maxTupleVert t))
    .id' (.const 0) hstep
    (B := fun ts => (encList (encFinFn r encUnary) ts).length) .self ?_
  intro ts i _
  simp only [encUnary_apply, List.length_replicate]
  refine foldl_max_le_bound _ maxTupleVert 0 _ (Nat.zero_le _) fun t ht => ?_
  have hmem : t ∈ ts := List.mem_of_mem_take ht
  refine foldl_max_le_bound _ id 0 _ (Nat.zero_le _) fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  have h1 := SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary)
    (List.ofFn t) (t j) (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have h2 := SizedListEncoding.length_elem_le (encA := encFinFn r encUnary)
    (encL := encList (encFinFn r encUnary)) ts t hmem
  simp only [encFinFn_apply, encUnary_apply, List.length_replicate] at h1 h2
  dsimp only [id]
  omega

/-- Raw vertex identifier assigned to a free or existential variable of `φ` at constraint index
`tIdx` on tuple `t`. -/
private def rawId {r' d numExist : ℕ} (N : ℕ) (t : Fin r' → ℕ) (tIdx : ℕ) :
    Sum (Fin r' × Fin d) (Fin numExist) → ℕ
  | Sum.inl (i, j) => t i * d + j.1
  | Sum.inr e => N * d + tIdx * numExist + e.1

private theorem rawId_lt {r' d numExist : ℕ} {N m : ℕ} {t : Fin r' → ℕ} {tIdx : ℕ}
    (ht : ∀ i, t i < N) (hidx : tIdx < m) (v : Sum (Fin r' × Fin d) (Fin numExist)) :
    rawId (d := d) (numExist := numExist) N t tIdx v < N * d + m * numExist := by
  rcases v with ⟨i, j⟩ | e
  · have hti : t i + 1 ≤ N := ht i
    have hmul : t i * d + j.1 < (t i + 1) * d := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hle : (t i + 1) * d ≤ N * d := Nat.mul_le_mul_right d hti
    dsimp [rawId]
    omega
  · have hmul : tIdx * numExist + e.1 < (tIdx + 1) * numExist := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hle : (tIdx + 1) * numExist ≤ m * numExist := Nat.mul_le_mul_right numExist hidx
    dsimp [rawId]
    omega

/-- One relaxation step for vertex `u`: take the minimum of `rep[u]` and `rep[w]` across all
equality edges `(u, w)` or `(w, u)` in `eqs`. -/
private def relaxOne (eqs : List (ℕ × ℕ)) (rep : List ℕ) (u : ℕ) : ℕ :=
  eqs.foldl
    (fun acc p =>
      if p.1 == u then min acc (rep.getD p.2 p.2)
      else if p.2 == u then min acc (rep.getD p.1 p.1)
      else acc)
    (rep.getD u u)

/-- Synchronous relaxation pass across all indices `0 .. rep.length - 1`. -/
private def relaxStep (eqs : List (ℕ × ℕ)) (rep : List ℕ) : List ℕ :=
  (List.range rep.length).map (relaxOne eqs rep)

/-- Representative table produced by `T` passes of synchronous min-propagation on equality
pairs `eqs`. -/
def collapseRep (eqs : List (ℕ × ℕ)) (T : ℕ) : List ℕ :=
  (relaxStep eqs)^[T] (List.range T)

private theorem relaxOne_le_init (eqs : List (ℕ × ℕ)) (rep : List ℕ) (u : ℕ) :
    relaxOne eqs rep u ≤ rep.getD u u := by
  have haux : ∀ (l : List (ℕ × ℕ)) (acc : ℕ),
      l.foldl (fun a p => if p.1 == u then min a (rep.getD p.2 p.2)
        else if p.2 == u then min a (rep.getD p.1 p.1) else a) acc ≤ acc := by
    intro l
    induction l with
    | nil => intro acc; exact le_rfl
    | cons p ps ih =>
      intro acc
      dsimp only [List.foldl_cons]
      refine (ih _).trans ?_
      split_ifs <;> simp
  exact haux eqs (rep.getD u u)

private theorem relaxOne_le_edge (eqs : List (ℕ × ℕ)) (rep : List ℕ) {u v : ℕ}
    (he : (u, v) ∈ eqs ∨ (v, u) ∈ eqs) :
    relaxOne eqs rep u ≤ rep.getD v v := by
  have hmono : ∀ (l : List (ℕ × ℕ)) (a b : ℕ), a ≤ b →
      l.foldl (fun x p => if p.1 == u then min x (rep.getD p.2 p.2)
        else if p.2 == u then min x (rep.getD p.1 p.1) else x) a ≤
      l.foldl (fun x p => if p.1 == u then min x (rep.getD p.2 p.2)
        else if p.2 == u then min x (rep.getD p.1 p.1) else x) b := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons p ps ih =>
      intro a b hab
      dsimp only [List.foldl_cons]
      apply ih
      split_ifs <;> omega
  have haux : ∀ (l : List (ℕ × ℕ)) (acc : ℕ), (u, v) ∈ l ∨ (v, u) ∈ l →
      l.foldl (fun a p => if p.1 == u then min a (rep.getD p.2 p.2)
        else if p.2 == u then min a (rep.getD p.1 p.1) else a) acc ≤ rep.getD v v := by
    intro l
    induction l with
    | nil => intro _ h; rcases h with h | h <;> cases h
    | cons p ps ih =>
      intro acc hmem
      dsimp only [List.foldl_cons]
      have hhead_or : (p = (u, v) ∨ p = (v, u)) ∨ ((u, v) ∈ ps ∨ (v, u) ∈ ps) := by
        rcases hmem with h | h
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr (Or.inl h')
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr (Or.inr h')
      rcases hhead_or with (rfl | rfl) | htail
      · have hle : (if (u == u) then min acc (rep.getD v v)
            else if (v == u) then min acc (rep.getD u u) else acc) ≤ rep.getD v v := by
          simp
        exact (hmono ps _ _ hle).trans (by
          have hdec : ∀ (l : List (ℕ × ℕ)) (a : ℕ),
              l.foldl (fun x p => if p.1 == u then min x (rep.getD p.2 p.2)
                else if p.2 == u then min x (rep.getD p.1 p.1) else x) a ≤ a := by
            intro l
            induction l with
            | nil => intro _; exact le_rfl
            | cons q qs ihq =>
              intro a; dsimp only [List.foldl_cons]
              refine (ihq _).trans ?_; split_ifs <;> simp
          exact hdec ps _)
      · have hle : (if (v == u) then min acc (rep.getD u u)
            else if (u == u) then min acc (rep.getD v v) else acc) ≤ rep.getD v v := by
          by_cases hvu : v = u
          · subst hvu; simp
          · simp [hvu]
        exact (hmono ps _ _ hle).trans (by
          have hdec : ∀ (l : List (ℕ × ℕ)) (a : ℕ),
              l.foldl (fun x p => if p.1 == u then min x (rep.getD p.2 p.2)
                else if p.2 == u then min x (rep.getD p.1 p.1) else x) a ≤ a := by
            intro l
            induction l with
            | nil => intro _; exact le_rfl
            | cons q qs ihq =>
              intro a; dsimp only [List.foldl_cons]
              refine (ihq _).trans ?_; split_ifs <;> simp
          exact hdec ps _)
      · exact ih _ htail
  exact haux eqs (rep.getD u u) he

private theorem relaxStep_length (eqs : List (ℕ × ℕ)) (rep : List ℕ) :
    (relaxStep eqs rep).length = rep.length := by
  simp [relaxStep]

private theorem iterate_relaxStep_length (eqs : List (ℕ × ℕ)) (T t : ℕ) :
    ((relaxStep eqs)^[t] (List.range T)).length = T := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', relaxStep_length, ih]

private theorem getD_relaxStep (eqs : List (ℕ × ℕ)) (rep : List ℕ) {u : ℕ}
    (hu : u < rep.length) :
    (relaxStep eqs rep).getD u u = relaxOne eqs rep u := by
  simp [relaxStep, hu]

private theorem iterate_relaxStep_le_self (eqs : List (ℕ × ℕ)) (T t u : ℕ) (hu : u < T) :
    ((relaxStep eqs)^[t] (List.range T)).getD u u ≤ u := by
  induction t with
  | zero =>
    simp [hu]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have hlen : ((relaxStep eqs)^[t] (List.range T)).length = T :=
      iterate_relaxStep_length eqs T t
    rw [getD_relaxStep eqs _ (by rw [hlen]; exact hu)]
    exact (relaxOne_le_init eqs _ u).trans ih

private theorem iterate_relaxStep_mono (eqs : List (ℕ × ℕ)) (T t u : ℕ) (hu : u < T) :
    ((relaxStep eqs)^[t + 1] (List.range T)).getD u u ≤
      ((relaxStep eqs)^[t] (List.range T)).getD u u := by
  rw [Function.iterate_succ_apply']
  have hlen : ((relaxStep eqs)^[t] (List.range T)).length = T :=
    iterate_relaxStep_length eqs T t
  rw [getD_relaxStep eqs _ (by rw [hlen]; exact hu)]
  exact relaxOne_le_init eqs _ u

private theorem relaxOne_preserves {D : Type*} (eqs : List (ℕ × ℕ)) (rep : List ℕ)
    (g : ℕ → D) (hg : ∀ p ∈ eqs, g p.1 = g p.2) (u : ℕ)
    (hrep : ∀ w, g (rep.getD w w) = g w) :
    g (relaxOne eqs rep u) = g u := by
  have haux : ∀ (l : List (ℕ × ℕ)) (acc : ℕ),
      (∀ p ∈ l, g p.1 = g p.2) → g acc = g u →
      g (l.foldl (fun a p => if p.1 == u then min a (rep.getD p.2 p.2)
        else if p.2 == u then min a (rep.getD p.1 p.1) else a) acc) = g u := by
    intro l
    induction l with
    | nil => exact fun _ _ ha => ha
    | cons p ps ih =>
      intro acc hl hacc
      dsimp only [List.foldl_cons]
      refine ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) ?_
      have hp := hl p List.mem_cons_self
      split_ifs with h1 h2
      · have h1' : p.1 = u := eq_of_beq h1
        rcases min_cases acc (rep.getD p.2 p.2) with ⟨hm, _⟩ | ⟨hm, _⟩
        · rw [hm, hacc]
        · rw [hm, hrep p.2, ← hp, h1']
      · have h2' : p.2 = u := eq_of_beq h2
        rcases min_cases acc (rep.getD p.1 p.1) with ⟨hm, _⟩ | ⟨hm, _⟩
        · rw [hm, hacc]
        · rw [hm, hrep p.1, hp, h2']
      · exact hacc
  exact haux eqs (rep.getD u u) hg (hrep u)

/-- Any function `g` respecting all equality pairs `eqs` takes the same value at `u` and its
`collapseRep` representative. -/
theorem collapseRep_preserves {D : Type*} (eqs : List (ℕ × ℕ)) (T : ℕ)
    (g : ℕ → D) (hg : ∀ p ∈ eqs, g p.1 = g p.2) (u : ℕ) :
    g ((collapseRep eqs T).getD u u) = g u := by
  have haux : ∀ t w, g (((relaxStep eqs)^[t] (List.range T)).getD w w) = g w := by
    intro t
    induction t with
    | zero =>
      intro w
      by_cases hw : w < T
      · simp [hw]
      · simp [hw]
    | succ t ih =>
      intro w
      rw [Function.iterate_succ_apply']
      have hlen : ((relaxStep eqs)^[t] (List.range T)).length = T :=
        iterate_relaxStep_length eqs T t
      by_cases hw : w < T
      · rw [getD_relaxStep eqs _ (by rw [hlen]; exact hw)]
        exact relaxOne_preserves eqs _ g hg w ih
      · have hw' : ((relaxStep eqs)^[t + 1] (List.range T)).length ≤ w := by
          rw [iterate_relaxStep_length]; omega
        rw [List.getD_eq_default _ _ (by rw [relaxStep_length, hlen]; omega)]
  exact haux T u

/-- A valid undirected path in `eqs` of vertices below `T`. -/
private def IsEqPath (eqs : List (ℕ × ℕ)) (T : ℕ) (l : List ℕ) (u v : ℕ) : Prop :=
  l.head? = some u ∧
  l.getLast? = some v ∧
  (∀ x ∈ l, x < T) ∧
  (∀ i (hi : i + 1 < l.length),
    (l[i], l[i + 1]) ∈ eqs ∨ (l[i + 1], l[i]) ∈ eqs)

private theorem isEqPath_shorten (eqs : List (ℕ × ℕ)) (T : ℕ) :
    ∀ (n : ℕ) (l : List ℕ) (u v : ℕ), l.length = n → IsEqPath eqs T l u v →
      ∃ l' : List ℕ, IsEqPath eqs T l' u v ∧ l'.length ≤ T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l u v hlen hpath
    by_cases hle : l.length ≤ T
    · exact ⟨l, hpath, hle⟩
    · obtain ⟨hhead, hlast, hlt, hedges⟩ := hpath
      have hnot_nodup : ¬ l.Nodup := by
        intro hnd
        have hsub : l.toFinset ⊆ Finset.range T := by
          intro x hx
          exact Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
        have hcard : l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
        have hle' : l.toFinset.card ≤ T := by
          simpa using Finset.card_le_card hsub
        omega
      have hex : ∃ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i < j ∧ l[i] = l[j] := by
        by_contra hno
        push Not at hno
        apply hnot_nodup
        rw [List.nodup_iff_injective_get]
        intro a b hab
        rcases lt_trichotomy a.1 b.1 with hlt' | heq | hgt
        · exact absurd hab (hno a.1 b.1 a.2 b.2 hlt')
        · exact Fin.ext heq
        · exact absurd hab.symm (hno b.1 a.1 b.2 a.2 hgt)
      obtain ⟨i, j, hi, hj, hij, hEq⟩ := hex
      let l' := l.take i ++ l.drop j
      have hlen' : l'.length = i + (l.length - j) := by
        simp [l', List.length_take, List.length_drop, Nat.min_eq_left (Nat.le_of_lt hi)]
      have hlt_len : l'.length < n := by omega
      have hne_drop : l.drop j ≠ [] := by
        intro hemp
        have := congrArg List.length hemp
        simp [List.length_drop] at this
        omega
      have hl'_head : l'.head? = some u := by
        cases i with
        | zero =>
          simp only [l', List.take_zero, List.nil_append]
          have h0 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
          rw [h0, List.head?_cons, ← hEq]
          cases l with
          | nil => simp at hi
          | cons a as => simpa using hhead
        | succ i' =>
          have hpos : 0 < (l.take (i' + 1)).length := by
            rw [List.length_take]
            omega
          have hne_take : l.take (i' + 1) ≠ [] := by
            intro hemp
            rw [hemp] at hpos
            simp at hpos
          rw [List.head?_append_of_ne_nil _ hne_take]
          cases l with
          | nil => simp at hi
          | cons a as => simpa using hhead
      have hl'_last : l'.getLast? = some v := by
        rw [List.getLast?_append_of_ne_nil _ hne_drop, List.getLast?_drop]
        simp only [show ¬ l.length ≤ j by omega, ↓reduceIte]
        exact hlast
      have hl'_lt : ∀ x ∈ l', x < T := by
        intro x hx
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact hlt x (List.mem_of_mem_take hx1)
        · exact hlt x (List.mem_of_mem_drop hx2)
      have hl'_edges : ∀ k (hk : k + 1 < l'.length),
          (l'[k], l'[k + 1]) ∈ eqs ∨ (l'[k + 1], l'[k]) ∈ eqs := by
        intro k hk
        have hlen_take : (l.take i).length = i := by
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
        by_cases hk1 : k + 1 < i
        · have hk0 : k < i := by omega
          have hget0 : l'[k] = l[k] := by
            rw [List.getElem_append_left (by omega), List.getElem_take]
          have hget1 : l'[k + 1] = l[k + 1] := by
            rw [List.getElem_append_left (by omega), List.getElem_take]
          rw [hget0, hget1]
          exact hedges k (by omega)
        · by_cases hk2 : k < i
          · have hki : k + 1 = i := by omega
            have hget0 : l'[k] = l[k] := by
              rw [List.getElem_append_left (by omega), List.getElem_take]
            have hget1 : l'[k + 1] = l[j] := by
              rw [List.getElem_append_right (by omega), List.getElem_drop]
              congr 1
              rw [hlen_take]
              omega
            have hEq' : l[k + 1]'(by omega) = l[j] := by
              simpa only [hki] using hEq
            rw [hget0, hget1, ← hEq']
            exact hedges k (by omega)
          · have hget0 : l'[k] = l[j + (k - i)] := by
              rw [List.getElem_append_right (by omega), List.getElem_drop]
              congr 1
              rw [hlen_take]
            have hget1 : l'[k + 1] = l[j + (k - i) + 1] := by
              rw [List.getElem_append_right (by omega), List.getElem_drop]
              congr 1
              rw [hlen_take]
              omega
            rw [hget0, hget1]
            exact hedges (j + (k - i)) (by omega)
      exact ih l'.length hlt_len l' u v rfl ⟨hl'_head, hl'_last, hl'_lt, hl'_edges⟩

private theorem iterate_relaxStep_le_of_path (eqs : List (ℕ × ℕ)) (T : ℕ) :
    ∀ (k : ℕ) (l : List ℕ) (u v : ℕ), l.length = k + 1 → IsEqPath eqs T l u v →
      ∀ t ≥ k, ((relaxStep eqs)^[t] (List.range T)).getD v v ≤ u := by
  intro k
  induction k with
  | zero =>
    intro l u v hlen ⟨hhead, hlast, hlt, _⟩ t _
    cases l with
    | nil => simp at hlen
    | cons a as =>
      cases as with
      | nil =>
        have hau : a = u := Option.some.inj hhead
        have hav : a = v := Option.some.inj hlast
        subst hau
        rw [← hav]
        exact iterate_relaxStep_le_self eqs T t a (hlt a List.mem_cons_self)
      | cons _ _ => simp at hlen
  | succ k ih =>
    intro l u v hlen ⟨hhead, hlast, hlt, hedges⟩ t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hne : l ≠ [] := by intro h; simp [h] at hlen
    let l' := l.dropLast
    have hlen' : l'.length = k + 1 := by simp [l', hlen]
    have hlast_val : l[k + 1]'(by omega) = v := by
      have h : l.getLast? = l[l.length - 1]? := List.getLast?_eq_getElem?
      rw [hlen, List.getElem?_eq_getElem (by omega)] at h
      exact Option.some.inj (h.symm.trans hlast)
    let w := l[k]'(by omega)
    have hpath' : IsEqPath eqs T l' u w := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hne' : l' ≠ [] := by intro h; simp [h] at hlen'
        have h1 : l = l' ++ [l.getLast hne] := (List.dropLast_append_getLast hne).symm
        rw [h1, List.head?_append_of_ne_nil _ hne'] at hhead
        exact hhead
      · have h : l'.getLast? = l'[l'.length - 1]? := List.getLast?_eq_getElem?
        rw [hlen', List.getElem?_eq_getElem (by omega), List.getElem_dropLast] at h
        exact h
      · intro x hx
        exact hlt x (List.mem_of_mem_dropLast hx)
      · intro i hi
        have hi' : i + 1 < l.length := by omega
        have := hedges i hi'
        simpa [l', List.getElem_dropLast] using this
    have hw_le : ((relaxStep eqs)^[t'] (List.range T)).getD w w ≤ u :=
      ih l' u w hlen' hpath' t' (by omega)
    have he : (w, v) ∈ eqs ∨ (v, w) ∈ eqs := by
      have h := hedges k (by omega)
      rwa [hlast_val] at h
    have hv_lt : v < T := hlt v (List.mem_of_getLast? hlast)
    rw [Function.iterate_succ_apply',
      getD_relaxStep eqs _ (by rw [iterate_relaxStep_length]; exact hv_lt)]
    exact (relaxOne_le_edge eqs _ (he.symm)).trans hw_le

private theorem isEqPath_append_edge {eqs : List (ℕ × ℕ)} {T : ℕ} {l : List ℕ} {a b c : ℕ}
    (hp : IsEqPath eqs T l a b) (he : (b, c) ∈ eqs ∨ (c, b) ∈ eqs) (hc : c < T) :
    IsEqPath eqs T (l ++ [c]) a c := by
  obtain ⟨hhead, hlast, hlt, hedges⟩ := hp
  have hne : l ≠ [] := by intro h; simp [h] at hhead
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.head?_append_of_ne_nil _ hne]; exact hhead
  · simp
  · intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hlt x hx1
    · simp only [List.mem_singleton] at hx2
      exact hx2 ▸ hc
  · intro i hi
    have hlen : (l ++ [c]).length = l.length + 1 := by simp
    by_cases hi' : i + 1 < l.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left hi']
      exact hedges i hi'
    · have hik : i + 1 = l.length := by omega
      have hi_lt : i < l.length := by omega
      have hlast_eq : l[i] = b := by
        have h : l.getLast? = l[l.length - 1]? := List.getLast?_eq_getElem?
        rw [← hik, Nat.add_sub_cancel, List.getElem?_eq_getElem hi_lt] at h
        exact Option.some.inj (h.symm.trans hlast)
      rw [List.getElem_append_left hi_lt, List.getElem_append_right (by omega)]
      have hsub : i + 1 - l.length = 0 := by omega
      simp only [hsub, List.getElem_singleton, hlast_eq]
      exact he

private theorem path_from_iterate_relaxStep (eqs : List (ℕ × ℕ)) (T : ℕ)
    (heqs : ∀ p ∈ eqs, p.1 < T ∧ p.2 < T) :
    ∀ (t u : ℕ), u < T →
      ∃ l : List ℕ, IsEqPath eqs T l (((relaxStep eqs)^[t] (List.range T)).getD u u) u := by
  intro t
  induction t with
  | zero =>
    intro u hu
    simp only [Function.iterate_zero, id_eq]
    rw [List.getD_eq_getElem _ _ (by simp [hu]), List.getElem_range]
    refine ⟨[u], rfl, rfl, ?_, fun i hi => by simp at hi⟩
    intro x hx
    simp only [List.mem_singleton] at hx
    exact hx ▸ hu
  | succ t ih =>
    intro u hu
    rw [Function.iterate_succ_apply',
      getD_relaxStep eqs _ (by rw [iterate_relaxStep_length]; exact hu)]
    set rep := (relaxStep eqs)^[t] (List.range T)
    have hfold : ∀ (l : List (ℕ × ℕ)) (acc : ℕ),
        (∀ p ∈ l, p ∈ eqs) →
        (∃ P, IsEqPath eqs T P acc u) →
        ∃ P, IsEqPath eqs T P
          (l.foldl (fun a p => if p.1 == u then min a (rep.getD p.2 p.2)
            else if p.2 == u then min a (rep.getD p.1 p.1) else a) acc) u := by
      intro l
      induction l with
      | nil => exact fun _ _ h => h
      | cons p ps ihp =>
        intro acc hl hacc
        dsimp only [List.foldl_cons]
        refine ihp _ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) ?_
        have hp_mem : p ∈ eqs := hl p List.mem_cons_self
        have hp_lt := heqs p hp_mem
        split_ifs with h1 h2
        · have h1' : p.1 = u := eq_of_beq h1
          rcases min_cases acc (rep.getD p.2 p.2) with ⟨hm, _⟩ | ⟨hm, _⟩
          · rwa [hm]
          · rw [hm]
            obtain ⟨P, hP⟩ := ih p.2 hp_lt.2
            exact ⟨P ++ [u], isEqPath_append_edge hP (Or.inr (h1' ▸ hp_mem)) hu⟩
        · have h2' : p.2 = u := eq_of_beq h2
          rcases min_cases acc (rep.getD p.1 p.1) with ⟨hm, _⟩ | ⟨hm, _⟩
          · rwa [hm]
          · rw [hm]
            obtain ⟨P, hP⟩ := ih p.1 hp_lt.1
            exact ⟨P ++ [u], isEqPath_append_edge hP (Or.inl (h2' ▸ hp_mem)) hu⟩
        · exact hacc
    exact hfold eqs (rep.getD u u) (fun _ h => h) (ih u hu)

/-- Whenever all equality pairs in `eqs` have endpoints below `T`, `collapseRep eqs T` assigns
equal representatives to both endpoints of every pair in `eqs`. -/
theorem collapseRep_eq_of_mem {eqs : List (ℕ × ℕ)} {T : ℕ}
    (heqs : ∀ p ∈ eqs, p.1 < T ∧ p.2 < T) {p : ℕ × ℕ} (hp : p ∈ eqs) :
    (collapseRep eqs T).getD p.1 p.1 = (collapseRep eqs T).getD p.2 p.2 := by
  obtain ⟨hu, hv⟩ := heqs p hp
  have hle : ∀ {a b : ℕ}, a < T → b < T → ((a, b) ∈ eqs ∨ (b, a) ∈ eqs) →
      (collapseRep eqs T).getD b b ≤ (collapseRep eqs T).getD a a := by
    intro a b ha hb hab
    obtain ⟨P, hP⟩ := path_from_iterate_relaxStep eqs T heqs T a ha
    have hPb := isEqPath_append_edge hP hab hb
    obtain ⟨Q, hQ, hQlen⟩ := isEqPath_shorten eqs T (P ++ [b]).length (P ++ [b]) _ b rfl hPb
    have hQne : Q ≠ [] := by intro h; simp [h, IsEqPath] at hQ
    have hQpos : 1 ≤ Q.length := List.length_pos_of_ne_nil hQne
    exact iterate_relaxStep_le_of_path eqs T (Q.length - 1) Q _ b (by omega) hQ T (by omega)
  exact le_antisymm (hle hv hu (Or.inr hp)) (hle hu hv (Or.inl hp))

/-- Bound on vertex indices used by `gadgetReduce`. -/
private def instanceBound {r' : ℕ} (I : FinStructure r') : ℕ :=
  max I.numVerts (maxEntry I.tuples + 1)

/-- Equality pairs induced by `φ` across all constraints of `I`. -/
private def gadgetEqPairs {r r' d : ℕ} (φ : PPFormula r r' d) (I : FinStructure r') :
    List (ℕ × ℕ) :=
  I.tuples.zipIdx.flatMap fun p =>
    φ.eqAtoms.map fun eq =>
      (rawId (d := d) (numExist := φ.numExist) (instanceBound I) p.1 p.2 eq.1,
       rawId (d := d) (numExist := φ.numExist) (instanceBound I) p.1 p.2 eq.2)

/-- The polynomial-time gadget reduction `FinStructure r' → FinStructure r` associated with a
primitive-positive formula `φ`. -/
def gadgetReduce {r r' d : ℕ} (φ : PPFormula r r' d) (I : FinStructure r') : FinStructure r :=
  let N := instanceBound I
  let T := N * d + I.tuples.length * φ.numExist
  let rep := collapseRep (gadgetEqPairs φ I) T
  { numVerts := T
    tuples := I.tuples.zipIdx.flatMap fun p =>
      φ.relAtoms.map fun a i =>
        let idx := rawId (d := d) (numExist := φ.numExist) N p.1 p.2 (a i)
        rep.getD idx idx }

@[fun_prop]
private theorem listGetDWithInput {Input α : Type}
    {encIn : Input ↪ List Bool} {encA : α ↪ List Bool}
    {fl : Input → List α} {fi : Input → ℕ} {fd : Input → α}
    (hl : ComputableInPolyTime fl encIn (encList encA))
    (hi : ComputableInPolyTime fi encIn encUnary)
    (hd : ComputableInPolyTime fd encIn encA) :
    ComputableInPolyTime (fun x => (fl x).getD (fi x) (fd x)) encIn encA :=
  (ComputableInPolyTime.optionGetDWithInput (ComputableInPolyTime.getElem? hl hi) hd).of_enc_eq
    fun _ => by simp only [List.getD_eq_getElem?_getD]

private theorem computableInPolyTime_relaxOne :
    ComputableInPolyTime
      (fun p : (List (ℕ × ℕ) × List ℕ) × ℕ => relaxOne p.1.1 p.1.2 p.2)
      (encPair (encPair (encList (encPair encUnary encUnary)) (encList encUnary)) encUnary)
      encUnary := by
  have hstep : ComputableInPolyTime
      (fun q : ((List ℕ × ℕ) × ℕ) × (ℕ × ℕ) =>
        if q.2.1 == q.1.1.2 then min q.1.2 (q.1.1.1.getD q.2.2 q.2.2)
        else if q.2.2 == q.1.1.2 then min q.1.2 (q.1.1.1.getD q.2.1 q.2.1)
        else q.1.2)
      (encPair (encPair (encPair (encList encUnary) encUnary) encUnary)
        (encPair encUnary encUnary))
      encUnary := by fun_prop
  have hfold : ComputableInPolyTime
      (fun p : (List (ℕ × ℕ) × List ℕ) × ℕ =>
        p.1.1.foldl
          (fun acc e =>
            if e.1 == p.2 then min acc (p.1.2.getD e.2 e.2)
            else if e.2 == p.2 then min acc (p.1.2.getD e.1 e.1)
            else acc)
          (p.1.2.getD p.2 p.2))
      (encPair (encPair (encList (encPair encUnary encUnary)) (encList encUnary)) encUnary)
      encUnary :=
    ComputableInPolyTime.foldlWith
      (encA := encPair encUnary encUnary) (encB := encUnary)
      (encL := encList (encPair encUnary encUnary))
      (encP := encPair (encList encUnary) encUnary)
      (par := fun p : (List (ℕ × ℕ) × List ℕ) × ℕ => (p.1.2, p.2))
      (list := fun p => p.1.1)
      (init := fun p => p.1.2.getD p.2 p.2)
      (step := fun par acc e =>
        if e.1 == par.2 then min acc (par.1.getD e.2 e.2)
        else if e.2 == par.2 then min acc (par.1.getD e.1 e.1)
        else acc)
      (by fun_prop) (by fun_prop) (by fun_prop) hstep
      (B := fun p => p.1.2.getD p.2 p.2)
      (by
        have hinit : ComputableInPolyTime
            (fun p : (List (ℕ × ℕ) × List ℕ) × ℕ => p.1.2.getD p.2 p.2)
            (encPair (encPair (encList (encPair encUnary encUnary)) (encList encUnary)) encUnary)
            encUnary := by fun_prop
        exact hinit.polyBounded)
      (by
        intro p i _
        simp only [encUnary_apply, List.length_replicate]
        exact relaxOne_le_init (p.1.1.take i) p.1.2 p.2)
  simpa only [relaxOne] using hfold

private theorem computableInPolyTime_relaxStep :
    ComputableInPolyTime (fun p : List (ℕ × ℕ) × List ℕ => relaxStep p.1 p.2)
      (encPair (encList (encPair encUnary encUnary)) (encList encUnary)) (encList encUnary) := by
  unfold relaxStep
  exact ComputableInPolyTime.mapWithInput (by fun_prop)
    (computableInPolyTime_relaxOne.comp (by fun_prop))

/-- `collapseRep` is computable in polynomial time on multi-tape Turing machines. -/
theorem computableInPolyTime_collapseRep :
    ComputableInPolyTime (fun p : List (ℕ × ℕ) × ℕ => collapseRep p.1 p.2)
      (encPair (encList (encPair encUnary encUnary)) encUnary) (encList encUnary) := by
  refine ComputableInPolyTime.iterateWith
    (par := fun p : List (ℕ × ℕ) × ℕ => p.1)
    (count := fun p => p.2)
    (init := fun p => List.range p.2)
    (step := relaxStep)
    (by fun_prop) (by fun_prop) (by fun_prop) computableInPolyTime_relaxStep
    (bound := fun p => p.2 * (2 * p.2 + 1))
    ?_ ?_
  · have hT : ComputableInPolyTime (fun p : List (ℕ × ℕ) × ℕ => p.2)
        (encPair (encList (encPair encUnary encUnary)) encUnary) encUnary := by fun_prop
    exact hT.polyBounded.mul (((PolyBounded.const 2).mul hT.polyBounded).add (.const 1))
  · intro p i _
    have hlen : ((relaxStep p.1)^[i] (List.range p.2)).length = p.2 :=
      iterate_relaxStep_length p.1 p.2 i
    refine (length_encList_le encUnary _ (b := p.2) fun x hx => ?_).trans ?_
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have hj' : j < p.2 := hlen ▸ hj
      have hle := iterate_relaxStep_le_self p.1 p.2 i j hj'
      rw [List.getD_eq_getElem _ _ hj] at hle
      simp only [encUnary_apply, List.length_replicate]
      omega
    · rw [hlen]

private theorem computableInPolyTime_rawId {r' d numExist : ℕ}
    (v : Sum (Fin r' × Fin d) (Fin numExist)) :
    ComputableInPolyTime
      (fun p : (ℕ × (Fin r' → ℕ)) × ℕ =>
        rawId (d := d) (numExist := numExist) p.1.1 p.1.2 p.2 v)
      (encPair (encPair encUnary (encFinFn r' encUnary)) encUnary) encUnary := by
  rcases v with ⟨i, j⟩ | e
  · dsimp only [rawId]
    have hti : ComputableInPolyTime (fun p : (ℕ × (Fin r' → ℕ)) × ℕ => p.1.2 i)
        (encPair (encPair encUnary (encFinFn r' encUnary)) encUnary) encUnary :=
      (ComputableInPolyTime.finFn_apply encUnary i).comp (by fun_prop)
    fun_prop
  · dsimp only [rawId]
    fun_prop

private theorem computableInPolyTime_gadgetReduce {r r' d : ℕ} (φ : PPFormula r r' d) :
    ComputableInPolyTime (gadgetReduce φ) (encFinStructure r') (encFinStructure r) := by
  have hN : ComputableInPolyTime (instanceBound (r' := r')) (encFinStructure r') encUnary := by
    unfold instanceBound
    exact ComputableInPolyTime.unary_max.comp
      ((encFinStructure_numVerts_polyTime .id').prod
        (ComputableInPolyTime.unary_add.comp
          (((computableInPolyTime_maxEntry r').comp (encFinStructure_tuples_polyTime .id')).prod
            (.const 1))))
  have hT : ComputableInPolyTime
      (fun I : FinStructure r' => instanceBound I * d + I.tuples.length * φ.numExist)
      (encFinStructure r') encUnary := by
    have hlen : ComputableInPolyTime (fun I : FinStructure r' => I.tuples.length)
        (encFinStructure r') encUnary := by fun_prop
    fun_prop
  have heq : ComputableInPolyTime (gadgetEqPairs φ) (encFinStructure r')
      (encList (encPair encUnary encUnary)) := by
    unfold gadgetEqPairs
    refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
    refine ComputableInPolyTime.mapConst φ.eqAtoms fun eq _ => ?_
    have h1 := (computableInPolyTime_rawId (r' := r') (d := d) (numExist := φ.numExist) eq.1).comp
      (show ComputableInPolyTime
        (fun p : FinStructure r' × ((Fin r' → ℕ) × ℕ) => ((instanceBound p.1, p.2.1), p.2.2))
        (encPair (encFinStructure r') (encPair (encFinFn r' encUnary) encUnary))
        (encPair (encPair encUnary (encFinFn r' encUnary)) encUnary) by fun_prop)
    have h2 := (computableInPolyTime_rawId (r' := r') (d := d) (numExist := φ.numExist) eq.2).comp
      (show ComputableInPolyTime
        (fun p : FinStructure r' × ((Fin r' → ℕ) × ℕ) => ((instanceBound p.1, p.2.1), p.2.2))
        (encPair (encFinStructure r') (encPair (encFinFn r' encUnary) encUnary))
        (encPair (encPair encUnary (encFinFn r' encUnary)) encUnary) by fun_prop)
    exact h1.prod h2
  have hrep : ComputableInPolyTime
      (fun I : FinStructure r' =>
        collapseRep (gadgetEqPairs φ I) (instanceBound I * d + I.tuples.length * φ.numExist))
      (encFinStructure r') (encList encUnary) :=
    computableInPolyTime_collapseRep.comp (heq.prod hT)
  have htuples : ComputableInPolyTime (fun I : FinStructure r' => (gadgetReduce φ I).tuples)
      (encFinStructure r') (encList (encFinFn r encUnary)) := by
    dsimp only [gadgetReduce]
    refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
    refine ComputableInPolyTime.mapConst φ.relAtoms fun a _ => ?_
    refine ComputableInPolyTime.finFn fun i => ?_
    have hidx := (computableInPolyTime_rawId (r' := r') (d := d) (numExist :=
      φ.numExist) (a i)).comp
      (show ComputableInPolyTime
        (fun p : FinStructure r' × ((Fin r' → ℕ) × ℕ) => ((instanceBound p.1, p.2.1), p.2.2))
        (encPair (encFinStructure r') (encPair (encFinFn r' encUnary) encUnary))
        (encPair (encPair encUnary (encFinFn r' encUnary)) encUnary) by fun_prop)
    have hrep' : ComputableInPolyTime
        (fun p : FinStructure r' × ((Fin r' → ℕ) × ℕ) =>
          collapseRep (gadgetEqPairs φ p.1)
            (instanceBound p.1 * d + p.1.tuples.length * φ.numExist))
        (encPair (encFinStructure r') (encPair (encFinFn r' encUnary) encUnary))
        (encList encUnary) := hrep.comp (ComputableInPolyTime.fst _ _)
    fun_prop
  exact encFinStructure_mk_polyTime hT htuples

/-- **Gadget reduction theorem**:
if `(A', B')` is pp-constructible from `(A, B)`, then `PCSP(A', B')` reduces in polynomial time
to `PCSP(A, B)`.
-/
theorem polyTimeReducible_pcsp_of_ppConstructible {r r' : ℕ}
    {A : Template.{u} r} {B : Template.{v} r}
    {A' : Template.{u'} r'} {B' : Template.{v'} r'}
    (hAB : A.HasHom B) (hAB' : A'.HasHom B')
    [Nonempty A.Domain]
    (hPP : PPConstructible A B A' B') :
    PromiseProblem.PolyTimeReducible (encFinStructure r') (encFinStructure r)
      (pcsp A' B' hAB') (pcsp A B hAB) := by
  obtain ⟨d, φ, ⟨h₁⟩, ⟨h₂⟩⟩ := hPP
  refine ⟨gadgetReduce φ, computableInPolyTime_gadgetReduce φ, ?_, ?_⟩
  · -- Completeness: `I → A'` implies `gadgetReduce φ I → A`.
    intro I ⟨hI⟩
    have hex : ∀ p : (Fin r' → ℕ) × ℕ, p ∈ I.tuples.zipIdx →
        ∃ y : Fin φ.numExist → A.Domain,
          let val := Sum.elim (Function.uncurry fun i j => h₁ (hI (p.1 i)) j) y
          (∀ a ∈ φ.relAtoms, (val ∘ a) ∈ A.rel) ∧
          (∀ eq ∈ φ.eqAtoms, val eq.1 = val eq.2) := by
      intro p hp
      have ht : p.1 ∈ I.tuples := by
        have hget := List.mem_zipIdx_iff_getElem?.mp hp
        have hlen : p.2 < I.tuples.length := by
          by_contra h
          have : I.tuples[p.2]? = none := List.getElem?_eq_none (by omega)
          simp [this] at hget
        rw [List.getElem?_eq_getElem hlen] at hget
        exact Option.some.inj hget ▸ List.getElem_mem hlen
      exact h₁.map_rel' (hI.map_rel' ht)
    classical
    choose y hy using hex
    let N := instanceBound I
    let T := N * d + I.tuples.length * φ.numExist
    let a₀ : A.Domain := Classical.arbitrary A.Domain
    let g : ℕ → A.Domain := fun u =>
      if hlt : u < N * d then
        h₁ (hI (u / d)) ⟨u % d, by
          have hd : 0 < d := Nat.pos_of_ne_zero (fun hd0 => by simp [hd0] at hlt)
          exact Nat.mod_lt u hd⟩
      else
        let rem := u - N * d
        if hrem : rem < I.tuples.length * φ.numExist then
          have hne_ex : 0 < φ.numExist :=
            Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hrem)
          have hidx : rem / φ.numExist < I.tuples.length := by
            rw [Nat.div_lt_iff_lt_mul hne_ex]
            exact hrem
          if hmem : (I.tuples[rem / φ.numExist], rem / φ.numExist) ∈ I.tuples.zipIdx then
            y (I.tuples[rem / φ.numExist], rem / φ.numExist) hmem ⟨rem % φ.numExist,
              Nat.mod_lt rem hne_ex⟩
          else a₀
        else a₀
    have hg_raw : ∀ (t : Fin r' → ℕ) (tIdx : ℕ) (ht : (t, tIdx) ∈ I.tuples.zipIdx)
        (v : Sum (Fin r' × Fin d) (Fin φ.numExist)),
        g (rawId (d := d) (numExist := φ.numExist) N t tIdx v) =
          Sum.elim (Function.uncurry fun i j => h₁ (hI (t i)) j) (y (t, tIdx) ht) v := by
      intro t tIdx ht v
      have hget : I.tuples[tIdx]? = some t ∧ tIdx < I.tuples.length := by
        have h := List.mem_zipIdx_iff_getElem?.mp ht
        have hlen : tIdx < I.tuples.length := by
          by_contra hlt
          have hnone : I.tuples[tIdx]? = none := List.getElem?_eq_none (by omega)
          simp [hnone] at h
        exact ⟨by simpa using h, hlen⟩
      have ht_mem : t ∈ I.tuples := by
        rw [List.getElem?_eq_getElem hget.2] at hget
        exact Option.some.inj hget.1 ▸ List.getElem_mem hget.2
      have hti : ∀ i, t i < N := fun i =>
        Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (le_maxEntry ht_mem i)) (le_max_right _ _)
      rcases v with ⟨i, j⟩ | e
      · have hd : 0 < d := Nat.zero_lt_of_lt j.2
        have hlt : t i * d + j.1 < N * d := by
          have h1 : t i + 1 ≤ N := hti i
          have h2 : t i * d + j.1 < (t i + 1) * d := by
            rw [Nat.add_mul, Nat.one_mul]; omega
          exact lt_of_lt_of_le h2 (Nat.mul_le_mul_right d h1)
        dsimp only [g, rawId, Sum.elim_inl, Function.uncurry_apply_pair]
        simp only [hlt, ↓reduceDIte]
        have hdiv : (t i * d + j.1) / d = t i := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt j.2, Nat.zero_add]
        have hmod : (t i * d + j.1) % d = j.1 := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]
        simp [hdiv, hmod]
      · have he_pos : 0 < φ.numExist := Nat.zero_lt_of_lt e.2
        have hnotlt : ¬ (N * d + tIdx * φ.numExist + e.1 < N * d) := by omega
        have hrem_eq : N * d + tIdx * φ.numExist + e.1 - N * d = tIdx * φ.numExist + e.1 := by
          omega
        have hrem_lt : tIdx * φ.numExist + e.1 < I.tuples.length * φ.numExist := by
          have h1 : tIdx + 1 ≤ I.tuples.length := hget.2
          have h2 : tIdx * φ.numExist + e.1 < (tIdx + 1) * φ.numExist := by
            rw [Nat.add_mul, Nat.one_mul]; omega
          exact lt_of_lt_of_le h2 (Nat.mul_le_mul_right φ.numExist h1)
        have hdiv : (tIdx * φ.numExist + e.1) / φ.numExist = tIdx := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ he_pos, Nat.div_eq_of_lt e.2, Nat.zero_add]
        have hmod : (tIdx * φ.numExist + e.1) % φ.numExist = e.1 := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt e.2]
        have ht_eq : I.tuples[tIdx]'hget.2 = t := by
          rw [List.getElem?_eq_getElem hget.2] at hget
          exact Option.some.inj hget.1
        dsimp only [g, rawId, Sum.elim_inr]
        simp only [hnotlt, ↓reduceDIte, hrem_eq, hrem_lt, hdiv, hmod]
        have hmem' : (I.tuples[tIdx]'hget.2, tIdx) ∈ I.tuples.zipIdx := by
          rw [ht_eq]; exact ht
        simp only [hmem', ↓reduceDIte]
        congr 1
        exact Prod.ext ht_eq rfl
    have hg_eq : ∀ p ∈ gadgetEqPairs φ I, g p.1 = g p.2 := by
      intro p hp
      rw [gadgetEqPairs, List.mem_flatMap] at hp
      obtain ⟨⟨t, tIdx⟩, ht, hmap⟩ := hp
      rw [List.mem_map] at hmap
      obtain ⟨eq, heq, rfl⟩ := hmap
      rw [hg_raw t tIdx ht eq.1, hg_raw t tIdx ht eq.2]
      exact (hy (t, tIdx) ht).2 eq heq
    refine ⟨Template.Hom.mk g fun (s : Fin r → ℕ) hs => ?_⟩
    change s ∈ (gadgetReduce φ I).tuples at hs
    dsimp only [gadgetReduce] at hs
    rw [List.mem_flatMap] at hs
    obtain ⟨⟨t, tIdx⟩, ht, hmap⟩ := hs
    rw [List.mem_map] at hmap
    obtain ⟨a, ha, rfl⟩ := hmap
    convert (hy (t, tIdx) ht).1 a ha using 1
    funext i
    change g ((collapseRep (gadgetEqPairs φ I) T).getD
        (rawId (d := d) (numExist := φ.numExist) N t tIdx (a i))
        (rawId (d := d) (numExist := φ.numExist) N t tIdx (a i))) =
      Sum.elim (Function.uncurry fun i j => h₁ (hI (t i)) j) (y (t, tIdx) ht) (a i)
    rw [collapseRep_preserves _ _ g hg_eq, hg_raw t tIdx ht (a i)]
  · -- Soundness (contrapositive): `gadgetReduce φ I → B` implies `I → B'`.
    intro I hno ⟨hG⟩
    apply hno
    let N := instanceBound I
    let T := N * d + I.tuples.length * φ.numExist
    let rep := collapseRep (gadgetEqPairs φ I) T
    have heq_lt : ∀ p ∈ gadgetEqPairs φ I, p.1 < T ∧ p.2 < T := by
      intro p hp
      rw [gadgetEqPairs, List.mem_flatMap] at hp
      obtain ⟨⟨t, tIdx⟩, ht, hmap⟩ := hp
      rw [List.mem_map] at hmap
      obtain ⟨eq, _, rfl⟩ := hmap
      have hget := List.mem_zipIdx_iff_getElem?.mp ht
      have hlen : tIdx < I.tuples.length := by
        by_contra hlt
        have hnone : I.tuples[tIdx]? = none := List.getElem?_eq_none (by omega)
        simp [hnone] at hget
      have ht_mem : t ∈ I.tuples := by
        rw [List.getElem?_eq_getElem hlen] at hget
        dsimp only at hget
        exact Option.some.inj hget ▸ List.getElem_mem hlen
      have hti : ∀ i, t i < N := fun i =>
        Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (le_maxEntry ht_mem i)) (le_max_right _ _)
      exact ⟨rawId_lt hti hlen eq.1, rawId_lt hti hlen eq.2⟩
    refine ⟨Template.Hom.mk
      (fun (v : ℕ) => h₂ fun j => hG (rep.getD (v * d + j.1) (v * d + j.1)))
      (fun (t : Fin r' → ℕ) ht => ?_)⟩
    change t ∈ I.tuples at ht
    obtain ⟨tIdx, htIdx, hget⟩ := List.getElem_of_mem ht
    have hzip : (t, tIdx) ∈ I.tuples.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem htIdx, hget]
    have hU : (fun i j => hG (rep.getD (t i * d + j.1) (t i * d + j.1))) ∈ φ.eval B := by
      refine ⟨fun e => hG (rep.getD (N * d + tIdx * φ.numExist + e.1)
        (N * d + tIdx * φ.numExist + e.1)), ?_, ?_⟩
      · intro a ha
        have hmem : (fun i => rep.getD
            (rawId (d := d) (numExist := φ.numExist) N t tIdx (a i))
            (rawId (d := d) (numExist := φ.numExist) N t tIdx (a i))) ∈
            (gadgetReduce φ I).tuples := by
          dsimp only [gadgetReduce]
          rw [List.mem_flatMap]
          refine ⟨(t, tIdx), hzip, ?_⟩
          rw [List.mem_map]
          exact ⟨a, ha, rfl⟩
        have hmap := hG.map_rel' hmem
        convert hmap using 1
        funext i
        change Sum.elim (Function.uncurry fun i j => hG (rep.getD (t i * d + j.1) (t i * d + j.1)))
            (fun e => hG (rep.getD (N * d + tIdx * φ.numExist + e.1)
              (N * d + tIdx * φ.numExist + e.1))) (a i) =
          hG (rep.getD (rawId (d := d) (numExist := φ.numExist) N t tIdx (a i))
            (rawId (d := d) (numExist := φ.numExist) N t tIdx (a i)))
        rcases a i with ⟨i', j'⟩ | e <;> rfl
      · intro eq heq
        have hmem : (rawId (d := d) (numExist := φ.numExist) N t tIdx eq.1,
            rawId (d := d) (numExist := φ.numExist) N t tIdx eq.2) ∈ gadgetEqPairs φ I := by
          rw [gadgetEqPairs, List.mem_flatMap]
          refine ⟨(t, tIdx), hzip, ?_⟩
          rw [List.mem_map]
          exact ⟨eq, heq, rfl⟩
        have hrep_eq := collapseRep_eq_of_mem heq_lt hmem
        cases h1 : eq.1 <;> cases h2 : eq.2 <;>
          simp only [Sum.elim_inl, Sum.elim_inr]
        all_goals
          exact congrArg (fun (u : ℕ) => hG u) (by simpa only [rep, rawId, h1, h2] using hrep_eq)
    exact h₂.map_rel' hU

/-- **BBKO algebraic gadget-reduction theorem**
: for finite `A, A'` and nonempty `A, B'`, a minion homomorphism
`Pol(A, B) → Pol(A', B')` induces a polynomial-time reduction `PCSP(A', B') ≤_p PCSP(A, B)`.
-/
theorem polyTimeReducible_pcsp_of_polMinion_hasHom {r r' : ℕ}
    {A : Template.{u} r} {B : Template.{v} r}
    {A' : Template.{u'} r'} {B' : Template.{v'} r'}
    (hAB : A.HasHom B) (hAB' : A'.HasHom B')
    [Finite A.Domain] [Finite A'.Domain] [Finite A'.rel]
    [Nonempty A.Domain] [Nonempty B'.Domain]
    (hPol : (polMinion A B).HasHom (polMinion A' B')) :
    PromiseProblem.PolyTimeReducible (encFinStructure r') (encFinStructure r)
      (pcsp A' B' hAB') (pcsp A B hAB) :=
  polyTimeReducible_pcsp_of_ppConstructible hAB hAB'
    ((ppConstructible_iff_polMinion_hasHom A B A' B').mpr hPol)

end Cslib.Complexity.PCSP

