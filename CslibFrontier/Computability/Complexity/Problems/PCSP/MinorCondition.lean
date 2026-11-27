/-
Copyright (c) 2026 PanMath Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.Complexity.Problems.PCSP.Gadgets

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Bipartite Minor Conditions and PMC-to-PCSP Reduction

This module formalizes bipartite minor conditions (`MinorConstraint`, `MinorCondition`), the
promise minor-condition problem `pmc M m` (`PMC_M(m)`), and its deterministic polynomial-time
reduction to `PCSP(A, B)`.

## Main definitions

* `Cslib.Complexity.PCSP.MinorConstraint`: a single minor constraint `(u, v, π)`.
* `Cslib.Complexity.PCSP.MinorCondition`: a bipartite minor condition of maximum arity `m`.
* `Cslib.Complexity.PCSP.encMinorCondition`: canonical unary/list encoding of `MinorCondition m`.
* `Cslib.Complexity.PCSP.MinorCondition.TriviallySat`: satisfiability by coordinate projections.
* `Cslib.Complexity.PCSP.MinorCondition.SatIn`: satisfiability in a minion `M`.
* `Cslib.Complexity.PCSP.pmc`: the promise problem `PMC_M(m)`.
* `Cslib.Complexity.PCSP.pmcToPcsp`: polynomial-time gadget reduction from `PMC_{Pol(A, B)}(m)` to
  `PCSP(A, B)`.

## Main results

* `Cslib.Complexity.PCSP.MinorCondition.TriviallySat.satIn`: trivially satisfiable minor conditions
  are satisfiable in every minion with a nonempty unary carrier.
* `Cslib.Complexity.PCSP.polyTimeReducible_pmc_pcsp`: `PMC_{Pol(A, B)}(m) ≤_p PCSP(A, B)`.
-/

public section

namespace Cslib.Complexity.PCSP

open Cslib.Complexity
open Turing.MultiTapeTM

universe u v

/-- A single bipartite minor constraint `(leftIdx, rightIdx, map)`. -/
@[ext]
structure MinorConstraint where
  /-- Index of the left variable. -/
  leftIdx : ℕ
  /-- Index of the right variable. -/
  rightIdx : ℕ
  /-- The minor map `Fin p → Fin q`, stored as a list of length `p`. -/
  map : List ℕ
  deriving DecidableEq

/-- Canonical encoding of a `MinorConstraint` with unary indices and map entries. -/
def encMinorConstraint : MinorConstraint ↪ List Bool where
  toFun c := encPair encUnary (encPair encUnary (encList encUnary)) (c.leftIdx, c.rightIdx, c.map)
  inj' := by
    intro c₁ c₂ h
    have h' := (encPair encUnary (encPair encUnary (encList encUnary))).injective h
    exact MinorConstraint.ext (congrArg Prod.fst h')
      (congrArg (fun p => p.2.1) h') (congrArg (fun p => p.2.2) h')

private theorem isPolyTime_toTriple_minorConstraint :
    ComputableInPolyTime (fun c : MinorConstraint => (c.leftIdx, c.rightIdx, c.map))
      encMinorConstraint (encPair encUnary (encPair encUnary (encList encUnary))) :=
  .of_eq fun _ => rfl

/-- Reading `MinorConstraint.leftIdx` is polynomial-time. -/
@[fun_prop]
theorem encMinorConstraint_leftIdx_polyTime {Input : Type} {encIn : Input ↪ List Bool}
    {f : Input → MinorConstraint} (hf : ComputableInPolyTime f encIn encMinorConstraint) :
    ComputableInPolyTime (fun x => (f x).leftIdx) encIn encUnary :=
  ((ComputableInPolyTime.fst _ _).comp isPolyTime_toTriple_minorConstraint).comp hf

/-- Reading `MinorConstraint.rightIdx` is polynomial-time. -/
@[fun_prop]
theorem encMinorConstraint_rightIdx_polyTime {Input : Type} {encIn : Input ↪ List Bool}
    {f : Input → MinorConstraint} (hf : ComputableInPolyTime f encIn encMinorConstraint) :
    ComputableInPolyTime (fun x => (f x).rightIdx) encIn encUnary :=
  (((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)).comp
    isPolyTime_toTriple_minorConstraint).comp hf

/-- Reading `MinorConstraint.map` is polynomial-time. -/
@[fun_prop]
theorem encMinorConstraint_map_polyTime {Input : Type} {encIn : Input ↪ List Bool}
    {f : Input → MinorConstraint} (hf : ComputableInPolyTime f encIn encMinorConstraint) :
    ComputableInPolyTime (fun x => (f x).map) encIn (encList encUnary) :=
  (((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)).comp
    isPolyTime_toTriple_minorConstraint).comp hf

/-- Constructing a `MinorConstraint` is polynomial-time. -/
@[fun_prop]
theorem encMinorConstraint_mk_polyTime {Input : Type} {encIn : Input ↪ List Bool}
    {l r : Input → ℕ} {mp : Input → List ℕ}
    (hl : ComputableInPolyTime l encIn encUnary)
    (hr : ComputableInPolyTime r encIn encUnary)
    (hmp : ComputableInPolyTime mp encIn (encList encUnary)) :
    ComputableInPolyTime (fun x => MinorConstraint.mk (l x) (r x) (mp x))
      encIn encMinorConstraint :=
  (hl.prod (hr.prod hmp)).of_enc_eq fun _ => rfl

/-- A bipartite minor condition of maximum arity `m`: lists of left and right variable arities
together with a list of minor constraints. -/
@[ext]
structure MinorCondition (m : ℕ) where
  /-- Arities of the left variables. -/
  leftArities : List ℕ
  /-- Arities of the right variables. -/
  rightArities : List ℕ
  /-- Minor constraints between left and right variables. -/
  constraints : List MinorConstraint
  deriving DecidableEq

/-- Canonical encoding of `MinorCondition m`. -/
def encMinorCondition (m : ℕ) : MinorCondition m ↪ List Bool where
  toFun s := encPair (encList encUnary)
    (encPair (encList encUnary) (encList encMinorConstraint))
    (s.leftArities, s.rightArities, s.constraints)
  inj' := by
    intro s₁ s₂ h
    have h' := (encPair (encList encUnary)
      (encPair (encList encUnary) (encList encMinorConstraint))).injective h
    exact MinorCondition.ext (congrArg Prod.fst h')
      (congrArg (fun p => p.2.1) h') (congrArg (fun p => p.2.2) h')

private theorem isPolyTime_toTriple_minorCondition (m : ℕ) :
    ComputableInPolyTime
      (fun s : MinorCondition m => (s.leftArities, s.rightArities, s.constraints))
      (encMinorCondition m)
      (encPair (encList encUnary) (encPair (encList encUnary) (encList encMinorConstraint))) :=
  .of_eq fun _ => rfl

/-- Reading `MinorCondition.leftArities` is polynomial-time. -/
@[fun_prop]
theorem encMinorCondition_leftArities_polyTime {m : ℕ} {Input : Type}
    {encIn : Input ↪ List Bool} {f : Input → MinorCondition m}
    (hf : ComputableInPolyTime f encIn (encMinorCondition m)) :
    ComputableInPolyTime (fun x => (f x).leftArities) encIn (encList encUnary) :=
  ((ComputableInPolyTime.fst _ _).comp (isPolyTime_toTriple_minorCondition m)).comp hf

/-- Reading `MinorCondition.rightArities` is polynomial-time. -/
@[fun_prop]
theorem encMinorCondition_rightArities_polyTime {m : ℕ} {Input : Type}
    {encIn : Input ↪ List Bool} {f : Input → MinorCondition m}
    (hf : ComputableInPolyTime f encIn (encMinorCondition m)) :
    ComputableInPolyTime (fun x => (f x).rightArities) encIn (encList encUnary) :=
  (((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)).comp
    (isPolyTime_toTriple_minorCondition m)).comp hf

/-- Reading `MinorCondition.constraints` is polynomial-time. -/
@[fun_prop]
theorem encMinorCondition_constraints_polyTime {m : ℕ} {Input : Type}
    {encIn : Input ↪ List Bool} {f : Input → MinorCondition m}
    (hf : ComputableInPolyTime f encIn (encMinorCondition m)) :
    ComputableInPolyTime (fun x => (f x).constraints) encIn (encList encMinorConstraint) :=
  (((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)).comp
    (isPolyTime_toTriple_minorCondition m)).comp hf

/-- Constructing a `MinorCondition m` is polynomial-time. -/
@[fun_prop]
theorem encMinorCondition_mk_polyTime {m : ℕ} {Input : Type} {encIn : Input ↪ List Bool}
    {la ra : Input → List ℕ} {cs : Input → List MinorConstraint}
    (hla : ComputableInPolyTime la encIn (encList encUnary))
    (hra : ComputableInPolyTime ra encIn (encList encUnary))
    (hcs : ComputableInPolyTime cs encIn (encList encMinorConstraint)) :
    ComputableInPolyTime (fun x => MinorCondition.mk (m := m) (la x) (ra x) (cs x))
      encIn (encMinorCondition m) :=
  (hla.prod (hra.prod hcs)).of_enc_eq fun _ => rfl

namespace MinorCondition

/-- A minor condition of maximum arity `m` is well-formed when every variable has arity at most
`m` and every constraint references valid indices with a well-typed minor map. -/
@[expose]
def WellFormed {m : ℕ} (Φ : MinorCondition m) : Prop :=
  (∀ p ∈ Φ.leftArities, p ≤ m) ∧
  (∀ q ∈ Φ.rightArities, q ≤ m) ∧
  ∀ c ∈ Φ.constraints,
    c.leftIdx < Φ.leftArities.length ∧
    c.rightIdx < Φ.rightArities.length ∧
    c.map.length = Φ.leftArities.getD c.leftIdx 0 ∧
    ∀ i < c.map.length, c.map.getD i 0 < Φ.rightArities.getD c.rightIdx 0

/-- A minor condition is trivially satisfiable if there is a projection assignment mapping each
variable to a coordinate in its arity that satisfies every minor constraint. -/
@[expose]
def TriviallySat {m : ℕ} (Φ : MinorCondition m) : Prop :=
  Φ.WellFormed ∧
  ∃ (ℓ r : ℕ → ℕ),
    (∀ u < Φ.leftArities.length, ℓ u < Φ.leftArities.getD u 0) ∧
    (∀ v < Φ.rightArities.length, r v < Φ.rightArities.getD v 0) ∧
    ∀ c ∈ Φ.constraints, c.map.getD (ℓ c.leftIdx) 0 = r c.rightIdx

/-- A minor condition is satisfiable in a minion `M` if there exist assignments `f_u ∈ M^(p_u)`
and `g_v ∈ M^(q_v)` satisfying `(f_u)_π = g_v` for every constraint `(u, v, π)`. -/
@[expose]
def SatIn {m : ℕ} (M : Minion.{u}) (Φ : MinorCondition m) : Prop :=
  Φ.WellFormed ∧
  ∃ (f : ∀ u : Fin Φ.leftArities.length, M.carrier (Φ.leftArities[u]))
    (g : ∀ v : Fin Φ.rightArities.length, M.carrier (Φ.rightArities[v])),
    ∀ c ∈ Φ.constraints,
      ∀ (hu : c.leftIdx < Φ.leftArities.length) (hv : c.rightIdx < Φ.rightArities.length)
        (hmap : ∀ i : Fin (Φ.leftArities[c.leftIdx]'hu),
          c.map.getD i.1 0 < Φ.rightArities[c.rightIdx]'hv),
        M.minor (fun i => ⟨c.map.getD i.1 0, hmap i⟩) (f ⟨c.leftIdx, hu⟩) = g ⟨c.rightIdx, hv⟩

/-- Trivial satisfiability implies satisfiability in any minion with a unary element. -/
theorem TriviallySat.satIn {m : ℕ} {M : Minion.{u}} (hM : Nonempty (M.carrier 1))
    {Φ : MinorCondition m} (htriv : Φ.TriviallySat) : Φ.SatIn M := by
  obtain ⟨hWF, ℓ, r, hℓ, hr, hsat⟩ := htriv
  obtain ⟨e₁⟩ := hM
  refine ⟨hWF,
    fun u => M.minor (fun _ : Fin 1 => (⟨ℓ u.1, by
      have h := hℓ u.1 u.2; rwa [List.getD_eq_getElem _ _ u.2] at h⟩ : Fin (Φ.leftArities[u])) ) e₁,
    fun v => M.minor (fun _ : Fin 1 => (⟨r v.1, by
      have h := hr v.1 v.2; rwa [List.getD_eq_getElem _ _ v.2] at h⟩ : Fin (Φ.rightArities[v]))) e₁,
    fun c hc hu hv hmap => ?_⟩
  rw [← M.minor_comp]
  congr 1
  funext _
  apply Fin.ext
  exact hsat c hc

end MinorCondition

/-- The promise minor-condition problem `PMC_M(m)`: yes-instances are trivially satisfiable
minor conditions of max arity `m`, and no-instances are well-formed conditions unsatisfiable in
`M`. -/
def pmc {m : ℕ} (M : Minion.{u}) (hM : Nonempty (M.carrier 1)) :
    PromiseProblem (MinorCondition m) where
  yes := {Φ | Φ.TriviallySat}
  no := {Φ | Φ.WellFormed ∧ ¬ Φ.SatIn M}
  disjoint := Set.disjoint_left.mpr fun _ hyes hno => hno.2 (hyes.satIn hM)

@[simp]
theorem mem_yes_pmc {m : ℕ} {M : Minion.{u}} {hM : Nonempty (M.carrier 1)}
    {Φ : MinorCondition m} :
    Φ ∈ (pmc M hM).yes ↔ Φ.TriviallySat :=
  Iff.rfl

@[simp]
theorem mem_no_pmc {m : ℕ} {M : Minion.{u}} {hM : Nonempty (M.carrier 1)}
    {Φ : MinorCondition m} :
    Φ ∈ (pmc M hM).no ↔ Φ.WellFormed ∧ ¬ Φ.SatIn M :=
  Iff.rfl

/-! ### Reduction from `PMC_{Pol(A, B)}(m)` to `PCSP(A, B)` -/

/-- Pad a tuple `x : Fin p → Fin nA` (for `p ≤ m`) to length `m` using a default value `d₀`. -/
private def padTuple {p m nA : ℕ} (d₀ : Fin nA) (x : Fin p → Fin nA) : Fin m → Fin nA :=
  fun i => if hi : i.1 < p then x ⟨i.1, hi⟩ else d₀

private noncomputable def pmcEqs {m nA : ℕ} (d₀ : Fin nA) (Φ : MinorCondition m) :
    List (ℕ × ℕ) :=
  let eW : (Fin m → Fin nA) ≃ Fin (nA ^ m) := Fintype.equivFinOfCardEq (by simp)
  let nW := nA ^ m
  let L := Φ.leftArities.length
  let R := Φ.rightArities.length
  Φ.constraints.flatMap fun c =>
    let pu := Φ.leftArities.getD c.leftIdx 0
    let qv := Φ.rightArities.getD c.rightIdx 0
    (List.range (m + 1)).flatMap fun p =>
      (List.range (m + 1)).flatMap fun q =>
        if pu = p ∧ qv = q ∧ c.leftIdx < L ∧ c.rightIdx < R then
          (Finset.univ : Finset (Fin q → Fin nA)).toList.map fun y =>
            let x : Fin p → Fin nA := fun i =>
              let idx := c.map.getD i.1 0
              if hidx : idx < q then y ⟨idx, hidx⟩ else d₀
            (c.leftIdx * nW + (eW (padTuple d₀ x)).1,
             (L + c.rightIdx) * nW + (eW (padTuple d₀ y)).1)
        else []

/-- Given a finite template `A` with enumeration `eA : A.Domain ≃ Fin nA` and default `d₀`, build
the polynomial-time reduction `pmcToPcsp` from `MinorCondition m` to `FinStructure r`. -/
noncomputable def pmcToPcsp {r m nA : ℕ} (A : Template.{u} r) (eA : A.Domain ≃ Fin nA)
    (d₀ : Fin nA) (Φ : MinorCondition m) : FinStructure r :=
  let eW : (Fin m → Fin nA) ≃ Fin (nA ^ m) := Fintype.equivFinOfCardEq (by simp)
  let nW := nA ^ m
  let L := Φ.leftArities.length
  let R := Φ.rightArities.length
  let T := (L + R) * nW
  let rep := collapseRep (pmcEqs d₀ Φ) T
  let leftTuples : List (Fin r → ℕ) :=
    Φ.leftArities.zipIdx.flatMap fun (pu, u) =>
      (List.range (m + 1)).flatMap fun p =>
        if pu = p then
          ((Finset.univ : Finset (Fin r → Fin p → Fin nA)).toList.filter fun X =>
            @decide (∀ j : Fin p, (fun i => eA.symm (X i j)) ∈ A.rel)
              (Classical.propDecidable _)).map fun X i =>
            let raw := u * nW + (eW (padTuple d₀ (X i))).1
            rep.getD raw raw
        else []
  let rightTuples : List (Fin r → ℕ) :=
    Φ.rightArities.zipIdx.flatMap fun (qv, v) =>
      (List.range (m + 1)).flatMap fun q =>
        if qv = q then
          ((Finset.univ : Finset (Fin r → Fin q → Fin nA)).toList.filter fun Y =>
            @decide (∀ j : Fin q, (fun i => eA.symm (Y i j)) ∈ A.rel)
              (Classical.propDecidable _)).map fun Y i =>
            let raw := (L + v) * nW + (eW (padTuple d₀ (Y i))).1
            rep.getD raw raw
        else []
  { numVerts := T, tuples := leftTuples ++ rightTuples }

private theorem computableInPolyTime_pmcToPcsp {r m nA : ℕ} (A : Template.{u} r)
    (eA : A.Domain ≃ Fin nA) (d₀ : Fin nA) :
    ComputableInPolyTime (pmcToPcsp (m := m) A eA d₀)
      (encMinorCondition m) (encFinStructure r) := by
  classical
  let eW : (Fin m → Fin nA) ≃ Fin (nA ^ m) := Fintype.equivFinOfCardEq (by simp)
  let nW := nA ^ m
  have hL : ComputableInPolyTime (fun Φ : MinorCondition m => Φ.leftArities.length)
      (encMinorCondition m) encUnary := by fun_prop
  have hR : ComputableInPolyTime (fun Φ : MinorCondition m => Φ.rightArities.length)
      (encMinorCondition m) encUnary := by fun_prop
  have hT : ComputableInPolyTime
      (fun Φ : MinorCondition m => (Φ.leftArities.length + Φ.rightArities.length) * nW)
      (encMinorCondition m) encUnary := by fun_prop
  have heqs : ComputableInPolyTime (pmcEqs (m := m) d₀)
      (encMinorCondition m) (encList (encPair encUnary encUnary)) := by
    unfold pmcEqs
    refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
    refine ComputableInPolyTime.flatMapConst (List.range (m + 1)) fun p _ => ?_
    refine ComputableInPolyTime.flatMapConst (List.range (m + 1)) fun q _ => ?_
    have hcond : ComputableInPolyTime
        (fun x : MinorCondition m × MinorConstraint =>
          decide (x.1.leftArities.getD x.2.leftIdx 0 = p ∧
            x.1.rightArities.getD x.2.rightIdx 0 = q ∧
            x.2.leftIdx < x.1.leftArities.length ∧
            x.2.rightIdx < x.1.rightArities.length))
        (encPair (encMinorCondition m) encMinorConstraint) encBool := by fun_prop
    have hbranch : ComputableInPolyTime
        (fun x : MinorCondition m × MinorConstraint =>
          (Finset.univ : Finset (Fin q → Fin nA)).toList.map fun y =>
            let x_1 : Fin p → Fin nA := fun i =>
              let idx := x.2.map.getD i.1 0
              if hidx : idx < q then y ⟨idx, hidx⟩ else d₀
            (x.2.leftIdx * nW + (eW (padTuple d₀ x_1)).1,
             (x.1.leftArities.length + x.2.rightIdx) * nW + (eW (padTuple d₀ y)).1))
        (encPair (encMinorCondition m) encMinorConstraint)
        (encList (encPair encUnary encUnary)) := by
      refine ComputableInPolyTime.mapConst (Finset.univ : Finset (Fin q → Fin nA)).toList
        fun y _ => ?_
      have hfin : ComputableInPolyTime
          (fun c : MinorConstraint =>
            (eW (padTuple d₀ fun i : Fin p =>
              let idx := c.map.getD i.1 0
              if hidx : idx < q then y ⟨idx, hidx⟩ else d₀)).1)
          encMinorConstraint encUnary := by
        -- Only depends on the finite tuple `fun i : Fin p => min (c.map.getD i.1 0) q`.
        let key : MinorConstraint → (Fin p → Fin (q + 1)) := fun c i =>
          let idx := c.map.getD i.1 0
          if hidx : idx < q then ⟨idx, Nat.lt_succ_of_lt hidx⟩ else ⟨q, Nat.lt_succ_self q⟩
        have hkey : ComputableInPolyTime key encMinorConstraint
            (encFinFn p (encFinEnum (Fin (q + 1)))) := by
          refine ComputableInPolyTime.finFn fun i => ?_
          have hget : ComputableInPolyTime (fun c : MinorConstraint => c.map.getD i.1 0)
              encMinorConstraint encUnary := by fun_prop
          have hcap : ComputableInPolyTime
              (fun c : MinorConstraint => min (c.map.getD i.1 0) q)
              encMinorConstraint encUnary := by fun_prop
          -- Finite dispatch on `min (c.map.getD i.1 0) q ≤ q`.
          have hlt : ∀ c : MinorConstraint, min (c.map.getD i.1 0) q < q + 1 := fun c =>
            Nat.lt_succ_of_le (Nat.min_le_right _ _)
          let toFin : ℕ → Fin (q + 1) :=
            fun k => if hk : k < q + 1 then ⟨k, hk⟩ else ⟨0, by omega⟩
          have htoFin : ComputableInPolyTime (fun c : MinorConstraint =>
              toFin (min (c.map.getD i.1 0) q)) encMinorConstraint (encFinEnum (Fin (q + 1))) := by
            have haux : ∀ (bound : ℕ), ComputableInPolyTime
                (fun k : ℕ => if k < bound then toFin k else toFin 0)
                encUnary (encFinEnum (Fin (q + 1))) := by
              intro bound
              induction bound with
              | zero => exact .const (toFin 0)
              | succ b ih =>
                have hEq : (fun k : ℕ => if k < b + 1 then toFin k else toFin 0) =
                    (fun k : ℕ => if k == b then toFin b else if k < b then toFin k else toFin 0)
                      := by
                  funext k
                  by_cases hkb : k = b
                  · subst hkb; simp
                  · have hne : (k == b) = false := beq_false_of_ne hkb
                    have hiff : (k < b + 1) ↔ (k < b) := by omega
                    simp [hne, hiff]
                rw [hEq]
                have hbeq : ComputableInPolyTime (fun k : ℕ => k == b) encUnary encBool := by
                  fun_prop
                exact hbeq.ite (.const (toFin b)) ih
            have hcomp := (haux (q + 1)).comp hcap
            exact hcomp.of_enc_eq fun c => congrArg _ (by
              simp only [Function.comp_apply, hlt c, ↓reduceIte])
          exact htoFin.of_enc_eq fun c => congrArg _ (by
            dsimp only [toFin, key]
            simp only [hlt c, ↓reduceDIte]
            apply Fin.ext
            split_ifs with h1 <;> dsimp <;> omega)
        have hpost : ComputableInPolyTime
            (fun fn : Fin p → Fin (q + 1) =>
              (eW (padTuple d₀ fun i : Fin p =>
                if h : (fn i).1 < q then y ⟨(fn i).1, h⟩ else d₀)).1)
            (encFinFn p (encFinEnum (Fin (q + 1)))) encUnary := .of_finite _
        exact (hpost.comp hkey).of_enc_eq fun c => congrArg _ (by
          dsimp only [Function.comp_apply, key]
          congr 1; congr 1; congr 1; funext i
          simp only [List.getD_eq_getElem?_getD]
          by_cases h : c.map[i.1]?.getD 0 < q <;> simp [h])
      have h1 : ComputableInPolyTime
          (fun x : MinorCondition m × MinorConstraint =>
            x.2.leftIdx * nW +
              (eW (padTuple d₀ fun i : Fin p =>
                let idx := x.2.map.getD i.1 0
                if hidx : idx < q then y ⟨idx, hidx⟩ else d₀)).1)
          (encPair (encMinorCondition m) encMinorConstraint) encUnary :=
        ComputableInPolyTime.unary_add.comp
          ((by fun_prop : ComputableInPolyTime
              (fun x : MinorCondition m × MinorConstraint => x.2.leftIdx * nW) _ _).prod
            (hfin.comp (ComputableInPolyTime.snd _ _)))
      have h2 : ComputableInPolyTime
          (fun x : MinorCondition m × MinorConstraint =>
            (x.1.leftArities.length + x.2.rightIdx) * nW + (eW (padTuple d₀ y)).1)
          (encPair (encMinorCondition m) encMinorConstraint) encUnary := by fun_prop
      exact h1.prod h2
    exact (hcond.ite hbranch (.const [])).of_enc_eq fun x => by simp [eW, nW]
  have hrep : ComputableInPolyTime
      (fun Φ : MinorCondition m =>
        collapseRep (pmcEqs d₀ Φ) ((Φ.leftArities.length + Φ.rightArities.length) * nW))
      (encMinorCondition m) (encList encUnary) :=
    computableInPolyTime_collapseRep.comp (heqs.prod hT)
  have hleft : ComputableInPolyTime
      (fun Φ : MinorCondition m =>
        Φ.leftArities.zipIdx.flatMap fun (pu, u) =>
          (List.range (m + 1)).flatMap fun p =>
            if pu = p then
              ((Finset.univ : Finset (Fin r → Fin p → Fin nA)).toList.filter fun X =>
                @decide (∀ j : Fin p, (fun i => eA.symm (X i j)) ∈ A.rel)
                  (Classical.propDecidable _)).map fun X i =>
                let raw := u * nW + (eW (padTuple d₀ (X i))).1
                (collapseRep (pmcEqs d₀ Φ)
                  ((Φ.leftArities.length + Φ.rightArities.length) * nW)).getD raw raw
            else [])
      (encMinorCondition m) (encList (encFinFn r encUnary)) := by
    refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
    refine ComputableInPolyTime.flatMapConst (List.range (m + 1)) fun p _ => ?_
    have hcond : ComputableInPolyTime (fun x : MinorCondition m × (ℕ × ℕ) => decide (x.2.1 = p))
        (encPair (encMinorCondition m) (encPair encUnary encUnary)) encBool := by fun_prop
    have hbranch : ComputableInPolyTime
        (fun x : MinorCondition m × (ℕ × ℕ) =>
          ((Finset.univ : Finset (Fin r → Fin p → Fin nA)).toList.filter fun X =>
            @decide (∀ j : Fin p, (fun i => eA.symm (X i j)) ∈ A.rel)
              (Classical.propDecidable _)).map fun X i =>
            let raw := x.2.2 * nW + (eW (padTuple d₀ (X i))).1
            (collapseRep (pmcEqs d₀ x.1)
              ((x.1.leftArities.length + x.1.rightArities.length) * nW)).getD raw raw)
        (encPair (encMinorCondition m) (encPair encUnary encUnary))
        (encList (encFinFn r encUnary)) := by
      refine ComputableInPolyTime.mapConst _ fun X _ => ?_
      refine ComputableInPolyTime.finFn fun i => ?_
      have hrep' := hrep.comp
        (ComputableInPolyTime.fst (encMinorCondition m) (encPair encUnary encUnary))
      have hraw : ComputableInPolyTime
          (fun x : MinorCondition m × (ℕ × ℕ) => x.2.2 * nW + (eW (padTuple d₀ (X i))).1)
          (encPair (encMinorCondition m) (encPair encUnary encUnary)) encUnary := by fun_prop
      exact (ComputableInPolyTime.optionGetDWithInput
        (ComputableInPolyTime.getElem? hrep' hraw) hraw).of_enc_eq fun _ => by
          simp only [List.getD_eq_getElem?_getD, Function.comp_apply]
    exact (hcond.ite hbranch (.const [])).of_enc_eq fun x => by simp
  have hright : ComputableInPolyTime
      (fun Φ : MinorCondition m =>
        Φ.rightArities.zipIdx.flatMap fun (qv, v) =>
          (List.range (m + 1)).flatMap fun q =>
            if qv = q then
              ((Finset.univ : Finset (Fin r → Fin q → Fin nA)).toList.filter fun Y =>
                @decide (∀ j : Fin q, (fun i => eA.symm (Y i j)) ∈ A.rel)
                  (Classical.propDecidable _)).map fun Y i =>
                let raw := (Φ.leftArities.length + v) * nW + (eW (padTuple d₀ (Y i))).1
                (collapseRep (pmcEqs d₀ Φ)
                  ((Φ.leftArities.length + Φ.rightArities.length) * nW)).getD raw raw
            else [])
      (encMinorCondition m) (encList (encFinFn r encUnary)) := by
    refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
    refine ComputableInPolyTime.flatMapConst (List.range (m + 1)) fun q _ => ?_
    have hcond : ComputableInPolyTime (fun x : MinorCondition m × (ℕ × ℕ) => decide (x.2.1 = q))
        (encPair (encMinorCondition m) (encPair encUnary encUnary)) encBool := by fun_prop
    have hbranch : ComputableInPolyTime
        (fun x : MinorCondition m × (ℕ × ℕ) =>
          ((Finset.univ : Finset (Fin r → Fin q → Fin nA)).toList.filter fun Y =>
            @decide (∀ j : Fin q, (fun i => eA.symm (Y i j)) ∈ A.rel)
              (Classical.propDecidable _)).map fun Y i =>
            let raw := (x.1.leftArities.length + x.2.2) * nW + (eW (padTuple d₀ (Y i))).1
            (collapseRep (pmcEqs d₀ x.1)
              ((x.1.leftArities.length + x.1.rightArities.length) * nW)).getD raw raw)
        (encPair (encMinorCondition m) (encPair encUnary encUnary))
        (encList (encFinFn r encUnary)) := by
      refine ComputableInPolyTime.mapConst _ fun Y _ => ?_
      refine ComputableInPolyTime.finFn fun i => ?_
      have hrep' := hrep.comp
        (ComputableInPolyTime.fst (encMinorCondition m) (encPair encUnary encUnary))
      have hraw : ComputableInPolyTime
          (fun x : MinorCondition m × (ℕ × ℕ) =>
            (x.1.leftArities.length + x.2.2) * nW + (eW (padTuple d₀ (Y i))).1)
          (encPair (encMinorCondition m) (encPair encUnary encUnary)) encUnary := by fun_prop
      exact (ComputableInPolyTime.optionGetDWithInput
        (ComputableInPolyTime.getElem? hrep' hraw) hraw).of_enc_eq fun _ => by
          simp only [List.getD_eq_getElem?_getD, Function.comp_apply]
    exact (hcond.ite hbranch (.const [])).of_enc_eq fun x => by simp
  exact encFinStructure_mk_polyTime hT
    ((ComputableInPolyTime.listAppend (encFinFn r encUnary)).comp (hleft.prod hright))

/-- **Reduction from `PMC_{Pol(A, B)}(m)` to `PCSP(A, B)`**
: for any finite nonempty template `A`, any template `B` with `A → B`, and any `m : ℕ`,
`PMC_{Pol(A, B)}(m)` reduces in deterministic polynomial time to `PCSP(A, B)`.
-/
theorem polyTimeReducible_pmc_pcsp {r : ℕ} (m : ℕ)
    {A : Template.{u} r} {B : Template.{v} r}
    [Finite A.Domain] [Nonempty A.Domain] (hAB : A.HasHom B) :
    PromiseProblem.PolyTimeReducible (encMinorCondition m) (encFinStructure r)
      (pmc (polMinion A B) ⟨hAB.some.projPoly (p := 1) 0⟩) (pcsp A B hAB) := by
  classical
  have : Fintype A.Domain := Fintype.ofFinite _
  let nA := Fintype.card A.Domain
  let eA : A.Domain ≃ Fin nA := Fintype.equivFin A.Domain
  let d₀ : Fin nA := eA (Classical.arbitrary A.Domain)
  let eW : (Fin m → Fin nA) ≃ Fin (nA ^ m) := Fintype.equivFinOfCardEq (by simp)
  let nW := nA ^ m
  have hnW_pos : 0 < nW := Nat.pow_pos (Fintype.card_pos)
  refine ⟨pmcToPcsp A eA d₀, computableInPolyTime_pmcToPcsp A eA d₀, ?_, ?_⟩
  · -- Completeness: `TriviallySat Φ` implies `pmcToPcsp Φ → A`.
    rintro Φ ⟨hWF, ℓ, r_asgn, hℓ, hr, hsat⟩
    rw [mem_yes_pcsp]
    let L := Φ.leftArities.length
    let R := Φ.rightArities.length
    let T := (L + R) * nW
    let g : ℕ → A.Domain := fun raw =>
      let idx := raw / nW
      let w : Fin m → Fin nA := eW.symm ⟨raw % nW, Nat.mod_lt raw hnW_pos⟩
      if hL : idx < L then
        let pos := ℓ idx
        if hpos : pos < m then eA.symm (w ⟨pos, hpos⟩) else eA.symm d₀
      else
        let pos := r_asgn (idx - L)
        if hpos : pos < m then eA.symm (w ⟨pos, hpos⟩) else eA.symm d₀
    have hg_left : ∀ u (hu : u < L) (p : ℕ) (hp : Φ.leftArities.getD u 0 = p)
        (x : Fin p → Fin nA),
        p ≤ m →
        g (u * nW + (eW (padTuple d₀ x)).1) =
          eA.symm (x ⟨ℓ u, by have := hℓ u hu; omega⟩) := by
      intro u hu p hp x hpm
      have hdiv : (u * nW + (eW (padTuple d₀ x)).1) / nW = u := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnW_pos,
          Nat.div_eq_of_lt (eW (padTuple d₀ x)).2, Nat.zero_add]
      have hmod : (u * nW + (eW (padTuple d₀ x)).1) % nW = (eW (padTuple d₀ x)).1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (eW (padTuple d₀ x)).2]
      have hℓlt : ℓ u < p := by have := hℓ u hu; omega
      have hℓm : ℓ u < m := lt_of_lt_of_le hℓlt hpm
      dsimp only [g]
      rw [hdiv]
      simp only [hu, ↓reduceDIte, hmod, Fin.eta, Equiv.symm_apply_apply, hℓm, padTuple, hℓlt]
    have hg_right : ∀ v (hv : v < R) (q : ℕ) (hq : Φ.rightArities.getD v 0 = q)
        (y : Fin q → Fin nA),
        q ≤ m →
        g ((L + v) * nW + (eW (padTuple d₀ y)).1) =
          eA.symm (y ⟨r_asgn v, by have := hr v hv; omega⟩) := by
      intro v hv q hq y hqm
      have hdiv : ((L + v) * nW + (eW (padTuple d₀ y)).1) / nW = L + v := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnW_pos,
          Nat.div_eq_of_lt (eW (padTuple d₀ y)).2, Nat.zero_add]
      have hmod : ((L + v) * nW + (eW (padTuple d₀ y)).1) % nW = (eW (padTuple d₀ y)).1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (eW (padTuple d₀ y)).2]
      have hrlt : r_asgn v < q := by have := hr v hv; omega
      have hrm : r_asgn v < m := lt_of_lt_of_le hrlt hqm
      have hnotL : ¬ (L + v < L) := by omega
      have hsub : L + v - L = v := by omega
      dsimp only [g]
      rw [hdiv]
      simp only [hnotL, ↓reduceDIte, hsub, hmod, Fin.eta, Equiv.symm_apply_apply, hrm, padTuple,
        hrlt]
    have hg_eq : ∀ pair ∈ pmcEqs d₀ Φ, g pair.1 = g pair.2 := by
      intro pair hpair
      dsimp only [pmcEqs] at hpair
      rw [List.mem_flatMap] at hpair
      obtain ⟨c, hc, h1⟩ := hpair
      rw [List.mem_flatMap] at h1
      obtain ⟨p, hp, h2⟩ := h1
      rw [List.mem_flatMap] at h2
      obtain ⟨q, hq, h3⟩ := h2
      split_ifs at h3 with hcond
      · obtain ⟨hpu, hqv, hcL, hcR⟩ := hcond
        rw [List.mem_map] at h3
        obtain ⟨y, _, rfl⟩ := h3
        have hpm : p ≤ m := by have := List.mem_range.mp hp; omega
        have hqm : q ≤ m := by have := List.mem_range.mp hq; omega
        rw [hg_left c.leftIdx hcL p hpu _ hpm, hg_right c.rightIdx hcR q hqv y hqm]
        have hidx : c.map.getD (ℓ c.leftIdx) 0 = r_asgn c.rightIdx := hsat c hc
        have hrc : r_asgn c.rightIdx < q := by have := hr c.rightIdx hcR; omega
        simp only [hidx, hrc, ↓reduceDIte]
      · exact nomatch h3
    refine ⟨Template.Hom.mk g fun (s : Fin r → ℕ) hs => ?_⟩
    change s ∈ (pmcToPcsp A eA d₀ Φ).tuples at hs
    dsimp only [pmcToPcsp] at hs
    rcases List.mem_append.mp hs with hsL | hsR
    · rw [List.mem_flatMap] at hsL
      obtain ⟨⟨pu, u⟩, hu_zip, h1⟩ := hsL
      rw [List.mem_flatMap] at h1
      obtain ⟨p, hp, h2⟩ := h1
      split_ifs at h2 with hpu
      · rw [List.mem_map] at h2
        obtain ⟨X, hX, rfl⟩ := h2
        have hX_rel := @of_decide_eq_true _ (Classical.propDecidable _) (List.mem_filter.mp hX).2
        have hget := List.mem_zipIdx_iff_getElem?.mp hu_zip
        have hu_lt : u < L := by
          by_contra hlt
          have hnone : Φ.leftArities[u]? = none := List.getElem?_eq_none (by omega)
          simp [hnone] at hget
        have hpu_get : Φ.leftArities.getD u 0 = p := by
          rw [List.getD_eq_getElem _ _ hu_lt]
          rw [List.getElem?_eq_getElem hu_lt] at hget
          exact (Option.some.inj hget).trans hpu
        have hpm : p ≤ m := by have := List.mem_range.mp hp; omega
        convert hX_rel ⟨ℓ u, by have := hℓ u hu_lt; omega⟩ using 1
        funext i
        change g ((collapseRep (pmcEqs d₀ Φ) T).getD (u * nW + (eW (padTuple d₀ (X i))).1)
            (u * nW + (eW (padTuple d₀ (X i))).1)) =
          eA.symm (X i ⟨ℓ u, by have := hℓ u hu_lt; omega⟩)
        rw [collapseRep_preserves _ T g hg_eq, hg_left u hu_lt p hpu_get (X i) hpm]
      · exact nomatch h2
    · rw [List.mem_flatMap] at hsR
      obtain ⟨⟨qv, v⟩, hv_zip, h1⟩ := hsR
      rw [List.mem_flatMap] at h1
      obtain ⟨q, hq, h2⟩ := h1
      split_ifs at h2 with hqv
      · rw [List.mem_map] at h2
        obtain ⟨Y, hY, rfl⟩ := h2
        have hY_rel := @of_decide_eq_true _ (Classical.propDecidable _) (List.mem_filter.mp hY).2
        have hget := List.mem_zipIdx_iff_getElem?.mp hv_zip
        have hv_lt : v < R := by
          by_contra hlt
          have hnone : Φ.rightArities[v]? = none := List.getElem?_eq_none (by omega)
          simp [hnone] at hget
        have hqv_get : Φ.rightArities.getD v 0 = q := by
          rw [List.getD_eq_getElem _ _ hv_lt]
          rw [List.getElem?_eq_getElem hv_lt] at hget
          exact (Option.some.inj hget).trans hqv
        have hqm : q ≤ m := by have := List.mem_range.mp hq; omega
        convert hY_rel ⟨r_asgn v, by have := hr v hv_lt; omega⟩ using 1
        funext i
        change g ((collapseRep (pmcEqs d₀ Φ) T).getD ((L + v) * nW + (eW (padTuple d₀ (Y i))).1)
            ((L + v) * nW + (eW (padTuple d₀ (Y i))).1)) =
          eA.symm (Y i ⟨r_asgn v, by have := hr v hv_lt; omega⟩)
        rw [collapseRep_preserves _ T g hg_eq, hg_right v hv_lt q hqv_get (Y i) hqm]
      · exact nomatch h2
  · -- Soundness: `pmcToPcsp Φ → B` implies `SatIn (polMinion A B) Φ`.
    rintro Φ ⟨hWF, hno⟩
    rw [mem_no_pcsp]
    rintro ⟨hG⟩
    apply hno
    let L := Φ.leftArities.length
    let R := Φ.rightArities.length
    let T := (L + R) * nW
    let rep := collapseRep (pmcEqs d₀ Φ) T
    have heq_lt : ∀ pair ∈ pmcEqs d₀ Φ, pair.1 < T ∧ pair.2 < T := by
      intro pair hpair
      dsimp only [pmcEqs] at hpair
      rw [List.mem_flatMap] at hpair
      obtain ⟨c, _, h1⟩ := hpair
      rw [List.mem_flatMap] at h1
      obtain ⟨p, _, h2⟩ := h1
      rw [List.mem_flatMap] at h2
      obtain ⟨q, _, h3⟩ := h2
      split_ifs at h3 with hcond
      · obtain ⟨_, _, hcL, hcR⟩ := hcond
        rw [List.mem_map] at h3
        obtain ⟨y, _, rfl⟩ := h3
        constructor
        · have h1' : ∀ w : Fin nW, c.leftIdx * nW + w.1 < (c.leftIdx + 1) * nW := fun w => by
            rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left w.2 _
          exact lt_of_lt_of_le (h1' _) (Nat.mul_le_mul_right nW (by omega))
        · have h2' : ∀ w : Fin nW, (L + c.rightIdx) * nW + w.1 < (L + c.rightIdx + 1) * nW :=
            fun w => by
              rw [Nat.add_mul (L + c.rightIdx) 1 nW, Nat.one_mul]
              exact Nat.add_lt_add_left w.2 _
          exact lt_of_lt_of_le (h2' _) (Nat.mul_le_mul_right nW (by omega))
      · exact nomatch h3
    let fL : ∀ u : Fin L, (polMinion A B).carrier (Φ.leftArities[u]) := fun u =>
      Template.Hom.mk
        (fun (x : Fin (Φ.leftArities[u]) → A.Domain) =>
          let raw := u.1 * nW + (eW (padTuple d₀ (eA ∘ x))).1
          hG (rep.getD raw raw))
        (fun (X : Fin r → Fin (Φ.leftArities[u]) → A.Domain) hX => by
          let X' : Fin r → Fin (Φ.leftArities[u]) → Fin nA := fun i j => eA (X i j)
          have hmem : (fun i => rep.getD (u.1 * nW + (eW (padTuple d₀ (X' i))).1)
              (u.1 * nW + (eW (padTuple d₀ (X' i))).1)) ∈ (pmcToPcsp A eA d₀ Φ).tuples := by
            refine List.mem_append_left _ ?_
            rw [List.mem_flatMap]
            refine ⟨(Φ.leftArities[u], u.1), ?_, ?_⟩
            · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem u.2]; rfl
            · rw [List.mem_flatMap]
              have hpm : Φ.leftArities[u] ≤ m := hWF.1 _ (List.getElem_mem u.2)
              refine ⟨Φ.leftArities[u], List.mem_range.mpr (by omega), ?_⟩
              simp only [↓reduceIte, List.mem_map]
              refine ⟨X', List.mem_filter.mpr ⟨Finset.mem_toList.mpr (Finset.mem_univ _),
                @decide_eq_true _ (Classical.propDecidable _) fun j => by
                  simpa [X'] using hX j⟩, rfl⟩
          exact hG.map_rel' hmem)
    let gR : ∀ v : Fin R, (polMinion A B).carrier (Φ.rightArities[v]) := fun v =>
      Template.Hom.mk
        (fun (y : Fin (Φ.rightArities[v]) → A.Domain) =>
          let raw := (L + v.1) * nW + (eW (padTuple d₀ (eA ∘ y))).1
          hG (rep.getD raw raw))
        (fun (Y : Fin r → Fin (Φ.rightArities[v]) → A.Domain) hY => by
          let Y' : Fin r → Fin (Φ.rightArities[v]) → Fin nA := fun i j => eA (Y i j)
          have hmem : (fun i => rep.getD ((L + v.1) * nW + (eW (padTuple d₀ (Y' i))).1)
              ((L + v.1) * nW + (eW (padTuple d₀ (Y' i))).1)) ∈ (pmcToPcsp A eA d₀ Φ).tuples := by
            refine List.mem_append_right _ ?_
            rw [List.mem_flatMap]
            refine ⟨(Φ.rightArities[v], v.1), ?_, ?_⟩
            · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem v.2]; rfl
            · rw [List.mem_flatMap]
              have hqm : Φ.rightArities[v] ≤ m := hWF.2.1 _ (List.getElem_mem v.2)
              refine ⟨Φ.rightArities[v], List.mem_range.mpr (by omega), ?_⟩
              simp only [↓reduceIte, List.mem_map]
              refine ⟨Y', List.mem_filter.mpr ⟨Finset.mem_toList.mpr (Finset.mem_univ _),
                @decide_eq_true _ (Classical.propDecidable _) fun j => by
                  simpa [Y'] using hY j⟩, rfl⟩
          exact hG.map_rel' hmem)
    refine ⟨hWF, fL, gR, fun c hc hu hv hmap => ?_⟩
    apply Template.Hom.ext
    funext y
    have hpu_m : Φ.leftArities[c.leftIdx]'hu ≤ m := hWF.1 _ (List.getElem_mem hu)
    have hqv_m : Φ.rightArities[c.rightIdx]'hv ≤ m := hWF.2.1 _ (List.getElem_mem hv)
    have hpair_mem :
        (c.leftIdx * nW + (eW (padTuple d₀ (eA ∘ (y ∘ fun i => ⟨c.map.getD i.1 0, hmap i⟩)))).1,
         (L + c.rightIdx) * nW + (eW (padTuple d₀ (eA ∘ y))).1) ∈ pmcEqs d₀ Φ := by
      dsimp only [pmcEqs]
      rw [List.mem_flatMap]
      refine ⟨c, hc, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨Φ.leftArities[c.leftIdx]'hu, List.mem_range.mpr (by omega), ?_⟩
      rw [List.mem_flatMap]
      refine ⟨Φ.rightArities[c.rightIdx]'hv, List.mem_range.mpr (by omega), ?_⟩
      have hcond : Φ.leftArities.getD c.leftIdx 0 = Φ.leftArities[c.leftIdx]'hu ∧
          Φ.rightArities.getD c.rightIdx 0 = Φ.rightArities[c.rightIdx]'hv ∧
          c.leftIdx < Φ.leftArities.length ∧ c.rightIdx < Φ.rightArities.length :=
        ⟨List.getD_eq_getElem _ _ hu, List.getD_eq_getElem _ _ hv, hu, hv⟩
      simp only [hcond, and_true, ↓reduceIte, List.mem_map]
      refine ⟨eA ∘ y, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
      congr 2
      · congr 1; congr 1; congr 1; funext i
        simp only [Function.comp_apply, hmap i, ↓reduceDIte]
        rfl
    exact congrArg (fun (u : ℕ) => hG u) (collapseRep_eq_of_mem heq_lt hpair_mem)

end Cslib.Complexity.PCSP
