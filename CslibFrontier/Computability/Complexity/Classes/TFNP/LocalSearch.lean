/-
Copyright (c) 2026 The Cslib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space
public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses
public import CslibFrontier.Computability.Complexity.Reduction.Turing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Local Search Problems, Transition Graphs, `PLS` Certificates, and Tight Reductions

This module develops the Johnson--Papadimitriou--Yannakakis theory of polynomial local
search (`PLS`) and the Schäffer--Yannakakis theory of tight `PLS`-reductions, bridged
directly to `Cslib.Complexity.PLS`, `Cslib.Complexity.SearchReducible`,
`Cslib.Complexity.SearchComplete`, and `Cslib.Complexity.PSPACE` under standard Lean axioms.

## Main definitions

- `CslibFrontier.Complexity.OptimizationSense`: maximization vs. minimization direction, with
  strict cost improvement `OptimizationSense.improves`.
- `CslibFrontier.Complexity.LocalSearchProblem`: local search problem `(enc, solWidth, isFeasible,
  cost, isNeighbor, sense)` with transition-graph edges `TransitionEdge`, local optimality
  search relation `IsLocallyOptimal` (`searchRel`), directed walks `TransitionPath`,
  reachable local optima `ReachableOptimum`, and shortest-path-to-sink `height`.
- `CslibFrontier.Complexity.PLSCertificate`: polynomial-time algorithms `(initSol, improve)`
  witnessing membership in `PLS`, together with the standard local search algorithm
  `standardOptimum` and its `PSPACE` decision languages `standardAlgExactLang` and
  `standardAlgQueryLang`.
- `CslibFrontier.Complexity.PLSReduction`, `CslibFrontier.Complexity.TightPLSReduction`:
  polynomial-time `PLS`-reductions and Schäffer--Yannakakis tight `PLS`-reductions.

## Main results

- `CslibFrontier.Complexity.PLSCertificate.searchRel_mem_PLS`: every local search problem with a
  `PLSCertificate` defines a search relation in `Cslib.Complexity.PLS`.
- `CslibFrontier.Complexity.PLSCertificate.computableInPolySpace_standardOptimum`,
  `CslibFrontier.Complexity.PLSCertificate.standardAlgExactLang_mem_PSPACE`,
  `CslibFrontier.Complexity.PLSCertificate.standardAlgQueryLang_mem_PSPACE`: computing the local
  optimum reached by a standard local search algorithm runs in polynomial space.
- `CslibFrontier.Complexity.PLSReduction.searchReducible`,
  `CslibFrontier.Complexity.PLSReduction.plsHard`,
  `CslibFrontier.Complexity.PLSReduction.plsComplete`: `PLS`-reductions induce
  `Cslib.Complexity.SearchReducible` and transfer `PLS`-hardness and `PLS`-completeness.
- `CslibFrontier.Complexity.TightPLSReduction.trans`: tight `PLS`-reductions compose transitively.
- `CslibFrontier.Complexity.TightPLSReduction.height_le`: tight `PLS`-reductions preserve transition
  graph height lower bounds (`P.height x s ≤ Q.height (f x) (lift (x, s))`) and transfer
  exponential-height polynomial-time instance families.
- `CslibFrontier.Complexity.TightPLSReduction.reachableOptimum_map`,
  `CslibFrontier.Complexity.TightPLSReduction.pspaceHard_standardAlgQuery`: tight `PLS`-reductions
  preserve reachable local optima and transfer `PSPACE`-hardness of the standard local search
  algorithm problem irrespective of the improving-neighbor selection rule.

## Tags

polynomial local search, PLS, tight PLS-reduction, transition graph, PSPACE, standard algorithm
-/

public section

namespace CslibFrontier.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity

/-- Optimization direction of a local search problem: maximization or minimization. -/
inductive OptimizationSense : Type
  | maximize
  | minimize
  deriving DecidableEq, Repr

/-- Whether cost `c'` strictly improves over cost `c` under `sense`. -/
@[expose]
def OptimizationSense.improves (sense : OptimizationSense) (c c' : ℤ) : Prop :=
  match sense with
  | .maximize => c < c'
  | .minimize => c' < c

@[simp]
theorem OptimizationSense.improves_maximize (c c' : ℤ) :
    OptimizationSense.maximize.improves c c' ↔ c < c' :=
  Iff.rfl

@[simp]
theorem OptimizationSense.improves_minimize (c c' : ℤ) :
    OptimizationSense.minimize.improves c c' ↔ c' < c :=
  Iff.rfl

instance instDecidableImproves (sense : OptimizationSense) (c c' : ℤ) :
    Decidable (sense.improves c c') := by
  unfold OptimizationSense.improves
  cases sense <;> infer_instance

theorem OptimizationSense.improves_irrefl (sense : OptimizationSense) (c : ℤ) :
    ¬ sense.improves c c := by
  cases sense <;> simp [OptimizationSense.improves]

theorem OptimizationSense.improves_trans (sense : OptimizationSense) {c₁ c₂ c₃ : ℤ}
    (h₁₂ : sense.improves c₁ c₂) (h₂₃ : sense.improves c₂ c₃) : sense.improves c₁ c₃ := by
  cases sense <;> simp only [OptimizationSense.improves] at h₁₂ h₂₃ ⊢ <;> omega

/-- A local search problem in the sense of Johnson, Papadimitriou, and Yannakakis, with
instances of type `α` encoded by `enc`, feasible solutions represented as fixed-width Boolean
strings of length `solWidth x`, integer cost function `cost`, neighborhood relation `isNeighbor`,
and optimization direction `sense`.
-/
@[ext]
structure LocalSearchProblem (α : Type*) where
  /-- Binary encoding of problem instances. -/
  enc : α ↪ List Bool
  /-- Bit-length of candidate solution strings for a given instance. -/
  solWidth : α → ℕ
  /-- Boolean feasibility predicate on `(instance, candidate_solution)`. -/
  isFeasible : α × List Bool → Bool
  /-- Integer objective value `c(x, s) ∈ ℤ`. -/
  cost : α × List Bool → ℤ
  /-- Neighborhood relation `(s, s') ∈ neighborSet x` between solutions. -/
  neighborSet : α → Set (List Bool × List Bool)
  /-- Optimization direction (`maximize` or `minimize`). -/
  sense : OptimizationSense

namespace LocalSearchProblem

variable {α : Type*} (P : LocalSearchProblem α)

/-- Neighborhood predicate `s' ∈ N(x, s)` extracted from `P.neighborSet`. -/
abbrev isNeighbor (x : α) (s s' : List Bool) : Prop :=
  (s, s') ∈ P.neighborSet x

/-- Solution `s` is feasible for instance `x`: it has bit-length `P.solWidth x` and satisfies
`P.isFeasible (x, s) = true`. -/
@[expose]
def Feasible (x : α) (s : List Bool) : Prop :=
  s.length = P.solWidth x ∧ P.isFeasible (x, s) = true

/-- Logical characterization of `P.Feasible x s`. -/
theorem feasible_iff (x : α) (s : List Bool) :
    P.Feasible x s ↔ s.length = P.solWidth x ∧ P.isFeasible (x, s) = true :=
  Iff.rfl

instance instDecidableFeasible (x : α) (s : List Bool) : Decidable (P.Feasible x s) := by
  unfold Feasible; infer_instance

/-- Directed edge `s → s'` in the transition graph `T(x)`: `s` and `s'` are feasible, `s'` lies
in the neighborhood of `s`, and `s'` strictly improves the objective over `s`. -/
@[expose]
def TransitionEdge (x : α) (s s' : List Bool) : Prop :=
  P.Feasible x s ∧ P.Feasible x s' ∧ P.isNeighbor x s s' ∧
    P.sense.improves (P.cost (x, s)) (P.cost (x, s'))

/-- Logical characterization of `P.TransitionEdge x s s'`. -/
theorem transitionEdge_iff (x : α) (s s' : List Bool) :
    P.TransitionEdge x s s' ↔
      P.Feasible x s ∧ P.Feasible x s' ∧ P.isNeighbor x s s' ∧
        P.sense.improves (P.cost (x, s)) (P.cost (x, s')) :=
  Iff.rfl

theorem TransitionEdge.feasible_left {P : LocalSearchProblem α} {x : α} {s s' : List Bool}
    (h : P.TransitionEdge x s s') : P.Feasible x s := h.1

theorem TransitionEdge.feasible_right {P : LocalSearchProblem α} {x : α} {s s' : List Bool}
    (h : P.TransitionEdge x s s') : P.Feasible x s' := h.2.1

theorem TransitionEdge.improves {P : LocalSearchProblem α} {x : α} {s s' : List Bool}
    (h : P.TransitionEdge x s s') : P.sense.improves (P.cost (x, s)) (P.cost (x, s')) :=
  h.2.2.2

/-- Local optimality of `s` for instance `x`: `s` is feasible and has no outgoing edge in the
transition graph `T(x)` (equivalently, `s` is a sink of `T(x)`). -/
@[expose]
def IsLocallyOptimal (x : α) (s : List Bool) : Prop :=
  P.Feasible x s ∧ ∀ s', ¬ P.TransitionEdge x s s'

/-- Logical characterization of `P.IsLocallyOptimal x s`. -/
theorem isLocallyOptimal_iff (x : α) (s : List Bool) :
    P.IsLocallyOptimal x s ↔ P.Feasible x s ∧ ∀ s', ¬ P.TransitionEdge x s s' :=
  Iff.rfl

/-- The `FNP` / `PLS` search relation associated with `P`: given instance `x`, find a locally
optimal feasible solution `s`. -/
abbrev searchRel : α → List Bool → Prop := P.IsLocallyOptimal

/-- Inductive non-empty directed walk in the transition graph `T(x)` from `s` to `s'`, recording
the list `mid` of internal vertices strictly between `s` and `s'` (`mid.length + 1` edges). -/
inductive TransitionPath (x : α) : List Bool → List Bool → List (List Bool) → Prop
  | single {s s' : List Bool} (he : P.TransitionEdge x s s') : TransitionPath x s s' []
  | cons {s u s' : List Bool} {mid : List (List Bool)}
      (he : P.TransitionEdge x s u) (hp : TransitionPath x u s' mid) :
      TransitionPath x s s' (u :: mid)

theorem TransitionPath.snoc {P : LocalSearchProblem α} {x : α} {s u s' : List Bool}
    {mid : List (List Bool)} (hp : P.TransitionPath x s u mid) (he : P.TransitionEdge x u s') :
    P.TransitionPath x s s' (mid ++ [u]) := by
  induction hp with
  | single he₀ => exact .cons he₀ (.single he)
  | cons he₀ _ ih => exact .cons he₀ (ih he)

/-- Directed walk in `T(x)` with explicit edge count `k : ℕ`. -/
inductive TransitionSteps (x : α) : ℕ → List Bool → List Bool → Prop
  | zero {s : List Bool} (hs : P.Feasible x s) : TransitionSteps x 0 s s
  | succ {k : ℕ} {s u s' : List Bool} (he : P.TransitionEdge x s u)
      (hp : TransitionSteps x k u s') : TransitionSteps x (k + 1) s s'

theorem TransitionPath.toTransitionSteps {P : LocalSearchProblem α} {x : α} {s s' : List Bool}
    {mid : List (List Bool)} (hp : P.TransitionPath x s s' mid) :
    P.TransitionSteps x (mid.length + 1) s s' := by
  induction hp with
  | single he => exact .succ he (.zero he.feasible_right)
  | cons he _ ih =>
    simp only [List.length_cons]
    exact .succ he ih

theorem TransitionSteps.feasible_left {P : LocalSearchProblem α} {x : α} {k : ℕ}
    {s s' : List Bool} (h : P.TransitionSteps x k s s') : P.Feasible x s := by
  cases h with
  | zero hs => exact hs
  | succ he _ => exact he.feasible_left

theorem TransitionSteps.feasible_right {P : LocalSearchProblem α} {x : α} {k : ℕ}
    {s s' : List Bool} (h : P.TransitionSteps x k s s') : P.Feasible x s' := by
  induction h with
  | zero hs => exact hs
  | succ _ _ ih => exact ih

theorem TransitionSteps.trans {P : LocalSearchProblem α} {x : α} {k₁ k₂ : ℕ}
    {s₁ s₂ s₃ : List Bool} (h₁ : P.TransitionSteps x k₁ s₁ s₂)
    (h₂ : P.TransitionSteps x k₂ s₂ s₃) : P.TransitionSteps x (k₁ + k₂) s₁ s₃ := by
  induction h₁ with
  | zero _ => simpa using h₂
  | succ he _ ih =>
    rw [Nat.succ_add]
    exact .succ he (ih h₂)

theorem TransitionSteps.improves_of_pos {P : LocalSearchProblem α} {x : α} {k : ℕ}
    {s s' : List Bool} (h : P.TransitionSteps x (k + 1) s s') :
    P.sense.improves (P.cost (x, s)) (P.cost (x, s')) := by
  induction k generalizing s with
  | zero =>
    cases h with
    | succ he hp =>
      cases hp with
      | zero _ => exact he.improves
  | succ k ih =>
    cases h with
    | succ he hp =>
      exact P.sense.improves_trans he.improves (ih hp)

theorem TransitionSteps.ne_of_pos {P : LocalSearchProblem α} {x : α} {k : ℕ}
    {s s' : List Bool} (h : P.TransitionSteps x (k + 1) s s') : s ≠ s' := by
  intro heq
  subst heq
  exact P.sense.improves_irrefl _ (h.improves_of_pos)

/-- Every feasible solution `s` reaches at least one locally optimal sink `s*` in `T(x)` in at
most `2 ^ (P.solWidth x)` steps. -/
theorem exists_transitionSteps_isLocallyOptimal (x : α) {s : List Bool} (hs : P.Feasible x s) :
    ∃ k s', k ≤ 2 ^ P.solWidth x ∧ P.TransitionSteps x k s s' ∧ P.IsLocallyOptimal x s' := by
  classical
  let FinSol := { u : List Bool // P.Feasible x u }
  have hfin : Finite { u : List Bool // u.length = P.solWidth x } := by
    let e : { u : List Bool // u.length = P.solWidth x } ≃ (Fin (P.solWidth x) → Bool) :=
      { toFun := fun u i ↦ u.1[i.val]'(i.isLt.trans_eq u.2.symm)
        invFun := fun f ↦ ⟨List.ofFn f, List.length_ofFn⟩
        left_inv := fun u ↦ Subtype.ext (List.ext_getElem (by simp [u.2]) fun _ _ _ ↦ by simp)
        right_inv := fun f ↦ funext fun _ ↦ by simp }
    exact Finite.of_equiv _ e.symm
  let _ : Fintype { u : List Bool // u.length = P.solWidth x } := Fintype.ofFinite _
  have hcard_cube : Fintype.card { u : List Bool // u.length = P.solWidth x } =
      2 ^ P.solWidth x := by
    let e : { u : List Bool // u.length = P.solWidth x } ≃ (Fin (P.solWidth x) → Bool) :=
      { toFun := fun u i ↦ u.1[i.val]'(i.isLt.trans_eq u.2.symm)
        invFun := fun f ↦ ⟨List.ofFn f, List.length_ofFn⟩
        left_inv := fun u ↦ Subtype.ext (List.ext_getElem (by simp [u.2]) fun _ _ _ ↦ by simp)
        right_inv := fun f ↦ funext fun _ ↦ by simp }
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  -- Bound the number of feasible solutions with strictly better cost than u.
  let betterSet (u : List Bool) : Finset { w : List Bool // w.length = P.solWidth x } :=
    Finset.univ.filter fun w ↦ P.Feasible x w.1 ∧ P.sense.improves (P.cost (x, u)) (P.cost (x, w.1))
  have hbetter_le (u : List Bool) : (betterSet u).card ≤ 2 ^ P.solWidth x :=
    (Finset.card_filter_le _ _).trans_eq hcard_cube
  suffices ∀ m u, P.Feasible x u → (betterSet u).card ≤ m →
      ∃ k s', k ≤ m ∧ P.TransitionSteps x k u s' ∧ P.IsLocallyOptimal x s' by
    exact this (2 ^ P.solWidth x) s hs (hbetter_le s)
  intro m
  induction m with
  | zero =>
    intro u hu hm
    refine ⟨0, u, le_rfl, .zero hu, hu, fun v he ↦ ?_⟩
    have hmem : ⟨v, he.feasible_right.1⟩ ∈ betterSet u := by
      simp [betterSet, he.feasible_right, he.improves]
    have hpos : 0 < (betterSet u).card := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  | succ m ih =>
    intro u hu hm
    by_cases hopt : P.IsLocallyOptimal x u
    · exact ⟨0, u, Nat.zero_le _, .zero hu, hopt⟩
    · simp only [IsLocallyOptimal, hu, true_and, not_forall, Classical.not_not] at hopt
      obtain ⟨v, he⟩ := hopt
      have hssub : betterSet v ⊂ betterSet u := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨⟨v, he.feasible_right.1⟩,
            by simp [betterSet, he.feasible_right, he.improves],
            by simp [betterSet, P.sense.improves_irrefl]⟩
        · intro w hw
          simp only [betterSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          exact ⟨hw.1, P.sense.improves_trans he.improves hw.2⟩
      have hlt : (betterSet v).card < (betterSet u).card := Finset.card_lt_card hssub
      obtain ⟨k, s', hk, hp, hs'⟩ := ih v he.feasible_right (by omega)
      exact ⟨k + 1, s', by omega, .succ he hp, hs'⟩

/-- Solution `s'` is a locally optimal solution of `x` reachable from `s₀` in `T(x)`. -/
@[expose]
def ReachableOptimum (x : α) (s₀ s' : List Bool) : Prop :=
  ∃ k, P.TransitionSteps x k s₀ s' ∧ P.IsLocallyOptimal x s'

/-- The **height** of a solution `s` in the transition graph `T(x)`: the shortest
directed path length from `s` to a sink (local optimum) of `T(x)` (and `0` if `s` is infeasible).
-/
noncomputable def height (x : α) (s : List Bool) : ℕ :=
  by
    classical
    exact if hs : P.Feasible x s then
      Nat.find (P.exists_transitionSteps_isLocallyOptimal x hs)
    else 0

theorem height_le_of_transitionSteps {P : LocalSearchProblem α} {x : α} {k : ℕ}
    {s s' : List Bool} (hp : P.TransitionSteps x k s s') (hopt : P.IsLocallyOptimal x s') :
    P.height x s ≤ k := by
  classical
  have hs : P.Feasible x s := hp.feasible_left
  unfold height
  rw [dite_eq_left_of_eq_true (eq_true hs)]
  by_cases hk : k ≤ 2 ^ P.solWidth x
  · exact Nat.find_min' _ ⟨s', hk, hp, hopt⟩
  · obtain ⟨_, hfind_le, _, _⟩ := Nat.find_spec (P.exists_transitionSteps_isLocallyOptimal x hs)
    omega

theorem exists_transitionSteps_height {P : LocalSearchProblem α} {x : α} {s : List Bool}
    (hs : P.Feasible x s) :
    ∃ s', P.TransitionSteps x (P.height x s) s s' ∧ P.IsLocallyOptimal x s' := by
  classical
  unfold height
  rw [dite_eq_left_of_eq_true (eq_true hs)]
  obtain ⟨s', _, hp, hopt⟩ := Nat.find_spec (P.exists_transitionSteps_isLocallyOptimal x hs)
  exact ⟨s', hp, hopt⟩

theorem height_eq_zero_of_isLocallyOptimal {P : LocalSearchProblem α} {x : α} {s : List Bool}
    (hopt : P.IsLocallyOptimal x s) : P.height x s = 0 :=
  Nat.eq_zero_of_le_zero (P.height_le_of_transitionSteps (.zero hopt.1) hopt)

theorem not_isLocallyOptimal_of_height_pos {P : LocalSearchProblem α} {x : α} {s : List Bool}
    (hpos : 0 < P.height x s) : ¬ P.IsLocallyOptimal x s := by
  intro hopt
  have := P.height_eq_zero_of_isLocallyOptimal hopt
  omega

end LocalSearchProblem

/-! ### `PLS` Certificates and the Standard Local Search Algorithm -/

/-- A polynomial-time certificate placing
a `LocalSearchProblem` in `PLS` (`Cslib.Complexity.PLS`).
-/
structure PLSCertificate {α : Type} (P : LocalSearchProblem α) where
  /-- Algorithm `A`: computes an initial feasible solution for any instance. -/
  initSol : α → List Bool
  /-- Algorithm `C`: returns `some s'` for an improving neighbor `s'`, or `none` if locally
  optimal. -/
  improve : α × List Bool → Option (List Bool)
  /-- Polynomial-time computability of the solution bit-width `solWidth` in unary. -/
  solWidth_polyTime : ComputableInPolyTime P.solWidth P.enc encUnary
  /-- Polynomial-time computability of the feasibility check `isFeasible`. -/
  isFeasible_polyTime : ComputableInPolyTime P.isFeasible (encPair P.enc encBits) encBool
  /-- Polynomial-time computability of the integer objective `cost` (`encIntBin`). -/
  cost_polyTime : ComputableInPolyTime P.cost (encPair P.enc encBits) encIntBin
  /-- Polynomial-time computability of Algorithm `A` (`initSol`). -/
  initSol_polyTime : ComputableInPolyTime initSol P.enc encBits
  /-- Polynomial-time computability of Algorithm `C` (`improve`). -/
  improve_polyTime : ComputableInPolyTime improve (encPair P.enc encBits) (encOption encBits)
  /-- Algorithm `A` always outputs a feasible solution. -/
  initSol_feasible : ∀ x, P.Feasible x (initSol x)
  /-- When Algorithm `C` outputs `some s'` on a feasible `s`, `s → s'` is an improving edge. -/
  improve_some : ∀ x s s', P.Feasible x s → improve (x, s) = some s' → P.TransitionEdge x s s'
  /-- When Algorithm `C` outputs `none` on a feasible `s`, `s` is locally optimal. -/
  improve_none : ∀ x s, P.Feasible x s → improve (x, s) = none → P.IsLocallyOptimal x s

namespace PLSCertificate

variable {α : Type} {P : LocalSearchProblem α}

/-- Totalized hypercube step induced by `cert`: move to the improving neighbor on feasible
non-optimal inputs, stay put on local optima, and jump to `cert.initSol x` on infeasible strings. -/
@[expose]
def cubeStep (cert : PLSCertificate P) (p : α × List Bool) : List Bool :=
  if P.isFeasible p then (cert.improve p).getD p.2 else cert.initSol p.1

theorem cubeStep_preservesWidth (cert : PLSCertificate P) :
    PreservesWidth P.solWidth cert.cubeStep := by
  intro x u hu
  unfold cubeStep
  by_cases hf : P.isFeasible (x, u) = true
  · simp only [hf, ↓reduceIte]
    cases hi : cert.improve (x, u) with
    | none => exact hu
    | some s' => exact (cert.improve_some x u s' ⟨hu, hf⟩ hi).feasible_right.1
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact (cert.initSol_feasible x).1

theorem cubeStep_polyTime (cert : PLSCertificate P) :
    ComputableInPolyTime cert.cubeStep (encPair P.enc encBits) encBits := by
  unfold cubeStep
  have hget : ComputableInPolyTime
      (fun p : α × List Bool ↦ (cert.improve p).getD p.2) (encPair P.enc encBits) encBits :=
    optionGetDWithInput cert.improve_polyTime (snd P.enc encBits)
  have hinit : ComputableInPolyTime
      (fun p : α × List Bool ↦ cert.initSol p.1) (encPair P.enc encBits) encBits :=
    cert.initSol_polyTime.comp (fst P.enc encBits)
  exact cert.isFeasible_polyTime.ite' hget hinit

/-- **Bridge Theorem**: every `LocalSearchProblem` equipped with a JPY88 `PLSCertificate` belongs
to `Cslib.Complexity.PLS P.enc`. -/
theorem searchRel_mem_PLS (cert : PLSCertificate P) : P.searchRel ∈ PLS P.enc := by
  have habs : ComputableInPolyTime
      (fun p : α × List Bool ↦ (P.cost p).natAbs) (encPair P.enc encBits) encNat :=
    intBin_natAbs.comp cert.cost_polyTime
  obtain ⟨m, hm, hbits⟩ := exists_length_bits_le cert.solWidth_polyTime habs
  let bound (x : α) : ℕ := 2 ^ (m x + 1)
  have hbound_pt : ComputableInPolyTime bound P.enc encNat :=
    binary_two_pow.comp (unary_add' hm (const 1))
  have hcost_lt (x : α) (u : List Bool) (hu : u.length = P.solWidth x) :
      (P.cost (x, u)).natAbs < bound x := by
    have hb := hbits x u hu
    have hsize : (P.cost (x, u)).natAbs.size ≤ m x := by
      simpa only [Nat.size_eq_bits_len] using hb
    have hlt := (Nat.lt_size_self (P.cost (x, u)).natAbs).trans_le
      (Nat.pow_le_pow_right (by omega) hsize)
    have hpow : 2 ^ m x < 2 ^ (m x + 1) :=
      Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)
    exact hlt.trans hpow
  let natCost (p : α × List Bool) : ℕ :=
    if P.isFeasible p then
      match P.sense with
      | .minimize => (P.cost p + (bound p.1 : ℤ)).toNat
      | .maximize => ((bound p.1 : ℤ) - P.cost p).toNat
    else
      2 * bound p.1
  have hnatCost_pt : ComputableInPolyTime natCost (encPair P.enc encBits) encNat := by
    have hb_pair : ComputableInPolyTime (fun p : α × List Bool ↦ bound p.1)
        (encPair P.enc encBits) encNat := hbound_pt.comp (fst P.enc encBits)
    have hb_int : ComputableInPolyTime (fun p : α × List Bool ↦ (bound p.1 : ℤ))
        (encPair P.enc encBits) encIntBin := intBin_natCast.comp hb_pair
    have hmin_br : ComputableInPolyTime
        (fun p : α × List Bool ↦ (P.cost p + (bound p.1 : ℤ)).toNat)
        (encPair P.enc encBits) encNat :=
      intBin_toNat.comp (intBin_add' cert.cost_polyTime hb_int)
    have hmax_br : ComputableInPolyTime
        (fun p : α × List Bool ↦ ((bound p.1 : ℤ) - P.cost p).toNat)
        (encPair P.enc encBits) encNat :=
      intBin_toNat.comp (intBin_sub' hb_int cert.cost_polyTime)
    have hfeas_br : ComputableInPolyTime
        (fun p : α × List Bool ↦ match P.sense with
          | .minimize => (P.cost p + (bound p.1 : ℤ)).toNat
          | .maximize => ((bound p.1 : ℤ) - P.cost p).toNat)
        (encPair P.enc encBits) encNat := by
      cases P.sense
      · exact hmax_br
      · exact hmin_br
    have hinfeas_br : ComputableInPolyTime (fun p : α × List Bool ↦ 2 * bound p.1)
        (encPair P.enc encBits) encNat :=
      binary_mul' (const 2) hb_pair
    exact cert.isFeasible_polyTime.ite' hfeas_br hinfeas_br
  have heq : P.searchRel = localOptRel P.solWidth cert.cubeStep natCost := by
    funext x u
    apply propext
    simp only [LocalSearchProblem.searchRel, LocalSearchProblem.IsLocallyOptimal,
      LocalSearchProblem.Feasible, localOptRel]
    constructor
    · rintro ⟨⟨hu, hf⟩, hno⟩
      refine ⟨hu, ?_⟩
      unfold cubeStep
      simp only [hf, ↓reduceIte]
      cases hi : cert.improve (x, u) with
      | none => exact le_rfl
      | some s' => exact (hno s' (cert.improve_some x u s' ⟨hu, hf⟩ hi)).elim
    · rintro ⟨hu, hle⟩
      by_cases hf : P.isFeasible (x, u) = true
      · refine ⟨⟨hu, hf⟩, ?_⟩
        unfold cubeStep at hle
        simp only [hf, ↓reduceIte] at hle
        cases hi : cert.improve (x, u) with
        | none => exact (cert.improve_none x u ⟨hu, hf⟩ hi).2
        | some s' =>
          exfalso
          simp only [hi, Option.getD_some] at hle
          have he := cert.improve_some x u s' ⟨hu, hf⟩ hi
          have hu_abs := hcost_lt x u hu
          have hs_abs := hcost_lt x s' he.feasible_right.1
          have himp := he.improves
          have hlt_cost : natCost (x, s') < natCost (x, u) := by
            simp only [natCost, hf, he.feasible_right.2, ↓reduceIte]
            cases hsense : P.sense <;>
              simp only [hsense, OptimizationSense.improves] at himp ⊢ <;> omega
          omega
      · exfalso
        unfold cubeStep at hle
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hle
        have hinit := cert.initSol_feasible x
        have hinit_abs := hcost_lt x (cert.initSol x) hinit.1
        have hpos_b : 0 < bound x := Nat.pos_of_ne_zero (by positivity)
        have hlt_init : natCost (x, cert.initSol x) < natCost (x, u) := by
          simp only [natCost, hinit.2, hf, Bool.false_eq_true, ↓reduceIte]
          cases P.sense <;> dsimp only <;> omega
        omega
  rw [heq]
  exact localOptRel_mem_PLS cert.solWidth_polyTime cert.cubeStep_polyTime hnatCost_pt
    cert.cubeStep_preservesWidth

/-- Every problem with a `PLSCertificate` belongs to `Cslib.Complexity.TFNP P.enc`. -/
theorem searchRel_mem_TFNP (cert : PLSCertificate P) : P.searchRel ∈ TFNP P.enc :=
  PLS_subset_TFNP cert.searchRel_mem_PLS

/-- Every problem with a `PLSCertificate` is a total search problem (`IsTotalSearch`). -/
theorem isTotalSearch_searchRel (cert : PLSCertificate P) : IsTotalSearch P.searchRel :=
  cert.searchRel_mem_TFNP.2

/-- One state transition of the standard local search algorithm on `(instance, current_sol)`. -/
@[expose]
def standardStep (cert : PLSCertificate P) (p : α × List Bool) : α × List Bool :=
  (p.1, if P.Feasible p.1 p.2 then (cert.improve p).getD p.2 else cert.initSol p.1)

/-- The unique local optimum `s*(x, s₀)` obtained by iterating `cert.improve` starting from `s₀`
(defaulting to `cert.initSol x` if `s₀` is infeasible) until reaching a local optimum. -/
@[expose]
def standardOptimum (cert : PLSCertificate P) (p : α × List Bool) : List Bool :=
  (cert.standardStep^[2 ^ P.solWidth p.1]
    (p.1, if P.Feasible p.1 p.2 then p.2 else cert.initSol p.1)).2

/-- From any feasible starting solution `s₀`, `cert.standardOptimum (x, s₀)` is a local optimum of
`x` reachable from `s₀` in `T(x)`. -/
theorem reachableOptimum_standardOptimum (cert : PLSCertificate P) {x : α} {s₀ : List Bool}
    (hs₀ : P.Feasible x s₀) :
    P.ReachableOptimum x s₀ (cert.standardOptimum (x, s₀)) := by
  have hiter : ∀ (m : ℕ) (u : List Bool), P.Feasible x u →
      ∃ k ≤ m, P.TransitionSteps x k u (cert.standardStep^[m] (x, u)).2 ∧
        ((cert.standardStep^[m] (x, u)).1 = x) ∧
        (P.IsLocallyOptimal x (cert.standardStep^[m] (x, u)).2 ∨ k = m) := by
    intro m
    induction m with
    | zero =>
      intro u hu
      exact ⟨0, le_rfl, .zero hu, rfl, .inr rfl⟩
    | succ m ih =>
      intro u hu
      have hstep_eq : cert.standardStep (x, u) = (x, (cert.improve (x, u)).getD u) := by
        simp [standardStep, hu]
      rw [Function.iterate_succ_apply, hstep_eq]
      cases hi : cert.improve (x, u) with
      | none =>
        have hopt := cert.improve_none x u hu hi
        have hfix : ∀ r, cert.standardStep^[r] (x, u) = (x, u) := by
          intro r
          induction r with
          | zero => rfl
          | succ r ihr =>
            rw [Function.iterate_succ_apply', ihr]
            simp [standardStep, hu, hi]
        rw [Option.getD_none, hfix m]
        exact ⟨0, Nat.zero_le _, .zero hu, rfl, .inl hopt⟩
      | some v =>
        have he := cert.improve_some x u v hu hi
        simp only [Option.getD_some]
        obtain ⟨k, hkm, hp, hfst, hend⟩ := ih v he.feasible_right
        refine ⟨k + 1, by omega, .succ he hp, hfst, ?_⟩
        rcases hend with hopt | rfl
        · exact .inl hopt
        · exact .inr rfl
  -- Run for 2 ^ solWidth x steps; if k = 2 ^ solWidth x and still not locally optimal, one more
  -- step would exceed the strict-improvement cardinality bound!
  unfold standardOptimum
  simp only [hs₀, ↓reduceIte]
  obtain ⟨k, hkle, hp, _, hend⟩ := hiter (2 ^ P.solWidth x) s₀ hs₀
  rcases hend with hopt | hkeq
  · exact ⟨k, hp, hopt⟩
  · set sEnd := (cert.standardStep^[2 ^ P.solWidth x] (x, s₀)).2
    by_cases hopt : P.IsLocallyOptimal x sEnd
    · exact ⟨k, hp, hopt⟩
    · exfalso
      have hsEnd : P.Feasible x sEnd := hp.feasible_right
      simp only [LocalSearchProblem.IsLocallyOptimal, hsEnd, true_and, not_forall,
        Classical.not_not] at hopt
      obtain ⟨w, he⟩ := hopt
      have hp1 : P.TransitionSteps x (2 ^ P.solWidth x + 1) s₀ w :=
        hkeq ▸ hp.trans (.succ he (.zero he.feasible_right))
      -- Count visited distinct feasible states along hp1: there are 2^n + 2 states in a cube of
      -- 2^n!
      let Cube := { u : List Bool // u.length = P.solWidth x }
      let e : Cube ≃ (Fin (P.solWidth x) → Bool) :=
        { toFun := fun u i ↦ u.1[i.val]'(i.isLt.trans_eq u.2.symm)
          invFun := fun f ↦ ⟨List.ofFn f, List.length_ofFn⟩
          left_inv := fun u ↦ Subtype.ext (List.ext_getElem (by simp [u.2]) fun _ _ _ ↦ by simp)
          right_inv := fun f ↦ funext fun _ ↦ by simp }
      let _ : Fintype Cube := Fintype.ofEquiv _ e.symm
      have hcard : Fintype.card Cube = 2 ^ P.solWidth x := by
        rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      have hchain : ∀ {r : ℕ} {a b : List Bool}, P.TransitionSteps x r a b →
          ∃ S : Finset Cube, S.card = r + 1 ∧
            ∀ z ∈ S, z.1 = a ∨ P.sense.improves (P.cost (x, a)) (P.cost (x, z.1)) := by
        intro r
        induction r with
        | zero =>
          intro a b h0
          cases h0 with
          | zero ha =>
            exact ⟨{⟨a, ha.1⟩}, by simp,
              fun z hz ↦ .inl (congrArg Subtype.val (Finset.mem_singleton.mp hz))⟩
        | succ r ihr =>
          intro a b hsucc
          cases hsucc with
          | succ hea hpb =>
            obtain ⟨S, hScard, hSprop⟩ := ihr hpb
            have hnotMem : (⟨a, hea.feasible_left.1⟩ : Cube) ∉ S := by
              intro hmem
              rcases hSprop _ hmem with heq | himp
              · exact P.sense.improves_irrefl _ (heq ▸ hea.improves)
              · exact P.sense.improves_irrefl _ (P.sense.improves_trans hea.improves himp)
            refine ⟨insert ⟨a, hea.feasible_left.1⟩ S, ?_, ?_⟩
            · rw [Finset.card_insert_of_notMem hnotMem, hScard]
            · intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hzS
              · exact .inl rfl
              · rcases hSprop z hzS with heq | himp
                · exact .inr (heq ▸ hea.improves)
                · exact .inr (P.sense.improves_trans hea.improves himp)
      obtain ⟨S, hScard, _⟩ := hchain hp1
      have hle_univ : S.card ≤ Fintype.card Cube := Finset.card_le_univ S
      omega

private theorem decide_feasible_polyTime (cert : PLSCertificate P) :
    ComputableInPolyTime (fun p : α × List Bool ↦ decide (P.Feasible p.1 p.2))
      (encPair P.enc encBits) encBool := by
  have hlen_eq : ComputableInPolyTime
      (fun p : α × List Bool ↦ decide (p.2.length = P.solWidth p.1))
      (encPair P.enc encBits) encBool :=
    decide_eq' (length_bits.comp (snd P.enc encBits))
      (cert.solWidth_polyTime.comp (fst P.enc encBits))
  refine (bool_and' hlen_eq cert.isFeasible_polyTime).of_enc_eq fun p ↦ congrArg encBool ?_
  simp [LocalSearchProblem.Feasible]

/-- Computing `cert.standardOptimum` runs within deterministic polynomial space
(`ComputableInPolySpace`). -/
theorem computableInPolySpace_standardOptimum (cert : PLSCertificate P) [Inhabited α] :
    ComputableInPolySpace cert.standardOptimum (encPair P.enc encBits) encBits := by
  have hfeas_pt := cert.decide_feasible_polyTime
  let initFn (p : α × List Bool) : α × List Bool :=
    (p.1, if P.Feasible p.1 p.2 then p.2 else cert.initSol p.1)
  have hinit_pt : ComputableInPolyTime initFn
      (encPair P.enc encBits) (encPair P.enc encBits) := by
    have h2 : ComputableInPolyTime
        (fun p : α × List Bool ↦ if decide (P.Feasible p.1 p.2) then p.2 else cert.initSol p.1)
        (encPair P.enc encBits) encBits :=
      hfeas_pt.ite' (snd P.enc encBits) (cert.initSol_polyTime.comp (fst P.enc encBits))
    have h2' : ComputableInPolyTime
        (fun p : α × List Bool ↦ if P.Feasible p.1 p.2 then p.2 else cert.initSol p.1)
        (encPair P.enc encBits) encBits := by
      simpa only [decide_eq_true_eq] using h2
    exact (fst P.enc encBits).prod h2'
  have hstep_pt : ComputableInPolyTime cert.standardStep
      (encPair P.enc encBits) (encPair P.enc encBits) := by
    have hget : ComputableInPolyTime
        (fun p : α × List Bool ↦ (cert.improve p).getD p.2) (encPair P.enc encBits) encBits :=
      optionGetDWithInput cert.improve_polyTime (snd P.enc encBits)
    have h2 : ComputableInPolyTime
        (fun p : α × List Bool ↦
          if decide (P.Feasible p.1 p.2) then (cert.improve p).getD p.2 else cert.initSol p.1)
        (encPair P.enc encBits) encBits :=
      hfeas_pt.ite' hget (cert.initSol_polyTime.comp (fst P.enc encBits))
    have h2' : ComputableInPolyTime
        (fun p : α × List Bool ↦
          if P.Feasible p.1 p.2 then (cert.improve p).getD p.2 else cert.initSol p.1)
        (encPair P.enc encBits) encBits := by
      simpa only [decide_eq_true_eq] using h2
    exact (fst P.enc encBits).prod h2'
  have hn_pt : ComputableInPolyTime
      (fun p : α × List Bool ↦ 2 ^ P.solWidth p.1) (encPair P.enc encBits) encNat :=
    binary_two_pow.comp (cert.solWidth_polyTime.comp (fst P.enc encBits))
  have hstate_inv : ∀ (p : α × List Bool) (k : ℕ),
      (cert.standardStep^[k] (initFn p)).1 = p.1 ∧
      (cert.standardStep^[k] (initFn p)).2.length = P.solWidth p.1 := by
    intro p k
    induction k with
    | zero =>
      refine ⟨rfl, ?_⟩
      dsimp only [initFn]
      split_ifs with hf
      · exact hf.1
      · exact (cert.initSol_feasible p.1).1
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      set st := cert.standardStep^[k] (initFn p)
      have hst : st = (p.1, st.2) := Prod.ext ih.1 rfl
      rw [hst]
      refine ⟨rfl, ?_⟩
      dsimp only [standardStep]
      split_ifs with hf
      · cases hi : cert.improve (p.1, st.2) with
        | none => exact ih.2
        | some s' => exact (cert.improve_some p.1 st.2 s' hf hi).feasible_right.1
      · exact (cert.initSol_feasible p.1).1
  obtain ⟨cw, dw, hw_le⟩ := cert.solWidth_polyTime.polyBounded_length.exists_le
  let B (p : α × List Bool) : ℕ :=
    2 * (encPair P.enc encBits p).length +
      cw * ((encPair P.enc encBits p).length + 1) ^ dw + 2
  have hB : PolyBounded (fun p ↦ (encPair P.enc encBits p).length) B := by
    dsimp only [B]
    growth_poly
  have hstate_bound : ∀ (p : α × List Bool) (k : ℕ), k ≤ 2 ^ P.solWidth p.1 →
      (encPair P.enc encBits (cert.standardStep^[k] (initFn p))).length ≤ B p := by
    intro p k _
    obtain ⟨hfst, hlen⟩ := hstate_inv p k
    have hpx : (P.enc p.1).length ≤ (encPair P.enc encBits p).length :=
      length_le_encPair_left P.enc encBits p
    have hw : P.solWidth p.1 ≤ cw * ((P.enc p.1).length + 1) ^ dw := by
      simpa only [encUnary_apply, List.length_replicate] using hw_le p.1
    have hw' : P.solWidth p.1 ≤ cw * ((encPair P.enc encBits p).length + 1) ^ dw :=
      hw.trans (Nat.mul_le_mul_left cw (Nat.pow_le_pow_left (Nat.add_le_add_right hpx 1) dw))
    rw [length_encPair (cert.standardStep^[k] (initFn p)), encBits_apply, hfst, hlen]
    dsimp only [B]
    omega
  have hiter_ps : ComputableInPolySpace
      (fun p : α × List Bool ↦ cert.standardStep^[2 ^ P.solWidth p.1] (initFn p))
      (encPair P.enc encBits) (encPair P.enc encBits) :=
    ComputableInPolySpace.iterate hn_pt
      (ComputableInPolySpace.of_polyTime hinit_pt)
      (ComputableInPolySpace.of_polyTime hstep_pt) hB hstate_bound
  exact (ComputableInPolySpace.of_polyTime (snd P.enc encBits)).comp hiter_ps

/-- The exact standard-algorithm decision language: given `(x, s')` where `s'` is
locally optimal for `x`, is `s'` equal to `cert.standardOptimum (x, cert.initSol x)`?
-/
def standardAlgExactLang (cert : PLSCertificate P) : Set (α × List Bool) :=
  { p | P.IsLocallyOptimal p.1 p.2 ∧ p.2 = cert.standardOptimum (p.1, cert.initSol p.1) }

/-- The exact standard-algorithm decision language belongs to `Cslib.Complexity.PSPACE`. -/
theorem standardAlgExactLang_mem_PSPACE (cert : PLSCertificate P) [Inhabited α] :
    cert.standardAlgExactLang ∈ PSPACE (encPair P.enc encBits) := by
  let isOptBool (p : α × List Bool) : Bool :=
    decide (P.Feasible p.1 p.2) && !(cert.improve p).isSome
  have hopt_pt : ComputableInPolyTime isOptBool (encPair P.enc encBits) encBool :=
    bool_and' cert.decide_feasible_polyTime (bool_not.comp (optionIsSome cert.improve_polyTime))
  have hisOpt_iff (p : α × List Bool) : isOptBool p = true ↔ P.IsLocallyOptimal p.1 p.2 := by
    rcases p with ⟨x, s⟩
    dsimp only [isOptBool]
    by_cases hf : P.Feasible x s
    · rw [decide_eq_true hf, Bool.true_and]
      cases hi : cert.improve (x, s) with
      | none =>
        simp only [Option.isSome_none, Bool.not_false, true_iff]
        exact cert.improve_none x s hf hi
      | some s' =>
        simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, false_iff]
        intro hopt
        exact hopt.2 s' (cert.improve_some x s s' hf hi)
    · rw [decide_eq_false hf, Bool.false_and]
      simp only [Bool.false_eq_true, false_iff]
      exact fun hopt ↦ hf hopt.1
  have hstart_ps : ComputableInPolySpace
      (fun p : α × List Bool ↦ cert.standardOptimum (p.1, cert.initSol p.1))
      (encPair P.enc encBits) encBits :=
    cert.computableInPolySpace_standardOptimum.comp
      (ComputableInPolySpace.of_polyTime
        ((fst P.enc encBits).prod (cert.initSol_polyTime.comp (fst P.enc encBits))))
  have heq_ps : ComputableInPolySpace
      (fun p : α × List Bool ↦ decide (p.2 = cert.standardOptimum (p.1, cert.initSol p.1)))
      (encPair P.enc encBits) encBool :=
    (ComputableInPolySpace.of_polyTime (decide_eq' (fst encBits encBits) (snd encBits encBits)))
      |>.comp ((ComputableInPolySpace.of_polyTime (snd P.enc encBits)).prod hstart_ps)
  have hdec_ps : ComputableInPolySpace
      (fun p : α × List Bool ↦
        isOptBool p && decide (p.2 = cert.standardOptimum (p.1, cert.initSol p.1)))
      (encPair P.enc encBits) encBool :=
    (ComputableInPolySpace.of_polyTime bool_and).comp
      ((ComputableInPolySpace.of_polyTime hopt_pt).prod heq_ps)
  refine mem_PSPACE.mpr ⟨_, hdec_ps, fun p ↦ ?_⟩
  simp [standardAlgExactLang, hisOpt_iff]

/-- Parameterized standard-algorithm decision language: given
`(instance x, initial feasible solution s₀, query parameter q)`, does `s*(x, s₀)` satisfy the
polynomial-time query predicate `query (x, q, s*(x, s₀))`?
-/
def standardAlgQueryLang (cert : PLSCertificate P) {κ : Type}
    (query : (α × κ) × List Bool → Bool) : Set ((α × List Bool) × κ) :=
  { p | P.Feasible p.1.1 p.1.2 ∧ query ((p.1.1, p.2), cert.standardOptimum p.1) = true }

/-- For any polynomial-time query predicate `query`, `cert.standardAlgQueryLang query` belongs to
`Cslib.Complexity.PSPACE`. -/
theorem standardAlgQueryLang_mem_PSPACE (cert : PLSCertificate P) [Inhabited α]
    {κ : Type} {encQ : κ ↪ List Bool} {query : (α × κ) × List Bool → Bool}
    (hq : ComputableInPolyTime query (encPair (encPair P.enc encQ) encBits) encBool) :
    cert.standardAlgQueryLang query ∈ PSPACE (encPair (encPair P.enc encBits) encQ) := by
  let encIn := encPair (encPair P.enc encBits) encQ
  have hp1 : ComputableInPolyTime (fun p : (α × List Bool) × κ ↦ p.1)
      encIn (encPair P.enc encBits) := fst (encPair P.enc encBits) encQ
  have hfeas_pt : ComputableInPolyTime
      (fun p : (α × List Bool) × κ ↦ decide (P.Feasible p.1.1 p.1.2)) encIn encBool :=
    cert.decide_feasible_polyTime.comp hp1
  have hopt_ps : ComputableInPolySpace
      (fun p : (α × List Bool) × κ ↦ cert.standardOptimum p.1) encIn encBits :=
    cert.computableInPolySpace_standardOptimum.comp (ComputableInPolySpace.of_polyTime hp1)
  have hxq_ps : ComputableInPolySpace
      (fun p : (α × List Bool) × κ ↦ (p.1.1, p.2)) encIn (encPair P.enc encQ) :=
    ComputableInPolySpace.of_polyTime
      (((fst P.enc encBits).comp hp1).prod (snd (encPair P.enc encBits) encQ))
  have hq_ps : ComputableInPolySpace
      (fun p : (α × List Bool) × κ ↦ query ((p.1.1, p.2), cert.standardOptimum p.1))
      encIn encBool :=
    (ComputableInPolySpace.of_polyTime hq).comp (hxq_ps.prod hopt_ps)
  have hdec_ps : ComputableInPolySpace
      (fun p : (α × List Bool) × κ ↦
        decide (P.Feasible p.1.1 p.1.2) && query ((p.1.1, p.2), cert.standardOptimum p.1))
      encIn encBool :=
    (ComputableInPolySpace.of_polyTime bool_and).comp
      ((ComputableInPolySpace.of_polyTime hfeas_pt).prod hq_ps)
  refine mem_PSPACE.mpr ⟨_, hdec_ps, fun p ↦ ?_⟩
  simp [standardAlgQueryLang]

end PLSCertificate

/-! ### `PLS`-Reductions and Tight `PLS`-Reductions -/

/-- A polynomial-time `PLS`-reduction `(f, g)` from `P` to `Q`
: `f` maps instances of `P` to instances of `Q` in polynomial time, `g` maps feasible
solutions of `f x` back to feasible solutions of `x` in polynomial time, and local optima of `f x`
map to local optima of `x`.
-/
structure PLSReduction {α β : Type*} (P : LocalSearchProblem α) (Q : LocalSearchProblem β) where
  /-- Forward polynomial-time map on instances. -/
  f : α → β
  /-- Backward polynomial-time map on `(source_instance, target_solution)`. -/
  g : α × List Bool → List Bool
  /-- Polynomial-time computability of `f`. -/
  f_polyTime : ComputableInPolyTime f P.enc Q.enc
  /-- Polynomial-time computability of `g`. -/
  g_polyTime : ComputableInPolyTime g (encPair P.enc encBits) encBits
  /-- Feasible solutions of `f x` map to feasible solutions of `x`. -/
  map_feasible : ∀ x s, Q.Feasible (f x) s → P.Feasible x (g (x, s))
  /-- Locally optimal solutions of `f x` map to locally optimal solutions of `x`. -/
  map_locallyOptimal : ∀ x s, Q.IsLocallyOptimal (f x) s → P.IsLocallyOptimal x (g (x, s))

namespace PLSReduction

/-- Identity `PLS`-reduction on `P`. -/
@[expose]
def refl {α : Type} (P : LocalSearchProblem α) : PLSReduction P P where
  f := id
  g := Prod.snd
  f_polyTime := ComputableInPolyTime.id'
  g_polyTime := snd P.enc encBits
  map_feasible := fun _ _ h ↦ h
  map_locallyOptimal := fun _ _ h ↦ h

/-- Composition of `PLS`-reductions `P ≤_PLS Q` and `Q ≤_PLS R`. -/
@[expose]
def trans {α β γ : Type} {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    {R : LocalSearchProblem γ} (r₁ : PLSReduction P Q) (r₂ : PLSReduction Q R) :
    PLSReduction P R where
  f := r₂.f ∘ r₁.f
  g x := r₁.g (x.1, r₂.g (r₁.f x.1, x.2))
  f_polyTime := r₂.f_polyTime.comp r₁.f_polyTime
  g_polyTime := by
    have hf1 : ComputableInPolyTime (fun x : α × List Bool ↦ r₁.f x.1)
        (encPair P.enc encBits) Q.enc := r₁.f_polyTime.comp (fst P.enc encBits)
    have hg2 : ComputableInPolyTime (fun x : α × List Bool ↦ r₂.g (r₁.f x.1, x.2))
        (encPair P.enc encBits) encBits :=
      r₂.g_polyTime.comp (hf1.prod (snd P.enc encBits))
    exact r₁.g_polyTime.comp ((fst P.enc encBits).prod hg2)
  map_feasible := fun x s hs ↦ r₁.map_feasible x _ (r₂.map_feasible (r₁.f x) s hs)
  map_locallyOptimal := fun x s hs ↦
    r₁.map_locallyOptimal x _ (r₂.map_locallyOptimal (r₁.f x) s hs)

/-- Every `PLS`-reduction to a total target (`IsTotalSearch Q.searchRel`) induces a
polynomial-time search reduction `Cslib.Complexity.SearchReducible`. -/
theorem searchReducible {α β : Type} {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    (r : PLSReduction P Q) (hQ : IsTotalSearch Q.searchRel) :
    SearchReducible P.enc Q.enc P.searchRel Q.searchRel :=
  SearchReducible.of_isTotalSearch hQ r.f_polyTime r.g_polyTime r.map_locallyOptimal

/-- `PLS`-hardness transfers along `PLSReduction` when the target is total. -/
theorem plsHard {α β : Type} {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    (r : PLSReduction P Q) (hP : SearchHard @PLS P.enc P.searchRel)
    (hQ : IsTotalSearch Q.searchRel) :
    SearchHard @PLS Q.enc Q.searchRel :=
  hP.trans (r.searchReducible hQ)

/-- `PLS`-completeness transfers along `PLSReduction` when `Q` has a `PLSCertificate`. -/
theorem plsComplete {α β : Type} {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    (r : PLSReduction P Q) (hP : SearchHard @PLS P.enc P.searchRel)
    (certQ : PLSCertificate Q) :
    SearchComplete @PLS Q.enc Q.searchRel :=
  ⟨certQ.searchRel_mem_PLS, r.plsHard hP certQ.isTotalSearch_searchRel⟩

end PLSReduction

/-- A **tight `PLS`-reduction** from `P` to `Q`: a `PLSReduction`
equipped with a family of reasonable feasible solutions `reasonable x` and a polynomial-time
right-inverse `lift` satisfying:
1. `reasonable x` contains all local optima of `f x`;
2. for every feasible `s` of `x`, `lift (x, s)` is a reasonable feasible solution of `f x`
   satisfying `g (x, lift (x, s)) = s`;
3. for every non-trivial directed path in `T_Q(f x)` from `q ∈ reasonable x` to
   `q' ∈ reasonable x` whose internal vertices all lie outside `reasonable x`, either
   `g (x, q) = g (x, q')` or `g (x, q) → g (x, q')` is a directed edge in `T_P(x)`.
-/
structure TightPLSReduction {α β : Type*} (P : LocalSearchProblem α) (Q : LocalSearchProblem β)
    extends PLSReduction P Q where
  /-- Subset `R(x)` of reasonable solutions of `f x`. -/
  reasonableSet : α → Set (List Bool)
  /-- Polynomial-time lift mapping `(x, feasible s of x)` into `reasonableSet x`. -/
  lift : α × List Bool → List Bool
  /-- Polynomial-time computability of `lift`. -/
  lift_polyTime : ComputableInPolyTime lift (encPair P.enc encBits) encBits
  /-- Every reasonable solution is feasible for `f x`. -/
  reasonable_feasible : ∀ x q, q ∈ reasonableSet x → Q.Feasible (f x) q
  /-- Property 1: `reasonableSet x` contains every locally optimal solution of `f x`. -/
  optima_reasonable : ∀ x q, Q.IsLocallyOptimal (f x) q → q ∈ reasonableSet x
  /-- Property 2a: `lift (x, s)` is reasonable whenever `s` is feasible for `x`. -/
  lift_reasonable : ∀ x s, P.Feasible x s → lift (x, s) ∈ reasonableSet x
  /-- Property 2b: `g (x, lift (x, s)) = s` whenever `s` is feasible for `x`. -/
  g_lift : ∀ x s, P.Feasible x s → g (x, lift (x, s)) = s
  /-- Property 3: any minimal-return path in `T_Q(f x)` between reasonable endpoints with all
  internal vertices outside `reasonableSet x` projects either to `g(x, q) = g(x, q')` or to a
  single improving edge in `T_P(x)`. -/
  minimal_path_step :
    ∀ x q q' (mid : List (List Bool)),
      q ∈ reasonableSet x → q' ∈ reasonableSet x →
      (∀ u ∈ mid, u ∉ reasonableSet x) →
      Q.TransitionPath (f x) q q' mid →
      g (x, q) = g (x, q') ∨ P.TransitionEdge x (g (x, q)) (g (x, q'))

namespace TightPLSReduction

/-- Predicate view `q ∈ r.reasonableSet x` of the reasonable solution set. -/
abbrev reasonable {α β : Type*} {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    (r : TightPLSReduction P Q) (x : α) (q : List Bool) : Prop :=
  q ∈ r.reasonableSet x

/-- Identity tight `PLS`-reduction on `P`. -/
@[expose]
def refl {α : Type} (P : LocalSearchProblem α) : TightPLSReduction P P where
  toPLSReduction := PLSReduction.refl P
  reasonableSet x := { s | P.Feasible x s }
  lift := Prod.snd
  lift_polyTime := snd P.enc encBits
  reasonable_feasible := fun _ _ h ↦ h
  optima_reasonable := fun _ _ h ↦ h.1
  lift_reasonable := fun _ _ h ↦ h
  g_lift := fun _ _ _ ↦ rfl
  minimal_path_step := by
    intro x q q' mid _ _ hmid hp
    cases hp with
    | single he => exact .inr he
    | cons he _ => exact (hmid _ List.mem_cons_self he.feasible_right).elim

/-- Smart constructor for tight reductions whose reasonable set `R(x)` has **no outgoing
transitions leaving `R(x)`** (`∀ q ∈ R(x), ∀ q', Q.TransitionEdge (f x) q q' → q' ∈ R(x)`):
every non-empty path from `R(x)` to `R(x)` with internal vertices outside `R(x)` has `mid = []`,
so only single edges `q → q'` inside `R(x)` need to be checked. -/
@[expose]
def ofClosedReasonable {α β : Type*} {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    (red : PLSReduction P Q)
    (reasonable : α → List Bool → Prop)
    (lift : α × List Bool → List Bool)
    (hlift_pt : ComputableInPolyTime lift (encPair P.enc encBits) encBits)
    (hreas_feas : ∀ x q, reasonable x q → Q.Feasible (red.f x) q)
    (hopt_reas : ∀ x q, Q.IsLocallyOptimal (red.f x) q → reasonable x q)
    (hlift_reas : ∀ x s, P.Feasible x s → reasonable x (lift (x, s)))
    (hg_lift : ∀ x s, P.Feasible x s → red.g (x, lift (x, s)) = s)
    (hclosed : ∀ x q q', reasonable x q → Q.TransitionEdge (red.f x) q q' → reasonable x q')
    (hedge : ∀ x q q', reasonable x q → reasonable x q' → Q.TransitionEdge (red.f x) q q' →
      red.g (x, q) = red.g (x, q') ∨ P.TransitionEdge x (red.g (x, q)) (red.g (x, q'))) :
    TightPLSReduction P Q where
  toPLSReduction := red
  reasonableSet x := { q | reasonable x q }
  lift := lift
  lift_polyTime := hlift_pt
  reasonable_feasible := hreas_feas
  optima_reasonable := hopt_reas
  lift_reasonable := hlift_reas
  g_lift := hg_lift
  minimal_path_step := by
    intro x q q' mid hq hq' hmid hp
    cases hp with
    | single he => exact hedge x q q' hq hq' he
    | cons he _ => exact (hmid _ List.mem_cons_self (hclosed x q _ hq he)).elim

@[simp]
theorem ofClosedReasonable_toPLSReduction {α β : Type*} {P : LocalSearchProblem α}
    {Q : LocalSearchProblem β} (red : PLSReduction P Q) (reasonable : α → List Bool → Prop)
    (lift : α × List Bool → List Bool)
    (hlift_pt : ComputableInPolyTime lift (encPair P.enc encBits) encBits)
    (hreas_feas : ∀ x q, reasonable x q → Q.Feasible (red.f x) q)
    (hopt_reas : ∀ x q, Q.IsLocallyOptimal (red.f x) q → reasonable x q)
    (hlift_reas : ∀ x s, P.Feasible x s → reasonable x (lift (x, s)))
    (hg_lift : ∀ x s, P.Feasible x s → red.g (x, lift (x, s)) = s)
    (hclosed : ∀ x q q', reasonable x q → Q.TransitionEdge (red.f x) q q' → reasonable x q')
    (hedge : ∀ x q q', reasonable x q → reasonable x q' → Q.TransitionEdge (red.f x) q q' →
      red.g (x, q) = red.g (x, q') ∨ P.TransitionEdge x (red.g (x, q)) (red.g (x, q'))) :
    (ofClosedReasonable red reasonable lift hlift_pt hreas_feas hopt_reas hlift_reas hg_lift
      hclosed hedge).toPLSReduction = red :=
  rfl

@[simp]
theorem ofClosedReasonable_lift {α β : Type*} {P : LocalSearchProblem α}
    {Q : LocalSearchProblem β} (red : PLSReduction P Q) (reasonable : α → List Bool → Prop)
    (lift : α × List Bool → List Bool)
    (hlift_pt : ComputableInPolyTime lift (encPair P.enc encBits) encBits)
    (hreas_feas : ∀ x q, reasonable x q → Q.Feasible (red.f x) q)
    (hopt_reas : ∀ x q, Q.IsLocallyOptimal (red.f x) q → reasonable x q)
    (hlift_reas : ∀ x s, P.Feasible x s → reasonable x (lift (x, s)))
    (hg_lift : ∀ x s, P.Feasible x s → red.g (x, lift (x, s)) = s)
    (hclosed : ∀ x q q', reasonable x q → Q.TransitionEdge (red.f x) q q' → reasonable x q')
    (hedge : ∀ x q q', reasonable x q → reasonable x q' → Q.TransitionEdge (red.f x) q q' →
      red.g (x, q) = red.g (x, q') ∨ P.TransitionEdge x (red.g (x, q)) (red.g (x, q'))) :
    (ofClosedReasonable red reasonable lift hlift_pt hreas_feas hopt_reas hlift_reas hg_lift
      hclosed hedge).lift = lift :=
  rfl

@[simp]
theorem mem_reasonableSet_ofClosedReasonable {α β : Type*} {P : LocalSearchProblem α}
    {Q : LocalSearchProblem β} (red : PLSReduction P Q) (reasonable : α → List Bool → Prop)
    (lift : α × List Bool → List Bool)
    (hlift_pt : ComputableInPolyTime lift (encPair P.enc encBits) encBits)
    (hreas_feas : ∀ x q, reasonable x q → Q.Feasible (red.f x) q)
    (hopt_reas : ∀ x q, Q.IsLocallyOptimal (red.f x) q → reasonable x q)
    (hlift_reas : ∀ x s, P.Feasible x s → reasonable x (lift (x, s)))
    (hg_lift : ∀ x s, P.Feasible x s → red.g (x, lift (x, s)) = s)
    (hclosed : ∀ x q q', reasonable x q → Q.TransitionEdge (red.f x) q q' → reasonable x q')
    (hedge : ∀ x q q', reasonable x q → reasonable x q' → Q.TransitionEdge (red.f x) q q' →
      red.g (x, q) = red.g (x, q') ∨ P.TransitionEdge x (red.g (x, q)) (red.g (x, q')))
    (x : α) (q : List Bool) :
    q ∈ (ofClosedReasonable red reasonable lift hlift_pt hreas_feas hopt_reas hlift_reas hg_lift
      hclosed hedge).reasonableSet x ↔ reasonable x q :=
  Iff.rfl

/-- Split any positive-length `TransitionSteps` walk ending in `R` at its first return to `R`. -/
private theorem split_first_return {β : Type*} {Q : LocalSearchProblem β}
    (R : List Bool → Prop) {y : β} :
    ∀ {k : ℕ} {q q' : List Bool},
      Q.TransitionSteps y (k + 1) q q' → R q' →
      ∃ (q₁ : List Bool) (mid : List (List Bool)) (rem : ℕ),
        mid.length + 1 + rem = k + 1 ∧
        R q₁ ∧
        (∀ u ∈ mid, ¬ R u) ∧
        Q.TransitionPath y q q₁ mid ∧
        Q.TransitionSteps y rem q₁ q' := by
  intro k
  induction k with
  | zero =>
    intro q q' hp hq'
    cases hp with
    | succ he hp0 =>
      cases hp0 with
      | zero _ =>
        exact ⟨q', [], 0, rfl, hq', by simp,
          LocalSearchProblem.TransitionPath.single he,
          LocalSearchProblem.TransitionSteps.zero he.feasible_right⟩
  | succ k ih =>
    intro q q' hp hq'
    cases hp with
    | @succ _ _ u _ he hrest =>
      by_cases hu : R u
      · exact ⟨u, [], k + 1, by simp; omega, hu, by simp,
          LocalSearchProblem.TransitionPath.single he, hrest⟩
      · obtain ⟨q₁, mid, rem, hlen, hq₁, hmid, hpath, hsteps⟩ := ih hrest hq'
        refine ⟨q₁, u :: mid, rem, ?_, hq₁, ?_,
          LocalSearchProblem.TransitionPath.cons he hpath, hsteps⟩
        · simp only [List.length_cons]; omega
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hwm
          · exact hu
          · exact hmid w hwm

/-- Project any `TransitionPath` between reasonable endpoints (even with internal reasonable
vertices) to either equality `g(x, q) = g(x, q')` or a non-empty `P.TransitionPath` whose internal
vertices are all images `g(x, u)` of reasonable internal vertices `u ∈ mid`. -/
theorem project_transitionPath {α β : Type*} {P : LocalSearchProblem α}
    {Q : LocalSearchProblem β} (r : TightPLSReduction P Q) {x : α} :
    ∀ {mid : List (List Bool)} {q q' : List Bool},
      r.reasonable x q → r.reasonable x q' →
      Q.TransitionPath (r.f x) q q' mid →
      r.g (x, q) = r.g (x, q') ∨
        ∃ midP : List (List Bool),
          (∀ v ∈ midP, ∃ u ∈ mid, r.reasonable x u ∧ v = r.g (x, u)) ∧
          P.TransitionPath x (r.g (x, q)) (r.g (x, q')) midP := by
  intro mid
  induction hlen : mid.length using Nat.strongRecOn generalizing mid with
  | ind n ih =>
    intro q q' hq hq' hp
    subst hlen
    -- Check whether any internal vertex in `mid` is reasonable; if so, split at the first one!
    have hsplit_path :
        (∀ u ∈ mid, ¬ r.reasonable x u) ∨
          ∃ (mid₁ : List (List Bool)) (u : List Bool) (mid₂ : List (List Bool)),
            mid = mid₁ ++ u :: mid₂ ∧
            r.reasonable x u ∧
            (∀ w ∈ mid₁, ¬ r.reasonable x w) ∧
            Q.TransitionPath (r.f x) q u mid₁ ∧
            Q.TransitionPath (r.f x) u q' mid₂ := by
      clear ih hq hq'
      induction hp with
      | single _ => exact .inl (by simp)
      | @cons _ u _ tail he hrest ihr =>
        by_cases hu : r.reasonable x u
        · exact .inr ⟨[], u, tail, rfl, hu, by simp,
            LocalSearchProblem.TransitionPath.single he, hrest⟩
        · rcases ihr with hall | ⟨mid₁, w, mid₂, hmid_eq, hw, hmid₁, hp₁, hp₂⟩
          · refine .inl fun w hw ↦ ?_
            rcases List.mem_cons.mp hw with rfl | hwt
            · exact hu
            · exact hall w hwt
          · refine .inr ⟨u :: mid₁, w, mid₂, by simp [hmid_eq], hw, ?_,
              LocalSearchProblem.TransitionPath.cons he hp₁, hp₂⟩
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hzm
            · exact hu
            · exact hmid₁ z hzm
    rcases hsplit_path with hall | ⟨mid₁, u, mid₂, hmid_eq, hu, hmid₁, hp₁, hp₂⟩
    · rcases r.minimal_path_step x q q' mid hq hq' hall hp with heq | hedge
      · exact .inl heq
      · exact .inr ⟨[], by simp, LocalSearchProblem.TransitionPath.single hedge⟩
    · have hlen2 : mid₂.length < mid.length := by
        simp [hmid_eq]
        omega
      have hstep1 := r.minimal_path_step x q u mid₁ hq hu hmid₁ hp₁
      have hstep2 := ih mid₂.length hlen2 (mid := mid₂) rfl hu hq' hp₂
      rcases hstep1 with heq1 | hedge1
      · rcases hstep2 with heq2 | ⟨midP, hmidP, hpP⟩
        · exact .inl (heq1.trans heq2)
        · refine .inr ⟨midP, ?_, heq1.symm ▸ hpP⟩
          intro v hv
          obtain ⟨w, hw, hw_reas, rfl⟩ := hmidP v hv
          exact ⟨w, by simp [hmid_eq, hw], hw_reas, rfl⟩
      · rcases hstep2 with heq2 | ⟨midP, hmidP, hpP⟩
        · exact .inr ⟨[], by simp,
            heq2 ▸ LocalSearchProblem.TransitionPath.single hedge1⟩
        · refine .inr ⟨r.g (x, u) :: midP, ?_,
            LocalSearchProblem.TransitionPath.cons hedge1 hpP⟩
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hvm
          · exact ⟨u, by simp [hmid_eq], hu, rfl⟩
          · obtain ⟨w, hw, hw_reas, rfl⟩ := hmidP v hvm
            exact ⟨w, by simp [hmid_eq, hw], hw_reas, rfl⟩

/-- **Transitivity of tight `PLS`-reductions**: the composition of tight reductions `P ≤_tight Q`
and `Q ≤_tight R` is a tight `PLS`-reduction `P ≤_tight R`. -/
@[expose]
def trans {α β γ : Type} {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    {R : LocalSearchProblem γ} (r₁ : TightPLSReduction P Q) (r₂ : TightPLSReduction Q R) :
    TightPLSReduction P R where
  toPLSReduction := r₁.toPLSReduction.trans r₂.toPLSReduction
  reasonableSet x := { w | r₂.reasonable (r₁.f x) w ∧ r₁.reasonable x (r₂.g (r₁.f x, w)) }
  lift p := r₂.lift (r₁.f p.1, r₁.lift p)
  lift_polyTime := by
    have hf1 : ComputableInPolyTime (fun p : α × List Bool ↦ r₁.f p.1)
        (encPair P.enc encBits) Q.enc := r₁.f_polyTime.comp (fst P.enc encBits)
    exact r₂.lift_polyTime.comp (hf1.prod r₁.lift_polyTime)
  reasonable_feasible x w hw := r₂.reasonable_feasible (r₁.f x) w hw.1
  optima_reasonable x w hw :=
    ⟨r₂.optima_reasonable (r₁.f x) w hw,
      r₁.optima_reasonable x _ (r₂.map_locallyOptimal (r₁.f x) w hw)⟩
  lift_reasonable x s hs := by
    have h1 := r₁.lift_reasonable x s hs
    have h1f := r₁.reasonable_feasible x _ h1
    refine ⟨r₂.lift_reasonable (r₁.f x) _ h1f, ?_⟩
    rw [r₂.g_lift (r₁.f x) _ h1f]
    exact h1
  g_lift x s hs := by
    dsimp only [PLSReduction.trans]
    have h1 := r₁.lift_reasonable x s hs
    have h1f := r₁.reasonable_feasible x _ h1
    rw [r₂.g_lift (r₁.f x) _ h1f, r₁.g_lift x s hs]
  minimal_path_step := by
    intro x w w' mid hw hw' hmid hp
    dsimp only [PLSReduction.trans]
    rcases r₂.project_transitionPath hw.1 hw'.1 hp with heq | ⟨midQ, hmidQ, hpQ⟩
    · exact .inl (congrArg (fun q ↦ r₁.g (x, q)) heq)
    · refine r₁.minimal_path_step x _ _ midQ hw.2 hw'.2 ?_ hpQ
      intro q hq hq_reas
      obtain ⟨u, hu_mem, hu_reas2, rfl⟩ := hmidQ q hq
      exact hmid u hu_mem ⟨hu_reas2, hq_reas⟩

/-- Decompose any `Q.TransitionSteps (f x) k q q'` between reasonable endpoints `q, q'` into a
projected `P.TransitionSteps x m (g (x, q)) (g (x, q'))` of length `m ≤ k`. -/
theorem project_transitionSteps {α β : Type*} {P : LocalSearchProblem α}
    {Q : LocalSearchProblem β} (r : TightPLSReduction P Q) {x : α} :
    ∀ {k : ℕ} {q q' : List Bool},
      r.reasonable x q → r.reasonable x q' →
      Q.TransitionSteps (r.f x) k q q' →
      ∃ m ≤ k, P.TransitionSteps x m (r.g (x, q)) (r.g (x, q')) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro q q' hq hq' hp
    cases k with
    | zero =>
      cases hp with
      | zero _ =>
        exact ⟨0, le_rfl, .zero (r.map_feasible x q (r.reasonable_feasible x q hq))⟩
    | succ k' =>
      obtain ⟨q₁, mid, rem, hlen, hq₁, hmid, hpath, hrem⟩ :=
        split_first_return (r.reasonable x) hp hq'
      have hrem_lt : rem < k' + 1 := by omega
      obtain ⟨m₂, hm₂, hp₂⟩ := ih rem hrem_lt hq₁ hq' hrem
      rcases r.minimal_path_step x q q₁ mid hq hq₁ hmid hpath with heq | hedge
      · exact ⟨m₂, by omega, heq.symm ▸ hp₂⟩
      · exact ⟨m₂ + 1, by omega, .succ hedge hp₂⟩

/-- **Height preservation of tight `PLS`-reductions**: for every feasible solution `s` of `x`,
`P.height x s ≤ Q.height (f x) (lift (x, s))`. -/
theorem height_le {α β : Type*} {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    (r : TightPLSReduction P Q) (x : α) {s : List Bool} (hs : P.Feasible x s) :
    P.height x s ≤ Q.height (r.f x) (r.lift (x, s)) := by
  have hlift_reas := r.lift_reasonable x s hs
  have hlift_feas := r.reasonable_feasible x _ hlift_reas
  obtain ⟨q', hpQ, hoptQ⟩ := Q.exists_transitionSteps_height hlift_feas
  have hq'_reas := r.optima_reasonable x q' hoptQ
  obtain ⟨m, hm_le, hpP⟩ := r.project_transitionSteps hlift_reas hq'_reas hpQ
  rw [r.g_lift x s hs] at hpP
  have hoptP := r.map_locallyOptimal x q' hoptQ
  exact (P.height_le_of_transitionSteps hpP hoptP).trans hm_le

/-- **Transfer of polynomial-time exponential-height instance families** along a tight
`PLS`-reduction. -/
theorem transfer_exp_height {α β : Type} {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    (r : TightPLSReduction P Q)
    {instP : ℕ → α × List Bool}
    (hpt : ComputableInPolyTime instP encUnary (encPair P.enc encBits))
    (hfeas : ∀ n, P.Feasible (instP n).1 (instP n).2)
    (hexp : ∀ n, 2 ^ n ≤ P.height (instP n).1 (instP n).2) :
    ∃ instQ : ℕ → β × List Bool,
      ComputableInPolyTime instQ encUnary (encPair Q.enc encBits) ∧
      (∀ n, Q.Feasible (instQ n).1 (instQ n).2) ∧
      (∀ n, 2 ^ n ≤ Q.height (instQ n).1 (instQ n).2) := by
  let instQ (n : ℕ) : β × List Bool :=
    (r.f (instP n).1, r.lift (instP n))
  have hinstQ_pt : ComputableInPolyTime instQ encUnary (encPair Q.enc encBits) :=
    (r.f_polyTime.comp hpt.fst').prod (r.lift_polyTime.comp hpt)
  refine ⟨instQ, hinstQ_pt, fun n ↦ ?_, fun n ↦ ?_⟩
  · exact r.reasonable_feasible _ _ (r.lift_reasonable _ _ (hfeas n))
  · exact (hexp n).trans (r.height_le (instP n).1 (hfeas n))

/-- **Reachable-optimum preservation of tight `PLS`-reductions**: every local optimum `q*` of
`f x` reachable from `lift (x, s₀)` in `T_Q(f x)` projects via `g(x, q*)` to a local optimum of
`x` reachable from `s₀` in `T_P(x)`. -/
theorem reachableOptimum_map {α β : Type*} {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    (r : TightPLSReduction P Q) {x : α} {s₀ q' : List Bool}
    (hs₀ : P.Feasible x s₀)
    (hreach : Q.ReachableOptimum (r.f x) (r.lift (x, s₀)) q') :
    P.ReachableOptimum x s₀ (r.g (x, q')) := by
  obtain ⟨k, hpQ, hoptQ⟩ := hreach
  have hlift_reas := r.lift_reasonable x s₀ hs₀
  have hq'_reas := r.optima_reasonable x q' hoptQ
  obtain ⟨m, _, hpP⟩ := r.project_transitionSteps hlift_reas hq'_reas hpQ
  rw [r.g_lift x s₀ hs₀] at hpP
  exact ⟨m, hpP, r.map_locallyOptimal x q' hoptQ⟩

/-- **Transfer of `PSPACE`-hardness of the standard local search algorithm problem** along a
tight `PLS`-reduction, **irrespective of the improving-neighbor algorithm `certQ.improve`**:
if every `A ∈ PSPACE` reduces in polynomial time to a reachable-optimum query on `P` (where all
reachable local optima of `x` from `s₀` agree on the answer), then `certQ.standardAlgQueryLang`
is `PSPACEComplete` for `Q`. -/
theorem pspaceComplete_standardAlgQuery_of_universal_reachable
    {α β κ₁ κ₂ : Type} [Inhabited β] {P : LocalSearchProblem α} {Q : LocalSearchProblem β}
    (r : TightPLSReduction P Q) (certQ : PLSCertificate Q)
    {encK₁ : κ₁ ↪ List Bool} {encK₂ : κ₂ ↪ List Bool}
    {queryP : (α × κ₁) × List Bool → Bool}
    {queryQ : (β × κ₂) × List Bool → Bool}
    {mapQuery : α × κ₁ → κ₂}
    (hqueryQ_pt : ComputableInPolyTime queryQ (encPair (encPair Q.enc encK₂) encBits) encBool)
    (hmapQ_pt : ComputableInPolyTime mapQuery (encPair P.enc encK₁) encK₂)
    (hcompat : ∀ x q₁ w, r.reasonable x w →
      queryQ ((r.f x, mapQuery (x, q₁)), w) = queryP ((x, q₁), r.g (x, w)))
    (hunivP : ∀ {γ : Type} (encA : γ ↪ List Bool) (A : Set γ), A ∈ PSPACE encA →
      ∃ red : γ → (α × List Bool) × κ₁,
        ComputableInPolyTime red encA (encPair (encPair P.enc encBits) encK₁) ∧
        ∀ a : γ, P.Feasible (red a).1.1 (red a).1.2 ∧
          (∀ s', P.ReachableOptimum (red a).1.1 (red a).1.2 s' →
            (a ∈ A ↔ queryP (((red a).1.1, (red a).2), s') = true))) :
    PSPACEComplete (encPair (encPair Q.enc encBits) encK₂)
      (certQ.standardAlgQueryLang queryQ) := by
  refine ⟨certQ.standardAlgQueryLang_mem_PSPACE hqueryQ_pt, fun {γ} encA A hA ↦ ?_⟩
  obtain ⟨redP, hredP_pt, hredP_spec⟩ := hunivP encA A hA
  let encMid := encPair (encPair P.enc encBits) encK₁
  let encOut := encPair (encPair Q.enc encBits) encK₂
  let liftAll (t : (α × List Bool) × κ₁) : (β × List Bool) × κ₂ :=
    ((r.f t.1.1, r.lift t.1), mapQuery (t.1.1, t.2))
  have hliftAll_pt : ComputableInPolyTime liftAll encMid encOut := by
    have ht1 : ComputableInPolyTime (fun t : (α × List Bool) × κ₁ ↦ t.1)
        encMid (encPair P.enc encBits) := fst (encPair P.enc encBits) encK₁
    have ht11 : ComputableInPolyTime (fun t : (α × List Bool) × κ₁ ↦ t.1.1) encMid P.enc :=
      (fst P.enc encBits).comp ht1
    have ht2 : ComputableInPolyTime (fun t : (α × List Bool) × κ₁ ↦ t.2) encMid encK₁ :=
      snd (encPair P.enc encBits) encK₁
    exact ((r.f_polyTime.comp ht11).prod (r.lift_polyTime.comp ht1)).prod
      (hmapQ_pt.comp (ht11.prod ht2))
  refine ⟨liftAll ∘ redP, hliftAll_pt.comp hredP_pt, fun a ↦ ?_⟩
  obtain ⟨hfeasP, hiffP⟩ := hredP_spec a
  set x := (redP a).1.1
  set s₀ := (redP a).1.2
  set q₁ := (redP a).2
  have hfeasQ : Q.Feasible (r.f x) (r.lift (x, s₀)) :=
    r.reasonable_feasible x _ (r.lift_reasonable x s₀ hfeasP)
  have hreachQ : Q.ReachableOptimum (r.f x) (r.lift (x, s₀))
      (certQ.standardOptimum (r.f x, r.lift (x, s₀))) :=
    certQ.reachableOptimum_standardOptimum hfeasQ
  have hreachP : P.ReachableOptimum x s₀
      (r.g (x, certQ.standardOptimum (r.f x, r.lift (x, s₀)))) :=
    r.reachableOptimum_map hfeasP hreachQ
  have hreas_opt : r.reasonable x (certQ.standardOptimum (r.f x, r.lift (x, s₀))) :=
    r.optima_reasonable x _ hreachQ.choose_spec.2
  change a ∈ A ↔ Q.Feasible (r.f x) (r.lift (x, s₀)) ∧
    queryQ ((r.f x, mapQuery (x, q₁)), certQ.standardOptimum (r.f x, r.lift (x, s₀))) = true
  rw [hcompat x q₁ _ hreas_opt]
  exact ⟨fun ha ↦ ⟨hfeasQ, (hiffP _ hreachP).mp ha⟩, fun ⟨_, hq⟩ ↦ (hiffP _ hreachP).mpr hq⟩

end TightPLSReduction

private example :
    ∃ P : LocalSearchProblem Bool,
      P.IsLocallyOptimal true [true] ∧ P.height true [false] = 1 := by
  let P : LocalSearchProblem Bool :=
    { enc := encBool
      solWidth := fun _ ↦ 1
      isFeasible := fun p ↦ decide (p.2.length = 1)
      cost := fun p ↦ if p.2.headD false then 1 else 0
      neighborSet := fun _ ↦ { q | q.2 ≠ q.1 }
      sense := .maximize }
  have hopt_true : P.IsLocallyOptimal true [true] := by
    refine ⟨⟨rfl, rfl⟩, fun s' he ↦ ?_⟩
    have himp := he.improves
    simp only [P, OptimizationSense.improves, List.headD_cons] at himp
    split_ifs at himp <;> omega
  refine ⟨P, hopt_true, ?_⟩
  have he : P.TransitionEdge true [false] [true] :=
    ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, by simp [P, LocalSearchProblem.isNeighbor], by decide⟩
  have hle : P.height true [false] ≤ 1 :=
    P.height_le_of_transitionSteps (.succ he (.zero he.feasible_right)) hopt_true
  have hpos : 0 < P.height true [false] := by
    by_contra h0
    have hz : P.height true [false] = 0 := by omega
    obtain ⟨s', hp, hopt⟩ := P.exists_transitionSteps_height
      (x := true) (s := [false]) ⟨rfl, rfl⟩
    rw [hz] at hp
    cases hp with
    | zero _ => exact hopt.2 [true] he
  omega

end CslibFrontier.Complexity
