/-
Copyright (c) 2026 Cslib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cslib Contributors
-/

module

public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Tight Local Search Reductions and the Local Max-Cut `PLS` Problem

This module develops two general building blocks of polynomial local search (`PLS`) theory under
standard Lean axioms, directly over `Cslib.Complexity.PLS` and `Mathlib.Combinatorics.SimpleGraph`:

1. **Abstract local search and Schäffer–Yannakakis tight reductions**: discrete local search
   problems (`LocalSearchProblem`), strictly improving and maximal improving paths, existence of
   maximal paths by natural-number cost descent, tight reductions (`TightLocalReduction`) with
   reflexivity, transitivity, and transfer of worst-case transition-path lower bounds across
   arbitrary pivoting rules.
2. **Encoded `LocalMaxCut` and bounded-degree `LocalMaxCutDeg`**: explicitly encoded edge-weighted
   graphs (`WeightedGraphCode`, `encWeightedGraph`), 1-bit flip local search (`LocalMaxCut`),
   restricted simple graphs of maximum degree at most `d` (`WeightedGraphDeg d`,
   `LocalMaxCutDeg d`), membership in `Cslib.Complexity.PLS`, polynomial-time solvability
   (`FPSearch`) for maximum degree `0` and `1`, and a tight-reduction bridge from weighted
   `SimpleGraph (Fin m)` instances (`graphLocalSearchProblem`, `encodeSimpleGraph`).

## Main definitions

* `CslibFrontier.Complexity.LocalSearch.LocalSearchProblem`: discrete local search instance with
  `ℕ`-valued cost objective (and maximization constructor `LocalSearchProblem.ofMax`).
* `CslibFrontier.Complexity.LocalSearch.TightLocalReduction`: tight local search reduction in the
  sense of Schäffer and Yannakakis.
* `CslibFrontier.Complexity.LocalSearch.WeightedGraphCode`,
  `CslibFrontier.Complexity.LocalSearch.encWeightedGraph`: explicit edge-weighted graph encoding
  with unary vertex indices and binary edge weights.
* `CslibFrontier.Complexity.LocalSearch.LocalMaxCut`,
  `CslibFrontier.Complexity.LocalSearch.WeightedGraphDeg`,
  `CslibFrontier.Complexity.LocalSearch.LocalMaxCutDeg`: the local max-cut `PLS` search problem and
  its restriction to simple graphs of maximum degree at most `d`.
* `CslibFrontier.Complexity.LocalSearch.graphCutWeight`,
  `CslibFrontier.Complexity.LocalSearch.graphLocalSearchProblem`,
  `CslibFrontier.Complexity.LocalSearch.encodeSimpleGraph`: local max-cut flip dynamics on
  `SimpleGraph V` and canonical encoding of `SimpleGraph (Fin m)`.

## Main results

* `CslibFrontier.Complexity.LocalSearch.TightLocalReduction.trans`: composition of tight local
  search reductions.
* `CslibFrontier.Complexity.LocalSearch.TightLocalReduction.length_ge_of_forall_maximal`:
  worst-case maximal improving path lower bounds transfer along any tight local search reduction.
* `CslibFrontier.Complexity.LocalSearch.localMaxCut_mem_PLS`,
  `CslibFrontier.Complexity.LocalSearch.localMaxCutDeg_mem_PLS`: `LocalMaxCut` and
  `LocalMaxCutDeg d` belong to `Cslib.Complexity.PLS`.
* `CslibFrontier.Complexity.LocalSearch.localMaxCutDeg_zero_mem_FPSearch`,
  `CslibFrontier.Complexity.LocalSearch.localMaxCutDeg_one_mem_FPSearch`: `LocalMaxCutDeg 0` and
  `LocalMaxCutDeg 1` are solvable in polynomial time (`Cslib.Complexity.FPSearch`).
* `CslibFrontier.Complexity.LocalSearch.tightLocalReductionEncodeSimpleGraph`: tight reduction
  from `graphLocalSearchProblem G w` on `SimpleGraph (Fin m)` to
  `(encodeSimpleGraph G w).toLocalSearchProblem`.
-/

public section

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

namespace CslibFrontier.Complexity.LocalSearch

/-! ### 1. Discrete Local Search Problems and Schäffer–Yannakakis Tight Reductions -/

section TightReductions

/-- A discrete local search problem on configuration type `σ` with feasible set `feasible`,
neighborhood relation `neighbors`, and `ℕ`-valued cost to be minimized. -/
@[ext]
structure LocalSearchProblem (σ : Type*) where
  /-- Set of feasible configurations. -/
  feasible : Set σ
  /-- Feasible neighbors reachable in one local step from a configuration. -/
  neighbors : σ → Set σ
  /-- Nonnegative integer cost objective to be minimized. -/
  cost : σ → ℕ
  /-- Every neighbor of a feasible configuration is feasible. -/
  neighbors_subset : ∀ s ∈ feasible, neighbors s ⊆ feasible

namespace LocalSearchProblem

variable {σ : Type*}

/-- Construct a `LocalSearchProblem` from a maximization objective `payoff : σ → ℕ` uniformly
bounded by `bound` on feasible configurations, via `cost s = bound - payoff s`. -/
@[expose]
def ofMax (feasible : Set σ) (neighbors : σ → Set σ)
    (neighbors_subset : ∀ s ∈ feasible, neighbors s ⊆ feasible)
    (bound : ℕ) (payoff : σ → ℕ) : LocalSearchProblem σ where
  feasible := feasible
  neighbors := neighbors
  cost s := bound - payoff s
  neighbors_subset := neighbors_subset

/-- A feasible configuration `s` is a local optimum of `P` if no neighbor has strictly lower
cost. -/
@[expose]
def IsLocalOpt (P : LocalSearchProblem σ) (s : σ) : Prop :=
  s ∈ P.feasible ∧ ∀ s' ∈ P.neighbors s, P.cost s ≤ P.cost s'

/-- A strictly cost-improving local step `s → s'` in `P`. -/
@[expose]
def IsImprovingStep (P : LocalSearchProblem σ) (s s' : σ) : Prop :=
  s ∈ P.feasible ∧ s' ∈ P.neighbors s ∧ P.cost s' < P.cost s

/-- The target of a strictly improving step is feasible. -/
theorem IsImprovingStep.right_mem {P : LocalSearchProblem σ} {s s' : σ}
    (h : P.IsImprovingStep s s') : s' ∈ P.feasible :=
  P.neighbors_subset s h.1 h.2.1

/-- Local optimality in `ofMax` coincides with payoff local maximality whenever `payoff ≤ bound`
on feasible configurations. -/
theorem ofMax_isLocalOpt_iff {feasible : Set σ} {neighbors : σ → Set σ}
    {hnbr : ∀ s ∈ feasible, neighbors s ⊆ feasible} {bound : ℕ} {payoff : σ → ℕ}
    (hbound : ∀ s ∈ feasible, payoff s ≤ bound) {s : σ} :
    (ofMax feasible neighbors hnbr bound payoff).IsLocalOpt s ↔
      s ∈ feasible ∧ ∀ s' ∈ neighbors s, payoff s' ≤ payoff s := by
  refine ⟨fun ⟨hs, h⟩ ↦ ⟨hs, fun s' hs' ↦ ?_⟩, fun ⟨hs, h⟩ ↦ ⟨hs, fun s' hs' ↦ ?_⟩⟩
  · have hle := h s' hs'
    have hb1 := hbound s hs
    have hb2 := hbound s' (hnbr s hs hs')
    dsimp only [ofMax] at hle; omega
  · have := h s' hs'; dsimp only [ofMax]; omega

/-- Improving steps in `ofMax` coincide with strictly payoff-increasing steps whenever
`payoff ≤ bound` on feasible configurations. -/
theorem ofMax_isImprovingStep_iff {feasible : Set σ} {neighbors : σ → Set σ}
    {hnbr : ∀ s ∈ feasible, neighbors s ⊆ feasible} {bound : ℕ} {payoff : σ → ℕ}
    (hbound : ∀ s ∈ feasible, payoff s ≤ bound) {s s' : σ} :
    (ofMax feasible neighbors hnbr bound payoff).IsImprovingStep s s' ↔
      s ∈ feasible ∧ s' ∈ neighbors s ∧ payoff s < payoff s' := by
  refine ⟨fun ⟨hs, hs', hlt⟩ ↦ ⟨hs, hs', ?_⟩, fun ⟨hs, hs', hlt⟩ ↦ ⟨hs, hs', ?_⟩⟩
  · have hb1 := hbound s hs
    have hb2 := hbound s' (hnbr s hs hs')
    dsimp only [ofMax] at hlt; omega
  · have hb1 := hbound s hs
    have hb2 := hbound s' (hnbr s hs hs')
    dsimp only [ofMax]; omega

/-- A nonempty list of configurations forming a directed path of strictly improving steps in `P`. -/
@[expose]
def IsImprovingPath (P : LocalSearchProblem σ) : List σ → Prop
  | [] => False
  | [s] => s ∈ P.feasible
  | s :: s' :: rest => P.IsImprovingStep s s' ∧ P.IsImprovingPath (s' :: rest)

/-- Every improving path is nonempty. -/
theorem IsImprovingPath.ne_nil {P : LocalSearchProblem σ} {L : List σ}
    (h : P.IsImprovingPath L) : L ≠ [] := by
  rintro rfl; exact h

/-- Every configuration visited along an improving path is feasible. -/
theorem IsImprovingPath.mem_feasible {P : LocalSearchProblem σ} :
    ∀ {L : List σ}, P.IsImprovingPath L → ∀ s ∈ L, s ∈ P.feasible
  | [], h, _, _ => h.elim
  | [_], h, _, hx => by rcases List.mem_singleton.mp hx with rfl; exact h
  | _ :: s' :: rest, ⟨hstep, hrest⟩, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hstep.1
    · exact hrest.mem_feasible x hx'

/-- Concatenation of two improving paths sharing their junction configuration. -/
theorem IsImprovingPath.append_cons {P : LocalSearchProblem σ} :
    ∀ {L₁ : List σ} {u : σ} {L₂ : List σ},
      P.IsImprovingPath (L₁ ++ [u]) → P.IsImprovingPath (u :: L₂) →
        P.IsImprovingPath (L₁ ++ u :: L₂)
  | [], _, _, _, h₂ => h₂
  | [_], _, _, h₁, h₂ => ⟨h₁.1, h₂⟩
  | _ :: s' :: rest, _, _, h₁, h₂ => ⟨h₁.1, append_cons (L₁ := s' :: rest) h₁.2 h₂⟩

/-- Prefix-suffix splitting of an improving path `L₁ ++ u :: L₂`. -/
theorem IsImprovingPath.split_at {P : LocalSearchProblem σ} :
    ∀ {L₁ : List σ} {u : σ} {L₂ : List σ},
      P.IsImprovingPath (L₁ ++ u :: L₂) →
        P.IsImprovingPath (L₁ ++ [u]) ∧ P.IsImprovingPath (u :: L₂)
  | [], u, _, h => ⟨h.mem_feasible u List.mem_cons_self, h⟩
  | [_], _, _, ⟨hstep, hrest⟩ => ⟨⟨hstep, hstep.right_mem⟩, hrest⟩
  | _ :: s' :: rest, _, _, ⟨hstep, hrest⟩ =>
    let ⟨ha, hb⟩ := hrest.split_at (L₁ := s' :: rest)
    ⟨⟨hstep, ha⟩, hb⟩

/-- The number of steps `L.length - 1` of an improving path is bounded by the starting cost. -/
theorem IsImprovingPath.length_le_cost_succ {P : LocalSearchProblem σ} :
    ∀ {L : List σ} (h : P.IsImprovingPath L), L.length ≤ P.cost (L.head h.ne_nil) + 1
  | [], h => h.elim
  | [_], _ => Nat.succ_le_succ (Nat.zero_le _)
  | _ :: _ :: _, ⟨hstep, hrest⟩ => by
    have ih := hrest.length_le_cost_succ
    have hlt := hstep.2.2
    simp only [List.length_cons, List.head_cons] at ih ⊢
    omega

/-- A maximal improving path is an improving path terminating at a local optimum of `P`. -/
@[expose]
def IsMaximalImprovingPath (P : LocalSearchProblem σ) (L : List σ) : Prop :=
  ∃ h : P.IsImprovingPath L, P.IsLocalOpt (L.getLast h.ne_nil)

/-- Every maximal improving path is nonempty. -/
theorem IsMaximalImprovingPath.ne_nil {P : LocalSearchProblem σ} {L : List σ}
    (h : P.IsMaximalImprovingPath L) : L ≠ [] :=
  h.elim fun hp _ ↦ hp.ne_nil

/-- From every feasible configuration `s₀`, there exists a maximal improving path starting at
`s₀`. -/
theorem exists_isMaximalImprovingPath (P : LocalSearchProblem σ) {s₀ : σ} (hs₀ : s₀ ∈ P.feasible) :
    ∃ (L : List σ) (h : P.IsMaximalImprovingPath L), L.head h.ne_nil = s₀ := by
  classical
  have haux : ∀ k : ℕ, ∀ s ∈ P.feasible, P.cost s ≤ k →
      ∃ (L : List σ) (h : P.IsMaximalImprovingPath L), L.head h.ne_nil = s := by
    intro k
    induction k with
    | zero =>
      intro s hs h0
      exact ⟨[s], ⟨hs, hs, fun s' _ ↦ by simp only [List.getLast_singleton]; omega⟩, rfl⟩
    | succ k ih =>
      intro s hs hle
      by_cases hopt : P.IsLocalOpt s
      · exact ⟨[s], ⟨hs, hopt⟩, rfl⟩
      · have hex : ∃ s' ∈ P.neighbors s, P.cost s' < P.cost s := by
          by_contra hno; apply hopt; refine ⟨hs, fun s' hs' ↦ ?_⟩
          by_contra hgt; exact hno ⟨s', hs', lt_of_not_ge hgt⟩
        obtain ⟨s', hs', hlt⟩ := hex
        obtain ⟨L, ⟨hpath, hlast⟩, hhead⟩ :=
          ih s' (P.neighbors_subset s hs hs') (by omega)
        cases L with
        | nil => exact hpath.elim
        | cons u rest =>
          have hus : u = s' := hhead
          subst hus
          refine ⟨s :: u :: rest, ⟨⟨⟨hs, hs', hlt⟩, hpath⟩, ?_⟩, rfl⟩
          simpa only [List.getLast_cons (List.cons_ne_nil u rest)] using hlast
  exact haux (P.cost s₀) s₀ hs₀ le_rfl

end LocalSearchProblem

/-- A tight local search reduction from `P` to `Q` in the sense of Schäffer and Yannakakis
: a set `reasonable` of feasible configurations of `Q` containing all local optima,
together with maps `lift : σ → τ` and `decode : τ → σ`, such that lifting followed by decoding is
the identity on `P.feasible`, local optima of `Q` decode to local optima of `P`, and every
`Q`-improving path between elements of `reasonable` whose internal vertices lie outside `reasonable`
decodes either to no change or to a single improving step in `P`.
-/
structure TightLocalReduction {σ τ : Type*}
    (P : LocalSearchProblem σ) (Q : LocalSearchProblem τ) where
  /-- Designated subset `R` of reasonable configurations of `Q`. -/
  reasonable : Set τ
  /-- Reasonable configurations are feasible in `Q`. -/
  reasonable_subset : reasonable ⊆ Q.feasible
  /-- Every local optimum of `Q` lies in `reasonable`. -/
  localOpt_mem_reasonable : ∀ t, Q.IsLocalOpt t → t ∈ reasonable
  /-- Lifting map embedding feasible configurations of `P` into `reasonable`. -/
  lift : σ → τ
  /-- Solution projection mapping configurations of `Q` back to `P`. -/
  decode : τ → σ
  /-- Every feasible configuration of `P` lifts into `reasonable`. -/
  lift_mem_reasonable : ∀ s ∈ P.feasible, lift s ∈ reasonable
  /-- Every reasonable configuration decodes to a feasible configuration of `P`. -/
  decode_mem_feasible : ∀ t ∈ reasonable, decode t ∈ P.feasible
  /-- `decode` is a left inverse to `lift` on `P.feasible`. -/
  decode_lift : ∀ s ∈ P.feasible, decode (lift s) = s
  /-- Every local optimum of `Q` decodes to a local optimum of `P`. -/
  decode_isLocalOpt : ∀ t, Q.IsLocalOpt t → P.IsLocalOpt (decode t)
  /-- Every improving path in `Q` between configurations in `reasonable` with no internal vertices
  in `reasonable` projects either to equality or to a single improving step of `P`. -/
  path_decode : ∀ t ∈ reasonable, ∀ (mid : List τ) (t' : τ),
    (∀ u ∈ mid, u ∉ reasonable) → t' ∈ reasonable →
    Q.IsImprovingPath (t :: (mid ++ [t'])) →
    decode t' = decode t ∨ P.IsImprovingStep (decode t) (decode t')

namespace TightLocalReduction

variable {σ τ υ : Type*}

/-- Build a `TightLocalReduction` when `reasonable` is forward-closed under `Q.IsImprovingStep`
(for example `reasonable = Q.feasible`), so no improving path leaves `reasonable` and single-step
projection suffices. -/
@[expose]
def ofClosed {P : LocalSearchProblem σ} {Q : LocalSearchProblem τ}
    (reasonable : Set τ) (hsub : reasonable ⊆ Q.feasible)
    (hclosed : ∀ t ∈ reasonable, ∀ t', Q.IsImprovingStep t t' → t' ∈ reasonable)
    (hopt_mem : ∀ t, Q.IsLocalOpt t → t ∈ reasonable)
    (lift : σ → τ) (decode : τ → σ)
    (hlift : ∀ s ∈ P.feasible, lift s ∈ reasonable)
    (hdec_feas : ∀ t ∈ reasonable, decode t ∈ P.feasible)
    (hdec_lift : ∀ s ∈ P.feasible, decode (lift s) = s)
    (hdec_opt : ∀ t, Q.IsLocalOpt t → P.IsLocalOpt (decode t))
    (hstep : ∀ t ∈ reasonable, ∀ t', Q.IsImprovingStep t t' →
      decode t' = decode t ∨ P.IsImprovingStep (decode t) (decode t')) :
    TightLocalReduction P Q where
  reasonable := reasonable
  reasonable_subset := hsub
  localOpt_mem_reasonable := hopt_mem
  lift := lift
  decode := decode
  lift_mem_reasonable := hlift
  decode_mem_feasible := hdec_feas
  decode_lift := hdec_lift
  decode_isLocalOpt := hdec_opt
  path_decode t ht mid t' hmid _ hpath := by
    cases mid with
    | nil => exact hstep t ht t' hpath.1
    | cons u rest => exact (hmid u List.mem_cons_self (hclosed t ht u hpath.1)).elim

/-- Identity tight local search reduction. -/
def refl (P : LocalSearchProblem σ) : TightLocalReduction P P :=
  ofClosed P.feasible Set.Subset.rfl (fun _ _ _ h ↦ h.right_mem) (fun _ h ↦ h.1) id id
    (fun _ h ↦ h) (fun _ h ↦ h) (fun _ _ ↦ rfl) (fun _ h ↦ h) (fun _ _ _ h ↦ Or.inr h)

private lemma split_first_mem {α : Type*} (R : Set α) :
    ∀ (xs : List α) (y : α), y ∈ R →
      ∃ (pre suff : List α) (z : α),
        xs ++ [y] = pre ++ z :: suff ∧ z ∈ R ∧ ∀ u ∈ pre, u ∉ R
  | [], y, hy => ⟨[], [], y, rfl, hy, fun _ h ↦ (List.not_mem_nil h).elim⟩
  | x :: xs, y, hy => by
    classical
    by_cases hx : x ∈ R
    · exact ⟨[], xs ++ [y], x, rfl, hx, fun _ h ↦ (List.not_mem_nil h).elim⟩
    · obtain ⟨pre, suff, z, heq, hz, hpre⟩ := split_first_mem R xs y hy
      refine ⟨x :: pre, suff, z, by simp only [List.cons_append, heq], hz, fun u hu ↦ ?_⟩
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact hx
      · exact hpre u hu'

/-- Every `Q`-improving path from `t ∈ r.reasonable` to `t' ∈ r.reasonable` compresses under
`r.decode` to a `P`-improving path from `r.decode t` to `r.decode t'` of no greater length
(and with all internal vertices decoded from internal `r.reasonable` vertices). -/
theorem compress_improvingPath {P : LocalSearchProblem σ} {Q : LocalSearchProblem τ}
    (r : TightLocalReduction P Q) {t t' : τ} (ht : t ∈ r.reasonable) (ht' : t' ∈ r.reasonable)
    {rest : List τ} (hpath : Q.IsImprovingPath (t :: (rest ++ [t']))) :
    ∃ (L : List σ) (hL : P.IsImprovingPath L),
      L.head hL.ne_nil = r.decode t ∧ L.getLast hL.ne_nil = r.decode t' ∧
      L.length ≤ rest.length + 2 ∧
      ∀ s ∈ L, s = r.decode t ∨ s = r.decode t' ∨
        ∃ u ∈ rest, u ∈ r.reasonable ∧ s = r.decode u := by
  have hgen : ∀ (n : ℕ) (a : τ) (xs : List τ), xs.length ≤ n → a ∈ r.reasonable →
      Q.IsImprovingPath (a :: (xs ++ [t'])) →
      ∃ (L : List σ) (hL : P.IsImprovingPath L),
        L.head hL.ne_nil = r.decode a ∧ L.getLast hL.ne_nil = r.decode t' ∧
        L.length ≤ xs.length + 2 ∧
        ∀ s ∈ L, s = r.decode a ∨ s = r.decode t' ∨
          ∃ u ∈ xs, u ∈ r.reasonable ∧ s = r.decode u := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro a xs hlen ha hp
      obtain ⟨pre, suff, z, heq, hz, hpre⟩ := split_first_mem r.reasonable xs t' ht'
      have hp' : Q.IsImprovingPath ((a :: pre) ++ z :: suff) := by
        simpa only [List.cons_append, ← heq] using hp
      obtain ⟨hp1, hp2⟩ := hp'.split_at (L₁ := a :: pre)
      have hstep := r.path_decode a ha pre z hpre hz hp1
      cases suff with
      | nil =>
        have hzt : z = t' := by
          have := congrArg (fun l ↦ l.getLast?) heq
          simpa only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
            List.getLast?_singleton, Option.some.injEq] using this.symm
        subst hzt
        rcases hstep with hsame | himp
        · refine ⟨[r.decode a], r.decode_mem_feasible a ha, rfl, hsame.symm, by simp,
            fun s hs ↦ Or.inl (List.mem_singleton.mp hs)⟩
        · refine ⟨[r.decode a, r.decode z], ⟨himp, r.decode_mem_feasible z hz⟩,
            rfl, rfl, by simp, fun s hs ↦ ?_⟩
          rcases List.mem_cons.mp hs with rfl | hs'
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (List.mem_singleton.mp hs'))
      | cons w ws =>
        have hdrop : (w :: ws) = (w :: ws).dropLast ++ [t'] := by
          have hlast : (w :: ws).getLast (List.cons_ne_nil w ws) = t' := by
            have h1 := congrArg (fun l ↦ l.getLast?) heq
            simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
              List.getLast?_singleton, List.getLast?_cons_cons] at h1
            have h2 := List.getLast?_eq_some_getLast (List.cons_ne_nil w ws)
            exact Option.some.inj (h2.symm.trans h1.symm)
          rw [← hlast, List.dropLast_append_getLast (List.cons_ne_nil w ws)]
        let ys := (w :: ws).dropLast
        have hlen_eq : xs.length + 1 = pre.length + 1 + (ys.length + 1) := by
          have := congrArg List.length heq
          have hw := congrArg List.length hdrop
          simp only [List.length_append, List.length_cons, List.length_nil] at this hw
          dsimp only [ys] at hw ⊢; omega
        have hp2' : Q.IsImprovingPath (z :: (ys ++ [t'])) := by rwa [← hdrop]
        obtain ⟨L₂, hL₂, hhead₂, hlast₂, hlen₂, hmem₂⟩ :=
          ih ys.length (by omega) z ys le_rfl hz hp2'
        have hsub : pre ++ [z] ++ ys = xs := by
          have hcat : (pre ++ [z] ++ ys) ++ [t'] = xs ++ [t'] := by
            calc (pre ++ [z] ++ ys) ++ [t']
                = pre ++ (z :: (ys ++ [t'])) := by simp [List.append_assoc]
              _ = pre ++ (z :: w :: ws) := by dsimp only [ys]; rw [← hdrop]
              _ = xs ++ [t'] := heq.symm
          exact List.append_inj_left' hcat rfl
        have hz_in_xs : z ∈ xs := by rw [← hsub]; simp
        have hys_sub : ∀ u ∈ ys, u ∈ xs := fun u hu ↦ by rw [← hsub]; simp [hu]
        rcases hstep with hsame | himp
        · refine ⟨L₂, hL₂, hhead₂.trans hsame, hlast₂, by omega, fun s hs ↦ ?_⟩
          rcases hmem₂ s hs with rfl | rfl | ⟨u, hu, hur, rfl⟩
          · exact Or.inl hsame
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr ⟨u, hys_sub u hu, hur, rfl⟩)
        · cases L₂ with
          | nil => exact hL₂.elim
          | cons b bs =>
            simp only [List.head_cons] at hhead₂; subst hhead₂
            refine ⟨r.decode a :: r.decode z :: bs, ⟨himp, hL₂⟩, rfl,
              by simpa only [List.getLast_cons (List.cons_ne_nil _ bs)] using hlast₂,
              by simp only [List.length_cons] at hlen₂ ⊢; omega, fun s hs ↦ ?_⟩
            rcases List.mem_cons.mp hs with rfl | hs'
            · exact Or.inl rfl
            · rcases hmem₂ s hs' with rfl | rfl | ⟨u, hu, hur, rfl⟩
              · exact Or.inr (Or.inr ⟨z, hz_in_xs, hz, rfl⟩)
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr ⟨u, hys_sub u hu, hur, rfl⟩)
  exact hgen rest.length t rest le_rfl ht hpath

/-- Tight local search reductions compose. -/
def trans {P : LocalSearchProblem σ} {Q : LocalSearchProblem τ} {R : LocalSearchProblem υ}
    (r₁ : TightLocalReduction P Q) (r₂ : TightLocalReduction Q R) :
    TightLocalReduction P R where
  reasonable := {w ∈ r₂.reasonable | r₂.decode w ∈ r₁.reasonable}
  reasonable_subset _ hw := r₂.reasonable_subset hw.1
  localOpt_mem_reasonable w hw :=
    ⟨r₂.localOpt_mem_reasonable w hw, r₁.localOpt_mem_reasonable _ (r₂.decode_isLocalOpt w hw)⟩
  lift s := r₂.lift (r₁.lift s)
  decode w := r₁.decode (r₂.decode w)
  lift_mem_reasonable s hs := by
    have h1 := r₁.lift_mem_reasonable s hs
    have h1f := r₁.reasonable_subset h1
    exact ⟨r₂.lift_mem_reasonable _ h1f, (r₂.decode_lift _ h1f).symm ▸ h1⟩
  decode_mem_feasible _ hw := r₁.decode_mem_feasible _ hw.2
  decode_lift s hs := by
    rw [r₂.decode_lift _ (r₁.reasonable_subset (r₁.lift_mem_reasonable s hs)), r₁.decode_lift s hs]
  decode_isLocalOpt w hw := r₁.decode_isLocalOpt _ (r₂.decode_isLocalOpt w hw)
  path_decode w hw mid w' hmid hw' hpath := by
    obtain ⟨L, hL, hhead, hlast, _, hmem⟩ := r₂.compress_improvingPath hw.1 hw'.1 hpath
    cases L with
    | nil => exact hL.elim
    | cons q₀ qs =>
      simp only [List.head_cons] at hhead
      cases qs with
      | nil =>
        simp only [List.getLast_singleton] at hlast
        exact Or.inl (congrArg r₁.decode (hlast.symm.trans hhead))
      | cons q₁ qr =>
        let qmid := (q₁ :: qr).dropLast
        have hlast_eq : (q₁ :: qr).getLast (List.cons_ne_nil q₁ qr) = r₂.decode w' := by
          simpa only [List.getLast_cons (List.cons_ne_nil q₁ qr)] using hlast
        have hqeq : q₀ :: q₁ :: qr = r₂.decode w :: (qmid ++ [r₂.decode w']) := by
          rw [hhead, ← hlast_eq, List.dropLast_append_getLast (List.cons_ne_nil q₁ qr)]
        have hL' : Q.IsImprovingPath (r₂.decode w :: (qmid ++ [r₂.decode w'])) := hqeq ▸ hL
        have hcost_lt : ∀ x ∈ qmid,
            Q.cost (r₂.decode w') < Q.cost x ∧ Q.cost x < Q.cost (r₂.decode w) := by
          intro x hx
          obtain ⟨pre, suff, hsplit⟩ := List.append_of_mem hx
          have hfull : Q.IsImprovingPath
              ((r₂.decode w :: pre) ++ x :: (suff ++ [r₂.decode w'])) := by
            simpa only [hsplit, List.cons_append, List.append_assoc] using hL'
          have hstrict : ∀ {a b : τ} {ms : List τ},
              Q.IsImprovingPath (a :: (ms ++ [b])) → Q.cost b < Q.cost a := by
            intro a b ms; induction ms generalizing a with
            | nil => intro h; exact h.1.2.2
            | cons m ms ih => intro h; exact (ih h.2).trans h.1.2.2
          obtain ⟨hp_left, hp_right⟩ := hfull.split_at (L₁ := r₂.decode w :: pre)
          exact ⟨hstrict hp_right, hstrict hp_left⟩
        have hqmid : ∀ x ∈ qmid, x ∉ r₁.reasonable := by
          intro x hx hxr
          have hxL : x ∈ q₀ :: q₁ :: qr := by rw [hqeq]; simp [hx]
          rcases hmem x hxL with h1 | h2 | ⟨u, hu, hur, rfl⟩
          · exact (h1 ▸ (hcost_lt x hx).2).false
          · exact (h2 ▸ (hcost_lt x hx).1).false
          · exact hmid u hu ⟨hur, hxr⟩
        exact r₁.path_decode _ hw.2 qmid _ hqmid hw'.2 hL'

/-- **Worst-case path-length transfer along tight reductions**
: if every maximal improving path in `P` starting at `s₀ ∈ P.feasible` has length at
least `B`, then every maximal improving path in `Q` starting at `r.lift s₀` also has length at
least `B` (under every pivoting rule).
-/
theorem length_ge_of_forall_maximal {P : LocalSearchProblem σ} {Q : LocalSearchProblem τ}
    (r : TightLocalReduction P Q) {s₀ : σ} (hs₀ : s₀ ∈ P.feasible) {B : ℕ}
    (hlow : ∀ (L : List σ) (hL : P.IsMaximalImprovingPath L),
      L.head hL.ne_nil = s₀ → B ≤ L.length)
    (M : List τ) (hM : Q.IsMaximalImprovingPath M)
    (hstart : M.head hM.ne_nil = r.lift s₀) :
    B ≤ M.length := by
  rcases hM with ⟨hMpath, hMopt⟩
  cases M with
  | nil => exact hMpath.elim
  | cons t₀ ts =>
    simp only [List.head_cons] at hstart
    cases ts with
    | nil =>
      simp only [List.getLast_singleton] at hMopt
      have hPopt : P.IsLocalOpt s₀ := by
        simpa only [hstart, r.decode_lift s₀ hs₀] using r.decode_isLocalOpt t₀ hMopt
      exact hlow [s₀] ⟨hs₀, hPopt⟩ rfl
    | cons t₁ tr =>
      let tend := (t₁ :: tr).getLast (List.cons_ne_nil t₁ tr)
      let rest := (t₁ :: tr).dropLast
      have hopt_end : Q.IsLocalOpt tend := by
        simpa only [List.getLast_cons (List.cons_ne_nil t₁ tr)] using hMopt
      have hMeq : t₀ :: t₁ :: tr = r.lift s₀ :: (rest ++ [tend]) := by
        rw [hstart, List.dropLast_append_getLast (List.cons_ne_nil t₁ tr)]
      obtain ⟨L, hL, hhead, hlast, hlen, _⟩ :=
        r.compress_improvingPath (r.lift_mem_reasonable s₀ hs₀)
          (r.localOpt_mem_reasonable tend hopt_end) (hMeq ▸ hMpath)
      rw [r.decode_lift s₀ hs₀] at hhead
      have hLmax : P.IsMaximalImprovingPath L :=
        ⟨hL, hlast.symm ▸ r.decode_isLocalOpt tend hopt_end⟩
      have hMlen : (t₀ :: t₁ :: tr).length = rest.length + 2 := by
        have := congrArg List.length hMeq
        simp only [List.length_cons, List.length_append, List.length_nil] at this; omega
      exact (hlow L hLmax hhead).trans (hMlen ▸ hlen)

end TightLocalReduction

end TightReductions

/-! ### 2. Explicitly Encoded `LocalMaxCut` and Bounded-Degree `LocalMaxCutDeg` -/

section LocalMaxCutPLS

/-- An explicitly encoded edge-weighted undirected graph with `numVertices` vertices `0, ..., n - 1`
and edge list `edges` of triples `((u, v), w)` carrying binary natural weights `w : ℕ`. -/
@[ext]
structure WeightedGraphCode : Type where
  /-- Number of vertices `n`. -/
  numVertices : ℕ
  /-- List of weighted edges `((u, v), w)`. -/
  edges : List ((ℕ × ℕ) × ℕ)
  deriving DecidableEq

/-- Canonical polynomial-time bit-string encoding of `WeightedGraphCode`: vertex indices and count
in unary, edge weights in binary. -/
enc_structure encWeightedGraph : WeightedGraphCode where
  numVertices : encUnary,
  edges : (encList (encPair (encPair encUnary encUnary) encNat))

attribute [fun_prop] encWeightedGraph_numVertices_polyTime encWeightedGraph_edges_polyTime
  encWeightedGraph_mk_polyTime

namespace WeightedGraphCode

/-- Whether edge `e = ((u, v), w)` crosses the cut represented by bit string `x`. -/
@[expose] def edgeInCut (x : List Bool) (e : (ℕ × ℕ) × ℕ) : Bool :=
  x.getD e.1.1 false != x.getD e.1.2 false

/-- Cut weight of a partition bit string `x`: total weight of edges crossing the cut. -/
@[expose] def cutWeight (g : WeightedGraphCode) (x : List Bool) : ℕ :=
  (g.edges.map fun e ↦ if edgeInCut x e then e.2 else 0).sum

/-- Total weight of all edges in `g`. -/
@[expose] def totalWeight (g : WeightedGraphCode) : ℕ :=
  (g.edges.map Prod.snd).sum

/-- Every cut has weight at most `g.totalWeight`. -/
theorem cutWeight_le_totalWeight (g : WeightedGraphCode) (x : List Bool) :
    g.cutWeight x ≤ g.totalWeight := by
  unfold cutWeight totalWeight
  induction g.edges with
  | nil => exact le_rfl
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons]
    split_ifs <;> omega

/-- Minimization cost `totalWeight - cutWeight x` dual to `cutWeight`. -/
@[expose] def uncutWeight (g : WeightedGraphCode) (x : List Bool) : ℕ :=
  g.totalWeight - g.cutWeight x

/-- Flip bit `i` of a bit string normalized to length `n`. -/
@[expose] def flipBit (n : ℕ) (x : List Bool) (i : ℕ) : List Bool :=
  (List.range n).map fun j ↦ if j = i then !(x.getD j false) else x.getD j false

/-- `flipBit n x i` always has length `n`. -/
@[simp]
theorem length_flipBit (n : ℕ) (x : List Bool) (i : ℕ) : (flipBit n x i).length = n := by
  simp only [flipBit, List.length_map, List.length_range]

/-- Bit lookup in `flipBit n x i` at an in-range index `j < n`. -/
theorem getD_flipBit_of_lt {n : ℕ} (x : List Bool) (i : ℕ) {j : ℕ} (hj : j < n) :
    (flipBit n x i).getD j false = if j = i then !(x.getD j false) else x.getD j false := by
  simp only [flipBit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]

/-- Whether flipping vertex `i` strictly increases the cut weight of `x`. -/
def improvingFlip (g : WeightedGraphCode) (x : List Bool) (i : ℕ) : Bool :=
  decide (g.cutWeight x < g.cutWeight (flipBit g.numVertices x i))

/-- Deterministic local-search step for `LocalMaxCut`: flip the first strictly improving vertex,
or stay at `x` if `x` is locally optimal. -/
def flipStep (g : WeightedGraphCode) (x : List Bool) : List Bool :=
  ((List.range g.numVertices).find? (g.improvingFlip x)).elim x (flipBit g.numVertices x)

/-- `flipStep` preserves bit strings of length `g.numVertices`. -/
theorem length_flipStep (g : WeightedGraphCode) {x : List Bool} (hx : x.length = g.numVertices) :
    (g.flipStep x).length = g.numVertices := by
  unfold flipStep
  cases (List.range g.numVertices).find? (g.improvingFlip x) with
  | none => exact hx
  | some i => exact length_flipBit g.numVertices x i

/-- Number of edges in `g.edges` incident to vertex `v`. -/
@[expose] def vertexDegree (g : WeightedGraphCode) (v : ℕ) : ℕ :=
  g.edges.countP fun e ↦ decide (e.1.1 = v) || decide (e.1.2 = v)

/-- Check that `g` encodes a simple undirected graph: all edges satisfy `u < v < numVertices` and
no undirected pair `{u, v}` is repeated. -/
@[expose] def isSimpleGraph (g : WeightedGraphCode) : Bool :=
  (g.edges.all fun e ↦ decide (e.1.1 < e.1.2) && decide (e.1.2 < g.numVertices)) &&
    ((g.edges.zipIdx).all fun p ↦ (g.edges.zipIdx).all fun q ↦
      decide (p.2 = q.2) || !(decide (p.1.1.1 = q.1.1.1) && decide (p.1.1.2 = q.1.1.2)))

/-- `g.isSimpleGraph = true` iff all edges satisfy `u < v < numVertices` and
`(g.edges.map Prod.fst).Nodup`. -/
theorem isSimpleGraph_eq_true_iff (g : WeightedGraphCode) :
    g.isSimpleGraph = true ↔
      (∀ e ∈ g.edges, e.1.1 < e.1.2 ∧ e.1.2 < g.numVertices) ∧
        (g.edges.map Prod.fst).Nodup := by
  simp only [isSimpleGraph, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  refine and_congr_right fun _ ↦ ?_
  rw [List.nodup_iff_getElem?_ne_getElem?]
  constructor
  · intro h i j hij hj
    simp only [List.length_map] at hj
    have hi : i < g.edges.length := hij.trans hj
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.map_some, ne_eq, Option.some.injEq, Prod.ext_iff, not_and_or]
    have hmem_i : (g.edges[i], i) ∈ g.edges.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr
      (List.getElem?_eq_getElem hi)
    have hmem_j : (g.edges[j], j) ∈ g.edges.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr
      (List.getElem?_eq_getElem hj)
    rcases h _ hmem_i _ hmem_j with heq | hne
    · omega
    · exact hne
  · intro h p hp q hq
    have hpi := List.mk_mem_zipIdx_iff_getElem?.mp hp
    have hqi := List.mk_mem_zipIdx_iff_getElem?.mp hq
    rcases lt_trichotomy p.2 q.2 with hlt | heq | hgt
    · right
      have hqlen : q.2 < (g.edges.map Prod.fst).length := by
        rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hqi).1
      have hne := h p.2 q.2 hlt hqlen
      simp only [List.getElem?_map, hpi, hqi, Option.map_some, ne_eq, Option.some.injEq,
        Prod.ext_iff, not_and_or] at hne
      exact hne
    · exact Or.inl heq
    · right
      have hplen : p.2 < (g.edges.map Prod.fst).length := by
        rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hpi).1
      have hne := h q.2 p.2 hgt hplen
      simp only [List.getElem?_map, hpi, hqi, Option.map_some, ne_eq, Option.some.injEq,
        Prod.ext_iff] at hne
      by_cases h1 : p.1.1.1 = q.1.1.1
      · exact Or.inr fun h2 ↦ hne ⟨h1.symm, h2.symm⟩
      · exact Or.inl h1

/-- Check that `g` is a simple graph of maximum vertex degree at most `d`. -/
@[expose] def isSimpleDegLe (d : ℕ) (g : WeightedGraphCode) : Bool :=
  g.isSimpleGraph && (List.range g.numVertices).all fun v ↦ decide (g.vertexDegree v ≤ d)

/-- Logical characterization of `isSimpleDegLe d g = true`. -/
theorem isSimpleDegLe_eq_true_iff {d : ℕ} {g : WeightedGraphCode} :
    g.isSimpleDegLe d = true ↔
      (∀ e ∈ g.edges, e.1.1 < e.1.2 ∧ e.1.2 < g.numVertices) ∧
      (g.edges.map Prod.fst).Nodup ∧
      ∀ v < g.numVertices, g.vertexDegree v ≤ d := by
  simp only [isSimpleDegLe, Bool.and_eq_true, isSimpleGraph_eq_true_iff, List.all_eq_true,
    List.mem_range, decide_eq_true_eq, and_assoc]

/-- Monotonicity of `isSimpleDegLe` in the degree bound `d`. -/
theorem isSimpleDegLe_mono {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) {g : WeightedGraphCode}
    (hg : g.isSimpleDegLe d₁ = true) : g.isSimpleDegLe d₂ = true := by
  rcases isSimpleDegLe_eq_true_iff.mp hg with ⟨h1, h2, h3⟩
  exact isSimpleDegLe_eq_true_iff.mpr ⟨h1, h2, fun v hv ↦ (h3 v hv).trans hd⟩

/-- Discrete local search problem associated with `g : WeightedGraphCode`. -/
@[expose] def toLocalSearchProblem (g : WeightedGraphCode) : LocalSearchProblem (List Bool) :=
  LocalSearchProblem.ofMax
    {x | x.length = g.numVertices}
    (fun x ↦ {y | ∃ i < g.numVertices, y = flipBit g.numVertices x i})
    (fun _ _ _ ⟨i, _, hy⟩ ↦ hy ▸ length_flipBit g.numVertices _ i)
    g.totalWeight
    g.cutWeight

section PolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

private theorem cond_pt {α : Type} {encA : α ↪ List Bool} {c : γ → Bool} {t f : γ → α}
    (hc : ComputableInPolyTime c encIn encBool)
    (ht : ComputableInPolyTime t encIn encA)
    (hf : ComputableInPolyTime f encIn encA) :
    ComputableInPolyTime (fun x ↦ if c x then t x else f x) encIn encA :=
  hc.ite ht hf

attribute [local fun_prop] bool_and' bool_or' cond_pt binary_le' binary_lt'

@[fun_prop]
private theorem cutWeight_pt {g : γ → WeightedGraphCode} {x : γ → List Bool}
    (hg : ComputableInPolyTime g encIn encWeightedGraph)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime (fun a ↦ (g a).cutWeight (x a)) encIn encNat := by
  unfold cutWeight edgeInCut; fun_prop

@[fun_prop]
private theorem totalWeight_pt {g : γ → WeightedGraphCode}
    (hg : ComputableInPolyTime g encIn encWeightedGraph) :
    ComputableInPolyTime (fun a ↦ (g a).totalWeight) encIn encNat := by
  unfold totalWeight; fun_prop

@[fun_prop]
private theorem uncutWeight_pt {g : γ → WeightedGraphCode} {x : γ → List Bool}
    (hg : ComputableInPolyTime g encIn encWeightedGraph)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime (fun a ↦ (g a).uncutWeight (x a)) encIn encNat := by
  unfold uncutWeight; fun_prop

@[fun_prop]
private theorem flipBit_pt {n i : γ → ℕ} {x : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hx : ComputableInPolyTime x encIn encBits)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun a ↦ flipBit (n a) (x a) (i a)) encIn encBits := by
  unfold flipBit
  refine listToBits.comp ?_
  fun_prop

@[fun_prop]
private theorem improvingFlip_pt {g : γ → WeightedGraphCode} {x : γ → List Bool} {i : γ → ℕ}
    (hg : ComputableInPolyTime g encIn encWeightedGraph)
    (hx : ComputableInPolyTime x encIn encBits)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun a ↦ (g a).improvingFlip (x a) (i a)) encIn encBool := by
  unfold improvingFlip; fun_prop

/-- `flipStep` is computable in polynomial time. -/
theorem flipStep_polyTime :
    ComputableInPolyTime (fun p : WeightedGraphCode × List Bool ↦ p.1.flipStep p.2)
      (encPair encWeightedGraph encBits) encBits := by
  unfold flipStep; fun_prop

/-- `uncutWeight` is computable in polynomial time. -/
theorem uncutWeight_polyTime :
    ComputableInPolyTime (fun p : WeightedGraphCode × List Bool ↦ p.1.uncutWeight p.2)
      (encPair encWeightedGraph encBits) encNat := by
  fun_prop

/-- `cutWeight` is computable in polynomial time. -/
theorem cutWeight_polyTime :
    ComputableInPolyTime (fun p : WeightedGraphCode × List Bool ↦ p.1.cutWeight p.2)
      (encPair encWeightedGraph encBits) encNat := by
  fun_prop

end PolyTime

end WeightedGraphCode

/-- The **`LocalMaxCut`** search problem: given an edge-weighted graph `g`, find a partition bit
string `x` of length `g.numVertices` whose cut weight cannot be strictly increased by flipping any
single vertex. -/
@[expose] def LocalMaxCut (g : WeightedGraphCode) (x : List Bool) : Prop :=
  x.length = g.numVertices ∧
    ∀ i < g.numVertices, g.cutWeight (WeightedGraphCode.flipBit g.numVertices x i) ≤ g.cutWeight x

/-- `LocalMaxCut g x` coincides with local optimality in `g.toLocalSearchProblem`. -/
theorem toLocalSearchProblem_isLocalOpt_iff (g : WeightedGraphCode) (x : List Bool) :
    g.toLocalSearchProblem.IsLocalOpt x ↔ LocalMaxCut g x :=
  (LocalSearchProblem.ofMax_isLocalOpt_iff (fun y _ ↦ g.cutWeight_le_totalWeight y)).trans
    ⟨fun ⟨hx, h⟩ ↦ ⟨hx, fun i hi ↦ h _ ⟨i, hi, rfl⟩⟩,
     fun ⟨hx, h⟩ ↦ ⟨hx, fun _ ⟨i, hi, heq⟩ ↦ heq ▸ h i hi⟩⟩

/-- `LocalMaxCut` coincides with `Cslib.Complexity.localOptRel` for `flipStep` and `uncutWeight`. -/
theorem localMaxCut_eq_localOptRel :
    LocalMaxCut = localOptRel WeightedGraphCode.numVertices
      (fun p : WeightedGraphCode × List Bool ↦ p.1.flipStep p.2)
      (fun p ↦ p.1.uncutWeight p.2) := by
  funext g x
  apply propext
  simp only [LocalMaxCut, localOptRel]
  refine and_congr_right fun _ ↦ ?_
  unfold WeightedGraphCode.flipStep
  cases hf : (List.range g.numVertices).find? (g.improvingFlip x) with
  | none =>
    simp only [Option.elim, le_refl, iff_true]
    intro i hi
    have hnone := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
    simpa only [WeightedGraphCode.improvingFlip, decide_eq_true_eq, not_lt] using hnone
  | some i =>
    have hi : i < g.numVertices := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    have himp : g.cutWeight x < g.cutWeight (WeightedGraphCode.flipBit g.numVertices x i) := by
      simpa only [WeightedGraphCode.improvingFlip, decide_eq_true_eq] using List.find?_some hf
    have hb1 := g.cutWeight_le_totalWeight x
    have hb2 := g.cutWeight_le_totalWeight (WeightedGraphCode.flipBit g.numVertices x i)
    simp only [Option.elim, WeightedGraphCode.uncutWeight]
    exact ⟨fun h ↦ absurd (h i hi) (not_le.mpr himp), fun h ↦ by omega⟩

/-- **`LocalMaxCut` is in `PLS`**. -/
theorem localMaxCut_mem_PLS : LocalMaxCut ∈ PLS encWeightedGraph := by
  rw [localMaxCut_eq_localOptRel]
  exact localOptRel_mem_PLS (by fun_prop) WeightedGraphCode.flipStep_polyTime
    WeightedGraphCode.uncutWeight_polyTime fun g _ hx ↦ g.length_flipStep hx

/-- `LocalMaxCut` is a total search problem. -/
theorem isTotalSearch_localMaxCut : IsTotalSearch LocalMaxCut :=
  (PLS_subset_TFNP localMaxCut_mem_PLS).2

/-- Simple edge-weighted graphs of maximum degree at most `d`. -/
abbrev WeightedGraphDeg (d : ℕ) : Type :=
  {g : WeightedGraphCode // g.isSimpleDegLe d = true}

/-- Canonical bit-string encoding of `WeightedGraphDeg d`, inheriting `encWeightedGraph`. -/
@[expose] def encWeightedGraphDeg (d : ℕ) : WeightedGraphDeg d ↪ List Bool where
  toFun g := encWeightedGraph g.1
  inj' _ _ h := Subtype.ext (encWeightedGraph.injective h)

/-- Forgetful inclusion `WeightedGraphDeg d → WeightedGraphCode` is polynomial-time. -/
@[fun_prop]
theorem weightedGraphDeg_val_polyTime (d : ℕ) :
    ComputableInPolyTime Subtype.val (encWeightedGraphDeg d) encWeightedGraph :=
  ComputableInPolyTime.id'.of_enc_eq fun _ ↦ rfl

/-- The **`LocalMaxCutDeg d`** search problem: `LocalMaxCut` restricted to simple weighted graphs
of maximum degree at most `d`. -/
@[expose] def LocalMaxCutDeg (d : ℕ) (g : WeightedGraphDeg d) (x : List Bool) : Prop :=
  LocalMaxCut g.1 x

/-- `LocalMaxCutDeg d` reduces in polynomial time to `LocalMaxCut`. -/
theorem localMaxCutDeg_searchReducible_localMaxCut (d : ℕ) :
    SearchReducible (encWeightedGraphDeg d) encWeightedGraph (LocalMaxCutDeg d) LocalMaxCut :=
  SearchReducible.of_isTotalSearch isTotalSearch_localMaxCut (weightedGraphDeg_val_polyTime d)
    (.snd (encWeightedGraphDeg d) encBits) fun _ _ h ↦ h

/-- **`LocalMaxCutDeg d` is in `PLS`** for every degree bound `d : ℕ`. -/
theorem localMaxCutDeg_mem_PLS (d : ℕ) : LocalMaxCutDeg d ∈ PLS (encWeightedGraphDeg d) := by
  have hred := localMaxCutDeg_searchReducible_localMaxCut d
  obtain ⟨⟨p, hp⟩, V, hV, hiff⟩ := mem_FNP.mp (PLS_subset_TFNP localMaxCut_mem_PLS).1
  have hpair : ComputableInPolyTime
      (fun q : WeightedGraphDeg d × List Bool ↦ (q.1.1, q.2))
      (encPair (encWeightedGraphDeg d) encBits) (encPair encWeightedGraph encBits) :=
    ((weightedGraphDeg_val_polyTime d).comp (fst _ encBits)).pair (snd _ encBits)
  have hfnp : LocalMaxCutDeg d ∈ FNP (encWeightedGraphDeg d) :=
    mem_FNP.mpr ⟨⟨p, fun g x h ↦ hp g.1 x h⟩, fun q ↦ V (q.1.1, q.2),
      hV.comp hpair, fun g x ↦ hiff g.1 x⟩
  exact hred.mem_PLS hfnp localMaxCut_mem_PLS

/-- `LocalMaxCutDeg d` is a total search problem for every `d : ℕ`. -/
theorem isTotalSearch_localMaxCutDeg (d : ℕ) : IsTotalSearch (LocalMaxCutDeg d) :=
  (PLS_subset_TFNP (localMaxCutDeg_mem_PLS d)).2

/-- `LocalMaxCutDeg d₁` reduces in polynomial time to `LocalMaxCutDeg d₂` whenever `d₁ ≤ d₂`. -/
theorem localMaxCutDeg_searchReducible_mono {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) :
    SearchReducible (encWeightedGraphDeg d₁) (encWeightedGraphDeg d₂)
      (LocalMaxCutDeg d₁) (LocalMaxCutDeg d₂) :=
  SearchReducible.of_isTotalSearch (isTotalSearch_localMaxCutDeg d₂)
    (f := fun g ↦ ⟨g.1, g.1.isSimpleDegLe_mono hd g.2⟩)
    (ComputableInPolyTime.id'.of_enc_eq fun _ ↦ rfl)
    (.snd (encWeightedGraphDeg d₁) encBits) fun _ _ h ↦ h

/-- **Base case `d = 0`**: `LocalMaxCutDeg 0` lies in `FPSearch` (every graph of maximum degree `0`
has no edges, so the all-`false` string is immediately a local max-cut). -/
theorem localMaxCutDeg_zero_mem_FPSearch :
    LocalMaxCutDeg 0 ∈ FPSearch (encWeightedGraphDeg 0) := by
  refine mem_FPSearch_of_total (PLS_subset_TFNP (localMaxCutDeg_mem_PLS 0)).1
    (g := fun g ↦ List.replicate g.1.numVertices false)
    ((bitsReplicate false).comp (by fun_prop)) fun g ↦ ?_
  rcases WeightedGraphCode.isSimpleDegLe_eq_true_iff.mp g.2 with ⟨hrange, _, hdeg⟩
  have hemp : g.1.edges = [] := by
    cases he : g.1.edges with
    | nil => rfl
    | cons e es =>
      have he_mem : e ∈ g.1.edges := by simp [he]
      have hv : e.1.1 < g.1.numVertices := (hrange e he_mem).1.trans (hrange e he_mem).2
      have h0 := hdeg e.1.1 hv
      simp only [WeightedGraphCode.vertexDegree, he, List.countP_cons, decide_true, Bool.true_or,
        ↓reduceIte] at h0
      omega
  refine ⟨List.length_replicate, fun _ _ ↦ ?_⟩
  simp only [WeightedGraphCode.cutWeight, hemp, List.map_nil, List.sum_nil, le_refl]

private def matchingCut (g : WeightedGraphCode) : List Bool :=
  (List.range g.numVertices).map fun v ↦ g.edges.any fun e ↦ decide (e.1.2 = v)

/-- **Base case `d = 1`**: `LocalMaxCutDeg 1` lies in `FPSearch` (every simple graph of maximum
degree at most `1` is a matching, and placing the larger endpoint of each edge on the `true` side
cuts every edge simultaneously, achieving global optimum `g.totalWeight`). -/
theorem localMaxCutDeg_one_mem_FPSearch :
    LocalMaxCutDeg 1 ∈ FPSearch (encWeightedGraphDeg 1) := by
  have hpt : ComputableInPolyTime (fun g : WeightedGraphDeg 1 ↦ matchingCut g.1)
      (encWeightedGraphDeg 1) encBits := by
    unfold matchingCut
    refine listToBits.comp ?_
    fun_prop
  refine mem_FPSearch_of_total (PLS_subset_TFNP (localMaxCutDeg_mem_PLS 1)).1 hpt fun g ↦ ?_
  rcases WeightedGraphCode.isSimpleDegLe_eq_true_iff.mp g.2 with ⟨hrange, _, hdeg⟩
  refine ⟨by simp only [matchingCut, List.length_map, List.length_range], fun i _ ↦ ?_⟩
  refine (g.1.cutWeight_le_totalWeight _).trans ?_
  have hall : ∀ e ∈ g.1.edges, WeightedGraphCode.edgeInCut (matchingCut g.1) e = true := by
    intro e he
    have hu : e.1.1 < g.1.numVertices := (hrange e he).1.trans (hrange e he).2
    have hv : e.1.2 < g.1.numVertices := (hrange e he).2
    have hget : ∀ w < g.1.numVertices,
        (matchingCut g.1).getD w false = g.1.edges.any (fun e' ↦ decide (e'.1.2 = w)) := by
      intro w hw
      simp only [matchingCut, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hw, Option.map_some, Option.getD_some]
    have hv_true : (matchingCut g.1).getD e.1.2 false = true := by
      rw [hget e.1.2 hv, List.any_eq_true]; exact ⟨e, he, decide_eq_true rfl⟩
    have hu_false : (matchingCut g.1).getD e.1.1 false = false := by
      rw [hget e.1.1 hu]
      by_contra htrue
      simp only [Bool.not_eq_false, List.any_eq_true, decide_eq_true_eq] at htrue
      obtain ⟨e', he', he'2⟩ := htrue
      have hne : e' ≠ e := fun h ↦ by subst h; exact (hrange e' he').1.ne he'2.symm
      have hge2 : 2 ≤ g.1.vertexDegree e.1.1 := by
        unfold WeightedGraphCode.vertexDegree
        obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem he
        rw [hl, List.countP_append, List.countP_cons]
        have hp_e' : (decide (e'.1.1 = e.1.1) || decide (e'.1.2 = e.1.1)) = true := by simp [he'2]
        have hmem' : e' ∈ l₁ ∨ e' ∈ l₂ := by
          rw [hl] at he'
          rcases List.mem_append.mp he' with h1 | h2
          · exact Or.inl h1
          · exact Or.inr ((List.mem_cons.mp h2).resolve_left hne)
        rcases hmem' with h1 | h2
        · have h1p : 1 ≤ l₁.countP (fun x ↦ decide (x.1.1 = e.1.1) || decide (x.1.2 = e.1.1)) :=
            List.countP_pos_iff.mpr ⟨e', h1, hp_e'⟩
          simp only [decide_true, Bool.true_or, ↓reduceIte]; omega
        · have h2p : 1 ≤ l₂.countP (fun x ↦ decide (x.1.1 = e.1.1) || decide (x.1.2 = e.1.1)) :=
            List.countP_pos_iff.mpr ⟨e', h2, hp_e'⟩
          simp only [decide_true, Bool.true_or, ↓reduceIte]; omega
      exact (hdeg e.1.1 hu).not_gt (by omega)
    simp only [WeightedGraphCode.edgeInCut, hu_false, hv_true]; rfl
  have heq : g.1.cutWeight (matchingCut g.1) = g.1.totalWeight := by
    unfold WeightedGraphCode.cutWeight WeightedGraphCode.totalWeight
    congr 1
    exact List.map_congr_left fun e he ↦ by simp only [hall e he, ↓reduceIte]
  exact heq.ge

end LocalMaxCutPLS

/-! ### 3. `SimpleGraph` Flip Dynamics and Tight Encoding into `WeightedGraphDeg` -/

section SimpleGraphBridge

/-- Predicate testing whether an undirected edge `e : Sym2 V` crosses a binary cut
`x : V → Bool`. -/
@[expose]
def sym2InCut {V : Type*} (x : V → Bool) (e : Sym2 V) : Bool :=
  Sym2.lift ⟨fun u v ↦ decide (x u ≠ x v), fun _ _ ↦ by simp only [ne_comm]⟩ e

/-- Cut weight of a binary partition `x : V → Bool` on an edge-weighted `SimpleGraph V`. -/
@[expose]
def graphCutWeight {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Sym2 V → ℕ) (x : V → Bool) : ℕ :=
  ∑ e ∈ G.edgeFinset, if sym2InCut x e then w e else 0

/-- Total edge weight `∑ e ∈ G.edgeFinset, w e` of a weighted `SimpleGraph V`. -/
def graphTotalWeight {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Sym2 V → ℕ) : ℕ :=
  ∑ e ∈ G.edgeFinset, w e

/-- Every partition on `G` has cut weight at most `graphTotalWeight G w`. -/
theorem graphCutWeight_le_total {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Sym2 V → ℕ) (x : V → Bool) :
    graphCutWeight G w x ≤ graphTotalWeight G w :=
  Finset.sum_le_sum fun _ _ ↦ by split_ifs <;> omega

/-- Discrete 1-flip local search problem on a weighted `SimpleGraph V`. -/
@[expose]
def graphLocalSearchProblem {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : Sym2 V → ℕ) : LocalSearchProblem (V → Bool) :=
  LocalSearchProblem.ofMax Set.univ
    (fun x ↦ {y | ∃ v : V, y = Function.update x v (!x v)})
    (fun _ _ _ _ ↦ Set.mem_univ _)
    (graphTotalWeight G w) (graphCutWeight G w)

/-- Canonical `WeightedGraphCode` encoding of a weighted `SimpleGraph (Fin m)`. -/
def encodeSimpleGraph {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (w : Sym2 (Fin m) → ℕ) : WeightedGraphCode where
  numVertices := m
  edges := (List.range m).flatMap fun u ↦
    (List.range m).filterMap fun v ↦
      if h : u < v ∧ v < m then
        if G.Adj ⟨u, h.1.trans h.2⟩ ⟨v, h.2⟩ then
          some ((u, v), w s(⟨u, h.1.trans h.2⟩, ⟨v, h.2⟩))
        else none
      else none

/-- The encoded graph `encodeSimpleGraph G w` has `m` vertices. -/
@[simp]
theorem encodeSimpleGraph_numVertices {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (w : Sym2 (Fin m) → ℕ) : (encodeSimpleGraph G w).numVertices = m := by
  simp [encodeSimpleGraph]

private lemma mem_encodeSimpleGraph_edges_iff {m : ℕ} (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (w : Sym2 (Fin m) → ℕ) {e : (ℕ × ℕ) × ℕ} :
    e ∈ (encodeSimpleGraph G w).edges ↔
      ∃ h : e.1.1 < e.1.2 ∧ e.1.2 < m,
        G.Adj ⟨e.1.1, h.1.trans h.2⟩ ⟨e.1.2, h.2⟩ ∧
        e.2 = w s(⟨e.1.1, h.1.trans h.2⟩, ⟨e.1.2, h.2⟩) := by
  simp only [encodeSimpleGraph, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨u, hu, v, hv, hif⟩
    split_ifs at hif with hlt hadj
    simp only [Option.some.injEq] at hif
    subst hif; exact ⟨hlt, hadj, rfl⟩
  · rintro ⟨hlt, hadj, hw⟩
    refine ⟨e.1.1, hlt.1.trans hlt.2, e.1.2, hlt.2, ?_⟩
    split_ifs
    exact congrArg some (Prod.ext (Prod.ext rfl rfl) hw.symm)

private lemma nodup_encodeSimpleGraph_fst {m : ℕ} (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (w : Sym2 (Fin m) → ℕ) :
    ((encodeSimpleGraph G w).edges.map Prod.fst).Nodup := by
  let row (u : ℕ) : List (ℕ × ℕ) :=
    ((List.range m).filterMap fun v ↦
      if h : u < v ∧ v < m then
        if G.Adj ⟨u, h.1.trans h.2⟩ ⟨v, h.2⟩ then
          some ((u, v), w s(⟨u, h.1.trans h.2⟩, ⟨v, h.2⟩))
        else none
      else none).map Prod.fst
  have heq : (encodeSimpleGraph G w).edges.map Prod.fst = (List.range m).flatMap row := by
    simp only [encodeSimpleGraph, List.map_flatMap, row]
  rw [heq, List.nodup_flatMap]
  refine ⟨fun u _ ↦ ?_, List.nodup_range.pairwise_of_forall_ne fun u _ u' _ hne ↦ ?_⟩
  · have hrow : ∀ l : List ℕ, l.Nodup →
        ((l.filterMap fun v ↦
          if h : u < v ∧ v < m then
            if G.Adj ⟨u, h.1.trans h.2⟩ ⟨v, h.2⟩ then
              some ((u, v), w s(⟨u, h.1.trans h.2⟩, ⟨v, h.2⟩))
            else none
          else none).map Prod.fst).Nodup := by
      intro l hl; induction l with
      | nil => simp
      | cons v vs ih =>
        rcases List.nodup_cons.mp hl with ⟨hv, hvs⟩
        simp only [List.filterMap_cons]
        split_ifs
        · simp only [List.map_cons, List.nodup_cons, ih hvs, and_true, List.mem_map,
            List.mem_filterMap]
          rintro ⟨x, ⟨v', hv', hx⟩, hfst⟩
          split_ifs at hx
          simp only [Option.some.injEq] at hx; subst hx
          exact hv ((Prod.mk.inj hfst).2 ▸ hv')
        · exact ih hvs
        · exact ih hvs
    exact hrow (List.range m) List.nodup_range
  · intro p hp hp'
    simp only [row, List.mem_map, List.mem_filterMap] at hp hp'
    rcases hp with ⟨e, ⟨v, _, he⟩, rfl⟩
    rcases hp' with ⟨e', ⟨v', _, he'⟩, hfst⟩
    split_ifs at he; split_ifs at he'
    simp only [Option.some.injEq] at he he'; subst he; subst he'
    exact hne (Prod.mk.inj hfst).1.symm

/-- If `G : SimpleGraph (Fin m)` has `G.maxDegree ≤ d`, then `encodeSimpleGraph G w` satisfies
`isSimpleDegLe d = true`. -/
theorem encodeSimpleGraph_isSimpleDegLe {m d : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (w : Sym2 (Fin m) → ℕ) (hdeg : G.maxDegree ≤ d) :
    (encodeSimpleGraph G w).isSimpleDegLe d = true := by
  have hnodup := nodup_encodeSimpleGraph_fst G w
  refine WeightedGraphCode.isSimpleDegLe_eq_true_iff.mpr ⟨fun e he ↦
    (mem_encodeSimpleGraph_edges_iff G w |>.mp he).choose, hnodup, fun v hv ↦ ?_⟩
  let vf : Fin m := ⟨v, hv⟩
  refine le_trans ?_ ((G.degree_le_maxDegree vf).trans hdeg)
  unfold WeightedGraphCode.vertexDegree
  rw [List.countP_eq_length_filter]
  let incList := (encodeSimpleGraph G w).edges.filter
    fun e ↦ decide (e.1.1 = v) || decide (e.1.2 = v)
  let toNbr (e : (ℕ × ℕ) × ℕ) : ℕ := if e.1.1 = v then e.1.2 else e.1.1
  have hnodup_inc : (incList.map toNbr).Nodup := by
    have hfn : (incList.map Prod.fst).Nodup :=
      hnodup.sublist ((List.filter_sublist).map Prod.fst)
    rw [List.nodup_iff_injective_getElem] at hfn ⊢
    intro i j hij
    have hi : i.1 < incList.length := by simpa only [List.length_map] using i.2
    have hj : j.1 < incList.length := by simpa only [List.length_map] using j.2
    have hei := List.mem_filter.mp (incList.getElem_mem hi)
    have hej := List.mem_filter.mp (incList.getElem_mem hj)
    have hlt_i := (mem_encodeSimpleGraph_edges_iff G w |>.mp hei.1).choose
    have hlt_j := (mem_encodeSimpleGraph_edges_iff G w |>.mp hej.1).choose
    have hvi : incList[i.1].1.1 = v ∨ incList[i.1].1.2 = v := by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using hei.2
    have hvj : incList[j.1].1.1 = v ∨ incList[j.1].1.2 = v := by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using hej.2
    simp only [List.getElem_map, toNbr] at hij
    have hp : incList[i.1].1 = incList[j.1].1 := by
      ext <;> split_ifs at hij <;> omega
    exact Fin.ext (Fin.mk.inj (@hfn ⟨i.1, by simp [hi]⟩ ⟨j.1, by simp [hj]⟩ (by simpa using hp)))
  have hsub : (incList.map toNbr).toFinset ⊆ (G.neighborFinset vf).map
      ⟨Fin.val, Fin.val_injective⟩ := by
    intro u hu
    rcases List.mem_map.mp (List.mem_toFinset.mp hu) with ⟨e, he, rfl⟩
    rcases List.mem_filter.mp he with ⟨he_mem, hve⟩
    obtain ⟨hlt, hadj, _⟩ := (mem_encodeSimpleGraph_edges_iff G w).mp he_mem
    have hve' : e.1.1 = v ∨ e.1.2 = v := by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using hve
    dsimp only [toNbr]
    by_cases h1 : e.1.1 = v
    · simp only [h1, ↓reduceIte, Finset.mem_map, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨e.1.2, hlt.2⟩, by simpa [vf, h1] using hadj, rfl⟩
    · have h2 : e.1.2 = v := hve'.resolve_left h1
      simp only [h1, ↓reduceIte, Finset.mem_map, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨e.1.1, hlt.1.trans hlt.2⟩, by simpa [vf, h2] using hadj.symm, rfl⟩
  calc incList.length = (incList.map toNbr).length := (List.length_map _).symm
    _ = (incList.map toNbr).toFinset.card := (List.toFinset_card_of_nodup hnodup_inc).symm
    _ ≤ ((G.neighborFinset vf).map ⟨Fin.val, Fin.val_injective⟩).card := Finset.card_le_card hsub
    _ = G.degree vf := by rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]

/-- `encodeSimpleGraph G w` preserves exact cut weights on all partitions `x : Fin m → Bool`. -/
theorem encodeSimpleGraph_cutWeight {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (w : Sym2 (Fin m) → ℕ) (x : List Bool) :
    (encodeSimpleGraph G w).cutWeight x =
      graphCutWeight G w (fun i : Fin m ↦ x.getD i.1 false) := by
  have hnodup_edges : (encodeSimpleGraph G w).edges.Nodup :=
    (nodup_encodeSimpleGraph_fst G w).of_map Prod.fst
  unfold WeightedGraphCode.cutWeight graphCutWeight
  let edges := (encodeSimpleGraph G w).edges
  let f (e : (ℕ × ℕ) × ℕ) : ℕ := if WeightedGraphCode.edgeInCut x e then e.2 else 0
  have hsum : (edges.map f).sum = ∑ e ∈ edges.toFinset, f e := by
    rw [List.sum_toFinset _ hnodup_edges]
  change (edges.map f).sum = _
  rw [hsum]
  refine Finset.sum_bij
    (fun e he ↦
      let h := (mem_encodeSimpleGraph_edges_iff G w |>.mp (List.mem_toFinset.mp he)).choose
      s((⟨e.1.1, h.1.trans h.2⟩ : Fin m), ⟨e.1.2, h.2⟩))
    (fun e he ↦ by
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (mem_encodeSimpleGraph_edges_iff G w |>.mp (List.mem_toFinset.mp he)).choose_spec.1)
    (fun e₁ he₁ e₂ he₂ hsym ↦ by
      obtain ⟨h1, _, hw1⟩ := (mem_encodeSimpleGraph_edges_iff G w).mp (List.mem_toFinset.mp he₁)
      obtain ⟨h2, _, hw2⟩ := (mem_encodeSimpleGraph_edges_iff G w).mp (List.mem_toFinset.mp he₂)
      rcases Sym2.eq_iff.mp hsym with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have hp1 : e₁.1.1 = e₂.1.1 := congrArg Fin.val ha
        have hp2 : e₁.1.2 = e₂.1.2 := congrArg Fin.val hb
        refine Prod.ext (Prod.ext hp1 hp2) ?_
        rw [hw1, hw2, hsym]
      · have hp1 : e₁.1.1 = e₂.1.2 := congrArg Fin.val ha
        have hp2 : e₁.1.2 = e₂.1.1 := congrArg Fin.val hb
        omega)
    (fun s hs ↦ by
      induction s using Sym2.ind with
      | _ a b =>
        have hadj : G.Adj a b := SimpleGraph.mem_edgeFinset.mp hs
        have hne : a.1 ≠ b.1 := fun h ↦ hadj.ne (Fin.ext h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · refine ⟨((a.1, b.1), w s(a, b)), List.mem_toFinset.mpr
            ((mem_encodeSimpleGraph_edges_iff G w).mpr ⟨⟨hlt, b.2⟩, hadj, rfl⟩), rfl⟩
        · refine ⟨((b.1, a.1), w s(b, a)), List.mem_toFinset.mpr
            ((mem_encodeSimpleGraph_edges_iff G w).mpr ⟨⟨hgt, a.2⟩, hadj.symm, rfl⟩), Sym2.eq_swap⟩)
    (fun e he ↦ by
      obtain ⟨hlt, _, hw⟩ := (mem_encodeSimpleGraph_edges_iff G w).mp (List.mem_toFinset.mp he)
      by_cases hc : WeightedGraphCode.edgeInCut x e = true
      · have hs : sym2InCut (fun i : Fin m ↦ x.getD i.1 false)
            s(⟨e.1.1, hlt.1.trans hlt.2⟩, ⟨e.1.2, hlt.2⟩) = true := by
          simpa only [WeightedGraphCode.edgeInCut, sym2InCut, Sym2.lift_mk, bne_iff_ne,
            decide_eq_true_eq] using hc
        simp only [f, hc, hs, ↓reduceIte]; exact hw
      · have hs : sym2InCut (fun i : Fin m ↦ x.getD i.1 false)
            s(⟨e.1.1, hlt.1.trans hlt.2⟩, ⟨e.1.2, hlt.2⟩) = false := by
          simpa only [WeightedGraphCode.edgeInCut, sym2InCut, Sym2.lift_mk, bne_iff_ne,
            Bool.not_eq_true, decide_eq_false_iff_not] using hc
        simp only [f, hc, hs, Bool.false_eq_true, ↓reduceIte])

/-- `encodeSimpleGraph G w` preserves total edge weight. -/
theorem encodeSimpleGraph_totalWeight {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (w : Sym2 (Fin m) → ℕ) :
    (encodeSimpleGraph G w).totalWeight = graphTotalWeight G w := by
  have hnodup_edges : (encodeSimpleGraph G w).edges.Nodup :=
    (nodup_encodeSimpleGraph_fst G w).of_map Prod.fst
  unfold WeightedGraphCode.totalWeight graphTotalWeight
  let edges := (encodeSimpleGraph G w).edges
  have hsum : (edges.map Prod.snd).sum = ∑ e ∈ edges.toFinset, e.2 :=
    (List.sum_toFinset Prod.snd hnodup_edges).symm
  change (edges.map Prod.snd).sum = _
  rw [hsum]
  refine Finset.sum_bij
    (fun e he ↦
      let h := (mem_encodeSimpleGraph_edges_iff G w |>.mp (List.mem_toFinset.mp he)).choose
      s((⟨e.1.1, h.1.trans h.2⟩ : Fin m), ⟨e.1.2, h.2⟩))
    (fun e he ↦ SimpleGraph.mem_edgeFinset.mpr
      (mem_encodeSimpleGraph_edges_iff G w |>.mp (List.mem_toFinset.mp he)).choose_spec.1)
    (fun e₁ he₁ e₂ he₂ hsym ↦ by
      obtain ⟨h1, _, hw1⟩ := (mem_encodeSimpleGraph_edges_iff G w).mp (List.mem_toFinset.mp he₁)
      obtain ⟨h2, _, hw2⟩ := (mem_encodeSimpleGraph_edges_iff G w).mp (List.mem_toFinset.mp he₂)
      rcases Sym2.eq_iff.mp hsym with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Prod.ext (Prod.ext (congrArg Fin.val ha) (congrArg Fin.val hb))
          (by rw [hw1, hw2, hsym])
      · have ha' : e₁.1.1 = e₂.1.2 := congrArg Fin.val ha
        have hb' : e₁.1.2 = e₂.1.1 := congrArg Fin.val hb
        have := h1.1; have := h2.1; omega)
    (fun s hs ↦ by
      induction s using Sym2.ind with
      | _ a b =>
        have hadj : G.Adj a b := SimpleGraph.mem_edgeFinset.mp hs
        rcases lt_or_gt_of_ne (fun h ↦ hadj.ne (Fin.ext h)) with hlt | hgt
        · exact ⟨((a.1, b.1), w s(a, b)), List.mem_toFinset.mpr
            ((mem_encodeSimpleGraph_edges_iff G w).mpr ⟨⟨hlt, b.2⟩, hadj, rfl⟩), rfl⟩
        · exact ⟨((b.1, a.1), w s(b, a)), List.mem_toFinset.mpr
            ((mem_encodeSimpleGraph_edges_iff G w).mpr ⟨⟨hgt, a.2⟩, hadj.symm, rfl⟩), Sym2.eq_swap⟩)
    (fun e he ↦ (mem_encodeSimpleGraph_edges_iff G w |>.mp (List.mem_toFinset.mp he)).choose_spec.2)

/-- Tight local search reduction (isomorphism on `m`-bit strings) from
`graphLocalSearchProblem G w` to `(encodeSimpleGraph G w).toLocalSearchProblem`. -/
def tightLocalReductionEncodeSimpleGraph {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (w : Sym2 (Fin m) → ℕ) :
    TightLocalReduction (graphLocalSearchProblem G w)
      (encodeSimpleGraph G w).toLocalSearchProblem := by
  let g := encodeSimpleGraph G w
  let dec (u : List Bool) : Fin m → Bool := fun j ↦ u.getD j.1 false
  have hflip : ∀ (u : List Bool) (i : Fin m),
      dec (WeightedGraphCode.flipBit m u i.1) = Function.update (dec u) i (!(dec u i)) := by
    intro u i; funext j
    simp only [dec, WeightedGraphCode.getD_flipBit_of_lt u i.1 j.2]
    by_cases hji : j = i
    · subst hji; simp only [↓reduceIte, Function.update_self]
    · simp only [Fin.val_ne_of_ne hji, ↓reduceIte, Function.update_of_ne hji]
  have hdec_ofFn : ∀ x : Fin m → Bool, dec (List.ofFn x) = x := fun x ↦ by
    funext j
    simp only [dec, List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.2, ↓reduceDIte,
      Option.getD_some]
  refine TightLocalReduction.ofClosed g.toLocalSearchProblem.feasible Set.Subset.rfl
    (fun _ _ _ h ↦ h.right_mem) (fun _ h ↦ h.1) List.ofFn dec
    (fun _ _ ↦ List.length_ofFn) (fun _ _ ↦ Set.mem_univ _) (fun x _ ↦ hdec_ofFn x)
    (fun u hu ↦ ?_) (fun u _ v hstep ↦ ?_)
  · rcases (toLocalSearchProblem_isLocalOpt_iff g u).mp hu with ⟨_, hopt⟩
    refine (LocalSearchProblem.ofMax_isLocalOpt_iff
      (fun y _ ↦ graphCutWeight_le_total G w y)).mpr ⟨Set.mem_univ _, fun _ ⟨i, heq⟩ ↦ ?_⟩
    rw [heq, ← hflip u i]
    have h1 : g.cutWeight (WeightedGraphCode.flipBit m u i.1) ≤ g.cutWeight u := hopt i.1 i.2
    simpa only [g, dec, encodeSimpleGraph_cutWeight] using h1
  · rcases (LocalSearchProblem.ofMax_isImprovingStep_iff
      (fun y _ ↦ g.cutWeight_le_totalWeight y)).mp hstep with ⟨_, ⟨i, hi, heq⟩, hlt⟩
    rw [heq] at hlt ⊢
    refine Or.inr ((LocalSearchProblem.ofMax_isImprovingStep_iff
      (fun y _ ↦ graphCutWeight_le_total G w y)).mpr
      ⟨Set.mem_univ _, ⟨⟨i, hi⟩, hflip u ⟨i, hi⟩⟩, ?_⟩)
    simpa only [g, encodeSimpleGraph_cutWeight] using hlt

/-- Lifting a cut `x : Fin m → Bool` along `tightLocalReductionEncodeSimpleGraph G w` yields an
`m`-bit list. -/
@[simp]
theorem length_tightLocalReductionEncodeSimpleGraph_lift {m : ℕ} (G : SimpleGraph (Fin m))
    [DecidableRel G.Adj] (w : Sym2 (Fin m) → ℕ) (x : Fin m → Bool) :
    ((tightLocalReductionEncodeSimpleGraph G w).lift x).length = m := by
  simp [tightLocalReductionEncodeSimpleGraph, TightLocalReduction.ofClosed]

private theorem isSimpleDegLe_pos_neg_sample :
    let g_ok : WeightedGraphCode := ⟨3, [((0, 1), 4), ((1, 2), 7)]⟩
    let g_loop : WeightedGraphCode := ⟨2, [((0, 0), 1)]⟩
    let g_deg : WeightedGraphCode := ⟨4, [((0, 1), 1), ((0, 2), 1), ((0, 3), 1)]⟩
    g_ok.isSimpleDegLe 2 = true ∧ g_loop.isSimpleDegLe 5 = false ∧
      g_deg.isSimpleDegLe 2 = false ∧ LocalMaxCut g_ok [false, true, false] ∧
      ¬ LocalMaxCut g_ok [false, false, false] := by
  refine ⟨by decide, by decide, by decide, ⟨rfl, fun i hi ↦ ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩
  · interval_cases i <;> decide
  · exact absurd (h 1 (by decide)) (by decide)

end SimpleGraphBridge

end CslibFrontier.Complexity.LocalSearch
