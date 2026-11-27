/-
Copyright (c) 2026 Cslib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cslib Contributors
-/

module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm

/-!
# Polynomial-Time Shortest Simple Directed Paths with Nonnegative Integer Weights

This module implements and verifies a polynomial-time (`Turing.MultiTapeTM.ComputableInPolyTime`)
Bellman–Ford dynamic-programming and loop-erasure algorithm returning an explicit minimum-weight
vertex-simple directed path (as a list of arc indices) in a finite directed multigraph with
nonnegative binary natural arc weights, under standard Lean axioms.

## Main definitions

* `CslibFrontier.Algorithms.ShortestSimplePath.DigraphQuery`,
  `CslibFrontier.Algorithms.ShortestSimplePath.encDigraphQuery`: encoded shortest-path query
  `(numNodes, arcs, src, dst)` with unary node indices and binary `ℕ` arc weights.
* `CslibFrontier.Algorithms.ShortestSimplePath.IsArcWalk`,
  `CslibFrontier.Algorithms.ShortestSimplePath.walkVertices`,
  `CslibFrontier.Algorithms.ShortestSimplePath.IsSimpleArcPath`,
  `CslibFrontier.Algorithms.ShortestSimplePath.arcWalkCost`: valid directed arc walks, visited
  vertex sequences, vertex-simple directed paths, and additive walk cost.
* `CslibFrontier.Algorithms.ShortestSimplePath.loopErase`: deterministic cycle erasure turning any
  directed walk into a vertex-simple path of no larger cost.
* `CslibFrontier.Algorithms.ShortestSimplePath.shortestSimplePath`: Bellman–Ford dynamic
  programming followed by `loopErase`, returning `Option (List ℕ)`.

## Main results

* `CslibFrontier.Algorithms.ShortestSimplePath.IsSimpleArcPath.arc_nodup`,
  `CslibFrontier.Algorithms.ShortestSimplePath.IsSimpleArcPath.length_lt`: every vertex-simple path
  has pairwise distinct arc indices and uses strictly fewer than `numNodes` arcs.
* `CslibFrontier.Algorithms.ShortestSimplePath.loopErase_isSimpleArcPath`,
  `CslibFrontier.Algorithms.ShortestSimplePath.arcWalkCost_loopErase_le`: loop erasure preserves
  endpoints, eliminates repeated vertices, and does not increase `arcWalkCost`.
* `CslibFrontier.Algorithms.ShortestSimplePath.shortestSimplePath_polyTime`: `shortestSimplePath`
  is computable in polynomial time on multi-tape Turing machines.
* `CslibFrontier.Algorithms.ShortestSimplePath.shortestSimplePath_eq_some_of_exists`,
  `CslibFrontier.Algorithms.ShortestSimplePath.shortestSimplePath_eq_none_iff`:
  `shortestSimplePath` finds a minimum-cost vertex-simple `src → dst` path whenever any `src → dst`
  walk exists, and returns `none` otherwise.
-/

public section

open Turing.MultiTapeTM ComputableInPolyTime

namespace CslibFrontier.Algorithms.ShortestSimplePath

/-! ### 1. Directed Arc Walks, Simple Paths, and Cycle Erasure -/

/-- Default arc entry `((0, 0), 0)` used for totalized index lookups. -/
abbrev defaultArc : (ℕ × ℕ) × ℕ := ((0, 0), 0)

/-- Additive cost `∑_{e ∈ p} w_e` of an arc-index sequence `p`. -/
@[expose] def arcWalkCost (arcs : List ((ℕ × ℕ) × ℕ)) (p : List ℕ) : ℕ :=
  (p.map fun e ↦ (arcs.getD e defaultArc).2).sum

/-- `arcWalkCost` on the empty walk is `0`. -/
@[simp]
theorem arcWalkCost_nil (arcs : List ((ℕ × ℕ) × ℕ)) : arcWalkCost arcs [] = 0 := by
  simp only [arcWalkCost, List.map_nil, List.sum_nil]

/-- `arcWalkCost` on `e :: es`. -/
@[simp]
theorem arcWalkCost_cons (arcs : List ((ℕ × ℕ) × ℕ)) (e : ℕ) (es : List ℕ) :
    arcWalkCost arcs (e :: es) = (arcs.getD e defaultArc).2 + arcWalkCost arcs es := by
  simp only [arcWalkCost, List.map_cons, List.sum_cons]

/-- `arcWalkCost` distributes over list concatenation. -/
@[simp]
theorem arcWalkCost_append (arcs : List ((ℕ × ℕ) × ℕ)) (p q : List ℕ) :
    arcWalkCost arcs (p ++ q) = arcWalkCost arcs p + arcWalkCost arcs q := by
  simp only [arcWalkCost, List.map_append, List.sum_append]

/-- Valid directed walk from `u` to `t` on vertex set `{0, ..., numNodes - 1}` represented as a
list of arc indices into `arcs`. -/
inductive IsArcWalk (numNodes : ℕ) (arcs : List ((ℕ × ℕ) × ℕ)) : ℕ → ℕ → List ℕ → Prop
  | nil {u : ℕ} (hu : u < numNodes) : IsArcWalk numNodes arcs u u []
  | cons {u v t e : ℕ} {es : List ℕ} (hu : u < numNodes) (he : e < arcs.length)
      (hsrc : (arcs.getD e defaultArc).1.1 = u) (hdst : (arcs.getD e defaultArc).1.2 = v)
      (hrest : IsArcWalk numNodes arcs v t es) : IsArcWalk numNodes arcs u t (e :: es)

/-- The starting vertex of a valid walk lies below `numNodes`. -/
theorem IsArcWalk.start_lt {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {u t : ℕ} {p : List ℕ}
    (h : IsArcWalk n arcs u t p) : u < n := by
  cases h with
  | nil hu => exact hu
  | cons hu => exact hu

/-- The ending vertex of a valid walk lies below `numNodes`. -/
theorem IsArcWalk.end_lt {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {u t : ℕ} {p : List ℕ}
    (h : IsArcWalk n arcs u t p) : t < n := by
  induction h with
  | nil hu => exact hu
  | cons _ _ _ _ _ ih => exact ih

/-- Every arc index appearing in a valid walk lies below `arcs.length`. -/
theorem IsArcWalk.arc_lt {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {u t : ℕ} {p : List ℕ}
    (h : IsArcWalk n arcs u t p) : ∀ e ∈ p, e < arcs.length := by
  induction h with
  | nil => intro _ hm; exact (List.not_mem_nil hm).elim
  | cons _ he _ _ _ ih =>
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
    · exact he
    · exact ih x hx'

/-- Concatenation of two valid directed walks with matching midpoint. -/
theorem IsArcWalk.append {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {u v t : ℕ} {p q : List ℕ}
    (hp : IsArcWalk n arcs u v p) (hq : IsArcWalk n arcs v t q) :
    IsArcWalk n arcs u t (p ++ q) := by
  induction hp with
  | nil => exact hq
  | cons hu he hsrc hdst _ ih => exact .cons hu he hsrc hdst (ih hq)

/-- Sequence of vertices visited along an arc sequence starting at `u`. -/
@[expose] def walkVertices (arcs : List ((ℕ × ℕ) × ℕ)) (u : ℕ) : List ℕ → List ℕ
  | [] => [u]
  | e :: es => u :: walkVertices arcs (arcs.getD e defaultArc).1.2 es

/-- `walkVertices arcs u p` has length `p.length + 1`. -/
@[simp]
theorem length_walkVertices (arcs : List ((ℕ × ℕ) × ℕ)) (u : ℕ) (p : List ℕ) :
    (walkVertices arcs u p).length = p.length + 1 := by
  induction p generalizing u with
  | nil => rfl
  | cons e es ih => simp only [walkVertices, List.length_cons, ih]

/-- Every vertex in `walkVertices arcs u p` of a valid walk lies in `List.range numNodes`. -/
theorem IsArcWalk.mem_walkVertices_lt {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {u t : ℕ} {p : List ℕ}
    (h : IsArcWalk n arcs u t p) : ∀ x ∈ walkVertices arcs u p, x < n := by
  induction h with
  | nil hu => intro x hx; simpa only [walkVertices, List.mem_singleton.mp hx] using hu
  | cons hu _ _ hdst _ ih =>
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
    · exact hu
    · rw [hdst] at hx'; exact ih x hx'

/-- A vertex-simple directed path from `u` to `t`: a valid walk with no repeated vertices. -/
@[expose] def IsSimpleArcPath (numNodes : ℕ) (arcs : List ((ℕ × ℕ) × ℕ)) (u t : ℕ) (p : List ℕ) :
    Prop :=
  IsArcWalk numNodes arcs u t p ∧ (walkVertices arcs u p).Nodup

/-- Every vertex-simple directed path uses strictly fewer than `numNodes` arcs. -/
theorem IsSimpleArcPath.length_lt {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {u t : ℕ} {p : List ℕ}
    (hp : IsSimpleArcPath n arcs u t p) : p.length < n := by
  have hsub :=
    (hp.2.subperm fun x hx ↦ List.mem_range.mpr (hp.1.mem_walkVertices_lt x hx)).length_le
  simp only [length_walkVertices, List.length_range] at hsub
  omega

/-- Every vertex-simple directed path has pairwise distinct arc indices (`p.Nodup`). -/
theorem IsSimpleArcPath.arc_nodup {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {u t : ℕ} {p : List ℕ}
    (hp : IsSimpleArcPath n arcs u t p) : p.Nodup := by
  rcases hp with ⟨hw, hnd⟩
  have hmem_start : ∀ {a b e : ℕ} {es : List ℕ},
      IsArcWalk n arcs a b es → e ∈ es → (arcs.getD e defaultArc).1.1 ∈ walkVertices arcs a es := by
    intro a b e es hes; induction hes with
    | nil => intro hm; exact (List.not_mem_nil hm).elim
    | cons _ _ hsrc hdst _ ih =>
      intro hm; rcases List.mem_cons.mp hm with rfl | hm'
      · simp only [walkVertices, hsrc, List.mem_cons, true_or]
      · simp only [walkVertices, hdst, List.mem_cons]; exact Or.inr (ih hm')
  induction hw with
  | nil => exact List.nodup_nil
  | cons _ _ hsrc hdst hrest ih =>
    simp only [walkVertices, hdst, List.nodup_cons] at hnd
    exact List.nodup_cons.mpr ⟨fun hmem ↦ hnd.1 (hsrc ▸ hmem_start hrest hmem), ih hnd.2⟩

/-- Boolean decidable check for `IsArcWalk`. -/
@[expose] def checkArcWalk (numNodes : ℕ) (arcs : List ((ℕ × ℕ) × ℕ)) (u t : ℕ) : List ℕ → Bool
  | [] => decide (u = t) && decide (u < numNodes)
  | e :: es =>
    let a := arcs.getD e defaultArc
    decide (u < numNodes) && decide (e < arcs.length) && decide (a.1.1 = u) &&
      checkArcWalk numNodes arcs a.1.2 t es

/-- `checkArcWalk` decides `IsArcWalk` exactly. -/
theorem checkArcWalk_eq_true_iff (n : ℕ) (arcs : List ((ℕ × ℕ) × ℕ)) (u t : ℕ) (p : List ℕ) :
    checkArcWalk n arcs u t p = true ↔ IsArcWalk n arcs u t p := by
  induction p generalizing u with
  | nil =>
    simp only [checkArcWalk, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨rfl, hu⟩ ↦ .nil hu, fun h ↦ by cases h; exact ⟨rfl, ‹_›⟩⟩
  | cons e es ih =>
    simp only [checkArcWalk, Bool.and_eq_true, decide_eq_true_eq, and_assoc, ih]
    exact ⟨fun ⟨hu, he, hsrc, hrest⟩ ↦ .cons hu he hsrc rfl hrest,
      fun h ↦ by cases h with | cons hu he hsrc hdst hrest => subst hdst; exact ⟨hu, he, hsrc,
        hrest⟩⟩

/-- Drop prefix arcs of a path `q` starting at `cur` until reaching vertex `target`. -/
def dropUntilVertex (arcs : List ((ℕ × ℕ) × ℕ)) (target : ℕ) (cur : ℕ) : List ℕ → List ℕ
  | [] => []
  | e :: es =>
    if cur = target then e :: es
    else dropUntilVertex arcs target (arcs.getD e defaultArc).1.2 es

private lemma dropUntilVertex_spec {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {target cur t : ℕ}
    {q : List ℕ} (hq : IsSimpleArcPath n arcs cur t q) (hmem : target ∈ walkVertices arcs cur q) :
    IsSimpleArcPath n arcs target t (dropUntilVertex arcs target cur q) ∧
      arcWalkCost arcs (dropUntilVertex arcs target cur q) ≤ arcWalkCost arcs q ∧
      (dropUntilVertex arcs target cur q).Sublist q := by
  rcases hq with ⟨hw, hnd⟩
  induction hw with
  | @nil c hu =>
    simp only [walkVertices, List.mem_singleton] at hmem; subst hmem
    exact ⟨⟨.nil hu, List.nodup_singleton _⟩, le_rfl, List.Sublist.refl []⟩
  | @cons c w _ e es hu he hsrc hdst hrest ih =>
    simp only [dropUntilVertex]
    by_cases hct : c = target
    · subst hct; simp only [↓reduceIte]
      exact ⟨⟨.cons hu he hsrc hdst hrest, hnd⟩, le_rfl, List.Sublist.refl _⟩
    · simp only [hct, ↓reduceIte, hdst]
      simp only [walkVertices, hdst, List.mem_cons, List.nodup_cons] at hmem hnd
      have ht' : target ∈ walkVertices arcs w es := hmem.resolve_left (Ne.symm hct)
      obtain ⟨hsimp, hcost, hsub⟩ := ih ht' hnd.2
      exact ⟨hsimp, hcost.trans (by rw [arcWalkCost_cons]; omega),
        hsub.trans (List.sublist_cons_self _ _)⟩

/-- One backward step of cycle erasure: prepend arc `e` to simple path `q`, collapsing any cycle
if `(arcs[e]).1.1` already appears in `walkVertices arcs (arcs[e]).1.2 q`. -/
def loopEraseStep (arcs : List ((ℕ × ℕ) × ℕ)) (q : List ℕ) (e : ℕ) : List ℕ :=
  let a := arcs.getD e defaultArc
  if (walkVertices arcs a.1.2 q).any (fun x ↦ decide (x = a.1.1)) then
    dropUntilVertex arcs a.1.1 a.1.2 q
  else
    e :: q

/-- Deterministic cycle erasure producing a vertex-simple path from any valid walk `p`. -/
def loopErase (arcs : List ((ℕ × ℕ) × ℕ)) (p : List ℕ) : List ℕ :=
  p.reverse.foldl (loopEraseStep arcs) []

private lemma loopErase_cons (arcs : List ((ℕ × ℕ) × ℕ)) (e : ℕ) (es : List ℕ) :
    loopErase arcs (e :: es) = loopEraseStep arcs (loopErase arcs es) e := by
  simp only [loopErase, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `loopErase` converts any valid `u → t` walk into a vertex-simple `u → t` path. -/
theorem loopErase_isSimpleArcPath {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {u t : ℕ} {p : List ℕ}
    (hp : IsArcWalk n arcs u t p) : IsSimpleArcPath n arcs u t (loopErase arcs p) := by
  induction hp with
  | @nil a hu => exact ⟨.nil hu, List.nodup_singleton a⟩
  | @cons a b _ e es hu he hsrc hdst _ ih =>
    rw [loopErase_cons]
    unfold loopEraseStep
    simp only [hsrc, hdst]
    by_cases hmem : (walkVertices arcs b (loopErase arcs es)).any (fun x ↦ decide (x = a)) = true
    · simp only [hmem, ↓reduceIte]
      have hu_mem : a ∈ walkVertices arcs b (loopErase arcs es) := by
        rcases List.any_eq_true.mp hmem with ⟨x, hx, hxu⟩
        exact (decide_eq_true_eq.mp hxu) ▸ hx
      exact (dropUntilVertex_spec ih hu_mem).1
    · simp only [hmem, Bool.false_eq_true, ↓reduceIte]
      have hu_not : a ∉ walkVertices arcs b (loopErase arcs es) := fun hm ↦
        hmem (List.any_eq_true.mpr ⟨a, hm, decide_eq_true rfl⟩)
      refine ⟨.cons hu he hsrc hdst ih.1, ?_⟩
      simp only [walkVertices, hdst, List.nodup_cons]
      exact ⟨hu_not, ih.2⟩

/-- `loopErase` never increases `arcWalkCost`. -/
theorem arcWalkCost_loopErase_le {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {u t : ℕ} {p : List ℕ}
    (hp : IsArcWalk n arcs u t p) : arcWalkCost arcs (loopErase arcs p) ≤ arcWalkCost arcs p := by
  induction hp with
  | nil => exact le_rfl
  | @cons a b _ e es _ _ hsrc hdst hrest ih =>
    rw [loopErase_cons, arcWalkCost_cons]
    unfold loopEraseStep
    simp only [hsrc, hdst]
    by_cases hmem : (walkVertices arcs b (loopErase arcs es)).any (fun x ↦ decide (x = a)) = true
    · simp only [hmem, ↓reduceIte]
      have hu_mem : a ∈ walkVertices arcs b (loopErase arcs es) := by
        rcases List.any_eq_true.mp hmem with ⟨x, hx, hxu⟩
        exact (decide_eq_true_eq.mp hxu) ▸ hx
      have hdrop := (dropUntilVertex_spec (loopErase_isSimpleArcPath hrest) hu_mem).2.1
      omega
    · simp only [hmem, Bool.false_eq_true, ↓reduceIte, arcWalkCost_cons]; omega

/-- For every step of `loopEraseStep`, the output is a sublist of `e :: q`. -/
private lemma loopEraseStep_sublist (arcs : List ((ℕ × ℕ) × ℕ)) (q : List ℕ) (e : ℕ) :
    (loopEraseStep arcs q e).Sublist (e :: q) := by
  have hdrop : ∀ (tgt cur : ℕ) (xs : List ℕ), (dropUntilVertex arcs tgt cur xs).Sublist xs := by
    intro tgt cur xs; induction xs generalizing cur with
    | nil => exact List.Sublist.refl []
    | cons a as ih =>
      simp only [dropUntilVertex]
      split_ifs
      · exact List.Sublist.refl _
      · exact (ih _).trans (List.sublist_cons_self _ _)
  unfold loopEraseStep
  dsimp only
  split_ifs
  · exact (hdrop _ _ q).trans (List.sublist_cons_self _ _)
  · exact List.Sublist.refl _

/-! ### 2. Polynomial-Time Bellman–Ford Dynamic Programming -/

/-- Encoded shortest-path query on a finite nonnegatively weighted directed multigraph. -/
@[ext]
structure DigraphQuery : Type where
  /-- Number of vertices `numNodes`. -/
  numNodes : ℕ
  /-- Directed arcs `((u, v), w)` with `0 ≤ u, v < numNodes` and binary weight `w : ℕ`. -/
  arcs : List ((ℕ × ℕ) × ℕ)
  /-- Source vertex `src`. -/
  src : ℕ
  /-- Target vertex `dst`. -/
  dst : ℕ
  deriving DecidableEq

/-- Canonical bit-string encoding of `DigraphQuery`: unary vertices, binary arc weights. -/
enc_structure encDigraphQuery : DigraphQuery where
  numNodes : encUnary,
  arcs : (encList (encPair (encPair encUnary encUnary) encNat)),
  src : encUnary,
  dst : encUnary

attribute [fun_prop] encDigraphQuery_numNodes_polyTime encDigraphQuery_arcs_polyTime
  encDigraphQuery_src_polyTime encDigraphQuery_dst_polyTime encDigraphQuery_mk_polyTime

/-- Dynamic-programming table type: for each node `v`, `some (cost, arcWalk)` or `none`. -/
abbrev BFTable : Type := List (Option (ℕ × List ℕ))

/-- Bit-string encoding of `BFTable`. -/
abbrev encBFTable : BFTable ↪ List Bool :=
  encList (encOption (encPair encNat (encList encUnary)))

/-- Pick the cheaper of two `Option (ℕ × List ℕ)` path candidates. -/
def betterEntry (cur cand : Option (ℕ × List ℕ)) : Option (ℕ × List ℕ) :=
  match cur, cand with
  | none, y => y
  | x, none => x
  | some (c₁, p₁), some (c₂, p₂) => if c₂ < c₁ then some (c₂, p₂) else some (c₁, p₁)

/-- Relax a single indexed arc `(a, e)` entering vertex `v` against table `tbl`. -/
def relaxArcFor (numNodes v : ℕ) (tbl : BFTable) (cur : Option (ℕ × List ℕ))
    (ae : ((ℕ × ℕ) × ℕ) × ℕ) : Option (ℕ × List ℕ) :=
  if ae.1.1.1 < numNodes && ae.1.1.2 == v then
    match tbl.getD ae.1.1.1 none with
    | none => cur
    | some (cu, pu) => betterEntry cur (some (cu + ae.1.2, pu ++ [ae.2]))
  else
    cur

/-- One parallel Bellman–Ford relaxation round across all `v ∈ List.range numNodes`. -/
def bfRound (numNodes : ℕ) (arcs : List ((ℕ × ℕ) × ℕ)) (tbl : BFTable) : BFTable :=
  (List.range numNodes).map fun v ↦
    arcs.zipIdx.foldl (relaxArcFor numNodes v tbl) (tbl.getD v none)

/-- Initial Bellman–Ford table: `some (0, [])` at `src`, `none` at all other vertices. -/
def bfInit (numNodes src : ℕ) : BFTable :=
  (List.range numNodes).map fun v ↦ if v = src then some (0, []) else none

/-- Bellman–Ford table after `numNodes` relaxation rounds. -/
def bfRun (q : DigraphQuery) : BFTable :=
  (bfRound q.numNodes q.arcs)^[q.numNodes] (bfInit q.numNodes q.src)

/-- Shortest vertex-simple directed path from `q.src` to `q.dst`, returning `some p` with `p` a
minimum-cost simple path of arc indices if any `src → dst` walk exists, and `none` otherwise. -/
def shortestSimplePath (q : DigraphQuery) : Option (List ℕ) :=
  if q.dst < q.numNodes then
    ((bfRun q).getD q.dst none).map fun cp ↦ loopErase q.arcs cp.2
  else
    none

private def BFInv (q : DigraphQuery) (k : ℕ) (tbl : BFTable) : Prop :=
  tbl.length = q.numNodes ∧
    (∀ v < q.numNodes, ∀ c p, tbl.getD v none = some (c, p) →
      IsArcWalk q.numNodes q.arcs q.src v p ∧ arcWalkCost q.arcs p = c ∧ p.length ≤ k) ∧
    (∀ v < q.numNodes, ∀ p, IsArcWalk q.numNodes q.arcs q.src v p → p.length ≤ k →
      ∃ c p', tbl.getD v none = some (c, p') ∧ c ≤ arcWalkCost q.arcs p)

private lemma bfInv_init (q : DigraphQuery) : BFInv q 0 (bfInit q.numNodes q.src) := by
  refine ⟨by simp only [bfInit, List.length_map, List.length_range], fun v hv c p hget ↦ ?_,
    fun v hv p hp hlen ↦ ?_⟩
  · simp only [bfInit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv,
      Option.map_some, Option.getD_some] at hget
    split_ifs at hget with hvs
    simp only [Option.some.injEq, Prod.mk.injEq] at hget
    rcases hget with ⟨rfl, rfl⟩; subst hvs
    exact ⟨.nil hv, rfl, le_rfl⟩
  · cases p with
    | nil =>
      cases hp
      refine ⟨0, [], ?_, le_rfl⟩
      simp only [bfInit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv,
        Option.map_some, Option.getD_some, ↓reduceIte]
    | cons _ _ => simp only [List.length_cons] at hlen; omega

private lemma betterEntry_sound {P : ℕ × List ℕ → Prop} {cur cand : Option (ℕ × List ℕ)}
    (hcur : ∀ x, cur = some x → P x) (hcand : ∀ x, cand = some x → P x) :
    ∀ x, betterEntry cur cand = some x → P x := by
  cases cur with
  | none => exact hcand
  | some a =>
    cases cand with
    | none => exact hcur
    | some b =>
      dsimp only [betterEntry]; split_ifs
      · intro x hx; exact hcand x hx
      · intro x hx; exact hcur x hx

private lemma betterEntry_le_left {cur cand : Option (ℕ × List ℕ)} {c : ℕ} {p : List ℕ}
    (h : cur = some (c, p)) : ∃ c' p', betterEntry cur cand = some (c', p') ∧ c' ≤ c := by
  subst h
  cases cand with
  | none => exact ⟨c, p, rfl, le_rfl⟩
  | some b =>
    rcases b with ⟨c₂, p₂⟩; dsimp only [betterEntry]; split_ifs with hlt
    · exact ⟨c₂, p₂, rfl, hlt.le⟩
    · exact ⟨c, p, rfl, le_rfl⟩

private lemma betterEntry_le_right (cur : Option (ℕ × List ℕ)) (c : ℕ) (p : List ℕ) :
    ∃ c' p', betterEntry cur (some (c, p)) = some (c', p') ∧ c' ≤ c := by
  cases cur with
  | none => exact ⟨c, p, rfl, le_rfl⟩
  | some a =>
    rcases a with ⟨c₁, p₁⟩; dsimp only [betterEntry]; split_ifs with hlt
    · exact ⟨c, p, rfl, le_rfl⟩
    · exact ⟨c₁, p₁, rfl, le_of_not_gt hlt⟩

private lemma walk_snoc_split {n : ℕ} {arcs : List ((ℕ × ℕ) × ℕ)} {s v : ℕ} :
    ∀ {p : List ℕ}, IsArcWalk n arcs s v p → p ≠ [] →
      ∃ u e q, p = q ++ [e] ∧ IsArcWalk n arcs s u q ∧ u < n ∧ e < arcs.length ∧
        (arcs.getD e defaultArc).1.1 = u ∧ (arcs.getD e defaultArc).1.2 = v
  | [], _, hne => (hne rfl).elim
  | [e], .cons hu he hsrc hdst (.nil _), _ => ⟨s, e, [], rfl, .nil hu, hu, he, hsrc, hdst⟩
  | e :: e' :: es, .cons hu he hsrc hdst hrest, _ => by
    obtain ⟨u', elast, q, heq, hq, hu', hel, hs', hd'⟩ :=
      walk_snoc_split hrest (List.cons_ne_nil e' es)
    exact ⟨u', elast, e :: q, by simp [heq], .cons hu he hsrc hdst hq, hu', hel, hs', hd'⟩

private lemma bfInv_step (q : DigraphQuery) {k : ℕ} {tbl : BFTable} (hinv : BFInv q k tbl) :
    BFInv q (k + 1) (bfRound q.numNodes q.arcs tbl) := by
  rcases hinv with ⟨hlen_tbl, hsound, hcomp⟩
  let good (v : ℕ) (cp : ℕ × List ℕ) : Prop :=
    IsArcWalk q.numNodes q.arcs q.src v cp.2 ∧ arcWalkCost q.arcs cp.2 = cp.1 ∧ cp.2.length ≤ k + 1
  have hrelax_sound : ∀ v < q.numNodes, ∀ (ls : List (((ℕ × ℕ) × ℕ) × ℕ)),
      (∀ ae ∈ ls, ae ∈ q.arcs.zipIdx) → ∀ cur, (∀ x, cur = some x → good v x) →
      ∀ x, ls.foldl (relaxArcFor q.numNodes v tbl) cur = some x → good v x := by
    intro v hv ls hls cur hcur
    induction ls generalizing cur with
    | nil => exact hcur
    | cons ae rest ih =>
      refine ih (fun y hy ↦ hls y (List.mem_cons_of_mem ae hy)) _ ?_
      have hae := List.mk_mem_zipIdx_iff_getElem?.mp (hls ae List.mem_cons_self)
      have he_lt : ae.2 < q.arcs.length := (List.getElem?_eq_some_iff.mp hae).1
      have hget_ae : q.arcs.getD ae.2 defaultArc = ae.1 := by
        simp only [List.getD_eq_getElem?_getD, hae, Option.getD_some]
      unfold relaxArcFor
      by_cases hcond : (ae.1.1.1 < q.numNodes && ae.1.1.2 == v) = true
      · simp only [hcond, ↓reduceIte]
        have hcond' : ae.1.1.1 < q.numNodes ∧ ae.1.1.2 = v := by
          simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hcond
        cases htu : tbl.getD ae.1.1.1 none with
        | none => exact hcur
        | some cp =>
          rcases cp with ⟨cu, pu⟩
          obtain ⟨hwu, hcu, hpu⟩ := hsound ae.1.1.1 hcond'.1 cu pu htu
          refine betterEntry_sound hcur fun x hx ↦ ?_
          cases Option.some.inj hx
          refine ⟨hwu.append (.cons hcond'.1 he_lt (by rw [hget_ae])
            (by rw [hget_ae, hcond'.2]) (.nil hv)), ?_, ?_⟩
          · simp only [arcWalkCost_append, arcWalkCost_cons, arcWalkCost_nil, add_zero, hcu,
              hget_ae]
          · simp only [List.length_append, List.length_singleton]; omega
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte]; exact hcur
  have hrelax_mono : ∀ v (ls : List (((ℕ × ℕ) × ℕ) × ℕ)) (cur : Option (ℕ × List ℕ)) c p,
      cur = some (c, p) →
      ∃ c' p', ls.foldl (relaxArcFor q.numNodes v tbl) cur = some (c', p') ∧ c' ≤ c := by
    intro v ls; induction ls with
    | nil => intro cur c p h; exact ⟨c, p, h, le_rfl⟩
    | cons ae rest ih =>
      intro cur c p hcur
      have h1 : ∃ c₁ p₁, relaxArcFor q.numNodes v tbl cur ae = some (c₁, p₁) ∧ c₁ ≤ c := by
        unfold relaxArcFor
        split_ifs
        · cases tbl.getD ae.1.1.1 none with
          | none => exact ⟨c, p, hcur, le_rfl⟩
          | some cp => exact betterEntry_le_left hcur
        · exact ⟨c, p, hcur, le_rfl⟩
      obtain ⟨c₁, p₁, h1eq, h1le⟩ := h1
      obtain ⟨c₂, p₂, h2eq, h2le⟩ := ih _ c₁ p₁ h1eq
      exact ⟨c₂, p₂, h2eq, h2le.trans h1le⟩
  refine ⟨by simp only [bfRound, List.length_map, List.length_range], fun v hv c p hget ↦ ?_,
    fun v hv p hp hlen ↦ ?_⟩
  · simp only [bfRound, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv,
      Option.map_some, Option.getD_some] at hget
    refine hrelax_sound v hv q.arcs.zipIdx (fun _ h ↦ h) (tbl.getD v none) (fun x hx ↦ ?_)
      (c, p) hget
    obtain ⟨hw, hc, hl⟩ := hsound v hv x.1 x.2 hx
    exact ⟨hw, hc, by omega⟩
  · simp only [bfRound, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv,
      Option.map_some, Option.getD_some]
    cases p with
    | nil =>
      obtain ⟨c, p', htv, hle⟩ := hcomp v hv [] hp (Nat.zero_le k)
      exact hrelax_mono v q.arcs.zipIdx _ c p' htv |>.imp fun c' h ↦
        h.imp fun p'' ⟨heq, hle'⟩ ↦ ⟨heq, hle'.trans hle⟩
    | cons e₀ es =>
      obtain ⟨u, e, pref, heq, hpref, hu, he_lt, hsrc, hdst⟩ :=
        walk_snoc_split hp (List.cons_ne_nil e₀ es)
      have hpref_len : pref.length ≤ k := by
        have := congrArg List.length heq
        simp only [List.length_cons, List.length_append, List.length_nil] at this hlen; omega
      obtain ⟨cu, pu, htu, hcu_le⟩ := hcomp u hu pref hpref hpref_len
      let ae : ((ℕ × ℕ) × ℕ) × ℕ := (q.arcs[e]'he_lt, e)
      have hae_mem : ae ∈ q.arcs.zipIdx :=
        List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem he_lt)
      have hae_eq : q.arcs.getD e defaultArc = ae.1 := by
        simp only [ae, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he_lt, Option.getD_some]
      obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hae_mem
      rw [hsplit, List.foldl_append, List.foldl_cons]
      have hstep : ∃ c₁ p₁,
          relaxArcFor q.numNodes v tbl (l₁.foldl (relaxArcFor q.numNodes v tbl) (tbl.getD v none))
            ae = some (c₁, p₁) ∧ c₁ ≤ cu + ae.1.2 := by
        unfold relaxArcFor
        have hae1 : ae.1.1.1 = u := hae_eq ▸ hsrc
        have hae2 : ae.1.1.2 = v := hae_eq ▸ hdst
        have hc : (decide (ae.1.1.1 < q.numNodes) && (ae.1.1.2 == v)) = true := by
          simp only [hae1, hae2, hu, decide_true, beq_self_eq_true, Bool.and_self]
        rw [hc]; simp only [↓reduceIte, hae1, htu]
        exact betterEntry_le_right _ (cu + ae.1.2) (pu ++ [e])
      obtain ⟨c₁, p₁, h1eq, h1le⟩ := hstep
      obtain ⟨c₂, p₂, h2eq, h2le⟩ := hrelax_mono v l₂ _ c₁ p₁ h1eq
      refine ⟨c₂, p₂, h2eq, h2le.trans (h1le.trans ?_)⟩
      rw [heq, arcWalkCost_append, arcWalkCost_cons, arcWalkCost_nil, add_zero, hae_eq]
      omega

private lemma bfInv_run (q : DigraphQuery) : BFInv q q.numNodes (bfRun q) := by
  have h : ∀ k, BFInv q k ((bfRound q.numNodes q.arcs)^[k] (bfInit q.numNodes q.src)) := by
    intro k; induction k with
    | zero => exact bfInv_init q
    | succ k ih => rw [Function.iterate_succ_apply']; exact bfInv_step q ih
  exact h q.numNodes

/-- **Soundness and optimality of `shortestSimplePath`**: whenever any directed walk from `q.src`
to `q.dst` exists, `shortestSimplePath q` returns `some p` where `p` is a vertex-simple
`q.src → q.dst` path minimizing `arcWalkCost q.arcs` over all `q.src → q.dst` walks. -/
theorem shortestSimplePath_eq_some_of_exists (q : DigraphQuery)
    (hex : ∃ w, IsArcWalk q.numNodes q.arcs q.src q.dst w) :
    ∃ p, shortestSimplePath q = some p ∧
      IsSimpleArcPath q.numNodes q.arcs q.src q.dst p ∧
      ∀ w, IsArcWalk q.numNodes q.arcs q.src q.dst w →
        arcWalkCost q.arcs p ≤ arcWalkCost q.arcs w := by
  obtain ⟨w₀, hw₀⟩ := hex
  have hdst : q.dst < q.numNodes := hw₀.end_lt
  obtain ⟨_, hsound, hcomp⟩ := bfInv_run q
  have hw₀s := loopErase_isSimpleArcPath hw₀
  obtain ⟨c, p₀, hget, _⟩ := hcomp q.dst hdst (loopErase q.arcs w₀) hw₀s.1 hw₀s.length_lt.le
  obtain ⟨hp₀w, hp₀c, _⟩ := hsound q.dst hdst c p₀ hget
  refine ⟨loopErase q.arcs p₀, ?_, loopErase_isSimpleArcPath hp₀w, fun w hw ↦ ?_⟩
  · simp only [shortestSimplePath, hdst, ↓reduceIte, hget, Option.map_some]
  · have hws := loopErase_isSimpleArcPath hw
    obtain ⟨c', p', hget', hle'⟩ := hcomp q.dst hdst (loopErase q.arcs w) hws.1 hws.length_lt.le
    rw [hget] at hget'
    cases Option.some.inj hget'
    exact (arcWalkCost_loopErase_le hp₀w).trans
      (hp₀c.le.trans (hle'.trans (arcWalkCost_loopErase_le hw)))

/-- `shortestSimplePath q = none` if and only if no directed walk from `q.src` to `q.dst` exists. -/
theorem shortestSimplePath_eq_none_iff (q : DigraphQuery) :
    shortestSimplePath q = none ↔ ¬ ∃ w, IsArcWalk q.numNodes q.arcs q.src q.dst w := by
  constructor
  · intro hnone hex
    obtain ⟨p, hsome, _⟩ := shortestSimplePath_eq_some_of_exists q hex
    rw [hnone] at hsome; cases hsome
  · intro hno
    unfold shortestSimplePath
    by_cases hdst : q.dst < q.numNodes
    · simp only [hdst, ↓reduceIte, Option.map_eq_none_iff]
      cases hget : (bfRun q).getD q.dst none with
      | none => rfl
      | some cp => exact (hno ⟨cp.2, ((bfInv_run q).2.1 q.dst hdst cp.1 cp.2 hget).1⟩).elim
    · simp only [hdst, ↓reduceIte]

/-! ### 3. Polynomial-Time Computability of `shortestSimplePath` -/

section PolyTime

private theorem cond_pt {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {c : γ → Bool} {t f : γ → α}
    (hc : ComputableInPolyTime c encIn encBool)
    (ht : ComputableInPolyTime t encIn encA)
    (hf : ComputableInPolyTime f encIn encA) :
    ComputableInPolyTime (fun x ↦ if c x then t x else f x) encIn encA :=
  hc.ite ht hf

attribute [local fun_prop] bool_and' bool_or' cond_pt binary_le' binary_lt'

private theorem walkVertices_eq_foldl (arcs : List ((ℕ × ℕ) × ℕ)) (u : ℕ) (p : List ℕ) :
    walkVertices arcs u p =
      (p.foldl (fun (acc : ℕ × List ℕ) e ↦
        let nxt := (arcs.getD e defaultArc).1.2
        (nxt, acc.2 ++ [nxt])) (u, [u])).2 := by
  have haux : ∀ (xs : List ℕ) (cur : ℕ) (pref : List ℕ),
      (xs.foldl (fun (acc : ℕ × List ℕ) e ↦
        let nxt := (arcs.getD e defaultArc).1.2
        (nxt, acc.2 ++ [nxt])) (cur, pref ++ [cur])).2 = pref ++ walkVertices arcs cur xs := by
    intro xs; induction xs with
    | nil => intro cur pref; rfl
    | cons e es ih =>
      intro cur pref
      simp only [List.foldl_cons, walkVertices]
      simpa only [List.append_assoc, List.singleton_append] using ih _ (pref ++ [cur])
  simpa only [List.nil_append] using (haux p u []).symm

private lemma encArcs_node_le (arcs : List ((ℕ × ℕ) × ℕ)) (e : ℕ) :
    (arcs.getD e defaultArc).1.2 ≤
      (encList (encPair (encPair encUnary encUnary) encNat) arcs).length := by
  rcases h : arcs[e]? with _ | a
  · simp only [List.getD_eq_getElem?_getD, h, Option.getD_none, defaultArc, Nat.zero_le]
  · simp only [List.getD_eq_getElem?_getD, h, Option.getD_some]
    have hmem := length_le_encList_of_mem (encPair (encPair encUnary encUnary) encNat)
      (List.mem_of_getElem? h)
    simp only [length_encPair, encUnary_apply, List.length_replicate] at hmem
    omega

@[fun_prop]
private theorem walkVertices_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {arcs : γ → List ((ℕ × ℕ) × ℕ)} {u : γ → ℕ} {p : γ → List ℕ}
    (harcs : ComputableInPolyTime arcs encIn (encList (encPair (encPair encUnary encUnary) encNat)))
    (hu : ComputableInPolyTime u encIn encUnary)
    (hp : ComputableInPolyTime p encIn (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ walkVertices (arcs x) (u x) (p x)) encIn (encList encUnary) := by
  simp_rw [walkVertices_eq_foldl]
  let encA := encList (encPair (encPair encUnary encUnary) encNat)
  let encAcc := encPair encUnary (encList encUnary)
  have hfold : ComputableInPolyTime
      (fun x ↦ (p x).foldl (fun (acc : ℕ × List ℕ) e ↦
        let nxt := ((arcs x).getD e defaultArc).1.2
        (nxt, acc.2 ++ [nxt])) (u x, [u x])) encIn encAcc := by
    refine foldlWith_of_bounded_growth (encP := encA) (encA := encUnary)
      (encL := encList encUnary) (encB := encAcc)
      (step := fun as (acc : ℕ × List ℕ) e ↦
        let nxt := (as.getD e defaultArc).1.2
        (nxt, acc.2 ++ [nxt]))
      harcs hp (by fun_prop) (by fun_prop)
      (growth := fun x ↦ 4 * (encA (arcs x)).length + 4)
      (((PolyBounded.const 4).mul harcs.polyBounded_length).add (.const 4)) fun x acc e _ ↦ ?_
    have hle : ((arcs x).getD e defaultArc).1.2 ≤ (encA (arcs x)).length :=
      encArcs_node_le (arcs x) e
    simp only [encAcc, length_encPair, encList_append, List.length_append, encList_cons,
      encList_nil, length_frame, encUnary_apply, List.length_replicate, List.length_nil]
    omega
  exact (snd encUnary (encList encUnary)).comp hfold

private theorem dropUntilVertex_eq_foldl (arcs : List ((ℕ × ℕ) × ℕ)) (tgt cur : ℕ) (q : List ℕ) :
    dropUntilVertex arcs tgt cur q =
      (q.foldl (fun (acc : (Bool × ℕ) × List ℕ) e ↦
        if acc.1.1 then ((true, acc.1.2), acc.2 ++ [e])
        else if acc.1.2 = tgt then ((true, acc.1.2), [e])
        else ((false, (arcs.getD e defaultArc).1.2), [])) ((false, cur), [])).2 := by
  have hfound : ∀ (xs : List ℕ) (c : ℕ) (out : List ℕ),
      (xs.foldl (fun (acc : (Bool × ℕ) × List ℕ) e ↦
        if acc.1.1 then ((true, acc.1.2), acc.2 ++ [e])
        else if acc.1.2 = tgt then ((true, acc.1.2), [e])
        else ((false, (arcs.getD e defaultArc).1.2), [])) ((true, c), out)).2 = out ++ xs := by
    intro xs; induction xs with
    | nil => intro c out; simp
    | cons e es ih =>
      intro c out; simp only [List.foldl_cons, ↓reduceIte, ih, List.append_assoc,
        List.singleton_append]
  induction q generalizing cur with
  | nil => rfl
  | cons e es ih =>
    simp only [dropUntilVertex, List.foldl_cons, Bool.false_eq_true, ↓reduceIte]
    split_ifs with h
    · simpa only [List.singleton_append] using (hfound es cur [e]).symm
    · exact ih _

@[fun_prop]
private theorem dropUntilVertex_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {arcs : γ → List ((ℕ × ℕ) × ℕ)} {tgt cur : γ → ℕ} {q : γ → List ℕ}
    (harcs : ComputableInPolyTime arcs encIn (encList (encPair (encPair encUnary encUnary) encNat)))
    (htgt : ComputableInPolyTime tgt encIn encUnary)
    (hcur : ComputableInPolyTime cur encIn encUnary)
    (hq : ComputableInPolyTime q encIn (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ dropUntilVertex (arcs x) (tgt x) (cur x) (q x))
      encIn (encList encUnary) := by
  simp_rw [dropUntilVertex_eq_foldl]
  let encA := encList (encPair (encPair encUnary encUnary) encNat)
  let encP := encPair encA encUnary
  let encAcc := encPair (encPair encBool encUnary) (encList encUnary)
  have hfold := foldlWith_of_bounded_growth (encP := encP) (encA := encUnary)
    (encL := encList encUnary) (encB := encAcc)
    (par := fun x ↦ (arcs x, tgt x)) (list := q) (init := fun x ↦ ((false, cur x), []))
    (step := fun pt (acc : (Bool × ℕ) × List ℕ) e ↦
      if acc.1.1 then ((true, acc.1.2), acc.2 ++ [e])
      else if acc.1.2 = pt.2 then ((true, acc.1.2), [e])
      else ((false, (pt.1.getD e defaultArc).1.2), []))
    (harcs.prod htgt) hq (by fun_prop) (by fun_prop)
    (growth := fun x ↦ 4 * (encA (arcs x)).length + 4 * (encList encUnary (q x)).length + 12)
    ((((PolyBounded.const 4).mul harcs.polyBounded_length).add
      ((PolyBounded.const 4).mul hq.polyBounded_length)).add (.const 12))
    (fun x acc e he ↦ by
      have he_le := length_le_encList_of_mem encUnary he
      have hn_le : ((arcs x).getD e defaultArc).1.2 ≤ (encA (arcs x)).length :=
        encArcs_node_le (arcs x) e
      simp only [encUnary_apply, List.length_replicate] at he_le
      dsimp only
      split_ifs <;>
        simp only [encAcc, length_encPair, encBool_apply, List.length_singleton,
          encUnary_apply, List.length_replicate, encList_append, List.length_append,
          encList_cons, encList_nil, length_frame, List.length_nil] <;>
        omega)
  exact (snd (encPair encBool encUnary) (encList encUnary)).comp hfold

private lemma length_encList_sublist {α : Type} (enc : α ↪ List Bool) :
    ∀ {l₁ l₂ : List α}, l₁.Sublist l₂ → (encList enc l₁).length ≤ (encList enc l₂).length
  | _, _, .slnil => le_rfl
  | _, _, .cons a h => by
    simp only [encList_cons, List.length_append, length_frame]; have :=
      length_encList_sublist enc h; omega
  | _, _, .cons_cons a h => by
    simp only [encList_cons, List.length_append, length_frame]; have :=
      length_encList_sublist enc h; omega

@[fun_prop]
private theorem loopErase_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {arcs : γ → List ((ℕ × ℕ) × ℕ)} {p : γ → List ℕ}
    (harcs : ComputableInPolyTime arcs encIn (encList (encPair (encPair encUnary encUnary) encNat)))
    (hp : ComputableInPolyTime p encIn (encList encUnary)) :
    ComputableInPolyTime (fun x ↦ loopErase (arcs x) (p x)) encIn (encList encUnary) := by
  unfold loopErase
  have hrev : ComputableInPolyTime (fun x ↦ (p x).reverse) encIn (encList encUnary) := by fun_prop
  have hsub_fold : ∀ (as : List ((ℕ × ℕ) × ℕ)) (ls : List ℕ),
      (ls.foldl (loopEraseStep as) []).Sublist ls.reverse := by
    intro as ls; induction ls using List.reverseRecOn with
    | nil => exact List.Sublist.refl []
    | append_singleton xs e ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.reverse_append,
        List.reverse_singleton, List.singleton_append]
      exact (loopEraseStep_sublist as _ e).trans (List.Sublist.cons_cons e ih)
  refine foldlWith (encA := encUnary) (encL := encList encUnary) (encB := encList encUnary)
    (step := loopEraseStep) harcs hrev (const []) (by unfold loopEraseStep; fun_prop)
    (B := fun x ↦ (encList encUnary (p x)).length) hp.polyBounded_length fun x i _ ↦ ?_
  refine length_encList_sublist encUnary ((hsub_fold _ _).trans ?_)
  have : ((p x).reverse.take i).reverse.Sublist (p x).reverse.reverse :=
    List.reverse_sublist.mpr (List.take_sublist i (p x).reverse)
  simpa only [List.reverse_reverse] using this

@[fun_prop]
private theorem betterEntry_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {a b : γ → Option (ℕ × List ℕ)}
    (ha : ComputableInPolyTime a encIn (encOption (encPair encNat (encList encUnary))))
    (hb : ComputableInPolyTime b encIn (encOption (encPair encNat (encList encUnary)))) :
    ComputableInPolyTime (fun x ↦ betterEntry (a x) (b x))
      encIn (encOption (encPair encNat (encList encUnary))) := by
  have heq : ∀ u v : Option (ℕ × List ℕ),
      betterEntry u v = u.elim v fun p₁ ↦ v.elim (some p₁) fun p₂ ↦
        if p₂.1 < p₁.1 then some p₂ else some p₁ := by
    rintro (_ | ⟨c₁, p₁⟩) (_ | ⟨c₂, p₂⟩) <;> rfl
  simp_rw [heq]; fun_prop

private lemma bfEntry_enc_le {q : DigraphQuery} {v k : ℕ} (hk : k ≤ q.numNodes)
    {opt : Option (ℕ × List ℕ)}
    (hopt : ∀ c p, opt = some (c, p) →
      IsArcWalk q.numNodes q.arcs q.src v p ∧ arcWalkCost q.arcs p = c ∧ p.length ≤ k) :
    (encOption (encPair encNat (encList encUnary)) opt).length ≤
      2 * (q.numNodes + 1) * ((encDigraphQuery q).length + 4) + 8 := by
  cases opt with
  | none => simp only [encOption_none, List.length_nil, Nat.zero_le]
  | some cp =>
    rcases cp with ⟨c, p⟩
    obtain ⟨hw, rfl, hplen⟩ := hopt c p rfl
    let L := (encDigraphQuery q).length
    have harcs_le : (encList (encPair (encPair encUnary encUnary) encNat) q.arcs).length ≤ L := by
      change (encList (encPair (encPair encUnary encUnary) encNat) q.arcs).length ≤
        (encDigraphQueryFields (q.numNodes, q.arcs, q.src, q.dst)).length
      simp only [encDigraphQueryFields, length_encPair]
      omega
    have harcs_len : q.arcs.length ≤ L :=
      (length_le_length_encList _ q.arcs).trans harcs_le
    have hp_enc : (encList encUnary p).length ≤ p.length * (2 * L + 1) := by
      refine length_encList_le encUnary p fun e he ↦ ?_
      simp only [encUnary_apply, List.length_replicate]
      exact (hw.arc_lt e he).le.trans harcs_len
    have hcost_bits : (arcWalkCost q.arcs p).bits.length ≤ L + p.length + 1 := by
      rw [← Nat.size_eq_bits_len (arcWalkCost q.arcs p) |>.symm]
      unfold arcWalkCost
      refine (Nat.size_sum_le (b := L) fun w hw' ↦ ?_).trans ?_
      · rcases List.mem_map.mp hw' with ⟨e, he, rfl⟩
        have he_lt := hw.arc_lt e he
        have hmem : q.arcs.getD e defaultArc ∈ q.arcs := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he_lt, Option.getD_some]
          exact q.arcs.getElem_mem he_lt
        have hlen := (length_le_encList_of_mem _ hmem).trans harcs_le
        simp only [length_encPair, encNat_apply, Nat.size_eq_bits_len] at hlen
        omega
      · simp only [List.length_map]
        have := Nat.size_le_self p.length
        omega
    have hpk : p.length ≤ q.numNodes := hplen.trans hk
    simp only [encOption_some, List.length_cons, length_encPair, encNat_apply]
    have hmul : p.length * (2 * L + 1) ≤ q.numNodes * (2 * L + 1) :=
      Nat.mul_le_mul_right _ hpk
    have hfin : 2 * (L + p.length + 1) + 1 + p.length * (2 * L + 1) + 1 ≤
        2 * (q.numNodes + 1) * (L + 4) + 8 := by
      nlinarith
    dsimp only [L] at hcost_bits hp_enc hfin
    omega

private theorem relaxArcStep_polyTime :
    ComputableInPolyTime
      (fun r : ((((ℕ × List ((ℕ × ℕ) × ℕ)) × BFTable) × ℕ) × Option (ℕ × List ℕ)) ×
          (((ℕ × ℕ) × ℕ) × ℕ) ↦
        relaxArcFor r.1.1.1.1.1 r.1.1.2 r.1.1.1.2 r.1.2 r.2)
      (encPair (encPair (encPair (encPair (encPair encUnary
          (encList (encPair (encPair encUnary encUnary) encNat))) encBFTable) encUnary)
        (encOption (encPair encNat (encList encUnary))))
        (encPair (encPair (encPair encUnary encUnary) encNat) encUnary))
      (encOption (encPair encNat (encList encUnary))) := by
  let encE := encOption (encPair encNat (encList encUnary))
  let encAE := encPair (encPair (encPair encUnary encUnary) encNat) encUnary
  let encP0 := encPair (encPair encUnary
    (encList (encPair (encPair encUnary encUnary) encNat))) encBFTable
  let encP := encPair encP0 encUnary
  let encPE := encPair encP encE
  let encAll := encPair encPE encAE
  have hp : ComputableInPolyTime (fun r : _ ↦ r.1.1) encAll encP :=
    (fst encP encE).comp (fst encPE encAE)
  have hp0 : ComputableInPolyTime (fun r : _ ↦ r.1.1.1) encAll encP0 :=
    (fst encP0 encUnary).comp hp
  have hn : ComputableInPolyTime (fun r : _ ↦ r.1.1.1.1.1) encAll encUnary :=
    (fst encUnary _).comp ((fst _ encBFTable).comp hp0)
  have htbl : ComputableInPolyTime (fun r : _ ↦ r.1.1.1.2) encAll encBFTable :=
    (snd _ encBFTable).comp hp0
  have hv : ComputableInPolyTime (fun r : _ ↦ r.1.1.2) encAll encUnary :=
    (snd encP0 encUnary).comp hp
  have hcur : ComputableInPolyTime (fun r : _ ↦ r.1.2) encAll encE :=
    (snd encP encE).comp (fst encPE encAE)
  have hae : ComputableInPolyTime (fun r : _ ↦ r.2) encAll encAE := snd encPE encAE
  have ha1 : ComputableInPolyTime (fun r : _ ↦ r.2.1) encAll
      (encPair (encPair encUnary encUnary) encNat) := (fst _ encUnary).comp hae
  have hau : ComputableInPolyTime (fun r : _ ↦ r.2.1.1.1) encAll encUnary :=
    (fst encUnary encUnary).comp ((fst _ encNat).comp ha1)
  have hav : ComputableInPolyTime (fun r : _ ↦ r.2.1.1.2) encAll encUnary :=
    (snd encUnary encUnary).comp ((fst _ encNat).comp ha1)
  have haw : ComputableInPolyTime (fun r : _ ↦ r.2.1.2) encAll encNat :=
    (snd _ encNat).comp ha1
  have haidx : ComputableInPolyTime (fun r : _ ↦ r.2.2) encAll encUnary :=
    (snd _ encUnary).comp hae
  have hcond : ComputableInPolyTime
      (fun r : _ ↦ decide (r.2.1.1.1 < r.1.1.1.1.1) && (r.2.1.1.2 == r.1.1.2)) encAll encBool := by
    have hbeq : ∀ a b : ℕ, (a == b) = decide (a = b) := fun a b ↦ by by_cases a = b <;> simp [*]
    simp_rw [hbeq]
    exact bool_and' (by fun_prop) (by fun_prop)
  have hget : ComputableInPolyTime (fun r : _ ↦ r.1.1.1.2.getD r.2.1.1.1 none) encAll encE := by
    dsimp only [encE, encBFTable] at htbl ⊢; fun_prop
  have hbody : ComputableInPolyTime
      (fun r : _ ↦ (r.1.1.1.2.getD r.2.1.1.1 none).elim r.1.2 fun cp ↦
        betterEntry r.1.2 (some (cp.1 + r.2.1.2, cp.2 ++ [r.2.2]))) encAll encE := by
    refine optionElimWithInput hget hcur ?_
    let encS := encPair encAll (encPair encNat (encList encUnary))
    have hl := fst encAll (encPair encNat (encList encUnary))
    have hcp := snd encAll (encPair encNat (encList encUnary))
    have hcu := (fst encNat (encList encUnary)).comp hcp
    have hpu := (snd encNat (encList encUnary)).comp hcp
    have hsum := binary_add' hcu (haw.comp hl)
    have hi := haidx.comp hl
    have hmkCand : ∀ {γ : Type} {encIn : γ ↪ List Bool}
        {fc : γ → ℕ} {fp : γ → List ℕ} {fi : γ → ℕ},
        ComputableInPolyTime fc encIn encNat →
        ComputableInPolyTime fp encIn (encList encUnary) →
        ComputableInPolyTime fi encIn encUnary →
        ComputableInPolyTime (fun x ↦ some (fc x, fp x ++ [fi x]))
          encIn (encOption (encPair encNat (encList encUnary))) :=
      fun _ _ _ ↦ by fun_prop
    exact betterEntry_polyTime (hcur.comp hl) (hmkCand hsum hpu hi)
  convert hcond.ite hbody hcur using 1
  funext r
  unfold relaxArcFor; cases r.1.1.1.2.getD r.2.1.1.1 none <;> rfl

private theorem bfRound_polyTime :
    ComputableInPolyTime
      (fun p : (ℕ × List ((ℕ × ℕ) × ℕ)) × BFTable ↦ bfRound p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList (encPair (encPair encUnary encUnary) encNat))) encBFTable)
      encBFTable := by
  let encA := encList (encPair (encPair encUnary encUnary) encNat)
  let encP := encPair (encPair (encPair encUnary encA) encBFTable) encUnary
  let encAE := encPair (encPair (encPair encUnary encUnary) encNat) encUnary
  let encE := encOption (encPair encNat (encList encUnary))
  have hinner : ComputableInPolyTime
      (fun x : ((ℕ × List ((ℕ × ℕ) × ℕ)) × BFTable) × ℕ ↦
        x.1.1.2.zipIdx.foldl (relaxArcFor x.1.1.1 x.2 x.1.2) (x.1.2.getD x.2 none))
      encP encE := by
    have hpa := (fst (encPair encUnary encA) encBFTable).comp (fst _ encUnary)
    have harcs_p : ComputableInPolyTime (fun x : _ ↦ x.1.1.2) encP encA :=
      (snd encUnary encA).comp hpa
    have htbl_p : ComputableInPolyTime (fun x : _ ↦ x.1.2) encP encBFTable :=
      (snd (encPair encUnary encA) encBFTable).comp (fst _ encUnary)
    have hv_p : ComputableInPolyTime (fun x : _ ↦ x.2) encP encUnary := snd _ encUnary
    refine foldlWith (encP := encP) (encA := encAE) (encL := encList encAE) (encB := encE)
      (par := id) (list := fun x ↦ x.1.1.2.zipIdx) (init := fun x ↦ x.1.2.getD x.2 none)
      (step := fun x cur ae ↦ relaxArcFor x.1.1.1 x.2 x.1.2 cur ae)
      id' (by fun_prop) (by dsimp only [encE, encBFTable] at htbl_p ⊢; fun_prop)
      relaxArcStep_polyTime
      (B := fun x ↦ 6 * (encP x).length + 16)
      (((PolyBounded.const 6).mul PolyBounded.self).add (.const 16)) fun x i _ ↦ ?_
    let B₀ := 6 * (encP x).length + 16
    have htbl_le : (encBFTable x.1.2).length ≤ (encP x).length := by
      simp only [encP, length_encPair]; omega
    have harcs_le : (encA x.1.1.2).length ≤ (encP x).length := by
      simp only [encP, length_encPair]; omega
    have hinit_le : (encE (x.1.2.getD x.2 none)).length ≤ B₀ := by
      rcases h : x.1.2[x.2]? with _ | opt
      · simp [List.getD_eq_getElem?_getD, h, encE]
      · simp only [List.getD_eq_getElem?_getD, h, Option.getD_some]
        have := (length_le_encList_of_mem encE (List.mem_of_getElem? h)).trans htbl_le
        dsimp only [B₀]; omega
    have hcand_le : ∀ ae ∈ x.1.1.2.zipIdx, ∀ u < x.1.1.1, ∀ cu pu,
        x.1.2.getD u none = some (cu, pu) →
        (encE (some (cu + ae.1.2, pu ++ [ae.2]))).length ≤ B₀ := by
      intro ae hae u _ cu pu htu
      have hae' := List.mk_mem_zipIdx_iff_getElem?.mp hae
      have he_lt : ae.2 < x.1.1.2.length := (List.getElem?_eq_some_iff.mp hae').1
      have hw_le : ae.1.2.bits.length ≤ (encP x).length := by
        have := (length_le_encList_of_mem _ (List.mem_of_getElem? hae')).trans harcs_le
        simp only [length_encPair, encNat_apply] at this; omega
      have he_le : ae.2 ≤ (encP x).length :=
        he_lt.le.trans ((length_le_length_encList _ x.1.1.2).trans harcs_le)
      have hu_mem : some (cu, pu) ∈ x.1.2 := by
        rcases h : x.1.2[u]? with _ | opt
        · simp [List.getD_eq_getElem?_getD, h] at htu
        · simp only [List.getD_eq_getElem?_getD, h, Option.getD_some] at htu
          exact htu ▸ List.mem_of_getElem? h
      have hu_le := (length_le_encList_of_mem encE hu_mem).trans htbl_le
      simp only [encE, encOption_some, List.length_cons, length_encPair, encNat_apply] at hu_le ⊢
      have hadd : (cu + ae.1.2).bits.length ≤ cu.bits.length + ae.1.2.bits.length + 1 := by
        simpa only [Nat.size_eq_bits_len] using Nat.size_add_le cu ae.1.2
      simp only [encList_append, List.length_append, encList_cons, encList_nil, length_frame,
        encUnary_apply, List.length_replicate, List.length_nil]
      dsimp only [B₀]; omega
    have hfold_bound : ∀ ls : List (((ℕ × ℕ) × ℕ) × ℕ), (∀ ae ∈ ls, ae ∈ x.1.1.2.zipIdx) →
        ∀ cur, (encE cur).length ≤ B₀ →
        (encE (ls.foldl (relaxArcFor x.1.1.1 x.2 x.1.2) cur)).length ≤ B₀ := by
      intro ls hls cur hcur; induction ls generalizing cur with
      | nil => exact hcur
      | cons ae rest ih =>
        refine ih (fun y hy ↦ hls y (List.mem_cons_of_mem ae hy)) _ ?_
        unfold relaxArcFor
        by_cases hc : (ae.1.1.1 < x.1.1.1 && ae.1.1.2 == x.2) = true
        · simp only [hc, ↓reduceIte]
          have hu_lt : ae.1.1.1 < x.1.1.1 :=
            decide_eq_true_eq.mp ((Bool.and_eq_true _ _).mp hc).1
          cases htu : x.1.2.getD ae.1.1.1 none with
          | none => exact hcur
          | some cp =>
            have hnew := hcand_le ae (hls ae List.mem_cons_self) ae.1.1.1 hu_lt cp.1 cp.2 htu
            cases cur with
            | none => exact hnew
            | some c0 =>
              dsimp only [betterEntry]; split_ifs
              · exact hnew
              · exact hcur
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact hcur
    exact hfold_bound _ (fun y hy ↦ List.mem_of_mem_take hy) _ hinit_le
  unfold bfRound
  exact mapWithInput (by fun_prop) hinner

/-- **`shortestSimplePath` is computable in polynomial time.** -/
@[fun_prop]
theorem shortestSimplePath_polyTime :
    ComputableInPolyTime shortestSimplePath encDigraphQuery (encOption (encList encUnary)) := by
  have hrun : ComputableInPolyTime bfRun encDigraphQuery encBFTable := by
    unfold bfRun
    refine (iterateWith_spec
      (par := fun q : DigraphQuery ↦ (q.numNodes, q.arcs))
      (count := DigraphQuery.numNodes)
      (init := fun q ↦ bfInit q.numNodes q.src)
      (step := fun p tbl ↦ bfRound p.1 p.2 tbl)
      (by fun_prop) (by fun_prop) (by unfold bfInit; fun_prop) bfRound_polyTime
      BFInv bfInv_init (fun q _ _ _ h ↦ bfInv_step q h)
      (size := fun q ↦
        q.numNodes * (4 * (q.numNodes + 1) * ((encDigraphQuery q).length + 4) + 17))
      (by
        have hn : PolyBounded (fun q ↦ (encDigraphQuery q).length) DigraphQuery.numNodes :=
          (encDigraphQuery_numNodes_polyTime id').polyBounded
        exact hn.mul ((((PolyBounded.const 4).mul (hn.add (.const 1))).mul
          (PolyBounded.self.add (.const 4))).add (.const 17)))
      (fun q i tbl hi hinv ↦ ?_)).1
    have htbl := length_encList_le (encOption (encPair encNat (encList encUnary))) tbl
      (b := 2 * (q.numNodes + 1) * ((encDigraphQuery q).length + 4) + 8) fun opt hopt ↦ by
        obtain ⟨v, hv, rfl⟩ := List.getElem_of_mem hopt
        refine bfEntry_enc_le (v := v) hi fun c p hcp ↦
          hinv.2.1 v (hinv.1 ▸ hv) c p ?_
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]
          using hcp
    rw [hinv.1] at htbl
    refine htbl.trans (Nat.mul_le_mul_left q.numNodes (by nlinarith))
  unfold shortestSimplePath
  have hmap : ∀ (arcs : List ((ℕ × ℕ) × ℕ)) (o : Option (ℕ × List ℕ)),
      o.map (fun cp ↦ loopErase arcs cp.2) = o.elim none fun cp ↦ some (loopErase arcs cp.2) := by
    rintro _ (_ | _) <;> rfl
  simp_rw [hmap]
  fun_prop

private theorem shortestSimplePath_sample :
    let q : DigraphQuery := ⟨3, [((0, 2), 10), ((0, 1), 3), ((1, 2), 4), ((1, 1), 0)], 0, 2⟩
    shortestSimplePath q = some [1, 2] ∧
      arcWalkCost q.arcs [1, 2] = 7 ∧
      shortestSimplePath ⟨3, [((0, 1), 2)], 0, 2⟩ = none := by
  decide

end PolyTime

end CslibFrontier.Algorithms.ShortestSimplePath
