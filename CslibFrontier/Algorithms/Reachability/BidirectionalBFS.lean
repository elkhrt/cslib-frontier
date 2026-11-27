/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Bidirectional Breadth-First Search and Greedy Alternation

This module develops the mathematical theory of layer-by-layer breadth-first search (BFS),
bidirectional BFS with arbitrary alternation strategies, and the greedy alternation strategy on
finite simple graphs under standard Lean axioms.

Given a finite simple graph `G` and source vertex `s`, the `k`-th BFS layer consists of the
vertices at graph distance `k` from `s`, generated iteratively by expanding neighbors of layer `k`
not appearing in earlier layers. Expanding layer `k` inspects all incident edges, incurring
degree-sum cost `∑ v ∈ bfsLayer G s k, G.degree v`.

A bidirectional BFS between `s` and `t` maintains forward frontier index `i` and backward frontier
index `j`, advancing one frontier at a time according to an alternation strategy until either the
explored balls intersect (certifying `G.dist s t = i + j`) or one frontier becomes empty
(certifying `¬ G.Reachable s t`). The greedy alternation strategy always expands whichever current
frontier has smaller degree-sum cost. Its total edge-exploration cost is at most `G.dist s t` (and
hence at most `G.diam` on connected graphs) times the cost of any alternation strategy for
reachable pairs, and at most `(maxComponentDiam G + 1)` times the cost of any alternation strategy
for unreachable pairs.

## Main definitions

* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bfsLayer`: the `k`-th BFS layer from `s`.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bfsVisited`: vertices discovered within
  the first `k` exploration steps.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bfsLayerCost`: sum of vertex degrees in
  the `k`-th BFS layer.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bfsPrefixCost`: total edge-exploration
  cost of expanding layers `0.. k-1`.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.AlternationStrategy`: decision rule
  `(i, j) ↦ Bool` choosing whether to expand the forward (`true`) or backward (`false`) frontier.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.greedyAlternation`: Borassi–Natale greedy
  alternation strategy expanding the frontier of smaller degree-sum cost.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bidirState`: frontier pair `(i, j)` after
  `m` bidirectional BFS steps.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bidirStopStep`: number of steps until
  bidirectional BFS terminates.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bidirTerminal`: terminal frontier pair
  `(i, j)` of bidirectional BFS.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bidirExploredEdges`: total edges explored
  by bidirectional BFS.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.maxComponentDiam`: maximum finite graph
  distance across all components.

## Main results

* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.mem_bfsLayer_succ_iff`: each BFS layer is
  the unvisited neighborhood of the preceding layer.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bfsVisited_inter_nonempty_iff`: forward
  and backward visited sets touch at `(i, j)` iff `G.Reachable s t` and `G.dist s t ≤ i + j`.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bidirStopStep_eq_dist`: for reachable
  `s, t`, every alternation strategy terminates in `G.dist s t` steps and certifies `G.dist s t`.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bidirExploredEdges_greedy_le_dist_mul`:
  for reachable `s, t`, greedy bidirectional BFS explores at most `G.dist s t` times as many edges
  as any alternation strategy.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bidirExploredEdges_greedy_le_diam_mul`:
  on a graph with `G.Connected` (or reachable `s, t` with `G.ediam ≠ ⊤`), greedy bidirectional BFS
  explores at most `G.diam` times as many edges as any alternation strategy.
* `CslibFrontier.Algorithms.Reachability.BidirectionalBFS.bidirExploredEdges_greedy_le_unreach`:
  for unreachable `s, t`, greedy bidirectional BFS terminates certifying unreachability and
  explores at most `(maxComponentDiam G + 2)` times as many edges as any alternation strategy.
-/

public section

namespace CslibFrontier.Algorithms.Reachability.BidirectionalBFS

open Finset

section Layers

variable {V : Type*} [Fintype V]

/-- The `k`-th breadth-first search layer from `s` in a finite simple graph `G`, consisting of all
reachable vertices at graph distance `k` from `s`. -/
noncomputable def bfsLayer (G : _root_.SimpleGraph V) (s : V) (k : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ G.Reachable s v ∧ G.dist s v = k

/-- Membership in `bfsLayer G s k` holds iff `v` is reachable from `s` at distance `k`. -/
theorem mem_bfsLayer_iff {G : _root_.SimpleGraph V} {s v : V} {k : ℕ} :
    v ∈ bfsLayer G s k ↔ G.Reachable s v ∧ G.dist s v = k := by
  classical
  simp [bfsLayer]

/-- The `0`-th BFS layer from `s` is the singleton `{s}`. -/
@[simp]
theorem bfsLayer_zero (G : _root_.SimpleGraph V) (s : V) :
    bfsLayer G s 0 = {s} := by
  ext v
  rw [mem_bfsLayer_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hd⟩
    exact ((G.dist_eq_zero_iff_eq_or_not_reachable).mp hd).resolve_right (not_not.mpr hr) |>.symm
  · rintro rfl
    exact ⟨.refl _, _root_.SimpleGraph.dist_self⟩

/-- Distinct BFS layers from the same source are disjoint. -/
theorem disjoint_bfsLayer (G : _root_.SimpleGraph V) (s : V) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (bfsLayer G s j) (bfsLayer G s k) := by
  rw [Finset.disjoint_left]
  intro v hvj hvk
  rw [mem_bfsLayer_iff] at hvj hvk
  exact hjk (hvj.2.symm.trans hvk.2)

/-- The set of vertices discovered by BFS from `s` up to and including layer `k`, i.e., all
reachable vertices at graph distance at most `k` from `s`. -/
noncomputable def bfsVisited (G : _root_.SimpleGraph V) (s : V) (k : ℕ) : Finset V := by
  classical
  exact (Finset.range (k + 1)).biUnion (bfsLayer G s)

/-- Membership in `bfsVisited G s k` holds iff `v` is reachable from `s` with `G.dist s v ≤ k`. -/
theorem mem_bfsVisited_iff {G : _root_.SimpleGraph V} {s v : V} {k : ℕ} :
    v ∈ bfsVisited G s k ↔ G.Reachable s v ∧ G.dist s v ≤ k := by
  classical
  simp only [bfsVisited, Finset.mem_biUnion, Finset.mem_range, mem_bfsLayer_iff]
  constructor
  · rintro ⟨j, hj, hr, rfl⟩
    exact ⟨hr, Nat.lt_succ_iff.mp hj⟩
  · rintro ⟨hr, hd⟩
    exact ⟨G.dist s v, Nat.lt_succ_of_le hd, hr, rfl⟩

/-- At step `0`, the visited set is `{s}`. -/
@[simp]
theorem bfsVisited_zero (G : _root_.SimpleGraph V) (s : V) :
    bfsVisited G s 0 = {s} := by
  ext v
  rw [mem_bfsVisited_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hd⟩
    have hd0 : G.dist s v = 0 := Nat.eq_zero_of_le_zero hd
    exact ((G.dist_eq_zero_iff_eq_or_not_reachable).mp hd0).resolve_right (not_not.mpr hr) |>.symm
  · rintro rfl
    exact ⟨.refl _, by simp⟩

/-- Visited sets grow monotonically with the layer index. -/
@[gcongr]
theorem bfsVisited_mono (G : _root_.SimpleGraph V) (s : V) {j k : ℕ} (hjk : j ≤ k) :
    bfsVisited G s j ⊆ bfsVisited G s k := by
  intro v hv
  rw [mem_bfsVisited_iff] at hv ⊢
  exact ⟨hv.1, hv.2.trans hjk⟩

/-- Each BFS layer `k` is contained in `bfsVisited G s k`. -/
theorem bfsLayer_subset_bfsVisited (G : _root_.SimpleGraph V) (s : V) (k : ℕ) :
    bfsLayer G s k ⊆ bfsVisited G s k := by
  intro v hv
  rw [mem_bfsLayer_iff] at hv
  rw [mem_bfsVisited_iff]
  exact ⟨hv.1, hv.2.le⟩

omit [Fintype V] in
/-- Split a walk `p` at step `a ≤ p.length` into a prefix of length `a` and a suffix of length
`p.length - a`. -/
private lemma walk_split {G : _root_.SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v) (a : ℕ), a ≤ p.length →
      ∃ w : V, (∃ q₁ : G.Walk u w, q₁.length = a) ∧
        (∃ q₂ : G.Walk w v, q₂.length = p.length - a)
  | u, _, .nil, 0, _ => ⟨u, ⟨.nil, rfl⟩, ⟨.nil, rfl⟩⟩
  | _, _, .nil, _ + 1, ha => absurd ha (by simp)
  | u, v, .cons h p, 0, _ => ⟨u, ⟨.nil, rfl⟩, ⟨.cons h p, rfl⟩⟩
  | _, _, .cons h p, a + 1, ha => by
      have ha' : a ≤ p.length := Nat.le_of_succ_le_succ ha
      obtain ⟨w, ⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩ := walk_split p a ha'
      exact ⟨w, ⟨.cons h q₁, by simp [hq₁]⟩, ⟨q₂, by simp [hq₂]⟩⟩

/-- BFS exploration step characterization: a vertex `w` belongs to layer `k + 1` if and only if
`w` is adjacent to some vertex in layer `k` and does not belong to any earlier layer `0, ..., k`. -/
theorem mem_bfsLayer_succ_iff (G : _root_.SimpleGraph V) (s w : V) (k : ℕ) :
    w ∈ bfsLayer G s (k + 1) ↔
      (∃ v ∈ bfsLayer G s k, G.Adj v w) ∧ w ∉ bfsVisited G s k := by
  rw [mem_bfsLayer_iff, mem_bfsVisited_iff]
  constructor
  · rintro ⟨hr, hd⟩
    refine ⟨?_, fun ⟨_, hle⟩ ↦ by omega⟩
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    rw [hd] at hp
    have hrev : p.reverse.length = k + 1 := by simp [hp]
    cases hpr : p.reverse with
    | nil => simp [hpr] at hrev
    | cons hadj q =>
      rename_i v
      simp only [hpr, _root_.SimpleGraph.Walk.length_cons, Nat.add_right_cancel_iff] at hrev
      have hqlen : q.reverse.length = k := by simp [hrev]
      have hr_sv : G.Reachable s v := q.reverse.reachable
      have hdist_le : G.dist s v ≤ k := hqlen ▸ G.dist_le q.reverse
      have hdist_ge : k ≤ G.dist s v := by
        obtain ⟨pv, hpv⟩ := hr_sv.exists_walk_length_eq_dist
        have htri := G.dist_le (pv.concat hadj.symm)
        rw [_root_.SimpleGraph.Walk.length_concat, hpv, hd] at htri
        omega
      exact ⟨v, mem_bfsLayer_iff.mpr ⟨hr_sv, le_antisymm hdist_le hdist_ge⟩, hadj.symm⟩
  · rintro ⟨⟨v, hv, hadj⟩, hnot⟩
    obtain ⟨hrv, hdv⟩ := mem_bfsLayer_iff.mp hv
    have hrw : G.Reachable s w := hrv.trans hadj.reachable
    have hnotle : ¬ G.dist s w ≤ k := fun hle ↦ hnot ⟨hrw, hle⟩
    have hupper : G.dist s w ≤ k + 1 := by
      obtain ⟨pv, hpv⟩ := hrv.exists_walk_length_eq_dist
      have htri := G.dist_le (pv.concat hadj)
      rw [_root_.SimpleGraph.Walk.length_concat, hpv, hdv] at htri
      exact htri
    exact ⟨hrw, by omega⟩

/-- Every vertex in `bfsLayer G s (k + 1)` has a neighbor in `bfsLayer G s k`. -/
theorem exists_adj_mem_bfsLayer_of_mem_succ {G : _root_.SimpleGraph V} {s w : V} {k : ℕ}
    (hw : w ∈ bfsLayer G s (k + 1)) :
    ∃ v ∈ bfsLayer G s k, G.Adj v w :=
  ((mem_bfsLayer_succ_iff G s w k).mp hw).1

/-- If a BFS layer `k` is empty, all subsequent layers `j ≥ k` are empty. -/
theorem bfsLayer_eq_empty_of_le {G : _root_.SimpleGraph V} {s : V} {k j : ℕ}
    (hempty : bfsLayer G s k = ∅) (hkj : k ≤ j) :
    bfsLayer G s j = ∅ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  clear hkj
  induction d with
  | zero => exact hempty
  | succ d ih =>
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Nat.add_succ] at hw
    obtain ⟨v, hv, _⟩ := exists_adj_mem_bfsLayer_of_mem_succ hw
    rw [ih] at hv
    exact Finset.notMem_empty v hv

/-- Any nonempty BFS layer has index at most `Fintype.card V - 1`. -/
theorem le_card_sub_one_of_bfsLayer_nonempty {G : _root_.SimpleGraph V} {s : V} {k : ℕ}
    (hne : (bfsLayer G s k).Nonempty) :
    k ≤ Fintype.card V - 1 := by
  obtain ⟨v, hv⟩ := hne
  rw [mem_bfsLayer_iff] at hv
  obtain ⟨p, hp_path, hp_len⟩ := hv.1.exists_path_of_dist
  have hsup := hp_path.length_lt
  omega

/-- Layer `Fintype.card V` is always empty. -/
theorem bfsLayer_card_eq_empty (G : _root_.SimpleGraph V) (s : V) :
    bfsLayer G s (Fintype.card V) = ∅ := by
  by_contra hne
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hle := le_card_sub_one_of_bfsLayer_nonempty ⟨v, hv⟩
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

/-- If `s` and `t` are reachable and `k ≤ G.dist s t`, then `bfsLayer G s k` is nonempty. -/
theorem bfsLayer_nonempty_of_le_dist {G : _root_.SimpleGraph V} {s t : V} {k : ℕ}
    (hr : G.Reachable s t) (hk : k ≤ G.dist s t) :
    (bfsLayer G s k).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hempty := bfsLayer_eq_empty_of_le hne hk
  have ht : t ∈ bfsLayer G s (G.dist s t) := mem_bfsLayer_iff.mpr ⟨hr, rfl⟩
  rw [hempty] at ht
  exact Finset.notMem_empty t ht

/-- Forward and backward BFS visited sets touch at `(i, j)` iff `s` and `t` are reachable with
`G.dist s t ≤ i + j`. -/
theorem bfsVisited_inter_nonempty_iff (G : _root_.SimpleGraph V) (s t : V) (i j : ℕ) :
    (∃ w, w ∈ bfsVisited G s i ∧ w ∈ bfsVisited G t j) ↔
      G.Reachable s t ∧ G.dist s t ≤ i + j := by
  constructor
  · rintro ⟨w, hws, hwt⟩
    rw [mem_bfsVisited_iff] at hws hwt
    rcases hws with ⟨hrs, hds⟩
    rcases hwt with ⟨hrt, hdt⟩
    refine ⟨hrs.trans hrt.symm, ?_⟩
    obtain ⟨p₁, hp₁⟩ := hrs.exists_walk_length_eq_dist
    obtain ⟨p₂, hp₂⟩ := hrt.exists_walk_length_eq_dist
    have hle := G.dist_le (p₁.append p₂.reverse)
    rw [_root_.SimpleGraph.Walk.length_append, _root_.SimpleGraph.Walk.length_reverse, hp₁,
      hp₂] at hle
    omega
  · rintro ⟨hr, hij⟩
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    set a := min i p.length
    obtain ⟨w, ⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩ := walk_split p a (Nat.min_le_right i p.length)
    refine ⟨w, mem_bfsVisited_iff.mpr ⟨q₁.reachable, ?_⟩,
      mem_bfsVisited_iff.mpr ⟨q₂.reverse.reachable, ?_⟩⟩
    · exact (G.dist_le q₁).trans (hq₁.le.trans (Nat.min_le_left i p.length))
    · calc G.dist t w ≤ q₂.reverse.length := G.dist_le _
        _ = p.length - a := by rw [_root_.SimpleGraph.Walk.length_reverse, hq₂]
        _ ≤ j := by omega

/-- Degree-sum cost of expanding BFS layer `k` from `s`: `c^s_k = ∑ v ∈ L^s_k, deg(v)`. -/
noncomputable def bfsLayerCost (G : _root_.SimpleGraph V) (s : V) (k : ℕ) : ℕ := by
  classical
  exact ∑ v ∈ bfsLayer G s k, G.degree v

/-- Cumulative edge-exploration cost of expanding the first `k` layers `L^s_0, ..., L^s_{k-1}`. -/
noncomputable def bfsPrefixCost (G : _root_.SimpleGraph V) (s : V) (k : ℕ) : ℕ :=
  ∑ a ∈ Finset.range k, bfsLayerCost G s a

/-- Exploring zero layers incurs zero edge cost. -/
@[simp]
theorem bfsPrefixCost_zero (G : _root_.SimpleGraph V) (s : V) :
    bfsPrefixCost G s 0 = 0 := by
  simp [bfsPrefixCost]

/-- Exploring `k + 1` layers adds `bfsLayerCost G s k` to `bfsPrefixCost G s k`. -/
@[simp]
theorem bfsPrefixCost_succ (G : _root_.SimpleGraph V) (s : V) (k : ℕ) :
    bfsPrefixCost G s (k + 1) = bfsPrefixCost G s k + bfsLayerCost G s k :=
  Finset.sum_range_succ _ k

/-- Prefix exploration cost is monotone in the number of explored layers. -/
@[gcongr]
theorem bfsPrefixCost_mono (G : _root_.SimpleGraph V) (s : V) {j k : ℕ} (hjk : j ≤ k) :
    bfsPrefixCost G s j ≤ bfsPrefixCost G s k :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hjk)

/-- Any individual explored layer's cost is bounded by the prefix cost. -/
theorem bfsLayerCost_le_bfsPrefixCost (G : _root_.SimpleGraph V) (s : V) {a k : ℕ} (hak : a < k) :
    bfsLayerCost G s a ≤ bfsPrefixCost G s k :=
  Finset.single_le_sum (f := bfsLayerCost G s) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr hak)

/-- Since distinct BFS layers are disjoint, the prefix cost over layers `0 .. k-1` equals the sum
of degrees over `bfsVisited G s (k - 1)` when `k ≥ 1`. -/
theorem bfsPrefixCost_succ_eq_sum_visited (G : _root_.SimpleGraph V) (s : V) (k : ℕ) :
    bfsPrefixCost G s (k + 1) = by
      classical
      exact ∑ v ∈ bfsVisited G s k, G.degree v := by
  classical
  simp only [bfsPrefixCost, bfsVisited, bfsLayerCost]
  symm
  refine Finset.sum_biUnion ?_
  intro a _ b _ hab
  exact disjoint_bfsLayer G s hab

/-- Maximum finite distance between reachable vertices in `G`, i.e., the maximum diameter among all
connected components of `G`. -/
noncomputable def maxComponentDiam (G : _root_.SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ (α := V × V)).sup fun p ↦ G.dist p.1 p.2

/-- Every pair of vertices satisfies `G.dist u v ≤ maxComponentDiam G`. -/
theorem dist_le_maxComponentDiam (G : _root_.SimpleGraph V) (u v : V) :
    G.dist u v ≤ maxComponentDiam G := by
  classical
  exact Finset.le_sup (f := fun p : V × V ↦ G.dist p.1 p.2) (Finset.mem_univ (u, v))

/-- Universal upper-bound elimination for `maxComponentDiam`: if every reachable pair has distance
at most `D`, then `maxComponentDiam G ≤ D`. -/
theorem maxComponentDiam_le {G : _root_.SimpleGraph V} {D : ℕ}
    (h : ∀ u v : V, G.Reachable u v → G.dist u v ≤ D) :
    maxComponentDiam G ≤ D := by
  classical
  refine Finset.sup_le fun p _ ↦ ?_
  by_cases hr : G.Reachable p.1 p.2
  · exact h p.1 p.2 hr
  · rw [_root_.SimpleGraph.dist_eq_zero_of_not_reachable hr]; exact Nat.zero_le D

/-- Every BFS layer of index strictly greater than `maxComponentDiam G` is empty. -/
theorem bfsLayer_eq_empty_of_gt_maxComponentDiam {G : _root_.SimpleGraph V} {s : V} {k : ℕ}
    (hk : maxComponentDiam G < k) :
    bfsLayer G s k = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  have h1 := (mem_bfsLayer_iff.mp hv).2
  have h2 := dist_le_maxComponentDiam G s v
  omega

/-- Bounding a layer's edge cost by the degree sum over any superset `S ⊇ bfsLayer G s k`. -/
theorem bfsLayerCost_le_sum_of_subset {G : _root_.SimpleGraph V} {s : V} {k : ℕ} {S : Finset V}
    (hsub : bfsLayer G s k ⊆ S) :
    bfsLayerCost G s k ≤ by classical exact ∑ v ∈ S, G.degree v := by
  classical
  exact Finset.sum_le_sum_of_subset hsub

/-- Whenever `G.ediam ≠ ⊤` (in particular when `G.Connected`), `maxComponentDiam G = G.diam`. -/
theorem maxComponentDiam_eq_diam {G : _root_.SimpleGraph V} (h : G.ediam ≠ ⊤) :
    maxComponentDiam G = G.diam := by
  classical
  apply le_antisymm
  · exact Finset.sup_le fun p _ ↦ G.dist_le_diam h
  · rcases isEmpty_or_nonempty V with hE | hN
    · simp [_root_.SimpleGraph.diam, _root_.SimpleGraph.ediam]
    · obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
      rw [← huv]
      exact dist_le_maxComponentDiam G u v

/-- Any nonempty BFS layer has index at most `maxComponentDiam G`. -/
theorem le_maxComponentDiam_of_bfsLayer_nonempty {G : _root_.SimpleGraph V} {s : V} {k : ℕ}
    (hne : (bfsLayer G s k).Nonempty) :
    k ≤ maxComponentDiam G := by
  obtain ⟨v, hv⟩ := hne
  rw [mem_bfsLayer_iff] at hv
  rw [← hv.2]
  exact dist_le_maxComponentDiam G s v

/-- Layer `maxComponentDiam G + 1` is always empty. -/
theorem bfsLayer_maxComponentDiam_succ_eq_empty (G : _root_.SimpleGraph V) (s : V) :
    bfsLayer G s (maxComponentDiam G + 1) = ∅ := by
  by_contra hne
  have := le_maxComponentDiam_of_bfsLayer_nonempty (Finset.nonempty_iff_ne_empty.mpr hne)
  omega

end Layers

section Bidirectional

variable {V : Type*} [Fintype V]

/-- An alternation strategy maps the current frontier indices `(i, j)` of the forward and backward
searches to `true` (expand forward layer `L^s_i`) or `false` (expand backward layer `L^t_j`). -/
abbrev AlternationStrategy := ℕ × ℕ → Bool

/-- The Borassi–Natale greedy alternation strategy: expand the forward layer `L^s_i` if
`c^s_i ≤ c^t_j`, and expand the backward layer `L^t_j` otherwise. -/
noncomputable def greedyAlternation (G : _root_.SimpleGraph V) (s t : V) : AlternationStrategy :=
  fun p ↦ decide (bfsLayerCost G s p.1 ≤ bfsLayerCost G t p.2)

/-- The greedy strategy chooses forward iff `bfsLayerCost G s i ≤ bfsLayerCost G t j`. -/
@[simp]
theorem greedyAlternation_eq_true_iff (G : _root_.SimpleGraph V) (s t : V) (i j : ℕ) :
    greedyAlternation G s t (i, j) = true ↔ bfsLayerCost G s i ≤ bfsLayerCost G t j :=
  decide_eq_true_iff

/-- The greedy strategy chooses backward iff `bfsLayerCost G t j < bfsLayerCost G s i`. -/
@[simp]
theorem greedyAlternation_eq_false_iff (G : _root_.SimpleGraph V) (s t : V) (i j : ℕ) :
    greedyAlternation G s t (i, j) = false ↔ bfsLayerCost G t j < bfsLayerCost G s i := by
  simp [greedyAlternation]

/-- Termination predicate for bidirectional BFS at state `(i, j)`: either the forward and backward
search spaces share a vertex, or one of the current frontiers is empty (certifying that `s` and `t`
lie in distinct connected components). -/
@[expose]
def BidirDone (G : _root_.SimpleGraph V) (s t : V) (p : ℕ × ℕ) : Prop :=
  (∃ w, w ∈ bfsVisited G s p.1 ∧ w ∈ bfsVisited G t p.2) ∨
    bfsLayer G s p.1 = ∅ ∨ bfsLayer G t p.2 = ∅

/-- Frontier state `(i, j)` after `m` exploration steps under alternation strategy `strat`. -/
@[expose]
def bidirState (strat : AlternationStrategy) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 =>
    let p := bidirState strat m
    if strat p then (p.1 + 1, p.2) else (p.1, p.2 + 1)

/-- At step `0`, bidirectional BFS starts at frontier pair `(0, 0)`. -/
@[simp]
theorem bidirState_zero (strat : AlternationStrategy) : bidirState strat 0 = (0, 0) := by
  rfl

/-- After `m` steps, the sum of explored forward and backward layers equals `m`. -/
theorem bidirState_add (strat : AlternationStrategy) (m : ℕ) :
    (bidirState strat m).1 + (bidirState strat m).2 = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [bidirState]
    split_ifs <;> dsimp <;> omega

/-- Forward frontier index is monotone in the step count. -/
theorem bidirState_fst_mono (strat : AlternationStrategy) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    (bidirState strat m₁).1 ≤ (bidirState strat m₂).1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    rw [Nat.add_succ]
    simp only [bidirState]
    split_ifs <;> dsimp <;> omega

/-- Backward frontier index is monotone in the step count. -/
theorem bidirState_snd_mono (strat : AlternationStrategy) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    (bidirState strat m₁).2 ≤ (bidirState strat m₂).2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    rw [Nat.add_succ]
    simp only [bidirState]
    split_ifs <;> dsimp <;> omega

/-- Bidirectional BFS always satisfies `BidirDone` within `2 * Fintype.card V` steps. -/
theorem exists_bidirDone (G : _root_.SimpleGraph V) (s t : V) (strat : AlternationStrategy) :
    ∃ m, BidirDone G s t (bidirState strat m) := by
  refine ⟨2 * Fintype.card V, ?_⟩
  have hsum := bidirState_add strat (2 * Fintype.card V)
  rcases le_or_gt (Fintype.card V) (bidirState strat (2 * Fintype.card V)).1 with h1 | h1
  · exact Or.inr (Or.inl (bfsLayer_eq_empty_of_le (bfsLayer_card_eq_empty G s) h1))
  · have h2 : Fintype.card V ≤ (bidirState strat (2 * Fintype.card V)).2 := by omega
    exact Or.inr (Or.inr (bfsLayer_eq_empty_of_le (bfsLayer_card_eq_empty G t) h2))

/-- Stopping step of bidirectional BFS: the least `m` at which `BidirDone` holds. -/
noncomputable def bidirStopStep (G : _root_.SimpleGraph V) (s t : V)
    (strat : AlternationStrategy) : ℕ := by
  classical
  exact Nat.find (exists_bidirDone G s t strat)

/-- Terminal frontier pair `(i, j)` when bidirectional BFS stops. -/
@[expose]
noncomputable def bidirTerminal (G : _root_.SimpleGraph V) (s t : V)
    (strat : AlternationStrategy) : ℕ × ℕ :=
  bidirState strat (bidirStopStep G s t strat)

/-- Total number of edges explored (sum of degrees across all expanded forward and backward layers)
by bidirectional BFS under strategy `strat`. -/
@[expose]
noncomputable def bidirExploredEdges (G : _root_.SimpleGraph V) (s t : V)
    (strat : AlternationStrategy) : ℕ :=
  let p := bidirTerminal G s t strat
  bfsPrefixCost G s p.1 + bfsPrefixCost G t p.2

/-- `BidirDone` holds at the terminal state `bidirTerminal G s t strat`. -/
theorem bidirDone_terminal (G : _root_.SimpleGraph V) (s t : V) (strat : AlternationStrategy) :
    BidirDone G s t (bidirTerminal G s t strat) := by
  classical
  exact Nat.find_spec (exists_bidirDone G s t strat)

/-- `bidirStopStep` is bounded by any step at which `BidirDone` holds. -/
theorem bidirStopStep_le {G : _root_.SimpleGraph V} {s t : V} {strat : AlternationStrategy}
    {m : ℕ} (h : BidirDone G s t (bidirState strat m)) :
    bidirStopStep G s t strat ≤ m := by
  classical
  exact Nat.find_min' (exists_bidirDone G s t strat) h

/-- Before `bidirStopStep`, `BidirDone` does not hold. -/
theorem not_bidirDone_of_lt {G : _root_.SimpleGraph V} {s t : V} {strat : AlternationStrategy}
    {m : ℕ} (hm : m < bidirStopStep G s t strat) :
    ¬ BidirDone G s t (bidirState strat m) := by
  classical
  exact Nat.find_min (exists_bidirDone G s t strat) hm

/-- Every forward layer `a < (bidirTerminal G s t strat).1` was chosen for expansion at some step
`m < bidirStopStep G s t strat` with `bidirState strat m = (a, b)` and
`b ≤ (bidirTerminal G s t strat).2`. -/
theorem exists_step_of_lt_terminal_fst (G : _root_.SimpleGraph V) (s t : V)
    (strat : AlternationStrategy) {a : ℕ} (ha : a < (bidirTerminal G s t strat).1) :
    ∃ m < bidirStopStep G s t strat,
      (bidirState strat m).1 = a ∧
      (bidirState strat m).2 ≤ (bidirTerminal G s t strat).2 ∧
      strat (bidirState strat m) = true := by
  have haux : ∀ k, a < (bidirState strat k).1 →
      ∃ m < k, (bidirState strat m).1 = a ∧ strat (bidirState strat m) = true := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rcases lt_or_ge a (bidirState strat k).1 with hlt | hge
      · obtain ⟨m, hmk, hma, hst⟩ := ih hlt
        exact ⟨m, Nat.lt_succ_of_lt hmk, hma, hst⟩
      · simp only [bidirState] at hk
        cases hst : strat (bidirState strat k)
        · rw [hst] at hk
          dsimp at hk
          omega
        · rw [hst] at hk
          dsimp at hk
          exact ⟨k, Nat.lt_succ_self k, by omega, hst⟩
  obtain ⟨m, hm, hma, hst⟩ := haux (bidirStopStep G s t strat) ha
  exact ⟨m, hm, hma, bidirState_snd_mono strat hm.le, hst⟩

/-- Every backward layer `b < (bidirTerminal G s t strat).2` was chosen for expansion at some step
`m < bidirStopStep G s t strat` with `bidirState strat m = (a, b)` and
`a ≤ (bidirTerminal G s t strat).1`. -/
theorem exists_step_of_lt_terminal_snd (G : _root_.SimpleGraph V) (s t : V)
    (strat : AlternationStrategy) {b : ℕ} (hb : b < (bidirTerminal G s t strat).2) :
    ∃ m < bidirStopStep G s t strat,
      (bidirState strat m).2 = b ∧
      (bidirState strat m).1 ≤ (bidirTerminal G s t strat).1 ∧
      strat (bidirState strat m) = false := by
  have haux : ∀ k, b < (bidirState strat k).2 →
      ∃ m < k, (bidirState strat m).2 = b ∧ strat (bidirState strat m) = false := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rcases lt_or_ge b (bidirState strat k).2 with hlt | hge
      · obtain ⟨m, hmk, hmb, hst⟩ := ih hlt
        exact ⟨m, Nat.lt_succ_of_lt hmk, hmb, hst⟩
      · simp only [bidirState] at hk
        cases hst : strat (bidirState strat k)
        · rw [hst] at hk
          dsimp at hk
          exact ⟨k, Nat.lt_succ_self k, by omega, hst⟩
        · rw [hst] at hk
          dsimp at hk
          omega
  obtain ⟨m, hm, hmb, hst⟩ := haux (bidirStopStep G s t strat) hb
  exact ⟨m, hm, hmb, bidirState_fst_mono strat hm.le, hst⟩

/-- For reachable vertices `s` and `t`, bidirectional BFS under any alternation strategy terminates
in exactly `G.dist s t` steps, so `(bidirTerminal G s t strat).1 + (bidirTerminal G s t strat).2`
recovers the exact shortest-path distance `G.dist s t`. -/
theorem bidirStopStep_eq_dist {G : _root_.SimpleGraph V} {s t : V} (hr : G.Reachable s t)
    (strat : AlternationStrategy) :
    bidirStopStep G s t strat = G.dist s t := by
  apply le_antisymm
  · refine bidirStopStep_le (Or.inl ?_)
    exact (bfsVisited_inter_nonempty_iff G s t _ _).mpr ⟨hr, (bidirState_add strat _).ge⟩
  · by_contra hlt
    push Not at hlt
    have hdone := bidirDone_terminal G s t strat
    have hsum : (bidirTerminal G s t strat).1 + (bidirTerminal G s t strat).2 =
        bidirStopStep G s t strat := bidirState_add strat _
    rcases hdone with hinter | hemp | hemp
    · have hne := (bfsVisited_inter_nonempty_iff G s t _ _).mp hinter
      omega
    · have hle : (bidirTerminal G s t strat).1 ≤ G.dist s t := by omega
      exact (bfsLayer_nonempty_of_le_dist hr hle).ne_empty hemp
    · have hle : (bidirTerminal G s t strat).2 ≤ G.dist s t := by omega
      have hd : G.dist t s = G.dist s t := _root_.SimpleGraph.dist_comm
      exact (bfsLayer_nonempty_of_le_dist hr.symm (hd ▸ hle)).ne_empty hemp

/-- Exact reachability and shortest-path correctness of bidirectional BFS: the forward and backward
visited sets intersect at termination iff `G.Reachable s t`, and when they do, the sum of terminal
frontier indices equals `G.dist s t`. -/
theorem bidirTerminal_inter_iff_reachable (G : _root_.SimpleGraph V) (s t : V)
    (strat : AlternationStrategy) :
    (∃ w, w ∈ bfsVisited G s (bidirTerminal G s t strat).1 ∧
      w ∈ bfsVisited G t (bidirTerminal G s t strat).2) ↔ G.Reachable s t := by
  constructor
  · intro hinter
    exact ((bfsVisited_inter_nonempty_iff G s t _ _).mp hinter).1
  · intro hr
    have hstep := bidirStopStep_eq_dist hr strat
    have hsum : (bidirTerminal G s t strat).1 + (bidirTerminal G s t strat).2 = G.dist s t := by
      rw [bidirTerminal, bidirState_add, hstep]
    exact (bfsVisited_inter_nonempty_iff G s t _ _).mpr ⟨hr, hsum.ge⟩

/-- Any alternation strategy stops within `2 * maxComponentDiam G + 1` steps, even when `G` is
disconnected. -/
theorem bidirStopStep_le_two_mul_maxComponentDiam (G : _root_.SimpleGraph V) (s t : V)
    (strat : AlternationStrategy) :
    bidirStopStep G s t strat ≤ 2 * maxComponentDiam G + 1 := by
  refine bidirStopStep_le ?_
  set m := 2 * maxComponentDiam G + 1
  have hsum := bidirState_add strat m
  rcases le_or_gt (maxComponentDiam G + 1) (bidirState strat m).1 with h1 | h1
  · exact Or.inr (Or.inl (bfsLayer_eq_empty_of_le
      (bfsLayer_maxComponentDiam_succ_eq_empty G s) h1))
  · have h2 : maxComponentDiam G + 1 ≤ (bidirState strat m).2 := by omega
    exact Or.inr (Or.inr (bfsLayer_eq_empty_of_le
      (bfsLayer_maxComponentDiam_succ_eq_empty G t) h2))

/-- Both terminal frontier indices are at most `maxComponentDiam G + 1`. -/
theorem bidirTerminal_le_maxComponentDiam_succ (G : _root_.SimpleGraph V) (s t : V)
    (strat : AlternationStrategy) :
    (bidirTerminal G s t strat).1 ≤ maxComponentDiam G + 1 ∧
      (bidirTerminal G s t strat).2 ≤ maxComponentDiam G + 1 := by
  constructor
  · by_contra h1
    push Not at h1
    obtain ⟨m, hm, hma, _, _⟩ := exists_step_of_lt_terminal_fst G s t strat
      (a := maxComponentDiam G + 1) h1
    refine not_bidirDone_of_lt hm (Or.inr (Or.inl ?_))
    rw [hma]
    exact bfsLayer_maxComponentDiam_succ_eq_empty G s
  · by_contra h2
    push Not at h2
    obtain ⟨m, hm, hmb, _, _⟩ := exists_step_of_lt_terminal_snd G s t strat
      (b := maxComponentDiam G + 1) h2
    refine not_bidirDone_of_lt hm (Or.inr (Or.inr ?_))
    rw [hmb]
    exact bfsLayer_maxComponentDiam_succ_eq_empty G t

/-- Competitiveness of the greedy alternation strategy for reachable pairs: if an alternation
strategy `strat` explores at most `f` edges between `s` and `t`, then the greedy alternation
strategy explores at most `G.dist s t * f` edges. -/
theorem bidirExploredEdges_greedy_le_dist_mul {G : _root_.SimpleGraph V} {s t : V}
    (hr : G.Reachable s t) (strat : AlternationStrategy) {f : ℕ}
    (hf : bidirExploredEdges G s t strat ≤ f) :
    bidirExploredEdges G s t (greedyAlternation G s t) ≤ G.dist s t * f := by
  set pg := bidirTerminal G s t (greedyAlternation G s t)
  set pa := bidirTerminal G s t strat
  have hsum_g : pg.1 + pg.2 = G.dist s t := by
    change (bidirState _ _).1 + (bidirState _ _).2 = _
    rw [bidirState_add, bidirStopStep_eq_dist hr]
  have hsum_a : pa.1 + pa.2 = G.dist s t := by
    change (bidirState _ _).1 + (bidirState _ _).2 = _
    rw [bidirState_add, bidirStopStep_eq_dist hr]
  have hcost_a : bfsPrefixCost G s pa.1 + bfsPrefixCost G t pa.2 ≤ f := hf
  rcases Nat.eq_zero_or_pos (G.dist s t) with hd0 | hdpos
  · have hpg : pg.1 = 0 ∧ pg.2 = 0 := by omega
    simp [bidirExploredEdges, pg, hpg.1, hpg.2, hd0]
  · rcases lt_trichotomy pg.1 pa.1 with hlt | heq | hgt
    · -- Greedy explored fewer forward steps and more backward steps than `strat`.
      have hf_step : ∀ a ∈ Finset.range pg.1, bfsLayerCost G s a ≤ f := by
        intro a ha
        rw [Finset.mem_range] at ha
        exact (bfsLayerCost_le_bfsPrefixCost G s (ha.trans hlt)).trans (by omega)
      have hb_step : ∀ b ∈ Finset.range pg.2, bfsLayerCost G t b ≤ f := by
        intro b hb
        rw [Finset.mem_range] at hb
        obtain ⟨m, _, hmb, hma, hst⟩ :=
          exists_step_of_lt_terminal_snd G s t (greedyAlternation G s t) hb
        have hcost : bfsLayerCost G t b <
            bfsLayerCost G s (bidirState (greedyAlternation G s t) m).1 := by
          have := (greedyAlternation_eq_false_iff G s t
            (bidirState (greedyAlternation G s t) m).1
            (bidirState (greedyAlternation G s t) m).2).mp hst
          rwa [hmb] at this
        have ha_lt : (bidirState (greedyAlternation G s t) m).1 < pa.1 :=
          lt_of_le_of_lt hma hlt
        exact hcost.le.trans ((bfsLayerCost_le_bfsPrefixCost G s ha_lt).trans (by omega))
      calc bidirExploredEdges G s t (greedyAlternation G s t)
          = ∑ a ∈ Finset.range pg.1, bfsLayerCost G s a +
              ∑ b ∈ Finset.range pg.2, bfsLayerCost G t b := rfl
        _ ≤ ∑ _ ∈ Finset.range pg.1, f + ∑ _ ∈ Finset.range pg.2, f :=
            Nat.add_le_add (Finset.sum_le_sum hf_step) (Finset.sum_le_sum hb_step)
        _ = (pg.1 + pg.2) * f := by simp [Nat.add_mul]
        _ = G.dist s t * f := by rw [hsum_g]
    · -- Greedy and `strat` explored the exact same number of forward and backward steps.
      have heq2 : pg.2 = pa.2 := by omega
      have heq_cost : bidirExploredEdges G s t (greedyAlternation G s t) =
          bidirExploredEdges G s t strat := by
        simp [bidirExploredEdges, pg, pa, heq, heq2]
      calc bidirExploredEdges G s t (greedyAlternation G s t)
          ≤ f := heq_cost ▸ hf
        _ = 1 * f := (Nat.one_mul f).symm
        _ ≤ G.dist s t * f := Nat.mul_le_mul_right f hdpos
    · -- Greedy explored more forward steps and fewer backward steps than `strat`.
      have hgt2 : pg.2 < pa.2 := by omega
      have hb_step : ∀ b ∈ Finset.range pg.2, bfsLayerCost G t b ≤ f := by
        intro b hb
        rw [Finset.mem_range] at hb
        exact (bfsLayerCost_le_bfsPrefixCost G t (hb.trans hgt2)).trans (by omega)
      have hf_step : ∀ a ∈ Finset.range pg.1, bfsLayerCost G s a ≤ f := by
        intro a ha
        rw [Finset.mem_range] at ha
        obtain ⟨m, _, hma, hmb, hst⟩ :=
          exists_step_of_lt_terminal_fst G s t (greedyAlternation G s t) ha
        have hcost : bfsLayerCost G s a ≤
          bfsLayerCost G t (bidirState (greedyAlternation G s t) m).2 := by
          have := (greedyAlternation_eq_true_iff G s t
            (bidirState (greedyAlternation G s t) m).1
            (bidirState (greedyAlternation G s t) m).2).mp hst
          rwa [hma] at this
        have hb_lt : (bidirState (greedyAlternation G s t) m).2 < pa.2 :=
          lt_of_le_of_lt hmb hgt2
        exact hcost.trans ((bfsLayerCost_le_bfsPrefixCost G t hb_lt).trans (by omega))
      calc bidirExploredEdges G s t (greedyAlternation G s t)
          = ∑ a ∈ Finset.range pg.1, bfsLayerCost G s a +
              ∑ b ∈ Finset.range pg.2, bfsLayerCost G t b := rfl
        _ ≤ ∑ _ ∈ Finset.range pg.1, f + ∑ _ ∈ Finset.range pg.2, f :=
            Nat.add_le_add (Finset.sum_le_sum hf_step) (Finset.sum_le_sum hb_step)
        _ = (pg.1 + pg.2) * f := by simp [Nat.add_mul]
        _ = G.dist s t * f := by rw [hsum_g]

/-- Competitiveness of the greedy alternation strategy on a connected finite graph of diameter `d`:
if there exists an alternation strategy exploring at most `f` edges between `s` and `t`, then the
greedy alternation strategy explores at most `G.diam * f` edges. -/
theorem bidirExploredEdges_greedy_le_diam_mul {G : _root_.SimpleGraph V} (hconn : G.Connected)
    (s t : V) {f : ℕ} (hstrat : ∃ strat : AlternationStrategy, bidirExploredEdges G s t strat ≤ f) :
    bidirExploredEdges G s t (greedyAlternation G s t) ≤ G.diam * f := by
  obtain ⟨strat, hf⟩ := hstrat
  have hediam : G.ediam ≠ ⊤ := by
    have hle : G.ediam ≤ (Fintype.card V : ℕ∞) := by
      refine iSup₂_le fun u v ↦ ?_
      obtain ⟨p, hp, _⟩ := (hconn u v).exists_path_of_dist
      exact (G.edist_le p).trans (Nat.cast_le.mpr hp.length_lt.le)
    exact ne_top_of_le_ne_top (WithTop.coe_ne_top) hle
  exact (bidirExploredEdges_greedy_le_dist_mul (hconn s t) strat hf).trans
    (Nat.mul_le_mul_right f (G.dist_le_diam hediam))

/-- Competitiveness of the greedy alternation strategy for unreachable vertices `s, t` in a
possibly disconnected graph: greedy explores at most `(maxComponentDiam G + 2) * f` edges. -/
theorem bidirExploredEdges_greedy_le_unreach {G : _root_.SimpleGraph V} {s t : V}
    (hunr : ¬ G.Reachable s t) (strat : AlternationStrategy) {f : ℕ}
    (hf : bidirExploredEdges G s t strat ≤ f) :
    bidirExploredEdges G s t (greedyAlternation G s t) ≤ (maxComponentDiam G + 2) * f := by
  set pg := bidirTerminal G s t (greedyAlternation G s t)
  set pa := bidirTerminal G s t strat
  have hcost_a : bfsPrefixCost G s pa.1 + bfsPrefixCost G t pa.2 ≤ f := hf
  have hdone_a := bidirDone_terminal G s t strat
  have hpg_bd : pg.1 ≤ maxComponentDiam G + 1 ∧ pg.2 ≤ maxComponentDiam G + 1 :=
    bidirTerminal_le_maxComponentDiam_succ G s t (greedyAlternation G s t)
  rcases hdone_a with hinter | hemp_s | hemp_t
  · exact absurd ((bidirTerminal_inter_iff_reachable G s t strat).mp hinter) hunr
  · have hpg1_le : pg.1 ≤ pa.1 := by
      by_contra hgt
      push Not at hgt
      obtain ⟨m, hm, hma, _, _⟩ :=
        exists_step_of_lt_terminal_fst G s t (greedyAlternation G s t) hgt
      exact not_bidirDone_of_lt hm (Or.inr (Or.inl (hma ▸ hemp_s)))
    have hpa1_le : bfsPrefixCost G s pa.1 ≤ f := le_trans (Nat.le_add_right _ _) hcost_a
    have hf_sum : bfsPrefixCost G s pg.1 ≤ f := (bfsPrefixCost_mono G s hpg1_le).trans hpa1_le
    have hb_step : ∀ b ∈ Finset.range pg.2, bfsLayerCost G t b ≤ f := by
      intro b hb
      rw [Finset.mem_range] at hb
      obtain ⟨m, hm, hmb, _, hst⟩ :=
        exists_step_of_lt_terminal_snd G s t (greedyAlternation G s t) hb
      have ha_lt : (bidirState (greedyAlternation G s t) m).1 < pa.1 := by
        by_contra hge
        push Not at hge
        exact not_bidirDone_of_lt hm (Or.inr (Or.inl (bfsLayer_eq_empty_of_le hemp_s hge)))
      have hcost : bfsLayerCost G t b <
          bfsLayerCost G s (bidirState (greedyAlternation G s t) m).1 := by
        have := (greedyAlternation_eq_false_iff G s t _ _).mp hst
        rwa [hmb] at this
      exact hcost.le.trans ((bfsLayerCost_le_bfsPrefixCost G s ha_lt).trans hpa1_le)
    calc bidirExploredEdges G s t (greedyAlternation G s t)
        = bfsPrefixCost G s pg.1 + ∑ b ∈ Finset.range pg.2, bfsLayerCost G t b := rfl
      _ ≤ f + ∑ _ ∈ Finset.range pg.2, f := Nat.add_le_add hf_sum (Finset.sum_le_sum hb_step)
      _ = (pg.2 + 1) * f := by simp [Nat.add_mul, Nat.add_comm]
      _ ≤ (maxComponentDiam G + 2) * f := Nat.mul_le_mul_right f (Nat.succ_le_succ hpg_bd.2)
  · have hpg2_le : pg.2 ≤ pa.2 := by
      by_contra hgt
      push Not at hgt
      obtain ⟨m, hm, hmb, _, _⟩ :=
        exists_step_of_lt_terminal_snd G s t (greedyAlternation G s t) hgt
      exact not_bidirDone_of_lt hm (Or.inr (Or.inr (hmb ▸ hemp_t)))
    have hpa2_le : bfsPrefixCost G t pa.2 ≤ f := le_trans (Nat.le_add_left _ _) hcost_a
    have hb_sum : bfsPrefixCost G t pg.2 ≤ f := (bfsPrefixCost_mono G t hpg2_le).trans hpa2_le
    have hf_step : ∀ a ∈ Finset.range pg.1, bfsLayerCost G s a ≤ f := by
      intro a ha
      rw [Finset.mem_range] at ha
      obtain ⟨m, hm, hma, _, hst⟩ :=
        exists_step_of_lt_terminal_fst G s t (greedyAlternation G s t) ha
      have hb_lt : (bidirState (greedyAlternation G s t) m).2 < pa.2 := by
        by_contra hge
        push Not at hge
        exact not_bidirDone_of_lt hm (Or.inr (Or.inr (bfsLayer_eq_empty_of_le hemp_t hge)))
      have hcost : bfsLayerCost G s a ≤
          bfsLayerCost G t (bidirState (greedyAlternation G s t) m).2 := by
        have := (greedyAlternation_eq_true_iff G s t _ _).mp hst
        rwa [hma] at this
      exact hcost.trans ((bfsLayerCost_le_bfsPrefixCost G t hb_lt).trans hpa2_le)
    calc bidirExploredEdges G s t (greedyAlternation G s t)
        = ∑ a ∈ Finset.range pg.1, bfsLayerCost G s a + bfsPrefixCost G t pg.2 := rfl
      _ ≤ ∑ _ ∈ Finset.range pg.1, f + f := Nat.add_le_add (Finset.sum_le_sum hf_step) hb_sum
      _ = (pg.1 + 1) * f := by simp [Nat.add_mul]
      _ ≤ (maxComponentDiam G + 2) * f := Nat.mul_le_mul_right f (Nat.succ_le_succ hpg_bd.1)

/-- Unified competitiveness bound valid for every pair `s, t` in any finite simple graph `G`
(connected or disconnected): greedy bidirectional BFS explores at most
`(maxComponentDiam G + 2) * f` edges whenever some alternation strategy explores at most `f`
edges. -/
theorem bidirExploredEdges_greedy_le_maxComponentDiam_mul (G : _root_.SimpleGraph V) (s t : V)
    (strat : AlternationStrategy) {f : ℕ} (hf : bidirExploredEdges G s t strat ≤ f) :
    bidirExploredEdges G s t (greedyAlternation G s t) ≤ (maxComponentDiam G + 2) * f := by
  by_cases hr : G.Reachable s t
  · exact (bidirExploredEdges_greedy_le_dist_mul hr strat hf).trans
      (Nat.mul_le_mul_right f ((dist_le_maxComponentDiam G s t).trans (by omega)))
  · exact bidirExploredEdges_greedy_le_unreach hr strat hf

/-- Non-vacuity check: on the 4-vertex path `0 - 1 - 2 - 3`, the graph is connected of diameter `3`
and greedy bidirectional BFS terminates in `3` steps respecting the diameter competitiveness
bound. -/
private theorem path4_greedy_nonvacuity :
    ∃ (G : _root_.SimpleGraph (Fin 4)) (s t : Fin 4),
      G.Connected ∧ 2 ≤ G.dist s t ∧
      bidirStopStep G s t (greedyAlternation G s t) = G.dist s t ∧
      bidirExploredEdges G s t (greedyAlternation G s t) ≤
        G.diam * bidirExploredEdges G s t (fun _ ↦ true) := by
  let G : _root_.SimpleGraph (Fin 4) := _root_.SimpleGraph.fromRel
    fun u v ↦ u.1 + 1 = v.1
  have hadj : ∀ u v : Fin 4, G.Adj u v ↔ u.1 + 1 = v.1 ∨ v.1 + 1 = u.1 := by
    intro u v
    simp only [G, _root_.SimpleGraph.fromRel_adj]
    omega
  have h01 : G.Adj 0 1 := (hadj 0 1).mpr (Or.inl rfl)
  have h12 : G.Adj 1 2 := (hadj 1 2).mpr (Or.inl rfl)
  have h23 : G.Adj 2 3 := (hadj 2 3).mpr (Or.inl rfl)
  have hr0 : ∀ v : Fin 4, G.Reachable 0 v := fun v ↦
    match v with
    | ⟨0, _⟩ => .refl _
    | ⟨1, _⟩ => h01.reachable
    | ⟨2, _⟩ => h01.reachable.trans h12.reachable
    | ⟨3, _⟩ => h01.reachable.trans (h12.reachable.trans h23.reachable)
  have hconn : G.Connected := _root_.SimpleGraph.Connected.mk fun u v ↦ (hr0 u).symm.trans (hr0 v)
  have hdist : 2 ≤ G.dist 0 3 := by
    match hd : G.dist 0 3 with
    | 0 =>
      have := (G.dist_eq_zero_iff_eq_or_not_reachable.mp hd).resolve_right (not_not.mpr (hr0 3))
      exact absurd this (by decide)
    | 1 =>
      have := (hadj 0 3).mp (G.dist_eq_one_iff_adj.mp hd)
      omega
    | _ + 2 => omega
  exact ⟨G, 0, 3, hconn, hdist, bidirStopStep_eq_dist (hconn 0 3) _,
    bidirExploredEdges_greedy_le_diam_mul hconn 0 3 ⟨fun _ ↦ true, le_rfl⟩⟩

end Bidirectional

end CslibFrontier.Algorithms.Reachability.BidirectionalBFS
