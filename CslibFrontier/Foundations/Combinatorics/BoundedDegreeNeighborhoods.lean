/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PanMath Formalization Team (adapted from Kane, Ostuni, and Wu, CC-BY-4.0)
-/

module
-- upstream: candidate
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounded-Degree Hypergraph Edge Deletion for Pairwise Non-Adjacent Neighborhoods

Given an indexed finite hypergraph `E : ι → Finset V` in which every vertex `v : V` belongs to at
most `d` edges, this module proves that for any monotone growth function `F : ℕ → ℕ`, deleting a
small subset `S : Finset ι` of edges yields a linear-sized set `R : Finset V` of vertices whose
remaining neighborhoods have `O_{d, F}(1)` size and share no remaining hyperedge, while
`#S * F t ≤ #R`.

## Main definitions

* `CslibFrontier.Combinatorics.incidentEdges`: hyperedge indices `e : ι` containing vertex `v`.
* `CslibFrontier.Combinatorics.HasMaxVertexDegree`: upper bound `d` on `#(incidentEdges E v)`.
* `CslibFrontier.Combinatorics.closedNeighborhood`: vertices sharing a non-deleted edge with `v`
  (together with `v` itself).
* `CslibFrontier.Combinatorics.NeighborhoodDisjoint`: two vertex sets share no non-deleted edge.

## Main results

* `CslibFrontier.Combinatorics.card_edges_ge_mul_le`: Markov bound `#S * B ≤ d * card V` when every
  edge in `S` has cardinality at least `B`.
* `CslibFrontier.Combinatorics.exists_independent_subset_of_deg_le`: greedy independent-set
  extraction in a symmetric conflict relation of bounded degree.
* `CslibFrontier.Combinatorics.exists_edge_deletion_disjoint_bounded_neighborhoods`: two-scale
  pigeonhole edge-deletion theorem extracting pairwise non-adjacent bounded neighborhoods.
-/

public section

open Finset
open scoped BigOperators

namespace CslibFrontier.Combinatorics

section Defs

variable {ι V : Type*}

/-- The set of hyperedge indices incident to vertex `v` in an indexed hypergraph
`E : ι → Finset V`. -/
def incidentEdges [Fintype ι] [DecidableEq V] (E : ι → Finset V) (v : V) : Finset ι :=
  univ.filter fun e ↦ v ∈ E e

/-- Membership in `incidentEdges E v` holds iff `v ∈ E e`. -/
@[simp]
theorem mem_incidentEdges [Fintype ι] [DecidableEq V] {E : ι → Finset V} {v : V} {e : ι} :
    e ∈ incidentEdges E v ↔ v ∈ E e := by
  simp [incidentEdges]

/-- An indexed hypergraph `E : ι → Finset V` has maximum vertex degree at most `d` if every vertex
lies in at most `d` hyperedges. -/
@[expose] def HasMaxVertexDegree [Fintype ι] [DecidableEq V] (E : ι → Finset V) (d : ℕ) : Prop :=
  ∀ v : V, #(incidentEdges E v) ≤ d

/-- Characterization of `HasMaxVertexDegree`. -/
theorem hasMaxVertexDegree_iff [Fintype ι] [DecidableEq V] {E : ι → Finset V} {d : ℕ} :
    HasMaxVertexDegree E d ↔ ∀ v : V, #(incidentEdges E v) ≤ d :=
  Iff.rfl

/-- Monotonicity of `HasMaxVertexDegree` in the degree bound. -/
theorem HasMaxVertexDegree.mono [Fintype ι] [DecidableEq V] {E : ι → Finset V} {d d' : ℕ}
    (h : HasMaxVertexDegree E d) (hdd' : d ≤ d') : HasMaxVertexDegree E d' :=
  fun v ↦ (h v).trans hdd'

/-- The closed neighborhood of `v` in `E` after deleting a finset `S` of hyperedges: `v` together
with all vertices `w` that share some surviving edge `e ∉ S` with `v`. -/
def closedNeighborhood [Fintype ι] [DecidableEq ι] [DecidableEq V]
    (E : ι → Finset V) (S : Finset ι) (v : V) : Finset V :=
  insert v ((univ.filter fun e ↦ e ∉ S ∧ v ∈ E e).biUnion E)

/-- Membership in `closedNeighborhood E S v`. -/
theorem mem_closedNeighborhood_iff [Fintype ι] [DecidableEq ι] [DecidableEq V]
    {E : ι → Finset V} {S : Finset ι} {v w : V} :
    w ∈ closedNeighborhood E S v ↔ w = v ∨ ∃ e, e ∉ S ∧ v ∈ E e ∧ w ∈ E e := by
  simp only [closedNeighborhood, mem_insert, mem_biUnion, mem_filter, mem_univ, true_and]
  exact or_congr Iff.rfl (exists_congr fun _ ↦ and_assoc)

/-- Every vertex belongs to its own closed neighborhood. -/
@[simp]
theorem self_mem_closedNeighborhood [Fintype ι] [DecidableEq ι] [DecidableEq V]
    (E : ι → Finset V) (S : Finset ι) (v : V) :
    v ∈ closedNeighborhood E S v :=
  mem_insert_self v _

/-- Symmetry of `closedNeighborhood` membership. -/
theorem mem_closedNeighborhood_comm [Fintype ι] [DecidableEq ι] [DecidableEq V]
    (E : ι → Finset V) (S : Finset ι) (u v : V) :
    u ∈ closedNeighborhood E S v ↔ v ∈ closedNeighborhood E S u := by
  simp only [mem_closedNeighborhood_iff]
  constructor
  · rintro (rfl | ⟨e, heS, hv, hu⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨e, heS, hu, hv⟩
  · rintro (rfl | ⟨e, heS, hu, hv⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨e, heS, hv, hu⟩

/-- Two vertex subsets `A, B : Finset V` are non-adjacent after deleting edges `S` if no surviving
hyperedge `e ∉ S` intersects both `A` and `B`. -/
@[expose] def NeighborhoodDisjoint (E : ι → Finset V) (S : Finset ι)
    (A B : Finset V) : Prop :=
  ∀ e, e ∉ S → ∀ u ∈ A, ∀ w ∈ B, ¬ (u ∈ E e ∧ w ∈ E e)

/-- Symmetry of `NeighborhoodDisjoint`. -/
theorem NeighborhoodDisjoint.symm {E : ι → Finset V} {S : Finset ι}
    {A B : Finset V} (h : NeighborhoodDisjoint E S A B) :
    NeighborhoodDisjoint E S B A :=
  fun e he w hw u hu ⟨hwE, huE⟩ ↦ h e he u hu w hw ⟨huE, hwE⟩

end Defs

section CountingAndGreedy

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [DecidableEq V]

omit [Fintype ι] [Fintype V] [DecidableEq ι] in
private lemma card_le_sdiff_add (A B : Finset V) : #A ≤ #(A \ B) + #B := by
  have h1 : #(A \ B) + #(A ∩ B) = #A := card_sdiff_add_card_inter A B
  have h2 : #(A ∩ B) ≤ #B := card_le_card inter_subset_right
  omega

omit [DecidableEq ι] in
/-- Double-counting identity: the sum of hyperedge cardinalities equals the sum of vertex
degrees. -/
theorem sum_card_edges_eq_sum_incidentEdges (E : ι → Finset V) :
    ∑ e : ι, #(E e) = ∑ v : V, #(incidentEdges E v) := by
  have hlhs : ∀ e : ι, #(E e) = ∑ v : V, if v ∈ E e then 1 else 0 := fun e ↦ by
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, card_eq_sum_ones]
  have hrhs : ∀ v : V, #(incidentEdges E v) = ∑ e : ι, if v ∈ E e then 1 else 0 := fun v ↦ by
    rw [incidentEdges, card_eq_sum_ones, sum_filter]
  simp_rw [hlhs, hrhs]
  exact sum_comm

omit [DecidableEq ι] in
/-- Total incidence bound under `HasMaxVertexDegree E d`. -/
theorem sum_card_edges_le {E : ι → Finset V} {d : ℕ} (hd : HasMaxVertexDegree E d) :
    ∑ e : ι, #(E e) ≤ d * Fintype.card V := by
  calc ∑ e : ι, #(E e)
      = ∑ v : V, #(incidentEdges E v) := sum_card_edges_eq_sum_incidentEdges E
    _ ≤ ∑ _v : V, d := sum_le_sum fun v _ ↦ hd v
    _ = d * Fintype.card V := by simp [Nat.mul_comm]

omit [DecidableEq ι] in
/-- Markov bound on the number of large hyperedges: `#S * B ≤ d * card V` where `S` is the set of
edges of size at least `B`. -/
theorem card_edges_ge_mul_le {E : ι → Finset V} {d : ℕ} (hd : HasMaxVertexDegree E d)
    (B : ℕ) :
    #(univ.filter fun e : ι ↦ B ≤ #(E e)) * B ≤ d * Fintype.card V := by
  calc #(univ.filter fun e : ι ↦ B ≤ #(E e)) * B
      = ∑ _e ∈ univ.filter (fun e : ι ↦ B ≤ #(E e)), B := by simp
    _ ≤ ∑ e ∈ univ.filter (fun e : ι ↦ B ≤ #(E e)), #(E e) :=
        sum_le_sum fun e he ↦ (mem_filter.mp he).2
    _ ≤ ∑ e : ι, #(E e) := sum_le_univ_sum_of_nonneg fun _ ↦ Nat.zero_le _
    _ ≤ d * Fintype.card V := sum_card_edges_le hd

omit [Fintype V] in
/-- If every surviving edge containing `v` has cardinality at most `A` and `v` has degree at most
`d`, then `#(closedNeighborhood E S v) ≤ d * A + 1`. -/
theorem card_closedNeighborhood_le_of_forall_le {E : ι → Finset V} {S : Finset ι} {d A : ℕ}
    (hd : HasMaxVertexDegree E d) {v : V}
    (hA : ∀ e, e ∉ S → v ∈ E e → #(E e) ≤ A) :
    #(closedNeighborhood E S v) ≤ d * A + 1 := by
  have hsub : univ.filter (fun e ↦ e ∉ S ∧ v ∈ E e) ⊆ incidentEdges E v := by
    intro e he
    exact mem_incidentEdges.mpr (mem_filter.mp he).2.2
  have hcard_f : #(univ.filter fun e ↦ e ∉ S ∧ v ∈ E e) ≤ d :=
    (card_le_card hsub).trans (hd v)
  calc #(closedNeighborhood E S v)
      ≤ #((univ.filter fun e ↦ e ∉ S ∧ v ∈ E e).biUnion E) + 1 := card_insert_le _ _
    _ ≤ (∑ e ∈ univ.filter (fun e ↦ e ∉ S ∧ v ∈ E e), #(E e)) + 1 :=
        Nat.add_le_add_right card_biUnion_le 1
    _ ≤ (∑ _e ∈ univ.filter (fun e ↦ e ∉ S ∧ v ∈ E e), A) + 1 := by
        refine Nat.add_le_add_right (sum_le_sum fun e he ↦ ?_) 1
        rcases mem_filter.mp he with ⟨_, heS, hvE⟩
        exact hA e heS hvE
    _ = #(univ.filter fun e ↦ e ∉ S ∧ v ∈ E e) * A + 1 := by simp
    _ ≤ d * A + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right A hcard_f) 1

omit [Fintype ι] [Fintype V] [DecidableEq ι] in
/-- Greedy independent-set extraction on a finset `U`: if `rel : V → V → Prop` is symmetric and
every `u ∈ U` has at most `C` elements `u' ∈ U` with `u' = u ∨ rel u u'`, then `U` contains a
subset `R ⊆ U` of pairwise `¬ rel`-related vertices with `#U ≤ #R * C`. -/
theorem exists_independent_subset_of_deg_le (U : Finset V) (rel : V → V → Prop)
    [DecidableRel rel] (hsym : ∀ ⦃x y⦄, rel x y → rel y x) {C : ℕ} (_hC : 1 ≤ C)
    (hdeg : ∀ u ∈ U, #(U.filter fun u' ↦ u' = u ∨ rel u u') ≤ C) :
    ∃ R ⊆ U, #U ≤ #R * C ∧ (R : Set V).Pairwise (fun x y ↦ ¬ rel x y) := by
  classical
  revert hdeg
  refine Finset.strongInductionOn U fun W ih hdegW ↦ ?_
  by_cases hW : W = ∅
  · subst hW
    exact ⟨∅, Subset.rfl, by simp, by simp⟩
  · obtain ⟨u, huW⟩ := nonempty_iff_ne_empty.mpr hW
    let N := W.filter fun u' ↦ u' = u ∨ rel u u'
    have huN : u ∈ N := mem_filter.mpr ⟨huW, Or.inl rfl⟩
    have hN_le : #N ≤ C := hdegW u huW
    let W' := W \ N
    have hW'_lt : W' ⊂ W := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, fun heq ↦ ?_⟩
      have huW' : u ∈ W' := heq.symm ▸ huW
      exact (mem_sdiff.mp huW').2 huN
    have hdegW' : ∀ x ∈ W', #(W'.filter fun u' ↦ u' = x ∨ rel x u') ≤ C := by
      intro x hx
      have hxW : x ∈ W := (mem_sdiff.mp hx).1
      refine (card_le_card ?_).trans (hdegW x hxW)
      intro y hy
      rcases mem_filter.mp hy with ⟨hyW', hyr⟩
      exact mem_filter.mpr ⟨(mem_sdiff.mp hyW').1, hyr⟩
    obtain ⟨R', hR'W', hcardR', hpairR'⟩ := ih W' hW'_lt hdegW'
    refine ⟨insert u R', insert_subset huW (hR'W'.trans sdiff_subset), ?_, ?_⟩
    · have huR' : u ∉ R' := fun hu_in ↦ (mem_sdiff.mp (hR'W' hu_in)).2 huN
      have hW_le : #W ≤ #W' + #N := card_le_sdiff_add W N
      calc #W ≤ #W' + #N := hW_le
        _ ≤ #R' * C + C := Nat.add_le_add hcardR' hN_le
        _ = (#R' + 1) * C := by ring
        _ = #(insert u R') * C := by rw [card_insert_of_notMem huR']
    · rw [coe_insert]
      refine Set.Pairwise.insert hpairR' fun y hy _ ↦ ?_
      have hyW' : y ∈ W' := hR'W' hy
      have hyN : y ∉ N := (mem_sdiff.mp hyW').2
      refine ⟨fun hrel ↦ hyN (mem_filter.mpr ⟨(mem_sdiff.mp hyW').1, Or.inr hrel⟩),
        fun hrel ↦ hyN (mem_filter.mpr ⟨(mem_sdiff.mp hyW').1, Or.inr (hsym hrel)⟩)⟩

end CountingAndGreedy

section MainTheorem

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [DecidableEq V]

private def microStep (d t Ft Bk : ℕ) : ℕ :=
  max (Bk + 1) (4 * d * (d * Bk * t ^ 2 + 1) * max Ft 1)

private def microThreshold (d A Ft : ℕ) : ℕ → ℕ
  | 0 => A
  | k + 1 => microStep d (d * A + 3) Ft (microThreshold d A Ft k)

private lemma microThreshold_strictMono (d A Ft : ℕ) :
    StrictMono (microThreshold d A Ft) :=
  strictMono_nat_of_lt_succ fun k ↦ by
    simp only [microThreshold, microStep]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

private def macroStep (d : ℕ) (F : ℕ → ℕ) (A : ℕ) : ℕ :=
  let t := d * A + 3
  microThreshold d A (F t) (4 * d * t + 1)

private def macroThreshold (d : ℕ) (F : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => macroStep d F (macroThreshold d F i)

private lemma macroThreshold_strictMono (d : ℕ) (F : ℕ → ℕ) :
    StrictMono (macroThreshold d F) :=
  strictMono_nat_of_lt_succ fun i ↦ by
    simp only [macroThreshold, macroStep]
    exact microThreshold_strictMono d (macroThreshold d F i)
      (F (d * macroThreshold d F i + 3)) (Nat.succ_pos _)

/-- Upper bound `O_{d, F}(1)` on the neighborhood size extracted by
`exists_edge_deletion_disjoint_bounded_neighborhoods` (always at least `3`). -/
def neighborhoodSizeBound (d : ℕ) (F : ℕ → ℕ) : ℕ :=
  d * macroThreshold d F (4 * d) + 3

/-- `neighborhoodSizeBound d F` is always at least `3`. -/
theorem three_le_neighborhoodSizeBound (d : ℕ) (F : ℕ → ℕ) :
    3 ≤ neighborhoodSizeBound d F :=
  Nat.le_add_left 3 _

/-- Denominator constant `O_{d, F}(1)` in `#V ≤ neighborhoodCountDivisor d F * #R` from
`exists_edge_deletion_disjoint_bounded_neighborhoods`. -/
def neighborhoodCountDivisor (d : ℕ) (F : ℕ → ℕ) : ℕ :=
  let Amax := macroThreshold d F (4 * d)
  let tmax := d * Amax + 3
  let Bmax := microThreshold d Amax (F tmax) (4 * d * tmax + 1)
  2 * (d * Bmax * tmax ^ 2 + 1)

/-- `neighborhoodCountDivisor d F` is always positive. -/
theorem neighborhoodCountDivisor_pos (d : ℕ) (F : ℕ → ℕ) :
    0 < neighborhoodCountDivisor d F := by
  unfold neighborhoodCountDivisor
  positivity

omit [DecidableEq ι] in
private lemma pigeonhole_disjoint_bands {L : ℕ} (hL : 0 < L) (b : ℕ → ℕ) (hb : StrictMono b)
    {E : ι → Finset V} {d : ℕ} (hd : HasMaxVertexDegree E d) :
    ∃ k < L,
      #(univ.filter fun v : V ↦ ∃ e : ι, b k < #(E e) ∧ #(E e) ≤ b (k + 1) ∧ v ∈ E e) * L ≤
        d * Fintype.card V := by
  classical
  let bandVerts : ℕ → Finset V := fun k ↦
    univ.filter fun v : V ↦ ∃ e : ι, b k < #(E e) ∧ #(E e) ≤ b (k + 1) ∧ v ∈ E e
  have hsum : ∑ k ∈ range L, #(bandVerts k) ≤ d * Fintype.card V := by
    have hcard_band : ∀ k, #(bandVerts k) = ∑ v : V, if v ∈ bandVerts k then 1 else 0 := fun k ↦ by
      rw [← sum_filter, filter_mem_eq_inter, univ_inter, card_eq_sum_ones]
    calc ∑ k ∈ range L, #(bandVerts k)
        = ∑ k ∈ range L, ∑ v : V, if v ∈ bandVerts k then 1 else 0 :=
            sum_congr rfl fun k _ ↦ hcard_band k
      _ = ∑ v : V, ∑ k ∈ range L, if v ∈ bandVerts k then 1 else 0 := sum_comm
      _ ≤ ∑ v : V, #(incidentEdges E v) := by
            refine sum_le_sum fun v _ ↦ ?_
            let pickEdge : {k // k ∈ (range L).filter (v ∈ bandVerts ·)} →
                {e // e ∈ incidentEdges E v} := fun ⟨k, hk⟩ ↦
              have hvb : v ∈ bandVerts k := (mem_filter.mp hk).2
              have hex : ∃ e : ι, b k < #(E e) ∧ #(E e) ≤ b (k + 1) ∧ v ∈ E e :=
                (mem_filter.mp hvb).2
              ⟨Classical.choose hex, mem_incidentEdges.mpr (Classical.choose_spec hex).2.2⟩
            have hinj : Function.Injective pickEdge := by
              rintro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ heq
              have hspec₁ := Classical.choose_spec
                ((mem_filter.mp (mem_filter.mp hk₁).2).2)
              have hspec₂ := Classical.choose_spec
                ((mem_filter.mp (mem_filter.mp hk₂).2).2)
              have he_eq : Classical.choose ((mem_filter.mp (mem_filter.mp hk₁).2).2) =
                  Classical.choose ((mem_filter.mp (mem_filter.mp hk₂).2).2) :=
                Subtype.ext_iff.mp heq
              rw [← he_eq] at hspec₂
              ext
              by_contra hne
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · have hle : b (k₁ + 1) ≤ b k₂ := hb.monotone (Nat.succ_le_of_lt hlt)
                omega
              · have hle : b (k₂ + 1) ≤ b k₁ := hb.monotone (Nat.succ_le_of_lt hgt)
                omega
            have hcard := Fintype.card_le_of_injective pickEdge hinj
            simp only [Fintype.card_coe] at hcard
            rwa [← sum_filter, ← card_eq_sum_ones]
      _ ≤ ∑ _v : V, d := sum_le_sum fun v _ ↦ hd v
      _ = d * Fintype.card V := by simp [Nat.mul_comm]
  by_contra! hall
  have hgt : d * Fintype.card V * L < (∑ k ∈ range L, #(bandVerts k)) * L := by
    calc d * Fintype.card V * L
        = ∑ _k ∈ range L, d * Fintype.card V := by simp [Nat.mul_comm]
      _ < ∑ k ∈ range L, #(bandVerts k) * L :=
          sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hL.ne') fun k hk ↦
            hall k (mem_range.mp hk)
      _ = (∑ k ∈ range L, #(bandVerts k)) * L := (Finset.sum_mul _ _ _).symm
  have hle := Nat.mul_le_mul_right L hsum
  omega

/-- **Bounded-Degree Hypergraph Neighborhood Extraction**: for every indexed hypergraph
`E : ι → Finset V` with maximum vertex degree at most `d` and every monotone growth function
`F : ℕ → ℕ`, there exist `t ≤ neighborhoodSizeBound d F` (`3 ≤ t`), a deleted edge set
`S : Finset ι`, and a vertex set `R : Finset V` such that:
1. `Fintype.card V ≤ neighborhoodCountDivisor d F * #R`,
2. every `v ∈ R` has `#(closedNeighborhood E S v) ≤ t`,
3. distinct `u, v ∈ R` have `NeighborhoodDisjoint E S` closed neighborhoods in `E` outside `S`,
4. `#S * F t ≤ #R`. -/
theorem exists_edge_deletion_disjoint_bounded_neighborhoods {E : ι → Finset V} {d : ℕ}
    (hd : HasMaxVertexDegree E d) {F : ℕ → ℕ} (hF : Monotone F) :
    ∃ (t : ℕ) (S : Finset ι) (R : Finset V),
      3 ≤ t ∧ t ≤ neighborhoodSizeBound d F ∧
      Fintype.card V ≤ neighborhoodCountDivisor d F * #R ∧
      (∀ v ∈ R, #(closedNeighborhood E S v) ≤ t) ∧
      (R : Set V).Pairwise (fun u v ↦
        NeighborhoodDisjoint E S (closedNeighborhood E S u) (closedNeighborhood E S v)) ∧
      #S * F t ≤ #R := by
  classical
  let L₁ := 4 * d + 1
  obtain ⟨i, hi, hband₁⟩ :=
    pigeonhole_disjoint_bands (L := L₁) (by positivity) (macroThreshold d F)
      (macroThreshold_strictMono d F) hd
  let A := macroThreshold d F i
  let A_next := macroThreshold d F (i + 1)
  let t := d * A + 3
  have ht3 : 3 ≤ t := Nat.le_add_left 3 _
  have hi_le : i ≤ 4 * d := Nat.lt_succ_iff.mp hi
  have hA_le : A ≤ macroThreshold d F (4 * d) :=
    (macroThreshold_strictMono d F).monotone hi_le
  have ht_le : t ≤ neighborhoodSizeBound d F := by
    unfold neighborhoodSizeBound
    exact Nat.add_le_add_right (Nat.mul_le_mul_left d hA_le) 3
  let bad₁ : Finset V :=
    univ.filter fun v : V ↦ ∃ e : ι, A < #(E e) ∧ #(E e) ≤ A_next ∧ v ∈ E e
  have hbad₁_card : #bad₁ * (4 * d + 1) ≤ d * Fintype.card V := hband₁
  let V' : Finset V := univ \ bad₁
  have hV'_add : #V' + #bad₁ = Fintype.card V := by
    have h := card_sdiff_add_card_eq_card (subset_univ bad₁)
    simpa [V'] using h
  let L₂ := 4 * d * t + 1
  let B : ℕ → ℕ := microThreshold d A (F t)
  have hB_strict : StrictMono B := microThreshold_strictMono d A (F t)
  have hB_L₂ : B L₂ = A_next := rfl
  obtain ⟨k, hk, hband₂⟩ :=
    pigeonhole_disjoint_bands (L := L₂) (by positivity) B hB_strict hd
  let M : Finset V :=
    univ.filter fun w : V ↦ ∃ e : ι, B k < #(E e) ∧ #(E e) ≤ B (k + 1) ∧ w ∈ E e
  have hM_card : #M * (4 * d * t + 1) ≤ d * Fintype.card V := hband₂
  let S_small : Finset ι := univ.filter fun e : ι ↦ A < #(E e)
  have hN_small_le : ∀ w : V, #(closedNeighborhood E S_small w) ≤ t := by
    intro w
    have hle := card_closedNeighborhood_le_of_forall_le hd (S := S_small) (A := A) (v := w)
      fun e heS _ ↦ not_lt.mp (by simpa [S_small] using heS)
    omega
  let touchM : Finset V := M.biUnion (closedNeighborhood E S_small)
  have htouchM_card : #touchM ≤ #M * t := by
    calc #touchM ≤ ∑ w ∈ M, #(closedNeighborhood E S_small w) := card_biUnion_le
      _ ≤ ∑ _w ∈ M, t := sum_le_sum fun w _ ↦ hN_small_le w
      _ = #M * t := by simp
  let U : Finset V := V' \ touchM
  have hU_card_two : Fintype.card V ≤ 2 * #U := by
    have hsub : #V' ≤ #U + #touchM := card_le_sdiff_add V' touchM
    have hbad₁_four : 4 * #bad₁ ≤ Fintype.card V := by
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · omega
      · have : 4 * #bad₁ * d ≤ d * Fintype.card V := by nlinarith
        have : 4 * #bad₁ * d ≤ Fintype.card V * d := by linarith
        exact Nat.le_of_mul_le_mul_right this hd_pos
    have hM_four : 4 * (#M * t) ≤ Fintype.card V := by
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · have hM0 : #M = 0 := by omega
        simp [hM0]
      · have : 4 * (#M * t) * d ≤ d * Fintype.card V := by nlinarith
        have : 4 * (#M * t) * d ≤ Fintype.card V * d := by linarith
        exact Nat.le_of_mul_le_mul_right this hd_pos
    omega
  let S : Finset ι := univ.filter fun e : ι ↦ B (k + 1) < #(E e)
  have hBk1_le_Anext : B (k + 1) ≤ A_next := by
    rw [← hB_L₂]
    exact hB_strict.monotone (Nat.succ_le_of_lt hk)
  have hB0_le_Bk : A ≤ B k := hB_strict.monotone (Nat.zero_le k)
  have hN_eq_small : ∀ u ∈ U, closedNeighborhood E S u = closedNeighborhood E S_small u := by
    intro u hu
    have huV' : u ∈ V' := (mem_sdiff.mp hu).1
    have hu_not_bad₁ : u ∉ bad₁ := (mem_sdiff.mp huV').2
    ext w
    simp only [mem_closedNeighborhood_iff, S, S_small, mem_filter, mem_univ, true_and, not_lt]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨e, he_le, huE, hwE⟩
      refine ⟨e, ?_, huE, hwE⟩
      by_contra! hgtA
      exact hu_not_bad₁ (mem_filter.mpr ⟨mem_univ u, e, hgtA, he_le.trans hBk1_le_Anext, huE⟩)
    · rintro ⟨e, heA, huE, hwE⟩
      exact ⟨e, heA.trans (hB0_le_Bk.trans (hB_strict (Nat.lt_succ_self k)).le), huE, hwE⟩
  have hU_edge_le_Bk : ∀ u ∈ U, ∀ w ∈ closedNeighborhood E S u,
      ∀ e, e ∉ S → w ∈ E e → #(E e) ≤ B k := by
    intro u hu w hw e heS hwE
    rw [hN_eq_small u hu] at hw
    have hu_not_touch : u ∉ touchM := (mem_sdiff.mp hu).2
    have hw_not_M : w ∉ M := fun hwM ↦
      hu_not_touch (mem_biUnion.mpr ⟨w, hwM,
        (mem_closedNeighborhood_comm E S_small w u).mp hw⟩)
    have he_le_Bk1 : #(E e) ≤ B (k + 1) := not_lt.mp (by simpa [S] using heS)
    by_contra! hgtBk
    exact hw_not_M (mem_filter.mpr ⟨mem_univ w, e, hgtBk, he_le_Bk1, hwE⟩)
  let Ck : ℕ := d * B k * t ^ 2 + 1
  let conflict : V → V → Prop := fun u v ↦
    ¬ NeighborhoodDisjoint E S (closedNeighborhood E S u) (closedNeighborhood E S v)
  have hconflict_sym : ∀ ⦃u v⦄, conflict u v → conflict v u :=
    fun _ _ huv hdisj ↦ huv hdisj.symm
  have hdegU : ∀ u ∈ U, #(U.filter fun u' ↦ u' = u ∨ conflict u u') ≤ Ck := by
    intro u hu
    let N_u := closedNeighborhood E S u
    let edges_u := N_u.biUnion fun w ↦ univ.filter fun e : ι ↦ e ∉ S ∧ w ∈ E e
    let verts2_u := edges_u.biUnion E
    let reach_u := insert u (verts2_u.biUnion (closedNeighborhood E S_small))
    have hsub : U.filter (fun u' ↦ u' = u ∨ conflict u u') ⊆ reach_u := by
      intro u' hu'
      rcases mem_filter.mp hu' with ⟨hu'U, heq_u | hconf⟩
      · rw [heq_u]
        exact mem_insert_self u _
      · simp only [conflict, NeighborhoodDisjoint, not_forall, Classical.not_not] at hconf
        rcases hconf with ⟨e, heS, w, hw, w', hw', hwE, hw'E⟩
        rw [hN_eq_small u' hu'U] at hw'
        have he_mem : e ∈ edges_u := mem_biUnion.mpr ⟨w, hw, mem_filter.mpr ⟨mem_univ e, heS, hwE⟩⟩
        have hw'_mem : w' ∈ verts2_u := mem_biUnion.mpr ⟨e, he_mem, hw'E⟩
        exact mem_insert_of_mem (mem_biUnion.mpr ⟨w', hw'_mem,
          (mem_closedNeighborhood_comm E S_small w' u').mp hw'⟩)
    have hNu_le : #N_u ≤ t := by
      rw [show N_u = closedNeighborhood E S u from rfl, hN_eq_small u hu]
      exact hN_small_le u
    have hedges_le : #edges_u ≤ t * d := by
      calc #edges_u ≤ ∑ w ∈ N_u, #(univ.filter fun e : ι ↦ e ∉ S ∧ w ∈ E e) := card_biUnion_le
        _ ≤ ∑ w ∈ N_u, #(incidentEdges E w) := by
            refine sum_le_sum fun w _ ↦ card_le_card fun e he ↦ ?_
            exact mem_incidentEdges.mpr (mem_filter.mp he).2.2
        _ ≤ ∑ _w ∈ N_u, d := sum_le_sum fun w _ ↦ hd w
        _ = #N_u * d := by simp
        _ ≤ t * d := Nat.mul_le_mul_right d hNu_le
    have hverts2_le : #verts2_u ≤ t * d * B k := by
      calc #verts2_u ≤ ∑ e ∈ edges_u, #(E e) := card_biUnion_le
        _ ≤ ∑ _e ∈ edges_u, B k := by
            refine sum_le_sum fun e he ↦ ?_
            rcases mem_biUnion.mp he with ⟨w, hw, hew⟩
            rcases mem_filter.mp hew with ⟨_, heS, hwE⟩
            exact hU_edge_le_Bk u hu w hw e heS hwE
        _ = #edges_u * B k := by simp
        _ ≤ t * d * B k := Nat.mul_le_mul_right (B k) hedges_le
    have hreach_le : #reach_u ≤ Ck := by
      calc #reach_u
          ≤ #(verts2_u.biUnion (closedNeighborhood E S_small)) + 1 := card_insert_le _ _
        _ ≤ (∑ w' ∈ verts2_u, #(closedNeighborhood E S_small w')) + 1 :=
            Nat.add_le_add_right card_biUnion_le 1
        _ ≤ (∑ _w' ∈ verts2_u, t) + 1 :=
            Nat.add_le_add_right (sum_le_sum fun w' _ ↦ hN_small_le w') 1
        _ = #verts2_u * t + 1 := by simp
        _ ≤ (t * d * B k) * t + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right t hverts2_le) 1
        _ = Ck := by dsimp [Ck]; ring
    exact (card_le_card hsub).trans hreach_le
  obtain ⟨R, hRU, hUR, hpairR⟩ :=
    exists_independent_subset_of_deg_le U conflict hconflict_sym (Nat.le_add_left 1 _) hdegU
  have hBk_le_Bmax : Ck * 2 ≤ neighborhoodCountDivisor d F := by
    unfold neighborhoodCountDivisor
    dsimp only
    let Amax := macroThreshold d F (4 * d)
    let tmax := d * Amax + 3
    have ht_tmax : t ≤ tmax := Nat.add_le_add_right (Nat.mul_le_mul_left d hA_le) 3
    have hFt_le : F t ≤ F tmax := hF ht_tmax
    have hB_mono : ∀ m, microThreshold d A (F t) m ≤ microThreshold d Amax (F tmax) m := by
      intro m
      induction m with
      | zero => exact hA_le
      | succ m ihm =>
        simp only [microThreshold, microStep]
        refine max_le_max (Nat.add_le_add_right ihm 1) ?_
        refine Nat.mul_le_mul ?_ (max_le_max hFt_le le_rfl)
        refine Nat.mul_le_mul_left (4 * d) (Nat.add_le_add_right ?_ 1)
        exact Nat.mul_le_mul (Nat.mul_le_mul_left d ihm) (Nat.pow_le_pow_left ht_tmax 2)
    have hk_le : k ≤ 4 * d * tmax + 1 := by
      have : k < 4 * d * t + 1 := hk
      have : 4 * d * t ≤ 4 * d * tmax := Nat.mul_le_mul_left (4 * d) ht_tmax
      omega
    have hBk_le : B k ≤ microThreshold d Amax (F tmax) (4 * d * tmax + 1) :=
      (hB_mono k).trans ((microThreshold_strictMono d Amax (F tmax)).monotone hk_le)
    have hprod : d * B k * t ^ 2 ≤
        d * microThreshold d Amax (F tmax) (4 * d * tmax + 1) * tmax ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left d hBk_le) (Nat.pow_le_pow_left ht_tmax 2)
    dsimp only [Ck, Amax, tmax] at hprod ⊢
    omega
  have hcardV_R : Fintype.card V ≤ neighborhoodCountDivisor d F * #R := by
    calc Fintype.card V ≤ 2 * #U := hU_card_two
      _ ≤ 2 * (#R * Ck) := Nat.mul_le_mul_left 2 hUR
      _ = (Ck * 2) * #R := by ring
      _ ≤ neighborhoodCountDivisor d F * #R := Nat.mul_le_mul_right #R hBk_le_Bmax
  have hS_bound : #S * F t ≤ #R := by
    have hS_sub : S ⊆ univ.filter (fun e : ι ↦ B (k + 1) ≤ #(E e)) :=
      fun e he ↦ mem_filter.mpr ⟨mem_univ e, (mem_filter.mp he).2.le⟩
    have hS_mul : #S * B (k + 1) ≤ d * Fintype.card V :=
      (Nat.mul_le_mul_right _ (card_le_card hS_sub)).trans (card_edges_ge_mul_le hd (B (k + 1)))
    have hBk1_ge : 4 * d * Ck * max (F t) 1 ≤ B (k + 1) := by
      simp only [B, microThreshold, microStep]
      exact le_max_right _ _
    have h1 : #S * (4 * d * Ck * max (F t) 1) ≤ d * (2 * (#R * Ck)) := by
      calc #S * (4 * d * Ck * max (F t) 1)
          ≤ #S * B (k + 1) := Nat.mul_le_mul_left #S hBk1_ge
        _ ≤ d * Fintype.card V := hS_mul
        _ ≤ d * (2 * #U) := Nat.mul_le_mul_left d hU_card_two
        _ ≤ d * (2 * (#R * Ck)) := Nat.mul_le_mul_left d (Nat.mul_le_mul_left 2 hUR)
    by_cases hd0 : d = 0
    · have hS_empty : S = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro e he
        have he_gt : 0 < #(E e) := lt_of_le_of_lt (Nat.zero_le _) (mem_filter.mp he).2
        obtain ⟨v, hv⟩ := card_pos.mp he_gt
        have hv_deg := hd v
        rw [hd0, Nat.le_zero, card_eq_zero, eq_empty_iff_forall_notMem] at hv_deg
        exact hv_deg e (mem_incidentEdges.mpr hv)
      simp [hS_empty]
    · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
      have hCk_pos : 0 < Ck := by dsimp [Ck]; positivity
      have hmax_le : #S * max (F t) 1 * (2 * d * Ck) ≤ #R * (2 * d * Ck) := by
        have h_lhs : #S * (4 * d * Ck * max (F t) 1) =
            2 * (#S * max (F t) 1 * (2 * d * Ck)) := by ring
        have h_rhs : d * (2 * (#R * Ck)) = #R * (2 * d * Ck) := by ring
        rw [h_lhs, h_rhs] at h1
        omega
      have h2dCk_pos : 0 < 2 * d * Ck := by positivity
      have hle_max : #S * max (F t) 1 ≤ #R := Nat.le_of_mul_le_mul_right hmax_le h2dCk_pos
      exact (Nat.mul_le_mul_left #S (le_max_left (F t) 1)).trans hle_max
  refine ⟨t, S, R, ht3, ht_le, hcardV_R, ?_, ?_, hS_bound⟩
  · intro v hv
    rw [hN_eq_small v (hRU hv)]
    exact hN_small_le v
  · intro u hu v hv huv
    have hnc := hpairR hu hv huv
    simpa [conflict] using hnc

end MainTheorem

end CslibFrontier.Combinatorics
