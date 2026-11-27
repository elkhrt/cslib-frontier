/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SetCover
public import CslibFrontier.Computability.Complexity.Problems.VertexCover

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Set Cover with Intersection 1 and Unweighted Set Cover `NP`-Completeness

A finite set system `S : Cslib.Complexity.SetSystem` has *intersection at most 1*
(`Cslib.Complexity.IsIntersectOne`) when any two distinct candidate subsets in `S.sets` share
at most one distinct element. The restricted decision problem
`Cslib.Complexity.SetCoverIntersectOne`
asks whether an intersection-1 set system admits a cover of its ground set of cardinality at most
`k`.

This module develops two foundational complexity-theoretic results on canonical `Cslib.Complexity`
encodings under standard Lean axioms:

1. **`NP`-completeness of `SetCoverIntersectOne` and unweighted `SetCover`**: mapping a graph
   instance `(G, k)` to the set system of undirected edges (ground set) and vertex-incidence stars
   (candidate sets) yields a polynomial-time many-one reduction from `VertexCover` to
   `SetCoverIntersectOne` (since two distinct vertices of a simple graph share at most one edge),
   establishing `NP`-completeness of both `SetCoverIntersectOne` and unweighted `SetCover`.
2. **Polynomial-time SC-1 normalization and quadratic set-count bound**: `normalizeSetSystem`
   deduplicates `ground`, restricts every candidate set to `ground` in canonical ground order,
   drops empty restrictions, and deduplicates identical candidate sets while preserving
   `IsIntersectOne`, `Coverable`, and `optCoverSize`, paired with a polynomial-time cover-pullback
   map `liftNormalizedCover` and the sharp linear-hypergraph bound
   `(normalizeSetSystem S).sets.length ≤ n.choose 2 + n` where `n = S.ground.toFinset.card`.

## Main definitions

* `Cslib.Complexity.IsIntersectOne`, `Cslib.Complexity.pairInterAtMostOne`,
  `Cslib.Complexity.isIntersectOneBool`: set systems whose distinct candidate sets intersect
  in at most one element, with executable polynomial-time Boolean tests.
* `Cslib.Complexity.SetCoverIntersectOne`: the SC-1 decision problem on `encSetCover`.
* `Cslib.Complexity.graphCanonicalEdges`, `Cslib.Complexity.graphIncidenceSetSystem`,
  `Cslib.Complexity.vertexCoverToSetCover`: polynomial-time vertex-edge incidence reduction
  from `VertexCover` to `SetCoverIntersectOne` and `SetCover`.
* `Cslib.Complexity.normalizeSetSystem`, `Cslib.Complexity.liftNormalizedCover`:
  polynomial-time canonicalization and cover-pullback for finite set systems.

## Main results

* `Cslib.Complexity.setCoverIntersectOne_npComplete`: `SetCoverIntersectOne` is `NP`-complete.
* `Cslib.Complexity.setCover_npHard`, `Cslib.Complexity.setCover_npComplete`:
  unweighted `SetCover` is `NP`-complete.
* `Cslib.Complexity.normalizeSetSystem_isIntersectOne`,
  `Cslib.Complexity.normalizeSetSystem_coverable_iff`,
  `Cslib.Complexity.normalizeSetSystem_optCoverSize`,
  `Cslib.Complexity.liftNormalizedCover_isCoverList`: soundness of polynomial-time set-system
  normalization and cover lifting.
* `Cslib.Complexity.normalizeSetSystem_sets_length_le`,
  `Cslib.Complexity.normalizeSetSystem_total_size_le_sq`: sharp `n.choose 2 + n` set-count
  bound and `n ^ 2` total vertex-count bound for normalized SC-1 instances.

## Tags

computational complexity, NP-completeness, set cover, linear hypergraph, vertex cover
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Set Cover with Intersection 1 -/

/-- A set system `S` has *intersection at most 1* when any two distinct candidate subsets in
`S.sets` share at most one distinct element. -/
@[expose] def IsIntersectOne (S : SetSystem) : Prop :=
  ∀ i j : Fin S.sets.length, i ≠ j → (S.sets[i].toFinset ∩ S.sets[j].toFinset).card ≤ 1

/-- Boolean test checking that two lists `A, B : List ℕ` share at most one distinct element. -/
def pairInterAtMostOne (A B : List ℕ) : Bool :=
  (A.filter fun x ↦ decide (x ∈ B)).all fun x ↦
    (A.filter fun y ↦ decide (y ∈ B)).all fun y ↦ decide (x = y)

/-- `pairInterAtMostOne A B = true` iff `(A.toFinset ∩ B.toFinset).card ≤ 1`. -/
theorem pairInterAtMostOne_eq_true_iff (A B : List ℕ) :
    pairInterAtMostOne A B = true ↔ (A.toFinset ∩ B.toFinset).card ≤ 1 := by
  simp only [pairInterAtMostOne, List.all_eq_true, List.mem_filter, decide_eq_true_eq,
    Finset.card_le_one, Finset.mem_inter, List.mem_toFinset]

/-- Testing `pairInterAtMostOne` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_pairInterAtMostOne :
    ComputableInPolyTime (fun p : List ℕ × List ℕ ↦ pairInterAtMostOne p.1 p.2)
      (encPair (encList encNat) (encList encNat)) encBool := by
  unfold pairInterAtMostOne
  fun_prop

/-- Executable Boolean test deciding `IsIntersectOne S`. -/
def isIntersectOneBool (S : SetSystem) : Bool :=
  S.sets.zipIdx.all fun p ↦
    S.sets.zipIdx.all fun q ↦ decide (p.2 = q.2) || pairInterAtMostOne p.1 q.1

/-- `isIntersectOneBool S = true` iff `IsIntersectOne S`. -/
theorem isIntersectOneBool_eq_true_iff (S : SetSystem) :
    isIntersectOneBool S = true ↔ IsIntersectOne S := by
  simp only [isIntersectOneBool, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    pairInterAtMostOne_eq_true_iff, IsIntersectOne]
  constructor
  · intro h i j hij
    have hi : (S.sets[i.1], i.1) ∈ S.sets.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr (by simp [i.isLt])
    have hj : (S.sets[j.1], j.1) ∈ S.sets.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr (by simp [j.isLt])
    exact (h _ hi _ hj).resolve_left fun heq ↦ hij (Fin.ext heq)
  · intro h p hp q hq
    obtain ⟨hip, heqp⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hp)
    obtain ⟨hiq, heqq⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hq)
    by_cases hij : p.2 = q.2
    · exact Or.inl hij
    · right
      rw [← heqp, ← heqq]
      exact h ⟨p.2, by simpa using hip⟩ ⟨q.2, by simpa using hiq⟩ fun hc ↦
        hij (congrArg Fin.val hc)

/-- Testing `isIntersectOneBool` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_isIntersectOneBool :
    ComputableInPolyTime isIntersectOneBool encSetSystem encBool := by
  unfold isIntersectOneBool
  fun_prop

/-- **Set Cover with Intersection 1 (SC-1)**: pairs `(S, k)` where `S` has pairwise set
intersections of cardinality at most `1` and admits a cover of cardinality at most `k`. -/
@[expose] def SetCoverIntersectOne : Set (SetSystem × ℕ) :=
  {p | IsIntersectOne p.1 ∧ p ∈ SetCover}

/-- `SetCoverIntersectOne` lies in `NP`. -/
theorem setCoverIntersectOne_mem_NP : SetCoverIntersectOne ∈ NP encSetCover := by
  obtain ⟨poly, V, hV, hisV⟩ := SetCover_mem_NP
  have heq : SetCoverIntersectOne =
      {p : SetSystem × ℕ | isIntersectOneBool p.1 = true ∧ p ∈ SetCover} := by
    ext p
    simp [SetCoverIntersectOne, isIntersectOneBool_eq_true_iff]
  rw [heq]
  exact ⟨poly, fun x ↦ isIntersectOneBool x.1.1 && V x, by fun_prop, hisV.guard⟩

/-! ### Polynomial-time reduction from `VertexCover` to `SetCoverIntersectOne` and `SetCover` -/

/-- Canonical duplicate-free list of undirected edges `(u, v)` (`u < v`) between declared vertices
of `G : Cslib.Complexity.Graph`. -/
def graphCanonicalEdges (G : Graph) : List (ℕ × ℕ) :=
  G.distinctVertices.flatMap fun u ↦
    (G.distinctVertices.filter fun v ↦ decide (u < v) && G.adjBool u v).map fun v ↦ (u, v)

/-- Membership in `graphCanonicalEdges G`. -/
theorem mem_graphCanonicalEdges {G : Graph} {e : ℕ × ℕ} :
    e ∈ graphCanonicalEdges G ↔
      e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices ∧ e.1 < e.2 ∧ G.toSimpleGraph.Adj e.1 e.2 := by
  rcases e with ⟨u, v⟩
  simp only [graphCanonicalEdges, List.mem_flatMap, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff, Graph.mem_distinctVertices,
    Prod.mk.injEq]
  exact ⟨fun ⟨_, hu, _, ⟨hv, hlt, hadj⟩, rfl, rfl⟩ ↦ ⟨hu, hv, hlt, hadj⟩,
    fun ⟨hu, hv, hlt, hadj⟩ ↦ ⟨u, hu, v, ⟨hv, hlt, hadj⟩, rfl, rfl⟩⟩

/-- `graphCanonicalEdges G` has no duplicate entries. -/
theorem nodup_graphCanonicalEdges (G : Graph) : (graphCanonicalEdges G).Nodup := by
  rw [graphCanonicalEdges, List.nodup_flatMap]
  refine ⟨fun u _ ↦ (G.nodup_distinctVertices.filter _).map fun _ _ h ↦ (Prod.mk.inj h).2, ?_⟩
  refine G.nodup_distinctVertices.pairwise_of_forall_ne fun u _ u' _ hne e he₁ he₂ ↦ ?_
  simp only [List.mem_map, List.mem_filter] at he₁ he₂
  obtain ⟨_, _, rfl⟩ := he₁
  obtain ⟨_, _, heq⟩ := he₂
  exact hne (Prod.mk.inj heq).1.symm

@[local fun_prop]
private theorem computableInPolyTime_graphCanonicalEdges :
    ComputableInPolyTime graphCanonicalEdges encGraph (encList (encPair encNat encNat)) := by
  unfold graphCanonicalEdges
  fun_prop

/-- Vertex-edge incidence set system of `G : Graph`: ground elements are indices `0, ..., |E| - 1`
of `graphCanonicalEdges G`, and each vertex `w ∈ G.distinctVertices` gives the set of indices of
edges incident to `w`. -/
def graphIncidenceSetSystem (G : Graph) : SetSystem where
  ground := List.range (graphCanonicalEdges G).length
  sets := G.distinctVertices.map fun w ↦
    ((graphCanonicalEdges G).zipIdx.filter fun p ↦
      decide (p.1.1 = w) || decide (p.1.2 = w)).map Prod.snd

/-- `graphIncidenceSetSystem` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_graphIncidenceSetSystem :
    ComputableInPolyTime graphIncidenceSetSystem encGraph encSetSystem := by
  have hground : ComputableInPolyTime
      (fun G : Graph ↦ List.range (graphCanonicalEdges G).length) encGraph (encList encNat) := by
    have h := (map unary_to_binary).comp (range.comp
      ((length_list (encPair encNat encNat)).comp computableInPolyTime_graphCanonicalEdges))
    simpa only [Function.comp_def, List.map_id'] using h
  have hsets : ComputableInPolyTime
      (fun G : Graph ↦ G.distinctVertices.map fun w ↦
        ((graphCanonicalEdges G).zipIdx.filter fun p ↦
          decide (p.1.1 = w) || decide (p.1.2 = w)).map Prod.snd)
      encGraph encNatSetList := by
    unfold encNatSetList
    refine mapWithInput (by fun_prop) ?_
    have hfilt : ComputableInPolyTime
        (fun q : Graph × ℕ ↦ (graphCanonicalEdges q.1).zipIdx.filter fun p ↦
          decide (p.1.1 = q.2) || decide (p.1.2 = q.2))
        (encPair encGraph encNat) (encList (encPair (encPair encNat encNat) encUnary)) := by
      fun_prop
    exact (map (unary_to_binary.comp (snd _ _))).comp hfilt
  exact computableInPolyTime_setSystemMk hground hsets

/-- Ground set of `graphIncidenceSetSystem G`. -/
@[simp]
theorem graphIncidenceSetSystem_ground (G : Graph) :
    (graphIncidenceSetSystem G).ground = List.range (graphCanonicalEdges G).length := by rfl

/-- Number of candidate sets in `graphIncidenceSetSystem G`. -/
@[simp]
theorem graphIncidenceSetSystem_sets_length (G : Graph) :
    (graphIncidenceSetSystem G).sets.length = G.distinctVertices.length := by
  simp [graphIncidenceSetSystem]

/-- Membership of edge index `e` in the `i`-th vertex-incidence set of
`graphIncidenceSetSystem G`. -/
theorem mem_graphIncidenceSetSystem_set {G : Graph} (i : Fin G.distinctVertices.length)
    {e : ℕ} :
    e ∈ (graphIncidenceSetSystem G).sets[i.1]'(by simp [i.isLt]) ↔
      ∃ he : e < (graphCanonicalEdges G).length,
        ((graphCanonicalEdges G)[e]'he).1 = G.distinctVertices[i.1] ∨
        ((graphCanonicalEdges G)[e]'he).2 = G.distinctVertices[i.1] := by
  simp only [graphIncidenceSetSystem, List.getElem_map, List.mem_map, List.mem_filter,
    Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨pair, idx⟩, ⟨hzip, hinc⟩, rfl⟩
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hzip)
    exact ⟨by simpa using hlt, by simpa only [heq] using hinc⟩
  · rintro ⟨he, hinc⟩
    exact ⟨((graphCanonicalEdges G)[e], e),
      ⟨List.mem_zipIdx_iff_getElem?.mpr (by simp [he]), hinc⟩, rfl⟩

/-- The vertex-edge incidence set system of every simple graph satisfies `IsIntersectOne`. -/
theorem graphIncidenceSetSystem_isIntersectOne (G : Graph) :
    IsIntersectOne (graphIncidenceSetSystem G) := by
  intro i j hij
  rw [Finset.card_le_one]
  intro e₁ he₁ e₂ he₂
  simp only [Finset.mem_inter, List.mem_toFinset] at he₁ he₂
  have hi : i.1 < G.distinctVertices.length := by simpa [graphIncidenceSetSystem] using i.isLt
  have hj : j.1 < G.distinctVertices.length := by simpa [graphIncidenceSetSystem] using j.isLt
  set vi := G.distinctVertices[i.1]
  set vj := G.distinctVertices[j.1]
  have hvw : vi ≠ vj := fun heq ↦
    hij (Fin.ext ((List.Nodup.getElem_inj_iff G.nodup_distinctVertices).mp heq))
  obtain ⟨h1lt, h1i⟩ := (mem_graphIncidenceSetSystem_set ⟨i.1, hi⟩).mp he₁.1
  obtain ⟨_, h1j⟩ := (mem_graphIncidenceSetSystem_set ⟨j.1, hj⟩).mp he₁.2
  obtain ⟨h2lt, h2i⟩ := (mem_graphIncidenceSetSystem_set ⟨i.1, hi⟩).mp he₂.1
  obtain ⟨_, h2j⟩ := (mem_graphIncidenceSetSystem_set ⟨j.1, hj⟩).mp he₂.2
  have hlt1 := (mem_graphCanonicalEdges.mp (List.getElem_mem h1lt)).2.2.1
  have hlt2 := (mem_graphCanonicalEdges.mp (List.getElem_mem h2lt)).2.2.1
  have pairEq : ∀ {p : ℕ × ℕ}, p.1 < p.2 → (p.1 = vi ∨ p.2 = vi) → (p.1 = vj ∨ p.2 = vj) →
      p = (min vi vj, max vi vj) := by
    rintro ⟨a, b⟩ hab ha hb
    dsimp only at hab ha hb
    rcases ha with h1 | h1 <;> rcases hb with h2 | h2
    · exact absurd (h1.symm.trans h2) hvw
    · rw [← h1, ← h2]
      exact Prod.ext (min_eq_left hab.le).symm (max_eq_right hab.le).symm
    · rw [← h1, ← h2]
      exact Prod.ext (min_eq_right hab.le).symm (max_eq_left hab.le).symm
    · exact absurd (h1.symm.trans h2) hvw
  have hsame : (graphCanonicalEdges G)[e₁] = (graphCanonicalEdges G)[e₂] :=
    (pairEq hlt1 h1i h1j).trans (pairEq hlt2 h2i h2j).symm
  exact (List.Nodup.getElem_inj_iff (nodup_graphCanonicalEdges G)).mp hsame

/-- Polynomial-time reduction mapping a `VertexCoverInstance` `(G, k)` to an equivalent
`SetCoverIntersectOne` instance (rejecting `k > |V(G)|` via `(SetSystem.mk [0] [], 0)` since
`VertexCover` checks exact cover size `k ≤ |V(G)|` while `SetCover` checks size at most `k`). -/
def vertexCoverToSetCover (x : VertexCoverInstance) : SetSystem × ℕ :=
  if decide (x.k ≤ x.graph.distinctVertices.length) then
    (graphIncidenceSetSystem x.graph, x.k)
  else
    (SetSystem.mk [0] [], 0)

/-- For `x.k ≤ x.graph.distinctVertices.length`, `vertexCoverToSetCover x` evaluates directly to
`(graphIncidenceSetSystem x.graph, x.k)`. -/
theorem vertexCoverToSetCover_of_le {x : VertexCoverInstance}
    (hk : x.k ≤ x.graph.distinctVertices.length) :
    vertexCoverToSetCover x = (graphIncidenceSetSystem x.graph, x.k) := by
  simp [vertexCoverToSetCover, hk]

/-- `vertexCoverToSetCover` always outputs an intersection-1 set system. -/
theorem vertexCoverToSetCover_isIntersectOne (x : VertexCoverInstance) :
    IsIntersectOne (vertexCoverToSetCover x).1 := by
  unfold vertexCoverToSetCover
  split_ifs
  · exact graphIncidenceSetSystem_isIntersectOne x.graph
  · intro i; exact Fin.elim0 i

/-- `vertexCoverToSetCover` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_vertexCoverToSetCover :
    ComputableInPolyTime vertexCoverToSetCover encVertexCoverInstance encSetCover := by
  have hlen : ComputableInPolyTime
      (fun x : VertexCoverInstance ↦ x.graph.distinctVertices.length)
      encVertexCoverInstance encNat :=
    unary_to_binary.comp ((length_list encNat).comp (by fun_prop))
  have hcmp : ComputableInPolyTime
      (fun x : VertexCoverInstance ↦ decide (x.k ≤ x.graph.distinctVertices.length))
      encVertexCoverInstance encBool :=
    binary_le' (by fun_prop) hlen
  exact ComputableInPolyTime.ite hcmp
    ((computableInPolyTime_graphIncidenceSetSystem.comp (by fun_prop)).prod (by fun_prop))
    (const (SetSystem.mk [0] [], 0))

/-- `vertexCoverToSetCover x ∈ SetCover` iff `x ∈ VertexCover`. -/
theorem vertexCoverToSetCover_mem_setCover_iff (x : VertexCoverInstance) :
    vertexCoverToSetCover x ∈ SetCover ↔ x ∈ VertexCover := by
  classical
  rw [mem_VertexCover_iff_exists_card_le, ← Graph.length_distinctVertices]
  unfold vertexCoverToSetCover
  set G := x.graph
  set V := G.distinctVertices
  split_ifs with hdec
  · have hk : x.k ≤ V.length := of_decide_eq_true hdec
    refine ⟨fun h ↦ ⟨hk, ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩
    · obtain ⟨C, hcov, hcard⟩ := mem_SetCover_iff.mp h
      let f : Fin (graphIncidenceSetSystem G).sets.length → ℕ := fun i ↦
        V[i.1]'(by simpa [graphIncidenceSetSystem, V] using i.isLt)
      let S : Finset ℕ := C.image f
      refine ⟨S, fun v hv ↦ ?_, fun u hu v hv hadj ↦ ?_, Finset.card_image_le.trans hcard⟩
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact Graph.mem_distinctVertices.mp (List.getElem_mem _)
      · have edgeHit : ∀ {a b : ℕ}, a ∈ G.vertices → b ∈ G.vertices → a < b →
            G.toSimpleGraph.Adj a b → a ∈ S ∨ b ∈ S := by
          intro a b ha hb hlt hab
          have hmem : (a, b) ∈ graphCanonicalEdges G :=
            mem_graphCanonicalEdges.mpr ⟨ha, hb, hlt, hab⟩
          obtain ⟨e, he, heq⟩ := List.getElem_of_mem hmem
          obtain ⟨i, hiC, hie⟩ := hcov e (by simpa [graphIncidenceSetSystem] using he)
          have hiV : i.1 < V.length := by simpa [graphIncidenceSetSystem, V] using i.isLt
          obtain ⟨_, hinc⟩ := (mem_graphIncidenceSetSystem_set ⟨i.1, hiV⟩).mp hie
          have hfi : f i ∈ S := Finset.mem_image_of_mem f hiC
          rw [heq] at hinc
          dsimp only at hinc
          exact hinc.imp (fun he ↦ by rwa [he]) (fun he ↦ by rwa [he])
        rcases lt_or_gt_of_ne hadj.ne with hlt | hgt
        · exact edgeHit hu hv hlt hadj
        · exact (edgeHit hv hu hgt hadj.symm).symm
    · obtain ⟨S, _, hcov, hcard⟩ := h
      refine mem_SetCover_iff.mpr ?_
      let C : Finset (Fin (graphIncidenceSetSystem G).sets.length) :=
        Finset.univ.filter fun i ↦
          V[i.1]'(by simpa [graphIncidenceSetSystem, V] using i.isLt) ∈ S
      have hC_le : C.card ≤ S.card :=
        Finset.card_le_card_of_injOn
          (fun i ↦ V[i.1]'(by simpa [graphIncidenceSetSystem, V] using i.isLt))
          (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
          (fun _ _ _ _ heq ↦
            Fin.ext ((List.Nodup.getElem_inj_iff G.nodup_distinctVertices).mp heq))
      refine ⟨C, fun e he ↦ ?_, hC_le.trans hcard⟩
      have helt : e < (graphCanonicalEdges G).length := by
        simpa [graphIncidenceSetSystem] using he
      obtain ⟨hu, hv, _, hadj⟩ := mem_graphCanonicalEdges.mp (List.getElem_mem helt)
      have pickIdx : ∀ {w : ℕ}, w ∈ G.vertices → w ∈ S →
          (w = (graphCanonicalEdges G)[e].1 ∨ w = (graphCanonicalEdges G)[e].2) →
          ∃ i ∈ C, e ∈ (graphIncidenceSetSystem G).sets[i] := by
        intro w hwG hwS hinc
        obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem (Graph.mem_distinctVertices.mpr hwG)
        let i : Fin (graphIncidenceSetSystem G).sets.length :=
          ⟨idx, by simpa [graphIncidenceSetSystem, V] using hidx⟩
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hwS⟩,
          (mem_graphIncidenceSetSystem_set ⟨idx, hidx⟩).mpr ⟨helt, hinc.imp Eq.symm Eq.symm⟩⟩
      exact (hcov _ hu _ hv hadj).elim (fun h ↦ pickIdx hu h (Or.inl rfl))
        (fun h ↦ pickIdx hv h (Or.inr rfl))
  · have hnk : ¬x.k ≤ V.length := fun hk ↦ hdec (decide_eq_true hk)
    rw [mem_SetCover_iff]
    refine ⟨fun ⟨_, hcov, _⟩ ↦ ?_, fun ⟨hk, _⟩ ↦ False.elim (hnk hk)⟩
    obtain ⟨i, _, _⟩ := hcov 0 List.mem_cons_self
    exact Fin.elim0 i

/-- `vertexCoverToSetCover x ∈ SetCoverIntersectOne` iff `x ∈ VertexCover`. -/
theorem vertexCoverToSetCover_mem_setCoverIntersectOne_iff (x : VertexCoverInstance) :
    vertexCoverToSetCover x ∈ SetCoverIntersectOne ↔ x ∈ VertexCover :=
  ⟨fun h ↦ (vertexCoverToSetCover_mem_setCover_iff x).mp h.2,
    fun h ↦ ⟨vertexCoverToSetCover_isIntersectOne x,
      (vertexCoverToSetCover_mem_setCover_iff x).mpr h⟩⟩

/-- `VertexCover` reduces in polynomial time to `SetCoverIntersectOne`. -/
theorem polyTimeReducible_vertexCover_setCoverIntersectOne :
    PolyTimeReducible encVertexCoverInstance encSetCover VertexCover SetCoverIntersectOne :=
  ⟨vertexCoverToSetCover, computableInPolyTime_vertexCoverToSetCover,
    fun x ↦ (vertexCoverToSetCover_mem_setCoverIntersectOne_iff x).symm⟩

/-- `VertexCover` reduces in polynomial time to unweighted `SetCover`. -/
theorem polyTimeReducible_vertexCover_setCover :
    PolyTimeReducible encVertexCoverInstance encSetCover VertexCover SetCover :=
  ⟨vertexCoverToSetCover, computableInPolyTime_vertexCoverToSetCover,
    fun x ↦ (vertexCoverToSetCover_mem_setCover_iff x).symm⟩

/-- `SetCoverIntersectOne` is `NP`-hard. -/
theorem setCoverIntersectOne_npHard : NPHard encSetCover SetCoverIntersectOne :=
  VertexCover_npHard.trans polyTimeReducible_vertexCover_setCoverIntersectOne

/-- **`SetCoverIntersectOne` (SC-1) is `NP`-complete**. -/
theorem setCoverIntersectOne_npComplete : NPComplete encSetCover SetCoverIntersectOne :=
  ⟨setCoverIntersectOne_mem_NP, setCoverIntersectOne_npHard⟩

/-- Unweighted `SetCover` is `NP`-hard. -/
theorem setCover_npHard : NPHard encSetCover SetCover :=
  VertexCover_npHard.trans polyTimeReducible_vertexCover_setCover

/-- **Unweighted `SetCover` is `NP`-complete**. -/
theorem setCover_npComplete : NPComplete encSetCover SetCover :=
  ⟨SetCover_mem_NP, setCover_npHard⟩

/-! ### Polynomial-time SC-1 normalization and quadratic set-count bound -/

/-- Deduplicate a list in first-occurrence order using `selectDistinct`. -/
private def dedupFirst {α : Type} [DecidableEq α] (l : List α) : List α :=
  selectDistinct l (List.replicate l.length true)

private theorem mem_dedupFirst {α : Type} [DecidableEq α] {l : List α} {x : α} :
    x ∈ dedupFirst l ↔ x ∈ l :=
  mem_selectDistinct_replicate

private theorem nodup_dedupFirst {α : Type} [DecidableEq α] (l : List α) :
    (dedupFirst l).Nodup :=
  nodup_selectDistinct _ _

private theorem length_dedupFirst {α : Type} [DecidableEq α] (l : List α) :
    (dedupFirst l).length = l.toFinset.card :=
  length_selectDistinct_replicate l

@[local fun_prop]
private theorem computableInPolyTime_dedupFirst {α : Type} [DecidableEq α]
    (enc : α ↪ List Bool) :
    ComputableInPolyTime (dedupFirst (α := α)) (encList enc) (encList enc) := by
  have hrep : ComputableInPolyTime (fun l : List α ↦ List.replicate l.length true)
      (encList enc) encBits :=
    (bitsReplicate true).comp (length_list enc)
  exact (computableInPolyTime_selectDistinct enc).comp (id'.prod hrep)

/-- Canonical restriction of a candidate subset `A` to a duplicate-free ground list `U`. -/
private def restrictToGround (U A : List ℕ) : List ℕ :=
  U.filter fun u ↦ decide (u ∈ A)

@[local fun_prop]
private theorem computableInPolyTime_restrictToGround :
    ComputableInPolyTime (fun p : List ℕ × List ℕ ↦ restrictToGround p.1 p.2)
      (encPair (encList encNat) (encList encNat)) (encList encNat) := by
  unfold restrictToGround
  fun_prop

/-- Canonicalize a finite set system `S`: deduplicate `S.ground`, restrict every candidate set to
`S.ground` in canonical ground order, discard empty restrictions, and deduplicate identical
candidate sets. -/
def normalizeSetSystem (S : SetSystem) : SetSystem :=
  let U := dedupFirst S.ground
  let raw := (S.sets.map (restrictToGround U)).filter fun B ↦ !B.isEmpty
  SetSystem.mk U (dedupFirst raw)

/-- Lift a cover index list `I` of `normalizeSetSystem S` back to a cover index list of `S` of
identical length. -/
def liftNormalizedCover (S : SetSystem) (I : List ℕ) : List ℕ :=
  let U := dedupFirst S.ground
  let mapped := S.sets.map (restrictToGround U)
  let N := normalizeSetSystem S
  I.map fun j ↦ mapped.idxOf (N.sets.getD j [])

/-- `normalizeSetSystem` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_normalizeSetSystem :
    ComputableInPolyTime normalizeSetSystem encSetSystem encSetSystem := by
  have hu : ComputableInPolyTime (fun S : SetSystem ↦ dedupFirst S.ground)
      encSetSystem (encList encNat) := by
    fun_prop
  have hmapped : ComputableInPolyTime
      (fun S : SetSystem ↦ S.sets.map (restrictToGround (dedupFirst S.ground)))
      encSetSystem (encList (encList encNat)) :=
    mapWithInput computableInPolyTime_setSystemSets
      (computableInPolyTime_restrictToGround.comp ((hu.comp (fst _ _)).prod (snd _ _)))
  have hraw : ComputableInPolyTime
      (fun S : SetSystem ↦
        (S.sets.map (restrictToGround (dedupFirst S.ground))).filter fun B ↦ !B.isEmpty)
      encSetSystem (encList (encList encNat)) :=
    (filter (by fun_prop)).comp hmapped
  exact computableInPolyTime_setSystemMk hu
    ((computableInPolyTime_dedupFirst (encList encNat)).comp hraw)

/-- `liftNormalizedCover` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_liftNormalizedCover :
    ComputableInPolyTime (fun p : SetSystem × List ℕ ↦ liftNormalizedCover p.1 p.2)
      (encPair encSetSystem (encList encNat)) (encList encNat) := by
  let encQ := encPair (encPair encSetSystem (encList encNat)) encNat
  have hu : ComputableInPolyTime (fun S : SetSystem ↦ dedupFirst S.ground)
      encSetSystem (encList encNat) := by
    fun_prop
  have hmappedS : ComputableInPolyTime
      (fun S : SetSystem ↦ S.sets.map (restrictToGround (dedupFirst S.ground)))
      encSetSystem (encList (encList encNat)) :=
    mapWithInput computableInPolyTime_setSystemSets
      (computableInPolyTime_restrictToGround.comp ((hu.comp (fst _ _)).prod (snd _ _)))
  have hmapped : ComputableInPolyTime
      (fun q : (SetSystem × List ℕ) × ℕ ↦
        q.1.1.sets.map (restrictToGround (dedupFirst q.1.1.ground)))
      encQ (encList (encList encNat)) :=
    hmappedS.comp ((fst _ _).comp (fst _ _))
  have hNsets : ComputableInPolyTime
      (fun q : (SetSystem × List ℕ) × ℕ ↦ (normalizeSetSystem q.1.1).sets)
      encQ (encList (encList encNat)) :=
    computableInPolyTime_setSystemSets.comp
      (computableInPolyTime_normalizeSetSystem.comp ((fst _ _).comp (fst _ _)))
  have htarget : ComputableInPolyTime
      (fun q : (SetSystem × List ℕ) × ℕ ↦ (normalizeSetSystem q.1.1).sets.getD q.2 [])
      encQ (encList encNat) :=
    listGetD_binary [] hNsets (snd (encPair encSetSystem (encList encNat)) encNat)
  have hidx : ComputableInPolyTime
      (fun q : (SetSystem × List ℕ) × ℕ ↦
        (q.1.1.sets.map (restrictToGround (dedupFirst q.1.1.ground))).idxOf
          ((normalizeSetSystem q.1.1).sets.getD q.2 []))
      encQ encUnary := by
    convert (idxOf (encList encNat)).comp (hmapped.prod htarget) using 1
    funext q
    dsimp only [Function.comp_def, List.idxOf]
    congr 1
    funext x
    exact Bool.eq_iff_iff.mpr ⟨fun h ↦ decide_eq_true (beq_iff_eq.mp h),
      fun h ↦ beq_iff_eq.mpr (of_decide_eq_true h)⟩
  exact mapWithInput (snd encSetSystem (encList encNat)) (unary_to_binary.comp hidx)

/-- `(normalizeSetSystem S).ground` has no duplicate elements. -/
theorem normalizeSetSystem_ground_nodup (S : SetSystem) :
    (normalizeSetSystem S).ground.Nodup :=
  nodup_dedupFirst S.ground

/-- `normalizeSetSystem S` preserves the ground finset of `S`. -/
@[simp]
theorem normalizeSetSystem_ground_toFinset (S : SetSystem) :
    (normalizeSetSystem S).ground.toFinset = S.ground.toFinset := by
  ext u
  simp [normalizeSetSystem, mem_dedupFirst]

/-- `(normalizeSetSystem S).ground.length` equals `S.ground.toFinset.card`. -/
@[simp]
theorem normalizeSetSystem_ground_length (S : SetSystem) :
    (normalizeSetSystem S).ground.length = S.ground.toFinset.card :=
  length_dedupFirst S.ground

/-- `(normalizeSetSystem S).sets` has no duplicate sets, and every candidate set is nonempty,
duplicate-free, contained in `(normalizeSetSystem S).ground`, and obtained by restricting some
`S.sets[i]` to `(normalizeSetSystem S).ground`. -/
theorem normalizeSetSystem_sets_wf (S : SetSystem) :
    (normalizeSetSystem S).sets.Nodup ∧
    ∀ B ∈ (normalizeSetSystem S).sets,
      B ≠ [] ∧ B.Nodup ∧ (∀ u ∈ B, u ∈ (normalizeSetSystem S).ground) ∧
      ∃ i : Fin S.sets.length, B =
        (normalizeSetSystem S).ground.filter (fun u ↦ decide (u ∈ S.sets[i])) := by
  refine ⟨nodup_dedupFirst _, fun B hB ↦ ?_⟩
  simp only [normalizeSetSystem, mem_dedupFirst, List.mem_filter, List.mem_map,
    Bool.not_eq_true', List.isEmpty_eq_false_iff] at hB
  obtain ⟨⟨A, hA, rfl⟩, hne⟩ := hB
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
  exact ⟨hne, (nodup_dedupFirst S.ground).filter _,
    fun u hu ↦ (List.mem_filter.mp hu).1, ⟨i, hi⟩, rfl⟩

/-- `normalizeSetSystem` preserves `IsIntersectOne`. -/
theorem normalizeSetSystem_isIntersectOne {S : SetSystem} (hS : IsIntersectOne S) :
    IsIntersectOne (normalizeSetSystem S) := by
  obtain ⟨hnd, hwf⟩ := normalizeSetSystem_sets_wf S
  intro i j hij
  have hBi := hwf _ (List.getElem_mem i.isLt)
  have hBj := hwf _ (List.getElem_mem j.isLt)
  obtain ⟨i₀, hi₀⟩ := hBi.2.2.2
  obtain ⟨j₀, hj₀⟩ := hBj.2.2.2
  have hij₀ : i₀ ≠ j₀ := fun heq ↦
    hij (Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp (hi₀.trans (heq ▸ hj₀.symm))))
  refine (Finset.card_le_card fun u hu ↦ ?_).trans (hS i₀ j₀ hij₀)
  simp only [Finset.mem_inter, List.mem_toFinset] at hu ⊢
  have h1 : u ∈ (normalizeSetSystem S).ground.filter (fun x ↦ decide (x ∈ S.sets[i₀])) := by
    rw [← hi₀]; exact hu.1
  have h2 : u ∈ (normalizeSetSystem S).ground.filter (fun x ↦ decide (x ∈ S.sets[j₀])) := by
    rw [← hj₀]; exact hu.2
  exact ⟨of_decide_eq_true (List.mem_filter.mp h1).2, of_decide_eq_true (List.mem_filter.mp h2).2⟩

/-- Lifting any valid cover list of `normalizeSetSystem S` produces a valid cover list of `S` of
the exact same length. -/
theorem liftNormalizedCover_isCoverList {S : SetSystem} {I : List ℕ}
    (hI : (normalizeSetSystem S).isCoverList I = true) :
    S.isCoverList (liftNormalizedCover S I) = true ∧
      (liftNormalizedCover S I).length = I.length := by
  set U := dedupFirst S.ground
  set mapped := S.sets.map (restrictToGround U)
  set N := normalizeSetSystem S
  obtain ⟨hbound, hcov⟩ := (N.isCoverList_eq_true_iff I).mp hI
  have hmem_mapped : ∀ (j : ℕ) (hj : j < N.sets.length), N.sets[j]'hj ∈ mapped := fun j hj ↦ by
    have hm : N.sets[j]'hj ∈ N.sets := List.getElem_mem hj
    simp only [N, normalizeSetSystem, mem_dedupFirst, List.mem_filter] at hm
    exact hm.1
  refine ⟨(S.isCoverList_eq_true_iff _).mpr ⟨?_, ?_⟩, by simp [liftNormalizedCover]⟩
  · intro idx hidx
    simp only [liftNormalizedCover, List.mem_map] at hidx
    obtain ⟨j, hjI, rfl⟩ := hidx
    have hj : j < N.sets.length := hbound j hjI
    rw [List.getD_eq_getElem _ _ hj]
    have hlt := List.idxOf_lt_length_iff.mpr (hmem_mapped j hj)
    simpa [mapped] using hlt
  · intro u hu
    have huN : u ∈ N.ground := mem_dedupFirst.mpr hu
    obtain ⟨j, hjI, hj, huj⟩ := hcov u huN
    let idx := mapped.idxOf (N.sets[j]'hj)
    have hidx_m : idx < mapped.length := List.idxOf_lt_length_iff.mpr (hmem_mapped j hj)
    have hidx_s : idx < S.sets.length := by simpa [mapped] using hidx_m
    have heq : restrictToGround U (S.sets[idx]'hidx_s) = N.sets[j]'hj := by
      have h : mapped[idx]'hidx_m = N.sets[j]'hj := List.idxOf_lt_length_iff.mp hidx_m |> fun _ ↦
        List.getElem_idxOf hidx_m
      simpa [mapped] using h
    have hu_filt : u ∈ restrictToGround U (S.sets[idx]'hidx_s) := by
      rw [heq]; exact huj
    have hu_in : u ∈ S.sets[idx]'hidx_s :=
      of_decide_eq_true (List.mem_filter.mp hu_filt).2
    refine ⟨idx, ?_, hidx_s, hu_in⟩
    simp only [liftNormalizedCover, List.mem_map]
    refine ⟨j, hjI, ?_⟩
    change mapped.idxOf (N.sets.getD j []) = idx
    rw [List.getD_eq_getElem _ _ hj]

/-- `normalizeSetSystem` preserves `Coverable`. -/
@[simp]
theorem normalizeSetSystem_coverable_iff (S : SetSystem) :
    (normalizeSetSystem S).Coverable ↔ S.Coverable := by
  set U := dedupFirst S.ground
  set N := normalizeSetSystem S
  constructor
  · rintro ⟨C, hC⟩
    let I := (C.image Fin.val).toList
    have hI : N.isCoverList I = true := (N.isCoverList_eq_true_iff I).mpr
      ⟨fun j hj ↦ by
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hj); exact k.isLt,
      fun u hu ↦ by
        obtain ⟨k, hkC, huk⟩ := hC u hu
        exact ⟨k.1, Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hkC), k.isLt, huk⟩⟩
    obtain ⟨_, hcovS⟩ := (S.isCoverList_eq_true_iff _).mp (liftNormalizedCover_isCoverList hI).1
    refine ⟨Finset.univ, fun u hu ↦ ?_⟩
    obtain ⟨idx, _, hlt, hui⟩ := hcovS u hu
    exact ⟨⟨idx, hlt⟩, Finset.mem_univ _, hui⟩
  · rintro ⟨_, hC⟩
    refine ⟨Finset.univ, fun u hu ↦ ?_⟩
    obtain ⟨i, _, hui⟩ := hC u (mem_dedupFirst.mp hu)
    let B := restrictToGround U S.sets[i]
    have huB : u ∈ B := List.mem_filter.mpr ⟨hu, decide_eq_true hui⟩
    have hBN : B ∈ N.sets := mem_dedupFirst.mpr <| List.mem_filter.mpr
      ⟨List.mem_map_of_mem (List.getElem_mem i.isLt),
        Bool.not_eq_true' _ |>.mpr (List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem huB))⟩
    obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hBN
    exact ⟨⟨j, hj⟩, Finset.mem_univ _, heq.symm ▸ huB⟩

/-- `normalizeSetSystem` preserves `optCoverSize`. -/
@[simp]
theorem normalizeSetSystem_optCoverSize (S : SetSystem) :
    (normalizeSetSystem S).optCoverSize = S.optCoverSize := by
  classical
  set U := dedupFirst S.ground
  set N := normalizeSetSystem S
  by_cases hS : S.Coverable
  · have hN : N.Coverable := (normalizeSetSystem_coverable_iff S).mpr hS
    refine le_antisymm ?_ ?_
    · obtain ⟨C, hC, hcard⟩ := SetSystem.exists_isCover_optCoverSize hS
      let D : Finset (Fin N.sets.length) := Finset.univ.filter fun j ↦
        ∃ i ∈ C, restrictToGround U S.sets[i] = N.sets[j]
      have hD_cov : N.IsCover D := fun u hu ↦ by
        obtain ⟨i, hiC, hui⟩ := hC u (mem_dedupFirst.mp hu)
        let B := restrictToGround U S.sets[i]
        have huB : u ∈ B := List.mem_filter.mpr ⟨hu, decide_eq_true hui⟩
        have hBN : B ∈ N.sets := mem_dedupFirst.mpr <| List.mem_filter.mpr
          ⟨List.mem_map_of_mem (List.getElem_mem i.isLt),
            Bool.not_eq_true' _ |>.mpr (List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem huB))⟩
        obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hBN
        exact ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hiC, heq.symm⟩,
          heq.symm ▸ huB⟩
      have hD_le : D.card ≤ C.card := by
        have hsub : D ⊆ C.biUnion fun i ↦
            Finset.univ.filter fun j : Fin N.sets.length ↦
              restrictToGround U S.sets[i] = N.sets[j] := fun j hj ↦ by
          obtain ⟨_, i, hiC, heq⟩ := Finset.mem_filter.mp hj
          exact Finset.mem_biUnion.mpr ⟨i, hiC, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩
        refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
        have h1 : ∀ i ∈ C, (Finset.univ.filter fun j : Fin N.sets.length ↦
            restrictToGround U S.sets[i] = N.sets[j]).card ≤ 1 := fun _ _ ↦
          Finset.card_le_one.mpr fun _ h₁ _ h₂ ↦ Fin.ext <|
            (List.Nodup.getElem_inj_iff (normalizeSetSystem_sets_wf S).1).mp
              ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)
        exact (Finset.sum_le_sum h1).trans (by simp)
      exact (SetSystem.optCoverSize_le hD_cov).trans (hD_le.trans hcard.le)
    · obtain ⟨D, hD, hcard⟩ := SetSystem.exists_isCover_optCoverSize hN
      let I := (D.image Fin.val).toList
      have hI : N.isCoverList I = true := (N.isCoverList_eq_true_iff I).mpr
        ⟨fun j hj ↦ by
          obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hj); exact k.isLt,
        fun u hu ↦ by
          obtain ⟨k, hkD, huk⟩ := hD u hu
          exact ⟨k.1, Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hkD), k.isLt, huk⟩⟩
      obtain ⟨hL, hlen⟩ := liftNormalizedCover_isCoverList hI
      obtain ⟨_, hcov⟩ := (S.isCoverList_eq_true_iff _).mp hL
      let C : Finset (Fin S.sets.length) := Finset.univ.filter fun i ↦
        i.1 ∈ (liftNormalizedCover S I).toFinset
      have hC_cov : S.IsCover C := fun u hu ↦ by
        obtain ⟨idx, hidx, hlt, hui⟩ := hcov u hu
        exact ⟨⟨idx, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, List.mem_toFinset.mpr hidx⟩,
          hui⟩
      have hC_le : C.card ≤ (liftNormalizedCover S I).toFinset.card :=
        Finset.card_le_card_of_injOn Fin.val
          (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
          (fun _ _ _ _ h ↦ Fin.ext h)
      have hI_len : I.length = D.card := by
        simp [I, Finset.card_image_of_injective _ Fin.val_injective]
      exact (SetSystem.optCoverSize_le hC_cov).trans <|
        hC_le.trans <| (List.toFinset_card_le _).trans (by rw [hlen, hI_len, hcard])
  · have hN : ¬N.Coverable := mt (normalizeSetSystem_coverable_iff S).mp hS
    rw [SetSystem.optCoverSize_eq_zero_of_not_coverable hN,
      SetSystem.optCoverSize_eq_zero_of_not_coverable hS]

/-- **Sharp SC-1 set-count bound**: on any intersection-1 set system `S` with
`n = S.ground.toFinset.card` distinct ground elements, `normalizeSetSystem S` has at most
`n.choose 2 + n` candidate sets (at most `n` singletons and at most `n.choose 2` sets of size at
least `2`). -/
theorem normalizeSetSystem_sets_length_le {S : SetSystem} (hS : IsIntersectOne S) :
    (normalizeSetSystem S).sets.length ≤
      S.ground.toFinset.card.choose 2 + S.ground.toFinset.card := by
  classical
  set N := normalizeSetSystem S
  set G := S.ground.toFinset
  have hN := normalizeSetSystem_isIntersectOne hS
  obtain ⟨hnd, hwf⟩ := normalizeSetSystem_sets_wf S
  let big : Finset (Fin N.sets.length) := Finset.univ.filter fun i ↦ 2 ≤ N.sets[i].length
  let small : Finset (Fin N.sets.length) := Finset.univ.filter fun i ↦ ¬2 ≤ N.sets[i].length
  have hsplit : N.sets.length = big.card + small.card := by
    have hu : big ∪ small = Finset.univ := by
      ext i
      simp only [big, small, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      exact em _
    have hd : Disjoint big small := Finset.disjoint_left.mpr fun _ h1 h2 ↦
      (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hc := congrArg Finset.card hu
    rw [Finset.card_union_of_disjoint hd, Finset.card_univ, Fintype.card_fin] at hc
    exact hc.symm
  have hbig : big.card ≤ G.card.choose 2 := by
    rw [← Finset.card_powersetCard 2 G]
    let pairOf (i : Fin N.sets.length) : Finset ℕ :=
      if h : 2 ≤ N.sets[i.1].length then
        {N.sets[i.1][0]'(by omega), N.sets[i.1][1]'(by omega)}
      else ∅
    refine Finset.card_le_card_of_injOn pairOf (fun i hi ↦ ?_) (fun i hi j hj heq ↦ ?_)
    · have h2 : 2 ≤ N.sets[i.1].length := (Finset.mem_filter.mp hi).2
      obtain ⟨_, hBnd, hBsub, _⟩ := hwf N.sets[i.1] (List.getElem_mem i.isLt)
      have hne01 : N.sets[i.1][0]'(by omega) ≠ N.sets[i.1][1]'(by omega) := fun h ↦
        absurd ((List.Nodup.getElem_inj_iff hBnd).mp h) (by decide)
      have hp : pairOf i = {N.sets[i.1][0]'(by omega), N.sets[i.1][1]'(by omega)} := by
        simp [pairOf, h2]
      have huG : ∀ x ∈ N.sets[i.1], x ∈ G := fun x hx ↦
        (congrArg (x ∈ ·) (normalizeSetSystem_ground_toFinset S)).mp
          (List.mem_toFinset.mpr (hBsub x hx))
      change pairOf i ∈ Finset.powersetCard 2 G
      rw [hp, Finset.mem_powersetCard]
      refine ⟨fun u hu ↦ ?_, Finset.card_pair hne01⟩
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact huG _ (List.getElem_mem _)
      · rw [Finset.mem_singleton.mp hu']
        exact huG _ (List.getElem_mem _)
    · by_contra hij
      have hi2 : 2 ≤ N.sets[i.1].length := (Finset.mem_filter.mp hi).2
      have hj2 : 2 ≤ N.sets[j.1].length := (Finset.mem_filter.mp hj).2
      obtain ⟨_, hBnd, _, _⟩ := hwf N.sets[i.1] (List.getElem_mem i.isLt)
      have hne01 : N.sets[i.1][0]'(by omega) ≠ N.sets[i.1][1]'(by omega) := fun h ↦
        absurd ((List.Nodup.getElem_inj_iff hBnd).mp h) (by decide)
      have hpi : pairOf i = {N.sets[i.1][0]'(by omega), N.sets[i.1][1]'(by omega)} := by
        simp [pairOf, hi2]
      have hpj : pairOf j = {N.sets[j.1][0]'(by omega), N.sets[j.1][1]'(by omega)} := by
        simp [pairOf, hj2]
      have hpair_eq : ({N.sets[i.1][0]'(by omega), N.sets[i.1][1]'(by omega)} : Finset ℕ) =
          {N.sets[j.1][0]'(by omega), N.sets[j.1][1]'(by omega)} :=
        hpi.symm.trans (heq.trans hpj)
      have hsub : ({N.sets[i.1][0]'(by omega), N.sets[i.1][1]'(by omega)} : Finset ℕ) ⊆
          N.sets[i].toFinset ∩ N.sets[j].toFinset := fun u hu ↦ by
        have hui : u ∈ N.sets[i].toFinset := by
          rcases Finset.mem_insert.mp hu with rfl | hu'
          · exact List.mem_toFinset.mpr (List.getElem_mem _)
          · rw [Finset.mem_singleton.mp hu']; exact List.mem_toFinset.mpr (List.getElem_mem _)
        have huj : u ∈ N.sets[j].toFinset := by
          rw [hpair_eq] at hu
          rcases Finset.mem_insert.mp hu with rfl | hu'
          · exact List.mem_toFinset.mpr (List.getElem_mem _)
          · rw [Finset.mem_singleton.mp hu']; exact List.mem_toFinset.mpr (List.getElem_mem _)
        exact Finset.mem_inter.mpr ⟨hui, huj⟩
      have hcard2 : 2 ≤ (N.sets[i].toFinset ∩ N.sets[j].toFinset).card := by
        have h1 := Finset.card_le_card hsub
        rwa [Finset.card_pair hne01] at h1
      exact absurd (hcard2.trans (hN i j hij)) (by decide)
  have hsmall : small.card ≤ G.card := by
    refine Finset.card_le_card_of_injOn (fun i ↦ N.sets[i.1].headD 0) (fun i _ ↦ ?_)
      (fun i hi j hj heq ↦ ?_)
    · obtain ⟨hne, _, hBsub, _⟩ := hwf N.sets[i.1] (List.getElem_mem i.isLt)
      cases hBi : N.sets[i.1] with
      | nil => exact absurd hBi hne
      | cons a _ =>
        have haN : a ∈ N.ground := hBsub a (by rw [hBi]; exact List.mem_cons_self)
        change (N.sets[i.1].headD 0) ∈ S.ground.toFinset
        rw [hBi, List.headD_cons, ← normalizeSetSystem_ground_toFinset S]
        exact List.mem_toFinset.mpr haN
    · have hi1 : ¬2 ≤ N.sets[i.1].length := (Finset.mem_filter.mp hi).2
      have hj1 : ¬2 ≤ N.sets[j.1].length := (Finset.mem_filter.mp hj).2
      have hni := (hwf N.sets[i.1] (List.getElem_mem i.isLt)).1
      have hnj := (hwf N.sets[j.1] (List.getElem_mem j.isLt)).1
      have sing : ∀ l : List ℕ, l ≠ [] → ¬2 ≤ l.length → l = [l.headD 0] := by
        rintro (_ | ⟨a, _ | ⟨b, tl⟩⟩) h1 h2
        · exact absurd rfl h1
        · rfl
        · exact absurd (by simp : 2 ≤ (a :: b :: tl).length) h2
      have hsi := sing N.sets[i.1] hni hi1
      have hsj := sing N.sets[j.1] hnj hj1
      have hsame : N.sets[i.1] = N.sets[j.1] := by
        calc N.sets[i.1] = [N.sets[i.1].headD 0] := hsi
          _ = [N.sets[j.1].headD 0] := congrArg (fun x ↦ [x]) heq
          _ = N.sets[j.1] := hsj.symm
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp hsame)
  omega

/-- For `n = S.ground.toFinset.card ≥ 3`, a normalized SC-1 set system satisfies
`(normalizeSetSystem S).sets.length + (normalizeSetSystem S).ground.length ≤ n ^ 2`. -/
theorem normalizeSetSystem_total_size_le_sq {S : SetSystem} (hS : IsIntersectOne S)
    (hn : 3 ≤ S.ground.toFinset.card) :
    (normalizeSetSystem S).sets.length + (normalizeSetSystem S).ground.length ≤
      S.ground.toFinset.card ^ 2 := by
  have h1 := normalizeSetSystem_sets_length_le hS
  rw [normalizeSetSystem_ground_length]
  set n := S.ground.toFinset.card
  have hch : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
  have hsub : n * (n - 1) + n = n * n := by
    cases n with
    | zero => omega
    | succ k => simp [Nat.mul_succ, Nat.succ_mul, Nat.add_comm]
  have h3n : 3 * n ≤ n * n := by nlinarith
  rw [sq]
  omega

-- Non-vacuity check: the triangle graph `K_3` induces a non-trivial intersection-1 set system on
-- `3` ground elements with `3` sets and exact optimum cover size `2`, while adding a duplicate-pair
-- set fails `IsIntersectOne`.
example : (∃ S : SetSystem, IsIntersectOne S ∧ S.Coverable ∧ S.ground.toFinset.card = 3 ∧
      S.optCoverSize = 2 ∧ (normalizeSetSystem S).optCoverSize = 2) ∧
    (∃ S' : SetSystem, ¬IsIntersectOne S') := by
  refine ⟨?_, ⟨SetSystem.mk [0, 1] [[0, 1], [0, 1]], ?_⟩⟩
  · let G : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2), (0, 2)]⟩
    have hmem : (⟨G, 2⟩ : VertexCoverInstance) ∈ VertexCover := by
      rw [mem_VertexCover_iff_mk]
      refine ⟨{0, 1}, by decide, ?_, by decide⟩
      intro u hu v hv hadj
      have hne := hadj.ne
      have hedge := (Graph.toSimpleGraph_adj.mp hadj).2
      simp only [G, List.mem_cons, List.not_mem_nil, or_false] at hu hv hedge
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> simp at hne hedge ⊢
    have hno1 : (⟨G, 1⟩ : VertexCoverInstance) ∉ VertexCover := by
      rw [mem_VertexCover_iff_mk]
      rintro ⟨S, _, hcov, hcard⟩
      have h01 := hcov 0 (by decide) 1 (by decide) (by rw [Graph.toSimpleGraph_adj]; decide)
      have h12 := hcov 1 (by decide) 2 (by decide) (by rw [Graph.toSimpleGraph_adj]; decide)
      have h02 := hcov 0 (by decide) 2 (by decide) (by rw [Graph.toSimpleGraph_adj]; decide)
      have hle1 := Finset.card_le_one.mp hcard.le
      rcases h01 with h0 | h1 <;> rcases h12 with h1' | h2 <;> rcases h02 with h0' | h2'
      exacts [absurd (hle1 0 h0 1 h1') (by decide), absurd (hle1 0 h0 1 h1') (by decide),
        absurd (hle1 0 h0 2 h2) (by decide), absurd (hle1 0 h0 2 h2) (by decide),
        absurd (hle1 1 h1 0 h0') (by decide), absurd (hle1 1 h1 2 h2') (by decide),
        absurd (hle1 1 h1 0 h0') (by decide), absurd (hle1 1 h1 2 h2) (by decide)]
    let S := graphIncidenceSetSystem G
    have h2 : (S, 2) ∈ SetCover := by
      have heq : vertexCoverToSetCover ⟨G, 2⟩ = (S, 2) := by
        have hlen : G.distinctVertices.length = 3 := by decide
        simp [vertexCoverToSetCover, hlen, S]
      exact heq ▸ (vertexCoverToSetCover_mem_setCover_iff ⟨G, 2⟩).mpr hmem
    have hnot1 : (S, 1) ∉ SetCover := fun h1 ↦ hno1 <|
      (vertexCoverToSetCover_mem_setCover_iff ⟨G, 1⟩).mp <| by
        have heq : vertexCoverToSetCover ⟨G, 1⟩ = (S, 1) := by
          have hlen : G.distinctVertices.length = 3 := by decide
          simp [vertexCoverToSetCover, hlen, S]
        exact heq.symm ▸ h1
    obtain ⟨hcovS, hle2⟩ := mem_SetCover_iff_optCoverSize.mp h2
    have hgt1 : ¬S.optCoverSize ≤ 1 := fun hle1 ↦
      hnot1 (mem_SetCover_iff_optCoverSize.mpr ⟨hcovS, hle1⟩)
    have hopt : S.optCoverSize = 2 := by omega
    have hcard3 : S.ground.toFinset.card = 3 := by
      decide
    exact ⟨S, graphIncidenceSetSystem_isIntersectOne G, hcovS, hcard3, hopt,
      (normalizeSetSystem_optCoverSize S).trans hopt⟩
  · rw [← isIntersectOneBool_eq_true_iff]
    decide

end Cslib.Complexity
end
