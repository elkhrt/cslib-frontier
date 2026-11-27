/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy

import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.EncLen
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.List.GetD

/-!
# Parameterized Subgraph Isomorphism

This module defines the `SubgraphIsomorphism` decision problem over encoded finite simple graphs
(`Cslib.Complexity.Graph`), parameterized by the number of edges `patternEdgeCount` in the pattern
graph $H$, together with the standard isolated-vertex-free restriction `SubgraphIsomorphismNoIso`.

## Main definitions

* `CslibFrontier.ParameterizedComplexity.SubgraphIsoInstance`,
  `CslibFrontier.ParameterizedComplexity.encSubgraphIsoInstance`,
  `CslibFrontier.ParameterizedComplexity.SubgraphIsoInstance.patternEdgeCount`,
  `CslibFrontier.ParameterizedComplexity.SubgraphIsoInstance.HasNoIsolatedPatternVertices`.
* `CslibFrontier.ParameterizedComplexity.SubgraphIsomorphism`,
  `CslibFrontier.ParameterizedComplexity.SubgraphIsomorphismNoIso`.

## Main results

* `CslibFrontier.ParameterizedComplexity.patternEdgeCount_eq_card_edgeFinset`,
  `CslibFrontier.ParameterizedComplexity.card_patternVertices_le_two_mul_patternEdgeCount`,
  `CslibFrontier.ParameterizedComplexity.two_le_card_patternVertices_of_pos`,
  `CslibFrontier.ParameterizedComplexity.degree_le_patternEdgeCount`.
* `CslibFrontier.ParameterizedComplexity.exists_mem_subgraphIsomorphismNoIso_of_pos`,
  `CslibFrontier.ParameterizedComplexity.exists_not_mem_subgraphIsomorphismNoIso`,
  `CslibFrontier.ParameterizedComplexity.exists_not_hasNoIsolatedPatternVertices`.
* `CslibFrontier.ParameterizedComplexity.subgraphIsomorphism_mem_NP`,
  `CslibFrontier.ParameterizedComplexity.subgraphIsomorphismNoIso_mem_NP`,
  `CslibFrontier.ParameterizedComplexity.subgraphIsomorphismNoIso_decidableInTimeO`,
  `CslibFrontier.ParameterizedComplexity.subgraphIsomorphismNoIso_mem_XP`,
  `CslibFrontier.ParameterizedComplexity.subgraphIsomorphismNoIso_slice_mem_P`.
* `CslibFrontier.ParameterizedComplexity.fptReducible_subgraphIsomorphism_noIso`,
  `CslibFrontier.ParameterizedComplexity.fptReducible_clique_subgraphIsomorphismNoIso`,
  `CslibFrontier.ParameterizedComplexity.subgraphIsomorphismNoIso_wHard`,
  `CslibFrontier.ParameterizedComplexity.subgraphIsomorphism_wHard`.
-/

public section

namespace CslibFrontier.ParameterizedComplexity

open Cslib.Complexity Turing.MultiTapeTM

/-! ### 1. Instances, Encodings, and Pattern Graph Invariants -/

/-- An instance `(target, pattern)` of **Subgraph Isomorphism**, asking whether `target` ($G$)
contains a subgraph isomorphic to `pattern` ($H$). -/
@[ext]
structure SubgraphIsoInstance where
  /-- Host graph $G$ in which a copy of `pattern` is sought. -/
  target : Graph
  /-- Pattern graph $H$ to embed injectively into `target`. -/
  pattern : Graph
  deriving DecidableEq, Repr, Inhabited

/-- Framed pair encoding of `SubgraphIsoInstance` via `encGraph` on `(target, pattern)`. -/
def encSubgraphIsoInstance : SubgraphIsoInstance ↪ List Bool :=
  ⟨fun I => encPair encGraph encGraph (I.target, I.pattern), fun x y h => by
    have h' := (encPair encGraph encGraph).injective h; cases x; cases y; simp_all⟩

@[simp]
theorem encSubgraphIsoInstance_apply (I : SubgraphIsoInstance) :
    encSubgraphIsoInstance I = encPair encGraph encGraph (I.target, I.pattern) := by rfl

private theorem length_encGraph_le_encSubgraphIso (I : SubgraphIsoInstance) :
    (encGraph I.target).length ≤ (encSubgraphIsoInstance I).length ∧
      (encGraph I.pattern).length ≤ (encSubgraphIsoInstance I).length := by
  rw [encSubgraphIsoInstance_apply, length_encPair]; dsimp only; omega

private theorem computableInDegree_subgraphIsoFields :
    ComputableInDegree (fun I : SubgraphIsoInstance => (I.target, I.pattern))
      encSubgraphIsoInstance (encPair encGraph encGraph) 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- Projecting `SubgraphIsoInstance.target` is polynomial-time computable. -/
@[fun_prop]
theorem computableInPolyTime_subgraphIsoTarget {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → SubgraphIsoInstance}
    (hg : ComputableInPolyTime g encIn encSubgraphIsoInstance) :
    ComputableInPolyTime (fun x => (g x).target) encIn encGraph :=
  (ComputableInDegree.fst' computableInDegree_subgraphIsoFields).computableInPolyTime.comp hg

/-- Projecting `SubgraphIsoInstance.pattern` is polynomial-time computable. -/
@[fun_prop]
theorem computableInPolyTime_subgraphIsoPattern {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → SubgraphIsoInstance}
    (hg : ComputableInPolyTime g encIn encSubgraphIsoInstance) :
    ComputableInPolyTime (fun x => (g x).pattern) encIn encGraph :=
  (ComputableInDegree.snd' computableInDegree_subgraphIsoFields).computableInPolyTime.comp hg

/-- Constructing a `SubgraphIsoInstance` from computed graphs is polynomial-time computable. -/
@[fun_prop]
theorem computableInPolyTime_subgraphIsoMk {γ : Type} {encIn : γ ↪ List Bool}
    {G H : γ → Graph}
    (hG : ComputableInPolyTime G encIn encGraph)
    (hH : ComputableInPolyTime H encIn encGraph) :
    ComputableInPolyTime (fun x => SubgraphIsoInstance.mk (G x) (H x))
      encIn encSubgraphIsoInstance :=
  (hG.prod hH).of_enc_eq fun _ => rfl

private def orderedEdgeList (G : Graph) : List (ℕ × ℕ) :=
  G.distinctVertices.flatMap fun u =>
    (G.distinctVertices.filter fun v => decide (u < v) && G.adjBool u v).map fun v => (u, v)

/-- Number of undirected edges in `I.pattern.induced`, computed by counting ordered adjacent
pairs `u < v` among `I.pattern.distinctVertices`. -/
def SubgraphIsoInstance.patternEdgeCount (I : SubgraphIsoInstance) : ℕ :=
  (orderedEdgeList I.pattern).length

/-- Every declared vertex of `I.pattern` has at least one neighbor in `I.pattern.induced`. -/
@[expose]
def SubgraphIsoInstance.HasNoIsolatedPatternVertices (I : SubgraphIsoInstance) : Prop :=
  ∀ u : {v // v ∈ I.pattern.vertices},
    ∃ w : {v // v ∈ I.pattern.vertices}, I.pattern.induced.Adj u w

/-- Semantic characterization of `SubgraphIsoInstance.HasNoIsolatedPatternVertices`. -/
theorem SubgraphIsoInstance.hasNoIsolatedPatternVertices_iff (I : SubgraphIsoInstance) :
    I.HasNoIsolatedPatternVertices ↔
      ∀ u : {v // v ∈ I.pattern.vertices},
        ∃ w : {v // v ∈ I.pattern.vertices}, I.pattern.induced.Adj u w := Iff.rfl

/-- **Subgraph Isomorphism**: instances `(G, H)` admitting an injective graph homomorphism
(`SimpleGraph.Copy`) from `H.induced` into `G.induced`. -/
@[expose]
def SubgraphIsomorphism : Set SubgraphIsoInstance :=
  {I | Nonempty (SimpleGraph.Copy I.pattern.induced I.target.induced)}

/-- **Isolated-vertex-free Subgraph Isomorphism**: instances `(G, H)` in `SubgraphIsomorphism`
whose pattern graph `H` has no isolated vertices. -/
@[expose]
def SubgraphIsomorphismNoIso : Set SubgraphIsoInstance :=
  {I | I ∈ SubgraphIsomorphism ∧ I.HasNoIsolatedPatternVertices}

/-- Membership characterization for `SubgraphIsomorphismNoIso`. -/
theorem mem_subgraphIsomorphismNoIso_iff {I : SubgraphIsoInstance} :
    I ∈ SubgraphIsomorphismNoIso ↔ I ∈ SubgraphIsomorphism ∧ I.HasNoIsolatedPatternVertices :=
  Iff.rfl

private theorem nodup_orderedEdgeList (G : Graph) : (orderedEdgeList G).Nodup := by
  have haux : ∀ us : List ℕ, us.Nodup →
      (us.flatMap fun u =>
        (G.distinctVertices.filter fun v => decide (u < v) && G.adjBool u v).map fun v =>
          (u, v)).Nodup := by
    intro us hus
    induction us with
    | nil => simp
    | cons u us ih =>
      obtain ⟨hu_nin, hus'⟩ := List.nodup_cons.mp hus
      simp only [List.flatMap_cons]
      refine List.nodup_append.mpr ⟨(G.nodup_distinctVertices.filter _).map
        (fun a b h => (Prod.mk.inj h).2), ih hus', fun _ hp₁ _ hp₂ hEq => ?_⟩
      subst hEq
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp₁
      obtain ⟨u', hu', hp₂'⟩ := List.mem_flatMap.mp hp₂
      obtain ⟨_, _, heq⟩ := List.mem_map.mp hp₂'
      exact hu_nin ((Prod.mk.inj heq).1 ▸ hu')
  exact haux G.distinctVertices G.nodup_distinctVertices

private theorem mem_orderedEdgeList_iff (G : Graph) {p : ℕ × ℕ} :
    p ∈ orderedEdgeList G ↔
      p.1 ∈ G.vertices ∧ p.2 ∈ G.vertices ∧ p.1 < p.2 ∧ G.toSimpleGraph.Adj p.1 p.2 := by
  rcases p with ⟨u, v⟩
  simp only [orderedEdgeList, List.mem_flatMap, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff, Prod.mk.injEq,
    Graph.mem_distinctVertices]
  exact ⟨fun ⟨_, hu', _, ⟨hv', hlt, hadj⟩, rfl, rfl⟩ => ⟨hu', hv', hlt, hadj⟩,
    fun ⟨hu, hv, hlt, hadj⟩ => ⟨u, hu, v, ⟨hv, hlt, hadj⟩, rfl, rfl⟩⟩

/-- `SubgraphIsoInstance.patternEdgeCount` equals the cardinality of
`I.pattern.induced.edgeFinset`. -/
theorem patternEdgeCount_eq_card_edgeFinset (I : SubgraphIsoInstance) :
    I.patternEdgeCount = I.pattern.induced.edgeFinset.card := by
  classical
  set G := I.pattern
  have hnodup := nodup_orderedEdgeList G
  rw [SubgraphIsoInstance.patternEdgeCount, ← List.toFinset_card_of_nodup hnodup]
  refine Finset.card_bij
    (fun p hp => by
      have hm := (mem_orderedEdgeList_iff G).mp (List.mem_toFinset.mp hp)
      exact s(⟨p.1, hm.1⟩, ⟨p.2, hm.2.1⟩))
    (fun p hp => by
      have hm := (mem_orderedEdgeList_iff G).mp (List.mem_toFinset.mp hp)
      exact SimpleGraph.mem_edgeFinset.mpr hm.2.2.2)
    (fun p₁ hp₁ p₂ hp₂ heq => by
      have hm₁ := (mem_orderedEdgeList_iff G).mp (List.mem_toFinset.mp hp₁)
      have hm₂ := (mem_orderedEdgeList_iff G).mp (List.mem_toFinset.mp hp₂)
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2)
      · have e1 : p₁.1 = p₂.2 := congrArg Subtype.val h1
        have e2 : p₁.2 = p₂.1 := congrArg Subtype.val h2
        omega)
    (fun e he => by
      induction e using Sym2.ind with
      | _ a b =>
        have hadj : G.toSimpleGraph.Adj a.1 b.1 := SimpleGraph.mem_edgeFinset.mp he
        have hne : a.1 ≠ b.1 := hadj.ne
        rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
        · refine ⟨(a.1, b.1), List.mem_toFinset.mpr
            ((mem_orderedEdgeList_iff G).mpr ⟨a.2, b.2, hlt, hadj⟩), rfl⟩
        · exact absurd heq hne
        · refine ⟨(b.1, a.1), List.mem_toFinset.mpr
            ((mem_orderedEdgeList_iff G).mpr ⟨b.2, a.2, hgt, hadj.symm⟩), Sym2.eq_swap⟩)

open ComputableInPolyTime in
/-- Computing `patternEdgeCount` in unary is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_patternEdgeCount_unary :
    ComputableInPolyTime SubgraphIsoInstance.patternEdgeCount encSubgraphIsoInstance encUnary := by
  unfold SubgraphIsoInstance.patternEdgeCount orderedEdgeList
  fun_prop

open ComputableInPolyTime in
/-- Computing `patternEdgeCount` in binary is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_patternEdgeCount :
    ComputableInPolyTime SubgraphIsoInstance.patternEdgeCount encSubgraphIsoInstance encNat :=
  unary_to_binary.comp computableInPolyTime_patternEdgeCount_unary

private def hasNoIsolatedBool (G : Graph) : Bool :=
  G.distinctVertices.all fun u => G.distinctVertices.any fun w => G.adjBool u w

private theorem hasNoIsolatedBool_eq_true_iff (I : SubgraphIsoInstance) :
    hasNoIsolatedBool I.pattern = true ↔ I.HasNoIsolatedPatternVertices := by
  simp [hasNoIsolatedBool, Graph.mem_distinctVertices,
    SubgraphIsoInstance.HasNoIsolatedPatternVertices]

open ComputableInPolyTime in
private theorem computableInPolyTime_hasNoIsolatedBool :
    ComputableInPolyTime (fun I : SubgraphIsoInstance => hasNoIsolatedBool I.pattern)
      encSubgraphIsoInstance encBool := by
  unfold hasNoIsolatedBool
  fun_prop

/-! ### 2. Handshaking Bounds and Non-Degeneracy / Sharpness Theorems -/

/-- When `I.pattern` has no isolated vertices, `|V(H)| ≤ 2 |E(H)|`. -/
theorem card_patternVertices_le_two_mul_patternEdgeCount {I : SubgraphIsoInstance}
    (hno : I.HasNoIsolatedPatternVertices) :
    I.pattern.distinctVertices.length ≤ 2 * I.patternEdgeCount := by
  classical
  rw [patternEdgeCount_eq_card_edgeFinset, Graph.length_distinctVertices,
    ← Graph.card_vertexSubtype, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc Fintype.card {v // v ∈ I.pattern.vertices}
      = ∑ _ : {v // v ∈ I.pattern.vertices}, 1 := by simp
    _ ≤ ∑ u : {v // v ∈ I.pattern.vertices}, I.pattern.induced.degree u :=
        Finset.sum_le_sum fun u _ => by
          obtain ⟨w, hw⟩ := hno u
          exact Finset.card_pos.mpr ⟨w, (I.pattern.induced.mem_neighborFinset u w).mpr hw⟩

/-- When `I.pattern` has at least one edge, `I.pattern` has at least two distinct vertices. -/
theorem two_le_card_patternVertices_of_pos {I : SubgraphIsoInstance}
    (hk : 0 < I.patternEdgeCount) :
    2 ≤ I.pattern.distinctVertices.length := by
  classical
  rw [patternEdgeCount_eq_card_edgeFinset] at hk
  obtain ⟨e, he⟩ := Finset.card_pos.mp hk
  induction e using Sym2.ind with
  | _ a b =>
    have hadj : I.pattern.induced.Adj a b := SimpleGraph.mem_edgeFinset.mp he
    have hab : a ≠ b := hadj.ne
    rw [Graph.length_distinctVertices, ← Graph.card_vertexSubtype]
    have hcard : ({a, b} : Finset {v // v ∈ I.pattern.vertices}).card = 2 :=
      Finset.card_pair hab
    exact hcard ▸ Finset.card_le_univ _

/-- Every vertex of `I.pattern.induced` has degree at most `I.patternEdgeCount`. -/
theorem degree_le_patternEdgeCount (I : SubgraphIsoInstance)
    (u : {v // v ∈ I.pattern.vertices}) :
    I.pattern.induced.degree u ≤ I.patternEdgeCount := by
  classical
  rw [patternEdgeCount_eq_card_edgeFinset, SimpleGraph.degree]
  exact Finset.card_le_card_of_injOn (fun w => s(u, w))
    (fun w hw => SimpleGraph.mem_edgeFinset.mpr
      ((I.pattern.induced.mem_neighborFinset u w).mp hw))
    (fun w₁ _ w₂ _ heq => by
      rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl)

/-- Explicit graph consisting of `r` vertex-disjoint edges `{2i, 2i + 1}` on `2r` vertices. -/
private def matchingGraph (r : ℕ) : Graph where
  vertices := List.range (2 * r)
  edges := (List.range r).map fun i => (2 * i, 2 * i + 1)

private theorem matchingGraph_adj_iff (r u v : ℕ) :
    (matchingGraph r).toSimpleGraph.Adj u v ↔
      ∃ i < r, (u = 2 * i ∧ v = 2 * i + 1) ∨ (u = 2 * i + 1 ∧ v = 2 * i) := by
  simp only [Graph.toSimpleGraph_adj, matchingGraph, List.mem_map, List.mem_range, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩⟩
    · exact ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨by omega, Or.inl ⟨i, hi, rfl, rfl⟩⟩
    · exact ⟨by omega, Or.inr ⟨i, hi, rfl, rfl⟩⟩

private theorem matchingGraph_hasNoIsolated (G : Graph) (r : ℕ) :
    (SubgraphIsoInstance.mk G (matchingGraph r)).HasNoIsolatedPatternVertices := by
  rintro ⟨u, hu⟩
  have hu' : u < 2 * r := List.mem_range.mp hu
  by_cases heven : u % 2 = 0
  · refine ⟨⟨u + 1, List.mem_range.mpr (by omega)⟩, ?_⟩
    rw [Graph.induced_adj, matchingGraph_adj_iff]; dsimp only
    exact ⟨u / 2, by omega, Or.inl ⟨by omega, by omega⟩⟩
  · refine ⟨⟨u - 1, List.mem_range.mpr (by omega)⟩, ?_⟩
    rw [Graph.induced_adj, matchingGraph_adj_iff]; dsimp only
    exact ⟨u / 2, by omega, Or.inr ⟨by omega, by omega⟩⟩

private theorem matchingGraph_patternEdgeCount (G : Graph) (r : ℕ) :
    (SubgraphIsoInstance.mk G (matchingGraph r)).patternEdgeCount = r := by
  classical
  rw [patternEdgeCount_eq_card_edgeFinset]
  let emb : Fin r → {v // v ∈ (matchingGraph r).vertices} × {v // v ∈ (matchingGraph r).vertices} :=
    fun i => (⟨2 * i.1, List.mem_range.mpr (by omega)⟩,
      ⟨2 * i.1 + 1, List.mem_range.mpr (by omega)⟩)
  refine (Finset.card_bij (fun i _ => s((emb i).1, (emb i).2))
    (fun i _ => SimpleGraph.mem_edgeFinset.mpr <|
      (SimpleGraph.mem_edgeSet ..).mpr <| (Graph.induced_adj ..).mpr <|
        (matchingGraph_adj_iff ..).mpr ⟨i.1, i.2, Or.inl ⟨rfl, rfl⟩⟩)
    (fun i₁ _ i₂ _ heq => by
      rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        [exact Fin.ext (by have := congrArg Subtype.val h1; dsimp [emb] at this; omega);
         (have := congrArg Subtype.val h1; dsimp [emb] at this; omega)])
    (fun e he => by
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨i, hi, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := (matchingGraph_adj_iff r a.1 b.1).mp
          ((Graph.induced_adj (G := matchingGraph r)).mp (SimpleGraph.mem_edgeFinset.mp he))
        · exact ⟨⟨i, hi⟩, Finset.mem_univ _, by congr 1 <;> ext <;> dsimp [emb] <;> omega⟩
        · exact ⟨⟨i, hi⟩, Finset.mem_univ _, by
            rw [Sym2.eq_swap]; congr 1 <;> ext <;> dsimp [emb] <;> omega⟩)).symm.trans
    (Finset.card_fin r)

/-- For every `r : ℕ`, there exists an instance in `SubgraphIsomorphismNoIso` whose pattern graph
has no isolated vertices and has `patternEdgeCount` equal to `r`. -/
theorem exists_mem_subgraphIsomorphismNoIso_of_pos (r : ℕ) :
    ∃ I : SubgraphIsoInstance, I ∈ SubgraphIsomorphismNoIso ∧ I.patternEdgeCount = r :=
  ⟨⟨matchingGraph r, matchingGraph r⟩,
    ⟨⟨SimpleGraph.Copy.id _⟩, matchingGraph_hasNoIsolated (matchingGraph r) r⟩,
    matchingGraph_patternEdgeCount (matchingGraph r) r⟩

/-- Non-collapse of `SubgraphIsomorphism`: there exists an isolated-vertex-free instance with
positive `patternEdgeCount` that does not belong to `SubgraphIsomorphism`. -/
theorem exists_not_mem_subgraphIsomorphismNoIso :
    ∃ I : SubgraphIsoInstance, I.HasNoIsolatedPatternVertices ∧
      I.patternEdgeCount = 1 ∧ I ∉ SubgraphIsomorphism := by
  refine ⟨⟨⟨[], []⟩, matchingGraph 1⟩,
    matchingGraph_hasNoIsolated ⟨[], []⟩ 1,
    matchingGraph_patternEdgeCount ⟨[], []⟩ 1, ?_⟩
  rintro ⟨f⟩
  have h0 : (0 : ℕ) ∈ (matchingGraph 1).vertices := by simp [matchingGraph]
  exact List.not_mem_nil (f ⟨0, h0⟩).2

/-- Non-collapse of `HasNoIsolatedPatternVertices`: a single isolated vertex violates
`HasNoIsolatedPatternVertices`. -/
theorem exists_not_hasNoIsolatedPatternVertices :
    ∃ I : SubgraphIsoInstance, ¬I.HasNoIsolatedPatternVertices := by
  refine ⟨⟨⟨[0], []⟩, ⟨[0], []⟩⟩, fun h => ?_⟩
  obtain ⟨w, hw⟩ := h ⟨0, by simp⟩
  simp [Graph.induced_adj, Graph.toSimpleGraph_adj] at hw

/-! ### 3. Executable Index-Tuple Mapping, `NP` Membership, and `XP` / `P` Solvers -/

/-- Check whether an index list `ds : List ℕ` represents an injective homomorphism from
`I.pattern.distinctVertices` into `I.target.distinctVertices`. -/
private def isValidIndexHom (I : SubgraphIsoInstance) (ds : List ℕ) : Bool :=
  let V_H := I.pattern.distinctVertices
  let V_G := I.target.distinctVertices
  decide (ds.length = V_H.length) &&
    ds.all (fun j => decide (j < V_G.length)) &&
    (List.range V_H.length).all (fun i₁ =>
      (List.range V_H.length).all fun i₂ =>
        decide (i₁ = i₂) || decide (ds.getD i₁ 0 ≠ ds.getD i₂ 0)) &&
    (List.range V_H.length).all (fun i₁ =>
      (List.range V_H.length).all fun i₂ =>
        !I.pattern.adjBool (V_H.getD i₁ 0) (V_H.getD i₂ 0) ||
          I.target.adjBool (V_G.getD (ds.getD i₁ 0) 0) (V_G.getD (ds.getD i₂ 0) 0))

open ComputableInPolyTime in
private theorem computableInPolyTime_isValidIndexHom :
    ComputableInPolyTime (fun p : SubgraphIsoInstance × List ℕ => isValidIndexHom p.1 p.2)
      (encPair encSubgraphIsoInstance (encList encUnary)) encBool := by
  let encP := encPair encSubgraphIsoInstance (encList encUnary)
  have hVH : ComputableInPolyTime (fun p : SubgraphIsoInstance × List ℕ =>
      p.1.pattern.distinctVertices) encP (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices.comp (computableInPolyTime_subgraphIsoPattern
      (fst _ _))
  have hVG : ComputableInPolyTime (fun p : SubgraphIsoInstance × List ℕ =>
      p.1.target.distinctVertices) encP (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices.comp (computableInPolyTime_subgraphIsoTarget
      (fst _ _))
  have hlenH : ComputableInPolyTime (fun p : SubgraphIsoInstance × List ℕ =>
      p.1.pattern.distinctVertices.length) encP encUnary := (length_list encNat).comp hVH
  have hlenG : ComputableInPolyTime (fun p : SubgraphIsoInstance × List ℕ =>
      p.1.target.distinctVertices.length) encP encUnary := (length_list encNat).comp hVG
  have h1 : ComputableInPolyTime (fun p : SubgraphIsoInstance × List ℕ =>
      decide (p.2.length = p.1.pattern.distinctVertices.length)) encP encBool :=
    decide_eq' ((length_list encUnary).comp (snd _ _)) hlenH
  have h2 : ComputableInPolyTime (fun p : SubgraphIsoInstance × List ℕ =>
      p.2.all fun j => decide (j < p.1.target.distinctVertices.length)) encP encBool :=
    allWithInput (snd _ _) (unary_lt' (snd _ _) (hlenG.comp (fst _ _)))
  have h3 : ComputableInPolyTime (fun p : SubgraphIsoInstance × List ℕ =>
      (List.range p.1.pattern.distinctVertices.length).all fun i₁ =>
        (List.range p.1.pattern.distinctVertices.length).all fun i₂ =>
          decide (i₁ = i₂) || decide (p.2.getD i₁ 0 ≠ p.2.getD i₂ 0)) encP encBool := by
    apply allWithInput (range.comp hlenH)
    apply allWithInput (range.comp (hlenH.comp (fst _ _)))
    have hds_q : ComputableInPolyTime
        (fun q : ((SubgraphIsoInstance × List ℕ) × ℕ) × ℕ => q.1.1.2)
        (encPair (encPair encP encUnary) encUnary) (encList encUnary) :=
      (snd _ _).comp ((fst _ _).comp (fst _ _))
    exact bool_or.comp
      ((decide_eq' ((snd _ _).comp (fst _ _)) (snd _ _)).prod
        (bool_not.comp (decide_eq'
          (listGetDWithInput hds_q ((snd _ _).comp (fst _ _)) 0)
          (listGetDWithInput hds_q (snd _ _) 0))))
  have h4 : ComputableInPolyTime (fun p : SubgraphIsoInstance × List ℕ =>
      (List.range p.1.pattern.distinctVertices.length).all fun i₁ =>
        (List.range p.1.pattern.distinctVertices.length).all fun i₂ =>
          !p.1.pattern.adjBool (p.1.pattern.distinctVertices.getD i₁ 0)
              (p.1.pattern.distinctVertices.getD i₂ 0) ||
            p.1.target.adjBool (p.1.target.distinctVertices.getD (p.2.getD i₁ 0) 0)
              (p.1.target.distinctVertices.getD (p.2.getD i₂ 0) 0)) encP encBool := by
    apply allWithInput (range.comp hlenH)
    apply allWithInput (range.comp (hlenH.comp (fst _ _)))
    have hp_q : ComputableInPolyTime (fun x : ((SubgraphIsoInstance × List ℕ) × ℕ) × ℕ => x.1.1)
        (encPair (encPair encP encUnary) encUnary) encP :=
      (fst encP encUnary).comp (fst (encPair encP encUnary) encUnary)
    have hu₁ := listGetDWithInput (hVH.comp hp_q) ((snd _ _).comp (fst _ _)) 0
    have hu₂ := listGetDWithInput (hVH.comp hp_q) (snd _ _) 0
    have hv₁ := listGetDWithInput (hVG.comp hp_q)
      (listGetDWithInput ((snd _ _).comp hp_q) ((snd _ _).comp (fst _ _)) 0) 0
    have hv₂ := listGetDWithInput (hVG.comp hp_q)
      (listGetDWithInput ((snd _ _).comp hp_q) (snd _ _) 0) 0
    exact bool_or.comp
      ((bool_not.comp (Graph.computableInPolyTime_adjBool_comp
          (computableInPolyTime_subgraphIsoPattern ((fst _ _).comp hp_q)) hu₁ hu₂)).prod
        (Graph.computableInPolyTime_adjBool_comp
          (computableInPolyTime_subgraphIsoTarget ((fst _ _).comp hp_q)) hv₁ hv₂))
  exact bool_and' (bool_and' (bool_and' h1 h2) h3) h4

private theorem mem_subgraphIsomorphism_iff_exists_indexHom (I : SubgraphIsoInstance) :
    I ∈ SubgraphIsomorphism ↔
      ∃ ds : List ℕ, isValidIndexHom I ds = true := by
  set V_H := I.pattern.distinctVertices
  set V_G := I.target.distinctVertices
  constructor
  · rintro ⟨f⟩
    let eqH := I.pattern.vertexEquiv
    let eqG := I.target.vertexEquiv
    let ds : List ℕ := (List.finRange V_H.length).map fun i => (eqG.symm (f (eqH i))).1
    refine ⟨ds, ?_⟩
    have hlen : ds.length = V_H.length := by simp [ds]
    have hget (i : ℕ) (hi : i < V_H.length) :
        ds.getD i 0 = (eqG.symm (f (eqH ⟨i, hi⟩))).1 := by
      rw [List.getD_eq_getElem _ _ (by simpa [hlen] using hi)]; simp [ds]
    have hVH (i : ℕ) (hi : i < V_H.length) : V_H.getD i 0 = (eqH ⟨i, hi⟩).1 :=
      (I.pattern.vertexEquiv_apply ⟨i, hi⟩).symm
    have hVG (j : Fin V_G.length) : V_G.getD j.1 0 = (eqG j).1 :=
      (I.target.vertexEquiv_apply j).symm
    simp only [isValidIndexHom, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true, Bool.not_eq_true', Graph.adjBool_eq_false_iff,
      Graph.adjBool_eq_true_iff]
    refine ⟨⟨⟨hlen, fun j hj => ?_⟩, fun i₁ hi₁ i₂ hi₂ => ?_⟩, fun i₁ hi₁ i₂ hi₂ => ?_⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
      exact (eqG.symm (f (eqH i))).isLt
    · by_cases heq : i₁ = i₂
      · exact Or.inl heq
      · right; rw [hget i₁ hi₁, hget i₂ hi₂]
        exact fun hval => heq (Fin.ext_iff.mp
          (eqH.injective (f.injective (eqG.symm.injective (Fin.ext hval)))))
    · by_cases hadj : I.pattern.toSimpleGraph.Adj (V_H.getD i₁ 0) (V_H.getD i₂ 0)
      · right; rw [hVH i₁ hi₁, hVH i₂ hi₂] at hadj
        rw [hget i₁ hi₁, hget i₂ hi₂, hVG, hVG, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact f.toHom.map_adj hadj
      · exact Or.inl hadj
  · rintro ⟨ds, hds⟩
    simp only [isValidIndexHom, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true, Bool.not_eq_true', Graph.adjBool_eq_false_iff,
      Graph.adjBool_eq_true_iff] at hds
    obtain ⟨⟨⟨hlen, hlt⟩, hinj⟩, hadj⟩ := hds
    let eqH := I.pattern.vertexEquiv
    let eqG := I.target.vertexEquiv
    let mapFin : Fin V_H.length → Fin V_G.length := fun i =>
      ⟨ds.getD i.1 0, hlt (ds.getD i.1 0) (by
        rw [List.getD_eq_getElem _ _ (hlen.symm ▸ i.isLt)]; exact List.getElem_mem _)⟩
    let phi : {v // v ∈ I.pattern.vertices} → {v // v ∈ I.target.vertices} :=
      fun u => eqG (mapFin (eqH.symm u))
    have hphi_inj : Function.Injective phi := fun u₁ u₂ heq => by
      by_contra hne
      exact (hinj (eqH.symm u₁).1 (eqH.symm u₁).isLt (eqH.symm u₂).1
        (eqH.symm u₂).isLt).resolve_left
        (fun hv => hne (eqH.symm.injective (Fin.ext hv))) (congrArg Fin.val (eqG.injective heq))
    refine ⟨⟨⟨phi, fun {u₁ u₂} hu => ?_⟩, hphi_inj⟩⟩
    rw [Graph.induced_adj] at hu ⊢
    set i₁ := eqH.symm u₁; set i₂ := eqH.symm u₂
    have hu₁ : V_H.getD i₁.1 0 = u₁.1 := by
      have := (I.pattern.vertexEquiv_apply i₁).symm; rwa [Equiv.apply_symm_apply] at this
    have hu₂ : V_H.getD i₂.1 0 = u₂.1 := by
      have := (I.pattern.vertexEquiv_apply i₂).symm; rwa [Equiv.apply_symm_apply] at this
    rw [I.target.vertexEquiv_apply (mapFin i₁), I.target.vertexEquiv_apply (mapFin i₂)]
    exact (hadj i₁.1 i₁.isLt i₂.1 i₂.isLt).resolve_left (by rwa [hu₁, hu₂, not_not])

/-- Decode a certificate bitstring into `m` unary-block indices of width `w`. -/
private def blockCount (par : ℕ × List Bool) (a : ℕ) : ℕ :=
  (List.range par.1).countP fun c => par.2.getD (par.1 * a + c) false

private def decodeUnaryBlocks (m w : ℕ) (cert : List Bool) : List ℕ :=
  (List.range m).map (blockCount (w, cert))

private def subgraphIsoVerifier (p : SubgraphIsoInstance × List Bool) : Bool :=
  isValidIndexHom p.1
    (decodeUnaryBlocks p.1.pattern.distinctVertices.length
      p.1.target.distinctVertices.length p.2)

open ComputableInPolyTime in
private theorem computableInPolyTime_subgraphIsoVerifier :
    ComputableInPolyTime subgraphIsoVerifier
      (encPair encSubgraphIsoInstance encBits) encBool := by
  let encP := encPair encSubgraphIsoInstance encBits
  have hm : ComputableInPolyTime
      (fun p : SubgraphIsoInstance × List Bool => p.1.pattern.distinctVertices.length)
      encP encUnary :=
    (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp
      (computableInPolyTime_subgraphIsoPattern (fst encSubgraphIsoInstance encBits)))
  have hw : ComputableInPolyTime
      (fun p : SubgraphIsoInstance × List Bool => p.1.target.distinctVertices.length)
      encP encUnary :=
    (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp
      (computableInPolyTime_subgraphIsoTarget (fst encSubgraphIsoInstance encBits)))
  let encW := encPair encUnary encBits
  have hw_R : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × ℕ) × ℕ => r.1.1) (encPair (encPair encW encUnary) encUnary)
      encW :=
    (fst encW encUnary).comp (fst (encPair encW encUnary) encUnary)
  have hblk : ComputableInPolyTime (fun q : (ℕ × List Bool) × ℕ => blockCount q.1 q.2)
      (encPair encW encUnary) encUnary :=
    countPWithInput (range.comp ((fst encUnary encBits).comp (fst encW encUnary)))
      (bitsGetDWithInput ((snd encUnary encBits).comp hw_R)
        (unary_add' (unary_mul' ((fst encUnary encBits).comp hw_R)
          ((snd encW encUnary).comp (fst (encPair encW encUnary) encUnary)))
          (snd (encPair encW encUnary) encUnary)) false)
  have hdec : ComputableInPolyTime
      (fun p : SubgraphIsoInstance × List Bool =>
        decodeUnaryBlocks p.1.pattern.distinctVertices.length
          p.1.target.distinctVertices.length p.2)
      encP (encList encUnary) := by
    have hmap := mapWith hblk (hw.prod (snd encSubgraphIsoInstance encBits)) (range.comp hm)
    have heq1 : (fun x : SubgraphIsoInstance × List Bool =>
        (List.range (((List.length ∘ Graph.distinctVertices) ∘
          fun x_1 : SubgraphIsoInstance × List Bool => x_1.1.pattern) x)).map fun a =>
            blockCount ((((List.length ∘ Graph.distinctVertices) ∘
              fun x_1 : SubgraphIsoInstance × List Bool => x_1.1.target) x, x.2)) a) =
        fun p : SubgraphIsoInstance × List Bool =>
          decodeUnaryBlocks p.1.pattern.distinctVertices.length
            p.1.target.distinctVertices.length p.2 :=
      funext fun _ => rfl
    exact heq1 ▸ hmap
  have hcomp := computableInPolyTime_isValidIndexHom.comp
    ((fst encSubgraphIsoInstance encBits).prod hdec)
  have heq2 : ((fun p : SubgraphIsoInstance × List ℕ => isValidIndexHom p.1 p.2) ∘
      fun x : SubgraphIsoInstance × List Bool =>
        (x.1, decodeUnaryBlocks x.1.pattern.distinctVertices.length
          x.1.target.distinctVertices.length x.2)) = subgraphIsoVerifier :=
    funext fun _ => rfl
  exact heq2 ▸ hcomp

/-- **`SubgraphIsomorphism` belongs to `NP`**, verified by unary-block vertex-index maps of
quadratic bit-length. -/
theorem subgraphIsomorphism_mem_NP : SubgraphIsomorphism ∈ NP encSubgraphIsoInstance := by
  refine ⟨Polynomial.X ^ 2, subgraphIsoVerifier, computableInPolyTime_subgraphIsoVerifier,
    fun I => ?_⟩
  rw [mem_subgraphIsomorphism_iff_exists_indexHom]
  refine ⟨?_, fun ⟨_, _, hcert⟩ => ⟨_, hcert⟩⟩
  rintro ⟨ds, hds⟩
  have hvalid := hds
  simp only [isValidIndexHom, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hvalid
  obtain ⟨⟨⟨hlen, hlt⟩, _⟩, _⟩ := hvalid
  let m := I.pattern.distinctVertices.length
  let w := I.target.distinctVertices.length
  let N := (encSubgraphIsoInstance I).length ^ 2
  have hm_le : m ≤ (encSubgraphIsoInstance I).length :=
    I.pattern.length_distinctVertices_le.trans (length_encGraph_le_encSubgraphIso I).2
  have hw_le : w ≤ (encSubgraphIsoInstance I).length :=
    I.target.length_distinctVertices_le.trans (length_encGraph_le_encSubgraphIso I).1
  refine ⟨unaryBlocks w N (fun a => ds.getD a 0),
    by simp [N, Polynomial.eval_pow, Polynomial.eval_X], ?_⟩
  have hdec : decodeUnaryBlocks m w (unaryBlocks w N (fun a => ds.getD a 0)) = ds := by
    refine List.ext_getElem (by simp [decodeUnaryBlocks, m, hlen]) fun a ha₁ ha₂ => ?_
    simp only [decodeUnaryBlocks, List.getElem_map, List.getElem_range]
    have hd_lt : ds[a] < w := hlt ds[a] (List.getElem_mem _)
    have hget : ds.getD a 0 = ds[a] := List.getD_eq_getElem ds 0 ha₂
    have ha_m : a + 1 ≤ m := by simp only [decodeUnaryBlocks, List.length_map,
      List.length_range] at ha₁; omega
    have hfit : w * (a + 1) ≤ N :=
      (Nat.mul_le_mul hw_le (ha_m.trans hm_le)).trans_eq (sq _).symm
    unfold blockCount
    rw [countP_unaryBlocks (f := fun j => ds.getD j 0) (hget ▸ hd_lt.le) hfit, hget]
  rw [subgraphIsoVerifier]; change isValidIndexHom I (decodeUnaryBlocks m w _) = true
  rwa [hdec]

/-- **`SubgraphIsomorphismNoIso` belongs to `NP`**. -/
theorem subgraphIsomorphismNoIso_mem_NP :
    SubgraphIsomorphismNoIso ∈ NP encSubgraphIsoInstance := by
  obtain ⟨P, V, hVpoly, hV⟩ := subgraphIsomorphism_mem_NP
  refine ⟨P, fun p => hasNoIsolatedBool p.1.pattern && V p,
    ComputableInPolyTime.bool_and.comp ((computableInPolyTime_hasNoIsolatedBool.comp
      (ComputableInPolyTime.fst encSubgraphIsoInstance encBits)).prod hVpoly), fun I => ?_⟩
  simp only [SubgraphIsomorphismNoIso, Set.mem_ofPred_eq, Bool.and_eq_true,
    hasNoIsolatedBool_eq_true_iff, hV I]
  exact ⟨fun ⟨⟨w, hw1, hw2⟩, h2⟩ => ⟨w, hw1, h2, hw2⟩,
    fun ⟨w, hw1, h2, hw2⟩ => ⟨⟨w, hw1, hw2⟩, h2⟩⟩

section ExhaustiveSolver

private def nextTupleRec (n : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: ds => if d + 1 < n then (d + 1) :: ds else 0 :: nextTupleRec n ds

private def nextTupleStep (n : ℕ) (st : List ℕ × Bool) (d : ℕ) : List ℕ × Bool :=
  if st.2 then if d + 1 < n then (st.1 ++ [d + 1], false) else (st.1 ++ [0], true)
  else (st.1 ++ [d], false)

private def nextTuple (n : ℕ) (ds : List ℕ) : List ℕ :=
  (ds.foldl (nextTupleStep n) ([], true)).1

private theorem foldl_nextTupleStep_false (n : ℕ) :
    ∀ (ds acc : List ℕ), (ds.foldl (nextTupleStep n) (acc, false)).1 = acc ++ ds
  | [], acc => by simp
  | d :: ds, acc => by
    simp only [List.foldl_cons, nextTupleStep, Bool.false_eq_true, ↓reduceIte,
      foldl_nextTupleStep_false n ds (acc ++ [d]), List.append_assoc, List.singleton_append]

private theorem foldl_nextTupleStep_true (n : ℕ) :
    ∀ (ds acc : List ℕ), (ds.foldl (nextTupleStep n) (acc, true)).1 = acc ++ nextTupleRec n ds
  | [], acc => by simp [nextTupleRec]
  | d :: ds, acc => by
    simp only [List.foldl_cons, nextTupleStep, ↓reduceIte, nextTupleRec]
    split_ifs <;> simp [foldl_nextTupleStep_false, foldl_nextTupleStep_true, List.append_assoc]

private theorem nextTuple_eq_rec (n : ℕ) (ds : List ℕ) :
    nextTuple n ds = nextTupleRec n ds := by
  simpa [nextTuple] using foldl_nextTupleStep_true n ds []

private def tupleOfCode (n : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | ℓ + 1, c => (c % n) :: tupleOfCode n ℓ (c / n)

private theorem tupleOfCode_zero (n ℓ : ℕ) :
    tupleOfCode n ℓ 0 = List.replicate ℓ 0 := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => simp [tupleOfCode, ih, List.replicate_succ]

private theorem nextTupleRec_tupleOfCode {n : ℕ} (hn : 0 < n) :
    ∀ (ℓ c : ℕ), nextTupleRec n (tupleOfCode n ℓ c) = tupleOfCode n ℓ (c + 1)
  | 0, _ => rfl
  | ℓ + 1, c => by
    simp only [tupleOfCode, nextTupleRec]
    have hmod_lt : c % n < n := Nat.mod_lt c hn
    have hdiv_eq : c = n * (c / n) + c % n := (Nat.div_add_mod c n).symm
    split_ifs with hlt
    · have h1 : (c + 1) % n = c % n + 1 := by
        conv_lhs => rw [hdiv_eq, Nat.add_assoc, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]
      have h2 : (c + 1) / n = c / n := by
        conv_lhs => rw [hdiv_eq, Nat.add_assoc, Nat.mul_add_div hn, Nat.div_eq_of_lt hlt,
          Nat.add_zero]
      rw [h1, h2]
    · have hrem : c % n + 1 = n := by omega
      have hc1 : c + 1 = n * (c / n + 1) := by linarith
      rw [hc1, Nat.mul_mod_right, Nat.mul_div_right _ hn, nextTupleRec_tupleOfCode hn ℓ (c / n)]

private theorem iterate_nextTuple_replicate {n : ℕ} (hn : 0 < n) (ℓ k : ℕ) :
    (nextTuple n)^[k] (List.replicate ℓ 0) = tupleOfCode n ℓ k := by
  induction k with
  | zero => simp [tupleOfCode_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, nextTuple_eq_rec, nextTupleRec_tupleOfCode hn]

private def codeOfTuple (n : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + n * codeOfTuple n ds

private theorem codeOfTuple_lt {n : ℕ} (hn : 0 < n) :
    ∀ (ds : List ℕ), (∀ d ∈ ds, d < n) → codeOfTuple n ds < n ^ ds.length
  | [], _ => by simp [codeOfTuple]
  | d :: ds, hds => by
    have hd : d < n := hds d List.mem_cons_self
    have hrest : codeOfTuple n ds < n ^ ds.length :=
      codeOfTuple_lt hn ds fun x hx => hds x (List.mem_cons_of_mem _ hx)
    simp only [codeOfTuple, List.length_cons, Nat.pow_succ']
    nlinarith

private theorem tupleOfCode_codeOfTuple {n : ℕ} (hn : 0 < n) :
    ∀ (ds : List ℕ), (∀ d ∈ ds, d < n) → tupleOfCode n ds.length (codeOfTuple n ds) = ds
  | [], _ => rfl
  | d :: ds, hds => by
    have hd : d < n := hds d List.mem_cons_self
    simp only [List.length_cons, codeOfTuple, tupleOfCode]
    have hm : (d + n * codeOfTuple n ds) % n = d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    have hdv : (d + n * codeOfTuple n ds) / n = codeOfTuple n ds := by
      rw [Nat.add_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hd, Nat.add_zero]
    rw [hm, hdv, tupleOfCode_codeOfTuple hn ds fun x hx => hds x (List.mem_cons_of_mem _ hx)]

private theorem length_nextTupleRec (n : ℕ) :
    ∀ ds : List ℕ, (nextTupleRec n ds).length = ds.length
  | [] => rfl
  | d :: ds => by
    simp only [nextTupleRec]
    split_ifs <;> simp [length_nextTupleRec n ds]

private theorem mem_nextTupleRec_le {n : ℕ} :
    ∀ {ds : List ℕ}, (∀ d ∈ ds, d ≤ n) → ∀ x ∈ nextTupleRec n ds, x ≤ n
  | [], _, _, hx => by simp [nextTupleRec] at hx
  | d :: ds, hds, x, hx => by
    simp only [nextTupleRec] at hx
    split_ifs at hx with hlt
    · rcases List.mem_cons.mp hx with rfl | hm
      · omega
      · exact hds x (List.mem_cons_of_mem _ hm)
    · rcases List.mem_cons.mp hx with rfl | hm
      · exact Nat.zero_le n
      · exact mem_nextTupleRec_le (fun y hy => hds y (List.mem_cons_of_mem _ hy)) x hm

private theorem length_enc_mem_le_encList_local {β : Type} (encB : β ↪ List Bool) :
    ∀ {L : List β} {b : β}, b ∈ L → (encB b).length ≤ (encList encB L).length
  | _ :: bs, _, hx => by
    rcases List.mem_cons.mp hx with rfl | hmem
    · simp only [encList_cons, List.length_append, length_frame]; omega
    · exact (length_enc_mem_le_encList_local encB hmem).trans (by simp [encList_cons])

open ComputableInPolyTime in
private theorem computableInPolyTime_nextTuple :
    ComputableInPolyTime (fun p : ℕ × List ℕ => nextTuple p.1 p.2)
      (encPair encUnary (encList encUnary)) (encList encUnary) := by
  let encS := encPair (encPair encUnary (encPair (encList encUnary) encBool)) encUnary
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × (List ℕ × Bool)) × ℕ => nextTupleStep q.1.1 q.1.2 q.2)
      encS (encPair (encList encUnary) encBool) := by
    unfold nextTupleStep encS
    have hsnoc1 : ComputableInPolyTime (fun q : (ℕ × (List ℕ × Bool)) × ℕ => q.1.2.1 ++ [q.2 + 1])
        (encPair (encPair encUnary (encPair (encList encUnary) encBool)) encUnary)
        (encList encUnary) := by fun_prop
    have hsnoc0 : ComputableInPolyTime (fun q : (ℕ × (List ℕ × Bool)) × ℕ => q.1.2.1 ++ [0])
        (encPair (encPair encUnary (encPair (encList encUnary) encBool)) encUnary)
        (encList encUnary) := by fun_prop
    have hsnocd : ComputableInPolyTime (fun q : (ℕ × (List ℕ × Bool)) × ℕ => q.1.2.1 ++ [q.2])
        (encPair (encPair encUnary (encPair (encList encUnary) encBool)) encUnary)
        (encList encUnary) := by fun_prop
    fun_prop
  refine (fst (encList encUnary) encBool).comp (foldlWith_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary) (encB := encPair (encList encUnary) encBool)
    (par := Prod.fst) (list := Prod.snd) (step := nextTupleStep)
    (fst encUnary (encList encUnary)) (snd encUnary (encList encUnary)) (const ([], true)) hstep
    (growth := fun p => 8 * (encPair encUnary (encList encUnary) p).length + 16) (by growth_poly)
    fun p st d hd => ?_)
  have hd_len : d ≤ (encList encUnary p.2).length := by
    simpa [encUnary_apply] using length_enc_mem_le_encList_local encUnary hd
  have hp_len : (encList encUnary p.2).length ≤ (encPair encUnary (encList encUnary) p).length := by
    rw [length_encPair]; omega
  simp only [nextTupleStep]
  split_ifs <;>
  · simp only [length_encPair, encBool_apply, List.length_singleton, encList_append,
      List.length_append, encList_cons, encList_nil, length_frame, encUnary_apply,
      List.length_replicate, List.length_nil] at *
    omega

private abbrev SearchState : Type := (SubgraphIsoInstance × List ℕ) × Bool

private def encSearchState : SearchState ↪ List Bool :=
  encPair (encPair encSubgraphIsoInstance (encList encUnary)) encBool

private def searchInit (I : SubgraphIsoInstance) : SearchState :=
  ((I, List.replicate I.pattern.distinctVertices.length 0), false)

private def searchStep (s : SearchState) : SearchState :=
  let I := s.1.1
  let ds := s.1.2
  ((I, nextTuple I.target.distinctVertices.length ds), s.2 || isValidIndexHom I ds)

private def searchRounds (I : SubgraphIsoInstance) : ℕ :=
  if hasNoIsolatedBool I.pattern &&
      decide (I.pattern.distinctVertices.length ≤ I.target.distinctVertices.length) then
    I.target.distinctVertices.length ^ I.pattern.distinctVertices.length
  else 0

private def searchNoIso (I : SubgraphIsoInstance) : Bool :=
  hasNoIsolatedBool I.pattern &&
    decide (I.pattern.distinctVertices.length ≤ I.target.distinctVertices.length) &&
    ((searchStep)^[searchRounds I] (searchInit I)).2

private theorem iterate_searchStep (I : SubgraphIsoInstance) (k : ℕ) :
    (searchStep)^[k] (searchInit I) =
      ((I, (nextTuple I.target.distinctVertices.length)^[k]
          (List.replicate I.pattern.distinctVertices.length 0)),
        (List.range k).any fun c =>
          isValidIndexHom I ((nextTuple I.target.distinctVertices.length)^[c]
            (List.replicate I.pattern.distinctVertices.length 0))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, searchStep,
      List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]

private theorem searchNoIso_eq_true_iff (I : SubgraphIsoInstance) :
    searchNoIso I = true ↔ I ∈ SubgraphIsomorphismNoIso := by
  set n := I.target.distinctVertices.length
  set ℓ := I.pattern.distinctVertices.length
  constructor
  · intro h
    simp only [searchNoIso, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hno_b, hle⟩, hfound⟩ := h
    have hno : I.HasNoIsolatedPatternVertices := (hasNoIsolatedBool_eq_true_iff I).mp hno_b
    rw [iterate_searchStep, List.any_eq_true] at hfound
    obtain ⟨c, _, hc⟩ := hfound
    exact ⟨(mem_subgraphIsomorphism_iff_exists_indexHom I).mpr ⟨_, hc⟩, hno⟩
  · rintro ⟨hmem, hno⟩
    have hno_b : hasNoIsolatedBool I.pattern = true := (hasNoIsolatedBool_eq_true_iff I).mpr hno
    obtain ⟨ds, hds⟩ := (mem_subgraphIsomorphism_iff_exists_indexHom I).mp hmem
    have hv := hds
    simp only [isValidIndexHom, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true] at hv
    obtain ⟨⟨⟨hlen, hlt⟩, hinj⟩, _⟩ := hv
    have hle : ℓ ≤ n := by
      have hsub : ds.toFinset ⊆ Finset.range n := fun d hd =>
        Finset.mem_range.mpr (hlt d (List.mem_toFinset.mp hd))
      have hnd : ds.Nodup := List.nodup_iff_getElem?_ne_getElem?.mpr fun i j hij hj_lt heq => by
        have hi_lt : i < ℓ := by omega
        have hj_lt' : j < ℓ := by omega
        have hd_eq : ds.getD i 0 = ds.getD j 0 := by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq]
        exact (hinj i hi_lt j hj_lt').resolve_left (ne_of_lt hij) hd_eq
      calc ℓ = ds.length := hlen.symm
        _ = ds.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
        _ ≤ (Finset.range n).card := Finset.card_le_card hsub
        _ = n := Finset.card_range n
    have hle_b : decide (I.pattern.distinctVertices.length ≤
        I.target.distinctVertices.length) = true := decide_eq_true hle
    have hrds : searchRounds I = n ^ ℓ := by
      unfold searchRounds; simp only [hno_b, hle_b, Bool.true_and, ↓reduceIte]; rfl
    rw [searchNoIso, hno_b, hle_b, Bool.true_and, Bool.true_and, hrds, iterate_searchStep]
    dsimp only
    rw [List.any_eq_true]
    rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
    · have hℓ0 : I.pattern.distinctVertices.length = 0 := by dsimp [n, ℓ] at hn0 hle; omega
      have hds_nil : ds = [] := List.eq_nil_of_length_eq_zero (hlen.trans hℓ0)
      subst hds_nil
      refine ⟨0, List.mem_range.mpr (by dsimp [ℓ]; rw [hℓ0]; norm_num), ?_⟩
      rw [hℓ0]; simpa using hds
    · have hcode_lt : codeOfTuple n ds < n ^ ℓ := by
        have hc := codeOfTuple_lt hn_pos ds hlt
        rwa [hlen] at hc
      refine ⟨codeOfTuple n ds, List.mem_range.mpr hcode_lt, ?_⟩
      rw [iterate_nextTuple_replicate hn_pos, ← hlen, tupleOfCode_codeOfTuple hn_pos ds hlt]
      exact hds

open ComputableInPolyTime in
/-- **Exhaustive search for `SubgraphIsomorphismNoIso`**: decidable on multi-tape Turing machines
in time $O((|V(G)| + 2)^{2 |E(H)|} \cdot (|I| + 1)^e)$. -/
theorem subgraphIsomorphismNoIso_decidableInTimeO :
    ∃ e : ℕ, DecidableInTimeO SubgraphIsomorphismNoIso encSubgraphIsoInstance
      fun I => (((I.target.distinctVertices.length + 2) ^ (2 * I.patternEdgeCount) : ℕ) : ℝ) *
        ((encSubgraphIsoInstance I).length + 1) ^ e := by
  have hn_u : ComputableInPolyTime
      (fun I : SubgraphIsoInstance => I.target.distinctVertices.length)
      encSubgraphIsoInstance encUnary :=
    (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp
      (computableInPolyTime_subgraphIsoTarget id'))
  have hℓ_u : ComputableInPolyTime
      (fun I : SubgraphIsoInstance => I.pattern.distinctVertices.length)
      encSubgraphIsoInstance encUnary :=
    (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp
      (computableInPolyTime_subgraphIsoPattern id'))
  have hle_pt : ComputableInPolyTime
      (fun I : SubgraphIsoInstance =>
        decide (I.pattern.distinctVertices.length ≤ I.target.distinctVertices.length))
      encSubgraphIsoInstance encBool :=
    binary_le' (unary_to_binary.comp hℓ_u) (unary_to_binary.comp hn_u)
  have hGuard_pt : ComputableInPolyTime
      (fun I : SubgraphIsoInstance =>
        hasNoIsolatedBool I.pattern &&
          decide (I.pattern.distinctVertices.length ≤ I.target.distinctVertices.length))
      encSubgraphIsoInstance encBool :=
    bool_and.comp (computableInPolyTime_hasNoIsolatedBool.prod hle_pt)
  have hInit_pt : ComputableInPolyTime searchInit encSubgraphIsoInstance encSearchState := by
    have hrep : ComputableInPolyTime
        (fun I : SubgraphIsoInstance => List.replicate I.pattern.distinctVertices.length 0)
        encSubgraphIsoInstance (encList encUnary) := by
      have hm := (map (const (encIn := encUnary) (encOut := encUnary) 0)).comp (range.comp hℓ_u)
      have heq : (List.map (fun _ : ℕ => 0) ∘
          (List.range ∘ (((List.length ∘ Graph.distinctVertices) ∘
            fun x : SubgraphIsoInstance => x.pattern) ∘ id))) =
          fun I : SubgraphIsoInstance => List.replicate I.pattern.distinctVertices.length 0 :=
        funext fun _ => by simp
      exact heq ▸ hm
    exact (id'.prod hrep).prod (const false)
  have hStep_pt : ComputableInPolyTime searchStep encSearchState encSearchState := by
    let encP := encPair encSubgraphIsoInstance (encList encUnary)
    have hp := fst encP encBool
    have hI : ComputableInPolyTime (fun s : SearchState => s.1.1)
        encSearchState encSubgraphIsoInstance :=
      (fst encSubgraphIsoInstance (encList encUnary)).comp hp
    have hds : ComputableInPolyTime (fun s : SearchState => s.1.2)
        encSearchState (encList encUnary) :=
      (snd encSubgraphIsoInstance (encList encUnary)).comp hp
    have hnext : ComputableInPolyTime
        (fun s : SearchState => nextTuple s.1.1.target.distinctVertices.length s.1.2)
        encSearchState (encList encUnary) := by
      have hc := computableInPolyTime_nextTuple.comp ((hn_u.comp hI).prod hds)
      have heq : ((fun p : ℕ × List ℕ => nextTuple p.1 p.2) ∘
          fun x : SearchState =>
            ((((List.length ∘ Graph.distinctVertices) ∘
              fun x_1 : SubgraphIsoInstance => x_1.target) ∘ id)
                ((Prod.fst ∘ Prod.fst) x),
              (Prod.snd ∘ Prod.fst) x)) =
          fun s : SearchState => nextTuple s.1.1.target.distinctVertices.length s.1.2 :=
        funext fun _ => rfl
      exact heq ▸ hc
    have hor : ComputableInPolyTime
        (fun s : SearchState => s.2 || isValidIndexHom s.1.1 s.1.2)
        encSearchState encBool := by
      have hc := bool_or.comp
        ((snd encP encBool).prod (computableInPolyTime_isValidIndexHom.comp hp))
      have heq : ((fun p : Bool × Bool => p.1 || p.2) ∘
          fun x : SearchState =>
            (x.2, ((fun p : SubgraphIsoInstance × List ℕ => isValidIndexHom p.1 p.2) ∘
              Prod.fst) x)) =
          fun s : SearchState => s.2 || isValidIndexHom s.1.1 s.1.2 :=
        funext fun _ => rfl
      exact heq ▸ hc
    have hraw := (hI.prod hnext).prod hor
    have heq_s : (fun x : SearchState =>
        (((Prod.fst ∘ Prod.fst) x, nextTuple x.1.1.target.distinctVertices.length x.1.2),
          x.2 || isValidIndexHom x.1.1 x.1.2)) = searchStep :=
      funext fun _ => rfl
    exact heq_s ▸ hraw
  have hRounds_pt : ComputableInPolyTime searchRounds encSubgraphIsoInstance encNat := by
    have hraw := ite' hGuard_pt (binary_pow.comp ((unary_to_binary.comp hn_u).prod hℓ_u)) (const 0)
    have heq_r : (fun x : SubgraphIsoInstance =>
        if (((fun p : Bool × Bool => p.1 && p.2) ∘ fun x_1 : SubgraphIsoInstance =>
          (hasNoIsolatedBool x_1.pattern,
            decide (x_1.pattern.distinctVertices.length ≤
              x_1.target.distinctVertices.length))) x) = true then
          ((fun p : ℕ × ℕ => p.1 ^ p.2) ∘ fun x_1 : SubgraphIsoInstance =>
            ((id ∘ (((List.length ∘ Graph.distinctVertices) ∘
              fun x_2 : SubgraphIsoInstance => x_2.target) ∘ id)) x_1,
              (((List.length ∘ Graph.distinctVertices) ∘
                fun x_2 : SubgraphIsoInstance => x_2.pattern) ∘ id) x_1)) x
        else 0) = searchRounds :=
      funext fun _ => rfl
    exact heq_r ▸ hraw
  obtain ⟨dI, _, hInit⟩ := hInit_pt.exists_degree
  obtain ⟨dS, _, hStep⟩ := hStep_pt.exists_degree
  obtain ⟨dR, _, hRounds⟩ := hRounds_pt.exists_degree
  obtain ⟨dG, _, hGuard⟩ := hGuard_pt.exists_degree
  obtain ⟨dA, _, hAcc⟩ := (show ComputableInPolyTime (fun s : SearchState => s.2)
    encSearchState encBool by unfold encSearchState; fun_prop).exists_degree
  set stBound : SubgraphIsoInstance → ℕ := fun I =>
    6 * ((encSubgraphIsoInstance I).length + 1) ^ 2 + 16
  have hst_len (I : SubgraphIsoInstance) (k : ℕ) :
      (encSearchState ((searchStep)^[k] (searchInit I))).length ≤ stBound I := by
    rw [iterate_searchStep]
    set n := I.target.distinctVertices.length
    set ℓ := I.pattern.distinctVertices.length
    set L := (encSubgraphIsoInstance I).length
    have hnL : n ≤ L := I.target.length_distinctVertices_le.trans
      (length_encGraph_le_encSubgraphIso I).1
    have hℓL : ℓ ≤ L := I.pattern.length_distinctVertices_le.trans
      (length_encGraph_le_encSubgraphIso I).2
    have hiter_props : ∀ j,
        ((nextTuple n)^[j] (List.replicate ℓ 0)).length = ℓ ∧
        ∀ d ∈ (nextTuple n)^[j] (List.replicate ℓ 0), d ≤ n := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply', nextTuple_eq_rec]
        exact ⟨(length_nextTupleRec n _).trans ih.1, mem_nextTupleRec_le ih.2⟩
    obtain ⟨hlen_tup, hmem_tup⟩ := hiter_props k
    have htup_enc : ∀ xs : List ℕ, (∀ d ∈ xs, d ≤ n) →
        (encList encUnary xs).length ≤ xs.length * (2 * n + 2) := by
      intro xs hxs
      induction xs with
      | nil => simp
      | cons d rest ih =>
        have hd := hxs d List.mem_cons_self
        have hr := ih fun x hx => hxs x (List.mem_cons_of_mem _ hx)
        simp only [encList_cons, List.length_append, length_frame, encUnary_apply,
          List.length_replicate, List.length_cons]
        nlinarith
    have htup_bound : (encList encUnary ((nextTuple n)^[k] (List.replicate ℓ 0))).length ≤
        2 * L ^ 2 + 2 * L := by
      calc (encList encUnary ((nextTuple n)^[k] (List.replicate ℓ 0))).length
          ≤ ((nextTuple n)^[k] (List.replicate ℓ 0)).length * (2 * n + 2) :=
            htup_enc _ hmem_tup
        _ = ℓ * (2 * n + 2) := by rw [hlen_tup]
        _ ≤ L * (2 * L + 2) := Nat.mul_le_mul hℓL (by omega)
        _ = 2 * L ^ 2 + 2 * L := by ring
    simp only [encSearchState, length_encPair, encBool_apply, List.length_singleton]
    dsimp only [stBound]
    nlinarith
  have hround (I : SubgraphIsoInstance) (k : ℕ) (_ : k ≤ searchRounds I) :
      ((encSearchState ((searchStep)^[k] (searchInit I))).length + 1) ^ dS ≤
        (stBound I + 1) ^ dS :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (hst_len I k) 1) dS
  have hit := hAcc.inO.comp
    (ComputableInO.iterate hRounds.inO hInit.inO hStep.inO hround hround
      (fun I k _ => hst_len I k))
  have hcnt_poly : PolyBounded (fun I => (encSubgraphIsoInstance I).length)
      (fun I => (encNat (searchRounds I)).length) :=
    hRounds_pt.polyBounded_length
  have hoverhead : PolyBounded (fun I => (encSubgraphIsoInstance I).length)
      (fun I => ((encSubgraphIsoInstance I).length + 1) ^ dG +
        (((encSubgraphIsoInstance I).length + 1) ^ dR +
          ((encSubgraphIsoInstance I).length + 1) ^ dI +
          (stBound I + 1) ^ dS + stBound I +
          ((encNat (searchRounds I)).length + 1) ^ 2 +
          (stBound I + 1) ^ dA) + 10) := by
    dsimp only [stBound]
    growth_poly
  obtain ⟨Cp, E, hCp⟩ := hoverhead.exists_le
  obtain ⟨dAnd, _, hAnd⟩ := ComputableInPolyTime.bool_and.exists_degree
  have hfn_eq : ((fun p : Bool × Bool => p.1 && p.2) ∘ fun I : SubgraphIsoInstance =>
      (hasNoIsolatedBool I.pattern &&
        decide (I.pattern.distinctVertices.length ≤ I.target.distinctVertices.length),
      ((fun s : SearchState => s.2) ∘ fun I => (searchStep)^[searchRounds I] (searchInit I)) I)) =
      searchNoIso := funext fun _ => rfl
  have hfull' := hfn_eq ▸ (hAnd.inO.comp (hGuard.inO.prod hit))
  have hrds_le (I : SubgraphIsoInstance) :
      searchRounds I + 1 ≤
        2 * (I.target.distinctVertices.length + 2) ^ (2 * I.patternEdgeCount) := by
    have h1 : 1 ≤ (I.target.distinctVertices.length + 2) ^ (2 * I.patternEdgeCount) :=
      Nat.one_le_pow _ _ (by omega)
    unfold searchRounds
    split_ifs with hg
    · simp only [Bool.and_eq_true] at hg
      have hno : I.HasNoIsolatedPatternVertices := (hasNoIsolatedBool_eq_true_iff I).mp hg.1
      have h2k := card_patternVertices_le_two_mul_patternEdgeCount hno
      have hpow : I.target.distinctVertices.length ^ I.pattern.distinctVertices.length ≤
          (I.target.distinctVertices.length + 2) ^ (2 * I.patternEdgeCount) :=
        (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) h2k)
      omega
    · omega
  let C_nat : ℕ := 3 * Cp + 5 ^ dAnd + 2
  refine ⟨E, (DecidableInTimeO.of_computableInO hfull'
    (fun I => (searchNoIso_eq_true_iff I).symm)
    (T := fun I => (C_nat : ℝ) *
      ((((I.target.distinctVertices.length + 2) ^ (2 * I.patternEdgeCount) : ℕ) : ℝ) *
        ((encSubgraphIsoInstance I).length + 1) ^ E))
    (fun I => ?_)).mono C_nat
      (fun _ => le_add_of_nonneg_right (Nat.cast_nonneg C_nat)) (fun _ => by positivity)⟩
  have hover := hCp I
  have hrds := hrds_le I
  have hpair4 : ∀ p : Bool × Bool, (encPair encBool encBool p).length = 4 := fun _ => by simp
  simp only [Function.comp_apply, hpair4]
  set X := (I.target.distinctVertices.length + 2) ^ (2 * I.patternEdgeCount)
  set P := ((encSubgraphIsoInstance I).length + 1) ^ E
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hXP1 : 1 ≤ X * P := Nat.mul_pos hX1 hP1
  set M_in := (stBound I + 1) ^ dS + stBound I + ((encNat (searchRounds I)).length + 1) ^ 2
  have hM_le : M_in ≤ Cp * P :=
    (by dsimp only [M_in]; omega : M_in ≤ _).trans hover
  have hmul_rds : (searchRounds I + 1) * M_in ≤ 2 * Cp * (X * P) := by
    calc (searchRounds I + 1) * M_in ≤ (2 * X) * (Cp * P) := Nat.mul_le_mul hrds hM_le
      _ = 2 * Cp * (X * P) := by ring
  have hst_end : ((encSearchState ((searchStep)^[searchRounds I] (searchInit I))).length + 1) ^ dA ≤
      (stBound I + 1) ^ dA :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (hst_len I (searchRounds I)) 1) dA
  have hrest_le : ((encSubgraphIsoInstance I).length + 1) ^ dG +
      (((encSubgraphIsoInstance I).length + 1) ^ dR +
        ((encSubgraphIsoInstance I).length + 1) ^ dI +
        ((encSearchState ((searchStep)^[searchRounds I] (searchInit I))).length + 1) ^ dA) ≤
      Cp * (X * P) := by
    calc _ ≤ Cp * P := by omega
      _ ≤ Cp * (X * P) := Nat.mul_le_mul_left Cp (Nat.le_mul_of_pos_left P hX1)
  have hand_le : (4 + 1) ^ dAnd ≤ 5 ^ dAnd * (X * P) :=
    Nat.le_mul_of_pos_right _ hXP1
  have hnat :
      ((encSubgraphIsoInstance I).length + 1) ^ dG +
        ((((encSubgraphIsoInstance I).length + 1) ^ dR +
          ((encSubgraphIsoInstance I).length + 1) ^ dI +
          (searchRounds I + 1) * M_in) +
          ((encSearchState ((searchStep)^[searchRounds I] (searchInit I))).length + 1) ^ dA) +
        (4 + 1) ^ dAnd ≤ C_nat * (X * P) := by
    have hexp : C_nat * (X * P) =
        2 * Cp * (X * P) + Cp * (X * P) + 5 ^ dAnd * (X * P) + 2 * (X * P) := by
      dsimp only [C_nat]; ring
    rw [hexp]; omega
  exact (Nat.cast_le.mpr hnat).trans_eq (by dsimp only [X, P]; push_cast; ring)

/-- **`SubgraphIsomorphismNoIso` belongs to `XP`** parameterized by `patternEdgeCount`. -/
theorem subgraphIsomorphismNoIso_mem_XP :
    SubgraphIsomorphismNoIso ∈ XP encSubgraphIsoInstance SubgraphIsoInstance.patternEdgeCount := by
  obtain ⟨e, hdec⟩ := subgraphIsomorphismNoIso_decidableInTimeO
  refine ⟨fun k => 2 ^ (2 * k), fun k => 2 * k + e,
    hdec.mono 1 (fun I => ?_) (fun _ => by positivity)⟩
  set L := (encSubgraphIsoInstance I).length
  set k := I.patternEdgeCount
  have hnL : I.target.distinctVertices.length + 2 ≤ 2 * (L + 1) := by
    have := I.target.length_distinctVertices_le.trans (length_encGraph_le_encSubgraphIso I).1
    dsimp [L]; omega
  have hpow : (I.target.distinctVertices.length + 2) ^ (2 * k) * (L + 1) ^ e ≤
      2 ^ (2 * k) * (L + 1) ^ (2 * k + e) := by
    calc (I.target.distinctVertices.length + 2) ^ (2 * k) * (L + 1) ^ e
        ≤ (2 * (L + 1)) ^ (2 * k) * (L + 1) ^ e :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hnL _)
      _ = 2 ^ (2 * k) * (L + 1) ^ (2 * k + e) := by rw [Nat.mul_pow, Nat.pow_add]; ring
  have hcast : (((I.target.distinctVertices.length + 2) ^ (2 * k) : ℕ) : ℝ) * ((L : ℝ) + 1) ^ e ≤
      (2 ^ (2 * k) : ℕ) * ((L : ℝ) + 1) ^ (2 * k + e) := by exact_mod_cast hpow
  push_cast at hcast ⊢
  linarith

/-- For any constant bound `K`, the bounded-edge slice `{I ∈ SubgraphIsomorphismNoIso | k ≤ K}`
is decidable in polynomial time (`∈ P`). -/
theorem subgraphIsomorphismNoIso_slice_mem_P (K : ℕ) :
    {I ∈ SubgraphIsomorphismNoIso | I.patternEdgeCount ≤ K} ∈ P encSubgraphIsoInstance := by
  let κK : SubgraphIsoInstance → ℕ := fun I => min I.patternEdgeCount K
  have hXP : {I ∈ SubgraphIsomorphismNoIso | I.patternEdgeCount ≤ K} ∈
      XP encSubgraphIsoInstance κK := by
    obtain ⟨f, g, hdec⟩ := subgraphIsomorphismNoIso_mem_XP
    have hp : ComputableInPolyTime (fun I : SubgraphIsoInstance => decide (I.patternEdgeCount ≤ K))
        encSubgraphIsoInstance encBool := by fun_prop
    obtain ⟨e', hdec'⟩ := hdec.inter hp (fun _ => by positivity)
    refine ⟨fun k => f k + 1, fun k => g k + e',
      (show {I | decide (I.patternEdgeCount ≤ K) = true} ∩ SubgraphIsomorphismNoIso =
          {I ∈ SubgraphIsomorphismNoIso | I.patternEdgeCount ≤ K} from by
        ext I; simp [and_comm]) ▸ hdec'.mono 1 (fun I => ?_) (fun _ => by positivity)⟩
    set L := ((encSubgraphIsoInstance I).length : ℝ)
    have hL1 : 1 ≤ L + 1 := by
      dsimp [L]; linarith [show (0 : ℝ) ≤ (encSubgraphIsoInstance I).length from Nat.cast_nonneg _]
    split_ifs with hle
    · have hk_eq : κK I = I.patternEdgeCount := Nat.min_eq_left (decide_eq_true_eq.mp hle)
      rw [hk_eq]
      have hp1 : (L + 1) ^ g I.patternEdgeCount ≤ (L + 1) ^ (g I.patternEdgeCount + e') :=
        pow_le_pow_right₀ hL1 (Nat.le_add_right _ _)
      have hp2 : (L + 1) ^ e' ≤ (L + 1) ^ (g I.patternEdgeCount + e') :=
        pow_le_pow_right₀ hL1 (Nat.le_add_left _ _)
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg (f I.patternEdgeCount))]
    · have hp2 : (L + 1) ^ e' ≤ (L + 1) ^ (g (κK I) + e') :=
        pow_le_pow_right₀ hL1 (Nat.le_add_left _ _)
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (f (κK I)))
        (pow_nonneg (by linarith : (0 : ℝ) ≤ L + 1) (g (κK I) + e'))]
  rwa [XP_eq_P_of_le (K := K) (fun I => Nat.min_le_right _ _)] at hXP

end ExhaustiveSolver

/-! ### 4. Isolated-Vertex Removal and `W[1]`-Hardness via `Clique` -/

/-- Strip isolated vertices from `H`, keeping only declared vertices incident to an edge. -/
private def stripIsolated (H : Graph) : Graph where
  vertices := H.distinctVertices.filter fun u => H.distinctVertices.any fun w => H.adjBool u w
  edges := H.edges

private def fixedYesNoIso : SubgraphIsoInstance := ⟨matchingGraph 1, matchingGraph 1⟩
private def fixedNoNoIso : SubgraphIsoInstance := ⟨⟨[], []⟩, matchingGraph 1⟩

private theorem fixedNoNoIso_not_mem_subgraphIsomorphism : fixedNoNoIso ∉ SubgraphIsomorphism := by
  rintro ⟨f⟩
  have h0 : (0 : ℕ) ∈ (matchingGraph 1).vertices := by simp [matchingGraph]
  exact List.not_mem_nil (f ⟨0, h0⟩).2

private def reduceStripIsolated (I : SubgraphIsoInstance) : SubgraphIsoInstance :=
  if decide (I.pattern.distinctVertices.length ≤ I.target.distinctVertices.length) then
    let H' := stripIsolated I.pattern
    if H'.vertices.isEmpty then fixedYesNoIso else ⟨I.target, H'⟩
  else fixedNoNoIso

open ComputableInPolyTime in
private theorem computableInPolyTime_reduceStripIsolated :
    ComputableInPolyTime reduceStripIsolated encSubgraphIsoInstance encSubgraphIsoInstance := by
  have hstrip : ComputableInPolyTime stripIsolated encGraph encGraph := by
    unfold stripIsolated
    fun_prop
  unfold reduceStripIsolated
  exact ite' (by fun_prop)
    (ite' ((listIsEmpty' encNat).comp
        (encGraph_vertices_polyTime (hstrip.comp (computableInPolyTime_subgraphIsoPattern id'))))
      (const fixedYesNoIso)
      (computableInPolyTime_subgraphIsoMk (computableInPolyTime_subgraphIsoTarget id')
        (hstrip.comp (computableInPolyTime_subgraphIsoPattern id'))))
    (const fixedNoNoIso)

private theorem stripIsolated_hasNoIsolated (G H : Graph) :
    (SubgraphIsoInstance.mk G (stripIsolated H)).HasNoIsolatedPatternVertices := by
  rintro ⟨u, hu⟩
  simp only [stripIsolated, List.mem_filter, List.any_eq_true, Graph.adjBool_eq_true_iff] at hu
  obtain ⟨hu_dv, w, hw_mem, hadj⟩ := hu
  have hw_in : w ∈ (stripIsolated H).vertices := by
    simp only [stripIsolated, List.mem_filter, List.any_eq_true, Graph.adjBool_eq_true_iff]
    exact ⟨hw_mem, u, hu_dv, hadj.symm⟩
  exact ⟨⟨w, hw_in⟩, hadj⟩

private theorem mem_stripIsolated_of_adj {H : Graph} {u v : ℕ}
    (hu : u ∈ H.vertices) (hv : v ∈ H.vertices) (hadj : H.toSimpleGraph.Adj u v) :
    u ∈ (stripIsolated H).vertices := by
  simp only [stripIsolated, List.mem_filter, List.any_eq_true, Graph.adjBool_eq_true_iff,
    Graph.mem_distinctVertices]
  exact ⟨hu, v, hv, hadj⟩

private theorem stripIsolated_edgeFinset_card (H : Graph) :
    (stripIsolated H).induced.edgeFinset.card = H.induced.edgeFinset.card := by
  classical
  refine Finset.card_bij
    (fun e _ => e.map fun u => ⟨u.1, H.mem_distinctVertices.mp (List.mem_of_mem_filter u.2)⟩)
    (fun e he => by
      induction e using Sym2.ind with | _ a b =>
        simp only [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Graph.induced_adj, Graph.toSimpleGraph_adj] at he ⊢
        exact he)
    (fun e₁ _ e₂ _ heq => by
      induction e₁ using Sym2.ind with | _ a₁ b₁ =>
        induction e₂ using Sym2.ind with | _ a₂ b₂ =>
          simpa only [Sym2.map_mk, Sym2.eq_iff, Subtype.ext_iff] using heq)
    (fun e he => by
      induction e using Sym2.ind with | _ a b =>
        have hadj : H.toSimpleGraph.Adj a.1 b.1 := SimpleGraph.mem_edgeFinset.mp he
        exact ⟨s(⟨a.1, mem_stripIsolated_of_adj a.2 b.2 hadj⟩,
          ⟨b.1, mem_stripIsolated_of_adj b.2 a.2 hadj.symm⟩),
          SimpleGraph.mem_edgeFinset.mpr hadj, rfl⟩)

/-- **Isolated-vertex removal**: `SubgraphIsomorphism` polynomial-time FPT-reduces to
`SubgraphIsomorphismNoIso` with parameter at most `max k 1`. -/
theorem fptReducible_subgraphIsomorphism_noIso :
    FPTReducible encSubgraphIsoInstance encSubgraphIsoInstance
      SubgraphIsoInstance.patternEdgeCount SubgraphIsoInstance.patternEdgeCount
      SubgraphIsomorphism SubgraphIsomorphismNoIso := by
  refine FPTReducible.of_computableInPolyTime computableInPolyTime_reduceStripIsolated
    (h := fun k => k + 1) (fun I => ?_) (fun I => ?_)
  · unfold reduceStripIsolated; dsimp only
    split_ifs with hle hemp
    · simp [fixedYesNoIso, matchingGraph_patternEdgeCount]
    · rw [patternEdgeCount_eq_card_edgeFinset, stripIsolated_edgeFinset_card,
        ← patternEdgeCount_eq_card_edgeFinset]; exact Nat.le_succ _
    · simp [fixedNoNoIso, matchingGraph_patternEdgeCount]
  · unfold reduceStripIsolated; dsimp only
    split_ifs with hle hemp
    · simp only [decide_eq_true_eq] at hle
      have hyes : fixedYesNoIso ∈ SubgraphIsomorphismNoIso :=
        ⟨⟨SimpleGraph.Copy.id _⟩, matchingGraph_hasNoIsolated (matchingGraph 1) 1⟩
      simp only [hyes, iff_true]
      have hcard_le : Fintype.card {x // x ∈ I.pattern.vertices} ≤
          Fintype.card {x // x ∈ I.target.vertices} := by
        simpa [Graph.card_vertexSubtype, ← Graph.length_distinctVertices] using hle
      obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard_le
      refine ⟨⟨⟨emb, fun {u v} hadj => ?_⟩, emb.injective⟩⟩
      have hu_in := mem_stripIsolated_of_adj u.2 v.2 hadj
      rw [List.isEmpty_iff.mp hemp] at hu_in; exact (List.not_mem_nil hu_in).elim
    · simp only [decide_eq_true_eq] at hle
      simp only [SubgraphIsomorphismNoIso, Set.mem_ofPred_eq,
        stripIsolated_hasNoIsolated I.target I.pattern, and_true]
      constructor
      · rintro ⟨f⟩
        let inc : {v // v ∈ (stripIsolated I.pattern).vertices} ↪ {v // v ∈ I.pattern.vertices} :=
          ⟨fun u => ⟨u.1, I.pattern.mem_distinctVertices.mp (List.mem_of_mem_filter u.2)⟩,
            fun _ _ h => Subtype.ext (Subtype.mk.inj h)⟩
        exact ⟨⟨⟨fun u => f (inc u), fun hadj => f.toHom.map_adj hadj⟩,
          f.injective.comp inc.injective⟩⟩
      · rintro ⟨f₀⟩; classical
        let pSub : {v // v ∈ I.pattern.vertices} → Prop :=
          fun u => u.1 ∈ (stripIsolated I.pattern).vertices
        let eSub : {u : {v // v ∈ I.pattern.vertices} // pSub u} ≃
            {v // v ∈ (stripIsolated I.pattern).vertices} :=
          ⟨fun u => ⟨u.1.1, u.2⟩,
           fun v => ⟨⟨v.1, I.pattern.mem_distinctVertices.mp (List.mem_of_mem_filter v.2)⟩, v.2⟩,
           fun _ => rfl, fun _ => rfl⟩
        let f_in : {u : {v // v ∈ I.pattern.vertices} // pSub u} ↪ {v // v ∈ I.target.vertices} :=
          ⟨fun u => f₀ (eSub u), fun a b h => eSub.injective (f₀.injective h)⟩
        let pRng : {v // v ∈ I.target.vertices} → Prop := fun w => w ∈ Set.range f_in
        have hcard_H : Fintype.card {v // v ∈ I.pattern.vertices} =
            Fintype.card {u // pSub u} + Fintype.card {u // ¬pSub u} := by
          rw [Fintype.card_subtype_compl pSub, Nat.add_comm]
          exact (Nat.sub_add_cancel (Fintype.card_subtype_le pSub)).symm
        have hcard_G : Fintype.card {v // v ∈ I.target.vertices} =
            Fintype.card {w // pRng w} + Fintype.card {w // ¬pRng w} := by
          rw [Fintype.card_subtype_compl pRng, Nat.add_comm]
          exact (Nat.sub_add_cancel (Fintype.card_subtype_le pRng)).symm
        have hcard_range : Fintype.card {w // pRng w} = Fintype.card {u // pSub u} :=
          (Fintype.card_of_bijective (Equiv.ofInjective f_in f_in.injective).bijective).symm
        have hle_card : Fintype.card {v // v ∈ I.pattern.vertices} ≤
            Fintype.card {v // v ∈ I.target.vertices} := by
          simpa [Graph.card_vertexSubtype, ← Graph.length_distinctVertices] using hle
        obtain ⟨emb_out⟩ := Function.Embedding.nonempty_of_card_le
          (show Fintype.card {u // ¬pSub u} ≤ Fintype.card {w // ¬pRng w} by omega)
        let full : {v // v ∈ I.pattern.vertices} → {v // v ∈ I.target.vertices} := fun u =>
          if hu : pSub u then f_in ⟨u, hu⟩ else (emb_out ⟨u, hu⟩).1
        have hfull_inj : Function.Injective full := fun a b hab => by
          by_cases ha : pSub a <;> by_cases hb : pSub b <;>
            simp only [full, ha, hb, ↓reduceDIte] at hab
          · exact Subtype.ext_iff.mp (f_in.injective hab)
          · exact ((emb_out ⟨b, hb⟩).2 ⟨⟨a, ha⟩, hab⟩).elim
          · exact ((emb_out ⟨a, ha⟩).2 ⟨⟨b, hb⟩, hab.symm⟩).elim
          · exact Subtype.ext_iff.mp (emb_out.injective (Subtype.ext hab))
        refine ⟨⟨⟨full, fun {a b} hadj => ?_⟩, hfull_inj⟩⟩
        have ha : pSub a := mem_stripIsolated_of_adj a.2 b.2 hadj
        have hb : pSub b := mem_stripIsolated_of_adj b.2 a.2 hadj.symm
        simp only [full, ha, hb, ↓reduceDIte]
        exact f₀.toHom.map_adj hadj
    · simp only [decide_eq_true_eq, not_le] at hle
      simp only [show fixedNoNoIso ∉ SubgraphIsomorphismNoIso from
        fun h => fixedNoNoIso_not_mem_subgraphIsomorphism h.1, iff_false]
      rintro ⟨f⟩
      have hcard := Fintype.card_le_of_injective f f.injective
      simp only [Graph.card_vertexSubtype, ← Graph.length_distinctVertices] at hcard; omega

/-- Complete graph $K_m$ on vertex labels `0, …, m - 1`. -/
private def completePattern (m : ℕ) : Graph where
  vertices := List.range m
  edges := (List.range m).flatMap fun u =>
    ((List.range m).filter fun v => decide (u ≠ v)).map fun v => (u, v)

private theorem completePattern_adj_iff {m u v : ℕ} (hu : u < m) (hv : v < m) :
    (completePattern m).toSimpleGraph.Adj u v ↔ u ≠ v := by
  simp only [Graph.toSimpleGraph_adj, completePattern, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_range, decide_eq_true_eq, Prod.mk.injEq]
  exact ⟨fun h => h.1, fun hne => ⟨hne, Or.inl ⟨u, hu, v, ⟨hv, hne⟩, rfl, rfl⟩⟩⟩

private def cliqueToSubgraphIso (x : CliqueInstance) : SubgraphIsoInstance :=
  if min 2 x.m == 0 then fixedYesNoIso
  else if min 2 x.m == 1 then
    if x.graph.vertices.length == 0 then fixedNoNoIso else fixedYesNoIso
  else ⟨x.graph, completePattern (min (x.graph.vertices.length + 2) x.m)⟩

open ComputableInPolyTime in
private theorem computableInPolyTime_cliqueToSubgraphIso :
    ComputableInPolyTime cliqueToSubgraphIso encCliqueInstance encSubgraphIsoInstance := by
  have hv_pt := encGraph_vertices_polyTime (encCliqueInstance_graph_polyTime id')
  have hm_pt := encCliqueInstance_m_polyTime id'
  have hm2_u := binary_min_unary' (const 2) hm_pt
  have hm_cap := binary_min_unary' (unary_add' ((length_list encNat).comp hv_pt) (const 2)) hm_pt
  have hrng : ComputableInPolyTime List.range encUnary (encList encNat) := by
    have : List.range = fun m : ℕ => (List.range m).map id := by simp
    rw [this]; exact mapWithInput range (unary_to_binary.comp (snd _ _))
  have hcomp : ComputableInPolyTime completePattern encUnary encGraph :=
    encGraph_mk_polyTime hrng (flatMapWithInput hrng
      (mapWithInput (filterWithInput (hrng.comp (fst _ _)) (by fun_prop)) (by fun_prop)))
  unfold cliqueToSubgraphIso
  exact ite' (unary_beq hm2_u (const 0)) (const fixedYesNoIso)
    (ite' (unary_beq hm2_u (const 1))
      (ite' (unary_beq ((length_list encNat).comp hv_pt) (const 0))
        (const fixedNoNoIso) (const fixedYesNoIso))
      (computableInPolyTime_subgraphIsoMk (encCliqueInstance_graph_polyTime id')
        (hcomp.comp hm_cap)))

/-- **`Clique` FPT-reduces to `SubgraphIsomorphismNoIso`** by mapping `(G, m)` (`m ≥ 2`) to
`(G, K_{min(|V(G)| + 2, m)})`, which has `O(m²)` edges and no isolated vertices. -/
theorem fptReducible_clique_subgraphIsomorphismNoIso :
    FPTReducible encCliqueInstance encSubgraphIsoInstance
      CliqueInstance.m SubgraphIsoInstance.patternEdgeCount
      Clique SubgraphIsomorphismNoIso := by
  refine FPTReducible.of_computableInPolyTime computableInPolyTime_cliqueToSubgraphIso
    (h := fun m => m * m + 1) (fun x => ?_) (fun x => ?_)
  · unfold cliqueToSubgraphIso
    split_ifs with hm0 hm1 hemp
    · simp [fixedYesNoIso, matchingGraph_patternEdgeCount]
    · simp [fixedNoNoIso, matchingGraph_patternEdgeCount]
    · simp [fixedYesNoIso, matchingGraph_patternEdgeCount]
    · set m' := min (x.graph.vertices.length + 2) x.m
      have hm'_le : m' ≤ x.m := Nat.min_le_right _ _
      rw [patternEdgeCount_eq_card_edgeFinset]
      classical
      have hv : Fintype.card {v // v ∈ (completePattern m').vertices} = m' := by
        rw [Graph.card_vertexSubtype, completePattern,
          List.toFinset_card_of_nodup List.nodup_range, List.length_range]
      have hcard_le : (completePattern m').induced.edgeFinset.card ≤ m' * m' :=
        (Finset.card_le_univ _).trans
          ((Fintype.card_le_of_surjective (Function.uncurry Sym2.mk) Sym2.mk_surjective).trans_eq
            (by rw [Fintype.card_prod, hv]))
      exact (hcard_le.trans (Nat.mul_le_mul hm'_le hm'_le)).trans (Nat.le_succ _)
  · unfold cliqueToSubgraphIso
    have hyes : fixedYesNoIso ∈ SubgraphIsomorphismNoIso :=
      ⟨⟨SimpleGraph.Copy.id _⟩, matchingGraph_hasNoIsolated (matchingGraph 1) 1⟩
    have hno : fixedNoNoIso ∉ SubgraphIsomorphismNoIso := fun h =>
      fixedNoNoIso_not_mem_subgraphIsomorphism h.1
    split_ifs with hm0 hm1 hemp
    · have hm0' : x.m = 0 := by have := beq_iff_eq.mp hm0; omega
      simp only [hyes, iff_true, mem_Clique_iff, hm0']
      exact ⟨∅, by simp, by simp⟩
    · have hm1' : x.m = 1 := by have := beq_iff_eq.mp hm1; omega
      have hemp' : x.graph.vertices = [] := List.eq_nil_of_length_eq_zero (beq_iff_eq.mp hemp)
      simp only [hno, iff_false, mem_Clique_iff, hm1', hemp']
      rintro ⟨S, hS, hclq⟩
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [hclq.2]; omega)
      exact List.not_mem_nil (hS v hv)
    · have hm1' : x.m = 1 := by have := beq_iff_eq.mp hm1; omega
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil x.graph.vertices
        (fun h => by simp [h] at hemp)
      simp only [hyes, iff_true, mem_Clique_iff, hm1']
      exact ⟨{v}, fun u hu => by obtain rfl := Finset.mem_singleton.mp hu; exact hv, by simp⟩
    · set m' := min (x.graph.vertices.length + 2) x.m
      have hm2 : 2 ≤ x.m := by simp only [beq_iff_eq] at hm0 hm1; omega
      have hm'2 : 2 ≤ m' := Nat.le_min.mpr ⟨by omega, hm2⟩
      have hno_iso :
          (SubgraphIsoInstance.mk x.graph (completePattern m')).HasNoIsolatedPatternVertices := by
        rintro ⟨u, hu⟩
        have hu' : u < m' := List.mem_range.mp hu
        by_cases hu0 : u = 0
        · refine ⟨⟨1, List.mem_range.mpr (by omega)⟩, ?_⟩
          rw [Graph.induced_adj]; dsimp only
          exact (completePattern_adj_iff hu' (by omega)).mpr (by omega)
        · refine ⟨⟨0, List.mem_range.mpr (by omega)⟩, ?_⟩
          rw [Graph.induced_adj]; dsimp only
          exact (completePattern_adj_iff hu' (by omega)).mpr hu0
      simp only [SubgraphIsomorphismNoIso, Set.mem_ofPred_eq, hno_iso, and_true, mem_Clique_iff,
        SubgraphIsomorphism]
      constructor
      · rintro ⟨S, hSV, hclq, hcard⟩
        have hS_le : S.card ≤ x.graph.vertices.length :=
          (Finset.card_le_card fun v hv => List.mem_toFinset.mpr (hSV v hv)).trans
            (List.toFinset_card_le _)
        have hm'_eq : m' = x.m := Nat.min_eq_right (by omega)
        let eFin : Fin m' ≃ S :=
          (Fin.castOrderIso (hm'_eq.trans hcard.symm)).toEquiv.trans S.equivFin.symm
        let phi : {v // v ∈ (completePattern m').vertices} → {v // v ∈ x.graph.vertices} :=
          fun u => ⟨(eFin ⟨u.1, List.mem_range.mp u.2⟩).1,
            hSV _ (eFin ⟨u.1, List.mem_range.mp u.2⟩).2⟩
        have hphi_inj : Function.Injective phi := fun a b hab => by
          have hv : (phi a).1 = (phi b).1 := congrArg Subtype.val hab
          exact Subtype.ext (congrArg Fin.val (eFin.injective (Subtype.ext hv)))
        refine ⟨⟨⟨phi, fun {a b} hadj => ?_⟩, hphi_inj⟩⟩
        exact hclq (eFin ⟨a.1, List.mem_range.mp a.2⟩).2 (eFin ⟨b.1, List.mem_range.mp b.2⟩).2
          (Subtype.coe_ne_coe.mpr fun h =>
            hadj.ne (Subtype.ext (congrArg Fin.val (eFin.injective h))))
      · rintro ⟨f⟩
        let S : Finset ℕ := Finset.univ.image fun u : {v // v ∈ (completePattern m').vertices} =>
          (f u).1
        have hS_card : S.card = m' := by
          dsimp only [S]
          rw [Finset.card_image_of_injective Finset.univ
              (fun a b (h : (f a).1 = (f b).1) => f.injective (Subtype.ext h)),
            Finset.card_univ, Graph.card_vertexSubtype, completePattern,
            List.toFinset_card_of_nodup List.nodup_range, List.length_range]
        have hS_sub : ∀ v ∈ S, v ∈ x.graph.vertices := fun v hv => by
          obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv; exact (f u).2
        have hS_le : m' ≤ x.graph.vertices.length := hS_card ▸
          (Finset.card_le_card fun v hv => List.mem_toFinset.mpr (hS_sub v hv)).trans
            (List.toFinset_card_le _)
        have hm'_eq : m' = x.m := by
          rcases min_choice (x.graph.vertices.length + 2) x.m with h | h <;> [omega; exact h]
        refine ⟨S, hS_sub, ⟨fun u hu v hv huv => ?_, hS_card.trans hm'_eq⟩⟩
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu; obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
        exact f.toHom.map_adj ((completePattern_adj_iff (List.mem_range.mp a.2)
          (List.mem_range.mp b.2)).mpr fun h => huv (congrArg (fun z => (f z).1) (Subtype.ext h)))

/-- **`SubgraphIsomorphismNoIso` is `W[1]`-hard** parameterized by `patternEdgeCount`. -/
theorem subgraphIsomorphismNoIso_wHard :
    WHard 1 encSubgraphIsoInstance SubgraphIsoInstance.patternEdgeCount SubgraphIsomorphismNoIso :=
  Clique_wHard.trans fptReducible_clique_subgraphIsomorphismNoIso

/-- **`SubgraphIsomorphism` is `W[1]`-hard** parameterized by `patternEdgeCount`. -/
theorem subgraphIsomorphism_wHard :
    WHard 1 encSubgraphIsoInstance SubgraphIsoInstance.patternEdgeCount SubgraphIsomorphism :=
  subgraphIsomorphismNoIso_wHard.trans <| FPTReducible.of_computableInPolyTime
    (ComputableInPolyTime.ite' computableInPolyTime_hasNoIsolatedBool
      ComputableInPolyTime.id' (ComputableInPolyTime.const fixedNoNoIso))
    (h := fun k => k + 1)
    (fun I => by split_ifs <;> [exact Nat.le_succ _; simp [fixedNoNoIso,
      matchingGraph_patternEdgeCount]])
    (fun I => by
      split_ifs with hb
      · simp [SubgraphIsomorphismNoIso, (hasNoIsolatedBool_eq_true_iff I).mp hb]
      · simp [SubgraphIsomorphismNoIso, mt (hasNoIsolatedBool_eq_true_iff I).mpr hb,
          fixedNoNoIso_not_mem_subgraphIsomorphism])

end CslibFrontier.ParameterizedComplexity
