/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Problems.MaxCut.Simple
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Combinatorics.SimpleGraph.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.List.GetD


/-!
# Minimum Bisection (`MinBisection`)

This module defines the decision problems `MinBisection` (minimum bisection on simple undirected
graphs with an even number of vertices) and `ThreeMinBisection` (minimum bisection restricted to
3-regular simple graphs) and proves that `MinBisection` is `NP`-complete under standard Lean axioms.

`MinBisection` is reduced from `Cslib.Complexity.SimpleMaxCut` by adding `n` isolated vertices and
complementing the resulting `2n`-vertex graph, mapping threshold `k` to `n² - k`
. The further reduction to `ThreeMinBisection` lives in
`CslibFrontier.Computability.Complexity.Problems.ThreeMinBisectionGadget` and
`CslibFrontier.Computability.Complexity.Problems.ThreeMinBisection`.

## Main definitions

* `CslibFrontier.Complexity.MinBisectionInstance`: instance `(graph, bound)`.
* `CslibFrontier.Complexity.encMinBisection`: binary encoding of `MinBisectionInstance`.
* `CslibFrontier.Complexity.MinBisection`: minimum bisection on simple graphs.
* `CslibFrontier.Complexity.ThreeMinBisection`: minimum bisection on 3-regular simple graphs.

## Main results

* `CslibFrontier.Complexity.MinBisection.threeMinBisection_mem_NP`: `ThreeMinBisection ∈ NP`.
* `CslibFrontier.Complexity.MinBisection_npComplete`: `NPComplete encMinBisection MinBisection`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- An instance of minimum bisection: a graph and an upper bound on the bisection width. -/
@[ext]
structure MinBisectionInstance where
  /-- The input graph, interpreted via `graph.induced` on its declared vertices. -/
  graph : Graph
  /-- Upper bound on the number of edges crossing the bisection. -/
  bound : ℕ
  deriving DecidableEq, Repr

/-- Binary encoding of `MinBisectionInstance` as `(graph, bound)`. -/
enc_structure encMinBisection : MinBisectionInstance where
  graph : encGraph, bound : encNat

attribute [fun_prop] encMinBisection_graph_polyTime encMinBisection_bound_polyTime
  encMinBisection_mk_polyTime

/-- **Minimum Bisection** on simple undirected graphs: there is a subset `S` of half the declared
vertices of `x.graph.induced` with at most `x.bound` crossing edges. -/
@[expose]
def MinBisection : Set MinBisectionInstance :=
  {x | ∃ S : Finset {v // v ∈ x.graph.vertices},
    2 * S.card = Fintype.card {v // v ∈ x.graph.vertices} ∧
      (x.graph.induced.interedges S Sᶜ).card ≤ x.bound}

/-- **3-Min-Bisection**: `MinBisection` restricted to well-formed 3-regular simple graphs on
duplicate-free declared vertex sets (every vertex of degree 3 in `graph.induced`). -/
@[expose]
def ThreeMinBisection : Set MinBisectionInstance :=
  {x | x.graph.vertices.Nodup ∧
    (∀ e ∈ x.graph.edges, e.1 ∈ x.graph.vertices ∧ e.2 ∈ x.graph.vertices) ∧
    (∀ v : {v // v ∈ x.graph.vertices}, x.graph.induced.degree v = 3) ∧
    x ∈ MinBisection}

namespace MinBisection

/-! ### NP membership of `MinBisection` and `ThreeMinBisection` -/

/-- The ordered pairs `(u, v)` of adjacent distinct declared vertices with `u ∈ S` and `v ∉ S`. -/
private def crossingPairs (G : Graph) (S : List ℕ) : List (ℕ × ℕ) :=
  (G.distinctVertices.flatMap fun u => G.distinctVertices.map fun v => (u, v)).filter
    fun p => G.adjBool p.1 p.2 && (decide (p.1 ∈ S) && !decide (p.2 ∈ S))

private theorem card_interedges_eq_crossingPairs (G : Graph) (l : List ℕ) :
    (G.induced.interedges (l.toFinset.subtype (· ∈ G.vertices))
      (l.toFinset.subtype (· ∈ G.vertices))ᶜ).card = (crossingPairs G l).length := by
  have hnd : (crossingPairs G l).Nodup :=
    (G.nodup_distinctVertices.product G.nodup_distinctVertices).filter _
  refine SimpleMaxCut.card_interedges_eq_length G l.toFinset hnd fun p => ?_
  simp only [crossingPairs, List.mem_filter, List.mem_flatMap, List.mem_map,
    Graph.mem_distinctVertices, Bool.and_eq_true, Graph.adjBool_eq_true_iff,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, List.mem_toFinset]
  constructor
  · rintro ⟨⟨u, hu, v, hv, rfl⟩, hadj, h1, h2⟩; exact ⟨hu, hv, hadj, h1, h2⟩
  · rintro ⟨hu, hv, hadj, h1, h2⟩; exact ⟨⟨p.1, hu, p.2, hv, rfl⟩, hadj, h1, h2⟩

/-- Executable verifier check for `MinBisection`. -/
private def checkBisection (p : MinBisectionInstance × List ℕ) : Bool :=
  (2 * p.2.length == p.1.graph.distinctVertices.length) &&
    decide ((crossingPairs p.1.graph p.2).length ≤ p.1.bound)

attribute [local irreducible] encMinBisection encGraph encNat encUnary in
private theorem computableInPolyTime_checkBisection :
    ComputableInPolyTime checkBisection (encPair encMinBisection (encList encNat)) encBool := by
  have h1 : ComputableInPolyTime
      (fun p : MinBisectionInstance × List ℕ =>
        2 * p.2.length == p.1.graph.distinctVertices.length)
      (encPair encMinBisection (encList encNat)) encBool := by
    have hV : ComputableInPolyTime
        (fun p : MinBisectionInstance × List ℕ => p.1.graph.distinctVertices.length)
        (encPair encMinBisection (encList encNat)) encUnary := by fun_prop
    have hL : ComputableInPolyTime (fun p : MinBisectionInstance × List ℕ => 2 * p.2.length)
        (encPair encMinBisection (encList encNat)) encUnary := by fun_prop
    exact (ComputableInPolyTime.decide_eq' hL hV).of_enc_eq fun p => by
      cases h : (2 * p.2.length == p.1.graph.distinctVertices.length) <;> simp_all
  have h2 : ComputableInPolyTime
      (fun p : MinBisectionInstance × List ℕ =>
        decide ((crossingPairs p.1.graph p.2).length ≤ p.1.bound))
      (encPair encMinBisection (encList encNat)) encBool := by
    have hcp : ComputableInPolyTime
        (fun p : MinBisectionInstance × List ℕ => (crossingPairs p.1.graph p.2).length)
        (encPair encMinBisection (encList encNat)) encNat := by
      have hu : ComputableInPolyTime
          (fun p : MinBisectionInstance × List ℕ => (crossingPairs p.1.graph p.2).length)
          (encPair encMinBisection (encList encNat)) encUnary := by
        unfold crossingPairs; fun_prop
      exact ComputableInPolyTime.unary_to_binary.comp hu
    fun_prop
  unfold checkBisection
  fun_prop

theorem card_subtype_eq_distinctVertices (G : Graph) :
    Fintype.card {v // v ∈ G.vertices} = G.distinctVertices.length := by
  rw [Graph.card_vertexSubtype, Graph.length_distinctVertices]

theorem mem_MinBisection_iff (x : MinBisectionInstance) :
    x ∈ MinBisection ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
      2 * S.card = x.graph.distinctVertices.length ∧
      (x.graph.induced.interedges (S.subtype (· ∈ x.graph.vertices))
        (S.subtype (· ∈ x.graph.vertices))ᶜ).card ≤ x.bound := by
  rw [MinBisection, Set.mem_ofPred_eq, card_subtype_eq_distinctVertices]
  constructor
  · rintro ⟨T, hcard, hcut⟩
    refine ⟨T.map (Function.Embedding.subtype _), fun v hv => ?_, ?_, ?_⟩
    · obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hv; exact u.2
    · rwa [Finset.card_map]
    · have hT' : (T.map (Function.Embedding.subtype _)).subtype (· ∈ x.graph.vertices) = T := by
        ext u; simp [u.2]
      rwa [hT']
  · rintro ⟨S, hsub, hcard, hcut⟩
    refine ⟨S.subtype (· ∈ x.graph.vertices), ?_, hcut⟩
    have hcard_eq : (S.subtype (· ∈ x.graph.vertices)).card = S.card :=
      Finset.card_bij (fun a _ => a.1) (fun a ha => Finset.mem_subtype.mp ha)
        (fun _ _ _ _ h => Subtype.ext h)
        (fun b hb => ⟨⟨b, hsub b hb⟩, Finset.mem_subtype.mpr hb, rfl⟩)
    rwa [hcard_eq]

theorem mem_NP : MinBisection ∈ NP encMinBisection := by
  have hset : MinBisection = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
      2 * S.card = x.graph.distinctVertices.length ∧
      (x.graph.induced.interedges (S.subtype (· ∈ x.graph.vertices))
        (S.subtype (· ∈ x.graph.vertices))ᶜ).card ≤ x.bound} :=
    Set.ext mem_MinBisection_iff
  rw [hset]
  exact mem_NP_of_subsetWitness (encγ := encNat) (vs := fun x => x.graph.vertices)
    (P := fun x S => 2 * S.card = x.graph.distinctVertices.length ∧
      (x.graph.induced.interedges (S.subtype (· ∈ x.graph.vertices))
        (S.subtype (· ∈ x.graph.vertices))ᶜ).card ≤ x.bound)
    (by fun_prop) computableInPolyTime_checkBisection fun x l hl _ => by
      simp only [checkBisection, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.toFinset_card_of_nodup hl, card_interedges_eq_crossingPairs]

/-- Executable check that `G` has duplicate-free vertices, valid edges, and is 3-regular. -/
private def isThreeRegularBool (G : Graph) : Bool :=
  decide G.vertices.Nodup &&
    G.edges.all (fun e => decide (e.1 ∈ G.vertices) && decide (e.2 ∈ G.vertices)) &&
    G.vertices.all (fun v => (G.vertices.filter fun u => G.adjBool v u).length == 3)

private theorem isThreeRegularBool_iff (G : Graph) :
    isThreeRegularBool G = true ↔
      G.vertices.Nodup ∧ (∀ e ∈ G.edges, e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices) ∧
        ∀ v : {v // v ∈ G.vertices}, G.induced.degree v = 3 := by
  classical
  simp only [isThreeRegularBool, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨⟨hnd, hedges⟩, hdeg⟩
    refine ⟨hnd, hedges, fun ⟨v, hv⟩ => ?_⟩
    have hdeg_eq : G.induced.degree ⟨v, hv⟩ =
      (G.vertices.filter fun u => G.adjBool v u).length := by
      rw [SimpleGraph.degree, ← List.toFinset_card_of_nodup (hnd.filter _)]
      rw [← Finset.card_map (Function.Embedding.subtype (· ∈ G.vertices))]
      congr 1; ext u
      simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Graph.induced_adj,
        Function.Embedding.coe_subtype, List.mem_toFinset, List.mem_filter,
        Graph.adjBool_eq_true_iff]
      exact ⟨fun ⟨⟨w, hw⟩, hadj, heq⟩ => ⟨heq ▸ hw, heq ▸ hadj⟩,
        fun ⟨hu, hadj⟩ => ⟨⟨u, hu⟩, hadj, rfl⟩⟩
    rw [hdeg_eq]; exact hdeg v hv
  · rintro ⟨hnd, hedges, hdeg⟩
    refine ⟨⟨hnd, hedges⟩, fun v hv => ?_⟩
    have hdeg_eq : G.induced.degree ⟨v, hv⟩ =
      (G.vertices.filter fun u => G.adjBool v u).length := by
      rw [SimpleGraph.degree, ← List.toFinset_card_of_nodup (hnd.filter _)]
      rw [← Finset.card_map (Function.Embedding.subtype (· ∈ G.vertices))]
      congr 1; ext u
      simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Graph.induced_adj,
        Function.Embedding.coe_subtype, List.mem_toFinset, List.mem_filter,
        Graph.adjBool_eq_true_iff]
      exact ⟨fun ⟨⟨w, hw⟩, hadj, heq⟩ => ⟨heq ▸ hw, heq ▸ hadj⟩,
        fun ⟨hu, hadj⟩ => ⟨⟨u, hu⟩, hadj, rfl⟩⟩
    rw [← hdeg_eq]; exact hdeg ⟨v, hv⟩

private theorem computableInPolyTime_isThreeRegularBool :
    ComputableInPolyTime isThreeRegularBool encGraph encBool := by
  have h1 : ComputableInPolyTime (fun G : Graph => decide G.vertices.Nodup) encGraph encBool :=
    ComputableInPolyTime.decide_nodup (encGraph_vertices_polyTime id')
  have h2 : ComputableInPolyTime
      (fun G : Graph => G.edges.all fun e => decide (e.1 ∈ G.vertices) && decide (e.2 ∈ G.vertices))
      encGraph encBool := by fun_prop
  have h3 : ComputableInPolyTime
      (fun G : Graph => G.vertices.all fun v => (G.vertices.filter fun u =>
        G.adjBool v u).length == 3)
      encGraph encBool := by
    refine ComputableInPolyTime.allWithInput (encGraph_vertices_polyTime id') ?_
    have hl : ComputableInPolyTime
        (fun p : Graph × ℕ => (p.1.vertices.filter fun u => p.1.adjBool p.2 u).length)
        (encPair encGraph encNat) encUnary := by fun_prop
    exact (ComputableInPolyTime.decide_eq' hl (ComputableInPolyTime.const 3)).of_enc_eq fun p => by
      cases h : ((p.1.vertices.filter fun u => p.1.adjBool p.2 u).length == 3) <;> simp_all
  unfold isThreeRegularBool
  fun_prop

theorem threeMinBisection_mem_NP : ThreeMinBisection ∈ NP encMinBisection := by
  obtain ⟨p, V, hV, hisV⟩ := mem_NP
  refine ⟨p, fun q => isThreeRegularBool q.1.graph && V q, ?_, ?_⟩
  · have hc : ComputableInPolyTime (fun q : MinBisectionInstance × List Bool =>
        isThreeRegularBool q.1.graph) (encPair encMinBisection encBits) encBool :=
      computableInPolyTime_isThreeRegularBool.comp
        (encMinBisection_graph_polyTime (ComputableInPolyTime.fst _ _))
    fun_prop
  · intro x
    simp only [ThreeMinBisection, Set.mem_ofPred_eq, Bool.and_eq_true, isThreeRegularBool_iff,
      hisV x]
    constructor
    · rintro ⟨hnd, he, hd, w, hw, hVw⟩; exact ⟨w, hw, ⟨hnd, he, hd⟩, hVw⟩
    · rintro ⟨w, hw, ⟨hnd, he, hd⟩, hVw⟩; exact ⟨hnd, he, hd, w, hw, hVw⟩

/-! ### Reduction 1: `SimpleMaxCut` → `MinBisection` -/

/-- Fixed YES-instance of `MinBisection`: 2 isolated vertices, bound 0. -/
def mbYesInstance : MinBisectionInstance := ⟨⟨[0, 1], []⟩, 0⟩

/-- Fixed NO-instance of `MinBisection`: single edge `{0, 1}`, bound 0. -/
def mbNoInstance : MinBisectionInstance := ⟨⟨[0, 1], [(0, 1)]⟩, 0⟩

private theorem mbYesInstance_mem : mbYesInstance ∈ MinBisection := by
  rw [mem_MinBisection_iff]
  refine ⟨{0}, by simp [mbYesInstance], ?_, ?_⟩
  · rw [Graph.length_distinctVertices]; simp [mbYesInstance]
  · have hzero : (mbYesInstance.graph.induced.interedges
        (({0} : Finset ℕ).subtype (· ∈ mbYesInstance.graph.vertices))
        (({0} : Finset ℕ).subtype (· ∈ mbYesInstance.graph.vertices))ᶜ) = ∅ := by
      ext ⟨a, b⟩
      simp only [Finset.notMem_empty, iff_false]
      rw [SimpleGraph.mem_interedges_iff]
      rintro ⟨_, _, hab⟩
      rw [Graph.induced_adj, Graph.toSimpleGraph_adj] at hab
      simp [mbYesInstance] at hab
    rw [hzero, Finset.card_empty]; exact Nat.zero_le _

private theorem mbNoInstance_notMem : mbNoInstance ∉ MinBisection := by
  rintro ⟨S, hcard, hcut⟩
  have h1 : S.card = 1 := by
    have hv : Fintype.card {v // v ∈ mbNoInstance.graph.vertices} = 2 := by
      rw [card_subtype_eq_distinctVertices]; decide
    omega
  obtain ⟨⟨v, hv⟩, rfl⟩ := Finset.card_eq_one.mp h1
  have h01 : v = 0 ∨ v = 1 := by simpa [mbNoInstance] using hv
  have hpos : 0 < (mbNoInstance.graph.induced.interedges {⟨v, hv⟩} {⟨v, hv⟩}ᶜ).card := by
    rw [Finset.card_pos]
    rcases h01 with rfl | rfl
    · refine ⟨(⟨0, by simp [mbNoInstance]⟩, ⟨1, by simp [mbNoInstance]⟩), ?_⟩
      rw [SimpleGraph.mem_interedges_iff]
      refine ⟨by simp, by simp [Subtype.ext_iff], ?_⟩
      simp [Graph.induced_adj, Graph.toSimpleGraph_adj, mbNoInstance]
    · refine ⟨(⟨1, by simp [mbNoInstance]⟩, ⟨0, by simp [mbNoInstance]⟩), ?_⟩
      rw [SimpleGraph.mem_interedges_iff]
      refine ⟨by simp, by simp [Subtype.ext_iff], ?_⟩
      simp [Graph.induced_adj, Graph.toSimpleGraph_adj, mbNoInstance]
  change (mbNoInstance.graph.induced.interedges {⟨v, hv⟩} {⟨v, hv⟩}ᶜ).card ≤ 0 at hcut
  omega

/-- Build the complement of `G ⊔ I_n` on `List.range (2 * n)`. -/
def complementPadded (G : Graph) : Graph :=
  let V := G.distinctVertices
  let n := V.length
  let edges := (List.range (2 * n)).flatMap fun i =>
    ((List.range (2 * n)).filter fun j =>
      decide (i < j) &&
        !(decide (i < n) && decide (j < n) && G.adjBool (V.getD i 0) (V.getD j 0))).map
      fun j => (i, j)
  ⟨List.range (2 * n), edges⟩

/-- Reduction from `SimpleMaxCut` to `MinBisection`. -/
def fromSimpleMaxCut (x : SimpleMaxCutInstance) : MinBisectionInstance :=
  let n := x.graph.distinctVertices.length
  if n == 0 then
    if x.bound == 0 then mbYesInstance else mbNoInstance
  else if decide (x.bound ≤ n * n) then
    ⟨complementPadded x.graph, n * n - x.bound⟩
  else
    mbNoInstance

private theorem complementPadded_adj_iff (G : Graph) {i j : ℕ}
    (hi : i < 2 * G.distinctVertices.length) (hj : j < 2 * G.distinctVertices.length) :
    (complementPadded G).toSimpleGraph.Adj i j ↔
      i ≠ j ∧ ¬ (i < G.distinctVertices.length ∧ j < G.distinctVertices.length ∧
        G.toSimpleGraph.Adj (G.distinctVertices.getD i 0) (G.distinctVertices.getD j 0)) := by
  set V := G.distinctVertices
  set n := V.length
  rw [Graph.toSimpleGraph_adj]
  have hmem : ∀ a b, (a, b) ∈ (complementPadded G).edges ↔
      a < 2 * n ∧ b < 2 * n ∧ a < b ∧
        ¬ (a < n ∧ b < n ∧ G.toSimpleGraph.Adj (V.getD a 0) (V.getD b 0)) := by
    intro a b
    simp only [complementPadded, List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, Prod.mk.injEq]
    constructor
    · rintro ⟨a', ha', b', ⟨hb', hab, hna⟩, rfl, rfl⟩
      refine ⟨ha', hb', hab, fun ⟨h1, h2, h3⟩ => ?_⟩
      rcases hna with (h | h) | h
      · exact h h1
      · exact h h2
      · rw [(Graph.adjBool_eq_true_iff _ _ _).mpr h3] at h; exact Bool.false_ne_true h.symm
    · rintro ⟨ha, hb, hab, hna⟩
      refine ⟨a, ha, b, ⟨hb, hab, ?_⟩, rfl, rfl⟩
      by_cases h1 : a < n
      · by_cases h2 : b < n
        · right
          cases hB : G.adjBool (V.getD a 0) (V.getD b 0) with
          | false => rfl
          | true => exact absurd ⟨h1, h2, (Graph.adjBool_eq_true_iff _ _ _).mp hB⟩ hna
        · left; right; exact h2
      · left; left; exact h1
  rw [hmem, hmem]
  constructor
  · rintro ⟨hne, ⟨_, _, _, hna⟩ | ⟨_, _, _, hna⟩⟩
    · exact ⟨hne, hna⟩
    · exact ⟨hne, fun ⟨h1, h2, h3⟩ => hna ⟨h2, h1, h3.symm⟩⟩
  · rintro ⟨hne, hna⟩
    refine ⟨hne, ?_⟩
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hi, hj, hlt, hna⟩
    · exact Or.inr ⟨hj, hi, hgt, fun ⟨h1, h2, h3⟩ => hna ⟨h2, h1, h3.symm⟩⟩

private theorem complementPadded_cut_add (G : Graph) (S' : Finset ℕ)
    (hS'sub : ∀ i ∈ S', i < 2 * G.distinctVertices.length)
    (hS'card : S'.card = G.distinctVertices.length) :
    let V := G.distinctVertices
    let n := V.length
    let S := (S'.filter (· < n)).image (fun i => V.getD i 0)
    ((complementPadded G).induced.interedges
        (S'.subtype (· ∈ (complementPadded G).vertices))
        (S'.subtype (· ∈ (complementPadded G).vertices))ᶜ).card +
      (G.induced.interedges (S.subtype (· ∈ G.vertices))
        (S.subtype (· ∈ G.vertices))ᶜ).card = n * n := by
  classical
  set V := G.distinctVertices
  set n := V.length
  set S := (S'.filter (· < n)).image (fun i => V.getD i 0)
  have hV_nd : V.Nodup := Graph.nodup_distinctVertices G
  have hV_mem : ∀ v, v ∈ V ↔ v ∈ G.vertices := fun _ => Graph.mem_distinctVertices
  have hV_inj : ∀ {i j}, i < n → j < n → V.getD i 0 = V.getD j 0 → i = j := fun {i j} hi hj h => by
    have h1 : V[i] = V[j] := by
      rw [List.getD_eq_getElem _ 0 hi, List.getD_eq_getElem _ 0 hj] at h; exact h
    exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hV_nd) (a₁ := ⟨i, hi⟩) (a₂ :=
      ⟨j, hj⟩) h1)
  have hS_iff : ∀ i < n, V.getD i 0 ∈ S ↔ i ∈ S' := by
    intro i hi
    simp only [S, Finset.mem_image, Finset.mem_filter]
    exact ⟨fun ⟨j, ⟨hjS, hjn⟩, hjeq⟩ => hV_inj hjn hi hjeq ▸ hjS,
      fun hiS => ⟨i, ⟨hiS, hi⟩, rfl⟩⟩
  set P := S' ×ˢ ((Finset.range (2 * n)) \ S')
  have hP_card : P.card = n * n := by
    rw [Finset.card_product,
      Finset.card_sdiff_of_subset (fun i hi => Finset.mem_range.mpr (hS'sub i hi)),
      Finset.card_range, hS'card]
    have : 2 * n - n = n := by omega
    rw [this]
  have hP_part : (P.filter fun p => (complementPadded G).toSimpleGraph.Adj p.1 p.2).card +
      (P.filter fun p => ¬ (complementPadded G).toSimpleGraph.Adj p.1 p.2).card = P.card :=
    Finset.card_filter_add_card_filter_not _
  -- Part 1: crossing pairs in complementPadded G
  have hpart1 : ((complementPadded G).induced.interedges
      (S'.subtype (· ∈ (complementPadded G).vertices))
      (S'.subtype (· ∈ (complementPadded G).vertices))ᶜ).card =
      (P.filter fun p => (complementPadded G).toSimpleGraph.Adj p.1 p.2).card := by
    rw [← Finset.card_map ((Function.Embedding.subtype (· ∈ (complementPadded G).vertices)).prodMap
      (Function.Embedding.subtype (· ∈ (complementPadded G).vertices)))]
    congr 1; ext ⟨i, j⟩
    simp only [Finset.mem_map, SimpleGraph.mem_interedges_iff, Finset.mem_compl, Finset.mem_subtype,
      Graph.induced_adj, Function.Embedding.coe_prodMap, Function.Embedding.coe_subtype,
      Prod.exists, Prod.map_apply, Prod.mk.injEq, Finset.mem_filter, P, Finset.mem_product,
      Finset.mem_sdiff, Finset.mem_range]
    constructor
    · rintro ⟨a, b, ⟨ha, hb, hab⟩, rfl, rfl⟩
      have hb_lt : b.1 < 2 * n := List.mem_range.mp b.2
      exact ⟨⟨ha, hb_lt, hb⟩, hab⟩
    · rintro ⟨⟨hiS, hjR, hjS⟩, hij⟩
      exact ⟨⟨i, List.mem_range.mpr (hS'sub i hiS)⟩, ⟨j, List.mem_range.mpr hjR⟩, ⟨hiS, hjS, hij⟩,
        rfl, rfl⟩
  -- Part 2: non-crossing pairs in P biject with crossing pairs of G
  have hpart2 : (G.induced.interedges (S.subtype (· ∈ G.vertices))
      (S.subtype (· ∈ G.vertices))ᶜ).card =
      (P.filter fun p => ¬ (complementPadded G).toSimpleGraph.Adj p.1 p.2).card := by
    let f : ℕ × ℕ → ℕ × ℕ := fun p => (V.getD p.1 0, V.getD p.2 0)
    have hbij : (P.filter fun p => ¬ (complementPadded G).toSimpleGraph.Adj p.1 p.2).image f =
        (G.induced.interedges (S.subtype (· ∈ G.vertices))
          (S.subtype (· ∈ G.vertices))ᶜ).map
          ((Function.Embedding.subtype (· ∈ G.vertices)).prodMap
            (Function.Embedding.subtype (· ∈ G.vertices))) := by
      ext ⟨u, v⟩
      simp only [Finset.mem_image, Finset.mem_filter, P, Finset.mem_product, Finset.mem_sdiff,
        Finset.mem_range, f, Finset.mem_map, SimpleGraph.mem_interedges_iff, Finset.mem_compl,
        Finset.mem_subtype, Graph.induced_adj, Function.Embedding.coe_prodMap,
        Function.Embedding.coe_subtype, Prod.exists, Prod.map_apply, Prod.mk.injEq]
      constructor
      · rintro ⟨i, j, ⟨⟨hiS, hjR, hjS⟩, hna⟩, rfl, rfl⟩
        have hiR : i < 2 * n := hS'sub i hiS
        rw [complementPadded_adj_iff G hiR hjR] at hna
        have hne : i ≠ j := fun h => hjS (h ▸ hiS)
        push Not at hna
        obtain ⟨hin, hjn, hadj⟩ := hna hne
        have huG : V.getD i 0 ∈ G.vertices := by
          rw [← hV_mem, List.getD_eq_getElem _ 0 hin]; exact List.getElem_mem hin
        have hvG : V.getD j 0 ∈ G.vertices := by
          rw [← hV_mem, List.getD_eq_getElem _ 0 hjn]; exact List.getElem_mem hjn
        exact ⟨⟨V.getD i 0, huG⟩, ⟨V.getD j 0, hvG⟩,
          ⟨(hS_iff i hin).mpr hiS, fun h => hjS ((hS_iff j hjn).mp h), hadj⟩, rfl, rfl⟩
      · rintro ⟨⟨u', hu'⟩, ⟨v', hv'⟩, ⟨huS, hvS, hadj⟩, rfl, rfl⟩
        obtain ⟨i, hi, hgi'⟩ := List.mem_iff_getElem.mp ((hV_mem u').mpr hu')
        obtain ⟨j, hj, hgj'⟩ := List.mem_iff_getElem.mp ((hV_mem v').mpr hv')
        have hgi : V.getD i 0 = u' := (List.getD_eq_getElem _ 0 hi).trans hgi'
        have hgj : V.getD j 0 = v' := (List.getD_eq_getElem _ 0 hj).trans hgj'
        dsimp only at huS hvS hadj
        rw [← hgi] at huS hadj; rw [← hgj] at hvS hadj
        refine ⟨i, j, ⟨⟨(hS_iff i hi).mp huS, by omega, fun hjS => hvS ((hS_iff j hj).mpr hjS)⟩,
          ?_⟩,
          hgi, hgj⟩
        have hi2 : i < 2 * G.distinctVertices.length := by change i < 2 * n; omega
        have hj2 : j < 2 * G.distinctVertices.length := by change j < 2 * n; omega
        rw [complementPadded_adj_iff G hi2 hj2]
        intro h; exact h.2 ⟨hi, hj, hadj⟩
    have hinj : Set.InjOn f ↑(P.filter fun p => ¬ (complementPadded G).toSimpleGraph.Adj p.1 p.2)
      := by
      rintro ⟨i1, j1⟩ h1 ⟨i2, j2⟩ h2 hfeq
      simp only [Finset.mem_coe, Finset.mem_filter, P, Finset.mem_product, Finset.mem_sdiff,
        Finset.mem_range] at h1 h2
      have hne1 : i1 ≠ j1 := fun h => h1.1.2.2 (h ▸ h1.1.1)
      have hne2 : i2 ≠ j2 := fun h => h2.1.2.2 (h ▸ h2.1.1)
      have hna1 := h1.2; rw [complementPadded_adj_iff G (hS'sub i1 h1.1.1) h1.1.2.1] at hna1
      have hna2 := h2.2; rw [complementPadded_adj_iff G (hS'sub i2 h2.1.1) h2.1.2.1] at hna2
      push Not at hna1 hna2
      obtain ⟨hi1, hj1, _⟩ := hna1 hne1
      obtain ⟨hi2, hj2, _⟩ := hna2 hne2
      obtain ⟨hfi, hfj⟩ := Prod.mk.inj hfeq
      exact Prod.ext (hV_inj hi1 hi2 hfi) (hV_inj hj1 hj2 hfj)
    rw [← Finset.card_map ((Function.Embedding.subtype (· ∈ G.vertices)).prodMap
        (Function.Embedding.subtype (· ∈ G.vertices))), ← hbij, Finset.card_image_of_injOn hinj]
  dsimp only
  rw [hpart1, hpart2, hP_part, hP_card]

theorem fromSimpleMaxCut_mem_iff (x : SimpleMaxCutInstance) :
    fromSimpleMaxCut x ∈ MinBisection ↔ x ∈ SimpleMaxCut := by
  classical
  set V := x.graph.distinctVertices
  set n := V.length
  by_cases hn0 : n = 0
  · have hVempty : ∀ v : {v // v ∈ x.graph.vertices}, False := fun ⟨v, hv⟩ => by
      have : v ∈ V := Graph.mem_distinctVertices.mpr hv
      rw [List.eq_nil_of_length_eq_zero hn0] at this; simp at this
    by_cases hb0 : x.bound = 0
    · have hred : fromSimpleMaxCut x = mbYesInstance := by
        simp only [fromSimpleMaxCut]; change (if (n == 0) = true then _ else _) = _
        simp [hn0, hb0]
      rw [hred]
      refine ⟨fun _ => ⟨∅, by simp [hb0]⟩, fun _ => mbYesInstance_mem⟩
    · have hred : fromSimpleMaxCut x = mbNoInstance := by
        simp only [fromSimpleMaxCut]; change (if (n == 0) = true then _ else _) = _
        simp [hn0, hb0]
      rw [hred]
      refine ⟨fun h => absurd h mbNoInstance_notMem, ?_⟩
      rintro ⟨S, hS⟩
      have hSe : S = ∅ := by ext v; exact False.elim (hVempty v)
      rw [hSe] at hS; simp [SimpleGraph.interedges] at hS; omega
  · have hnb : (n == 0) = false := beq_false_of_ne hn0
    by_cases hle : x.bound ≤ n * n
    · have hred : fromSimpleMaxCut x = ⟨complementPadded x.graph, n * n - x.bound⟩ := by
        simp only [fromSimpleMaxCut]
        change (if (n == 0) = true then _ else if decide (x.bound ≤ n * n) = true then _ else _) = _
        simp only [hnb, Bool.false_eq_true, ↓reduceIte, hle, decide_true]
        rfl
      rw [hred]
      constructor
      · intro h
        obtain ⟨S', hS'sub, hS'card, hS'cut⟩ := (mem_MinBisection_iff _).mp h
        dsimp only at hS'sub hS'card hS'cut
        have hS'lt : ∀ i ∈ S', i < 2 * n := fun i hi => by
          have : i ∈ List.range (2 * n) := hS'sub i hi
          exact List.mem_range.mp this
        have hS'n : S'.card = n := by
          have hlen : (complementPadded x.graph).distinctVertices.length = 2 * n := by
            rw [Graph.length_distinctVertices]
            have hv : (complementPadded x.graph).vertices = List.range (2 * n) := rfl
            rw [hv, List.toFinset_card_of_nodup List.nodup_range, List.length_range]
          omega
        have hadd := complementPadded_cut_add x.graph S' hS'lt hS'n
        dsimp only at hadd
        have hcut : x.bound ≤ (x.graph.induced.interedges
            (((S'.filter (· < n)).image (fun i => V.getD i 0)).subtype (· ∈ x.graph.vertices))
            (((S'.filter (· < n)).image (fun i =>
              V.getD i 0)).subtype (· ∈ x.graph.vertices))ᶜ).card := by
          dsimp only [V, n] at hadd hS'cut hle ⊢; omega
        exact ⟨_, hcut⟩
      · intro h
        obtain ⟨S, hSsub, hScut⟩ := SimpleMaxCut.mem_SimpleMaxCut_iff.mp h
        let I := (Finset.range n).filter fun i => V.getD i 0 ∈ S
        have hI_card : I.card = S.card := by
          have hV_nd : V.Nodup := Graph.nodup_distinctVertices x.graph
          have hbij : I.image (fun i => V.getD i 0) = S := by
            ext v
            simp only [I, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
            constructor
            · rintro ⟨i, ⟨_, hiS⟩, rfl⟩; exact hiS
            · intro hvS
              have hvV : v ∈ V := Graph.mem_distinctVertices.mpr (hSsub v hvS)
              obtain ⟨i, hi, hgi'⟩ := List.mem_iff_getElem.mp hvV
              have hgi : V.getD i 0 = v := (List.getD_eq_getElem _ 0 hi).trans hgi'
              exact ⟨i, ⟨hi, hgi.symm ▸ hvS⟩, hgi⟩
          have hinj : Set.InjOn (fun i => V.getD i 0) ↑I := fun i hi j hj heq => by
            have hi' : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
            have hj' : j < n := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
            have h1 : V[i] = V[j] := by
              rw [← List.getD_eq_getElem _ 0 hi', ← List.getD_eq_getElem _ 0 hj']; exact heq
            exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hV_nd)
              (a₁ := ⟨i, hi'⟩) (a₂ := ⟨j, hj'⟩) h1)
          rw [← hbij, Finset.card_image_of_injOn hinj]
        have hS_le : S.card ≤ n := by
          have := Finset.card_le_card (Finset.filter_subset (fun i =>
            V.getD i 0 ∈ S) (Finset.range n))
          rw [Finset.card_range] at this
          dsimp only [I] at hI_card; omega
        let pad := (Finset.range (n - I.card)).image (· + n)
        let S' := I ∪ pad
        have hdisj : Disjoint I pad := by
          rw [Finset.disjoint_left]
          intro i hi hpad
          have hi' : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
          obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hpad
          omega
        have hS'sub : ∀ i ∈ S', i < 2 * n := by
          intro i hi
          rcases Finset.mem_union.mp hi with hiI | hiP
          · have := Finset.mem_range.mp (Finset.mem_filter.mp hiI).1; omega
          · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hiP
            rw [Finset.mem_range] at hr; omega
        have hS'card : S'.card = n := by
          rw [Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective _ (add_left_injective n), Finset.card_range]
          omega
        have hS'_filt : S'.filter (· < n) = I := by
          ext i
          simp only [S', Finset.mem_filter, Finset.mem_union, pad, Finset.mem_image,
            Finset.mem_range]
          constructor
          · rintro ⟨hiI | ⟨r, _, rfl⟩, hlt⟩
            · exact hiI
            · omega
          · intro hiI; exact ⟨Or.inl hiI, Finset.mem_range.mp (Finset.mem_filter.mp hiI).1⟩
        have hS_eq : (S'.filter (· < n)).image (fun i => V.getD i 0) = S := by
          rw [hS'_filt]
          ext v; simp only [I, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨i, ⟨_, hiS⟩, rfl⟩; exact hiS
          · intro hvS
            obtain ⟨i, hi, hgi'⟩ := List.mem_iff_getElem.mp
              (Graph.mem_distinctVertices.mpr (hSsub v hvS))
            have hgi : V.getD i 0 = v := (List.getD_eq_getElem _ 0 hi).trans hgi'
            exact ⟨i, ⟨hi, hgi.symm ▸ hvS⟩, hgi⟩
        have hadd := complementPadded_cut_add x.graph S' hS'sub hS'card
        dsimp only at hadd
        rw [hS_eq] at hadd
        rw [mem_MinBisection_iff]
        dsimp only
        refine ⟨S', fun i hi => List.mem_range.mpr (hS'sub i hi), ?_, by
          dsimp only [V, n] at hadd hle ⊢; omega⟩
        have hlen : (complementPadded x.graph).distinctVertices.length = 2 * n := by
          rw [Graph.length_distinctVertices]
          have hv : (complementPadded x.graph).vertices = List.range (2 * n) := rfl
          rw [hv, List.toFinset_card_of_nodup List.nodup_range, List.length_range]
        omega
    · have hred : fromSimpleMaxCut x = mbNoInstance := by
        simp only [fromSimpleMaxCut]
        change (if (n == 0) = true then _ else if decide (x.bound ≤ n * n) = true then _ else _) = _
        simp [hnb, hle]
      rw [hred]
      refine ⟨fun h => absurd h mbNoInstance_notMem, ?_⟩
      rintro ⟨S, hScut⟩
      have hcard_all : (x.graph.induced.interedges S Sᶜ).card ≤ n * n := by
        have hsub : x.graph.induced.interedges S Sᶜ ⊆ Finset.univ ×ˢ Finset.univ :=
          fun _ _ => by simp
        have := Finset.card_le_card hsub
        rw [Finset.card_product, Finset.card_univ, card_subtype_eq_distinctVertices] at this
        exact this
      omega

attribute [local irreducible] encMinBisection encSimpleMaxCut encGraph encNat encUnary in
theorem computableInPolyTime_fromSimpleMaxCut :
    ComputableInPolyTime fromSimpleMaxCut encSimpleMaxCut encMinBisection := by
  have hcomp : ComputableInPolyTime complementPadded encGraph encGraph := by
    have hV : ComputableInPolyTime Graph.distinctVertices encGraph (encList encNat) :=
      Graph.computableInPolyTime_distinctVertices
    have h2n_u : ComputableInPolyTime (fun G : Graph => 2 * G.distinctVertices.length)
        encGraph encUnary := by fun_prop
    have hrange : ComputableInPolyTime (fun G : Graph => List.range (2 * G.distinctVertices.length))
        encGraph (encList encNat) := by
      have hr : ComputableInPolyTime (fun G : Graph => List.range (2 * G.distinctVertices.length))
          encGraph (encList encUnary) := by fun_prop
      exact ((ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp hr).of_enc_eq
        fun _ => by simp only [Function.comp_apply, List.map_id']
    have hedges : ComputableInPolyTime (fun G : Graph => (complementPadded G).edges)
        encGraph (encList (encPair encNat encNat)) := by
      dsimp only [complementPadded]
      have hstep : ComputableInPolyTime
          (fun p : Graph × ℕ =>
            ((List.range (2 * p.1.distinctVertices.length)).filter fun j =>
              decide (p.2 < j) &&
                !(decide (p.2 < p.1.distinctVertices.length) &&
                  decide (j < p.1.distinctVertices.length) &&
                  p.1.adjBool (p.1.distinctVertices.getD p.2 0)
                    (p.1.distinctVertices.getD j 0))).map
              fun j => (p.2, j))
          (encPair encGraph encNat) (encList (encPair encNat encNat)) := by
        have hget : ComputableInPolyTime
            (fun q : (Graph × ℕ) × ℕ => q.1.1.distinctVertices.getD q.2 0)
            (encPair (encPair encGraph encNat) encNat) encNat :=
          ComputableInPolyTime.listGetD_binary (d := 0)
            (Graph.computableInPolyTime_distinctVertices.comp
              ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))
            (ComputableInPolyTime.snd _ _)
        have hget1 : ComputableInPolyTime
            (fun q : (Graph × ℕ) × ℕ => q.1.1.distinctVertices.getD q.1.2 0)
            (encPair (encPair encGraph encNat) encNat) encNat :=
          ComputableInPolyTime.listGetD_binary (d := 0)
            (Graph.computableInPolyTime_distinctVertices.comp
              ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))
            ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
        have hn_b : ComputableInPolyTime
            (fun q : (Graph × ℕ) × ℕ => q.1.1.distinctVertices.length)
            (encPair (encPair encGraph encNat) encNat) encNat :=
          ComputableInPolyTime.unary_to_binary.comp (by
            have : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ => q.1.1.distinctVertices.length)
                (encPair (encPair encGraph encNat) encNat) encUnary := by fun_prop
            exact this)
        have hadj : ComputableInPolyTime
            (fun q : (Graph × ℕ) × ℕ =>
              q.1.1.adjBool (q.1.1.distinctVertices.getD q.1.2 0)
                (q.1.1.distinctVertices.getD q.2 0))
            (encPair (encPair encGraph encNat) encNat) encBool :=
          Graph.computableInPolyTime_adjBool_comp (by fun_prop) hget1 hget
        have hfilt : ComputableInPolyTime
            (fun p : Graph × ℕ =>
              (List.range (2 * p.1.distinctVertices.length)).filter fun j =>
                decide (p.2 < j) &&
                  !(decide (p.2 < p.1.distinctVertices.length) &&
                    decide (j < p.1.distinctVertices.length) &&
                    p.1.adjBool (p.1.distinctVertices.getD p.2 0) (p.1.distinctVertices.getD j 0)))
            (encPair encGraph encNat) (encList encNat) :=
          ComputableInPolyTime.filterWithInput (hrange.comp (ComputableInPolyTime.fst _ _))
            (by fun_prop)
        exact ComputableInPolyTime.mapWithInput hfilt (by fun_prop)
      exact ComputableInPolyTime.flatMapWithInput hrange hstep
    unfold complementPadded
    exact encGraph_mk_polyTime hrange hedges
  have hn_u : ComputableInPolyTime (fun x : SimpleMaxCutInstance => x.graph.distinctVertices.length)
      encSimpleMaxCut encUnary := by fun_prop
  have hn_b : ComputableInPolyTime (fun x : SimpleMaxCutInstance => x.graph.distinctVertices.length)
      encSimpleMaxCut encNat := ComputableInPolyTime.unary_to_binary.comp hn_u
  have hmain : ComputableInPolyTime
      (fun x : SimpleMaxCutInstance =>
        (⟨complementPadded x.graph,
          x.graph.distinctVertices.length * x.graph.distinctVertices.length -
          x.bound⟩ : MinBisectionInstance))
      encSimpleMaxCut encMinBisection :=
    encMinBisection_mk_polyTime (hcomp.comp (encSimpleMaxCut_graph_polyTime id')) (by fun_prop)
  unfold fromSimpleMaxCut
  fun_prop

theorem polyTimeReducible_SimpleMaxCut_MinBisection :
    PolyTimeReducible encSimpleMaxCut encMinBisection SimpleMaxCut MinBisection :=
  ⟨fromSimpleMaxCut, computableInPolyTime_fromSimpleMaxCut,
    fun x => (fromSimpleMaxCut_mem_iff x).symm⟩

theorem npHard : NPHard encMinBisection MinBisection :=
  SimpleMaxCut_npHard.trans polyTimeReducible_SimpleMaxCut_MinBisection

theorem npComplete : NPComplete encMinBisection MinBisection :=
  ⟨mem_NP, npHard⟩


end MinBisection

/-- Minimum Bisection is `NP`-complete. -/
theorem MinBisection_npComplete : NPComplete encMinBisection MinBisection :=
  MinBisection.npComplete

end CslibFrontier.Complexity
