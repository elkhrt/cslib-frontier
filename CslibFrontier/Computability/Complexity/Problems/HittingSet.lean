/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.SetCover
public import CslibFrontier.Computability.Complexity.Problems.VertexCover
public import CslibFrontier.Computability.PCP.Approximation.SetCover.ApproxReduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.List.GetD

/-!
# Hitting Set and Rank-Restricted $d$-Hitting Set

Finite hypergraphs (`Cslib.Complexity.HypergraphInstance`) and Hitting Set instances
(`Cslib.Complexity.HittingSetInstance`) over natural-number vertex identifiers, together with
Karp's `HittingSet` decision problem, its rank-restricted variant `DHittingSet d`
($d$-Hitting Set, $\mathrm{NP}$-complete for every $d \ge 2$), the minimization problem
`minHittingSet`, its exact cost-preserving polynomial-time duality with `minSetCover`, and its
$(1 + \ln |E(H)|)$-approximation via `SetSystem.greedyIndices`.

## Main definitions

* `Cslib.Complexity.HypergraphInstance`, `Cslib.Complexity.HittingSetInstance`,
  `Cslib.Complexity.encHypergraph`, `Cslib.Complexity.encHittingSet`: finite hypergraphs and
  Hitting Set instances with framed binary encodings.
* `Cslib.Complexity.HittingSet`, `Cslib.Complexity.DHittingSet`: decision problems Hitting Set
  and $d$-Hitting Set.
* `Cslib.Complexity.minHittingSet`: minimization formulation of Hitting Set.

## Main results

* `Cslib.Complexity.HittingSet_mem_NP`, `Cslib.Complexity.DHittingSet_mem_NP`: membership in
  `NP`.
* `Cslib.Complexity.DHittingSet_npComplete` ($d \ge 2$),
  `Cslib.Complexity.HittingSet_npComplete`: `NP`-completeness via `VertexCover`.
* `Cslib.Complexity.approxPreservingReducible_minSetCover_minHittingSet`: exact
  cost-preserving polynomial-time reduction from `minSetCover` to `minHittingSet`.
* `Cslib.Complexity.greedyHittingSet_feasible_and_bound`: $(1 + \ln |E(H)|)$ greedy upper bound.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Encoded Hypergraphs and Hitting Set Instances -/

/-- A finite hypergraph $H = (V(H), E(H))$ over natural-number vertex identifiers. -/
@[ext]
structure HypergraphInstance where
  /-- Declared vertices $V(H)$ of the hypergraph. -/
  vertices : List ℕ
  /-- Hyperedges $E(H)$, each represented as a list of vertex identifiers. -/
  edges : List (List ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- Framed binary encoding of `HypergraphInstance`. -/
enc_structure encHypergraph : HypergraphInstance where
  vertices : (encList encNat),
  edges : encNatSetList

attribute [fun_prop] encHypergraph_vertices_polyTime encHypergraph_edges_polyTime
  encHypergraph_mk_polyTime

/-- An instance $(H, \alpha)$ of `HittingSet`. -/
@[ext]
structure HittingSetInstance where
  /-- Input hypergraph $H$. -/
  hypergraph : HypergraphInstance
  /-- Maximum allowed hitting-set size $\alpha$. -/
  bound : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Framed binary encoding of `HittingSetInstance`. -/
enc_structure encHittingSet : HittingSetInstance where
  hypergraph : encHypergraph,
  bound : encNat

attribute [fun_prop] encHittingSet_hypergraph_polyTime encHittingSet_bound_polyTime
  encHittingSet_mk_polyTime

namespace HypergraphInstance

/-- Distinct declared vertices of `H` in order of first occurrence. -/
def distinctVertices (H : HypergraphInstance) : List ℕ :=
  selectDistinct H.vertices (List.replicate H.vertices.length true)

theorem mem_distinctVertices {H : HypergraphInstance} {v : ℕ} :
    v ∈ H.distinctVertices ↔ v ∈ H.vertices :=
  mem_selectDistinct_replicate

theorem nodup_distinctVertices (H : HypergraphInstance) : H.distinctVertices.Nodup :=
  nodup_selectDistinct _ _

theorem length_distinctVertices (H : HypergraphInstance) :
    H.distinctVertices.length = H.vertices.toFinset.card :=
  length_selectDistinct_replicate H.vertices

@[fun_prop]
theorem computableInPolyTime_distinctVertices :
    ComputableInPolyTime distinctVertices encHypergraph (encList encNat) := by
  unfold distinctVertices
  fun_prop

/-- Distinct declared vertices belonging to a hyperedge list `e`. -/
def cleanEdge (H : HypergraphInstance) (e : List ℕ) : List ℕ :=
  H.distinctVertices.filter fun v => decide (v ∈ e)

theorem length_cleanEdge_le_distinctVertices (H : HypergraphInstance) (e : List ℕ) :
    (H.cleanEdge e).length ≤ H.distinctVertices.length :=
  List.Sublist.length_le List.filter_sublist

theorem mem_cleanEdge {H : HypergraphInstance} {e : List ℕ} {v : ℕ} :
    v ∈ H.cleanEdge e ↔ v ∈ H.vertices ∧ v ∈ e := by
  simp [cleanEdge, mem_distinctVertices]

theorem nodup_cleanEdge (H : HypergraphInstance) (e : List ℕ) :
    (H.cleanEdge e).Nodup :=
  H.nodup_distinctVertices.filter _

theorem length_cleanEdge_eq_card (H : HypergraphInstance) (e : List ℕ) :
    (H.cleanEdge e).length = (e.filter (· ∈ H.vertices)).toFinset.card := by
  rw [← List.toFinset_card_of_nodup (H.nodup_cleanEdge e)]
  congr 1
  ext v
  simp [mem_cleanEdge, and_comm]

@[fun_prop]
theorem computableInPolyTime_cleanEdge :
    ComputableInPolyTime (fun p : HypergraphInstance × List ℕ => p.1.cleanEdge p.2)
      (encPair encHypergraph (encList encNat)) (encList encNat) := by
  unfold cleanEdge
  fun_prop

/-- A subset $U \subseteq V(H)$ is a *hitting set* of `H` if $U \cap e \neq \emptyset$ for
every $e \in E(H)$. -/
@[expose] def IsHittingSet (H : HypergraphInstance) (U : Finset ℕ) : Prop :=
  (∀ v ∈ U, v ∈ H.vertices) ∧ ∀ e ∈ H.edges, ∃ v ∈ U, v ∈ e

/-- `H` admits at least one hitting set (equivalently, every hyperedge contains at least one
declared vertex). -/
@[expose] def Hittable (H : HypergraphInstance) : Prop :=
  ∃ U : Finset ℕ, H.IsHittingSet U

/-- Executable test for whether every hyperedge contains at least one declared vertex. -/
@[expose] def hittableBool (H : HypergraphInstance) : Bool :=
  H.edges.all fun e => H.vertices.any fun v => decide (v ∈ e)

theorem hittableBool_eq_true_iff (H : HypergraphInstance) :
    H.hittableBool = true ↔ H.Hittable := by
  simp only [hittableBool, List.all_eq_true, List.any_eq_true, decide_eq_true_eq, Hittable,
    IsHittingSet]
  constructor
  · intro h
    refine ⟨H.vertices.toFinset, fun v hv => List.mem_toFinset.mp hv, fun e he => ?_⟩
    obtain ⟨v, hvV, hve⟩ := h e he
    exact ⟨v, List.mem_toFinset.mpr hvV, hve⟩
  · rintro ⟨U, hUV, hhit⟩ e he
    obtain ⟨v, hvU, hve⟩ := hhit e he
    exact ⟨v, hUV v hvU, hve⟩

@[fun_prop]
theorem computableInPolyTime_hittableBool :
    ComputableInPolyTime hittableBool encHypergraph encBool := by
  unfold hittableBool
  fun_prop

/-- Executable test that a list `C` of vertex identifiers forms a hitting set of `H`. -/
@[expose] def isHittingList (H : HypergraphInstance) (C : List ℕ) : Bool :=
  C.all (fun v => decide (v ∈ H.vertices)) &&
    H.edges.all fun e => C.any fun v => decide (v ∈ e)

theorem isHittingList_eq_true_iff (H : HypergraphInstance) (C : List ℕ) :
    H.isHittingList C = true ↔ H.IsHittingSet C.toFinset := by
  simp [isHittingList, IsHittingSet]

@[fun_prop]
theorem computableInPolyTime_isHittingList :
    ComputableInPolyTime (fun p : HypergraphInstance × List ℕ => p.1.isHittingList p.2)
      (encPair encHypergraph (encList encNat)) encBool := by
  unfold isHittingList
  fun_prop

/-- `H` has *rank* at most `d` if every hyperedge contains at most `d` distinct declared
vertices. -/
@[expose] def HasRankAtMost (d : ℕ) (H : HypergraphInstance) : Prop :=
  ∀ e ∈ H.edges, (H.cleanEdge e).length ≤ d

/-- Executable test for `HasRankAtMost d`. -/
@[expose] def hasRankAtMostBool (d : ℕ) (H : HypergraphInstance) : Bool :=
  H.edges.all fun e => decide ((H.cleanEdge e).length ≤ d)

theorem hasRankAtMostBool_eq_true_iff (d : ℕ) (H : HypergraphInstance) :
    H.hasRankAtMostBool d = true ↔ H.HasRankAtMost d := by
  simp [hasRankAtMostBool, HasRankAtMost]

@[fun_prop]
theorem computableInPolyTime_hasRankAtMostBool (d : ℕ) :
    ComputableInPolyTime (hasRankAtMostBool d) encHypergraph encBool := by
  unfold hasRankAtMostBool
  refine allWithInput (by fun_prop) ?_
  have hclean : ComputableInPolyTime
      (fun p : HypergraphInstance × List ℕ => (p.1.cleanEdge p.2).length)
      (encPair encHypergraph (encList encNat)) encNat :=
    unary_to_binary.comp ((length_list encNat).comp computableInPolyTime_cleanEdge)
  exact binary_le' hclean (const d)

/-- Rank of a hypergraph, defined as the maximum size of its cleaned hyperedges (`0` if
`E(H) = ∅`). -/
def rank (H : HypergraphInstance) : ℕ :=
  (H.edges.map fun e => (H.cleanEdge e).length).foldl max 0

private theorem foldl_max_ge (l : List ℕ) (init : ℕ) :
    init ≤ l.foldl max init ∧ ∀ x ∈ l, x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact ⟨le_rfl, fun _ h => by simp at h⟩
  | cons a l ih =>
    obtain ⟨hinit, hmem⟩ := ih (max init a)
    refine ⟨le_trans (le_max_left _ _) hinit, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hxl
    · exact le_trans (le_max_right _ _) hinit
    · exact hmem x hxl

theorem hasRankAtMost_rank (H : HypergraphInstance) :
    H.HasRankAtMost H.rank := by
  intro e he
  exact (foldl_max_ge _ 0).2 _ (List.mem_map_of_mem he)

theorem hasRankAtMost_mono {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) {H : HypergraphInstance}
    (h : H.HasRankAtMost d₁) : H.HasRankAtMost d₂ :=
  fun e he => le_trans (h e he) hd

/-- Minimum cardinality of a hitting set of `H` (`0` if `¬ H.Hittable`). -/
noncomputable def optHittingSize (H : HypergraphInstance) : ℕ :=
  sInf { n : ℕ | ∃ U : Finset ℕ, H.IsHittingSet U ∧ U.card = n }

theorem optHittingSize_le {H : HypergraphInstance} {U : Finset ℕ} (hU : H.IsHittingSet U) :
    H.optHittingSize ≤ U.card :=
  Nat.sInf_le ⟨U, hU, rfl⟩

theorem exists_isHittingSet_optHittingSize {H : HypergraphInstance} (hH : H.Hittable) :
    ∃ U : Finset ℕ, H.IsHittingSet U ∧ U.card = H.optHittingSize := by
  obtain ⟨U₀, hU₀⟩ := hH
  exact Nat.sInf_mem (s := { n : ℕ | ∃ U : Finset ℕ, H.IsHittingSet U ∧ U.card = n })
    ⟨U₀.card, U₀, hU₀, rfl⟩

end HypergraphInstance

/-! ### Decision Problems `HittingSet` and `DHittingSet` and Membership in `NP` -/

/-- The `HittingSet` decision problem: pairs $(H, \alpha)$ where `H` contains a hitting set of
size at most $\alpha$. -/
@[expose] def HittingSet : Set HittingSetInstance :=
  {x | ∃ U : Finset ℕ, x.hypergraph.IsHittingSet U ∧ U.card ≤ x.bound}

/-- The $d$-`HittingSet` decision problem: instances $(H, \alpha) \in \mathrm{HittingSet}$ whose
input hypergraph has rank at most `d`. -/
@[expose] def DHittingSet (d : ℕ) : Set HittingSetInstance :=
  {x | x ∈ HittingSet ∧ x.hypergraph.HasRankAtMost d}

theorem mem_HittingSet_iff {x : HittingSetInstance} :
    x ∈ HittingSet ↔ ∃ U : Finset ℕ, x.hypergraph.IsHittingSet U ∧ U.card ≤ x.bound :=
  Iff.rfl

theorem mem_DHittingSet_iff {d : ℕ} {x : HittingSetInstance} :
    x ∈ DHittingSet d ↔
      (∃ U : Finset ℕ, x.hypergraph.IsHittingSet U ∧ U.card ≤ x.bound) ∧
        x.hypergraph.HasRankAtMost d :=
  Iff.rfl

/-- `HittingSet` belongs to `NP`. -/
theorem HittingSet_mem_NP : HittingSet ∈ NP encHittingSet := by
  let vs : HittingSetInstance → List ℕ := fun x => x.hypergraph.vertices
  let check : HittingSetInstance × List ℕ → Bool := fun y =>
    decide (y.2.length ≤ y.1.bound) && y.1.hypergraph.isHittingList y.2
  have hvs : ComputableInPolyTime vs encHittingSet (encList encNat) := by
    dsimp [vs]; fun_prop
  have hcheck : ComputableInPolyTime check
      (encPair encHittingSet (encList encNat)) encBool := by
    have hlen : ComputableInPolyTime (fun y : HittingSetInstance × List ℕ => y.2.length)
        (encPair encHittingSet (encList encNat)) encNat :=
      unary_to_binary.comp ((length_list encNat).comp (snd encHittingSet (encList encNat)))
    exact bool_and' (binary_le' hlen (by fun_prop)) (by fun_prop)
  let P : HittingSetInstance → Finset ℕ → Prop := fun x U =>
    x.hypergraph.IsHittingSet U ∧ U.card ≤ x.bound
  have hP : ∀ (x : HittingSetInstance) (l : List ℕ), l.Nodup → (∀ v ∈ l, v ∈ vs x) →
      (check (x, l) = true ↔ P x l.toFinset) := by
    intro x l hnd _
    simp [check, P, HypergraphInstance.isHittingList_eq_true_iff,
      List.toFinset_card_of_nodup hnd, and_comm]
  have hmem := mem_NP_of_subsetWitness (encγ := encNat) (P := P) hvs hcheck hP
  have hEq : HittingSet = {x | ∃ U : Finset ℕ, (∀ v ∈ U, v ∈ vs x) ∧ P x U} := by
    ext x
    simp only [HittingSet, Set.mem_ofPred_eq, P, vs]
    exact ⟨fun ⟨U, hU, hc⟩ => ⟨U, hU.1, hU, hc⟩, fun ⟨U, _, hU, hc⟩ => ⟨U, hU, hc⟩⟩
  rwa [hEq]

/-- `DHittingSet d` belongs to `NP` for every `d : ℕ`. -/
theorem DHittingSet_mem_NP (d : ℕ) : DHittingSet d ∈ NP encHittingSet := by
  let vs : HittingSetInstance → List ℕ := fun x => x.hypergraph.vertices
  let check : HittingSetInstance × List ℕ → Bool := fun y =>
    y.1.hypergraph.hasRankAtMostBool d &&
      (decide (y.2.length ≤ y.1.bound) && y.1.hypergraph.isHittingList y.2)
  have hvs : ComputableInPolyTime vs encHittingSet (encList encNat) := by
    dsimp [vs]; fun_prop
  have hcheck : ComputableInPolyTime check
      (encPair encHittingSet (encList encNat)) encBool := by
    have hlen : ComputableInPolyTime (fun y : HittingSetInstance × List ℕ => y.2.length)
        (encPair encHittingSet (encList encNat)) encNat :=
      unary_to_binary.comp ((length_list encNat).comp (snd encHittingSet (encList encNat)))
    have hrk : ComputableInPolyTime
        (fun y : HittingSetInstance × List ℕ => y.1.hypergraph.hasRankAtMostBool d)
        (encPair encHittingSet (encList encNat)) encBool :=
      (HypergraphInstance.computableInPolyTime_hasRankAtMostBool d).comp
        (encHittingSet_hypergraph_polyTime (fst encHittingSet (encList encNat)))
    exact bool_and' hrk (bool_and' (binary_le' hlen (by fun_prop)) (by fun_prop))
  let P : HittingSetInstance → Finset ℕ → Prop := fun x U =>
    x.hypergraph.HasRankAtMost d ∧ x.hypergraph.IsHittingSet U ∧ U.card ≤ x.bound
  have hP : ∀ (x : HittingSetInstance) (l : List ℕ), l.Nodup → (∀ v ∈ l, v ∈ vs x) →
      (check (x, l) = true ↔ P x l.toFinset) := by
    intro x l hnd _
    simp [check, P, HypergraphInstance.hasRankAtMostBool_eq_true_iff,
      HypergraphInstance.isHittingList_eq_true_iff, List.toFinset_card_of_nodup hnd,
      and_left_comm, and_comm]
  have hmem := mem_NP_of_subsetWitness (encγ := encNat) (P := P) hvs hcheck hP
  have hEq : DHittingSet d = {x | ∃ U : Finset ℕ, (∀ v ∈ U, v ∈ vs x) ∧ P x U} := by
    ext x
    simp only [DHittingSet, HittingSet, Set.mem_ofPred_eq, P, vs]
    exact ⟨fun ⟨⟨U, hU, hc⟩, hrk⟩ => ⟨U, hU.1, hrk, hU, hc⟩,
      fun ⟨U, _, hrk, hU, hc⟩ => ⟨⟨U, hU, hc⟩, hrk⟩⟩
  rwa [hEq]

/-! ### Reduction from `VertexCover` to `DHittingSet d` ($d \ge 2$) -/

/-- Polynomial-time reduction mapping an undirected `VertexCoverInstance` to a rank-$\le 2$
`HittingSetInstance`. -/
def vertexCoverToHittingSet (x : VertexCoverInstance) : HittingSetInstance :=
  if x.graph.distinctVertices.length < x.k then
    ⟨⟨[], [[]]⟩, 0⟩
  else
    ⟨⟨x.graph.distinctVertices,
      ((VertexCover.declaredEdges x.graph).filter fun e => decide (e.1 ≠ e.2)).map
        fun e => [e.1, e.2]⟩,
     x.k⟩

@[fun_prop]
theorem computableInPolyTime_vertexCoverToHittingSet :
    ComputableInPolyTime vertexCoverToHittingSet encVertexCoverInstance encHittingSet := by
  unfold vertexCoverToHittingSet
  have hcond : ComputableInPolyTime
      (fun x : VertexCoverInstance => decide (x.graph.distinctVertices.length < x.k))
      encVertexCoverInstance encBool :=
    binary_lt'
      (unary_to_binary.comp ((length_list encNat).comp
        (Graph.computableInPolyTime_distinctVertices.comp
          (encVertexCoverInstance_graph_polyTime id'))))
      (encVertexCoverInstance_k_polyTime id')
  simpa only [decide_eq_true_eq] using
    ComputableInPolyTime.ite hcond (const (⟨⟨[], [[]]⟩, 0⟩ : HittingSetInstance)) (by fun_prop)

theorem vertexCoverToHittingSet_hasRankAtMost {d : ℕ} (hd : 2 ≤ d) (x : VertexCoverInstance) :
    (vertexCoverToHittingSet x).hypergraph.HasRankAtMost d := by
  unfold vertexCoverToHittingSet
  split_ifs with hlt
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    simp [HypergraphInstance.cleanEdge, HypergraphInstance.distinctVertices]
  · intro e he
    simp only [List.mem_map, List.mem_filter, VertexCover.mem_declaredEdges,
      decide_eq_true_eq] at he
    obtain ⟨⟨u, v⟩, ⟨⟨_, _, _⟩, _⟩, rfl⟩ := he
    rw [HypergraphInstance.length_cleanEdge_eq_card]
    have hsub : ([u, v].filter (· ∈ x.graph.distinctVertices)).toFinset ⊆ {u, v} := by
      intro w hw
      simp only [List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      simpa using hw.1
    exact le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_insert_le u {v}) (by simp; omega))

theorem vertexCoverToHittingSet_mem_HittingSet_iff (x : VertexCoverInstance) :
    vertexCoverToHittingSet x ∈ HittingSet ↔ x ∈ VertexCover := by
  rw [mem_VertexCover_iff_exists_card_le, ← Graph.length_distinctVertices x.graph]
  unfold vertexCoverToHittingSet
  split_ifs with hlt
  · simp only [not_le.mpr hlt, false_and, iff_false]
    rintro ⟨U, hU, -⟩
    obtain ⟨v, -, hv⟩ := hU.2 [] (List.mem_singleton.mpr rfl)
    simp at hv
  · push Not at hlt
    simp only [hlt, true_and, mem_HittingSet_iff, HypergraphInstance.IsHittingSet]
    refine ⟨fun ⟨U, ⟨hUV, hhit⟩, hcard⟩ => ⟨U, ?_, ?_, hcard⟩,
      fun ⟨U, hUV, hcov, hcard⟩ => ⟨U, ⟨?_, ?_⟩, hcard⟩⟩
    · intro v hv
      exact Graph.mem_distinctVertices.mp (hUV v hv)
    · intro u hu v hv hadj
      rw [Graph.toSimpleGraph_adj] at hadj
      obtain ⟨hne, he_or⟩ := hadj
      rcases he_or with he | he
      · have hmem : [u, v] ∈
            ((VertexCover.declaredEdges x.graph).filter fun e => decide (e.1 ≠ e.2)).map
              fun e => [e.1, e.2] := by
          refine List.mem_map.mpr ⟨(u, v), List.mem_filter.mpr ⟨?_, decide_eq_true hne⟩, rfl⟩
          exact VertexCover.mem_declaredEdges.mpr ⟨he, hu, hv⟩
        obtain ⟨w, hwU, hw⟩ := hhit [u, v] hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inl hwU
        · exact Or.inr hwU
      · have hmem : [v, u] ∈
            ((VertexCover.declaredEdges x.graph).filter fun e => decide (e.1 ≠ e.2)).map
              fun e => [e.1, e.2] := by
          refine List.mem_map.mpr ⟨(v, u), List.mem_filter.mpr ⟨?_, decide_eq_true hne.symm⟩, rfl⟩
          exact VertexCover.mem_declaredEdges.mpr ⟨he, hv, hu⟩
        obtain ⟨w, hwU, hw⟩ := hhit [v, u] hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inr hwU
        · exact Or.inl hwU
    · intro v hv
      exact Graph.mem_distinctVertices.mpr (hUV v hv)
    · intro e he
      simp only [List.mem_map, List.mem_filter, VertexCover.mem_declaredEdges,
        decide_eq_true_eq] at he
      obtain ⟨⟨u, v⟩, ⟨⟨he_mem, hu, hv⟩, hne⟩, rfl⟩ := he
      have hadj : x.graph.toSimpleGraph.Adj u v :=
        Graph.toSimpleGraph_adj.mpr ⟨hne, Or.inl he_mem⟩
      rcases hcov u hu v hv hadj with huU | hvU
      · exact ⟨u, huU, by simp⟩
      · exact ⟨v, hvU, by simp⟩

theorem vertexCoverToHittingSet_mem_DHittingSet_iff {d : ℕ} (hd : 2 ≤ d)
    (x : VertexCoverInstance) :
    vertexCoverToHittingSet x ∈ DHittingSet d ↔ x ∈ VertexCover := by
  change vertexCoverToHittingSet x ∈ HittingSet ∧ _ ↔ _
  rw [vertexCoverToHittingSet_mem_HittingSet_iff]
  exact and_iff_left (vertexCoverToHittingSet_hasRankAtMost hd x)

/-- Polynomial-time many-one reduction from `VertexCover` to `DHittingSet d` for `d ≥ 2`. -/
theorem polyTimeReducible_VertexCover_DHittingSet {d : ℕ} (hd : 2 ≤ d) :
    PolyTimeReducible encVertexCoverInstance encHittingSet VertexCover (DHittingSet d) :=
  ⟨vertexCoverToHittingSet, computableInPolyTime_vertexCoverToHittingSet,
    fun x => (vertexCoverToHittingSet_mem_DHittingSet_iff hd x).symm⟩

/-- `DHittingSet d` is `NP`-hard for every `d ≥ 2`. -/
theorem DHittingSet_npHard {d : ℕ} (hd : 2 ≤ d) :
    NPHard encHittingSet (DHittingSet d) :=
  VertexCover_npHard.trans (polyTimeReducible_VertexCover_DHittingSet hd)

/-- **`DHittingSet d` is `NP`-complete** for every `d ≥ 2`. -/
theorem DHittingSet_npComplete {d : ℕ} (hd : 2 ≤ d) :
    NPComplete encHittingSet (DHittingSet d) :=
  ⟨DHittingSet_mem_NP d, DHittingSet_npHard hd⟩

/-- `HittingSet` is `NP`-hard. -/
theorem HittingSet_npHard : NPHard encHittingSet HittingSet :=
  VertexCover_npHard.trans ⟨vertexCoverToHittingSet, computableInPolyTime_vertexCoverToHittingSet,
    fun x => (vertexCoverToHittingSet_mem_HittingSet_iff x).symm⟩

/-- **`HittingSet` is `NP`-complete**. -/
theorem HittingSet_npComplete : NPComplete encHittingSet HittingSet :=
  ⟨HittingSet_mem_NP, HittingSet_npHard⟩

/-! ### Minimization Variant `minHittingSet` and Exact Duality with `minSetCover` -/

/-- Minimization problem `minHittingSet`. -/
@[expose] noncomputable def minHittingSet : MinOptProblem HypergraphInstance (List ℕ) where
  IsValid := HypergraphInstance.Hittable
  Feasible H C := H.isHittingList C = true
  cost _ C := (C.length : ℝ)
  opt H := (H.optHittingSize : ℝ)
  opt_le H C _ hC := by
    have hhit := (H.isHittingList_eq_true_iff C).mp hC
    exact_mod_cast (HypergraphInstance.optHittingSize_le hhit).trans (List.toFinset_card_le C)
  exists_opt H hH := by
    obtain ⟨U, hU, hcard⟩ := HypergraphInstance.exists_isHittingSet_optHittingSize hH
    refine ⟨U.toList, ?_, ?_⟩
    · rw [H.isHittingList_eq_true_iff, Finset.toList_toFinset]
      exact hU
    · simp [Finset.length_toList, hcard]

/-- Dual hypergraph of a `SetSystem`: candidate set indices `0, …, m - 1` become vertices and
each ground element `u ∈ S.ground` induces the hyperedge of indices `i` with `u ∈ S.sets[i]`. -/
def setSystemToHypergraph (S : SetSystem) : HypergraphInstance where
  vertices := List.range S.sets.length
  edges := S.ground.map fun u =>
    (List.range S.sets.length).filter fun i => decide (u ∈ S.sets.getD i [])

@[fun_prop]
theorem computableInPolyTime_setSystemToHypergraph :
    ComputableInPolyTime setSystemToHypergraph encSetSystem encHypergraph := by
  unfold setSystemToHypergraph
  have hrange : ComputableInPolyTime (fun S : SetSystem => List.range S.sets.length)
      encSetSystem (encList encNat) := by
    simpa only [List.map_id', Function.comp_def] using
      mapWithInput (f := fun _ i => i)
        (range.comp ((length_list (encList encNat)).comp computableInPolyTime_setSystemSets))
        (unary_to_binary.comp (snd _ _))
  refine encHypergraph_mk_polyTime hrange ?_
  refine mapWithInput computableInPolyTime_setSystemGround ?_
  refine filterWithInput (hrange.comp (fst _ _)) ?_
  have hget : ComputableInPolyTime
      (fun q : (SetSystem × ℕ) × ℕ => q.1.1.sets.getD q.2 [])
      (encPair (encPair encSetSystem encNat) encNat) (encList encNat) := by
    have heq : (fun q : (SetSystem × ℕ) × ℕ => q.1.1.sets.getD q.2 []) =
        fun q => q.1.1.sets.getD (min q.1.1.sets.length q.2) [] :=
      funext fun q => by
        rcases le_total q.1.1.sets.length q.2 with h | h <;> simp [h]
    rw [heq]
    have hsets : ComputableInPolyTime (fun q : (SetSystem × ℕ) × ℕ => q.1.1.sets)
        (encPair (encPair encSetSystem encNat) encNat) (encList (encList encNat)) := by fun_prop
    exact listGetDWithInput hsets (binary_min_unary' ((length_list _).comp hsets) (snd _ _)) []
  have hmem : ComputableInPolyTime
      (fun q : (SetSystem × ℕ) × ℕ => decide (q.1.2 ∈ q.1.1.sets.getD q.2 []))
      (encPair (encPair encSetSystem encNat) encNat) encBool := by
    have hin : ComputableInPolyTime (fun p : ℕ × List ℕ => decide (p.1 ∈ p.2))
        (encPair encNat (encList encNat)) encBool := by fun_prop
    exact hin.comp ((snd encSetSystem encNat |>.comp (fst _ _)).prod hget)
  exact hmem

theorem setSystemToHypergraph_isHittingList_iff (S : SetSystem) (I : List ℕ) :
    (setSystemToHypergraph S).isHittingList I = true ↔ S.isCoverList I = true := by
  rw [HypergraphInstance.isHittingList_eq_true_iff, SetSystem.isCoverList_eq_true_iff]
  simp only [setSystemToHypergraph, HypergraphInstance.IsHittingSet, List.mem_toFinset,
    List.mem_range, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    List.mem_filter, decide_eq_true_eq]
  refine and_congr_right fun _ => forall₂_congr fun _ _ => ?_
  constructor
  · rintro ⟨i, hiI, hi, hui⟩
    rw [List.getD_eq_getElem _ _ hi] at hui
    exact ⟨i, hiI, hi, hui⟩
  · rintro ⟨i, hiI, hi, hui⟩
    exact ⟨i, hiI, hi, by rwa [List.getD_eq_getElem _ _ hi]⟩

theorem setSystemToHypergraph_hittable_iff (S : SetSystem) :
    (setSystemToHypergraph S).Hittable ↔ S.Coverable := by
  constructor
  · rintro ⟨U, hU⟩
    have hlist : S.isCoverList U.toList = true := by
      rw [← setSystemToHypergraph_isHittingList_iff,
        HypergraphInstance.isHittingList_eq_true_iff, Finset.toList_toFinset]
      exact hU
    obtain ⟨_, hcov⟩ := (S.isCoverList_eq_true_iff _).mp hlist
    refine ⟨Finset.univ.filter fun i : Fin S.sets.length => (i : ℕ) ∈ U, fun u hu => ?_⟩
    obtain ⟨i, hiU, hi, hui⟩ := hcov u hu
    rw [Finset.mem_toList] at hiU
    exact ⟨⟨i, hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiU⟩, hui⟩
  · rintro ⟨C, hC⟩
    let I := (C.image Fin.val).toList
    have hcov : S.isCoverList I = true := by
      rw [S.isCoverList_eq_true_iff]
      refine ⟨fun i hi => ?_, fun u hu => ?_⟩
      · rw [Finset.mem_toList] at hi
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
        exact j.isLt
      · obtain ⟨j, hjC, huj⟩ := hC u hu
        exact ⟨j.val, Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨j, hjC, rfl⟩), j.isLt, huj⟩
    exact ⟨I.toFinset, ((setSystemToHypergraph S).isHittingList_eq_true_iff I).mp
      ((setSystemToHypergraph_isHittingList_iff S I).mpr hcov)⟩

theorem setSystemToHypergraph_optHittingSize_eq (S : SetSystem)
    (hS : S.Coverable) :
    (setSystemToHypergraph S).optHittingSize = S.optCoverSize := by
  have hH : (setSystemToHypergraph S).Hittable :=
    (setSystemToHypergraph_hittable_iff S).mpr hS
  apply le_antisymm
  · obtain ⟨I, hfeas, hcost⟩ := minSetCover.exists_opt S hS
    have hhit : (setSystemToHypergraph S).IsHittingSet I.toFinset :=
      ((setSystemToHypergraph S).isHittingList_eq_true_iff I).mp
        ((setSystemToHypergraph_isHittingList_iff S I).mpr hfeas)
    have hle := HypergraphInstance.optHittingSize_le hhit
    have hcard : I.toFinset.card ≤ S.optCoverSize := by
      dsimp [minSetCover] at hcost
      have hlen : I.length = S.optCoverSize := by exact_mod_cast hcost
      exact (List.toFinset_card_le I).trans_eq hlen
    exact le_trans hle hcard
  · obtain ⟨C, hfeas, hcost⟩ := minHittingSet.exists_opt (setSystemToHypergraph S) hH
    have hcov : S.isCoverList C = true :=
      (setSystemToHypergraph_isHittingList_iff S C).mp hfeas
    have hle : (S.optCoverSize : ℝ) ≤ (C.length : ℝ) := minSetCover.opt_le S C hS hcov
    dsimp [minHittingSet] at hcost
    rw [hcost] at hle
    exact_mod_cast hle

/-- **Exact approximation-preserving reduction from `minSetCover` to `minHittingSet`** with
identity ratio transformation (`g = fun _ r => r`). -/
theorem approxPreservingReducible_minSetCover_minHittingSet :
    ApproxPreservingReducible minSetCover minHittingSet
      encSetSystem encHypergraph (encList encNat) (encList encNat) (fun _ r => r) := by
  refine ⟨setSystemToHypergraph, fun _ C => C, computableInPolyTime_setSystemToHypergraph,
    snd _ _, fun S hS => (setSystemToHypergraph_hittable_iff S).mpr hS,
    fun S C _ hC => (setSystemToHypergraph_isHittingList_iff S C).mp hC,
    fun S r C hS _ hcost => ?_⟩
  simpa [minSetCover, minHittingSet, setSystemToHypergraph_optHittingSize_eq S hS] using hcost

/-- Dual `SetSystem` of a `HypergraphInstance`: hyperedge indices `0, …, m - 1` become the
ground elements and each distinct declared vertex `v` induces the set of hyperedge indices
containing `v`. -/
def hypergraphToSetSystem (H : HypergraphInstance) : SetSystem where
  ground := List.range H.edges.length
  sets := H.distinctVertices.map fun v =>
    (List.range H.edges.length).filter fun j => decide (v ∈ H.edges.getD j [])

@[fun_prop]
theorem computableInPolyTime_hypergraphToSetSystem :
    ComputableInPolyTime hypergraphToSetSystem encHypergraph encSetSystem := by
  unfold hypergraphToSetSystem
  have hrange : ComputableInPolyTime (fun H : HypergraphInstance => List.range H.edges.length)
      encHypergraph (encList encNat) := by
    have hlen : ComputableInPolyTime (fun H : HypergraphInstance => H.edges.length)
        encHypergraph encUnary :=
      (length (encList encNat)).comp (encHypergraph_edges_polyTime id')
    simpa only [List.map_id', Function.comp_def] using
      mapWithInput (f := fun _ i => i) (range.comp hlen) (unary_to_binary.comp (snd _ _))
  refine computableInPolyTime_setSystemMk hrange ?_
  refine mapWithInput HypergraphInstance.computableInPolyTime_distinctVertices ?_
  refine filterWithInput (hrange.comp (fst _ _)) ?_
  have hget : ComputableInPolyTime
      (fun q : (HypergraphInstance × ℕ) × ℕ => q.1.1.edges.getD q.2 [])
      (encPair (encPair encHypergraph encNat) encNat) (encList encNat) := by
    have heq : (fun q : (HypergraphInstance × ℕ) × ℕ => q.1.1.edges.getD q.2 []) =
        fun q => q.1.1.edges.getD (min q.1.1.edges.length q.2) [] :=
      funext fun q => by
        rcases le_total q.1.1.edges.length q.2 with h | h <;> simp [h]
    rw [heq]
    have hedges : ComputableInPolyTime (fun q : (HypergraphInstance × ℕ) × ℕ => q.1.1.edges)
        (encPair (encPair encHypergraph encNat) encNat) (encList (encList encNat)) := by fun_prop
    exact listGetDWithInput hedges (binary_min_unary' ((length_list _).comp hedges) (snd _ _)) []
  have hin : ComputableInPolyTime (fun p : ℕ × List ℕ => decide (p.1 ∈ p.2))
      (encPair encNat (encList encNat)) encBool := by fun_prop
  exact hin.comp ((snd encHypergraph encNat |>.comp (fst _ _)).prod hget)

/-- Map selected set indices `I` of `hypergraphToSetSystem H` back to vertex identifiers in
`H.distinctVertices`. -/
def liftSetCoverToHittingSet (H : HypergraphInstance) (I : List ℕ) : List ℕ :=
  I.map fun i => H.distinctVertices.getD i (H.vertices.headD 0)

theorem hypergraphToSetSystem_coverable_iff (H : HypergraphInstance) :
    (hypergraphToSetSystem H).Coverable ↔ H.Hittable := by
  rw [← SetSystem.coverableBool_eq_true_iff, ← HypergraphInstance.hittableBool_eq_true_iff]
  simp only [SetSystem.coverableBool, hypergraphToSetSystem, HypergraphInstance.hittableBool,
    List.all_eq_true, List.any_eq_true, List.mem_range, List.mem_map, exists_exists_and_eq_and,
    List.mem_filter, decide_eq_true_eq, HypergraphInstance.mem_distinctVertices]
  constructor
  · intro h e he
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
    obtain ⟨v, hvV, _, hvj⟩ := h j hj
    rw [List.getD_eq_getElem _ _ hj] at hvj
    exact ⟨v, hvV, hvj⟩
  · intro h j hj
    obtain ⟨v, hvV, hvj⟩ := h H.edges[j] (List.getElem_mem hj)
    refine ⟨v, hvV, hj, ?_⟩
    rwa [List.getD_eq_getElem _ _ hj]

theorem liftSetCoverToHittingSet_isHittingList {H : HypergraphInstance} {I : List ℕ}
    (hcov : (hypergraphToSetSystem H).isCoverList I = true) :
    H.isHittingList (liftSetCoverToHittingSet H I) = true := by
  obtain ⟨hbound, hground⟩ := ((hypergraphToSetSystem H).isCoverList_eq_true_iff I).mp hcov
  rw [HypergraphInstance.isHittingList_eq_true_iff]
  have hbound' : ∀ i ∈ I, i < H.distinctVertices.length := by
    intro i hi
    simpa [hypergraphToSetSystem] using hbound i hi
  refine ⟨fun v hv => ?_, fun e he => ?_⟩
  · rw [List.mem_toFinset, liftSetCoverToHittingSet, List.mem_map] at hv
    obtain ⟨i, hiI, rfl⟩ := hv
    rw [List.getD_eq_getElem _ _ (hbound' i hiI)]
    exact HypergraphInstance.mem_distinctVertices.mp (List.getElem_mem (hbound' i hiI))
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
    obtain ⟨i, hiI, _, hjmem⟩ := hground j (List.mem_range.mpr hj)
    have hi' : i < H.distinctVertices.length := hbound' i hiI
    simp only [hypergraphToSetSystem, List.getElem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at hjmem
    rw [List.getD_eq_getElem _ _ hj] at hjmem
    refine ⟨H.distinctVertices[i]'hi', ?_, hjmem.2⟩
    rw [List.mem_toFinset, liftSetCoverToHittingSet, List.mem_map]
    exact ⟨i, hiI, List.getD_eq_getElem _ _ hi'⟩

/-- Greedy hitting-set algorithm via `SetSystem.greedyIndices` on `hypergraphToSetSystem H`,
achieving approximation ratio $1 + \ln |E(H)|$ on every hittable hypergraph. -/
noncomputable def greedyHittingSet (H : HypergraphInstance) : List ℕ :=
  liftSetCoverToHittingSet H ((hypergraphToSetSystem H).greedyIndices.map Fin.val)

theorem greedyHittingSet_feasible_and_bound {H : HypergraphInstance} (hH : H.Hittable) :
    minHittingSet.Feasible H (greedyHittingSet H) ∧
      minHittingSet.cost H (greedyHittingSet H) ≤
        (1 + Real.log H.edges.length) * minHittingSet.opt H := by
  have hcov_sys : (hypergraphToSetSystem H).Coverable :=
    (hypergraphToSetSystem_coverable_iff H).mpr hH
  have hg_cov := SetSystem.greedyIndices_isCover hcov_sys
  let I := (hypergraphToSetSystem H).greedyIndices.map Fin.val
  have hI_cov : (hypergraphToSetSystem H).isCoverList I = true := by
    rw [(hypergraphToSetSystem H).isCoverList_eq_true_iff]
    refine ⟨fun i hi => ?_, fun u hu => ?_⟩
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
      exact j.isLt
    · obtain ⟨j, hj, huj⟩ := hg_cov u hu
      rw [List.mem_toFinset] at hj
      exact ⟨j.val, List.mem_map.mpr ⟨j, hj, rfl⟩, j.isLt, huj⟩
  have hfeas : H.isHittingList (greedyHittingSet H) = true :=
    liftSetCoverToHittingSet_isHittingList hI_cov
  refine ⟨hfeas, ?_⟩
  have hlen : (greedyHittingSet H).length = (hypergraphToSetSystem H).greedyIndices.length := by
    simp [greedyHittingSet, liftSetCoverToHittingSet]
  have hlog := SetSystem.greedyIndices_length_le_one_add_log hcov_sys
  have hcard_ground : (hypergraphToSetSystem H).ground.toFinset.card = H.edges.length := by
    simp [hypergraphToSetSystem, List.toFinset_card_of_nodup List.nodup_range]
  have hopt_le : (hypergraphToSetSystem H).optCoverSize ≤ H.optHittingSize := by
    obtain ⟨U, hU, hUcard⟩ := HypergraphInstance.exists_isHittingSet_optHittingSize hH
    let C : Finset (Fin (hypergraphToSetSystem H).sets.length) :=
      Finset.univ.filter fun i =>
        H.distinctVertices[i.1]'(by simpa [hypergraphToSetSystem] using i.isLt) ∈ U
    have hC_cov : (hypergraphToSetSystem H).IsCover C := by
      intro j hj
      rw [hypergraphToSetSystem, List.mem_range] at hj
      obtain ⟨v, hvU, hve⟩ := hU.2 H.edges[j] (List.getElem_mem hj)
      have hvD : v ∈ H.distinctVertices :=
        HypergraphInstance.mem_distinctVertices.mpr (hU.1 v hvU)
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvD
      have hi' : i < (hypergraphToSetSystem H).sets.length := by
        simpa [hypergraphToSetSystem] using hi
      refine ⟨⟨i, hi'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvU⟩, ?_⟩
      simp only [hypergraphToSetSystem, Fin.getElem_fin, List.getElem_map, List.mem_filter,
        List.mem_range, decide_eq_true_eq]
      exact ⟨hj, by rwa [List.getD_eq_getElem _ _ hj]⟩
    have hC_card : C.card ≤ U.card := by
      refine Finset.card_le_card_of_injOn
        (fun i => H.distinctVertices[i.1]'(by simpa [hypergraphToSetSystem] using i.isLt))
        (fun i hi => (Finset.mem_filter.mp hi).2) ?_
      intro i₁ _ i₂ _ heq
      exact Fin.ext ((H.nodup_distinctVertices.getElem_inj_iff).mp heq)
    exact (SetSystem.optCoverSize_le hC_cov).trans (hC_card.trans_eq hUcard)
  have h1_nonneg : 0 ≤ 1 + Real.log H.edges.length := by
    rcases Nat.eq_zero_or_pos H.edges.length with h0 | hpos
    · simp [h0]
    · have hge1 : (1 : ℝ) ≤ H.edges.length := by exact_mod_cast hpos
      linarith [Real.log_nonneg hge1]
  simp only [minHittingSet, hlen]
  rw [hcard_ground] at hlog
  exact hlog.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hopt_le) h1_nonneg)

end Cslib.Complexity
