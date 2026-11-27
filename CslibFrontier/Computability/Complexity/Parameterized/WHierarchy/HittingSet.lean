/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.WeftCertificate
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.ListsUpTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PolyTime
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

/-!
# `HittingSet` and `WS[2]` are `W[2]`-Complete

The parameterized *Hitting Set* problem (`HittingSet`) asks whether a finite hypergraph `(V, E)`
admits a hitting set `T ⊆ V` of exact cardinality `|T| = k`, parameterized by `k`. The *Weighted
2-Normalized Satisfiability* problem (`WS2`, equivalently weighted CNF satisfiability) asks whether
a conjunctive normal form Boolean formula admits a satisfying assignment of Hamming weight `k`,
parameterized by `k`.

This module establishes that both `HittingSet` and `WS2` are `W[2]`-complete on multi-tape Turing
machines:
1. `HittingSet` FPT-reduces to `WS2` (preserving `k`) by viewing each hyperedge as a positive
   clause.
2. `WS2` FPT-reduces to `WCS 2 3` via a 3-layer unbounded fan-in circuit of weft at most `2` and
   depth at most `3`, placing both `WS2` and `HittingSet` in `W[2]`.
3. For every fixed depth `d`, `WCS 2 d` FPT-reduces to `HittingSet` via weft-`2` output
   certificates (`certsSucc 1 d`), selected-position brackets (`brackets d`), and weft-`1`
   refutation hyperedges (`certsOne d` + `refutes`), proving `W[2]`-hardness of `HittingSet` and
   `WS2`.

All results are proved unconditionally under standard Lean axioms.

## Main definitions

- `CslibFrontier.ParameterizedComplexity.FinHypergraph`,
  `CslibFrontier.ParameterizedComplexity.HittingSetInstance`,
  `CslibFrontier.ParameterizedComplexity.HittingSet`: finite hypergraphs with non-empty vertex sets
  and
  the parameterized `k`-hitting-set decision problem.
- `CslibFrontier.ParameterizedComplexity.WS2Formula`,
  `CslibFrontier.ParameterizedComplexity.WS2Instance`,
  `CslibFrontier.ParameterizedComplexity.WS2`: CNF (`2`-normalized) Boolean formulas and weighted
  CNF
  satisfiability.

## Main results

- `CslibFrontier.ParameterizedComplexity.fptReducible_HittingSet_WS2`: `HittingSet ≤_FPT WS2`.
- `CslibFrontier.ParameterizedComplexity.WS2_mem_W`,
  `CslibFrontier.ParameterizedComplexity.HittingSet_mem_W`: `WS2` and `HittingSet` belong to `W[2]`.
- `CslibFrontier.ParameterizedComplexity.fptReducible_WCS_HittingSet`: `WCS 2 d ≤_FPT HittingSet`
  for
  every fixed depth `d`.
- `CslibFrontier.ParameterizedComplexity.HittingSet_wHard`,
  `CslibFrontier.ParameterizedComplexity.WS2_wHard`: `HittingSet` and `WS2` are `W[2]`-hard.
- `CslibFrontier.ParameterizedComplexity.W_two_eq_FPT_iff`: `W[2] = FPT` if and only if
  `HittingSet ∈ FPT`.

## Tags

parameterized complexity, W[2]-completeness, hitting set, weighted CNF satisfiability, hypergraph
-/

public section

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.Unbounded
open Cslib.Complexity Cslib.Complexity.WCS.ToClique Turing.MultiTapeTM

namespace CslibFrontier.ParameterizedComplexity

/-! ### Finite hypergraphs and `HittingSet` -/

/-- Concrete representation of a finite hypergraph `(V, E)` over natural-number vertex identifiers,
with at least one vertex `headVertex` so `V` is guaranteed non-empty and `enc_structure` applies
without `Prop` fields. -/
@[ext]
structure FinHypergraph where
  /-- Base vertex ensuring the vertex set is non-empty. -/
  headVertex : ℕ
  /-- Additional declared vertices. -/
  tailVertices : List ℕ
  /-- Raw hyperedge lists; vertices outside `distinctVertices` are filtered out in `edgeList`. -/
  rawEdges : List (List ℕ)
  deriving DecidableEq

/-- Canonical binary encoding of `FinHypergraph`. -/
enc_structure encFinHypergraph : FinHypergraph where
  headVertex : encNat, tailVertices : (encList encNat), rawEdges : (encList (encList encNat))

namespace FinHypergraph

/-- Deduplicated non-empty list of declared vertices of `H`. -/
@[expose] def distinctVertices (H : FinHypergraph) : List ℕ :=
  selectDistinct (H.headVertex :: H.tailVertices) (List.replicate (H.tailVertices.length + 1) true)

/-- The finite vertex set `V(H)`. -/
@[expose] def vertexSet (H : FinHypergraph) : Finset ℕ :=
  H.distinctVertices.toFinset

/-- `distinctVertices` has no duplicates. -/
theorem nodup_distinctVertices (H : FinHypergraph) : H.distinctVertices.Nodup :=
  nodup_selectDistinct _ _

/-- Membership in `distinctVertices`. -/
theorem mem_distinctVertices {H : FinHypergraph} {v : ℕ} :
    v ∈ H.distinctVertices ↔ v = H.headVertex ∨ v ∈ H.tailVertices := by
  unfold distinctVertices
  have hlen : (H.headVertex :: H.tailVertices).length = H.tailVertices.length + 1 := rfl
  rw [← hlen, mem_selectDistinct_replicate, List.mem_cons]

/-- Membership in `vertexSet`. -/
theorem mem_vertexSet {H : FinHypergraph} {v : ℕ} :
    v ∈ H.vertexSet ↔ v ∈ H.distinctVertices :=
  List.mem_toFinset

/-- `H.headVertex` always belongs to `H.vertexSet`. -/
theorem headVertex_mem_vertexSet (H : FinHypergraph) : H.headVertex ∈ H.vertexSet :=
  mem_vertexSet.2 (mem_distinctVertices.2 (Or.inl rfl))

/-- Every `FinHypergraph` has a non-empty vertex set. -/
theorem vertexSet_nonempty (H : FinHypergraph) : H.vertexSet.Nonempty :=
  ⟨H.headVertex, H.headVertex_mem_vertexSet⟩

/-- Hyperedges of `H` restricted to declared vertices in `H.distinctVertices`. -/
@[expose] def edgeList (H : FinHypergraph) : List (List ℕ) :=
  H.rawEdges.map fun e => e.filter (· ∈ H.distinctVertices)

/-- Finite family `E(H) ⊆ 𝒫(V(H))` of hyperedges of `H`. -/
@[expose] def edgeFinsets (H : FinHypergraph) : Finset (Finset ℕ) :=
  (H.edgeList.map List.toFinset).toFinset

/-- Membership in `H.edgeList`. -/
theorem mem_edgeList_iff {H : FinHypergraph} {e : List ℕ} :
    e ∈ H.edgeList ↔ ∃ r ∈ H.rawEdges, r.filter (· ∈ H.distinctVertices) = e :=
  List.mem_map

/-- When every raw hyperedge already lies inside `H.distinctVertices`, `H.edgeList = H.rawEdges`. -/
theorem edgeList_eq_rawEdges {H : FinHypergraph}
    (h : ∀ e ∈ H.rawEdges, ∀ v ∈ e, v ∈ H.distinctVertices) :
    H.edgeList = H.rawEdges := by
  rw [edgeList]
  conv_rhs => rw [← List.map_id H.rawEdges]
  exact List.map_congr_left fun e he =>
    List.filter_eq_self.2 fun v hv => decide_eq_true (h e he v hv)

/-- Membership in `H.edgeFinsets` in terms of `H.edgeList`. -/
theorem mem_edgeFinsets_iff {H : FinHypergraph} {E : Finset ℕ} :
    E ∈ H.edgeFinsets ↔ ∃ e ∈ H.edgeList, e.toFinset = E := by
  simp [edgeFinsets]

/-- Membership in `H.edgeFinsets` in terms of `H.rawEdges`. -/
theorem mem_edgeFinsets_iff_raw {H : FinHypergraph} {E : Finset ℕ} :
    E ∈ H.edgeFinsets ↔ ∃ r ∈ H.rawEdges, (r.filter (· ∈ H.distinctVertices)).toFinset = E := by
  simp [edgeFinsets, edgeList]

/-- Every hyperedge `E ∈ H.edgeFinsets` is a subset of `H.vertexSet`. -/
theorem subset_vertexSet_of_mem_edgeFinsets {H : FinHypergraph} {E : Finset ℕ}
    (hE : E ∈ H.edgeFinsets) : E ⊆ H.vertexSet := by
  simp only [edgeFinsets, edgeList, List.mem_toFinset, List.mem_map] at hE
  obtain ⟨l, ⟨r, -, rfl⟩, rfl⟩ := hE
  intro v hv
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hv
  exact mem_vertexSet.2 hv.2

/-- `T` is a hitting set (transversal) of `H` when `T ⊆ V(H)` and `T` intersects every hyperedge of
`H`. -/
@[expose] def IsHittingSet (H : FinHypergraph) (T : Finset ℕ) : Prop :=
  T ⊆ H.vertexSet ∧ ∀ E ∈ H.edgeFinsets, (T ∩ E).Nonempty

/-- Characterization of `H.IsHittingSet T`. -/
theorem isHittingSet_iff {H : FinHypergraph} {T : Finset ℕ} :
    H.IsHittingSet T ↔ T ⊆ H.vertexSet ∧ ∀ E ∈ H.edgeFinsets, (T ∩ E).Nonempty :=
  Iff.rfl

/-- `T` is an inclusion-minimal hitting set of `H` (`T ∈ Tr(H)`). -/
@[expose] def IsMinimalHittingSet (H : FinHypergraph) (T : Finset ℕ) : Prop :=
  Minimal H.IsHittingSet T

/-- Characterization of `H.IsMinimalHittingSet T`. -/
theorem isMinimalHittingSet_iff {H : FinHypergraph} {T : Finset ℕ} :
    H.IsMinimalHittingSet T ↔ Minimal H.IsHittingSet T :=
  Iff.rfl

/-- Hitting sets are upward-closed inside `V(H)`. -/
theorem IsHittingSet.mono {H : FinHypergraph} {T T' : Finset ℕ}
    (hT : H.IsHittingSet T) (hsub : T ⊆ T') (hV : T' ⊆ H.vertexSet) :
    H.IsHittingSet T' :=
  ⟨hV, fun E hE => (hT.2 E hE).mono (Finset.inter_subset_inter_right hsub)⟩

/-- Polynomial-time computability of `distinctVertices`. -/
@[fun_prop]
theorem computableInPolyTime_distinctVertices :
    ComputableInPolyTime distinctVertices encFinHypergraph (encList encNat) := by
  open scoped FinHypergraph in
  unfold distinctVertices
  fun_prop

/-- Polynomial-time computability of `edgeList`. -/
@[fun_prop]
theorem computableInPolyTime_edgeList :
    ComputableInPolyTime edgeList encFinHypergraph (encList (encList encNat)) := by
  open scoped FinHypergraph in
  unfold edgeList
  fun_prop

end FinHypergraph

/-- Parameterized `HittingSet` instance `(H, k)`. -/
@[ext]
structure HittingSetInstance where
  /-- Input hypergraph. -/
  hypergraph : FinHypergraph
  /-- Target hitting-set cardinality (and parameter). -/
  k : ℕ
  deriving DecidableEq

/-- Canonical binary encoding of `HittingSetInstance`. -/
enc_structure encHittingSetInstance : HittingSetInstance where
  hypergraph : encFinHypergraph, k : encNat

/-- **Parameterized `HittingSet`**: pairs `(H, k)` where `H` admits a hitting set `T ⊆ V(H)` of
exact cardinality `|T| = k`. -/
@[expose] def HittingSet : Set HittingSetInstance :=
  {x | ∃ T : Finset ℕ, x.hypergraph.IsHittingSet T ∧ T.card = x.k}

/-- Membership in `HittingSet`. -/
theorem mem_HittingSet {x : HittingSetInstance} :
    x ∈ HittingSet ↔ ∃ T : Finset ℕ, x.hypergraph.IsHittingSet T ∧ T.card = x.k :=
  Iff.rfl

/-- Any subset `T ⊆ V` of size `|T| ≤ k ≤ |V|` extends to a subset `T' ⊆ V` of exact size `k`. -/
theorem exists_superset_subset_card_eq {α : Type*} {T V : Finset α} {k : ℕ}
    (hTV : T ⊆ V) (hTk : T.card ≤ k) (hkV : k ≤ V.card) :
    ∃ T' : Finset α, T ⊆ T' ∧ T' ⊆ V ∧ T'.card = k := by
  classical
  have hdisj : Disjoint T (V \ T) :=
    Finset.disjoint_left.2 fun _ hxT hxV => (Finset.mem_sdiff.1 hxV).2 hxT
  have hunion : T ∪ (V \ T) = V := Finset.ext fun x => by
    simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h => h.elim (fun hx => hTV hx) And.left,
      fun hx => if hxT : x ∈ T then Or.inl hxT else Or.inr ⟨hx, hxT⟩⟩
  have hVcard : V.card = T.card + (V \ T).card := by
    conv_lhs => rw [← hunion]
    exact Finset.card_union_of_disjoint hdisj
  have hdiff : k - T.card ≤ (V \ T).card := by omega
  obtain ⟨S, hSV, hScard⟩ := Finset.exists_subset_card_eq hdiff
  refine ⟨T ∪ S, Finset.subset_union_left,
    Finset.union_subset hTV (hSV.trans fun _ hx => (Finset.mem_sdiff.1 hx).1), ?_⟩
  rw [Finset.card_union_of_disjoint (hdisj.mono_right hSV), hScard]
  omega

/-- When `k ≤ |V(H)|`, existence of a hitting set of exact size `k` is equivalent to existence of a
hitting set of size at most `k`. -/
theorem mem_HittingSet_iff_card_le {x : HittingSetInstance}
    (hk : x.k ≤ x.hypergraph.vertexSet.card) :
    x ∈ HittingSet ↔ ∃ T : Finset ℕ, x.hypergraph.IsHittingSet T ∧ T.card ≤ x.k := by
  refine ⟨fun ⟨T, hT, hcard⟩ => ⟨T, hT, hcard.le⟩, fun ⟨T, hT, hle⟩ => ?_⟩
  obtain ⟨T', hTT', hT'V, hcard'⟩ := exists_superset_subset_card_eq hT.1 hle hk
  exact ⟨T', hT.mono hTT' hT'V, hcard'⟩

/-! ### `WS2` (Weighted 2-Normalized / CNF Satisfiability) -/

/-- Concrete CNF (`2`-normalized) Boolean formula with non-empty variable set `headVar :: tailVars`
and disjunctive clauses of `(variable, polarity)` literals. -/
@[ext]
structure WS2Formula where
  /-- Base variable identifier ensuring `varSet` is non-empty. -/
  headVar : ℕ
  /-- Additional declared variable identifiers. -/
  tailVars : List ℕ
  /-- List of disjunctive clauses; each literal `(v, b)` asserts `x_v = b`. -/
  clauses : List (List (ℕ × Bool))
  deriving DecidableEq

/-- Canonical binary encoding of `WS2Formula`. -/
enc_structure encWS2Formula : WS2Formula where
  headVar : encNat, tailVars : (encList encNat),
  clauses : (encList (encList (encPair encNat encBool)))

namespace WS2Formula

/-- Deduplicated non-empty list of declared variables of `F`. -/
@[expose] def distinctVars (F : WS2Formula) : List ℕ :=
  selectDistinct (F.headVar :: F.tailVars) (List.replicate (F.tailVars.length + 1) true)

/-- The finite variable set `var(F)`. -/
@[expose] def varSet (F : WS2Formula) : Finset ℕ :=
  F.distinctVars.toFinset

/-- `distinctVars` has no duplicates. -/
theorem nodup_distinctVars (F : WS2Formula) : F.distinctVars.Nodup :=
  nodup_selectDistinct _ _

/-- Membership in `distinctVars`. -/
theorem mem_distinctVars {F : WS2Formula} {v : ℕ} :
    v ∈ F.distinctVars ↔ v = F.headVar ∨ v ∈ F.tailVars := by
  unfold distinctVars
  have hlen : (F.headVar :: F.tailVars).length = F.tailVars.length + 1 := rfl
  rw [← hlen, mem_selectDistinct_replicate, List.mem_cons]

/-- Membership in `varSet`. -/
theorem mem_varSet {F : WS2Formula} {v : ℕ} :
    v ∈ F.varSet ↔ v ∈ F.distinctVars :=
  List.mem_toFinset

/-- Clauses of `F` with literals filtered to declared variables in `F.distinctVars`. -/
@[expose] def cleanClauses (F : WS2Formula) : List (List (ℕ × Bool)) :=
  F.clauses.map fun C => C.filter fun lit => decide (lit.1 ∈ F.distinctVars)

/-- When all literals in `F.clauses` already belong to `F.distinctVars`,
`F.cleanClauses = F.clauses`. -/
theorem cleanClauses_eq_clauses {F : WS2Formula}
    (h : ∀ C ∈ F.clauses, ∀ lit ∈ C, lit.1 ∈ F.distinctVars) :
    F.cleanClauses = F.clauses := by
  rw [cleanClauses]
  conv_rhs => rw [← List.map_id F.clauses]
  exact List.map_congr_left fun C hC =>
    List.filter_eq_self.2 fun lit hlit => decide_eq_true (h C hC lit hlit)

/-- Assignment `A : Finset ℕ` (the set of `true` variables) satisfies `F` when `A ⊆ var(F)` and
every clause in `F.cleanClauses` contains a satisfied literal. -/
@[expose] def Satisfies (F : WS2Formula) (A : Finset ℕ) : Prop :=
  A ⊆ F.varSet ∧ ∀ C ∈ F.cleanClauses, ∃ lit ∈ C, decide (lit.1 ∈ A) = lit.2

/-- Characterization of `F.Satisfies A`. -/
theorem satisfies_iff {F : WS2Formula} {A : Finset ℕ} :
    F.Satisfies A ↔ A ⊆ F.varSet ∧ ∀ C ∈ F.cleanClauses, ∃ lit ∈ C, decide (lit.1 ∈ A) = lit.2 :=
  Iff.rfl

/-- Polynomial-time computability of `distinctVars`. -/
@[fun_prop]
theorem computableInPolyTime_distinctVars :
    ComputableInPolyTime distinctVars encWS2Formula (encList encNat) := by
  open scoped WS2Formula in
  unfold distinctVars
  fun_prop

/-- Polynomial-time computability of `cleanClauses`. -/
@[fun_prop]
theorem computableInPolyTime_cleanClauses :
    ComputableInPolyTime cleanClauses encWS2Formula
      (encList (encList (encPair encNat encBool))) := by
  open scoped WS2Formula in
  unfold cleanClauses
  fun_prop

end WS2Formula

/-- Parameterized `WS2` instance `(formula, k)`. -/
@[ext]
structure WS2Instance where
  /-- Input CNF (`2`-normalized) formula. -/
  formula : WS2Formula
  /-- Target Hamming weight (and parameter). -/
  k : ℕ
  deriving DecidableEq

/-- Canonical binary encoding of `WS2Instance`. -/
enc_structure encWS2Instance : WS2Instance where
  formula : encWS2Formula, k : encNat

/-- **Weighted `2`-Normalized Satisfiability (`WS[2]`)**: instances `(F, k)` admitting a satisfying
assignment `A ⊆ var(F)` of exact weight `|A| = k`. -/
@[expose] def WS2 : Set WS2Instance :=
  {x | ∃ A : Finset ℕ, x.formula.Satisfies A ∧ A.card = x.k}

/-- Membership in `WS2`. -/
theorem mem_WS2 {x : WS2Instance} :
    x ∈ WS2 ↔ ∃ A : Finset ℕ, x.formula.Satisfies A ∧ A.card = x.k :=
  Iff.rfl

/-! ### `HittingSet ≤_FPT WS2` -/

/-- Translate a hypergraph `H` to a positive CNF formula whose clauses are the hyperedges of `H`. -/
def hittingSetToWS2Formula (H : FinHypergraph) : WS2Formula where
  headVar := H.headVertex
  tailVars := H.tailVertices
  clauses := H.edgeList.map fun e => e.map (·, true)

/-- Parameter-preserving reduction from `HittingSet` to `WS2`. -/
def hittingSetToWS2 (x : HittingSetInstance) : WS2Instance :=
  ⟨hittingSetToWS2Formula x.hypergraph, x.k⟩

/-- Correctness of `hittingSetToWS2Formula`: `T` satisfies the positive CNF formula if and only if
`T` is a hitting set of `H`. -/
theorem satisfies_hittingSetToWS2Formula_iff (H : FinHypergraph) (T : Finset ℕ) :
    (hittingSetToWS2Formula H).Satisfies T ↔ H.IsHittingSet T := by
  have hd : (hittingSetToWS2Formula H).distinctVars = H.distinctVertices := rfl
  have hv : (hittingSetToWS2Formula H).varSet = H.vertexSet := rfl
  simp only [WS2Formula.Satisfies, FinHypergraph.IsHittingSet, hv]
  refine and_congr_right fun _ => ?_
  rw [WS2Formula.cleanClauses, hd]
  simp only [hittingSetToWS2Formula, FinHypergraph.edgeFinsets, List.mem_map, List.mem_toFinset]
  constructor
  · rintro h _ ⟨e, he, rfl⟩
    obtain ⟨⟨v, b⟩, hlit, hsat⟩ := h
      ((e.map (·, true)).filter fun lit => decide (lit.1 ∈ H.distinctVertices))
      ⟨e.map (·, true), ⟨e, he, rfl⟩, rfl⟩
    simp only [List.mem_filter, List.mem_map, Prod.mk.injEq] at hlit
    obtain ⟨⟨u, hu, rfl, rfl⟩, _⟩ := hlit
    simp only [decide_eq_true_eq] at hsat
    exact ⟨u, Finset.mem_inter.2 ⟨hsat, List.mem_toFinset.2 hu⟩⟩
  · rintro h _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    obtain ⟨v, hv_inter⟩ := h e.toFinset ⟨e, he, rfl⟩
    rw [Finset.mem_inter, List.mem_toFinset] at hv_inter
    have hvin : v ∈ H.distinctVertices := by
      simp only [FinHypergraph.edgeList, List.mem_map] at he
      obtain ⟨r, -, rfl⟩ := he
      exact of_decide_eq_true (List.mem_filter.1 hv_inter.2).2
    exact ⟨(v, true),
      List.mem_filter.2 ⟨List.mem_map.2 ⟨v, hv_inter.2, rfl⟩, decide_eq_true hvin⟩,
      decide_eq_true hv_inter.1⟩

/-- `hittingSetToWS2 x ∈ WS2 ↔ x ∈ HittingSet`. -/
theorem hittingSetToWS2_mem_WS2_iff (x : HittingSetInstance) :
    hittingSetToWS2 x ∈ WS2 ↔ x ∈ HittingSet := by
  simp only [hittingSetToWS2, mem_WS2, mem_HittingSet, satisfies_hittingSetToWS2Formula_iff]

/-- `hittingSetToWS2` is polynomial-time. -/
theorem computableInPolyTime_hittingSetToWS2 :
    ComputableInPolyTime hittingSetToWS2 encHittingSetInstance encWS2Instance := by
  open scoped HittingSetInstance FinHypergraph WS2Instance WS2Formula in
  unfold hittingSetToWS2 hittingSetToWS2Formula
  fun_prop

/-- **`HittingSet` FPT-reduces to `WS2`** via a parameter-preserving polynomial-time reduction. -/
theorem fptReducible_HittingSet_WS2 :
    FPTReducible encHittingSetInstance encWS2Instance (·.k) (·.k) HittingSet WS2 :=
  FPTReducible.of_computableInPolyTime computableInPolyTime_hittingSetToWS2 (h := id)
    (fun _ => le_rfl) fun x => (hittingSetToWS2_mem_WS2_iff x).symm

/-! ### `WS2 ∈ W[2]` (`WS2 ≤_FPT WCS 2 3`) -/

namespace WS2ToCircuit

/-- Clauses of `F` translated to wire indices in `[0, 2 * n)`: index `i` for positive literal on the
`i`-th distinct variable and `n + i` for its negation. -/
def clauseWires (F : WS2Formula) : List (List ℕ) :=
  let V := F.distinctVars
  let n := V.length
  F.cleanClauses.map fun C => C.map fun lit =>
    let idx := V.idxOf lit.1
    if lit.2 then idx else n + idx

/-- All wire indices in `clauseWires F` are strictly below `2 * F.distinctVars.length`. -/
theorem lt_of_mem_clauseWires {F : WS2Formula} {w : ℕ} {W : List ℕ}
    (hW : W ∈ clauseWires F) (hw : w ∈ W) : w < F.distinctVars.length + F.distinctVars.length := by
  simp only [clauseWires, List.mem_map] at hW
  obtain ⟨C, hC, rfl⟩ := hW
  obtain ⟨lit, hlit, rfl⟩ := List.mem_map.1 hw
  simp only [WS2Formula.cleanClauses, List.mem_map] at hC
  obtain ⟨rawC, -, rfl⟩ := hC
  have hmem : lit.1 ∈ F.distinctVars := of_decide_eq_true (List.mem_filter.1 hlit).2
  have hidx : F.distinctVars.idxOf lit.1 < F.distinctVars.length :=
    List.idxOf_lt_length_iff.2 hmem
  cases lit.2 <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega

/-- 3-layer gate list for a `WS2Formula`: input negations, clause disjunctions, and top-level
conjunction. -/
def circuitGates (n : ℕ) (CW : List (List ℕ)) : List (Op × List ℕ) :=
  (List.range n).map (fun i => (.not, [i])) ++
    CW.map (fun W => (.or W.length, W)) ++
    [(.and CW.length, (List.range CW.length).map (n + n + ·))]

/-- Circuit code for `F : WS2Formula`. -/
def circuitCode (F : WS2Formula) : List (Op × List ℕ) × List ℕ :=
  let n := F.distinctVars.length
  let CW := clauseWires F
  (circuitGates n CW, [n + n + CW.length])

/-- `circuitGates n CW` is a well-formed gate list from `n` inputs. -/
theorem isCodeFrom_circuitGates {n : ℕ} {CW : List (List ℕ)}
    (hCW : ∀ W ∈ CW, ∀ w ∈ W, w < n + n) :
    Program.IsCodeFrom signature n 0 (circuitGates n CW) := by
  rw [circuitGates, Program.isCodeFrom_append, Program.isCodeFrom_append]
  refine ⟨⟨Program.isCodeFrom_of_forall
      (List.forall_mem_map.2 fun i hi => ⟨rfl, fun _ hx => by simp_all⟩),
    Program.isCodeFrom_of_forall (List.forall_mem_map.2 fun W hW => ⟨by simp, fun w hw => ?_⟩)⟩,
    Program.isCodeFrom_of_forall (List.forall_mem_singleton.2 ⟨by simp,
      List.forall_mem_map.2 fun j hj => ?_⟩)⟩
  · have := hCW W hW w hw
    simp only [List.length_map, List.length_range]
    omega
  · simp only [List.mem_range, List.length_append, List.length_map, List.length_range] at hj ⊢
    omega

/-- `circuitCode F` decodes to a valid 1-output circuit. -/
theorem isSome_ofCode_circuitCode (F : WS2Formula) :
    (Circuit.ofCode (σ := signature) F.distinctVars.length 1 (circuitCode F)).isSome = true := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨isCodeFrom_circuitGates fun W hW w hw => lt_of_mem_clauseWires hW hw, rfl, ?_⟩
  simp only [circuitCode, circuitGates, List.mem_singleton, forall_eq, List.length_append,
    List.length_map, List.length_range, List.length_singleton]
  omega

/-- The circuit of `F : WS2Formula`. -/
def toCircuit (F : WS2Formula) : Σ n, Circuit signature n 1 :=
  ⟨F.distinctVars.length,
    (Circuit.ofCode (σ := signature) F.distinctVars.length 1 (circuitCode F)).get
      (isSome_ofCode_circuitCode F)⟩

/-- Code of `toCircuit F`. -/
theorem code_toCircuit (F : WS2Formula) : (toCircuit F).2.code = circuitCode F :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

/-- Number of inputs of `toCircuit F`. -/
theorem toCircuit_fst (F : WS2Formula) : (toCircuit F).1 = F.distinctVars.length := by rfl

/-- Evaluating `circuitGates` computes whether every clause wire list contains a `true` wire. -/
theorem evalCode_circuitGates {n : ℕ} {CW : List (List ℕ)}
    (hCW : ∀ W ∈ CW, ∀ w ∈ W, w < n + n) (x : List Bool) (hx : x.length = n) :
    (evalCode interpretation false x (circuitGates n CW)).getD (n + n + CW.length) false =
      decide (∀ W ∈ CW, ∃ w ∈ W, (x ++ x.map (!·)).getD w false = true) := by
  subst hx
  rw [circuitGates, evalCode_append, evalCode_append]
  have h1 : evalCode interpretation false x
      ((List.range x.length).map fun i => (Op.not, [i])) = x ++ x.map (!·) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.ext_getElem (by simp) fun i h₁ _ => ?_
      simp only [List.length_map, List.length_range] at h₁
      simp [List.getElem?_eq_getElem h₁]
    · exact List.forall_mem_map.2 fun j hj _ hi => by simp_all
  set lits := x ++ x.map (!·)
  have hlits_len : lits.length = x.length + x.length := by simp [lits]
  have h2 : evalCode interpretation false lits
      (CW.map fun W => (Op.or W.length, W)) =
      lits ++ CW.map fun W => decide (∃ w ∈ W, lits.getD w false = true) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.map_congr_left fun W hW => ?_
      simp only [Function.comp_apply, interpretation_or]
      rw [decide_eq_decide]
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨W[a.val], List.getElem_mem a.isLt, ?_⟩
        simpa [List.getElem?_eq_getElem a.isLt] using ha
      · rintro ⟨w, hw, hval⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
        refine ⟨⟨i, hi⟩, ?_⟩
        simpa [List.getElem?_eq_getElem hi] using hval
    · refine List.forall_mem_map.2 fun W hW w hw => ?_
      rw [hlits_len]
      exact hCW W hW w hw
  rw [h1, h2, evalCode_layer]
  · have hlen2 : (lits ++ CW.map fun W => decide (∃ w ∈ W, lits.getD w false = true)).length =
        x.length + x.length + CW.length := by simp [hlits_len, Nat.add_assoc]
    rw [← hlen2, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    simp only [List.map_singleton, List.getD_cons_zero, interpretation_and]
    rw [decide_eq_decide, List.forall_mem_iff_getElem, Fin.forall_iff]
    refine forall_congr' fun j => forall_congr' fun hj => ?_
    rw [List.getElem?_eq_getElem (by simpa using hj)]
    simp only [Option.elim_some, List.getElem_map, List.getElem_range]
    rw [show x.length + x.length + j = lits.length + j by rw [hlits_len],
      List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, decide_eq_true_eq]
  · refine List.forall_mem_singleton.2 (List.forall_mem_map.2 fun j hj => ?_)
    simp only [List.mem_range, List.length_append, List.length_map, hlits_len] at hj ⊢
    omega

private theorem le_of_mem_evalCode_circuitGates (cost : Op → ℕ) {n : ℕ} {CW : List (List ℕ)}
    (hCW : ∀ W ∈ CW, ∀ w ∈ W, w < n + n) {c₁ c₂ c₃ : ℕ}
    (h₁ : cost Op.not ≤ c₁) (h₂ : ∀ W ∈ CW, cost (Op.or W.length) ≤ c₂)
    (h₃ : cost (Op.and CW.length) ≤ c₃) :
    ∀ v ∈ evalCode (depthInterpretation (σ := signature) cost) 0 (List.replicate n 0)
      (circuitGates n CW), v ≤ 0 + c₁ + c₂ + c₃ := by
  rw [circuitGates, evalCode_append, evalCode_append]
  refine le_of_mem_evalCode_depth_layer _ _ _
    (List.forall_mem_singleton.2 (List.forall_mem_map.2 fun j hj => ?_))
    (le_of_mem_evalCode_depth_layer _ _ _ (List.forall_mem_map.2 fun W hW w hw => ?_)
      (le_of_mem_evalCode_depth_layer _ _ _
        (List.forall_mem_map.2 fun j hj _ hi => by simp_all)
        (fun _ hv => (List.eq_of_mem_replicate hv).le)
        (by simp [h₁]))
      (List.forall_mem_map.2 h₂))
    (by simp [h₃])
  · simp only [List.mem_range, length_evalCode, List.length_replicate, List.length_map,
      List.length_range] at hj ⊢
    omega
  · have := hCW W hW w hw
    simp only [length_evalCode, List.length_replicate, List.length_map, List.length_range]
    omega

/-- `toCircuit F` has weft at most `2`. -/
theorem weft_toCircuit_le (F : WS2Formula) : (toCircuit F).2.weft ≤ 2 := by
  refine Circuit.depthWith_le_of_evalCode _ _ fun v hv => ?_
  simpa using le_of_mem_evalCode_circuitGates (largeGateCost signature)
    (fun W hW w hw => lt_of_mem_clauseWires hW hw) (c₁ := 0) (c₂ := 1) (c₃ := 1)
    (by decide) (fun _ _ => largeGateCost_le_one _) (largeGateCost_le_one _) v
    (code_toCircuit F ▸ hv)

/-- `toCircuit F` has depth at most `3`. -/
theorem depth_toCircuit_le (F : WS2Formula) : (toCircuit F).2.depth ≤ 3 := by
  rw [← Circuit.depthWith_one]
  refine Circuit.depthWith_le_of_evalCode _ _ fun v hv => ?_
  simpa using le_of_mem_evalCode_circuitGates 1
    (fun W hW w hw => lt_of_mem_clauseWires hW hw) le_rfl (fun _ _ => le_rfl) le_rfl v
    (code_toCircuit F ▸ hv)

private def varSetOfBits (F : WS2Formula) (x : BitString (toCircuit F).1) : Finset ℕ :=
  (Finset.univ.filter fun i => x i = true).map
    ⟨fun i => F.distinctVars[i.val]'(i.isLt.trans_eq (toCircuit_fst F)),
      fun _ _ h => Fin.ext ((List.Nodup.getElem_inj_iff F.nodup_distinctVars).1 h)⟩

private theorem mem_varSetOfBits {F : WS2Formula} {x : BitString (toCircuit F).1} {v : ℕ} :
    v ∈ varSetOfBits F x ↔ ∃ h : v ∈ F.distinctVars,
      x ⟨F.distinctVars.idxOf v, List.idxOf_lt_length_iff.2 h⟩ = true := by
  simp only [varSetOfBits, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, fun ⟨hv, hx⟩ => ⟨_, hx, List.getElem_idxOf _⟩⟩
  rintro ⟨i, hi, rfl⟩
  refine ⟨List.getElem_mem _, ?_⟩
  convert hi using 2
  exact Fin.ext (F.nodup_distinctVars.idxOf_getElem _ _)

/-- `toCircuit F` has a weight-`k` satisfying input if and only if `(F, k) ∈ WS2`. -/
theorem toCircuit_satisfiableWithWeight_iff (F : WS2Formula) (k : ℕ) :
    (toCircuit F).2.SatisfiableWithWeight interpretation k ↔ (⟨F, k⟩ : WS2Instance) ∈ WS2 := by
  have hout : ((toCircuit F).2.outputs 0).toNat =
      F.distinctVars.length + F.distinctVars.length + (clauseWires F).length :=
    congrArg (fun c => c.2.headD 0) (code_toCircuit F)
  have heval : ∀ x : BitString (toCircuit F).1,
      (toCircuit F).2.eval interpretation x 0 = true ↔ F.Satisfies (varSetOfBits F x) := by
    intro x
    rw [Circuit.eval_eq_getD _ _ false, hout, code_toCircuit]
    dsimp only [circuitCode]
    rw [evalCode_circuitGates (fun W hW w hw => lt_of_mem_clauseWires hW hw) _
        (List.length_ofFn.trans (toCircuit_fst F)),
      decide_eq_true_eq]
    have hsub : varSetOfBits F x ⊆ F.varSet := fun v hv =>
      WS2Formula.mem_varSet.2 (mem_varSetOfBits.1 hv).1
    simp only [WS2Formula.Satisfies, hsub, true_and, clauseWires, List.mem_map]
    have hlit_val : ∀ (v : ℕ) (hv : v ∈ F.distinctVars) (pol : Bool),
        ((List.ofFn x ++ (List.ofFn x).map (!·)).getD
          (if pol then F.distinctVars.idxOf v else F.distinctVars.length + F.distinctVars.idxOf v)
          false = true) ↔ (decide (v ∈ varSetOfBits F x) = pol) := by
      intro v hv pol
      have hidx : F.distinctVars.idxOf v < F.distinctVars.length := List.idxOf_lt_length_iff.2 hv
      have hlen : (List.ofFn x).length = F.distinctVars.length :=
        List.length_ofFn.trans (toCircuit_fst F)
      have hbit : (List.ofFn x)[F.distinctVars.idxOf v]'(by omega) =
          decide (v ∈ varSetOfBits F x) := by
        rw [List.getElem_ofFn]
        cases hxv : x ⟨F.distinctVars.idxOf v, hidx⟩
        · symm; rw [decide_eq_false_iff_not, mem_varSetOfBits]; rintro ⟨_, h'⟩; simp [hxv] at h'
        · symm; rw [decide_eq_true_eq, mem_varSetOfBits]; exact ⟨hv, hxv⟩
      cases pol
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [← hlen, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left,
          List.getD_eq_getElem _ _ (by rw [List.length_map, hlen]; exact hidx),
          List.getElem_map, hbit]
        cases decide (v ∈ varSetOfBits F x) <;> decide
      · simp only [↓reduceIte]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem _ _ (by omega), hbit]
    constructor
    · intro h C hC
      obtain ⟨w, hw, htrue⟩ := h _ ⟨C, hC, rfl⟩
      obtain ⟨lit, hlit, rfl⟩ := List.mem_map.1 hw
      simp only [WS2Formula.cleanClauses, List.mem_map] at hC
      obtain ⟨rawC, -, rfl⟩ := hC
      have hv : lit.1 ∈ F.distinctVars := of_decide_eq_true (List.mem_filter.1 hlit).2
      exact ⟨lit, hlit, (hlit_val lit.1 hv lit.2).1 htrue⟩
    · rintro h _ ⟨C, hC, rfl⟩
      obtain ⟨lit, hlit, hsat⟩ := h C hC
      simp only [WS2Formula.cleanClauses, List.mem_map] at hC
      obtain ⟨rawC, -, rfl⟩ := hC
      have hv : lit.1 ∈ F.distinctVars := of_decide_eq_true (List.mem_filter.1 hlit).2
      exact ⟨_, List.mem_map.2 ⟨lit, hlit, rfl⟩, (hlit_val lit.1 hv lit.2).2 hsat⟩
  simp only [Circuit.SatisfiableWithWeight, heval, mem_WS2]
  refine ⟨fun ⟨x, hk, hx⟩ => ⟨varSetOfBits F x, hx, (Finset.card_map _).trans hk⟩, ?_⟩
  rintro ⟨A, hA, hk⟩
  let x : BitString (toCircuit F).1 := fun i =>
    decide (F.distinctVars[i.val]'(i.isLt.trans_eq (toCircuit_fst F)) ∈ A)
  have hvA : varSetOfBits F x = A := Finset.ext fun v => by
    simp only [mem_varSetOfBits, x, decide_eq_true_eq, List.getElem_idxOf, exists_prop]
    exact ⟨And.right, fun hv => ⟨WS2Formula.mem_varSet.1 (hA.1 hv), hv⟩⟩
  exact ⟨x, (Finset.card_map _).symm.trans ((congrArg Finset.card hvA).trans hk), hvA.symm ▸ hA⟩

/-- `clauseWires` is polynomial-time (with wire indices in unary). -/
theorem computableInPolyTime_clauseWires :
    ComputableInPolyTime clauseWires encWS2Formula (encList (encList encUnary)) := by
  have hV := WS2Formula.computableInPolyTime_distinctVars
  have hC := WS2Formula.computableInPolyTime_cleanClauses
  unfold clauseWires
  refine ComputableInPolyTime.mapWithInput hC ?_
  refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
  fun_prop

/-- `circuitCode` is polynomial-time. -/
theorem computableInPolyTime_circuitCode :
    ComputableInPolyTime circuitCode encWS2Formula (Circuit.encCode encOp) := by
  have hV := WS2Formula.computableInPolyTime_distinctVars
  have hCW := computableInPolyTime_clauseWires
  have hb := ComputableInPolyTime.unary_to_binary
  have hn : ComputableInPolyTime (fun F : WS2Formula => F.distinctVars.length)
      encWS2Formula encUnary := by
    fun_prop
  have hm : ComputableInPolyTime (fun F : WS2Formula => (clauseWires F).length)
      encWS2Formula encUnary := by
    fun_prop
  have hnot : ComputableInPolyTime
      (fun F : WS2Formula => (List.range F.distinctVars.length).map
        fun i => ((Op.not, [i]) : Op × List ℕ))
      encWS2Formula (encList (Circuit.encGate encOp)) := by
    fun_prop
  have hor : ComputableInPolyTime
      (fun F : WS2Formula => (clauseWires F).map fun W =>
        ((Op.or W.length, W) : Op × List ℕ))
      encWS2Formula (encList (Circuit.encGate encOp)) := by
    refine hCW.mapWithInput ?_
    have hWlen : ComputableInPolyTime (fun p : WS2Formula × List ℕ => p.2.length)
        (encPair encWS2Formula (encList encUnary)) encUnary := by fun_prop
    refine (computableInPolyTime_or.comp hWlen).prod ?_
    exact (((ComputableInPolyTime.map hb).comp
      (ComputableInPolyTime.snd encWS2Formula (encList encUnary))).of_enc_eq fun _ => by simp)
  have hand : ComputableInPolyTime
      (fun F : WS2Formula => [((Op.and (clauseWires F).length,
        (List.range (clauseWires F).length).map
          (F.distinctVars.length + F.distinctVars.length + ·)) : Op × List ℕ)])
      encWS2Formula (encList (Circuit.encGate encOp)) :=
    .cons' ((computableInPolyTime_and.comp hm).prod
      ((ComputableInPolyTime.range.comp hm).mapWithInput (hb.comp (by fun_prop)))) (.const [])
  unfold circuitCode circuitGates
  exact ((hnot.listAppend' hor).listAppend' hand).prod
    (.cons' (hb.comp (by fun_prop)) (.const []))

/-- Map a `WS2Instance` to `WCSInstance 2 3`. -/
def toWCS (x : WS2Instance) : WCSInstance 2 3 :=
  ⟨⟨toCircuit x.formula, weft_toCircuit_le x.formula, depth_toCircuit_le x.formula⟩, x.k⟩

/-- `toWCS` is polynomial-time. -/
theorem computableInPolyTime_toWCS :
    ComputableInPolyTime toWCS encWS2Instance (encWCS 2 3) := by
  open scoped WS2Instance in
  have hc := computableInPolyTime_circuitCode
  have hV := WS2Formula.computableInPolyTime_distinctVars
  refine (by fun_prop : ComputableInPolyTime
      (fun x : WS2Instance =>
        ((x.formula.distinctVars.length, circuitCode x.formula), x.k))
      encWS2Instance
      (encPair (encPair encUnary (Circuit.encCode encOp)) encNat)).of_enc_eq
    fun ⟨F, k⟩ => ?_
  simp only [toWCS, encWCS_apply, encPair_apply, encWeftCircuit_apply, Circuit.encCircuit_apply,
    code_toCircuit]
  rfl

end WS2ToCircuit

/-- **`WS2` FPT-reduces to `WCS 2 3`**. -/
theorem fptReducible_WS2_WCS :
    FPTReducible encWS2Instance (encWCS 2 3) (·.k) WCSInstance.weight WS2 (WCS 2 3) :=
  FPTReducible.of_computableInPolyTime WS2ToCircuit.computableInPolyTime_toWCS (h := id)
    (fun _ => le_rfl) fun x => (WS2ToCircuit.toCircuit_satisfiableWithWeight_iff x.formula x.k).symm

/-- **`WS2` belongs to `W[2]`**. -/
theorem WS2_mem_W : WS2 ∈ W 2 encWS2Instance (·.k) :=
  ⟨3, fptReducible_WS2_WCS⟩

/-- **`HittingSet` belongs to `W[2]`**. -/
theorem HittingSet_mem_W : HittingSet ∈ W 2 encHittingSetInstance (·.k) :=
  fptReducible_HittingSet_WS2.mem_W WS2_mem_W

/-! ### `W[2]`-Hardness of `HittingSet` (`WCS 2 d ≤_FPT HittingSet`) -/

namespace WCSToHittingSet

/-- Certificate block `[0, …, N_certs - 1]`. -/
def certBlock (N_certs : ℕ) : List ℕ :=
  List.range N_certs

/-- Bracket block `{N_certs + j | B[j].map fst = C}`. -/
def bracketBlock (N_certs : ℕ) (B : List (List (ℕ × ℕ))) (C : List ℕ) : List ℕ :=
  (B.zipIdx.filter fun p => decide (p.1.map Prod.fst = C)).map fun p => N_certs + p.2

/-- Incompatible bracket hyperedges `(B_{C₁} \ {P₁}) ∪ (B_{C₂} \ {P₂})` for `C₁ ≠ C₂` and
`!consistent P₁ P₂`. -/
def consistencyEdges (N_certs : ℕ) (B : List (List (ℕ × ℕ))) : List (List ℕ) :=
  B.zipIdx.flatMap fun p₁ =>
    B.zipIdx.flatMap fun p₂ =>
      let C₁ := p₁.1.map Prod.fst
      let C₂ := p₂.1.map Prod.fst
      if !decide (C₁ = C₂) && !consistent p₁.1 p₂.1 then
        [((bracketBlock N_certs B C₁).filter fun v => !decide (v = N_certs + p₁.2)) ++
          ((bracketBlock N_certs B C₂).filter fun v => !decide (v = N_certs + p₂.2))]
      else []

/-- Weft-`1` refutation hyperedges `(B_0 \ {cl₂}) ∪ {P | refutes cl₁ P}` for each weft-`2`
certificate `cl₂`, check `e` of `cl₂`, and refuting weft-`1` certificate `cl₁`. -/
def refutationEdges (d n kk : ℕ) (gates : List (Op × List ℕ))
    (C₂ : List (List (ℕ × Bool))) (B : List (List (ℕ × ℕ))) : List (List ℕ) :=
  let N_certs := C₂.length
  C₂.zipIdx.flatMap fun p =>
    (p.1.flatMap (WeftOne.claimChecks n gates)).flatMap fun e =>
      (certsOne d n gates e.1 (!e.2)).map fun cl₁ =>
        ((certBlock N_certs).filter fun v => !decide (v = p.2)) ++
          ((B.zipIdx.filter fun q => refutes n kk gates cl₁ q.1).map fun q => N_certs + q.2)

/-- Raw hyperedges of the weft-`2` reduction hypergraph. -/
def rawEdgesOf (d n : ℕ) (gates : List (Op × List ℕ)) (o k : ℕ) : List (List ℕ) :=
  let kk := min (n + 1) k
  let C₂ := certsSucc 1 d n gates o true
  let B := brackets d n kk
  let IL := indexLists d kk
  let N_certs := C₂.length
  [certBlock N_certs] ++
    IL.map (bracketBlock N_certs B) ++
    consistencyEdges N_certs B ++
    refutationEdges d n kk gates C₂ B

/-- Hypergraph constructed from a weft-`2`, depth-`d` gate list with output `o` and weight `k`. -/
def hypergraph (d n : ℕ) (gates : List (Op × List ℕ)) (o k : ℕ) : FinHypergraph :=
  let kk := min (n + 1) k
  let C₂ := certsSucc 1 d n gates o true
  let B := brackets d n kk
  { headVertex := 0
    tailVertices := List.range (C₂.length + B.length)
    rawEdges := rawEdgesOf d n gates o k }

/-- Map a `WCSInstance 2 d` to a `HittingSetInstance`. -/
def toHittingSet {d : ℕ} (x : WCSInstance 2 d) : HittingSetInstance :=
  ⟨hypergraph d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
    (x.circuit.toCircuit.2.outputs 0).toNat x.weight,
    size d x.circuit.toCircuit.1 x.weight⟩

private theorem mem_zipIdx_iff {α : Type*} {l : List α} {a : α} {i : ℕ} :
    (a, i) ∈ l.zipIdx ↔ ∃ h : i < l.length, l[i] = a := by
  rw [List.mem_iff_getElem]
  simp only [List.length_zipIdx, List.getElem_zipIdx, zero_add, Prod.mk.injEq]
  exact ⟨fun ⟨j, hj, h1, h2⟩ => ⟨h2 ▸ hj, h2 ▸ h1⟩, fun ⟨hi, h1⟩ => ⟨i, hi, h1, rfl⟩⟩

private theorem brackets_pos (d n kk : ℕ) : 0 < (brackets d n kk).length :=
  List.length_pos_of_mem (mem_brackets.2 ⟨Nat.zero_le _, by simp⟩ : ([] : List _) ∈ _)

private theorem nodup_brackets (d n kk : ℕ) : (brackets d n kk).Nodup := by
  unfold brackets pairs
  refine List.nodup_listsUpTo ?_ _
  rw [List.nodup_flatMap]
  refine ⟨fun j _ => List.nodup_range.map fun a b h => (Prod.mk.inj h).2, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun i _ j _ hij p hpi hpj => ?_
  obtain ⟨_, -, rfl⟩ := List.mem_map.1 hpi
  obtain ⟨_, -, h⟩ := List.mem_map.1 hpj
  exact hij (Prod.mk.inj h).1.symm

private theorem mem_distinctVertices_hypergraph_iff (d n : ℕ) (gates : List (Op × List ℕ))
    (o k v : ℕ) :
    v ∈ (hypergraph d n gates o k).distinctVertices ↔
      v < (certsSucc 1 d n gates o true).length + (brackets d n (min (n + 1) k)).length := by
  have hpos := brackets_pos d n (min (n + 1) k)
  rw [FinHypergraph.mem_distinctVertices]
  simp only [hypergraph, List.mem_range]
  omega

private theorem mem_bracketBlock_iff {N_certs : ℕ} {B : List (List (ℕ × ℕ))} {C : List ℕ}
    {v : ℕ} :
    v ∈ bracketBlock N_certs B C ↔
      ∃ (j : ℕ) (hj : j < B.length), B[j].map Prod.fst = C ∧ v = N_certs + j := by
  simp only [bracketBlock, List.mem_map, List.mem_filter, Prod.exists, mem_zipIdx_iff,
    decide_eq_true_eq]
  constructor
  · rintro ⟨P, j, ⟨⟨hj, rfl⟩, hC⟩, hv⟩
    exact ⟨j, hj, hC, hv.symm⟩
  · rintro ⟨j, hj, hC, rfl⟩
    exact ⟨B[j], j, ⟨⟨hj, rfl⟩, hC⟩, rfl⟩

private theorem rawEdgesOf_lt {d n : ℕ} {gates : List (Op × List ℕ)} {o k : ℕ}
    {e : List ℕ} (he : e ∈ rawEdgesOf d n gates o k) {v : ℕ} (hv : v ∈ e) :
    v < (certsSucc 1 d n gates o true).length + (brackets d n (min (n + 1) k)).length := by
  simp only [rawEdgesOf, List.mem_append, List.mem_singleton, List.mem_map] at he
  rcases he with ((rfl | ⟨C, -, rfl⟩) | hcons) | href
  · simp only [certBlock, List.mem_range] at hv; omega
  · obtain ⟨j, hj, -, rfl⟩ := mem_bracketBlock_iff.1 hv; omega
  · simp only [consistencyEdges, List.mem_flatMap] at hcons
    obtain ⟨p₁, -, p₂, -, hite⟩ := hcons
    split_ifs at hite
    swap; · cases hite
    simp only [List.mem_singleton] at hite
    subst hite
    rcases List.mem_append.1 hv with hv₁ | hv₂
    · obtain ⟨j, hj, -, rfl⟩ := mem_bracketBlock_iff.1 (List.mem_filter.1 hv₁).1; omega
    · obtain ⟨j, hj, -, rfl⟩ := mem_bracketBlock_iff.1 (List.mem_filter.1 hv₂).1; omega
  · simp only [refutationEdges, List.mem_flatMap, List.mem_map] at href
    obtain ⟨p, -, e', -, cl₁, -, rfl⟩ := href
    rcases List.mem_append.1 hv with hv₁ | hv₂
    · have := List.mem_range.1 (List.mem_filter.1 hv₁).1; omega
    · simp only [List.mem_map, List.mem_filter, Prod.exists, mem_zipIdx_iff] at hv₂
      obtain ⟨P, j, ⟨⟨hj, _⟩, _⟩, rfl⟩ := hv₂; omega

private theorem mem_edgeFinsets_hypergraph_iff (d n : ℕ) (gates : List (Op × List ℕ)) (o k : ℕ)
    {E : Finset ℕ} :
    E ∈ (hypergraph d n gates o k).edgeFinsets ↔
      ∃ e ∈ rawEdgesOf d n gates o k, e.toFinset = E := by
  have hraw : (hypergraph d n gates o k).rawEdges = rawEdgesOf d n gates o k := rfl
  simp only [FinHypergraph.edgeFinsets, FinHypergraph.edgeList, hraw, List.mem_toFinset,
    List.mem_map]
  constructor
  · rintro ⟨l, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨e, he, ?_⟩
    rw [List.filter_eq_self.2]
    intro v hv
    exact decide_eq_true
      ((mem_distinctVertices_hypergraph_iff d n gates o k v).2 (rawEdgesOf_lt he hv))
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, ⟨e, he, ?_⟩, rfl⟩
    rw [List.filter_eq_self.2]
    intro v hv
    exact decide_eq_true
      ((mem_distinctVertices_hypergraph_iff d n gates o k v).2 (rawEdgesOf_lt he hv))

private theorem map_fst_map_pair (u : ℕ → ℕ) (C : List ℕ) :
    (C.map fun j => (j, u j)).map Prod.fst = C :=
  List.map_map.trans (List.map_id C)

private theorem eq_map_pair_of_map_fst {u : ℕ → ℕ} {P : List (ℕ × ℕ)} {C : List ℕ}
    (hC : P.map Prod.fst = C) (hu : ∀ p ∈ P, p.2 = u p.1) :
    P = C.map fun j => (j, u j) := by
  subst hC
  induction P with
  | nil => rfl
  | cons p P ih =>
    obtain ⟨a, b⟩ := p
    have hb : b = u a := hu (a, b) List.mem_cons_self
    subst hb
    exact congrArg ((a, u a) :: ·) (ih fun q hq => hu q (List.mem_cons_of_mem _ hq))

/-- **Completeness of `toHittingSet`.** A satisfying weight-`k` input of a circuit of weft at most
`2` and depth at most `d` yields a hitting set of size `size d n k`. -/
theorem mem_HittingSet_of_eval {d n : ℕ} (c : Circuit signature n 1) (hw : c.weft ≤ 2)
    (hd : c.depth ≤ d) {k : ℕ} (x : BitString n) (hk : BitString.weight x = k)
    (hx : c.eval interpretation x 0 = true) :
    (⟨hypergraph d n c.code.1 (c.outputs 0).toNat k, size d n k⟩ : HittingSetInstance) ∈
      HittingSet := by
  classical
  have hkn : k ≤ n := hk ▸ BitString.weight_le_length x
  have hkk : min (n + 1) k = k := min_eq_right (by omega)
  obtain ⟨u, hu, hun, rfl⟩ := exists_eq_selectedBits x hk
  have ho_wft : (evalCode (depthInterpretation (largeGateCost signature)) 0
      (List.replicate n 0) c.code.1).getD (c.outputs 0).toNat 0 ≤ 2 := by
    simpa only [Circuit.getD_evalCode_depthInterpretation] using c.weft_le_iff.1 hw 0
  have ho_dp : (evalCode (depthInterpretation (σ := signature) 1) 0
      (List.replicate n 0) c.code.1).getD (c.outputs 0).toNat 0 ≤ d := by
    simpa only [Circuit.getD_evalCode_depthInterpretation] using
      (c.wireDepthsWith_outputs_le_depthWith 1 0).trans (c.depthWith_one.trans_le hd)
  set gates := c.code.1
  set o := (c.outputs 0).toNat
  have ho_lt : o < n + gates.length := c.toNat_outputs_lt 0
  rw [c.eval_eq_getD interpretation false] at hx
  obtain ⟨cl₂, hcl₂, hchecks₂⟩ :=
    (eval_eq_iff_exists_certsSucc (t := 1) c.isCodeFrom_code List.length_ofFn ho_lt ho_wft ho_dp
      true).1 hx
  set C₂ := certsSucc 1 d n gates o true
  set B := brackets d n k
  set IL := indexLists d k
  set N_certs := C₂.length
  obtain ⟨ic, hic_lt, hic_eq⟩ := List.getElem_of_mem hcl₂
  let trueBr : List ℕ → List (ℕ × ℕ) := fun C => C.map fun j => (j, u j)
  have htrueBr_mem : ∀ C ∈ IL, trueBr C ∈ B := by
    intro C hC
    obtain ⟨hlen, hlt⟩ := mem_indexLists.1 hC
    refine mem_brackets.2 ⟨by simpa [trueBr] using hlen, fun p hp => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    exact ⟨hlt j hj, hun j (hlt j hj)⟩
  let ib : List ℕ → ℕ := fun C => B.idxOf (trueBr C)
  have hib_lt : ∀ C ∈ IL, ib C < B.length := fun C hC =>
    List.idxOf_lt_length_iff.2 (htrueBr_mem C hC)
  have hib_get : ∀ C (hC : C ∈ IL), B[ib C]'(hib_lt C hC) = trueBr C := fun C _ =>
    List.getElem_idxOf _
  let T : Finset ℕ := insert ic (IL.toFinset.image fun C => N_certs + ib C)
  have hC₂_eq : (certsSucc 1 d n gates o true).length = N_certs := rfl
  have hB_eq : (brackets d n k).length = B.length := rfl
  rw [mem_HittingSet]
  refine ⟨T, ⟨?_, ?_⟩, ?_⟩
  · intro v hv
    rw [FinHypergraph.mem_vertexSet, mem_distinctVertices_hypergraph_iff, hkk, hC₂_eq, hB_eq]
    simp only [T, Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at hv
    rcases hv with rfl | ⟨C, hC, rfl⟩
    · exact Nat.lt_add_right _ hic_lt
    · have := hib_lt C hC; omega
  · intro E hE
    rw [mem_edgeFinsets_hypergraph_iff] at hE
    obtain ⟨e, he, rfl⟩ := hE
    simp only [rawEdgesOf, hkk, List.mem_append, List.mem_singleton, List.mem_map] at he
    rcases he with ((rfl | ⟨C, hC, rfl⟩) | hcons) | href
    · exact ⟨ic, Finset.mem_inter.2 ⟨Finset.mem_insert_self _ _,
        List.mem_toFinset.2 (List.mem_range.2 hic_lt)⟩⟩
    · refine ⟨N_certs + ib C, Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hC)), List.mem_toFinset.2 ?_⟩⟩
      exact mem_bracketBlock_iff.2 ⟨ib C, hib_lt C hC, by rw [hib_get C hC, map_fst_map_pair], rfl⟩
    · simp only [consistencyEdges, List.mem_flatMap] at hcons
      obtain ⟨⟨P₁, j₁⟩, hp₁, ⟨P₂, j₂⟩, hp₂, hite⟩ := hcons
      obtain ⟨hj₁, rfl⟩ := mem_zipIdx_iff.1 hp₁
      obtain ⟨hj₂, rfl⟩ := mem_zipIdx_iff.1 hp₂
      split_ifs at hite with hbad
      swap; · cases hite
      simp only [List.mem_singleton] at hite
      subst hite
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hbad
      set C₁ := B[j₁].map Prod.fst
      set C₂' := B[j₂].map Prod.fst
      have hC₁ : C₁ ∈ IL := by
        obtain ⟨hlen, hlt⟩ := mem_brackets.1 (List.getElem_mem hj₁)
        exact mem_indexLists.2 ⟨by simpa [C₁] using hlen, fun j hj =>
          let ⟨p, hp, h⟩ := List.mem_map.1 hj; h ▸ (hlt p hp).1⟩
      have hC₂' : C₂' ∈ IL := by
        obtain ⟨hlen, hlt⟩ := mem_brackets.1 (List.getElem_mem hj₂)
        exact mem_indexLists.2 ⟨by simpa [C₂'] using hlen, fun j hj =>
          let ⟨p, hp, h⟩ := List.mem_map.1 hj; h ▸ (hlt p hp).1⟩
      by_cases h1 : ib C₁ = j₁
      · have h2 : ib C₂' ≠ j₂ := by
          intro h2
          have hcons_true : consistent (trueBr C₁) (trueBr C₂') = true := by
            rw [consistent_iff]
            intro p hp q hq
            obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
            obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hq
            rw [pairOk_iff]
            have ha_lt := (mem_indexLists.1 hC₁).2 a ha
            have hb_lt := (mem_indexLists.1 hC₂').2 b hb
            exact ⟨(hu.injOn.eq_iff ha_lt hb_lt).symm,
              (hu.lt_iff_lt (Set.mem_Iio.2 ha_lt) (Set.mem_Iio.2 hb_lt)).symm⟩
          have heq1 : B[j₁] = trueBr C₁ := by rw [← hib_get C₁ hC₁]; simp only [h1]
          have heq2 : B[j₂] = trueBr C₂' := by rw [← hib_get C₂' hC₂']; simp only [h2]
          rw [heq1, heq2, hcons_true] at hbad
          exact absurd hbad.2 (by decide)
        refine ⟨N_certs + ib C₂', Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hC₂')), List.mem_toFinset.2
            (List.mem_append_right _ (List.mem_filter.2
              ⟨?_, by simp [hC₂_eq, h2]⟩))⟩⟩
        exact mem_bracketBlock_iff.2 ⟨ib C₂', hib_lt C₂' hC₂',
          by rw [hib_get C₂' hC₂', map_fst_map_pair], rfl⟩
      · refine ⟨N_certs + ib C₁, Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hC₁)), List.mem_toFinset.2
            (List.mem_append_left _ (List.mem_filter.2
              ⟨?_, by simp [hC₂_eq, h1]⟩))⟩⟩
        exact mem_bracketBlock_iff.2 ⟨ib C₁, hib_lt C₁ hC₁,
          by rw [hib_get C₁ hC₁, map_fst_map_pair], rfl⟩
    · simp only [refutationEdges, List.mem_flatMap, List.mem_map] at href
      obtain ⟨⟨cl', jc⟩, hjc, e, he, cl₁, hcl₁, rfl⟩ := href
      obtain ⟨hjc_lt, rfl⟩ := mem_zipIdx_iff.1 hjc
      by_cases hjc_eq : ic = jc
      · subst hjc_eq
        have hic_eq' : (certsSucc 1 d n gates o true)[ic] = cl₂ := hic_eq
        rw [hic_eq'] at he
        have he' : e ∈ cl₂.flatMap (WeftOne.claimChecks n gates) := List.mem_flatMap.2 he
        obtain ⟨he_lt, he_wft, he_dp⟩ :=
          check_bounds_of_mem_certsSucc c.isCodeFrom_code hcl₂ he'
        have he_val := hchecks₂ e he'
        obtain ⟨C, hC, href_true⟩ :=
          (eval_selectedBits_eq_iff_forall_certsOne_refutes c.isCodeFrom_code hu he_lt he_wft
            he_dp e.2).1 he_val cl₁ hcl₁
        refine ⟨N_certs + ib C, Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hC)), List.mem_toFinset.2
            (List.mem_append_right _ (List.mem_map.2 ⟨(trueBr C, ib C),
              List.mem_filter.2 ⟨mem_zipIdx_iff.2 ⟨hib_lt C hC, hib_get C hC⟩, href_true⟩,
              rfl⟩))⟩⟩
      · exact ⟨ic, Finset.mem_inter.2 ⟨Finset.mem_insert_self _ _, List.mem_toFinset.2
          (List.mem_append_left _ (List.mem_filter.2 ⟨List.mem_range.2 hic_lt,
            by simp [hjc_eq]⟩))⟩⟩
  · have hnotMem : ic ∉ IL.toFinset.image fun C => N_certs + ib C := by
      simp only [Finset.mem_image, List.mem_toFinset, not_exists, not_and]
      intro C _ h; have : ic < N_certs := hic_lt; omega
    have hinj : Set.InjOn (fun C => N_certs + ib C) (IL.toFinset : Set (List ℕ)) := by
      intro C₁ h₁ C₂' h₂ h
      rw [Finset.mem_coe, List.mem_toFinset] at h₁ h₂
      have hib_eq : ib C₁ = ib C₂' := Nat.add_left_cancel h
      have hbr_eq : trueBr C₁ = trueBr C₂' := by
        rw [← hib_get C₁ h₁, ← hib_get C₂' h₂]; simp only [hib_eq]
      simpa only [trueBr, map_fst_map_pair] using congrArg (List.map Prod.fst) hbr_eq
    rw [Finset.card_insert_of_notMem hnotMem, Finset.card_image_of_injOn hinj,
      List.toFinset_card_of_nodup (nodup_indexLists d k), size, hkk, add_comm]

/-- **Soundness of `toHittingSet`.** A hitting set of size `size d n k` for `hypergraph` yields a
satisfying weight-`k` input of `c`. -/
theorem satisfiableWithWeight_of_mem_HittingSet {d n : ℕ} (c : Circuit signature n 1) {k : ℕ}
    (h : (⟨hypergraph d n c.code.1 (c.outputs 0).toNat k, size d n k⟩ : HittingSetInstance) ∈
      HittingSet) :
    c.SatisfiableWithWeight interpretation k := by
  classical
  set kk := min (n + 1) k with hkk_def
  set gates := c.code.1
  set o := (c.outputs 0).toNat
  set C₂ := certsSucc 1 d n gates o true
  set B := brackets d n kk
  set IL := indexLists d kk
  set N_certs := C₂.length
  obtain ⟨T, ⟨hTV, hThit⟩, hTcard⟩ := mem_HittingSet.1 h
  rw [size, ← hkk_def] at hTcard
  have hedge : ∀ e ∈ rawEdgesOf d n gates o k, (T ∩ e.toFinset).Nonempty := fun e he =>
    hThit e.toFinset (mem_edgeFinsets_hypergraph_iff d n gates o k |>.2 ⟨e, he, rfl⟩)
  -- Block partition: `T` picks exactly one element from `certBlock` and one from each
  -- `bracketBlock`
  let Scert : Finset ℕ := T ∩ (certBlock N_certs).toFinset
  let Sbr : List ℕ → Finset ℕ := fun C => T ∩ (bracketBlock N_certs B C).toFinset
  have hScert_ne : Scert.Nonempty := hedge (certBlock N_certs) (by
    simp only [rawEdgesOf, ← hkk_def, List.mem_append, List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl rfl)))
  have hSbr_ne : ∀ C ∈ IL, (Sbr C).Nonempty := fun C hC =>
    hedge (bracketBlock N_certs B C) (by
      simp only [rawEdgesOf, ← hkk_def, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inr ⟨C, hC, rfl⟩)))
  have hpw : (IL.toFinset : Set (List ℕ)).PairwiseDisjoint Sbr := by
    intro C₁ _ C₂ _ hne
    change Disjoint (Sbr C₁) (Sbr C₂)
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    simp only [Sbr, Finset.mem_inter, List.mem_toFinset, mem_bracketBlock_iff] at hv₁ hv₂
    obtain ⟨j₁, hj₁, hC₁, rfl⟩ := hv₁.2
    obtain ⟨j₂, hj₂, hC₂, hv_eq⟩ := hv₂.2
    have hj_eq : j₁ = j₂ := by dsimp only [N_certs] at *; omega
    subst hj_eq
    exact hne (hC₁.symm.trans hC₂)
  have hdisj_cert : Disjoint Scert (IL.toFinset.biUnion Sbr) := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    simp only [Scert, Finset.mem_inter, List.mem_toFinset, certBlock, List.mem_range] at hv₁
    simp only [Finset.mem_biUnion, Sbr, Finset.mem_inter, List.mem_toFinset,
      mem_bracketBlock_iff] at hv₂
    obtain ⟨C, -, -, ⟨j, -, -, rfl⟩⟩ := hv₂
    dsimp only [N_certs] at *; omega
  let U : Finset ℕ := Scert ∪ IL.toFinset.biUnion Sbr
  have hUT_sub : U ⊆ T := Finset.union_subset Finset.inter_subset_left
    (Finset.biUnion_subset.2 fun _ _ => Finset.inter_subset_left)
  have hUcard_eq : U.card = Scert.card + ∑ C ∈ IL.toFinset, (Sbr C).card := by
    rw [Finset.card_union_of_disjoint hdisj_cert, Finset.card_biUnion hpw]
  have hsum_ge : IL.length ≤ ∑ C ∈ IL.toFinset, (Sbr C).card := by
    calc IL.length = IL.toFinset.card := (List.toFinset_card_of_nodup (nodup_indexLists d kk)).symm
      _ = ∑ _C ∈ IL.toFinset, 1 := by simp
      _ ≤ ∑ C ∈ IL.toFinset, (Sbr C).card := Finset.sum_le_sum fun C hC =>
          Finset.card_pos.2 (hSbr_ne C (List.mem_toFinset.1 hC))
  have hScert_pos : 1 ≤ Scert.card := Finset.card_pos.2 hScert_ne
  have hTcard' : T.card = IL.length + 1 := hTcard
  have hUle : U.card ≤ IL.length + 1 := hTcard' ▸ Finset.card_le_card hUT_sub
  have hScert_one : Scert.card = 1 := by omega
  have hsum_eq : ∑ C ∈ IL.toFinset, (Sbr C).card = IL.length := by omega
  have hUT : U = T := Finset.eq_of_subset_of_card_le hUT_sub (by omega)
  have hSbr_one : ∀ C ∈ IL, (Sbr C).card = 1 := by
    intro C hC
    have hCin : C ∈ IL.toFinset := List.mem_toFinset.2 hC
    by_contra hne1
    have hgt : 2 ≤ (Sbr C).card := by
      have := Finset.card_pos.2 (hSbr_ne C hC); omega
    have hsum_gt : IL.length < ∑ C' ∈ IL.toFinset, (Sbr C').card := by
      calc IL.length = ∑ _C' ∈ IL.toFinset, 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one,
              List.toFinset_card_of_nodup (nodup_indexLists d kk)]
        _ < ∑ C' ∈ IL.toFinset, (Sbr C').card :=
            Finset.sum_lt_sum (fun C' hC' => Finset.card_pos.2
              (hSbr_ne C' (List.mem_toFinset.1 hC'))) ⟨C, hCin, by omega⟩
    omega
  obtain ⟨ic, hic_eq⟩ := Finset.card_eq_one.1 hScert_one
  have hic_mem : ic ∈ Scert := hic_eq ▸ Finset.mem_singleton_self ic
  have hic_lt : ic < N_certs :=
    List.mem_range.1 (List.mem_toFinset.1 (Finset.mem_inter.1 hic_mem).2)
  have hbr_sel : ∀ C ∈ IL, ∃ j, ∃ hj : j < B.length,
      B[j].map Prod.fst = C ∧ Sbr C = {N_certs + j} := by
    intro C hC
    obtain ⟨v, hv_eq⟩ := Finset.card_eq_one.1 (hSbr_one C hC)
    have hv_mem : v ∈ Sbr C := hv_eq ▸ Finset.mem_singleton_self v
    obtain ⟨j, hj, hC_eq, rfl⟩ :=
      mem_bracketBlock_iff.1 (List.mem_toFinset.1 (Finset.mem_inter.1 hv_mem).2)
    exact ⟨j, hj, hC_eq, hv_eq⟩
  choose! jb hjb_lt hjb_fst hjb_eq using hbr_sel
  -- Consistency between selected brackets of distinct index lists
  have hcons_sel : ∀ (C₁ : List ℕ) (hC₁ : C₁ ∈ IL) (C₂' : List ℕ) (hC₂' : C₂' ∈ IL), C₁ ≠ C₂' →
      consistent (B[jb C₁]'(hjb_lt C₁ hC₁)) (B[jb C₂']'(hjb_lt C₂' hC₂')) = true := by
    intro C₁ hC₁ C₂' hC₂' hne
    by_contra hnc
    simp only [Bool.not_eq_true] at hnc
    let e := ((bracketBlock N_certs B C₁).filter fun v => !decide (v = N_certs + jb C₁)) ++
      ((bracketBlock N_certs B C₂').filter fun v => !decide (v = N_certs + jb C₂'))
    have he_mem : e ∈ rawEdgesOf d n gates o k := by
      simp only [rawEdgesOf, ← hkk_def, List.mem_append]
      refine Or.inl (Or.inr ?_)
      simp only [consistencyEdges, List.mem_flatMap]
      refine ⟨(B[jb C₁]'(hjb_lt C₁ hC₁), jb C₁), mem_zipIdx_iff.2 ⟨hjb_lt C₁ hC₁, rfl⟩,
        (B[jb C₂']'(hjb_lt C₂' hC₂'), jb C₂'), mem_zipIdx_iff.2 ⟨hjb_lt C₂' hC₂', rfl⟩, ?_⟩
      simp only [hjb_fst C₁ hC₁, hjb_fst C₂' hC₂', hne, decide_false, Bool.not_false, hnc,
        Bool.and_self, ↓reduceIte, List.mem_singleton]
      rfl
    obtain ⟨v, hv⟩ := hedge e he_mem
    rw [Finset.mem_inter, ← hUT, List.mem_toFinset] at hv
    rcases List.mem_append.1 hv.2 with hv₁ | hv₂
    · obtain ⟨hvb, hvne⟩ := List.mem_filter.1 hv₁
      have hvS : v ∈ Sbr C₁ := Finset.mem_inter.2 ⟨hUT ▸ hv.1, List.mem_toFinset.2 hvb⟩
      rw [hjb_eq C₁ hC₁, Finset.mem_singleton] at hvS
      simp [hvS] at hvne
    · obtain ⟨hvb, hvne⟩ := List.mem_filter.1 hv₂
      have hvS : v ∈ Sbr C₂' := Finset.mem_inter.2 ⟨hUT ▸ hv.1, List.mem_toFinset.2 hvb⟩
      rw [hjb_eq C₂' hC₂', Finset.mem_singleton] at hvS
      simp [hvS] at hvne
  -- Read `u : ℕ → ℕ` from singleton index lists `[j]`
  have hjIL_of : ∀ {j}, j < kk → [j] ∈ IL := fun hj =>
    mem_indexLists.2 ⟨by simp [Nat.one_le_two_pow], by simpa using hj⟩
  have hsing : ∀ (j : ℕ), ∀ (hj : j < kk), ∃ s,
      B[jb [j]]'(hjb_lt [j] (hjIL_of hj)) = [(j, s)] ∧ s < n := by
    intro j hj
    obtain ⟨⟨j', s⟩, hP, hj'⟩ := List.map_eq_singleton_iff.1 (hjb_fst [j] (hjIL_of hj))
    rw [show j' = j from hj'] at hP
    have hBmem : B[jb [j]]'(hjb_lt [j] (hjIL_of hj)) ∈ B := List.getElem_mem _
    have hs : s < n := ((mem_brackets.1 hBmem).2 (j, s) (hP ▸ List.mem_singleton_self _)).2
    exact ⟨s, hP, hs⟩
  choose! u hu_eq hun using hsing
  have hpairs : ∀ C (hC : C ∈ IL) p, p ∈ B[jb C]'(hjb_lt C hC) → p.1 < kk ∧ p.2 = u p.1 := by
    intro C hC p hp
    have hBmem : B[jb C]'(hjb_lt C hC) ∈ B := List.getElem_mem _
    have hp1 : p.1 < kk := ((mem_brackets.1 hBmem).2 p hp).1
    refine ⟨hp1, ?_⟩
    have hjIL : [p.1] ∈ IL := hjIL_of hp1
    by_cases hCeq : C = [p.1]
    · subst hCeq
      rw [hu_eq p.1 hp1, List.mem_singleton] at hp
      exact congrArg Prod.snd hp
    · have hcons := hcons_sel C hC [p.1] hjIL hCeq
      have hok := consistent_iff.1 hcons p hp (p.1, u p.1)
        (by rw [hu_eq p.1 hp1]; exact List.mem_singleton_self _)
      exact ((pairOk_iff _ _).1 hok).1.1 rfl
  have hmono : StrictMonoOn u (Set.Iio kk) := by
    intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    have hiIL : [i] ∈ IL := hjIL_of hi
    have hjIL : [j] ∈ IL := hjIL_of hj
    have hcons := hcons_sel [i] hiIL [j] hjIL (by simp; omega)
    have hok := consistent_iff.1 hcons (i, u i)
      (by rw [hu_eq i hi]; exact List.mem_singleton_self _) (j, u j)
      (by rw [hu_eq j hj]; exact List.mem_singleton_self _)
    exact ((pairOk_iff _ _).1 hok).2.1 hij
  have hkk_eq : kk = k := by
    have := (weight_selectedBits hmono hun).symm.trans_le (BitString.weight_le_length _)
    omega
  have hB_true : ∀ C (hC : C ∈ IL), B[jb C]'(hjb_lt C hC) = C.map fun j => (j, u j) :=
    fun C hC => eq_map_pair_of_map_fst (hjb_fst C hC) fun p hp => (hpairs C hC p hp).2
  -- Verify all checks of `cl₂ := C₂[ic]` hold on `selectedBits n kk u`
  set cl₂ := C₂[ic]
  have hcl₂_mem : cl₂ ∈ C₂ := List.getElem_mem hic_lt
  refine ⟨selectedBits n kk u, hkk_eq ▸ weight_selectedBits hmono hun, ?_⟩
  rw [c.eval_eq_getD interpretation false]
  refine eval_eq_of_kleeneEval_override c.isCodeFrom_code (kleeneEval_of_mem_certsSucc hcl₂_mem)
    List.length_ofFn ?_
  intro e he
  obtain ⟨he_lt, he_wft, he_dp⟩ :=
    check_bounds_of_mem_certsSucc c.isCodeFrom_code hcl₂_mem he
  rw [eval_selectedBits_eq_iff_forall_certsOne_refutes c.isCodeFrom_code hmono he_lt he_wft he_dp]
  intro cl₁ hcl₁
  let er := ((certBlock N_certs).filter fun v => !decide (v = ic)) ++
    ((B.zipIdx.filter fun q => refutes n kk gates cl₁ q.1).map fun q => N_certs + q.2)
  have her_mem : er ∈ rawEdgesOf d n gates o k := by
    simp only [rawEdgesOf, ← hkk_def, List.mem_append]
    refine Or.inr ?_
    simp only [refutationEdges, List.mem_flatMap, List.mem_map]
    exact ⟨(cl₂, ic), mem_zipIdx_iff.2 ⟨hic_lt, rfl⟩, e, List.mem_flatMap.1 he, cl₁, hcl₁, rfl⟩
  obtain ⟨v, hv⟩ := hedge er her_mem
  rw [Finset.mem_inter, ← hUT, List.mem_toFinset] at hv
  rcases List.mem_append.1 hv.2 with hv_cert | hv_br
  · obtain ⟨hvc, hvne⟩ := List.mem_filter.1 hv_cert
    have hvS : v ∈ Scert := Finset.mem_inter.2 ⟨hUT ▸ hv.1, List.mem_toFinset.2 hvc⟩
    rw [hic_eq, Finset.mem_singleton] at hvS
    simp [hvS] at hvne
  · simp only [List.mem_map, List.mem_filter, Prod.exists, mem_zipIdx_iff] at hv_br
    obtain ⟨P, j, ⟨⟨hj, rfl⟩, href_true⟩, rfl⟩ := hv_br
    rcases Finset.mem_union.1 hv.1 with hvc | hvbr
    · have : N_certs + j < N_certs :=
        List.mem_range.1 (List.mem_toFinset.1 (Finset.mem_inter.1 hvc).2)
      omega
    · obtain ⟨C, hC_fin, hvS⟩ := Finset.mem_biUnion.1 hvbr
      have hC : C ∈ IL := List.mem_toFinset.1 hC_fin
      rw [hjb_eq C hC, Finset.mem_singleton] at hvS
      have hj_eq : j = jb C := by dsimp only [N_certs] at *; omega
      subst hj_eq
      rw [hB_true C hC] at href_true
      exact ⟨C, hC, href_true⟩

/-- **Correctness of `toHittingSet`.** -/
theorem toHittingSet_mem_HittingSet_iff {d : ℕ} (x : WCSInstance 2 d) :
    toHittingSet x ∈ HittingSet ↔ x ∈ WCS 2 d := by
  obtain ⟨⟨⟨n, c⟩, hw, hd⟩, k⟩ := x
  rw [mem_WCS]
  exact ⟨satisfiableWithWeight_of_mem_HittingSet c,
    fun ⟨y, hy, hc⟩ => mem_HittingSet_of_eval c hw hd y hy hc⟩

/-! ### Polynomial-time computability of `toHittingSet` -/

section PolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

private theorem computableInPolyTime_unaryList_to_natList {f : γ → List ℕ}
    (hf : ComputableInPolyTime f encIn (encList encUnary)) :
    ComputableInPolyTime f encIn (encList encNat) :=
  ((ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp hf).of_enc_eq fun a => by
    simp

private theorem computableInPolyTime_unaryList2_to_natList2 {f : γ → List (List ℕ)}
    (hf : ComputableInPolyTime f encIn (encList (encList encUnary))) :
    ComputableInPolyTime f encIn (encList (encList encNat)) :=
  ((ComputableInPolyTime.map
    (ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary)).comp hf).of_enc_eq fun a => by
    dsimp only [Function.comp_apply]
    induction f a with
    | nil => rfl
    | cons l ls ih => simp [ih]

private theorem computableInPolyTime_bracketBlock
    {nc : γ → ℕ} {B : γ → List (List (ℕ × ℕ))} {C : γ → List ℕ}
    (hnc : ComputableInPolyTime nc encIn encUnary)
    (hB : ComputableInPolyTime B encIn (encList (encList (encPair encUnary encUnary))))
    (hC : ComputableInPolyTime C encIn (encList encUnary)) :
    ComputableInPolyTime (fun a => bracketBlock (nc a) (B a) (C a)) encIn (encList encUnary) := by
  unfold bracketBlock
  polytime

attribute [local fun_prop] computableInPolyTime_consistent computableInPolyTime_bracketBlock in
private theorem computableInPolyTime_consistencyEdges
    {nc : γ → ℕ} {B : γ → List (List (ℕ × ℕ))}
    (hnc : ComputableInPolyTime nc encIn encUnary)
    (hB : ComputableInPolyTime B encIn (encList (encList (encPair encUnary encUnary)))) :
    ComputableInPolyTime (fun a => consistencyEdges (nc a) (B a)) encIn
      (encList (encList encUnary)) := by
  unfold consistencyEdges
  polytime

attribute [local fun_prop] computableInPolyTime_refutes_poly in
private theorem computableInPolyTime_refutationEdges (d : ℕ)
    {n kk : γ → ℕ} {gates : γ → List (Op × List ℕ)}
    {C₂ : γ → List (List (ℕ × Bool))} {B : γ → List (List (ℕ × ℕ))}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hkk : ComputableInPolyTime kk encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp)))
    (hC₂ : ComputableInPolyTime C₂ encIn (encList (encList (encPair encUnary encBool))))
    (hB : ComputableInPolyTime B encIn (encList (encList (encPair encUnary encUnary)))) :
    ComputableInPolyTime (fun a => refutationEdges d (n a) (kk a) (gates a) (C₂ a) (B a))
      encIn (encList (encList encUnary)) := by
  unfold refutationEdges certBlock
  refine ComputableInPolyTime.flatMapWithInput (by fun_prop) ?_
  refine ComputableInPolyTime.flatMapWithInput
    (WeftOne.computableInPolyTime_checks (hn.comp (by fun_prop)) (hg.comp (by fun_prop))
      (by fun_prop)) ?_
  refine ComputableInPolyTime.mapWithInput
    (computableInPolyTime_certsOne d (hn.comp (by fun_prop)) (hg.comp (by fun_prop))
      ((ComputableInPolyTime.fst encNat encBool).comp (ComputableInPolyTime.snd _ _))
      (by polytime)) ?_
  polytime

private theorem computableInPolyTime_rawEdgesOf_aux
    {nc : γ → ℕ} {IL : γ → List (List ℕ)} {B : γ → List (List (ℕ × ℕ))}
    {cons ref : γ → List (List ℕ)}
    (hnc : ComputableInPolyTime nc encIn encUnary)
    (hIL : ComputableInPolyTime IL encIn (encList (encList encUnary)))
    (hB : ComputableInPolyTime B encIn (encList (encList (encPair encUnary encUnary))))
    (hcons : ComputableInPolyTime cons encIn (encList (encList encUnary)))
    (href : ComputableInPolyTime ref encIn (encList (encList encUnary))) :
    ComputableInPolyTime (fun a => [certBlock (nc a)] ++
      (IL a).map (bracketBlock (nc a) (B a)) ++ cons a ++ ref a) encIn
      (encList (encList encNat)) :=
  computableInPolyTime_unaryList2_to_natList2
    ((((ComputableInPolyTime.cons' (ComputableInPolyTime.range.comp hnc) (.const [])).listAppend'
      (hIL.mapWithInput (computableInPolyTime_bracketBlock
        (hnc.comp (ComputableInPolyTime.fst _ _)) (hB.comp (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.snd _ _)))).listAppend' hcons).listAppend' href)

private theorem computableInPolyTime_rawEdgesOf (d : ℕ)
    {n o k : γ → ℕ} {gates : γ → List (Op × List ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hg : ComputableInPolyTime gates encIn (encList (Circuit.encGate encOp)))
    (ho : ComputableInPolyTime o encIn encNat)
    (hk : ComputableInPolyTime k encIn encNat) :
    ComputableInPolyTime (fun a => rawEdgesOf d (n a) (gates a) (o a) (k a)) encIn
      (encList (encList encNat)) := by
  have hkk : ComputableInPolyTime (fun a => min (n a + 1) (k a)) encIn encUnary := by fun_prop
  have hC₂ := computableInPolyTime_certsSucc 1 d hn hg ho (ComputableInPolyTime.const true)
  have hB := computableInPolyTime_brackets_poly d hn hkk
  have hIL := computableInPolyTime_indexLists_poly d hkk
  have hnc : ComputableInPolyTime (fun a => (certsSucc 1 d (n a) (gates a) (o a) true).length)
      encIn encUnary := (ComputableInPolyTime.length_list _).comp hC₂
  unfold rawEdgesOf
  exact computableInPolyTime_rawEdgesOf_aux hnc hIL hB
    (computableInPolyTime_consistencyEdges hnc hB)
    (computableInPolyTime_refutationEdges d hn hkk hg hC₂ hB)

/-- `toHittingSet` is polynomial-time for every fixed depth `d`. -/
theorem computableInPolyTime_toHittingSet (d : ℕ) :
    ComputableInPolyTime (toHittingSet (d := d)) (encWCS 2 d) encHittingSetInstance := by
  open scoped HittingSetInstance FinHypergraph in
  have hwc := encWCS_circuit_polyTime (t := 2) (d := d) .id'
  have hn := WeftCircuit.computableInPolyTime_numInputs hwc
  have hg := WeftCircuit.computableInPolyTime_gates hwc
  have houts := WeftCircuit.computableInPolyTime_outputs hwc
  have hk := encWCS_weight_polyTime (t := 2) (d := d) .id'
  have ho : ComputableInPolyTime (fun x : WCSInstance 2 d => x.circuit.toCircuit.2.code.2.getD 0 0)
      (encWCS 2 d) encNat := by fun_prop
  have hkk : ComputableInPolyTime
      (fun x : WCSInstance 2 d => min (x.circuit.toCircuit.1 + 1) x.weight)
      (encWCS 2 d) encUnary := by fun_prop
  have hC₂ := computableInPolyTime_certsSucc 1 d hn hg ho (ComputableInPolyTime.const true)
  have hB := computableInPolyTime_brackets_poly d hn hkk
  have htail : ComputableInPolyTime
      (fun x : WCSInstance 2 d =>
        List.range ((certsSucc 1 d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
          (x.circuit.toCircuit.2.code.2.getD 0 0) true).length +
          (brackets d x.circuit.toCircuit.1 (min (x.circuit.toCircuit.1 + 1) x.weight)).length))
      (encWCS 2 d) (encList encNat) :=
    computableInPolyTime_unaryList_to_natList
      (ComputableInPolyTime.range.comp (ComputableInPolyTime.unary_add'
        ((ComputableInPolyTime.length_list _).comp hC₂)
        ((ComputableInPolyTime.length_list _).comp hB)))
  have hraw := computableInPolyTime_rawEdgesOf d hn hg ho hk
  have hsize : ComputableInPolyTime
      (fun x : WCSInstance 2 d => size d x.circuit.toCircuit.1 x.weight)
      (encWCS 2 d) encNat := by
    unfold size
    exact ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_add'
        ((ComputableInPolyTime.length_list _).comp (computableInPolyTime_indexLists_poly d hkk))
        (.const 1))
  have hmk : ∀ (f2 : WCSInstance 2 d → List ℕ) (f3 : WCSInstance 2 d → List (List ℕ))
      (fk : WCSInstance 2 d → ℕ),
      ComputableInPolyTime f2 (encWCS 2 d) (encList encNat) →
      ComputableInPolyTime f3 (encWCS 2 d) (encList (encList encNat)) →
      ComputableInPolyTime fk (encWCS 2 d) encNat →
      ComputableInPolyTime (fun x => HittingSetInstance.mk ⟨0, f2 x, f3 x⟩ (fk x))
        (encWCS 2 d) encHittingSetInstance := by
    intros; fun_prop
  have heq : (toHittingSet (d := d)) = fun x : WCSInstance 2 d =>
      ⟨hypergraph d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
        (x.circuit.toCircuit.2.code.2.getD 0 0) x.weight,
        size d x.circuit.toCircuit.1 x.weight⟩ := by
    funext x
    simp [toHittingSet, Circuit.code]
  rw [heq]
  exact hmk _ _ _ htail hraw hsize

end PolyTime

end WCSToHittingSet

/-- **For every fixed depth `d`, `WCS 2 d` FPT-reduces to `HittingSet`** with parameter bound
`k' ≤ (k + 1) ^ 2 ^ (d + 1) + 1`. -/
theorem fptReducible_WCS_HittingSet (d : ℕ) :
    FPTReducible (encWCS 2 d) encHittingSetInstance WCSInstance.weight (·.k)
      (WCS 2 d) HittingSet :=
  FPTReducible.of_computableInPolyTime (WCSToHittingSet.computableInPolyTime_toHittingSet d)
    (h := fun k => (k + 1) ^ 2 ^ (d + 1) + 1) (fun _ => size_le d _ _)
    fun x => (WCSToHittingSet.toHittingSet_mem_HittingSet_iff x).symm

/-- **`HittingSet` is `W[2]`-hard**. -/
theorem HittingSet_wHard : WHard 2 encHittingSetInstance (·.k) HittingSet :=
  wHard_iff.2 fptReducible_WCS_HittingSet

/-- **`WS2` is `W[2]`-hard**. -/
theorem WS2_wHard : WHard 2 encWS2Instance (·.k) WS2 :=
  HittingSet_wHard.trans fptReducible_HittingSet_WS2

/-- **`W[2] = FPT` if and only if `HittingSet ∈ FPT`**. -/
theorem W_two_eq_FPT_iff :
    (∀ ⦃α : Type⦄ (enc : α ↪ List Bool) (κ : α → ℕ), W 2 enc κ = FPT enc κ) ↔
      HittingSet ∈ FPT encHittingSetInstance (·.k) :=
  ⟨fun h => h _ _ ▸ HittingSet_mem_W,
    fun h _ _ _ => Set.Subset.antisymm (HittingSet_wHard.subset_FPT h) (FPT_subset_W 2)⟩

section Witnesses

private theorem hittingSet_nondegenerate_example :
    ∃ x : HittingSetInstance, x.k = 2 ∧ x ∈ HittingSet ∧ hittingSetToWS2 x ∈ WS2 := by
  let H : FinHypergraph := ⟨0, [1, 2, 3], [[0, 1], [2, 3], [1, 2]]⟩
  have hmem : (⟨H, 2⟩ : HittingSetInstance) ∈ HittingSet := by
    refine ⟨{1, 2}, ⟨?_, ?_⟩, by decide⟩
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rw [FinHypergraph.mem_vertexSet, FinHypergraph.mem_distinctVertices]
      rcases hv with rfl | rfl <;> simp [H]
    · intro E hE
      have hE_eq : H.edgeFinsets = {{0, 1}, {2, 3}, {1, 2}} := by decide
      rw [hE_eq] at hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl | rfl
      · exact ⟨1, by decide⟩
      · exact ⟨2, by decide⟩
      · exact ⟨1, by decide⟩
  exact ⟨⟨H, 2⟩, rfl, hmem, (hittingSetToWS2_mem_WS2_iff ⟨H, 2⟩).2 hmem⟩

end Witnesses

end CslibFrontier.ParameterizedComplexity
