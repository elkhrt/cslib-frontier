/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.SharpIndepSet
public import Mathlib.Order.Minimal

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# `#P`-Completeness of Counting Maximal Independent Sets (`#MaximalIndependentSet`)

This module formalizes the counting problem `#MaximalIndependentSet` (`SharpMaximalIndepSet`) on
encoded simple graphs (`Cslib.Complexity.Graph` under `encGraph`), proving under standard Lean
axioms that `SharpMaximalIndepSet` belongs to `#P`, admits a parsimonious reduction from
`SharpIndepSet` by attaching a degree-`1` pendant vertex to each declared vertex, and is
`#P`-complete under polynomial-time counting Turing reductions (`CountingTuringComplete`).

## Main definitions

- `CslibFrontier.Complexity.maximalIndepFinsets`, `CslibFrontier.Complexity.SharpMaximalIndepSet`:
  the finite
  set and count of inclusion-maximal independent subsets of declared vertices of a graph `G`.
- `CslibFrontier.Complexity.pendantGraph`: attaching a degree-`1` pendant vertex `2 * v + 1` to each
  declared vertex `2 * v` of `G`.

## Main results

- `CslibFrontier.Complexity.mem_maximalIndepFinsets_iff`: characterization of
  `maximalIndepFinsets G`.
- `CslibFrontier.Complexity.SharpMaximalIndepSet_mem_SharpP`:
  `SharpMaximalIndepSet ∈ SharpP encGraph`.
- `CslibFrontier.Complexity.SharpMaximalIndepSet_pendantGraph`,
  `CslibFrontier.Complexity.parsimoniousReducible_SharpIndepSet_SharpMaximalIndepSet`: attaching
  pendant
  vertices preserves counts bijectively (`SharpIndepSet ≤_pars SharpMaximalIndepSet`).
- `CslibFrontier.Complexity.countingTuringHard_of_add_offset_SharpMaximalIndepSet`: transfer of
  `#P`-hardness from `SharpMaximalIndepSet` along polynomial-time reductions with `{0, 1}` offsets.
- `CslibFrontier.Complexity.SharpMaximalIndepSet_countingTuringComplete`: `#P`-completeness of
  `SharpMaximalIndepSet`.
- `CslibFrontier.Complexity.SharpMaximalIndepSet_polyTime_implies_P_eq_NP`: if
  `SharpMaximalIndepSet ∈ FP`, then `P = NP`.

## Tags

computational complexity, SharpP, counting complexity, maximal independent set
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM

/-- The finite set of all inclusion-maximal independent subsets of declared vertices of `G`. -/
def maximalIndepFinsets (G : Graph) : Finset (Finset ℕ) :=
  (indepFinsets G).filter fun S ↦
    ∀ v ∈ G.distinctVertices, v ∈ S ∨ ∃ u ∈ S, G.adjBool u v = true

/-- Membership in `maximalIndepFinsets G` coincides with inclusion-maximality among independent
subsets of `G.vertices`. -/
theorem mem_maximalIndepFinsets_iff {G : Graph} {S : Finset ℕ} :
    S ∈ maximalIndepFinsets G ↔
      Maximal (fun T : Finset ℕ ↦
        (∀ v ∈ T, v ∈ G.vertices) ∧ G.toSimpleGraph.IsIndepSet (T : Set ℕ)) S := by
  simp only [maximalIndepFinsets, Finset.mem_filter, mem_indepFinsets_iff,
    Graph.adjBool_eq_true_iff, Graph.mem_distinctVertices, Maximal]
  refine and_congr_right fun ⟨hS_sub, hS_ind⟩ ↦ ⟨fun hdom T ⟨hT_sub, hT_ind⟩ hST v hvT ↦ ?_,
    fun hmax v hvG ↦ ?_⟩
  · rcases hdom v (hT_sub v hvT) with hvS | ⟨u, huS, hadj⟩
    · exact hvS
    · have huT : u ∈ T := hST huS
      exact False.elim (hT_ind huT hvT hadj.ne hadj)
  · by_cases hvS : v ∈ S
    · exact Or.inl hvS
    · refine Or.inr ?_
      by_contra hno
      push Not at hno
      have hins_sub : ∀ w ∈ insert v S, w ∈ G.vertices := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwS
        · exact hvG
        · exact hS_sub w hwS
      have hins_ind : G.toSimpleGraph.IsIndepSet ((insert v S : Finset ℕ) : Set ℕ) := by
        intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
        rcases hx with rfl | hxS <;> rcases hy with rfl | hyS
        · exact False.elim (hxy rfl)
        · exact fun hadj ↦ hno y hyS hadj.symm
        · exact fun hadj ↦ hno x hxS hadj
        · exact hS_ind hxS hyS hxy
      have hle : insert v S ≤ S :=
        hmax ⟨hins_sub, hins_ind⟩ (Finset.subset_insert v S)
      exact hvS (hle (Finset.mem_insert_self v S))

/-- Number of inclusion-maximal independent subsets of declared vertices of `G`
(`#MaximalIndependentSet`). -/
def SharpMaximalIndepSet (G : Graph) : ℕ :=
  (maximalIndepFinsets G).card

/-- The cardinality of `maximalIndepFinsets G` is `SharpMaximalIndepSet G`. -/
theorem card_maximalIndepFinsets (G : Graph) :
    (maximalIndepFinsets G).card = SharpMaximalIndepSet G := by rfl

/-- `#MaximalIndependentSet` belongs to `#P`. -/
theorem SharpMaximalIndepSet_mem_SharpP : SharpMaximalIndepSet ∈ SharpP encGraph := by
  let check (p : Graph × List ℕ) : Bool :=
    p.1.distinctVertices.all fun v ↦ p.2.any fun u ↦ decide (u = v) || p.1.adjBool u v
  have hcheck : ComputableInPolyTime check (encWithEntries encGraph encNat) encBool := by
    unfold check encWithEntries
    fun_prop
  refine sharpP_of_indepFinsets_filter _ check hcheck fun G l _ _ _ ↦ ?_
  simp only [check, List.all_eq_true, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.mem_toFinset]
  refine forall₂_congr fun v _ ↦ ?_
  exact ⟨fun ⟨u, hu, h⟩ ↦ h.elim (fun huv ↦ Or.inl (huv ▸ hu)) (fun ha ↦ Or.inr ⟨u, hu, ha⟩),
    fun h ↦ h.elim (fun hv ↦ ⟨v, hv, Or.inl rfl⟩) (fun ⟨u, hu, ha⟩ ↦ ⟨u, hu, Or.inr ha⟩)⟩

/-! ### Pendant-vertex parsimonious reduction `#IndependentSet ≤_pars #MaximalIndependentSet` -/

/-- Attach a pendant vertex `2 * v + 1` adjacent only to `2 * v` for each distinct declared vertex
`v` of `G`, placing the original graph on the even vertices `2 * v`. -/
def pendantGraph (G : Graph) : Graph where
  vertices := G.distinctVertices.flatMap fun v ↦ [2 * v, 2 * v + 1]
  edges := (G.edges.map fun e ↦ (2 * e.1, 2 * e.2)) ++
    (G.distinctVertices.map fun v ↦ (2 * v, 2 * v + 1))

private lemma mem_vertices_pendantGraph {G : Graph} {w : ℕ} :
    w ∈ (pendantGraph G).vertices ↔
      ∃ v ∈ G.distinctVertices, w = 2 * v ∨ w = 2 * v + 1 := by
  simp only [pendantGraph, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]

private lemma pendantGraph_adj_even_even {G : Graph} {u v : ℕ} :
    (pendantGraph G).toSimpleGraph.Adj (2 * u) (2 * v) ↔ G.toSimpleGraph.Adj u v := by
  simp only [Graph.toSimpleGraph_adj, pendantGraph, List.mem_append, List.mem_map, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨_, (⟨a, b, hab, ha, hb⟩ | ⟨a, _, ha, hb⟩) | (⟨a, b, hab, ha, hb⟩ | ⟨a, _, ha, hb⟩)⟩
    · refine ⟨by omega, Or.inl ?_⟩
      have : a = u ∧ b = v := ⟨by omega, by omega⟩
      exact this.1 ▸ this.2 ▸ hab
    · omega
    · refine ⟨by omega, Or.inr ?_⟩
      have : a = v ∧ b = u := ⟨by omega, by omega⟩
      exact this.1 ▸ this.2 ▸ hab
    · omega
  · rintro ⟨_, hab | hba⟩
    · exact ⟨by omega, Or.inl (Or.inl ⟨u, v, hab, rfl, rfl⟩)⟩
    · exact ⟨by omega, Or.inr (Or.inl ⟨v, u, hba, rfl, rfl⟩)⟩

private lemma pendantGraph_adj_even_odd {G : Graph} {u v : ℕ} (hv : v ∈ G.distinctVertices) :
    (pendantGraph G).toSimpleGraph.Adj (2 * u) (2 * v + 1) ↔ u = v := by
  simp only [Graph.toSimpleGraph_adj, pendantGraph, List.mem_append, List.mem_map, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨_, (⟨a, b, _, _, hb⟩ | ⟨a, _, ha, hb⟩) | (⟨a, b, _, ha, _⟩ | ⟨a, _, ha, _⟩)⟩ <;> omega
  · rintro rfl
    exact ⟨by omega, Or.inl (Or.inr ⟨u, hv, rfl, rfl⟩)⟩

private lemma pendantGraph_not_adj_odd_odd {G : Graph} {u v : ℕ} :
    ¬(pendantGraph G).toSimpleGraph.Adj (2 * u + 1) (2 * v + 1) := by
  simp only [Graph.toSimpleGraph_adj, pendantGraph, List.mem_append, List.mem_map, Prod.exists,
    Prod.mk.injEq]
  rintro ⟨_, (⟨a, b, _, ha, _⟩ | ⟨a, _, ha, _⟩) | (⟨a, b, _, ha, _⟩ | ⟨a, _, ha, _⟩)⟩ <;> omega

/-- Attaching pendant vertices preserves the count of independent sets as maximal independent sets:
`SharpMaximalIndepSet (pendantGraph G) = SharpIndepSet G`. -/
theorem SharpMaximalIndepSet_pendantGraph (G : Graph) :
    SharpMaximalIndepSet (pendantGraph G) = SharpIndepSet G := by
  rw [← card_maximalIndepFinsets, ← card_indepFinsets]
  let dvSet := G.distinctVertices.toFinset
  let liftSet (S : Finset ℕ) : Finset ℕ :=
    S.image (2 * ·) ∪ (dvSet \ S).image (fun v ↦ 2 * v + 1)
  refine (Finset.card_bij (fun S _ ↦ liftSet S)
    (fun S hS ↦ ?_) (fun S₁ _ S₂ _ heq ↦ ?_) (fun M hM ↦ ?_)).symm
  · obtain ⟨hS_sub, hS_ind⟩ := mem_indepFinsets_iff.mp hS
    rw [mem_maximalIndepFinsets_iff]
    have hlift_sub : ∀ w ∈ liftSet S, w ∈ (pendantGraph G).vertices := by
      intro w hw
      rw [mem_vertices_pendantGraph]
      simp only [liftSet, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff, dvSet,
        List.mem_toFinset] at hw
      rcases hw with ⟨v, hvS, rfl⟩ | ⟨v, ⟨hv, _⟩, rfl⟩
      · exact ⟨v, Graph.mem_distinctVertices.mpr (hS_sub v hvS), Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr rfl⟩
    have hlift_ind : (pendantGraph G).toSimpleGraph.IsIndepSet (liftSet S : Set ℕ) := by
      intro x hx y hy _
      simp only [Finset.mem_coe, liftSet, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff,
        dvSet, List.mem_toFinset] at hx hy
      rcases hx with ⟨u, huS, rfl⟩ | ⟨u, ⟨hu, huNS⟩, rfl⟩ <;>
        rcases hy with ⟨v, hvS, rfl⟩ | ⟨v, ⟨hv, hvNS⟩, rfl⟩
      · rw [pendantGraph_adj_even_even]
        exact hS_ind huS hvS (by omega)
      · rw [pendantGraph_adj_even_odd hv]
        exact fun huv ↦ hvNS (huv ▸ huS)
      · rw [SimpleGraph.adj_comm, pendantGraph_adj_even_odd hu]
        exact fun hvu ↦ huNS (hvu ▸ hvS)
      · exact pendantGraph_not_adj_odd_odd
    refine ⟨⟨hlift_sub, hlift_ind⟩, fun T ⟨hT_sub, hT_ind⟩ hST w hwT ↦ ?_⟩
    obtain ⟨v, hv, rfl | rfl⟩ := mem_vertices_pendantGraph.mp (hT_sub w hwT)
    · by_cases hvS : v ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hvS)
      · have hodd : 2 * v + 1 ∈ T := hST (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hv, hvS⟩)))
        have hadj := (pendantGraph_adj_even_odd hv).mpr rfl
        exact False.elim (hT_ind hwT hodd (by omega) hadj)
    · by_cases hvS : v ∈ S
      · have heven : 2 * v ∈ T := hST (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hvS))
        have hadj := (pendantGraph_adj_even_odd hv).mpr rfl
        exact False.elim (hT_ind heven hwT (by omega) hadj)
      · exact Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hv, hvS⟩))
  · ext v
    have hmem (S : Finset ℕ) : 2 * v ∈ liftSet S ↔ v ∈ S := by
      simp only [liftSet, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (⟨u, hu, he⟩ | ⟨u, _, he⟩)
        · exact (show u = v by omega) ▸ hu
        · omega
      · intro hv
        exact Or.inl ⟨v, hv, rfl⟩
    rw [← hmem S₁, ← hmem S₂, heq]
  · obtain ⟨⟨hM_sub, hM_ind⟩, hM_max⟩ := mem_maximalIndepFinsets_iff.mp hM
    let S := dvSet.filter fun v ↦ 2 * v ∈ M
    have hS_ind : S ∈ indepFinsets G := by
      rw [mem_indepFinsets_iff]
      refine ⟨fun v hv ↦ ?_, fun u hu v hv _ ↦ ?_⟩
      · simp only [S, Finset.mem_filter, dvSet, List.mem_toFinset, Graph.mem_distinctVertices] at hv
        exact hv.1
      · simp only [Finset.mem_coe, S, Finset.mem_filter] at hu hv
        rw [← pendantGraph_adj_even_even]
        exact hM_ind hu.2 hv.2 (by omega)
    refine ⟨S, hS_ind, ?_⟩
    ext w
    simp only [liftSet, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff, S,
      Finset.mem_filter, dvSet, List.mem_toFinset]
    constructor
    · rintro (⟨v, ⟨_, hvM⟩, rfl⟩ | ⟨v, ⟨hv, hvnot⟩, rfl⟩)
      · exact hvM
      · have hvNM : 2 * v ∉ M := fun hm ↦ hvnot ⟨hv, hm⟩
        by_contra hoddNM
        have hins_sub : ∀ x ∈ insert (2 * v + 1) M, x ∈ (pendantGraph G).vertices := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxM
          · exact mem_vertices_pendantGraph.mpr ⟨v, hv, Or.inr rfl⟩
          · exact hM_sub x hxM
        have hins_ind :
            (pendantGraph G).toSimpleGraph.IsIndepSet
              ((insert (2 * v + 1) M : Finset ℕ) : Set ℕ) := by
          intro x hx y hy hxy
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
          rcases hx with rfl | hxM <;> rcases hy with rfl | hyM
          · exact False.elim (hxy rfl)
          · obtain ⟨u, _, rfl | rfl⟩ := mem_vertices_pendantGraph.mp (hM_sub y hyM)
            · rw [SimpleGraph.adj_comm, pendantGraph_adj_even_odd hv]
              exact fun huv ↦ hvNM (huv ▸ hyM)
            · exact pendantGraph_not_adj_odd_odd
          · obtain ⟨u, _, rfl | rfl⟩ := mem_vertices_pendantGraph.mp (hM_sub x hxM)
            · rw [pendantGraph_adj_even_odd hv]
              exact fun huv ↦ hvNM (huv ▸ hxM)
            · exact pendantGraph_not_adj_odd_odd
          · exact hM_ind hxM hyM hxy
        exact hoddNM (hM_max ⟨hins_sub, hins_ind⟩ (Finset.subset_insert _ _)
          (Finset.mem_insert_self _ _))
    · intro hwM
      obtain ⟨v, hv, rfl | rfl⟩ := mem_vertices_pendantGraph.mp (hM_sub w hwM)
      · exact Or.inl ⟨v, ⟨hv, hwM⟩, rfl⟩
      · refine Or.inr ⟨v, ⟨hv, fun ⟨_, heven⟩ ↦ ?_⟩, rfl⟩
        exact hM_ind heven hwM (by omega) ((pendantGraph_adj_even_odd hv).mpr rfl)

/-- `pendantGraph` is computable in polynomial time on encoded graphs. -/
@[fun_prop]
theorem computableInPolyTime_pendantGraph :
    ComputableInPolyTime pendantGraph encGraph encGraph := by
  have hdouble : ComputableInPolyTime (fun v : ℕ ↦ 2 * v) encNat encNat := by
    rw [show (fun v : ℕ ↦ 2 * v) = fun v ↦ v + v from funext two_mul]
    exact .binary_add' .id' .id'
  have hdv := Graph.computableInPolyTime_distinctVertices
  have hverts : ComputableInPolyTime (fun G : Graph ↦ (pendantGraph G).vertices)
      encGraph (encList encNat) := by
    change ComputableInPolyTime
      (fun G : Graph ↦ G.distinctVertices.flatMap fun v ↦ [2 * v, 2 * v + 1])
      encGraph (encList encNat)
    fun_prop
  have hedges : ComputableInPolyTime (fun G : Graph ↦ (pendantGraph G).edges)
      encGraph (encList (encPair encNat encNat)) := by
    change ComputableInPolyTime
      (fun G : Graph ↦ (G.edges.map fun e ↦ (2 * e.1, 2 * e.2)) ++
        (G.distinctVertices.map fun v ↦ (2 * v, 2 * v + 1)))
      encGraph (encList (encPair encNat encNat))
    fun_prop
  exact encGraph_mk_polyTime hverts hedges

/-- `#IndependentSet` reduces parsimoniously to `#MaximalIndependentSet` via `pendantGraph`. -/
theorem parsimoniousReducible_SharpIndepSet_SharpMaximalIndepSet :
    ParsimoniousReducible encGraph encGraph SharpIndepSet SharpMaximalIndepSet :=
  ⟨pendantGraph, computableInPolyTime_pendantGraph,
    fun G ↦ (SharpMaximalIndepSet_pendantGraph G).symm⟩

/-- **Transfer of `#P`-hardness from `#MaximalIndependentSet` along an offset-`{0, 1}` reduction**:
if `r : Graph → β` and `offset : Graph → ℕ` are polynomial-time computable with
`g (r G) = SharpMaximalIndepSet G + offset G` and `offset G ≤ 1` for every graph `G`, then `g` is
`#P`-hard under polynomial-time counting Turing reductions. -/
theorem countingTuringHard_of_add_offset_SharpMaximalIndepSet {β : Type} {encB : β ↪ List Bool}
    {g : β → ℕ} {r : Graph → β} {offset : Graph → ℕ}
    (hr : ComputableInPolyTime r encGraph encB)
    (hoff : ComputableInPolyTime offset encGraph encNat)
    (hspec : ∀ G : Graph, g (r G) = SharpMaximalIndepSet G + offset G)
    (hle : ∀ G : Graph, offset G ≤ 1) :
    CountingTuringHard encB g :=
  countingTuringHard_of_add_offset_SharpIndepSet
    (r := r ∘ pendantGraph) (offset := offset ∘ pendantGraph)
    (hr.comp computableInPolyTime_pendantGraph)
    (hoff.comp computableInPolyTime_pendantGraph)
    (fun G ↦ by simp only [Function.comp_apply, hspec, SharpMaximalIndepSet_pendantGraph])
    (fun G ↦ hle (pendantGraph G))

/-- **`#MaximalIndependentSet` is `#P`-complete under polynomial-time counting Turing
reductions.** -/
theorem SharpMaximalIndepSet_countingTuringComplete :
    CountingTuringComplete encGraph SharpMaximalIndepSet :=
  ⟨SharpMaximalIndepSet_mem_SharpP,
    countingTuringHard_of_add_offset_SharpMaximalIndepSet (r := id) (offset := fun _ ↦ 0)
      ComputableInPolyTime.id' (ComputableInPolyTime.const 0)
      (fun _ ↦ (Nat.add_zero _).symm) (fun _ ↦ Nat.zero_le 1)⟩

/-- If `#MaximalIndependentSet` is computable in polynomial time (`FP`), then `P = NP`. -/
theorem SharpMaximalIndepSet_polyTime_implies_P_eq_NP
    (h : ComputableInPolyTime SharpMaximalIndepSet encGraph encNat)
    {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  SharpIndepSet_polyTime_implies_P_eq_NP
    ((h.comp computableInPolyTime_pendantGraph).of_enc_eq fun G ↦
      congrArg encNat (SharpMaximalIndepSet_pendantGraph G).symm)
    enc

/- Non-degeneracy witness: on the 3-vertex path `0 - 1 - 2`, `{0, 2}` is a maximal independent set
   while `{0}` is not maximal. -/
example :
    let P3 : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2)]⟩
    ({0, 2} : Finset ℕ) ∈ maximalIndepFinsets P3 ∧
      ({0} : Finset ℕ) ∉ maximalIndepFinsets P3 := by
  dsimp only
  simp only [mem_maximalIndepFinsets_iff, Maximal, SimpleGraph.IsIndepSet, Set.Pairwise,
    Finset.mem_coe, Graph.toSimpleGraph_adj]
  refine ⟨⟨⟨by decide, fun u hu v hv huv ⟨_, hadj⟩ ↦ ?_⟩, fun T ⟨hT_sub, hT_ind⟩ hST v hvT ↦ ?_⟩,
    fun ⟨_, hmax⟩ ↦ ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp at huv hadj
  · have hv3 := hT_sub v hvT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv3
    rcases hv3 with rfl | rfl | rfl
    · simp
    · exfalso
      exact hT_ind (hST (by simp : (0 : ℕ) ∈ ({0, 2} : Finset ℕ))) hvT (by decide)
        ⟨by decide, Or.inl (by simp)⟩
    · simp
  · have hsub : ({0, 2} : Finset ℕ) ≤ {0} :=
      hmax (y := {0, 2}) ⟨by decide, fun u hu v hv huv ⟨_, hadj⟩ ↦ by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp at huv hadj⟩ (by decide)
    exact absurd (hsub (by simp : (2 : ℕ) ∈ ({0, 2} : Finset ℕ))) (by decide)

end CslibFrontier.Complexity
