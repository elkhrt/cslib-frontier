/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.EqualIndepNum
import CslibFrontier.Computability.Complexity.Classes.NP.Image
import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
import CslibFrontier.Computability.Complexity.Classes.Oracle.FewQueries
import CslibFrontier.Computability.Complexity.Classes.Oracle.ThresholdSearch
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sigma

/-!
# $\Theta_2^p$-Completeness of Graph 1-Extendability and Partitioning Hardness

A finite graph $G$ is **1-extendable** (`Cslib.Complexity.OneExtendable`) if every declared vertex
belongs to an independent set of maximum size `G.indepNum`. More generally, for $k \ge 1$,
`Cslib.Complexity.OneExtendableKPartition k` asks whether the declared vertices of $G$ can be
partitioned into $k$ classes each inducing a 1-extendable subgraph.

## Main definitions

* `Cslib.Complexity.OneExtendable`: graphs in which every declared vertex belongs to a maximum
  independent set.
* `Cslib.Complexity.OneExtendableKPartition`: graphs having a vertex `k`-partition into
  1-extendable induced subgraphs.

## Main results

* `Cslib.Complexity.OneExtendable_mem_PNPLog`, `Cslib.Complexity.OneExtendable_pnpLogHard`,
  `Cslib.Complexity.OneExtendable_pnpLogComplete`: $\Theta_2^p$-completeness of `OneExtendable`.
* `Cslib.Complexity.polyTimeReducible_OneExtendableKPartition_succ`,
  `Cslib.Complexity.OneExtendableKPartition_pnpLogHard`: $\Theta_2^p$-hardness of
  `OneExtendableKPartition k` for every fixed $k \ge 1$.
-/

public section

open Cslib Cslib.Logic.PL
open Turing Turing.MultiTapeMachine Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

namespace Cslib.Complexity

/-! ### Problem definitions and basic characterizations -/

/-- **`OneExtendable`**: graphs in which every declared vertex belongs to a maximum independent set
(of cardinality `G.indepNum`). -/
@[expose]
def OneExtendable : Set Graph :=
  {G | ∀ u : {v // v ∈ G.vertices},
    ∃ S : Finset {v // v ∈ G.vertices}, G.induced.IsNIndepSet G.indepNum S ∧ u ∈ S}

/-- **`OneExtendableKPartition k`**: graphs whose declared vertices have a `k`-coloring in which
each color class induces a 1-extendable subgraph. -/
@[expose]
def OneExtendableKPartition (k : ℕ) : Set Graph :=
  {G | ∃ c : {v // v ∈ G.vertices} → Fin k, ∀ i : Fin k,
    ∀ u : {w : {v // v ∈ G.vertices} // c w = i},
      ∃ S : Finset {w : {v // v ∈ G.vertices} // c w = i},
        (G.induced.induce {w | c w = i}).IsNIndepSet
          (G.induced.induce {w | c w = i}).indepNum S ∧ u ∈ S}

private def IsOneExtSimple {V : Type*} (H : SimpleGraph V) : Prop :=
  ∀ u : V, ∃ S : Finset V, H.IsNIndepSet H.indepNum S ∧ u ∈ S

theorem mem_OneExtendable_iff {G : Graph} :
    G ∈ OneExtendable ↔
      ∀ v ∈ G.vertices, ∃ S : Finset ℕ,
        (∀ u ∈ S, u ∈ G.vertices) ∧ G.toSimpleGraph.IsNIndepSet G.indepNum S ∧ v ∈ S := by
  constructor
  · intro h v hv
    obtain ⟨S, hS, hvS⟩ := h ⟨v, hv⟩
    refine ⟨S.map (Function.Embedding.subtype _), ?_, ⟨?_, by simp [hS.card_eq]⟩,
      Finset.mem_map.mpr ⟨⟨v, hv⟩, hvS, rfl⟩⟩
    · intro u hu; obtain ⟨w, -, rfl⟩ := Finset.mem_map.mp hu; exact w.2
    · intro u hu w hw huw hadj
      obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hu)
      obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hw)
      exact hS.isIndepSet hu' hw' (Subtype.coe_ne_coe.mp huw) hadj
  · intro h ⟨v, hv⟩
    obtain ⟨S, hSV, hS, hvS⟩ := h v hv
    have hmap : (S.subtype (· ∈ G.vertices)).map (Function.Embedding.subtype _) = S :=
      (Finset.subtype_map _).trans (Finset.filter_eq_self.mpr hSV)
    refine ⟨S.subtype (· ∈ G.vertices), ⟨?_, ?_⟩, Finset.mem_subtype.mpr hvS⟩
    · intro u hu w hw huw hadj
      exact hS.isIndepSet (Finset.mem_subtype.mp hu) (Finset.mem_subtype.mp hw)
        (Subtype.ext_iff.not.mp huw) hadj
    · rw [← Finset.card_map (Function.Embedding.subtype _), hmap, hS.card_eq]

theorem mem_OneExtendableKPartition_iff {k : ℕ} {G : Graph} :
    G ∈ OneExtendableKPartition k ↔
      ∃ c : {v // v ∈ G.vertices} → Fin k, ∀ i : Fin k,
        ∀ u : {w : {v // v ∈ G.vertices} // c w = i},
          ∃ S : Finset {w : {v // v ∈ G.vertices} // c w = i},
            (G.induced.induce {w | c w = i}).IsNIndepSet
              (G.induced.induce {w | c w = i}).indepNum S ∧ u ∈ S :=
  Iff.rfl

private theorem indepNum_congr_iso {V W : Type*} {H₁ : SimpleGraph V} {H₂ : SimpleGraph W}
    (e : H₁ ≃g H₂) : H₁.indepNum = H₂.indepNum := by
  have hc : H₁ᶜ ≃g H₂ᶜ :=
    ⟨e.toEquiv, by intro a b; simp [SimpleGraph.compl_adj, e.injective.eq_iff, e.map_adj_iff]⟩
  rw [← H₁.cliqueNum_compl, ← H₂.cliqueNum_compl]; unfold SimpleGraph.cliqueNum; congr 1; ext n
  exact ⟨fun ⟨s, hs⟩ => ⟨s.map hc.toEquiv.toEmbedding,
      ⟨fun x hx y hy hxy => by
        obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
        exact hc.map_adj_iff.mpr (hs.isClique hx' hy' (hc.injective.ne_iff.mp hxy)),
      (Finset.card_map _).trans hs.card_eq⟩⟩,
    fun ⟨t, ht⟩ => ⟨t.map hc.symm.toEquiv.toEmbedding,
      ⟨fun x hx y hy hxy => by
        obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
        exact hc.symm.map_adj_iff.mpr (ht.isClique hx' hy' (hc.symm.injective.ne_iff.mp hxy)),
      (Finset.card_map _).trans ht.card_eq⟩⟩⟩

private theorem isOneExtSimple_congr_iso {V W : Type*} {H₁ : SimpleGraph V} {H₂ : SimpleGraph W}
    (e : H₁ ≃g H₂) : IsOneExtSimple H₁ ↔ IsOneExtSimple H₂ := by
  have hind := indepNum_congr_iso e
  refine ⟨fun h w => ?_, fun h u => ?_⟩
  · obtain ⟨S, hS, hw⟩ := h (e.symm w)
    refine ⟨S.map e.toEquiv.toEmbedding, ⟨?_, by rw [Finset.card_map, ← hind, hS.card_eq]⟩,
      Finset.mem_map.mpr ⟨e.symm w, hw, e.apply_symm_apply w⟩⟩
    intro x hx y hy hxy hadj
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    exact hS.isIndepSet hx' hy' (e.injective.ne_iff.mp hxy) (e.map_adj_iff.mp hadj)
  · obtain ⟨T, hT, hu⟩ := h (e u)
    refine ⟨T.map e.symm.toEquiv.toEmbedding, ⟨?_, by rw [Finset.card_map, hind, hT.card_eq]⟩,
      Finset.mem_map.mpr ⟨e u, hu, e.symm_apply_apply u⟩⟩
    intro x hx y hy hxy hadj
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    exact hT.isIndepSet hx' hy' (e.symm.injective.ne_iff.mp hxy) (e.symm.map_adj_iff.mp hadj)

theorem oneExtendableKPartition_one : OneExtendableKPartition 1 = OneExtendable := by
  ext G
  let isoUniv : ∀ c : {v // v ∈ G.vertices} → Fin 1,
      G.induced.induce {w | c w = 0} ≃g G.induced := fun c =>
    ⟨⟨Subtype.val, fun u => ⟨u, Subsingleton.elim (c u) 0⟩, fun _ => Subtype.ext rfl, fun _ => rfl⟩,
     Iff.rfl⟩
  exact ⟨fun ⟨c, hc⟩ => (isOneExtSimple_congr_iso (isoUniv c)).mp (hc 0),
    fun hG => ⟨fun _ => 0, fun i => by
      rw [Subsingleton.elim i 0]; exact (isOneExtSimple_congr_iso (isoUniv _)).mpr hG⟩⟩

/-! ### Closed-neighborhood deletion and $\Theta_2^p$ membership -/

private def unaryToNat (n : ℕ) : ℕ := n

@[fun_prop]
private theorem computableInPolyTime_unaryToNat_comp {γ : Type} {enc : γ ↪ List Bool}
    {f : γ → ℕ} (hf : ComputableInPolyTime f enc encUnary) :
    ComputableInPolyTime (fun x => unaryToNat (f x)) enc encNat :=
  unary_to_binary.comp hf

private def pairCode (a b : ℕ) : ℕ := Nat.pair a b

@[fun_prop]
private theorem computableInPolyTime_pairCode_comp {γ : Type} {enc : γ ↪ List Bool}
    {a b : γ → ℕ} (ha : ComputableInPolyTime a enc encUnary)
    (hb : ComputableInPolyTime b enc encUnary) :
    ComputableInPolyTime (fun x => pairCode (a x) (b x)) enc encNat :=
  unary_to_binary.comp (unary_pair.comp (ha.prod hb))

private theorem pairCode_inj {a₁ b₁ a₂ b₂ : ℕ} :
    pairCode a₁ b₁ = pairCode a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := Nat.pair_eq_pair

private def tripleCode (a i u : ℕ) : ℕ := Nat.pair a (Nat.pair i u)

@[fun_prop]
private theorem computableInPolyTime_tripleCode_comp {γ : Type} {enc : γ ↪ List Bool}
    {a i u : γ → ℕ} (ha : ComputableInPolyTime a enc encUnary)
    (hi : ComputableInPolyTime i enc encUnary)
    (hu : ComputableInPolyTime u enc encUnary) :
    ComputableInPolyTime (fun x => tripleCode (a x) (i x) (u x)) enc encNat :=
  unary_to_binary.comp (unary_pair.comp (ha.prod (unary_pair.comp (hi.prod hu))))

private theorem tripleCode_inj {a₁ i₁ u₁ a₂ i₂ u₂ : ℕ} :
    tripleCode a₁ i₁ u₁ = tripleCode a₂ i₂ u₂ ↔ a₁ = a₂ ∧ i₁ = i₂ ∧ u₁ = u₂ := by
  simp only [tripleCode, Nat.pair_eq_pair]

private def deleteClosedNeighborhood (G : Graph) (v : ℕ) : Graph :=
  ⟨G.distinctVertices.filter fun u => decide (u ≠ v) && !G.adjBool v u, G.edges⟩

@[fun_prop]
private theorem computableInPolyTime_deleteClosedNeighborhood :
    ComputableInPolyTime (fun p : Graph × ℕ => deleteClosedNeighborhood p.1 p.2)
      (encPair encGraph encNat) encGraph := by
  unfold deleteClosedNeighborhood; fun_prop

private theorem mem_vertices_deleteClosedNeighborhood {G : Graph} {v u : ℕ} :
    u ∈ (deleteClosedNeighborhood G v).vertices ↔
      u ∈ G.vertices ∧ u ≠ v ∧ ¬ G.toSimpleGraph.Adj v u := by
  simp [deleteClosedNeighborhood, Graph.mem_distinctVertices]

private theorem indepNum_deleteClosedNeighborhood_add_one_le {G : Graph} {v : ℕ}
    (hv : v ∈ G.vertices) :
    (deleteClosedNeighborhood G v).indepNum + 1 ≤ G.indepNum := by
  classical
  obtain ⟨T, hTV, hT⟩ :=
    mem_IndependentSet_iff.mp (Graph.indepNum_mem_IndependentSet (deleteClosedNeighborhood G v))
  change G.toSimpleGraph.IsNIndepSet (deleteClosedNeighborhood G v).indepNum T at hT
  have hvT : v ∉ T := fun hmem => (mem_vertices_deleteClosedNeighborhood.mp (hTV v hmem)).2.1 rfl
  rw [Graph.le_indepNum_iff, mem_IndependentSet_iff_mk]
  refine ⟨insert v T, ?_, ?_, by rw [Finset.card_insert_of_notMem hvT, hT.card_eq]⟩
  · intro u hu; rcases Finset.mem_insert.mp hu with rfl | huT
    · exact hv
    · exact (mem_vertices_deleteClosedNeighborhood.mp (hTV u huT)).1
  · intro x hx y hy hxy hadj
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hxT <;>
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hyT
    · exact hxy rfl
    · exact (mem_vertices_deleteClosedNeighborhood.mp (hTV y hyT)).2.2 hadj
    · exact (mem_vertices_deleteClosedNeighborhood.mp (hTV x hxT)).2.2 hadj.symm
    · exact hT.isIndepSet hxT hyT hxy hadj

private theorem indepNum_deleteClosedNeighborhood_eq_iff {G : Graph} {v : ℕ}
    (hv : v ∈ G.vertices) :
    (deleteClosedNeighborhood G v).indepNum = G.indepNum - 1 ↔
      ∃ S : Finset ℕ,
        (∀ u ∈ S, u ∈ G.vertices) ∧ G.toSimpleGraph.IsNIndepSet G.indepNum S ∧ v ∈ S := by
  classical
  have hpos : 1 ≤ G.indepNum := by
    rw [Graph.le_indepNum_iff, mem_IndependentSet_iff_mk]
    exact ⟨{v}, by simp [hv], by simp [SimpleGraph.isNIndepSet_iff, SimpleGraph.IsIndepSet]⟩
  have hle : (deleteClosedNeighborhood G v).indepNum ≤ G.indepNum - 1 := by
    have := indepNum_deleteClosedNeighborhood_add_one_le hv; omega
  constructor
  · intro heq
    obtain ⟨T, hTV, hT⟩ :=
      mem_IndependentSet_iff.mp (Graph.indepNum_mem_IndependentSet (deleteClosedNeighborhood G v))
    change G.toSimpleGraph.IsNIndepSet (deleteClosedNeighborhood G v).indepNum T at hT
    rw [heq] at hT
    have hvT : v ∉ T := fun hmem => (mem_vertices_deleteClosedNeighborhood.mp (hTV v hmem)).2.1 rfl
    refine ⟨insert v T, ?_, ⟨?_, ?_⟩, Finset.mem_insert_self v T⟩
    · intro u hu; rcases Finset.mem_insert.mp hu with rfl | huT
      · exact hv
      · exact (mem_vertices_deleteClosedNeighborhood.mp (hTV u huT)).1
    · intro x hx y hy hxy hadj
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hxT <;>
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hyT
      · exact hxy rfl
      · exact (mem_vertices_deleteClosedNeighborhood.mp (hTV y hyT)).2.2 hadj
      · exact (mem_vertices_deleteClosedNeighborhood.mp (hTV x hxT)).2.2 hadj.symm
      · exact hT.isIndepSet hxT hyT hxy hadj
    · rw [Finset.card_insert_of_notMem hvT, hT.card_eq]; omega
  · rintro ⟨S, hSV, hS, hvS⟩
    refine le_antisymm hle ?_
    rw [Graph.le_indepNum_iff, mem_IndependentSet_iff_mk]
    refine ⟨S.erase v, ?_, ?_, by rw [Finset.card_erase_of_mem hvS, hS.card_eq]⟩
    · intro u hu; obtain ⟨hne, huS⟩ := Finset.mem_erase.mp hu
      exact mem_vertices_deleteClosedNeighborhood.mpr
        ⟨hSV u huS, hne, fun hadj => hS.isIndepSet hvS huS hne.symm hadj⟩
    · exact hS.isIndepSet.mono (Finset.coe_subset.mpr (Finset.erase_subset v S))

private def disjointUnionList (gs : List Graph) : Graph where
  vertices := gs.zipIdx.flatMap fun Gt =>
    (List.range Gt.1.distinctVertices.length).map fun i => pairCode Gt.2 i
  edges := gs.zipIdx.flatMap fun Gt =>
    (List.range Gt.1.distinctVertices.length).flatMap fun i =>
      ((List.range Gt.1.distinctVertices.length).filter fun j =>
        Gt.1.adjBool (Gt.1.distinctVertices.getD i 0) (Gt.1.distinctVertices.getD j 0)).map
        fun j => (pairCode Gt.2 i, pairCode Gt.2 j)

@[fun_prop]
private theorem computableInPolyTime_disjointUnionList :
    ComputableInPolyTime disjointUnionList (encList encGraph) encGraph := by
  unfold disjointUnionList; fun_prop

private theorem mem_zipIdx_iff_getElem {α : Type*} {l : List α} {x : α} {t : ℕ} :
    (x, t) ∈ l.zipIdx ↔ ∃ h : t < l.length, l[t] = x := by
  rw [List.mem_iff_getElem]
  simp only [List.length_zipIdx, List.getElem_zipIdx, Nat.zero_add, Prod.mk.injEq]
  exact ⟨fun ⟨i, hi, hx, hit⟩ => ⟨hit ▸ hi, hit ▸ hx⟩, fun ⟨ht, hx⟩ => ⟨t, ht, hx, rfl⟩⟩

private theorem mem_vertices_disjointUnionList {gs : List Graph} {w : ℕ} :
    w ∈ (disjointUnionList gs).vertices ↔
      ∃ (t : Fin gs.length) (i : Fin gs[t].distinctVertices.length),
        w = pairCode t.1 i.1 := by
  simp only [disjointUnionList, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨G, t⟩, hGt, i, hi, rfl⟩
    obtain ⟨ht_lt, rfl⟩ := mem_zipIdx_iff_getElem.mp hGt
    exact ⟨⟨t, ht_lt⟩, ⟨i, hi⟩, rfl⟩
  · rintro ⟨⟨t, ht⟩, ⟨i, hi⟩, rfl⟩
    exact ⟨(gs[t], t), mem_zipIdx_iff_getElem.mpr ⟨ht, rfl⟩, i, hi, rfl⟩

private theorem mem_edges_disjointUnionList {gs : List Graph} {x y : ℕ} :
    (x, y) ∈ (disjointUnionList gs).edges ↔
      ∃ (t : Fin gs.length) (i j : Fin gs[t].distinctVertices.length),
        gs[t].toSimpleGraph.Adj (gs[t].vertexEquiv i).1 (gs[t].vertexEquiv j).1 ∧
          x = pairCode t.1 i.1 ∧ y = pairCode t.1 j.1 := by
  simp only [disjointUnionList, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_range, Prod.mk.injEq, Graph.adjBool_eq_true_iff]
  constructor
  · rintro ⟨⟨G, t⟩, hGt, i, hi, j, ⟨hj, hadj⟩, rfl, rfl⟩
    obtain ⟨ht_lt, rfl⟩ := mem_zipIdx_iff_getElem.mp hGt
    exact ⟨⟨t, ht_lt⟩, ⟨i, hi⟩, ⟨j, hj⟩,
      by rwa [Graph.vertexEquiv_apply, Graph.vertexEquiv_apply], rfl, rfl⟩
  · rintro ⟨⟨t, ht⟩, ⟨i, hi⟩, ⟨j, hj⟩, hadj, rfl, rfl⟩
    rw [Graph.vertexEquiv_apply, Graph.vertexEquiv_apply] at hadj
    exact ⟨(gs[t], t), mem_zipIdx_iff_getElem.mpr ⟨ht, rfl⟩, i, hi, j, ⟨hj, hadj⟩, rfl, rfl⟩

private theorem adj_disjointUnionList_pairCode {gs : List Graph}
    (t₁ t₂ : Fin gs.length) (i₁ : Fin gs[t₁].distinctVertices.length)
    (i₂ : Fin gs[t₂].distinctVertices.length) :
    (disjointUnionList gs).toSimpleGraph.Adj (pairCode t₁.1 i₁.1) (pairCode t₂.1 i₂.1) ↔
      t₁ = t₂ ∧ gs[t₁].toSimpleGraph.Adj (gs[t₁].vertexEquiv i₁).1 (gs[t₂].vertexEquiv i₂).1 := by
  rw [Graph.toSimpleGraph_adj]
  constructor
  · rintro ⟨_, hmem | hmem⟩
    · obtain ⟨t, i, j, hadj, e1, e2⟩ := mem_edges_disjointUnionList.mp hmem
      have ht1 : t₁ = t := Fin.ext (pairCode_inj.mp e1).1
      have ht2 : t₂ = t := Fin.ext (pairCode_inj.mp e2).1
      subst ht1 ht2
      have hi1 : i₁ = i := Fin.ext (pairCode_inj.mp e1).2
      have hj2 : i₂ = j := Fin.ext (pairCode_inj.mp e2).2
      subst hi1 hj2; exact ⟨rfl, hadj⟩
    · obtain ⟨t, i, j, hadj, e1, e2⟩ := mem_edges_disjointUnionList.mp hmem
      have ht2 : t₂ = t := Fin.ext (pairCode_inj.mp e1).1
      have ht1 : t₁ = t := Fin.ext (pairCode_inj.mp e2).1
      subst ht1 ht2
      have hi2 : i₂ = i := Fin.ext (pairCode_inj.mp e1).2
      have hj1 : i₁ = j := Fin.ext (pairCode_inj.mp e2).2
      subst hi2 hj1; exact ⟨rfl, hadj.symm⟩
  · rintro ⟨rfl, hadj⟩
    exact ⟨fun h => hadj.ne (congrArg (fun k => (gs[t₁].vertexEquiv k).1)
        (Fin.ext (pairCode_inj.mp h).2)),
      Or.inl (mem_edges_disjointUnionList.mpr ⟨t₁, i₁, i₂, hadj, rfl, rfl⟩)⟩

private theorem indepNum_disjointUnionList (gs : List Graph) :
    (disjointUnionList gs).indepNum = (gs.map Graph.indepNum).sum := by
  classical
  have hsum_fin : (gs.map Graph.indepNum).sum = ∑ t : Fin gs.length, gs[t].indepNum := by
    conv_lhs => rw [← List.ofFn_getElem (xs := gs)]
    simp
  rw [hsum_fin]
  let emb : (Σ t : Fin gs.length, Fin gs[t].distinctVertices.length) ↪ ℕ :=
    ⟨fun p => pairCode p.1.1 p.2.1, fun ⟨t₁, i₁⟩ ⟨t₂, i₂⟩ h => by
      obtain ⟨ht, hi⟩ := pairCode_inj.mp h
      have hteq : t₁ = t₂ := Fin.ext ht
      subst hteq; exact Sigma.ext rfl (heq_of_eq (Fin.ext hi))⟩
  refine le_antisymm ?_ ?_
  · obtain ⟨S, hSV, hS⟩ :=
      mem_IndependentSet_iff.mp (Graph.indepNum_mem_IndependentSet (disjointUnionList gs))
    change (disjointUnionList gs).toSimpleGraph.IsNIndepSet (disjointUnionList gs).indepNum S at hS
    let slice : ∀ t : Fin gs.length, Finset (Fin gs[t].distinctVertices.length) :=
      fun t => Finset.univ.filter fun i => pairCode t.1 i.1 ∈ S
    have hS_eq : S = (Finset.univ.sigma slice).map emb := by
      ext w
      simp only [Finset.mem_map, Finset.mem_sigma, Finset.mem_univ, true_and, slice,
        Finset.mem_filter, emb]
      refine ⟨fun hw => ?_, fun ⟨⟨t, i⟩, hw, heq⟩ => heq ▸ hw⟩
      obtain ⟨t, i, rfl⟩ := mem_vertices_disjointUnionList.mp (hSV w hw)
      exact ⟨⟨t, i⟩, hw, rfl⟩
    rw [← hS.card_eq, hS_eq, Finset.card_map, Finset.card_sigma]
    refine Finset.sum_le_sum fun t _ => ?_
    have hind_t : gs[t].induced.IsIndepSet
        (((slice t).map gs[t].vertexEquiv.toEmbedding : Finset _) : Set _) := by
      intro u hu v hv huv hadj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hu)
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hv)
      exact hS.isIndepSet (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
        (fun h => huv (congrArg gs[t].vertexEquiv (Fin.ext (pairCode_inj.mp h).2)))
        ((adj_disjointUnionList_pairCode t t i j).mpr ⟨rfl, hadj⟩)
    simpa [Graph.indepNum] using hind_t.card_le_indepNum
  · rw [Graph.le_indepNum_iff, mem_IndependentSet_iff_mk]
    choose J hJ using fun t : Fin gs.length => gs[t].induced.exists_isNIndepSet_indepNum
    let slice : ∀ t : Fin gs.length, Finset (Fin gs[t].distinctVertices.length) :=
      fun t => (J t).map gs[t].vertexEquiv.symm.toEmbedding
    refine ⟨(Finset.univ.sigma slice).map emb, ?_, ?_, ?_⟩
    · intro w hw; obtain ⟨⟨t, i⟩, -, rfl⟩ := Finset.mem_map.mp hw
      exact mem_vertices_disjointUnionList.mpr ⟨t, i, rfl⟩
    · intro x hx y hy hxy hadj
      obtain ⟨⟨t₁, i₁⟩, hi₁, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
      obtain ⟨⟨t₂, i₂⟩, hi₂, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
      obtain ⟨rfl, hadj'⟩ := (adj_disjointUnionList_pairCode t₁ t₂ i₁ i₂).mp hadj
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, slice, Finset.mem_map] at hi₁ hi₂
      obtain ⟨u₁, hu₁, e1⟩ := hi₁; obtain ⟨u₂, hu₂, e2⟩ := hi₂
      have hv₁ : gs[t₁].vertexEquiv i₁ = u₁ := by
        rw [← e1]; exact gs[t₁].vertexEquiv.apply_symm_apply _
      have hv₂ : gs[t₁].vertexEquiv i₂ = u₂ := by
        rw [← e2]; exact gs[t₁].vertexEquiv.apply_symm_apply _
      have hadj_ind : gs[t₁].induced.Adj u₁ u₂ := by
        change gs[t₁].toSimpleGraph.Adj u₁.1 u₂.1
        rwa [← hv₁, ← hv₂]
      exact (hJ t₁).isIndepSet hu₁ hu₂
        (fun h => hxy (congrArg (fun k => emb ⟨t₁, k⟩) (by rw [← e1, ← e2, h]))) hadj_ind
    · rw [Finset.card_map, Finset.card_sigma]
      exact Finset.sum_congr rfl fun t _ => by simp [slice, Graph.indepNum, (hJ t).card_eq]

private theorem list_mul_le_sum_iff_forall_eq {α : Type*} {l : List α} {f : α → ℕ} {B : ℕ}
    (hle : ∀ x ∈ l, f x ≤ B) :
    l.length * B ≤ (l.map f).sum ↔ ∀ x ∈ l, f x = B := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    have ha : f a ≤ B := hle a List.mem_cons_self
    have htl_le : ∀ x ∈ tl, f x ≤ B := fun x hx => hle x (List.mem_cons_of_mem a hx)
    have hsum_le : (tl.map f).sum ≤ tl.length * B := by
      simpa only [smul_eq_mul, List.length_map] using List.sum_le_length_nsmul (tl.map f) B
        fun y hy => by obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact htl_le x hx
    simp only [List.length_cons, List.map_cons, List.sum_cons, List.forall_mem_cons,
      ← ih htl_le, Nat.add_one_mul]; omega

private def oneExtendableCheckInstance (p : Graph × ℕ) : IndependentSetInstance :=
  ⟨disjointUnionList (p.1.distinctVertices.map (deleteClosedNeighborhood p.1)),
   unaryToNat p.1.distinctVertices.length * (p.2 - 1)⟩

@[fun_prop]
private theorem computableInPolyTime_oneExtendableCheckInstance :
    ComputableInPolyTime oneExtendableCheckInstance
      (encPair encGraph encNat) encIndependentSetInstance := by
  unfold oneExtendableCheckInstance
  have hv : ComputableInPolyTime (fun p : Graph × ℕ => p.1.distinctVertices)
      (encPair encGraph encNat) (encList encNat) := by fun_prop
  have hgs := mapWithInput (f := fun p v => deleteClosedNeighborhood p.1 v) hv
    ((computableInPolyTime_deleteClosedNeighborhood.comp
      (((fst encGraph encNat).comp (fst (encPair encGraph encNat) encNat)).prod
        (snd (encPair encGraph encNat) encNat))).of_enc_eq fun _ => rfl)
  exact encIndependentSetInstance_mk_polyTime
    (computableInPolyTime_disjointUnionList.comp hgs)
    (binary_mul' (computableInPolyTime_unaryToNat_comp ((length_list encNat).comp hv))
      (binary_sub' (snd _ _) (const 1)))

private theorem mem_OneExtendable_iff_checkInstance (G : Graph) :
    G ∈ OneExtendable ↔ oneExtendableCheckInstance (G, G.indepNum) ∈ IndependentSet := by
  rw [oneExtendableCheckInstance]
  dsimp only
  rw [← Graph.le_indepNum_iff, indepNum_disjointUnionList, List.map_map, unaryToNat]
  have hle : ∀ v ∈ G.distinctVertices,
      (Graph.indepNum ∘ deleteClosedNeighborhood G) v ≤ G.indepNum - 1 := fun v hv => by
    dsimp only [Function.comp_apply]
    have := indepNum_deleteClosedNeighborhood_add_one_le (Graph.mem_distinctVertices.mp hv); omega
  rw [list_mul_le_sum_iff_forall_eq hle, mem_OneExtendable_iff]
  exact ⟨fun h v hv => (indepNum_deleteClosedNeighborhood_eq_iff
      (Graph.mem_distinctVertices.mp hv)).mpr (h v (Graph.mem_distinctVertices.mp hv)),
    fun h v hv => (indepNum_deleteClosedNeighborhood_eq_iff hv).mp
      (h v (Graph.mem_distinctVertices.mpr hv))⟩

/-- **`OneExtendable ∈ PNPLog encGraph`**. -/
theorem OneExtendable_mem_PNPLog : OneExtendable ∈ PNPLog encGraph := by
  classical
  obtain ⟨toSAT, htoSAT, hSAT⟩ :=
    CookLevin.SAT_npHard encIndependentSetInstance IndependentSet IndependentSet.mem_NP
  let reqCheck : Graph × ℕ → List Bool := fun p => encCNF (toSAT (oneExtendableCheckInstance p))
  have hreqCheck : ComputableInPolyTime reqCheck (encPair encGraph encNat) encBits :=
    (ComputableInPolyTime.of_eq (f := fun φ : CNF ℕ => encCNF φ) fun _ => rfl).comp
      (htoSAT.comp computableInPolyTime_oneExtendableCheckInstance)
  have hq2 := computableInPolyTimeWithOracleQueries_query hreqCheck (encCNF '' SAT)
  have hmid : ∀ G : Graph,
      (encPair encGraph encNat (G, G.indepNum)).length ≤ 3 * (encGraph G).length + 2 := fun G => by
    have hind_le : G.indepNum ≤ (encGraph G).length :=
      G.indepNum_le_card.trans (G.vertices.toFinset_card_le.trans G.length_vertices_le_encGraph)
    have hnat : (encNat G.indepNum).length ≤ (encGraph G).length := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans hind_le
    rw [length_encPair]; dsimp only; omega
  have hseq := computableInPolyTimeWithOracleQueries_indepNum.bind_with
    (g := fun G m => decide (reqCheck (G, m) ∈ encCNF '' SAT)) hq2
    (fun _ _ _ => le_rfl) (midLen := fun n => 3 * n + 2) hmid
  refine mem_PNPLog_of_mem_PWithOracleQueries (c := 2) image_SAT_mem_NP
    ⟨_, hseq.mono (fun _ => by omega), fun G => ?_⟩
  rw [mem_OneExtendable_iff_checkInstance, hSAT]
  simp only [reqCheck, decide_eq_true_eq]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, heq⟩ => encCNF.injective heq ▸ h⟩

private def edgelessGraph (m : ℕ) : Graph := ⟨(List.range m).map unaryToNat, []⟩

@[fun_prop]
private theorem computableInPolyTime_edgelessGraph :
    ComputableInPolyTime edgelessGraph encUnary encGraph := by
  have hu : ComputableInPolyTime unaryToNat encUnary encNat := unary_to_binary
  unfold edgelessGraph; fun_prop

private theorem vertices_edgelessGraph (m : ℕ) : (edgelessGraph m).vertices = List.range m :=
  List.map_id (List.range m)

private theorem distinctVertices_edgelessGraph (m : ℕ) :
    (edgelessGraph m).distinctVertices.length = m := by
  rw [Graph.length_distinctVertices, vertices_edgelessGraph,
    List.toFinset_card_of_nodup List.nodup_range, List.length_range]

private theorem indepNum_edgelessGraph (m : ℕ) : (edgelessGraph m).indepNum = m := by
  refine le_antisymm ?_ ?_
  · calc (edgelessGraph m).indepNum ≤ (edgelessGraph m).vertices.toFinset.card :=
          (edgelessGraph m).indepNum_le_card
      _ = m := by rw [vertices_edgelessGraph, List.toFinset_card_of_nodup List.nodup_range,
          List.length_range]
  · rw [Graph.le_indepNum_iff, mem_IndependentSet_iff_mk]
    refine ⟨(List.range m).toFinset, fun v hv => by
      rw [vertices_edgelessGraph]; exact List.mem_toFinset.mp hv, ⟨?_, ?_⟩⟩
    · intro _ _ _ _ _ hadj; rw [Graph.toSimpleGraph_adj] at hadj; simp [edgelessGraph] at hadj
    · rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]

private theorem edgelessGraph_induced_eq_bot (m : ℕ) : (edgelessGraph m).induced = ⊥ := by
  ext ⟨u, hu⟩ ⟨v, hv⟩
  exact ⟨fun hadj => by
    rw [Graph.induced_adj, Graph.toSimpleGraph_adj] at hadj
    simp [edgelessGraph] at hadj, False.elim⟩

/-! ### Complete join, the 4-layer 1-extendable gadget, and $\Theta_2^p$-completeness -/

private def joinSimple {V₁ V₂ : Type*} (H₁ : SimpleGraph V₁) (H₂ : SimpleGraph V₂) :
    SimpleGraph (V₁ ⊕ V₂) where
  Adj
    | .inl u, .inl u' => H₁.Adj u u'
    | .inr v, .inr v' => H₂.Adj v v'
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
  symm := ⟨by rintro (u | v) (u' | v') h <;> first | exact h.symm | trivial⟩
  loopless := ⟨by rintro (u | v); exacts [H₁.loopless.irrefl u, H₂.loopless.irrefl v]⟩

private def joinSimpleSymm {V₁ V₂ : Type*} (H₁ : SimpleGraph V₁) (H₂ : SimpleGraph V₂) :
    joinSimple H₁ H₂ ≃g joinSimple H₂ H₁ where
  toEquiv := Equiv.sumComm V₁ V₂
  map_rel_iff' := by rintro (u | v) (u' | v') <;> rfl

private theorem indepNum_joinSimple {V₁ V₂ : Type*} [Finite V₁] [Finite V₂]
    (H₁ : SimpleGraph V₁) (H₂ : SimpleGraph V₂) :
    (joinSimple H₁ H₂).indepNum = max H₁.indepNum H₂.indepNum := by
  classical
  refine le_antisymm ?_ (max_le ?_ ?_)
  · obtain ⟨S, hS⟩ := (joinSimple H₁ H₂).exists_isNIndepSet_indepNum
    rw [← hS.card_eq]
    by_cases hL : ∃ u : V₁, Sum.inl u ∈ S
    · obtain ⟨u₀, hu₀⟩ := hL
      have hallL : ∀ x ∈ S, ∃ u : V₁, x = .inl u := fun x hx => by
        rcases x with u | v
        · exact ⟨u, rfl⟩
        · exact (hS.isIndepSet hu₀ hx (by simp) trivial).elim
      choose f hf using hallL
      let emb : {x // x ∈ S} ↪ V₁ :=
        ⟨fun x => f x.1 x.2, fun a b h =>
          Subtype.ext ((hf a.1 a.2).trans (by dsimp only at h; rw [h, ← hf b.1 b.2]))⟩
      have hind₁ : H₁.IsIndepSet ((Finset.univ.map emb : Finset _) : Set _) := by
        intro u hu u' hu' hne hadj
        obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hu)
        obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hu')
        exact hS.isIndepSet a.2 b.2 (fun h => hne (congrArg emb (Subtype.ext h)))
          (by rw [hf a.1 a.2, hf b.1 b.2]; exact hadj)
      simpa using hind₁.card_le_indepNum.trans (le_max_left _ _)
    · have hallR : ∀ x ∈ S, ∃ v : V₂, x = .inr v := fun x hx => by
        rcases x with u | v; exacts [(hL ⟨u, hx⟩).elim, ⟨v, rfl⟩]
      choose f hf using hallR
      let emb : {x // x ∈ S} ↪ V₂ :=
        ⟨fun x => f x.1 x.2, fun a b h =>
          Subtype.ext ((hf a.1 a.2).trans (by dsimp only at h; rw [h, ← hf b.1 b.2]))⟩
      have hind₂ : H₂.IsIndepSet ((Finset.univ.map emb : Finset _) : Set _) := by
        intro v hv v' hv' hne hadj
        obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hv)
        obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hv')
        exact hS.isIndepSet a.2 b.2 (fun h => hne (congrArg emb (Subtype.ext h)))
          (by rw [hf a.1 a.2, hf b.1 b.2]; exact hadj)
      simpa using hind₂.card_le_indepNum.trans (le_max_right _ _)
  · obtain ⟨S₁, hS₁⟩ := H₁.exists_isNIndepSet_indepNum
    have hind : (joinSimple H₁ H₂).IsIndepSet
        ((S₁.map ⟨Sum.inl, Sum.inl_injective⟩ : Finset (V₁ ⊕ V₂)) : Set (V₁ ⊕ V₂)) := by
      intro x hx y hy hxy hadj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
      exact hS₁.isIndepSet ha hb (fun h => hxy (congrArg Sum.inl h)) hadj
    simpa [hS₁.card_eq] using hind.card_le_indepNum
  · obtain ⟨S₂, hS₂⟩ := H₂.exists_isNIndepSet_indepNum
    have hind : (joinSimple H₁ H₂).IsIndepSet
        ((S₂.map ⟨Sum.inr, Sum.inr_injective⟩ : Finset (V₁ ⊕ V₂)) : Set (V₁ ⊕ V₂)) := by
      intro x hx y hy hxy hadj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
      exact hS₂.isIndepSet ha hb (fun h => hxy (congrArg Sum.inr h)) hadj
    simpa [hS₂.card_eq] using hind.card_le_indepNum

private theorem isOneExtSimple_joinSimple_left {V₁ V₂ : Type*} [Finite V₁] [Finite V₂]
    {H₁ : SimpleGraph V₁} {H₂ : SimpleGraph V₂} [Nonempty V₁]
    (h : IsOneExtSimple (joinSimple H₁ H₂)) :
    IsOneExtSimple H₁ ∧ (joinSimple H₁ H₂).indepNum = H₁.indepNum := by
  classical
  have hpull : ∀ u : V₁, ∃ S₁ : Finset V₁,
      H₁.IsNIndepSet (joinSimple H₁ H₂).indepNum S₁ ∧ u ∈ S₁ := fun u => by
    obtain ⟨S, hS, huS⟩ := h (.inl u)
    have hallL : ∀ x ∈ S, ∃ u' : V₁, x = .inl u' := fun x hx => by
      rcases x with u' | v; exacts [⟨u', rfl⟩, (hS.isIndepSet huS hx (by simp) trivial).elim]
    choose f hf using hallL
    let emb : {x // x ∈ S} ↪ V₁ :=
      ⟨fun x => f x.1 x.2, fun a b heq =>
        Subtype.ext ((hf a.1 a.2).trans (by dsimp only at heq; rw [heq, ← hf b.1 b.2]))⟩
    refine ⟨Finset.univ.map emb, ⟨?_, by simp [hS.card_eq]⟩, ?_⟩
    · intro x hx y hy hxy hadj
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
      obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
      exact hS.isIndepSet a.2 b.2 (fun he => hxy (congrArg emb (Subtype.ext he)))
        (by rw [hf a.1 a.2, hf b.1 b.2]; exact hadj)
    · refine Finset.mem_map.mpr ⟨⟨.inl u, huS⟩, Finset.mem_univ _, ?_⟩
      exact Sum.inl_injective (hf (.inl u) huS).symm
  obtain ⟨u₀⟩ := ‹Nonempty V₁›
  obtain ⟨S₀, hS₀, -⟩ := hpull u₀
  have heq : (joinSimple H₁ H₂).indepNum = H₁.indepNum :=
    le_antisymm (hS₀.card_eq ▸ hS₀.isIndepSet.card_le_indepNum)
      (by rw [indepNum_joinSimple]; exact le_max_left _ _)
  exact ⟨fun u => heq ▸ hpull u, heq⟩

private theorem isOneExtSimple_joinSimple_iff {V₁ V₂ : Type*} [Finite V₁] [Finite V₂]
    [Nonempty V₁] [Nonempty V₂] {H₁ : SimpleGraph V₁} {H₂ : SimpleGraph V₂} :
    IsOneExtSimple (joinSimple H₁ H₂) ↔
      IsOneExtSimple H₁ ∧ IsOneExtSimple H₂ ∧ H₁.indepNum = H₂.indepNum := by
  classical
  constructor
  · intro h
    obtain ⟨h₁, heq₁⟩ := isOneExtSimple_joinSimple_left h
    obtain ⟨h₂, heq₂⟩ := isOneExtSimple_joinSimple_left
      ((isOneExtSimple_congr_iso (joinSimpleSymm H₁ H₂)).mp h)
    rw [← indepNum_congr_iso (joinSimpleSymm H₁ H₂)] at heq₂
    exact ⟨h₁, h₂, heq₁.symm.trans heq₂⟩
  · rintro ⟨h₁, h₂, heq⟩ (u | v)
    · obtain ⟨S₁, hS₁, hu⟩ := h₁ u
      refine ⟨S₁.map ⟨Sum.inl, Sum.inl_injective⟩, ⟨?_, ?_⟩,
        Finset.mem_map.mpr ⟨u, hu, rfl⟩⟩
      · intro x hx y hy hxy hadj
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
        exact hS₁.isIndepSet ha hb (fun h => hxy (congrArg Sum.inl h)) hadj
      · rw [Finset.card_map, hS₁.card_eq, indepNum_joinSimple, heq, max_self]
    · obtain ⟨S₂, hS₂, hv⟩ := h₂ v
      refine ⟨S₂.map ⟨Sum.inr, Sum.inr_injective⟩, ⟨?_, ?_⟩,
        Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩
      · intro x hx y hy hxy hadj
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
        exact hS₂.isIndepSet ha hb (fun h => hxy (congrArg Sum.inr h)) hadj
      · rw [Finset.card_map, hS₂.card_eq, indepNum_joinSimple, heq, max_self]

private def completeJoin (G₁ G₂ : Graph) : Graph :=
  let p₁ := G₁.distinctVertices.length
  let p₂ := G₂.distinctVertices.length
  { vertices :=
      ((List.range p₁).map fun i => pairCode 0 i) ++
      ((List.range p₂).map fun j => pairCode 1 j)
    edges :=
      ((List.range p₁).flatMap fun i =>
        ((List.range p₁).filter fun i' =>
          G₁.adjBool (G₁.distinctVertices.getD i 0) (G₁.distinctVertices.getD i' 0)).map
          fun i' => (pairCode 0 i, pairCode 0 i')) ++
      ((List.range p₂).flatMap fun j =>
        ((List.range p₂).filter fun j' =>
          G₂.adjBool (G₂.distinctVertices.getD j 0) (G₂.distinctVertices.getD j' 0)).map
          fun j' => (pairCode 1 j, pairCode 1 j')) ++
      ((List.range p₁).flatMap fun i =>
        (List.range p₂).map fun j => (pairCode 0 i, pairCode 1 j)) }

@[fun_prop]
private theorem computableInPolyTime_completeJoin :
    ComputableInPolyTime (fun p : Graph × Graph => completeJoin p.1 p.2)
      (encPair encGraph encGraph) encGraph := by unfold completeJoin; fun_prop

private theorem mem_vertices_completeJoin {G₁ G₂ : Graph} {w : ℕ} :
    w ∈ (completeJoin G₁ G₂).vertices ↔
      (∃ i : Fin G₁.distinctVertices.length, w = pairCode 0 i.1) ∨
      (∃ j : Fin G₂.distinctVertices.length, w = pairCode 1 j.1) := by
  simp only [completeJoin, List.mem_append, List.mem_map, List.mem_range]
  exact ⟨fun | .inl ⟨i, hi, hw⟩ => .inl ⟨⟨i, hi⟩, hw.symm⟩
             | .inr ⟨j, hj, hw⟩ => .inr ⟨⟨j, hj⟩, hw.symm⟩,
         fun | .inl ⟨⟨i, hi⟩, hw⟩ => .inl ⟨i, hi, hw.symm⟩
             | .inr ⟨⟨j, hj⟩, hw⟩ => .inr ⟨j, hj, hw.symm⟩⟩

private theorem adj_completeJoin_left {G₁ G₂ : Graph} (i i' : Fin G₁.distinctVertices.length) :
    (completeJoin G₁ G₂).toSimpleGraph.Adj (pairCode 0 i.1) (pairCode 0 i'.1) ↔
      G₁.induced.Adj (G₁.vertexEquiv i) (G₁.vertexEquiv i') := by
  rw [Graph.toSimpleGraph_adj]
  simp only [completeJoin, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_range, Prod.mk.injEq, Graph.adjBool_eq_true_iff]
  constructor
  · rintro ⟨_, ((h | h) | h) | ((h | h) | h)⟩
    · obtain ⟨_, _, _, ⟨_, hadj⟩, e1, e2⟩ := h
      obtain ⟨-, rfl⟩ := pairCode_inj.mp e1.symm; obtain ⟨-, rfl⟩ := pairCode_inj.mp e2.symm
      rwa [Graph.induced_adj, Graph.vertexEquiv_apply, Graph.vertexEquiv_apply]
    · obtain ⟨_, _, _, _, e1, _⟩ := h; cases (pairCode_inj.mp e1).1
    · obtain ⟨_, _, _, _, _, e2⟩ := h; cases (pairCode_inj.mp e2).1
    · obtain ⟨_, _, _, ⟨_, hadj⟩, e1, e2⟩ := h
      obtain ⟨-, rfl⟩ := pairCode_inj.mp e1.symm; obtain ⟨-, rfl⟩ := pairCode_inj.mp e2.symm
      rw [Graph.induced_adj, Graph.vertexEquiv_apply, Graph.vertexEquiv_apply]; exact hadj.symm
    · obtain ⟨_, _, _, _, e1, _⟩ := h; cases (pairCode_inj.mp e1).1
    · obtain ⟨_, _, _, _, _, e2⟩ := h; cases (pairCode_inj.mp e2).1
  · intro hadj
    have hne : pairCode 0 i.1 ≠ pairCode 0 i'.1 := fun h =>
      hadj.ne (congrArg G₁.vertexEquiv (Fin.ext (pairCode_inj.mp h).2))
    rw [Graph.induced_adj, Graph.vertexEquiv_apply, Graph.vertexEquiv_apply] at hadj
    exact ⟨hne, Or.inl (Or.inl (Or.inl ⟨i.1, i.2, i'.1, ⟨i'.2, hadj⟩, rfl, rfl⟩))⟩

private theorem adj_completeJoin_right {G₁ G₂ : Graph} (j j' : Fin G₂.distinctVertices.length) :
    (completeJoin G₁ G₂).toSimpleGraph.Adj (pairCode 1 j.1) (pairCode 1 j'.1) ↔
      G₂.induced.Adj (G₂.vertexEquiv j) (G₂.vertexEquiv j') := by
  rw [Graph.toSimpleGraph_adj]
  simp only [completeJoin, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_range, Prod.mk.injEq, Graph.adjBool_eq_true_iff]
  constructor
  · rintro ⟨_, ((h | h) | h) | ((h | h) | h)⟩
    · obtain ⟨_, _, _, _, e1, _⟩ := h; cases (pairCode_inj.mp e1).1
    · obtain ⟨_, _, _, ⟨_, hadj⟩, e1, e2⟩ := h
      obtain ⟨-, rfl⟩ := pairCode_inj.mp e1.symm; obtain ⟨-, rfl⟩ := pairCode_inj.mp e2.symm
      rwa [Graph.induced_adj, Graph.vertexEquiv_apply, Graph.vertexEquiv_apply]
    · obtain ⟨_, _, _, _, e1, _⟩ := h; cases (pairCode_inj.mp e1).1
    · obtain ⟨_, _, _, _, e1, _⟩ := h; cases (pairCode_inj.mp e1).1
    · obtain ⟨_, _, _, ⟨_, hadj⟩, e1, e2⟩ := h
      obtain ⟨-, rfl⟩ := pairCode_inj.mp e1.symm; obtain ⟨-, rfl⟩ := pairCode_inj.mp e2.symm
      rw [Graph.induced_adj, Graph.vertexEquiv_apply, Graph.vertexEquiv_apply]; exact hadj.symm
    · obtain ⟨_, _, _, _, e1, _⟩ := h; cases (pairCode_inj.mp e1).1
  · intro hadj
    have hne : pairCode 1 j.1 ≠ pairCode 1 j'.1 := fun h =>
      hadj.ne (congrArg G₂.vertexEquiv (Fin.ext (pairCode_inj.mp h).2))
    rw [Graph.induced_adj, Graph.vertexEquiv_apply, Graph.vertexEquiv_apply] at hadj
    exact ⟨hne, Or.inl (Or.inl (Or.inr ⟨j.1, j.2, j'.1, ⟨j'.2, hadj⟩, rfl, rfl⟩))⟩

private theorem adj_completeJoin_cross {G₁ G₂ : Graph}
    (i : Fin G₁.distinctVertices.length) (j : Fin G₂.distinctVertices.length) :
    (completeJoin G₁ G₂).toSimpleGraph.Adj (pairCode 0 i.1) (pairCode 1 j.1) := by
  rw [Graph.toSimpleGraph_adj]
  refine ⟨(fun h => by cases (pairCode_inj.mp h).1), Or.inl ?_⟩
  simp only [completeJoin, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inr ⟨i.1, i.2, j.1, j.2, rfl⟩

private def completeJoinIso (G₁ G₂ : Graph) :
    (completeJoin G₁ G₂).induced ≃g joinSimple G₁.induced G₂.induced where
  toEquiv :=
    { toFun := fun w =>
        if h0 : (Nat.unpair w.1).1 = 0 then
          .inl (G₁.vertexEquiv ⟨(Nat.unpair w.1).2, by
            rcases mem_vertices_completeJoin.mp w.2 with ⟨i, hi⟩ | ⟨j, hj⟩
            · simp [hi, pairCode, Nat.unpair_pair]
            · simp [hj, pairCode, Nat.unpair_pair] at h0⟩)
        else
          .inr (G₂.vertexEquiv ⟨(Nat.unpair w.1).2, by
            rcases mem_vertices_completeJoin.mp w.2 with ⟨i, hi⟩ | ⟨j, hj⟩
            · exact (h0 (by simp [hi, pairCode, Nat.unpair_pair])).elim
            · simp [hj, pairCode, Nat.unpair_pair]⟩)
      invFun := fun
        | .inl u => ⟨pairCode 0 (G₁.vertexEquiv.symm u).1,
            mem_vertices_completeJoin.mpr (.inl ⟨G₁.vertexEquiv.symm u, rfl⟩)⟩
        | .inr v => ⟨pairCode 1 (G₂.vertexEquiv.symm v).1,
            mem_vertices_completeJoin.mpr (.inr ⟨G₂.vertexEquiv.symm v, rfl⟩)⟩
      left_inv := fun w => by
        apply Subtype.ext
        rcases mem_vertices_completeJoin.mp w.2 with ⟨i, hi⟩ | ⟨j, hj⟩
        · simp [hi, pairCode, Nat.unpair_pair]
        · simp [hj, pairCode, Nat.unpair_pair]
      right_inv := by rintro (u | v) <;> simp [pairCode, Nat.unpair_pair] }
  map_rel_iff' := by
    intro w₁ w₂
    rcases mem_vertices_completeJoin.mp w₁.2 with ⟨i₁, hi₁⟩ | ⟨j₁, hj₁⟩ <;>
      rcases mem_vertices_completeJoin.mp w₂.2 with ⟨i₂, hi₂⟩ | ⟨j₂, hj₂⟩
    · simp only [Equiv.coe_fn_mk, hi₁, hi₂, pairCode, Nat.unpair_pair, ↓reduceDIte,
        joinSimple, Graph.induced_adj]
      exact (adj_completeJoin_left i₁ i₂).symm
    · simp only [Equiv.coe_fn_mk, hi₁, hj₂, pairCode, Nat.unpair_pair, ↓reduceDIte,
        one_ne_zero, joinSimple, Graph.induced_adj, true_iff]
      exact adj_completeJoin_cross i₁ j₂
    · simp only [Equiv.coe_fn_mk, hj₁, hi₂, pairCode, Nat.unpair_pair, ↓reduceDIte,
        one_ne_zero, joinSimple, Graph.induced_adj, true_iff]
      exact (adj_completeJoin_cross i₂ j₁).symm
    · simp only [Equiv.coe_fn_mk, hj₁, hj₂, pairCode, Nat.unpair_pair, ↓reduceDIte,
        one_ne_zero, joinSimple, Graph.induced_adj]
      exact (adj_completeJoin_right j₁ j₂).symm

private def gadget4AdjPred (X : Graph) (a b i u j v : ℕ) : Bool :=
  match (b + 4 - a) % 4 with
  | 0 => decide (i ≠ j) || X.adjBool (X.distinctVertices.getD u 0) (X.distinctVertices.getD v 0)
  | 1 => decide (u ≠ j)
  | 2 => true
  | _ => decide (v ≠ i)

private theorem gadget4AdjPred_symm (X : Graph) {a b : ℕ} (ha : a < 4) (hb : b < 4)
    (i u j v : ℕ) :
    gadget4AdjPred X a b i u j v = gadget4AdjPred X b a j v i u := by
  have hadj_symm : X.adjBool (X.distinctVertices.getD u 0) (X.distinctVertices.getD v 0) =
      X.adjBool (X.distinctVertices.getD v 0) (X.distinctVertices.getD u 0) :=
    Bool.eq_iff_iff.mpr (by simp only [Graph.adjBool_eq_true_iff]; exact ⟨.symm, .symm⟩)
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    dsimp only [gadget4AdjPred]
  all_goals first | rfl | (rw [hadj_symm]; simp only [ne_comm])

@[fun_prop]
private theorem unary_ne' {γ : Type} {enc : γ ↪ List Bool} {l r : γ → ℕ}
    (hl : ComputableInPolyTime l enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary) :
    ComputableInPolyTime (fun x => decide (l x ≠ r x)) enc encBool :=
  (bool_not.comp (unary_eq' hl hr)).of_enc_eq fun x => by simp

@[fun_prop]
private theorem computableInPolyTime_gadget4AdjPred_comp {γ : Type} {enc : γ ↪ List Bool}
    {X : γ → Graph} (a b : ℕ) {i u j v : γ → ℕ}
    (hX : ComputableInPolyTime X enc encGraph)
    (hi : ComputableInPolyTime i enc encUnary)
    (hu : ComputableInPolyTime u enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary)
    (hv : ComputableInPolyTime v enc encUnary) :
    ComputableInPolyTime (fun q => gadget4AdjPred (X q) a b (i q) (u q) (j q) (v q))
      enc encBool := by
  unfold gadget4AdjPred
  split <;> fun_prop

private def gadget4 (X : Graph) : Graph :=
  let p := X.distinctVertices.length
  { vertices :=
      [0, 1, 2, 3].flatMap fun a =>
        (List.range p).flatMap fun i =>
          (List.range p).map fun u => tripleCode a i u
    edges :=
      [0, 1, 2, 3].flatMap fun a =>
        [0, 1, 2, 3].flatMap fun b =>
          (List.range p).flatMap fun i =>
            (List.range p).flatMap fun u =>
              (List.range p).flatMap fun j =>
                ((List.range p).filter fun v => gadget4AdjPred X a b i u j v).map fun v =>
                  (tripleCode a i u, tripleCode b j v) }

@[fun_prop]
private theorem computableInPolyTime_gadget4 :
    ComputableInPolyTime gadget4 encGraph encGraph := by
  have hv : ComputableInPolyTime (fun X : Graph => (gadget4 X).vertices)
      encGraph (encList encNat) := by
    dsimp only [gadget4]
    apply flatMapConst [0, 1, 2, 3]; intro a _
    fun_prop
  have he : ComputableInPolyTime (fun X : Graph => (gadget4 X).edges)
      encGraph (encList (encPair encNat encNat)) := by
    dsimp only [gadget4]
    apply flatMapConst [0, 1, 2, 3]; intro a _
    apply flatMapConst [0, 1, 2, 3]; intro b _
    fun_prop
  exact encGraph_mk_polyTime hv he

private theorem mem_vertices_gadget4 {X : Graph} {w : ℕ} :
    w ∈ (gadget4 X).vertices ↔
      ∃ (a : Fin 4) (i u : Fin X.distinctVertices.length), w = tripleCode a.1 i.1 u.1 := by
  simp only [gadget4, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, i, hi, u, hu, rfl⟩
    exact ⟨⟨a, by simp at ha; omega⟩, ⟨i, hi⟩, ⟨u, hu⟩, rfl⟩
  · rintro ⟨⟨a, ha⟩, ⟨i, hi⟩, ⟨u, hu⟩, rfl⟩
    have ha_m : a ∈ ([0, 1, 2, 3] : List ℕ) := by
      rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) with rfl | rfl | rfl | rfl <;> simp
    exact ⟨a, ha_m, i, hi, u, hu, rfl⟩

private theorem adj_gadget4_tripleCode {X : Graph}
    (a b : Fin 4) (i u j v : Fin X.distinctVertices.length) :
    (gadget4 X).toSimpleGraph.Adj (tripleCode a.1 i.1 u.1) (tripleCode b.1 j.1 v.1) ↔
      tripleCode a.1 i.1 u.1 ≠ tripleCode b.1 j.1 v.1 ∧
        gadget4AdjPred X a.1 b.1 i.1 u.1 j.1 v.1 = true := by
  have hedge : ∀ (a' b' : Fin 4) (i' u' j' v' : Fin X.distinctVertices.length),
      (tripleCode a'.1 i'.1 u'.1, tripleCode b'.1 j'.1 v'.1) ∈ (gadget4 X).edges ↔
        gadget4AdjPred X a'.1 b'.1 i'.1 u'.1 j'.1 v'.1 = true := by
    intro a' b' i' u' j' v'
    simp only [gadget4, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      Prod.mk.injEq]
    constructor
    · rintro ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨_, hp⟩, e1, e2⟩
      obtain ⟨rfl, rfl, rfl⟩ := tripleCode_inj.mp e1.symm
      obtain ⟨rfl, rfl, rfl⟩ := tripleCode_inj.mp e2.symm; exact hp
    · intro hp
      have ha_m : a'.1 ∈ ([0, 1, 2, 3] : List ℕ) := by
        rcases (by omega : a'.1 = 0 ∨ a'.1 = 1 ∨ a'.1 = 2 ∨ a'.1 = 3) with h | h | h | h <;>
          simp [h]
      have hb_m : b'.1 ∈ ([0, 1, 2, 3] : List ℕ) := by
        rcases (by omega : b'.1 = 0 ∨ b'.1 = 1 ∨ b'.1 = 2 ∨ b'.1 = 3) with h | h | h | h <;>
          simp [h]
      exact ⟨a'.1, ha_m, b'.1, hb_m, i'.1, i'.2, u'.1, u'.2, j'.1, j'.2, v'.1, ⟨v'.2, hp⟩,
        rfl, rfl⟩
  rw [Graph.toSimpleGraph_adj, hedge a b i u j v, hedge b a j v i u,
    gadget4AdjPred_symm X b.2 a.2 j.1 v.1 i.1 u.1, or_self]

private theorem gadget4_properties {X : Graph} (hne : X.vertices ≠ []) :
    Nonempty {v // v ∈ (gadget4 X).vertices} ∧
      (gadget4 X).indepNum = X.indepNum + 1 ∧
      gadget4 X ∈ OneExtendable := by
  classical
  let p := X.distinctVertices.length
  have hp : 0 < p := by
    rcases List.exists_mem_of_ne_nil X.vertices hne with ⟨v, hv⟩
    exact List.length_pos_of_mem (Graph.mem_distinctVertices.mpr hv)
  have hne_g : Nonempty {v // v ∈ (gadget4 X).vertices} :=
    ⟨⟨tripleCode 0 0 0, mem_vertices_gadget4.mpr ⟨0, ⟨0, hp⟩, ⟨0, hp⟩, rfl⟩⟩⟩
  have hextend : ∀ (a : Fin 4) (i u : Fin p),
      ∃ S : Finset ℕ, (∀ w ∈ S, w ∈ (gadget4 X).vertices) ∧
        (gadget4 X).toSimpleGraph.IsNIndepSet (X.indepNum + 1) S ∧
        tripleCode a.1 i.1 u.1 ∈ S := by
    intro a i u
    obtain ⟨I₀, hI₀⟩ := X.induced.exists_isNIndepSet_indepNum
    let b : Fin 4 := ⟨(a.1 + 1) % 4, Nat.mod_lt _ (by omega)⟩
    have hab_ne : a.1 ≠ b.1 := by have := a.2; dsimp [b]; omega
    have hdiff1 : (b.1 + 4 - a.1) % 4 = 1 := by have := a.2; dsimp [b]; omega
    let emb : {v // v ∈ X.vertices} ↪ ℕ :=
      ⟨fun v => tripleCode b.1 u.1 (X.vertexEquiv.symm v).1, fun v₁ v₂ h =>
        X.vertexEquiv.symm.injective (Fin.ext (tripleCode_inj.mp h).2.2)⟩
    let T : Finset ℕ := I₀.map emb
    have hx_notMem : tripleCode a.1 i.1 u.1 ∉ T := fun hm => by
      obtain ⟨_, -, heq⟩ := Finset.mem_map.mp hm; exact hab_ne (tripleCode_inj.mp heq).1.symm
    refine ⟨insert (tripleCode a.1 i.1 u.1) T, ?_, ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · intro w hw; rcases Finset.mem_insert.mp hw with rfl | hwT
      · exact mem_vertices_gadget4.mpr ⟨a, i, u, rfl⟩
      · obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hwT
        exact mem_vertices_gadget4.mpr ⟨b, u, X.vertexEquiv.symm v, rfl⟩
    · intro x hx y hy hxy hadj
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hxT <;>
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hyT
      · exact hxy rfl
      · obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hyT
        have hp_adj := ((adj_gadget4_tripleCode a b i u u (X.vertexEquiv.symm v)).mp hadj).2
        simp [gadget4AdjPred, hdiff1] at hp_adj
      · obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hxT
        have hp_adj := ((adj_gadget4_tripleCode a b i u u (X.vertexEquiv.symm v)).mp hadj.symm).2
        simp [gadget4AdjPred, hdiff1] at hp_adj
      · obtain ⟨v₁, hv₁, rfl⟩ := Finset.mem_map.mp hxT
        obtain ⟨v₂, hv₂, rfl⟩ := Finset.mem_map.mp hyT
        have hp_adj := ((adj_gadget4_tripleCode b b u (X.vertexEquiv.symm v₁) u
          (X.vertexEquiv.symm v₂)).mp hadj).2
        have hdiff0 : (b.1 + 4 - b.1) % 4 = 0 := by have := b.2; omega
        simp only [gadget4AdjPred, hdiff0, ne_self_iff_false, decide_false, Bool.false_or,
          Graph.adjBool_eq_true_iff] at hp_adj
        rw [← Graph.vertexEquiv_apply, ← Graph.vertexEquiv_apply,
          X.vertexEquiv.apply_symm_apply, X.vertexEquiv.apply_symm_apply] at hp_adj
        exact hI₀.isIndepSet hv₁ hv₂ (fun h => hxy (congrArg emb h)) hp_adj
    · rw [Finset.card_insert_of_notMem hx_notMem, Finset.card_map, hI₀.card_eq]; rfl
  have hub : (gadget4 X).indepNum ≤ X.indepNum + 1 := by
    obtain ⟨S, hSV, hS⟩ :=
      mem_IndependentSet_iff.mp (Graph.indepNum_mem_IndependentSet (gadget4 X))
    dsimp only at hSV hS
    rw [← hS.card_eq]
    let lay (w : ℕ) : ℕ := (Nat.unpair w).1
    let cpy (w : ℕ) : ℕ := (Nat.unpair (Nat.unpair w).2).1
    let vrt (w : ℕ) : ℕ := (Nat.unpair (Nat.unpair w).2).2
    have hdec : ∀ w ∈ S, lay w < 4 ∧ cpy w < p ∧ vrt w < p ∧
        w = tripleCode (lay w) (cpy w) (vrt w) := fun w hw => by
      obtain ⟨a, i, u, rfl⟩ := mem_vertices_gadget4.mp (hSV w hw)
      dsimp only [lay, cpy, vrt, tripleCode]
      simp only [Nat.unpair_pair]
      exact ⟨a.2, i.2, u.2, trivial⟩
    have hcode : ∀ w ∈ S, ∀ a' c' v', lay w = a' → cpy w = c' → vrt w = v' →
        w = tripleCode a' c' v' := fun w hw _ _ _ hl hc hv => by
      rw [← hl, ← hc, ← hv]; exact (hdec w hw).2.2.2
    have hcopy_le : ∀ (a : Fin 4) (i : Fin p),
        (S.filter fun w => lay w = a.1 ∧ cpy w = i.1).card ≤ X.indepNum := by
      intro a i
      set F := S.filter fun w => lay w = a.1 ∧ cpy w = i.1
      let emb : {w // w ∈ F} ↪ {v // v ∈ X.vertices} :=
        ⟨fun w => X.vertexEquiv ⟨vrt w.1, (hdec w.1 (Finset.mem_filter.mp w.2).1).2.2.1⟩,
          fun w₁ w₂ h => by
            have hu := congrArg Fin.val (X.vertexEquiv.injective h)
            obtain ⟨hw₁, ha₁, hi₁⟩ := Finset.mem_filter.mp w₁.2
            obtain ⟨hw₂, ha₂, hi₂⟩ := Finset.mem_filter.mp w₂.2
            exact Subtype.ext ((hdec w₁.1 hw₁).2.2.2.trans
              (by rw [ha₁, hi₁, ← ha₂, ← hi₂]; dsimp at hu; rw [hu, ← (hdec w₂.1 hw₂).2.2.2]))⟩
      have hind_F : X.induced.IsIndepSet ((Finset.univ.map emb : Finset _) : Set _) := by
        intro v₁ hv₁ v₂ hv₂ hne_v hadj_v
        obtain ⟨w₁, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hv₁)
        obtain ⟨w₂, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hv₂)
        obtain ⟨hw₁, ha₁, hi₁⟩ := Finset.mem_filter.mp w₁.2
        obtain ⟨hw₂, ha₂, hi₂⟩ := Finset.mem_filter.mp w₂.2
        have hw_ne : w₁.1 ≠ w₂.1 := fun h => hne_v (congrArg emb (Subtype.ext h))
        have hdiff0 : (a.1 + 4 - a.1) % 4 = 0 := by have := a.2; omega
        have hc₁ := hcode w₁.1 hw₁ a.1 i.1 (vrt w₁.1) ha₁ hi₁ rfl
        have hc₂ := hcode w₂.1 hw₂ a.1 i.1 (vrt w₂.1) ha₂ hi₂ rfl
        have emb_val : ∀ w : {w // w ∈ F},
            (emb w).1 = X.distinctVertices.getD (vrt w.1) 0 := fun w =>
          X.vertexEquiv_apply ⟨vrt w.1, (hdec w.1 (Finset.mem_filter.mp w.2).1).2.2.1⟩
        rw [Graph.induced_adj, emb_val, emb_val] at hadj_v
        have hadj_g : (gadget4 X).toSimpleGraph.Adj w₁.1 w₂.1 := by
          rw [hc₁, hc₂]
          refine (adj_gadget4_tripleCode a a i ⟨vrt w₁.1, (hdec w₁.1 hw₁).2.2.1⟩ i
            ⟨vrt w₂.1, (hdec w₂.1 hw₂).2.2.1⟩).mpr ⟨by rwa [← hc₁, ← hc₂], ?_⟩
          simp only [gadget4AdjPred, hdiff0, Bool.or_eq_true, Graph.adjBool_eq_true_iff]
          exact Or.inr hadj_v
        exact hS.isIndepSet hw₁ hw₂ hw_ne hadj_g
      simpa [Graph.indepNum] using hind_F.card_le_indepNum
    have hlayer_le : ∀ a : Fin 4, (S.filter fun w => lay w = a.1).card ≤ X.indepNum := by
      intro a
      set L := S.filter fun w => lay w = a.1
      by_cases hL_emp : L = ∅
      · simp [hL_emp]
      · obtain ⟨w₀, hw₀L⟩ := Finset.nonempty_iff_ne_empty.mpr hL_emp
        obtain ⟨hw₀S, ha₀⟩ := Finset.mem_filter.mp hw₀L
        let i₀ : Fin p := ⟨cpy w₀, (hdec w₀ hw₀S).2.1⟩
        have hsub : L ⊆ S.filter fun w => lay w = a.1 ∧ cpy w = i₀.1 := by
          intro w hwL; obtain ⟨hwS, ha⟩ := Finset.mem_filter.mp hwL
          refine Finset.mem_filter.mpr ⟨hwS, ha, ?_⟩; by_contra hij
          have hw_ne : w ≠ w₀ := fun h => hij (h ▸ rfl)
          have hcw := hcode w hwS a.1 (cpy w) (vrt w) ha rfl rfl
          have hcw₀ := hcode w₀ hw₀S a.1 i₀.1 (vrt w₀) ha₀ rfl rfl
          have hadj_g : (gadget4 X).toSimpleGraph.Adj w w₀ := by
            rw [hcw, hcw₀]
            refine (adj_gadget4_tripleCode a a ⟨cpy w, (hdec w hwS).2.1⟩
              ⟨vrt w, (hdec w hwS).2.2.1⟩ i₀ ⟨vrt w₀, (hdec w₀ hw₀S).2.2.1⟩).mpr
              ⟨by rwa [← hcw, ← hcw₀], by simp [gadget4AdjPred, hij]⟩
          exact hS.isIndepSet hwS hw₀S hw_ne hadj_g
        exact (Finset.card_le_card hsub).trans (hcopy_le a i₀)
    have hopp : ∀ (a b : Fin 4), (b.1 + 4 - a.1) % 4 = 2 →
        ∀ w ∈ S, lay w = a.1 → ∀ w' ∈ S, lay w' ≠ b.1 := by
      intro a b hdiff2 w hwS ha w' hw'S hb
      have hw_ne : w ≠ w' := fun h => by subst h; have := a.2; omega
      have hcw := hcode w hwS a.1 (cpy w) (vrt w) ha rfl rfl
      have hcw' := hcode w' hw'S b.1 (cpy w') (vrt w') hb rfl rfl
      have hadj_g : (gadget4 X).toSimpleGraph.Adj w w' := by
        rw [hcw, hcw']
        refine (adj_gadget4_tripleCode a b ⟨cpy w, (hdec w hwS).2.1⟩ ⟨vrt w, (hdec w hwS).2.2.1⟩
          ⟨cpy w', (hdec w' hw'S).2.1⟩ ⟨vrt w', (hdec w' hw'S).2.2.1⟩).mpr
          ⟨by rwa [← hcw, ← hcw'], by simp [gadget4AdjPred, hdiff2]⟩
      exact hS.isIndepSet hwS hw'S hw_ne hadj_g
    let occ (a : ℕ) : Prop := ∃ w ∈ S, lay w = a
    have hno02 : ¬ (occ 0 ∧ occ 2) := fun ⟨⟨w, hw, h0⟩, ⟨w', hw', h2⟩⟩ =>
      hopp 0 2 (by decide) w hw h0 w' hw' h2
    have hno13 : ¬ (occ 1 ∧ occ 3) := fun ⟨⟨w, hw, h1⟩, ⟨w', hw', h3⟩⟩ =>
      hopp 1 3 (by decide) w hw h1 w' hw' h3
    have hconsec : ∃ a : Fin 4, ∀ w ∈ S, lay w = a.1 ∨ lay w = (a.1 + 1) % 4 := by
      by_cases h0 : occ 0
      · by_cases h1 : occ 1
        · refine ⟨0, fun w hw => ?_⟩; have := (hdec w hw).1
          rcases (by omega : lay w = 0 ∨ lay w = 1 ∨ lay w = 2 ∨ lay w = 3) with h | h | h | h
          exacts [.inl h, .inr h, (hno02 ⟨h0, ⟨w, hw, h⟩⟩).elim, (hno13 ⟨h1, ⟨w, hw, h⟩⟩).elim]
        · refine ⟨3, fun w hw => ?_⟩; have := (hdec w hw).1
          rcases (by omega : lay w = 0 ∨ lay w = 1 ∨ lay w = 2 ∨ lay w = 3) with h | h | h | h
          exacts [.inr h, (h1 ⟨w, hw, h⟩).elim, (hno02 ⟨h0, ⟨w, hw, h⟩⟩).elim, .inl h]
      · by_cases h1 : occ 1
        · refine ⟨1, fun w hw => ?_⟩; have := (hdec w hw).1
          rcases (by omega : lay w = 0 ∨ lay w = 1 ∨ lay w = 2 ∨ lay w = 3) with h | h | h | h
          exacts [(h0 ⟨w, hw, h⟩).elim, .inl h, .inr h, (hno13 ⟨h1, ⟨w, hw, h⟩⟩).elim]
        · refine ⟨2, fun w hw => ?_⟩; have := (hdec w hw).1
          rcases (by omega : lay w = 0 ∨ lay w = 1 ∨ lay w = 2 ∨ lay w = 3) with h | h | h | h
          exacts [(h0 ⟨w, hw, h⟩).elim, (h1 ⟨w, hw, h⟩).elim, .inl h, .inr h]
    obtain ⟨a, hS_ab⟩ := hconsec
    let b : Fin 4 := ⟨(a.1 + 1) % 4, Nat.mod_lt _ (by omega)⟩
    have hab_ne : a.1 ≠ b.1 := by have := a.2; dsimp [b]; omega
    set L_a := S.filter fun w => lay w = a.1
    set L_b := S.filter fun w => lay w = b.1
    have hdisj : Disjoint L_a L_b := Finset.disjoint_left.mpr fun w ha hb =>
      hab_ne ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
    have hunion : S = L_a ∪ L_b := by
      ext w; simp only [L_a, L_b, Finset.mem_union, Finset.mem_filter]
      exact ⟨fun hw => (hS_ab w hw).imp (⟨hw, ·⟩) (⟨hw, ·⟩), fun h => h.elim And.left And.left⟩
    rw [hunion, Finset.card_union_of_disjoint hdisj]
    by_cases ha_emp : L_a = ∅
    · rw [ha_emp, Finset.card_empty, zero_add]; exact (hlayer_le b).trans (Nat.le_succ _)
    · by_cases hb_emp : L_b = ∅
      · rw [hb_emp, Finset.card_empty]; exact Nat.le_succ_of_le (hlayer_le a)
      · obtain ⟨w₁, hw₁a⟩ := Finset.nonempty_iff_ne_empty.mpr ha_emp
        obtain ⟨w₂, hw₂b⟩ := Finset.nonempty_iff_ne_empty.mpr hb_emp
        obtain ⟨hw₁S, ha₁⟩ := Finset.mem_filter.mp hw₁a
        obtain ⟨hw₂S, hb₂⟩ := Finset.mem_filter.mp hw₂b
        have hdiff1 : (b.1 + 4 - a.1) % 4 = 1 := by have := a.2; dsimp [b]; omega
        have hu_eq : ∀ w ∈ L_a, vrt w = cpy w₂ := by
          intro w hwa; obtain ⟨hwS, ha⟩ := Finset.mem_filter.mp hwa; by_contra huj
          have hw_ne : w ≠ w₂ := fun h => by subst h; exact hab_ne (ha.symm.trans hb₂)
          have hcw := hcode w hwS a.1 (cpy w) (vrt w) ha rfl rfl
          have hcw₂ := hcode w₂ hw₂S b.1 (cpy w₂) (vrt w₂) hb₂ rfl rfl
          have hadj_g : (gadget4 X).toSimpleGraph.Adj w w₂ := by
            rw [hcw, hcw₂]
            refine (adj_gadget4_tripleCode a b ⟨cpy w, (hdec w hwS).2.1⟩
              ⟨vrt w, (hdec w hwS).2.2.1⟩ ⟨cpy w₂, (hdec w₂ hw₂S).2.1⟩
              ⟨vrt w₂, (hdec w₂ hw₂S).2.2.1⟩).mpr
              ⟨by rwa [← hcw, ← hcw₂], by simp [gadget4AdjPred, hdiff1, huj]⟩
          exact hS.isIndepSet hwS hw₂S hw_ne hadj_g
        have hLa_sub : L_a ⊆ {w₁} := by
          intro w hwa; rw [Finset.mem_singleton]; by_contra hw_ne
          obtain ⟨hwS, ha⟩ := Finset.mem_filter.mp hwa
          have hi_ne : cpy w ≠ cpy w₁ := fun hi_eq => hw_ne (by
            rw [(hdec w hwS).2.2.2, (hdec w₁ hw₁S).2.2.2, ha, ha₁, hi_eq,
              hu_eq w hwa, hu_eq w₁ hw₁a])
          have hcw := hcode w hwS a.1 (cpy w) (vrt w) ha rfl rfl
          have hcw₁ := hcode w₁ hw₁S a.1 (cpy w₁) (vrt w₁) ha₁ rfl rfl
          have hadj_g : (gadget4 X).toSimpleGraph.Adj w w₁ := by
            rw [hcw, hcw₁]
            refine (adj_gadget4_tripleCode a a ⟨cpy w, (hdec w hwS).2.1⟩
              ⟨vrt w, (hdec w hwS).2.2.1⟩ ⟨cpy w₁, (hdec w₁ hw₁S).2.1⟩
              ⟨vrt w₁, (hdec w₁ hw₁S).2.2.1⟩).mpr
              ⟨by rwa [← hcw, ← hcw₁], by simp [gadget4AdjPred, hi_ne]⟩
          exact hS.isIndepSet hwS hw₁S hw_ne hadj_g
        have hLa_card : L_a.card ≤ 1 := (Finset.card_le_card hLa_sub).trans (by simp)
        have hLb_card : L_b.card ≤ X.indepNum := hlayer_le b
        omega
  have hind_eq : (gadget4 X).indepNum = X.indepNum + 1 := by
    refine le_antisymm hub ?_
    obtain ⟨S₀, hS₀V, hS₀, -⟩ := hextend 0 ⟨0, hp⟩ ⟨0, hp⟩
    rw [Graph.le_indepNum_iff, mem_IndependentSet_iff_mk]; exact ⟨S₀, hS₀V, hS₀⟩
  refine ⟨hne_g, hind_eq, ?_⟩
  rw [mem_OneExtendable_iff, hind_eq]
  intro w hw; obtain ⟨a, i, u, rfl⟩ := mem_vertices_gadget4.mp hw; exact hextend a i u

/-- **`EqualIndepNum` reduces in polynomial time to `OneExtendable`.** -/
theorem polyTimeReducible_EqualIndepNum_OneExtendable :
    PolyTimeReducible (encPair encGraph encGraph) encGraph EqualIndepNum OneExtendable := by
  let pad : Graph → Graph := fun G => disjointUnionList [G, edgelessGraph 1]
  have hpad_pt : ComputableInPolyTime pad encGraph encGraph :=
    (computableInPolyTime_disjointUnionList.comp ((cons encGraph).comp
      (ComputableInPolyTime.id'.prod
        ((cons encGraph).comp
          ((computableInPolyTime_edgelessGraph.comp (const 1)).prod (const [])))))).of_enc_eq
      fun _ => congrArg encGraph (by dsimp only [pad, Function.comp_apply])
  have hpad_ne : ∀ G : Graph, (pad G).vertices ≠ [] := fun _ =>
    List.ne_nil_of_mem (mem_vertices_disjointUnionList.mpr
      ⟨⟨1, by simp⟩, ⟨0, by simp [distinctVertices_edgelessGraph]⟩, rfl⟩)
  have hpad_ind : ∀ G : Graph, (pad G).indepNum = G.indepNum + 1 := fun G => by
    simp [pad, indepNum_disjointUnionList, indepNum_edgelessGraph]
  let red : Graph × Graph → Graph := fun p =>
    completeJoin (gadget4 (pad p.1)) (gadget4 (pad p.2))
  have hred_pt : ComputableInPolyTime red (encPair encGraph encGraph) encGraph :=
    (computableInPolyTime_completeJoin.comp
      ((computableInPolyTime_gadget4.comp (hpad_pt.comp (fst _ _))).prod
        (computableInPolyTime_gadget4.comp (hpad_pt.comp (snd _ _))))).of_enc_eq
      fun _ => congrArg encGraph (by dsimp only [red, Function.comp_apply])
  refine ⟨red, hred_pt, fun p => ?_⟩
  obtain ⟨hne₁, hind₁, h1ext₁⟩ := gadget4_properties (hpad_ne p.1)
  obtain ⟨hne₂, hind₂, h1ext₂⟩ := gadget4_properties (hpad_ne p.2)
  rw [EqualIndepNum, Set.mem_ofPred_eq]
  change _ ↔ IsOneExtSimple (red p).induced
  dsimp only [red]
  rw [isOneExtSimple_congr_iso (completeJoinIso _ _), isOneExtSimple_joinSimple_iff]
  change _ ↔ (gadget4 (pad p.1) ∈ OneExtendable ∧ gadget4 (pad p.2) ∈ OneExtendable ∧
    (gadget4 (pad p.1)).indepNum = (gadget4 (pad p.2)).indepNum)
  rw [hind₁, hind₂, hpad_ind, hpad_ind]
  exact ⟨fun h => ⟨h1ext₁, h1ext₂, by omega⟩, fun ⟨_, _, h⟩ => by omega⟩

/-- **`OneExtendable` is $\Theta_2^p$-hard.** -/
theorem OneExtendable_pnpLogHard : PolyTimeHard @PNPLog encGraph OneExtendable :=
  EqualIndepNum_pnpLogHard.trans polyTimeReducible_EqualIndepNum_OneExtendable

/-- **`OneExtendable` is $\Theta_2^p$-complete.** -/
theorem OneExtendable_pnpLogComplete : PolyTimeComplete @PNPLog encGraph OneExtendable :=
  ⟨OneExtendable_mem_PNPLog, OneExtendable_pnpLogHard⟩

/-! ### Inductive join reduction and $\Theta_2^p$-hardness of `OneExtendableKPartition k` -/

private def induceJoinSimpleColorIso {V₁ V₂ : Type*} (H₁ : SimpleGraph V₁) (H₂ : SimpleGraph V₂)
    {k : ℕ} (c : V₁ ⊕ V₂ → Fin k) (r : Fin k) :
    (joinSimple H₁ H₂).induce {x | c x = r} ≃g
      joinSimple (H₁.induce {u | c (.inl u) = r}) (H₂.induce {v | c (.inr v) = r}) where
  toEquiv :=
    { toFun := fun | ⟨.inl u, h⟩ => .inl ⟨u, h⟩ | ⟨.inr v, h⟩ => .inr ⟨v, h⟩
      invFun := fun | .inl ⟨u, h⟩ => ⟨.inl u, h⟩ | .inr ⟨v, h⟩ => ⟨.inr v, h⟩
      left_inv := by rintro ⟨u | v, _⟩ <;> rfl
      right_inv := by rintro (⟨_, _⟩ | ⟨_, _⟩) <;> rfl }
  map_rel_iff' := by rintro ⟨u | v, _⟩ ⟨u' | v', _⟩ <;> rfl

private theorem isOneExtSimple_bot {V : Type*} [Finite V] : IsOneExtSimple (⊥ : SimpleGraph V)
    := by
  cases nonempty_fintype V
  intro u
  have hind : (⊥ : SimpleGraph V).indepNum = Fintype.card V :=
    le_antisymm
      (by rw [← SimpleGraph.cliqueNum_compl, ← Nat.card_eq_fintype_card]
          exact (⊥ : SimpleGraph V)ᶜ.cliqueNum_le_natCard)
      (by simpa using (show (⊥ : SimpleGraph V).IsIndepSet ((Finset.univ : Finset V) : Set V) by
          intro _ _ _ _ _; simp).card_le_indepNum)
  exact ⟨Finset.univ, ⟨by intro _ _ _ _ _; simp, by rw [Finset.card_univ, hind]⟩,
    Finset.mem_univ u⟩

private theorem isOneExtSimple_induce_congr {V : Type*} {H : SimpleGraph V} {s t : Set V}
    (hst : s = t) : IsOneExtSimple (H.induce s) ↔ IsOneExtSimple (H.induce t) := by
  subst hst; rfl

/-- For every $k \ge 1$, `OneExtendableKPartition k` reduces in polynomial time to
`OneExtendableKPartition (k + 1)` via $G \mapsto G * \overline{K}_{(k + 1)|V(G)| + 1}$. -/
theorem polyTimeReducible_OneExtendableKPartition_succ {k : ℕ} (hk : 1 ≤ k) :
    PolyTimeReducible encGraph encGraph
      (OneExtendableKPartition k) (OneExtendableKPartition (k + 1)) := by
  classical
  let mOf : Graph → ℕ := fun G => (k + 1) * G.distinctVertices.length + 1
  have hmOf_pt : ComputableInPolyTime mOf encGraph encUnary :=
    unary_add' (unary_mul' (const (k + 1))
      ((length_list encNat).comp Graph.computableInPolyTime_distinctVertices)) (const 1)
  let red : Graph → Graph := fun G => completeJoin G (edgelessGraph (mOf G))
  have hred_pt : ComputableInPolyTime red encGraph encGraph :=
    (computableInPolyTime_completeJoin.comp
      (ComputableInPolyTime.id'.prod (computableInPolyTime_edgelessGraph.comp hmOf_pt))).of_enc_eq
      fun _ => congrArg encGraph (by dsimp only [red, Function.comp_apply])
  refine ⟨red, hred_pt, fun G => ?_⟩
  set n := G.distinctVertices.length
  set M := mOf G
  set W₂ := {v // v ∈ (edgelessGraph M).vertices}
  let φ := completeJoinIso G (edgelessGraph M)
  have hcard_G : Fintype.card {v // v ∈ G.vertices} = n := by
    rw [Graph.card_vertexSubtype, ← Graph.length_distinctVertices]
  have hcard_W₂ : Fintype.card W₂ = (k + 1) * n + 1 := by
    rw [Graph.card_vertexSubtype, ← Graph.length_distinctVertices, distinctVertices_edgelessGraph]
  have hpart_iso : (red G ∈ OneExtendableKPartition (k + 1)) ↔
      ∃ c' : {v // v ∈ G.vertices} ⊕ W₂ → Fin (k + 1), ∀ r : Fin (k + 1),
        IsOneExtSimple ((joinSimple G.induced (⊥ : SimpleGraph W₂)).induce {x | c' x = r}) := by
    simp only [OneExtendableKPartition, Set.mem_ofPred_eq]
    have hbot := edgelessGraph_induced_eq_bot M
    constructor
    · rintro ⟨c₀, hc₀⟩
      refine ⟨c₀ ∘ φ.symm, fun r => ?_⟩
      let ψ : (red G).induced.induce {w | c₀ w = r} ≃g
          (joinSimple G.induced (⊥ : SimpleGraph W₂)).induce {x | c₀ (φ.symm x) = r} :=
        ⟨⟨fun ⟨w, hw⟩ => ⟨φ w, by simpa using hw⟩,
          fun ⟨x, hx⟩ => ⟨φ.symm x, hx⟩,
          fun ⟨w, _⟩ => Subtype.ext (φ.symm_apply_apply w),
          fun ⟨x, _⟩ => Subtype.ext (φ.apply_symm_apply x)⟩,
         by
          rintro ⟨w₁, _⟩ ⟨w₂, _⟩
          dsimp only [Equiv.coe_fn_mk]
          change (joinSimple G.induced ⊥).Adj (φ w₁) (φ w₂) ↔ (red G).induced.Adj w₁ w₂
          rw [← hbot]
          exact φ.map_adj_iff⟩
      exact (isOneExtSimple_congr_iso ψ).mp (hc₀ r)
    · rintro ⟨c', hc'⟩
      refine ⟨c' ∘ φ, fun r => ?_⟩
      let ψ : (red G).induced.induce {w | c' (φ w) = r} ≃g
          (joinSimple G.induced (⊥ : SimpleGraph W₂)).induce {x | c' x = r} :=
        ⟨⟨fun ⟨w, hw⟩ => ⟨φ w, hw⟩,
          fun ⟨x, hx⟩ => ⟨φ.symm x, by simpa using hx⟩,
          fun ⟨w, _⟩ => Subtype.ext (φ.symm_apply_apply w),
          fun ⟨x, _⟩ => Subtype.ext (φ.apply_symm_apply x)⟩,
         by
          rintro ⟨w₁, _⟩ ⟨w₂, _⟩
          dsimp only [Equiv.coe_fn_mk]
          change (joinSimple G.induced ⊥).Adj (φ w₁) (φ w₂) ↔ (red G).induced.Adj w₁ w₂
          rw [← hbot]
          exact φ.map_adj_iff⟩
      exact (isOneExtSimple_congr_iso ψ).mpr (hc' r)
  rw [hpart_iso]
  constructor
  · rintro ⟨c, hc⟩
    let c' : {v // v ∈ G.vertices} ⊕ W₂ → Fin (k + 1) :=
      Sum.elim (Fin.castSucc ∘ c) (fun _ => Fin.last k)
    refine ⟨c', fun r => ?_⟩
    rw [isOneExtSimple_congr_iso (induceJoinSimpleColorIso G.induced (⊥ : SimpleGraph W₂) c' r)]
    rcases Fin.eq_castSucc_or_eq_last r with ⟨i, rfl⟩ | rfl
    · have hemp : IsEmpty {w : W₂ | c' (.inr w) = Fin.castSucc i} :=
        ⟨fun ⟨_, h⟩ => (Fin.castSucc_lt_last i).ne' h⟩
      let isoL : joinSimple (G.induced.induce {u | c' (.inl u) = Fin.castSucc i})
          ((⊥ : SimpleGraph W₂).induce {w | c' (.inr w) = Fin.castSucc i}) ≃g
          G.induced.induce {u | c u = i} :=
        ⟨⟨fun | .inl ⟨u, h⟩ => ⟨u, Fin.castSucc_inj.mp h⟩ | .inr w => hemp.elim w,
          fun ⟨u, h⟩ => .inl ⟨u, congrArg Fin.castSucc h⟩,
          by rintro (⟨_, _⟩ | w); exacts [rfl, hemp.elim w], fun _ => rfl⟩,
         by rintro (⟨_, _⟩ | w) (⟨_, _⟩ | w') <;>
            first | rfl | exact hemp.elim w | exact hemp.elim w'⟩
      exact (isOneExtSimple_congr_iso isoL).mpr (hc i)
    · have hemp : IsEmpty {u : {v // v ∈ G.vertices} | c' (.inl u) = Fin.last k} :=
        ⟨fun ⟨_, h⟩ => (Fin.castSucc_lt_last _).ne h⟩
      let isoR : joinSimple (G.induced.induce {u | c' (.inl u) = Fin.last k})
          ((⊥ : SimpleGraph W₂).induce {w | c' (.inr w) = Fin.last k}) ≃g
          (⊥ : SimpleGraph {w : W₂ | c' (.inr w) = Fin.last k}) :=
        ⟨⟨fun | .inl u => hemp.elim u | .inr w => w, Sum.inr,
          by rintro (u | _); exacts [hemp.elim u, rfl], fun _ => rfl⟩,
         by rintro (u | _) (u' | _) <;>
            first | rfl | exact hemp.elim u | exact hemp.elim u'⟩
      exact (isOneExtSimple_congr_iso isoR).mpr isOneExtSimple_bot
  · rintro ⟨c', hc'⟩
    have hmul_lt : Fintype.card (Fin (k + 1)) * n < Fintype.card W₂ := by
      rw [Fintype.card_fin, hcard_W₂]; omega
    obtain ⟨c₀, hc₀_gt⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (fun w : W₂ => c' (.inr w)) hmul_lt
    have hG_avoids : ∀ u : {v // v ∈ G.vertices}, c' (.inl u) ≠ c₀ := by
      intro u₀ hu₀
      have hneL : Nonempty {u : {v // v ∈ G.vertices} | c' (.inl u) = c₀} := ⟨⟨u₀, hu₀⟩⟩
      have hcardR : n < Fintype.card {w : W₂ | c' (.inr w) = c₀} := by rwa [Fintype.card_subtype]
      have hneR : Nonempty {w : W₂ | c' (.inr w) = c₀} :=
        Fintype.card_pos_iff.mp (Nat.lt_of_le_of_lt (Nat.zero_le n) hcardR)
      have h1ext_join := (isOneExtSimple_congr_iso
        (induceJoinSimpleColorIso G.induced (⊥ : SimpleGraph W₂) c' c₀)).mp (hc' c₀)
      obtain ⟨-, -, heq_ind⟩ := isOneExtSimple_joinSimple_iff.mp h1ext_join
      have hindR : ((⊥ : SimpleGraph W₂).induce {w : W₂ | c' (.inr w) = c₀}).indepNum =
          Fintype.card {w : W₂ | c' (.inr w) = c₀} := by
        let SubR := {w : W₂ | c' (.inr w) = c₀}
        have hbot : (⊥ : SimpleGraph W₂).induce {w : W₂ | c' (.inr w) = c₀} =
            (⊥ : SimpleGraph SubR) := by ext; rfl
        rw [hbot]
        exact le_antisymm
          (by rw [← SimpleGraph.cliqueNum_compl, ← Nat.card_eq_fintype_card]
              exact (⊥ : SimpleGraph SubR)ᶜ.cliqueNum_le_natCard)
          (by rw [← Finset.card_univ]
              exact (show (⊥ : SimpleGraph SubR).IsIndepSet
                ((Finset.univ : Finset SubR) : Set SubR) by
                  intro _ _ _ _ _; simp).card_le_indepNum)
      have hindL : (G.induced.induce {u | c' (.inl u) = c₀}).indepNum ≤ n := by
        rw [← SimpleGraph.cliqueNum_compl]
        exact (G.induced.induce {u | c' (.inl u) = c₀})ᶜ.cliqueNum_le_natCard.trans
          (by rw [Nat.card_eq_fintype_card]; exact (Fintype.card_subtype_le _).trans hcard_G.le)
      omega
    let eqv : {r : Fin (k + 1) // r ≠ c₀} ≃ Fin k :=
      { toFun := fun r =>
          if _h : r.1.1 < c₀.1 then ⟨r.1.1, by omega⟩
          else ⟨r.1.1 - 1, by have := Fin.val_ne_of_ne r.2; omega⟩
        invFun := fun i =>
          if _h : i.1 < c₀.1 then
            ⟨⟨i.1, by omega⟩, fun h => by
              have hval : i.1 = c₀.1 := congrArg Fin.val h
              omega⟩
          else
            ⟨⟨i.1 + 1, by omega⟩, fun h => by
              have hval : i.1 + 1 = c₀.1 := congrArg Fin.val h
              omega⟩
        left_inv := fun ⟨r, hr⟩ => by
          have hrne : r.1 ≠ c₀.1 := Fin.val_ne_of_ne hr
          apply Subtype.ext; apply Fin.ext
          by_cases h1 : r.1 < c₀.1
          · simp [h1]
          · have h2 : ¬ (r.1 - 1 < c₀.1) := by omega
            simp [h1, h2]; omega
        right_inv := fun i => by
          apply Fin.ext
          by_cases h1 : i.1 < c₀.1
          · simp [h1]
          · have h2 : ¬ (i.1 + 1 < c₀.1) := by omega
            simp [h1, h2] }
    refine ⟨fun u => eqv ⟨c' (.inl u), hG_avoids u⟩, fun i => ?_⟩
    let r := eqv.symm i
    have hset : {u : {v // v ∈ G.vertices} | eqv ⟨c' (.inl u), hG_avoids u⟩ = i} =
        {u | c' (.inl u) = r.1} := by
      ext u
      exact ⟨fun h => congrArg Subtype.val (eqv.eq_symm_apply.mpr h),
        fun h => eqv.eq_symm_apply.mp (Subtype.ext h)⟩
    change IsOneExtSimple (G.induced.induce {u | eqv ⟨c' (.inl u), hG_avoids u⟩ = i})
    rw [isOneExtSimple_induce_congr hset]
    by_cases hneL : Nonempty {u : {v // v ∈ G.vertices} | c' (.inl u) = r.1}
    · have h1ext_join := (isOneExtSimple_congr_iso
        (induceJoinSimpleColorIso G.induced (⊥ : SimpleGraph W₂) c' r.1)).mp (hc' r.1)
      exact (isOneExtSimple_joinSimple_left h1ext_join).1
    · exact fun u => (hneL ⟨u⟩).elim

/-- **`OneExtendableKPartition k` is $\Theta_2^p$-hard for every fixed $k \ge 1$.** -/
theorem OneExtendableKPartition_pnpLogHard {k : ℕ} (hk : 1 ≤ k) :
    PolyTimeHard @PNPLog encGraph (OneExtendableKPartition k) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = d + 1 := ⟨k - 1, by omega⟩
  clear hk
  induction d with
  | zero => rw [Nat.zero_add, oneExtendableKPartition_one]; exact OneExtendable_pnpLogHard
  | succ d ih => exact ih.trans (polyTimeReducible_OneExtendableKPartition_succ (Nat.succ_pos d))

end Cslib.Complexity
