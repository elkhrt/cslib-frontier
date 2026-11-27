/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.List.Chain
public import Mathlib.Logic.Relation

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card

/-!
# Independent Set Reconfiguration Under Token Jumping

This module develops independent set reconfiguration under the token jumping (TJ) rule on simple
graphs (`SimpleGraph V`). Two finite independent sets `I` and `J` are adjacent under a single token
jump (`TokenJumpAdj`) when `J` is obtained from `I` by replacing one vertex `v ∈ I` with a vertex
`w ∉ I`, formulated without decidable equality on `V`. We construct the token jumping
reconfiguration graph `tokenJumpGraph`, establish isomorphism invariance `Iso.tokenJumpGraphIso`,
develop reachability (`TokenJumpReachable`), subset-restricted reachability
(`TokenJumpReachableWithin`), induced-subgraph transport, and chain characterizations
(`IsTokenJumpSeq`). We then prove structural reconfiguration and independent-set bounds:
reconfiguration inside a common independent set, 2-token reconfiguration in `C_4`-free subgraphs,
and independent-set lower bounds from proper colorings, forests, single-vertex deletions yielding
forests, and connected graphs of maximum degree at most `2`.

## Main definitions

- `CslibFrontier.SimpleGraph.TokenJumpAdj`
- `CslibFrontier.SimpleGraph.tokenJumpGraph`
- `CslibFrontier.SimpleGraph.Iso.tokenJumpGraphIso`
- `CslibFrontier.SimpleGraph.TokenJumpReachable`
- `CslibFrontier.SimpleGraph.TokenJumpReachableWithin`
- `CslibFrontier.SimpleGraph.IsTokenJumpSeq`

## Main results

- `CslibFrontier.SimpleGraph.tokenJumpAdj_iff_insert_erase`,
  `CslibFrontier.SimpleGraph.tokenJumpAdj_iff_sdiff_card_eq_one`,
  `CslibFrontier.SimpleGraph.TokenJumpAdj.symm`,
  `CslibFrontier.SimpleGraph.TokenJumpAdj.irrefl`,
  `CslibFrontier.SimpleGraph.TokenJumpAdj.card_eq`,
  `CslibFrontier.SimpleGraph.TokenJumpAdj.sdiff_card_eq_one`,
  `CslibFrontier.SimpleGraph.Iso.tokenJumpAdj_iff`,
  `CslibFrontier.SimpleGraph.tokenJumpAdj_induce_iff`
- `CslibFrontier.SimpleGraph.tokenJumpGraph_adj`,
  `CslibFrontier.SimpleGraph.Iso.tokenJumpGraphIso_refl`,
  `CslibFrontier.SimpleGraph.Iso.tokenJumpGraphIso_trans`
- `CslibFrontier.SimpleGraph.TokenJumpReachable.symm`,
  `CslibFrontier.SimpleGraph.TokenJumpReachable.card_eq`,
  `CslibFrontier.SimpleGraph.Iso.tokenJumpReachable_iff`,
  `CslibFrontier.SimpleGraph.tokenJumpReachable_iff_reachable_tokenJumpGraph`
- `CslibFrontier.SimpleGraph.TokenJumpReachableWithin.mono_set`,
  `CslibFrontier.SimpleGraph.tokenJumpReachable_induce_iff`,
  `CslibFrontier.SimpleGraph.tokenJumpReachableWithin_iff_induce`
- `CslibFrontier.SimpleGraph.IsTokenJumpSeq.reverse`,
  `CslibFrontier.SimpleGraph.IsTokenJumpSeq.append`,
  `CslibFrontier.SimpleGraph.tokenJumpReachable_iff_exists_isTokenJumpSeq`,
  `CslibFrontier.SimpleGraph.tokenJumpReachableWithin_iff_exists_isTokenJumpSeq`
- `CslibFrontier.SimpleGraph.tokenJumpReachableWithin_of_subset_isIndepSet`,
  `CslibFrontier.SimpleGraph.tokenJumpReachableWithin_of_card_two_of_no_fourCycle`
- `exists_isIndepSet_mul_card_ge_of_colorable`,
  `exists_isIndepSet_two_mul_card_ge_of_isAcyclic`,
  `exists_isIndepSet_two_mul_card_add_one_ge_of_isAcyclic_delete`,
  `exists_isAcyclic_delete_of_connected_ncard_le_two`,
  `exists_isIndepSet_two_mul_card_add_one_ge_of_connected_ncard_le_two`,
  `exists_isIndepSet_two_mul_card_add_one_ge_of_connected_of_degree_le_two`,
  `exists_isIndepSet_two_mul_card_add_one_ge_of_connected_of_maxDegree_le_two`

## Tags

combinatorial reconfiguration, token jumping, independent set, graph coloring
-/

public section

namespace CslibFrontier.SimpleGraph

open _root_.SimpleGraph

/-! ### Single Token Jump Adjacency -/

section TokenJumpAdj

variable {V W : Type*}

/-- Two finite vertex sets `I` and `J` are adjacent under a single *token jump* in `G` if both
are independent sets in `G` and `J` is obtained from `I` by removing one vertex `v ∈ I` and adding
one vertex `w ∉ I`. -/
def TokenJumpAdj (G : SimpleGraph V) (I J : Finset V) : Prop :=
  G.IsIndepSet (I : Set V) ∧ G.IsIndepSet (J : Set V) ∧
    ∃ v ∈ I, ∃ w ∉ I, ∀ x, x ∈ J ↔ x = w ∨ (x ∈ I ∧ x ≠ v)

/-- Logical characterization of `CslibFrontier.SimpleGraph.TokenJumpAdj`. -/
theorem tokenJumpAdj_iff {G : SimpleGraph V} {I J : Finset V} :
    TokenJumpAdj G I J ↔
      G.IsIndepSet (I : Set V) ∧ G.IsIndepSet (J : Set V) ∧
        ∃ v ∈ I, ∃ w ∉ I, ∀ x, x ∈ J ↔ x = w ∨ (x ∈ I ∧ x ≠ v) :=
  Iff.rfl

/-- Characterization of `TokenJumpAdj` via `Finset.insert` and `Finset.erase`. -/
theorem tokenJumpAdj_iff_insert_erase [DecidableEq V] {G : SimpleGraph V} {I J : Finset V} :
    TokenJumpAdj G I J ↔
      G.IsIndepSet (I : Set V) ∧ G.IsIndepSet (J : Set V) ∧
        ∃ v ∈ I, ∃ w ∉ I, J = insert w (I.erase v) := by
  simp only [tokenJumpAdj_iff, Finset.ext_iff, Finset.mem_insert, Finset.mem_erase, and_comm]

/-- The left endpoint of a token jump is an independent set. -/
theorem TokenJumpAdj.isIndepSet_left {G : SimpleGraph V} {I J : Finset V}
    (h : TokenJumpAdj G I J) : G.IsIndepSet (I : Set V) :=
  h.1

/-- The right endpoint of a token jump is an independent set. -/
theorem TokenJumpAdj.isIndepSet_right {G : SimpleGraph V} {I J : Finset V}
    (h : TokenJumpAdj G I J) : G.IsIndepSet (J : Set V) :=
  h.2.1

/-- Constructing a single token jump from `insert w (I.erase v)`. -/
theorem TokenJumpAdj.of_insert_erase [DecidableEq V] {G : SimpleGraph V} {I : Finset V}
    {v w : V} (hI : G.IsIndepSet (I : Set V))
    (hJ : G.IsIndepSet ((insert w (I.erase v) : Finset V) : Set V))
    (hv : v ∈ I) (hw : w ∉ I) : TokenJumpAdj G I (insert w (I.erase v)) :=
  tokenJumpAdj_iff_insert_erase.mpr ⟨hI, hJ, v, hv, w, hw, rfl⟩

/-- Single token jump adjacency is symmetric. -/
theorem TokenJumpAdj.symm {G : SimpleGraph V} {I J : Finset V} (h : TokenJumpAdj G I J) :
    TokenJumpAdj G J I := by
  obtain ⟨hI, hJ, v, hv, w, hw, hmem⟩ := h
  refine ⟨hJ, hI, w, (hmem w).mpr (Or.inl rfl), v, ?_, fun x ↦ ⟨fun hxI ↦ ?_, ?_⟩⟩
  · intro hvJ
    rcases (hmem v).mp hvJ with rfl | ⟨_, hne⟩
    exacts [hw hv, hne rfl]
  · by_cases hxv : x = v
    · exact Or.inl hxv
    · exact Or.inr ⟨(hmem x).mpr (Or.inr ⟨hxI, hxv⟩), fun hxw ↦ hw (hxw ▸ hxI)⟩
  · rintro (rfl | ⟨hxJ, hxw⟩)
    · exact hv
    · rcases (hmem x).mp hxJ with hEq | ⟨hxI, _⟩
      exacts [(hxw hEq).elim, hxI]

/-- No finite vertex set is adjacent to itself by a single token jump. -/
@[simp]
theorem tokenJumpAdj_irrefl (G : SimpleGraph V) (I : Finset V) : ¬ TokenJumpAdj G I I := by
  rintro ⟨_, _, _, _, w, hw, hmem⟩
  exact hw ((hmem w).mpr (Or.inl rfl))

/-- Dot-notation irreflexivity of `CslibFrontier.SimpleGraph.TokenJumpAdj`. -/
theorem TokenJumpAdj.irrefl {G : SimpleGraph V} {I : Finset V} (h : TokenJumpAdj G I I) : False :=
  tokenJumpAdj_irrefl G I h

/-- Adjacent independent sets under a single token jump are distinct. -/
theorem TokenJumpAdj.ne {G : SimpleGraph V} {I J : Finset V} (h : TokenJumpAdj G I J) : I ≠ J :=
  fun hEq ↦ (hEq ▸ h).irrefl

/-- A single token jump preserves cardinality. -/
theorem TokenJumpAdj.card_eq {G : SimpleGraph V} {I J : Finset V} (h : TokenJumpAdj G I J) :
    I.card = J.card := by
  classical
  obtain ⟨_, _, v, hv, w, hw, rfl⟩ := tokenJumpAdj_iff_insert_erase.mp h
  rw [Finset.card_insert_of_notMem (fun hmem ↦ hw (Finset.mem_of_mem_erase hmem)),
    Finset.card_erase_add_one hv]

/-- If `I` and `J` are adjacent under a single token jump, then `#(I \ J) = 1`. -/
theorem TokenJumpAdj.sdiff_card_eq_one [DecidableEq V] {G : SimpleGraph V} {I J : Finset V}
    (h : TokenJumpAdj G I J) : (I \ J).card = 1 := by
  obtain ⟨_, _, v, hv, w, hw, rfl⟩ := tokenJumpAdj_iff_insert_erase.mp h
  have hsdiff : I \ insert w (I.erase v) = {v} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    refine ⟨fun ⟨hxI, hnot⟩ ↦ by_contra fun hxv ↦ hnot (Or.inr ⟨hxv, hxI⟩), ?_⟩
    rintro rfl
    exact ⟨hv, by rintro (rfl | ⟨hne, _⟩); exacts [hw hv, hne rfl]⟩
  rw [hsdiff, Finset.card_singleton]

/-- Two equicardinal independent sets are adjacent under a single token jump if and only if
`#(I \ J) = 1`. -/
theorem tokenJumpAdj_iff_sdiff_card_eq_one [DecidableEq V] {G : SimpleGraph V} {I J : Finset V} :
    TokenJumpAdj G I J ↔
      G.IsIndepSet (I : Set V) ∧ G.IsIndepSet (J : Set V) ∧ I.card = J.card ∧ (I \ J).card = 1 := by
  refine ⟨fun h ↦ ⟨h.isIndepSet_left, h.isIndepSet_right, h.card_eq, h.sdiff_card_eq_one⟩, ?_⟩
  rintro ⟨hI, hJ, hcard, hsdiff⟩
  have hcardI := Finset.card_sdiff_add_card_inter I J
  have hcardJ := Finset.card_sdiff_add_card_inter J I
  rw [Finset.inter_comm] at hcardJ
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hsdiff
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (show (J \ I).card = 1 by omega)
  have hv_mem : v ∈ I \ J := hv ▸ Finset.mem_singleton_self v
  have hw_mem : w ∈ J \ I := hw ▸ Finset.mem_singleton_self w
  refine tokenJumpAdj_iff_insert_erase.mpr
    ⟨hI, hJ, v, (Finset.mem_sdiff.mp hv_mem).1, w, (Finset.mem_sdiff.mp hw_mem).2, ?_⟩
  ext x
  simp only [Finset.mem_insert, Finset.mem_erase]
  refine ⟨fun hxJ ↦ ?_, ?_⟩
  · by_cases hxI : x ∈ I
    · exact Or.inr ⟨fun hxv ↦ (Finset.mem_sdiff.mp hv_mem).2 (hxv ▸ hxJ), hxI⟩
    · exact Or.inl (Finset.mem_singleton.mp (hw ▸ Finset.mem_sdiff.mpr ⟨hxJ, hxI⟩))
  · rintro (rfl | ⟨hxv, hxI⟩)
    · exact (Finset.mem_sdiff.mp hw_mem).1
    · exact by_contra fun hxJ ↦
        hxv (Finset.mem_singleton.mp (hv ▸ Finset.mem_sdiff.mpr ⟨hxI, hxJ⟩))

private theorem isIndepSet_map_iso_iff {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (I : Finset V) :
    H.IsIndepSet ((I.map e.toEquiv.toEmbedding : Finset W) : Set W) ↔ G.IsIndepSet (I : Set V) := by
  refine ⟨fun h x hx y hy hne hadj ↦ h (Finset.mem_map_of_mem _ hx) (Finset.mem_map_of_mem _ hy)
      (fun hEq ↦ hne (e.injective hEq)) (e.map_adj_iff.mpr hadj), ?_⟩
  intro h x hx y hy hne hadj
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
  exact h hu hv (fun hEq ↦ hne (congrArg e hEq)) (e.map_adj_iff.mp hadj)

private theorem map_symm_map_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (I : Finset V) :
    (I.map e.toEquiv.toEmbedding).map e.symm.toEquiv.toEmbedding = I := by
  ext x
  simp only [Finset.mem_map, RelIso.coe_fn_toEquiv, Equiv.toEmbedding_apply]
  exact ⟨fun ⟨_, ⟨b, hb, hab⟩, hax⟩ ↦ by simpa [← hax, ← hab] using hb,
    fun hx ↦ ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩⟩

/-- Graph isomorphisms preserve and reflect single token jump adjacency. -/
theorem Iso.tokenJumpAdj_iff {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {I J : Finset V} :
    TokenJumpAdj H (I.map e.toEquiv.toEmbedding) (J.map e.toEquiv.toEmbedding) ↔
      TokenJumpAdj G I J := by
  simp only [CslibFrontier.SimpleGraph.tokenJumpAdj_iff, isIndepSet_map_iso_iff]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨v', hv', w', hw', hmem⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hv'
    refine ⟨v, hv, e.symm w', fun hmem' ↦ hw' ?_, fun x ↦ ?_⟩
    · simpa using Finset.mem_map_of_mem e.toEquiv.toEmbedding hmem'
    · have hx := hmem (e x)
      simp only [Finset.mem_map, RelIso.coe_fn_toEquiv, Equiv.toEmbedding_apply,
        e.injective.eq_iff, exists_eq_right] at hx
      simpa [e.eq_symm_apply] using hx
  · rintro ⟨v, hv, w, hw, hmem⟩
    refine ⟨e v, Finset.mem_map_of_mem _ hv, e w, ?_, fun y ↦ ?_⟩
    · intro hmem'
      obtain ⟨x, hx, hEq⟩ := Finset.mem_map.mp hmem'
      exact hw (e.injective hEq ▸ hx)
    · simp only [Finset.mem_map, RelIso.coe_fn_toEquiv, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨x, hxJ, rfl⟩
        rcases (hmem x).mp hxJ with rfl | ⟨hxI, hxv⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨⟨x, hxI, rfl⟩, fun hEq ↦ hxv (e.injective hEq)⟩
      · rintro (rfl | ⟨⟨x, hxI, rfl⟩, hxv⟩)
        · exact ⟨w, (hmem w).mpr (Or.inl rfl), rfl⟩
        · exact ⟨x, (hmem x).mpr (Or.inr ⟨hxI, fun hEq ↦ hxv (congrArg e hEq)⟩), rfl⟩

private theorem isIndepSet_map_subtype_iff {G : SimpleGraph V} {S : Set V} (I : Finset S) :
    (G.induce S).IsIndepSet (I : Set S) ↔
      G.IsIndepSet ((I.map (Function.Embedding.subtype (· ∈ S)) : Finset V) : Set V) := by
  refine ⟨fun h x hx y hy hne hadj ↦ ?_, fun h u hu v hv hne hadj ↦
    h (Finset.mem_map_of_mem _ hu) (Finset.mem_map_of_mem _ hv)
      (fun hEq ↦ hne (Subtype.ext hEq)) hadj⟩
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
  exact h hu hv (fun hEq ↦ hne (congrArg Subtype.val hEq)) hadj

/-- Single token jump adjacency in an induced subgraph `G.induce S` coincides with single token jump
adjacency of the embedded vertex sets in `G`. -/
theorem tokenJumpAdj_induce_iff {G : SimpleGraph V} {S : Set V} {I J : Finset S} :
    TokenJumpAdj (G.induce S) I J ↔
      TokenJumpAdj G (I.map (Function.Embedding.subtype (· ∈ S)))
        (J.map (Function.Embedding.subtype (· ∈ S))) := by
  simp only [tokenJumpAdj_iff, isIndepSet_map_subtype_iff]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨v, hv, w, hw, hmem⟩
    refine ⟨v.1, Finset.mem_map_of_mem _ hv, w.1, by simpa using hw, fun x ↦ ⟨?_, ?_⟩⟩
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      rcases (hmem u).mp hu with rfl | ⟨huI, huv⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨Finset.mem_map_of_mem _ huI, fun hEq ↦ huv (Subtype.ext hEq)⟩
    · rintro (rfl | ⟨hxI, hxv⟩)
      · exact Finset.mem_map_of_mem _ ((hmem w).mpr (Or.inl rfl))
      · obtain ⟨u, huI, rfl⟩ := Finset.mem_map.mp hxI
        exact Finset.mem_map_of_mem _
          ((hmem u).mpr (Or.inr ⟨huI, fun hEq ↦ hxv (congrArg Subtype.val hEq)⟩))
  · rintro ⟨v, hv, w, hw, hmem⟩
    obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨w', _, rfl⟩ := Finset.mem_map.mp ((hmem w).mpr (Or.inl rfl))
    refine ⟨v', hv', w', fun hw'I ↦ hw (Finset.mem_map_of_mem _ hw'I), fun x ↦ ?_⟩
    simpa [Subtype.ext_iff] using hmem x.1

end TokenJumpAdj

/-! ### Token Jumping Reconfiguration Graph -/

section TokenJumpGraph

variable {V W : Type*}

/-- The *token jumping reconfiguration graph* of `G` on independent sets of cardinality `k`. -/
def tokenJumpGraph (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph {I : Finset V // G.IsIndepSet (I : Set V) ∧ I.card = k} where
  Adj I J := TokenJumpAdj G I.1 J.1
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun _ h ↦ h.irrefl⟩

/-- Adjacency characterization in `CslibFrontier.SimpleGraph.tokenJumpGraph`. -/
@[simp, grind =]
theorem tokenJumpGraph_adj {G : SimpleGraph V} {k : ℕ}
    {I J : {K : Finset V // G.IsIndepSet (K : Set V) ∧ K.card = k}} :
    (tokenJumpGraph G k).Adj I J ↔ TokenJumpAdj G I.1 J.1 :=
  Iff.rfl

/-- A graph isomorphism `e : G ≃g H` induces an isomorphism of token jumping reconfiguration
graphs `tokenJumpGraph G k ≃g tokenJumpGraph H k`. -/
def Iso.tokenJumpGraphIso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (k : ℕ) :
    tokenJumpGraph G k ≃g tokenJumpGraph H k where
  toFun I :=
    ⟨I.1.map e.toEquiv.toEmbedding, (isIndepSet_map_iso_iff e I.1).mpr I.2.1, by simp [I.2.2]⟩
  invFun J :=
    ⟨J.1.map e.symm.toEquiv.toEmbedding, (isIndepSet_map_iso_iff e.symm J.1).mpr J.2.1,
      by simp [J.2.2]⟩
  left_inv I := Subtype.ext (map_symm_map_iso e I.1)
  right_inv J := Subtype.ext (map_symm_map_iso e.symm J.1)
  map_rel_iff' := Iso.tokenJumpAdj_iff e

/-- Underlying vertex set of the forward image under `Iso.tokenJumpGraphIso`. -/
@[simp, grind =]
theorem Iso.tokenJumpGraphIso_apply_val {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (k : ℕ) (I : {K : Finset V // G.IsIndepSet (K : Set V) ∧ K.card = k}) :
    (Iso.tokenJumpGraphIso e k I).1 = I.1.map e.toEquiv.toEmbedding := by
  rw [Iso.tokenJumpGraphIso]; rfl

/-- Underlying vertex set of the inverse image under `Iso.tokenJumpGraphIso`. -/
@[simp, grind =]
theorem Iso.tokenJumpGraphIso_symm_apply_val {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (k : ℕ) (J : {K : Finset W // H.IsIndepSet (K : Set W) ∧ K.card = k}) :
    ((Iso.tokenJumpGraphIso e k).symm J).1 = J.1.map e.symm.toEquiv.toEmbedding := by
  rw [Iso.tokenJumpGraphIso]; rfl

/-- `Iso.tokenJumpGraphIso` preserves the identity graph isomorphism. -/
@[simp]
theorem Iso.tokenJumpGraphIso_refl (G : SimpleGraph V) (k : ℕ) :
    Iso.tokenJumpGraphIso (Iso.refl : G ≃g G) k = Iso.refl := by
  refine RelIso.ext fun I ↦ Subtype.ext ?_
  ext x
  simp only [Iso.tokenJumpGraphIso_apply_val, Finset.mem_map, RelIso.coe_fn_toEquiv,
    Equiv.toEmbedding_apply, RelIso.refl_apply, exists_eq_right]

/-- `Iso.tokenJumpGraphIso` preserves composition of graph isomorphisms. -/
@[simp]
theorem Iso.tokenJumpGraphIso_trans {U : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {K : SimpleGraph U} (e₁ : G ≃g H) (e₂ : H ≃g K) (k : ℕ) :
    Iso.tokenJumpGraphIso (e₁.trans e₂) k =
      (Iso.tokenJumpGraphIso e₁ k).trans (Iso.tokenJumpGraphIso e₂ k) := by
  refine RelIso.ext fun I ↦ Subtype.ext ?_
  ext x
  simp only [Iso.tokenJumpGraphIso_apply_val, RelIso.trans_apply, Finset.mem_map,
    RelIso.coe_fn_toEquiv, Equiv.toEmbedding_apply]
  exact ⟨fun ⟨a, ha, hEq⟩ ↦ ⟨e₁ a, ⟨a, ha, rfl⟩, hEq⟩,
    fun ⟨_, ⟨a, ha, rfl⟩, hEq⟩ ↦ ⟨a, ha, hEq⟩⟩

end TokenJumpGraph

/-! ### Reachability, Restricted Reachability, and Token Jump Sequences -/

section Reachability

variable {V W : Type*}

/-- Reachability between finite vertex sets by a finite sequence of token jumps in `G`. -/
def TokenJumpReachable (G : SimpleGraph V) (I J : Finset V) : Prop :=
  Relation.ReflTransGen (TokenJumpAdj G) I J

/-- Logical characterization of `CslibFrontier.SimpleGraph.TokenJumpReachable`. -/
theorem tokenJumpReachable_iff {G : SimpleGraph V} {I J : Finset V} :
    TokenJumpReachable G I J ↔ Relation.ReflTransGen (TokenJumpAdj G) I J :=
  Iff.rfl

/-- Every finite vertex set is token-jump reachable from itself. -/
@[simp]
theorem TokenJumpReachable.refl {G : SimpleGraph V} {I : Finset V} : TokenJumpReachable G I I :=
  Relation.ReflTransGen.refl

/-- A single token jump witnesses token-jump reachability. -/
theorem TokenJumpReachable.single {G : SimpleGraph V} {I J : Finset V}
    (h : TokenJumpAdj G I J) : TokenJumpReachable G I J :=
  Relation.ReflTransGen.single h

/-- Token-jump reachability is transitive. -/
theorem TokenJumpReachable.trans {G : SimpleGraph V} {I J K : Finset V}
    (h₁ : TokenJumpReachable G I J) (h₂ : TokenJumpReachable G J K) :
    TokenJumpReachable G I K :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Token-jump reachability is symmetric. -/
theorem TokenJumpReachable.symm {G : SimpleGraph V} {I J : Finset V}
    (h : TokenJumpReachable G I J) : TokenJumpReachable G J I := by
  induction h with
  | refl => exact .refl
  | tail _ hadj ih => exact (TokenJumpReachable.single hadj.symm).trans ih

/-- Token-jump reachable sets have equal cardinality. -/
theorem TokenJumpReachable.card_eq {G : SimpleGraph V} {I J : Finset V}
    (h : TokenJumpReachable G I J) : I.card = J.card := by
  induction h with
  | refl => rfl
  | tail _ hadj ih => exact ih.trans hadj.card_eq

/-- Independence propagates forward along token-jump reachability. -/
theorem TokenJumpReachable.isIndepSet_right {G : SimpleGraph V} {I J : Finset V}
    (h : TokenJumpReachable G I J) (hI : G.IsIndepSet (I : Set V)) : G.IsIndepSet (J : Set V) := by
  induction h with
  | refl => exact hI
  | tail _ hadj _ => exact hadj.isIndepSet_right

/-- Independence propagates backward along token-jump reachability. -/
theorem TokenJumpReachable.isIndepSet_left {G : SimpleGraph V} {I J : Finset V}
    (h : TokenJumpReachable G I J) (hJ : G.IsIndepSet (J : Set V)) : G.IsIndepSet (I : Set V) :=
  h.symm.isIndepSet_right hJ

private theorem tokenJumpReachable_map_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {A B : Finset V} (hAB : TokenJumpReachable G A B) :
    TokenJumpReachable H (A.map e.toEquiv.toEmbedding) (B.map e.toEquiv.toEmbedding) := by
  induction hAB with
  | refl => exact .refl
  | tail _ hadj ih => exact ih.trans (.single ((Iso.tokenJumpAdj_iff e).mpr hadj))

/-- Graph isomorphisms preserve and reflect token-jump reachability. -/
theorem Iso.tokenJumpReachable_iff {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {I J : Finset V} :
    TokenJumpReachable H (I.map e.toEquiv.toEmbedding) (J.map e.toEquiv.toEmbedding) ↔
      TokenJumpReachable G I J :=
  ⟨fun h ↦ by simpa [map_symm_map_iso] using tokenJumpReachable_map_iso e.symm h,
    tokenJumpReachable_map_iso e⟩

/-- On `k`-element independent sets, `TokenJumpReachable G I.1 J.1` is equivalent to graph
reachability in `tokenJumpGraph G k`. -/
theorem tokenJumpReachable_iff_reachable_tokenJumpGraph {G : SimpleGraph V} {k : ℕ}
    {I J : {K : Finset V // G.IsIndepSet (K : Set V) ∧ K.card = k}} :
    TokenJumpReachable G I.1 J.1 ↔ (tokenJumpGraph G k).Reachable I J := by
  constructor
  · intro h
    rcases I with ⟨I, hIind, hIcard⟩
    rcases J with ⟨J, hJind, hJcard⟩
    dsimp only at h
    induction h with
    | refl => exact Reachable.refl _
    | @tail B C _ hadj ih =>
      exact (ih hadj.isIndepSet_left (hadj.card_eq.trans hJcard)).trans (Adj.reachable hadj)
  · rintro ⟨w⟩
    induction w with
    | nil => exact .refl
    | cons hadj _ ih => exact (TokenJumpReachable.single hadj).trans ih

/-- Reachability between finite vertex sets by token jumps whose intermediate configurations all
lie inside a prescribed vertex subset `S`. -/
def TokenJumpReachableWithin (G : SimpleGraph V) (S : Set V) (I J : Finset V) : Prop :=
  Relation.ReflTransGen
    (fun A B ↦ TokenJumpAdj G A B ∧ (A : Set V) ⊆ S ∧ (B : Set V) ⊆ S) I J

/-- Logical characterization of `CslibFrontier.SimpleGraph.TokenJumpReachableWithin`. -/
theorem tokenJumpReachableWithin_iff {G : SimpleGraph V} {S : Set V} {I J : Finset V} :
    TokenJumpReachableWithin G S I J ↔
      Relation.ReflTransGen
        (fun A B ↦ TokenJumpAdj G A B ∧ (A : Set V) ⊆ S ∧ (B : Set V) ⊆ S) I J :=
  Iff.rfl

/-- Reflexivity of subset-restricted token-jump reachability. -/
@[simp]
theorem TokenJumpReachableWithin.refl {G : SimpleGraph V} {S : Set V} {I : Finset V} :
    TokenJumpReachableWithin G S I I :=
  Relation.ReflTransGen.refl

/-- A single token jump inside `S` witnesses restricted token-jump reachability within `S`. -/
theorem TokenJumpReachableWithin.single {G : SimpleGraph V} {S : Set V} {I J : Finset V}
    (h : TokenJumpAdj G I J) (hI : (I : Set V) ⊆ S) (hJ : (J : Set V) ⊆ S) :
    TokenJumpReachableWithin G S I J :=
  Relation.ReflTransGen.single ⟨h, hI, hJ⟩

/-- Transitivity of subset-restricted token-jump reachability. -/
theorem TokenJumpReachableWithin.trans {G : SimpleGraph V} {S : Set V} {I J K : Finset V}
    (h₁ : TokenJumpReachableWithin G S I J) (h₂ : TokenJumpReachableWithin G S J K) :
    TokenJumpReachableWithin G S I K :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Symmetry of subset-restricted token-jump reachability. -/
theorem TokenJumpReachableWithin.symm {G : SimpleGraph V} {S : Set V} {I J : Finset V}
    (h : TokenJumpReachableWithin G S I J) : TokenJumpReachableWithin G S J I := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    exact (TokenJumpReachableWithin.single hstep.1.symm hstep.2.2 hstep.2.1).trans ih

/-- Monotonicity of restricted token-jump reachability under enlarging the allowed vertex set. -/
theorem TokenJumpReachableWithin.mono_set {G : SimpleGraph V} {S T : Set V} {I J : Finset V}
    (hST : S ⊆ T) (h : TokenJumpReachableWithin G S I J) : TokenJumpReachableWithin G T I J := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    exact ih.trans (.single hstep.1 (hstep.2.1.trans hST) (hstep.2.2.trans hST))

/-- Restricted token-jump reachability implies unrestricted token-jump reachability. -/
theorem TokenJumpReachableWithin.tokenJumpReachable {G : SimpleGraph V} {S : Set V}
    {I J : Finset V} (h : TokenJumpReachableWithin G S I J) : TokenJumpReachable G I J := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.trans (.single hstep.1)

/-- Restricted token-jump reachability preserves cardinality. -/
theorem TokenJumpReachableWithin.card_eq {G : SimpleGraph V} {S : Set V} {I J : Finset V}
    (h : TokenJumpReachableWithin G S I J) : I.card = J.card :=
  h.tokenJumpReachable.card_eq

/-- Restricting token jumps to `Set.univ` coincides with unrestricted token-jump reachability. -/
@[simp, grind =]
theorem tokenJumpReachableWithin_univ {G : SimpleGraph V} {I J : Finset V} :
    TokenJumpReachableWithin G Set.univ I J ↔ TokenJumpReachable G I J := by
  refine ⟨TokenJumpReachableWithin.tokenJumpReachable, fun h ↦ ?_⟩
  induction h with
  | refl => exact .refl
  | tail _ hadj ih => exact ih.trans (.single hadj (Set.subset_univ _) (Set.subset_univ _))

private theorem coe_map_subtype_subset {S : Set V} (I : Finset S) :
    ((I.map (Function.Embedding.subtype (· ∈ S)) : Finset V) : Set V) ⊆ S := by
  intro x hx
  obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hx
  exact u.2

private theorem map_preimage_subtype {S : Set V} {I : Finset V} (hI : (I : Set V) ⊆ S) :
    (I.preimage Subtype.val Subtype.val_injective.injOn).map
      (Function.Embedding.subtype (· ∈ S)) = I := by
  ext x
  simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coe_subtype]
  exact ⟨fun ⟨u, hu, hEq⟩ ↦ hEq ▸ hu, fun hx ↦ ⟨⟨x, hI hx⟩, hx, rfl⟩⟩

private theorem preimage_map_subtype {S : Set V} (I : Finset S) :
    (I.map (Function.Embedding.subtype (· ∈ S))).preimage Subtype.val
      Subtype.val_injective.injOn = I := by
  ext u
  simp

/-- Token-jump reachability in an induced subgraph `G.induce S` is equivalent to restricted
token-jump reachability within `S` of the embedded finite vertex sets. -/
theorem tokenJumpReachable_induce_iff {G : SimpleGraph V} {S : Set V} {I J : Finset S} :
    TokenJumpReachable (G.induce S) I J ↔
      TokenJumpReachableWithin G S (I.map (Function.Embedding.subtype (· ∈ S)))
        (J.map (Function.Embedding.subtype (· ∈ S))) := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hadj ih =>
      exact ih.trans (.single (tokenJumpAdj_induce_iff.mp hadj)
        (coe_map_subtype_subset _) (coe_map_subtype_subset _))
  · intro h
    have hpre : ∀ {A B : Finset V}, TokenJumpReachableWithin G S A B →
        TokenJumpReachable (G.induce S)
          (A.preimage Subtype.val Subtype.val_injective.injOn)
          (B.preimage Subtype.val Subtype.val_injective.injOn) := by
      intro A B hAB
      induction hAB with
      | refl => exact .refl
      | @tail C D _ hstep ih =>
        have hadj : TokenJumpAdj (G.induce S)
            (C.preimage Subtype.val Subtype.val_injective.injOn)
            (D.preimage Subtype.val Subtype.val_injective.injOn) := by
          rw [tokenJumpAdj_induce_iff, map_preimage_subtype hstep.2.1,
            map_preimage_subtype hstep.2.2]
          exact hstep.1
        exact ih.trans (.single hadj)
    simpa [preimage_map_subtype] using hpre h

/-- For finite vertex subsets `I, J ⊆ S`, restricted token-jump reachability within `S` is
equivalent to token-jump reachability of their `Subtype.val` preimages in `G.induce S`. -/
theorem tokenJumpReachableWithin_iff_induce {G : SimpleGraph V} {S : Set V} {I J : Finset V}
    (hI : (I : Set V) ⊆ S) (hJ : (J : Set V) ⊆ S) :
    TokenJumpReachableWithin G S I J ↔
      TokenJumpReachable (G.induce S)
        (I.preimage Subtype.val Subtype.val_injective.injOn)
        (J.preimage Subtype.val Subtype.val_injective.injOn) := by
  rw [tokenJumpReachable_induce_iff, map_preimage_subtype hI, map_preimage_subtype hJ]

/-- A list of finite vertex sets is a *token jump sequence* in `G` if consecutive entries are
adjacent under `CslibFrontier.SimpleGraph.TokenJumpAdj`. -/
def IsTokenJumpSeq (G : SimpleGraph V) (L : List (Finset V)) : Prop :=
  L.IsChain (TokenJumpAdj G)

/-- Logical characterization of `CslibFrontier.SimpleGraph.IsTokenJumpSeq`. -/
theorem isTokenJumpSeq_iff {G : SimpleGraph V} {L : List (Finset V)} :
    IsTokenJumpSeq G L ↔ L.IsChain (TokenJumpAdj G) :=
  Iff.rfl

/-- The empty list is a token jump sequence. -/
@[simp]
theorem isTokenJumpSeq_nil (G : SimpleGraph V) : IsTokenJumpSeq G [] :=
  List.IsChain.nil

/-- Every singleton list is a token jump sequence. -/
@[simp]
theorem isTokenJumpSeq_singleton (G : SimpleGraph V) (I : Finset V) : IsTokenJumpSeq G [I] :=
  List.IsChain.singleton I

/-- Cons-cons characterization of `CslibFrontier.SimpleGraph.IsTokenJumpSeq`. -/
@[simp, grind =]
theorem isTokenJumpSeq_cons_cons {G : SimpleGraph V} {I J : Finset V} {L : List (Finset V)} :
    IsTokenJumpSeq G (I :: J :: L) ↔ TokenJumpAdj G I J ∧ IsTokenJumpSeq G (J :: L) :=
  List.isChain_cons_cons

/-- Reversing a token jump sequence yields a token jump sequence. -/
theorem IsTokenJumpSeq.reverse {G : SimpleGraph V} {L : List (Finset V)}
    (h : IsTokenJumpSeq G L) : IsTokenJumpSeq G L.reverse :=
  (List.isChain_reverse.mpr h).imp (fun _ _ hadj ↦ hadj.symm)

/-- Concatenating two token jump sequences whose boundary entries are token-jump adjacent yields a
token jump sequence. -/
theorem IsTokenJumpSeq.append {G : SimpleGraph V} {L₁ L₂ : List (Finset V)}
    (h₁ : IsTokenJumpSeq G L₁) (h₂ : IsTokenJumpSeq G L₂)
    (hlink : ∀ A ∈ L₁.getLast?, ∀ B ∈ L₂.head?, TokenJumpAdj G A B) :
    IsTokenJumpSeq G (L₁ ++ L₂) :=
  List.isChain_append.mpr ⟨h₁, h₂, hlink⟩

/-- Gluing two token jump sequences sharing a common pivot entry `I` yields a token jump
sequence. -/
theorem IsTokenJumpSeq.append_cons {G : SimpleGraph V} {L₁ L₂ : List (Finset V)} {I : Finset V}
    (h₁ : IsTokenJumpSeq G (L₁ ++ [I])) (h₂ : IsTokenJumpSeq G (I :: L₂)) :
    IsTokenJumpSeq G (L₁ ++ I :: L₂) :=
  List.isChain_split.mpr ⟨h₁, h₂⟩

/-- `TokenJumpReachable G I J` holds if and only if there is a token jump sequence starting at `I`
and ending at `J`. -/
theorem tokenJumpReachable_iff_exists_isTokenJumpSeq {G : SimpleGraph V} {I J : Finset V} :
    TokenJumpReachable G I J ↔
      ∃ L : List (Finset V), IsTokenJumpSeq G L ∧ L.head? = some I ∧ L.getLast? = some J := by
  constructor
  · intro h
    obtain ⟨L, hne, hchain, hhead, hlast⟩ := List.exists_isChain_ne_nil_of_relationReflTransGen h
    exact ⟨L, hchain, by rw [List.head?_eq_some_head hne, hhead],
      by rw [List.getLast?_eq_some_getLast hne, hlast]⟩
  · rintro ⟨L, hseq, hhead, hlast⟩
    have hne : L ≠ [] := fun hnil ↦ by simp [hnil] at hhead
    rw [List.head?_eq_some_head hne, Option.some.injEq] at hhead
    rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hlast
    exact tokenJumpReachable_iff.mpr
      (by simpa [hhead, hlast] using List.relationReflTransGen_of_exists_isChain L hseq hne)

/-- Assuming `(I : Set V) ⊆ S`, `TokenJumpReachableWithin G S I J` holds if and only if there is a
token jump sequence from `I` to `J` whose entries are all subsets of `S`. -/
theorem tokenJumpReachableWithin_iff_exists_isTokenJumpSeq {G : SimpleGraph V} {S : Set V}
    {I J : Finset V} (hI : (I : Set V) ⊆ S) :
    TokenJumpReachableWithin G S I J ↔
      ∃ L : List (Finset V),
        IsTokenJumpSeq G L ∧ L.head? = some I ∧ L.getLast? = some J ∧
          ∀ A ∈ L, (A : Set V) ⊆ S := by
  constructor
  · intro h
    obtain ⟨L, hne, hchain, hhead, hlast⟩ := List.exists_isChain_ne_nil_of_relationReflTransGen h
    refine ⟨L, hchain.imp (fun _ _ hstep ↦ hstep.1),
      by rw [List.head?_eq_some_head hne, hhead],
      by rw [List.getLast?_eq_some_getLast hne, hlast], ?_⟩
    exact List.IsChain.induction (fun A : Finset V ↦ (A : Set V) ⊆ S) L hchain
      (fun _ _ hstep _ ↦ hstep.2.2) (fun _ ↦ by rwa [hhead])
  · rintro ⟨L, hseq, hhead, hlast, hsub⟩
    have hne : L ≠ [] := fun hnil ↦ by simp [hnil] at hhead
    have hchain :
        L.IsChain (fun A B ↦ TokenJumpAdj G A B ∧ (A : Set V) ⊆ S ∧ (B : Set V) ⊆ S) :=
      hseq.imp_of_mem_imp (fun A B hA hB hadj ↦ ⟨hadj, hsub A hA, hsub B hB⟩)
    rw [List.head?_eq_some_head hne, Option.some.injEq] at hhead
    rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hlast
    exact tokenJumpReachableWithin_iff.mpr
      (by simpa [hhead, hlast] using List.relationReflTransGen_of_exists_isChain L hchain hne)

end Reachability

/-! ### Structural Reconfiguration and Independent Set Bounds -/

section ReconfigurationTheorems

variable {V : Type*}

/-- Any two equicardinal finite subsets of an independent set `K` are token-jump reachable within
`K`. -/
theorem tokenJumpReachableWithin_of_subset_isIndepSet {G : SimpleGraph V} {K : Set V}
    {I J : Finset V} (hK : G.IsIndepSet K) (hI : (I : Set V) ⊆ K) (hJ : (J : Set V) ⊆ K)
    (hcard : I.card = J.card) : TokenJumpReachableWithin G K I J := by
  classical
  suffices ∀ n : ℕ, ∀ A : Finset V, (A : Set V) ⊆ K → A.card = J.card → (A \ J).card = n →
      TokenJumpReachableWithin G K A J from this (I \ J).card I hI hcard rfl
  intro n
  induction n with
  | zero =>
    intro A _ hAcard hsdiff
    have hsub : A ⊆ J := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hsdiff)
    rw [Finset.eq_of_subset_of_card_le hsub hAcard.ge]
    exact .refl
  | succ m ih =>
    intro A hAK hAcard hsdiff
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (A \ J).card by omega)
    have hcardA := Finset.card_sdiff_add_card_inter A J
    have hcardJ := Finset.card_sdiff_add_card_inter J A
    rw [Finset.inter_comm] at hcardJ
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (J \ A).card by omega)
    have hwJ : w ∈ J := (Finset.mem_sdiff.mp hw).1
    let A' : Finset V := insert w (A.erase v)
    have hA'K : (A' : Set V) ⊆ K := fun x hx ↦ by
      rcases Finset.mem_insert.mp hx with rfl | hx'
      exacts [hJ hwJ, hAK (Finset.mem_of_mem_erase hx')]
    have hadj : TokenJumpAdj G A A' :=
      TokenJumpAdj.of_insert_erase (hK.mono hAK) (hK.mono hA'K)
        (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hw).2
    have hsdiff_eq : A' \ J = (A \ J).erase v := by
      ext x
      simp only [A', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      refine ⟨?_, fun ⟨hxv, hxA, hxJ⟩ ↦ ⟨Or.inr ⟨hxv, hxA⟩, hxJ⟩⟩
      rintro ⟨rfl | ⟨hxv, hxA⟩, hxJ⟩
      exacts [(hxJ hwJ).elim, ⟨hxv, hxA, hxJ⟩]
    have hsdiff' : (A' \ J).card = m := by
      rw [hsdiff_eq, Finset.card_erase_of_mem hv, hsdiff, Nat.add_sub_cancel]
    exact (TokenJumpReachableWithin.single hadj hAK hA'K).trans
      (ih A' hA'K (hadj.card_eq.symm.trans hAcard) hsdiff')

private theorem tokenJumpReachableWithin_pair_left [DecidableEq V] {G : SimpleGraph V} {S : Set V}
    {u v w : V} (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) (huv : u ≠ v) (huw : u ≠ w)
    (h1 : G.IsIndepSet (({u, v} : Finset V) : Set V))
    (h2 : G.IsIndepSet (({u, w} : Finset V) : Set V)) :
    TokenJumpReachableWithin G S {u, v} {u, w} := by
  by_cases hvw : v = w
  · subst hvw; exact .refl
  · have hsub1 : (({u, v} : Finset V) : Set V) ⊆ S := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
      exacts [hu, (Finset.mem_singleton.mp hx') ▸ hv]
    have hsub2 : (({u, w} : Finset V) : Set V) ⊆ S := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
      exacts [hu, (Finset.mem_singleton.mp hx') ▸ hw]
    have hEq : ({u, w} : Finset V) = insert w (({u, v} : Finset V).erase v) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
      constructor
      · rintro (rfl | rfl); exacts [Or.inr ⟨huv, Or.inl rfl⟩, Or.inl rfl]
      · rintro (rfl | ⟨hxv, rfl | rfl⟩); exacts [Or.inr rfl, Or.inl rfl, (hxv rfl).elim]
    have hw_not : w ∉ ({u, v} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨huw.symm, fun h ↦ hvw h.symm⟩
    have hadj : TokenJumpAdj G {u, v} {u, w} := by
      rw [hEq]
      exact TokenJumpAdj.of_insert_erase h1 (hEq ▸ h2)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)) hw_not
    exact TokenJumpReachableWithin.single hadj hsub1 hsub2

private theorem tokenJumpReachableWithin_pair_of_not_adj [DecidableEq V] {G : SimpleGraph V}
    {S : Set V} {a c b d : V} (ha : a ∈ S) (hc : c ∈ S) (hb : b ∈ S) (hd : d ∈ S)
    (hac : a ≠ c) (hbd : b ≠ d) (hI : G.IsIndepSet (({a, c} : Finset V) : Set V))
    (hJ : G.IsIndepSet (({b, d} : Finset V) : Set V)) (hnot : ¬ G.Adj a b) :
    TokenJumpReachableWithin G S {a, c} {b, d} := by
  by_cases hab : a = b
  · subst hab
    exact tokenJumpReachableWithin_pair_left ha hc hd hac hbd hI hJ
  · have hK : G.IsIndepSet (({a, b} : Finset V) : Set V) := by
      intro x hx y hy hxy hadj
      rcases Finset.mem_insert.mp hx with rfl | hx' <;>
        rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hxy rfl
      · rw [Finset.mem_singleton.mp hy'] at hadj; exact hnot hadj
      · rw [Finset.mem_singleton.mp hx'] at hadj; exact hnot hadj.symm
      · rw [Finset.mem_singleton.mp hx', Finset.mem_singleton.mp hy'] at hxy; exact hxy rfl
    have h1 := tokenJumpReachableWithin_pair_left ha hc hb hac hab hI hK
    have h2 := tokenJumpReachableWithin_pair_left hb ha hd (Ne.symm hab) hbd
      (by simpa [Finset.pair_comm] using hK) hJ
    exact h1.trans (by simpa [Finset.pair_comm] using h2)

/-- Any two `2`-element independent sets contained in a vertex set `S` whose induced subgraph
contains no `4`-cycle are token-jump reachable within `S` (in at most two token jumps). -/
theorem tokenJumpReachableWithin_of_card_two_of_no_fourCycle {G : SimpleGraph V} {S : Set V}
    {I J : Finset V} (hIsub : (I : Set V) ⊆ S) (hJsub : (J : Set V) ⊆ S)
    (hIcard : I.card = 2) (hJcard : J.card = 2)
    (hI : G.IsIndepSet (I : Set V)) (hJ : G.IsIndepSet (J : Set V))
    (hC4 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False) :
    TokenJumpReachableWithin G S I J := by
  classical
  obtain ⟨a, c, hac, rfl⟩ := Finset.card_eq_two.mp hIcard
  obtain ⟨b, d, hbd, rfl⟩ := Finset.card_eq_two.mp hJcard
  have ha : a ∈ S := hIsub (Finset.mem_insert_self a {c})
  have hc : c ∈ S := hIsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
  have hb : b ∈ S := hJsub (Finset.mem_insert_self b {d})
  have hd : d ∈ S := hJsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self d))
  by_cases hab : G.Adj a b
  · by_cases hbc : G.Adj b c
    · by_cases hcd : G.Adj c d
      · have hda : ¬ G.Adj d a := fun hda ↦ hC4 a ha b hb c hc d hd hac hbd hab hbc hcd hda
        simpa [Finset.pair_comm] using
          tokenJumpReachableWithin_pair_of_not_adj ha hc hd hb hac (Ne.symm hbd) hI
            (by simpa [Finset.pair_comm] using hJ) (fun h ↦ hda h.symm)
      · simpa [Finset.pair_comm] using
          tokenJumpReachableWithin_pair_of_not_adj hc ha hd hb (Ne.symm hac) (Ne.symm hbd)
            (by simpa [Finset.pair_comm] using hI) (by simpa [Finset.pair_comm] using hJ) hcd
    · simpa [Finset.pair_comm] using
        tokenJumpReachableWithin_pair_of_not_adj hc ha hb hd (Ne.symm hac) hbd
          (by simpa [Finset.pair_comm] using hI) hJ (fun h ↦ hbc h.symm)
  · exact tokenJumpReachableWithin_pair_of_not_adj ha hc hb hd hac hbd hI hJ hab

/-- Every finite `k`-colorable simple graph contains an independent set `I` satisfying
`Fintype.card V ≤ k * I.card`. -/
theorem exists_isIndepSet_mul_card_ge_of_colorable [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hc : G.Colorable k) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ Fintype.card V ≤ k * I.card := by
  classical
  obtain ⟨C⟩ := hc
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : IsEmpty V := ⟨fun v ↦ (C v).elim0⟩
    exact ⟨∅, by simp, by simp⟩
  · let colorFinset : Fin k → Finset V := fun c ↦ Finset.univ.filter fun v ↦ C v = c
    have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    obtain ⟨c₀, _, hc₀⟩ := Finset.exists_max_image Finset.univ (fun c ↦ (colorFinset c).card) hne
    refine ⟨colorFinset c₀, ?_, ?_⟩
    · intro u hu v hv _ hadj
      exact C.valid hadj ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
    · have hsum : ∑ c : Fin k, (colorFinset c).card = Fintype.card V := by
        simpa [colorFinset] using
          (Finset.card_eq_sum_card_fiberwise (f := C) (s := Finset.univ) (t := Finset.univ)
            (fun _ _ ↦ Finset.mem_univ _)).symm
      calc Fintype.card V = ∑ c : Fin k, (colorFinset c).card := hsum.symm
        _ ≤ ∑ _ : Fin k, (colorFinset c₀).card :=
            Finset.sum_le_sum fun c _ ↦ hc₀ c (Finset.mem_univ c)
        _ = k * (colorFinset c₀).card := by simp

/-- Every finite acyclic simple graph (forest) contains an independent set `I` with
`Fintype.card V ≤ 2 * I.card`. -/
theorem exists_isIndepSet_two_mul_card_ge_of_isAcyclic [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ Fintype.card V ≤ 2 * I.card :=
  exists_isIndepSet_mul_card_ge_of_colorable hG.colorable_two

/-- If deleting a single vertex `v` leaves an acyclic induced subgraph `G.induce ({v}ᶜ)`, then `G`
contains an independent set `I` with `Fintype.card V ≤ 2 * I.card + 1`. -/
theorem exists_isIndepSet_two_mul_card_add_one_ge_of_isAcyclic_delete [Fintype V]
    {G : SimpleGraph V} {v : V} (hG : (G.induce ({v}ᶜ : Set V)).IsAcyclic) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ Fintype.card V ≤ 2 * I.card + 1 := by
  classical
  obtain ⟨I', hI'ind, hI'card⟩ := exists_isIndepSet_two_mul_card_ge_of_isAcyclic hG
  refine ⟨I'.map (Function.Embedding.subtype (· ∈ ({v}ᶜ : Set V))),
    (isIndepSet_map_subtype_iff I').mp hI'ind, ?_⟩
  rw [Finset.card_map]
  have h1 := Fintype.card_subtype_compl (fun x : V ↦ x = v)
  have h2 : Fintype.card {x : V // x = v} = 1 := Fintype.card_unique
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hcard : Fintype.card ({v}ᶜ : Set V) + 1 = Fintype.card V := by
    change Fintype.card {x : V // ¬ x = v} + 1 = Fintype.card V
    omega
  omega

private theorem mem_support_of_isCycle_of_connected_ncard_le_two [Finite V] {G : SimpleGraph V}
    (hconn : G.Connected) (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ 2)
    {v₀ : V} {c : G.Walk v₀ v₀} (hc : c.IsCycle) (u : V) : u ∈ c.support := by
  classical
  have hclosed : ∀ ⦃w x : V⦄, w ∈ c.support → G.Adj w x → x ∈ c.support := by
    intro w x hw hadj
    let c' : G.Walk w w := c.rotate w hw
    have hc' : c'.IsCycle := hc.rotate hw
    have hsub : ({c'.snd, c'.penultimate} : Set V) ⊆ G.neighborSet w := by
      rintro z (rfl | rfl)
      exacts [c'.adj_snd hc'.not_nil, (c'.adj_penultimate hc'.not_nil).symm]
    have hpair : ({c'.snd, c'.penultimate} : Set V).ncard = 2 :=
      Set.ncard_pair hc'.snd_ne_penultimate
    have hEq : ({c'.snd, c'.penultimate} : Set V) = G.neighborSet w :=
      Set.eq_of_subset_of_ncard_le hsub (hpair.symm ▸ hdeg w) (Set.toFinite _)
    rcases (hEq.symm ▸ hadj : x ∈ ({c'.snd, c'.penultimate} : Set V)) with rfl | rfl
    · exact (c.mem_support_rotate_iff w hw).mp (c'.getVert_mem_support 1)
    · exact (c.mem_support_rotate_iff w hw).mp (c'.getVert_mem_support (c'.length - 1))
  obtain ⟨p⟩ := hconn v₀ u
  have hwalk : ∀ {a b : V} (q : G.Walk a b), a ∈ c.support → b ∈ c.support := by
    intro a b q
    induction q with
    | nil => exact id
    | cons hadj _ ih => intro ha; exact ih (hclosed ha hadj)
  exact hwalk p c.start_mem_support

/-- Every finite connected simple graph in which every vertex has at most `2` neighbors becomes
acyclic after deleting a single vertex. -/
theorem exists_isAcyclic_delete_of_connected_ncard_le_two [Finite V] {G : SimpleGraph V}
    (hconn : G.Connected) (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ 2) :
    ∃ v : V, (G.induce ({v}ᶜ : Set V)).IsAcyclic := by
  by_cases hacyc : G.IsAcyclic
  · obtain ⟨v⟩ := hconn.nonempty
    exact ⟨v, hacyc.induce ({v}ᶜ : Set V)⟩
  · rw [IsAcyclic] at hacyc
    push Not at hacyc
    obtain ⟨v₀, c, _⟩ := hacyc
    refine ⟨v₀, fun w d hd ↦ ?_⟩
    let f : G.induce ({v₀}ᶜ : Set V) →g G := (Embedding.induce ({v₀}ᶜ : Set V)).toHom
    have hd' : (d.map f).IsCycle :=
      (Walk.isCycle_map_iff_of_injective Subtype.val_injective).mpr hd
    have hmem : v₀ ∈ (d.map f).support :=
      mem_support_of_isCycle_of_connected_ncard_le_two hconn hdeg hd' v₀
    rw [Walk.support_map] at hmem
    obtain ⟨z, _, hz⟩ := List.mem_map.mp hmem
    exact z.2 hz

/-- Every finite connected simple graph in which every vertex has at most `2` neighbors contains an
independent set `I` with `Fintype.card V ≤ 2 * I.card + 1`. -/
theorem exists_isIndepSet_two_mul_card_add_one_ge_of_connected_ncard_le_two [Fintype V]
    {G : SimpleGraph V} (hconn : G.Connected) (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ 2) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ Fintype.card V ≤ 2 * I.card + 1 := by
  obtain ⟨v, hv⟩ := exists_isAcyclic_delete_of_connected_ncard_le_two hconn hdeg
  exact exists_isIndepSet_two_mul_card_add_one_ge_of_isAcyclic_delete hv

/-- Every finite connected simple graph with vertex degrees at most `2` contains an independent set
`I` with `Fintype.card V ≤ 2 * I.card + 1`. -/
theorem exists_isIndepSet_two_mul_card_add_one_ge_of_connected_of_degree_le_two [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    (hdeg : ∀ v : V, G.degree v ≤ 2) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ Fintype.card V ≤ 2 * I.card + 1 :=
  exists_isIndepSet_two_mul_card_add_one_ge_of_connected_ncard_le_two hconn
    (fun v ↦ by rw [ncard_neighborSet]; exact hdeg v)

/-- Every finite connected simple graph with `G.maxDegree ≤ 2` contains an independent set `I`
with `Fintype.card V ≤ 2 * I.card + 1`. -/
theorem exists_isIndepSet_two_mul_card_add_one_ge_of_connected_of_maxDegree_le_two [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected) (hmax : G.maxDegree ≤ 2) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ Fintype.card V ≤ 2 * I.card + 1 :=
  exists_isIndepSet_two_mul_card_add_one_ge_of_connected_of_degree_le_two hconn
    (fun v ↦ (G.degree_le_maxDegree v).trans hmax)

end ReconfigurationTheorems

/-! ### Non-Degenerate Positive and Frozen Witnesses -/

section Witnesses

/-- Positive token-jumping witness on `pathGraph 4`: the disjoint `2`-element independent sets
`{0, 2}` and `{1, 3}` are not adjacent in one jump, yet are token-jump reachable in two jumps via
`{0, 3}`. -/
private theorem tokenJumpReachable_witness_pathGraph_four :
    (pathGraph 4).IsIndepSet (({0, 2} : Finset (Fin 4)) : Set (Fin 4)) ∧
    (pathGraph 4).IsIndepSet (({1, 3} : Finset (Fin 4)) : Set (Fin 4)) ∧
    ¬ TokenJumpAdj (pathGraph 4) {0, 2} {1, 3} ∧
    TokenJumpReachable (pathGraph 4) {0, 2} {1, 3} := by
  have hI : (pathGraph 4).IsIndepSet (({0, 2} : Finset (Fin 4)) : Set (Fin 4)) := by decide
  have hM : (pathGraph 4).IsIndepSet (({0, 3} : Finset (Fin 4)) : Set (Fin 4)) := by decide
  have hJ : (pathGraph 4).IsIndepSet (({1, 3} : Finset (Fin 4)) : Set (Fin 4)) := by decide
  have h1 : TokenJumpAdj (pathGraph 4) {0, 2} {0, 3} :=
    tokenJumpAdj_iff_insert_erase.mpr ⟨hI, hM, 2, by decide, 3, by decide, by decide⟩
  have h2 : TokenJumpAdj (pathGraph 4) {0, 3} {1, 3} :=
    tokenJumpAdj_iff_insert_erase.mpr ⟨hM, hJ, 0, by decide, 1, by decide, by decide⟩
  refine ⟨hI, hJ, fun hadj ↦ ?_, (TokenJumpReachable.single h1).trans (.single h2)⟩
  have hsdiff := hadj.sdiff_card_eq_one
  revert hsdiff
  decide

/-- Frozen witness on `completeBipartiteGraph (Fin 2) (Fin 2)` (`K_{2,2} ≅ C_4`): the two
bipartition sides `{inl 0, inl 1}` and `{inr 0, inr 1}` are `2`-element independent sets, no
single token jump leaves `{inl 0, inl 1}`, and `{inr 0, inr 1}` is unreachable from
`{inl 0, inl 1}`. This witnesses sharpness of the `4`-cycle-free hypothesis in
`tokenJumpReachableWithin_of_card_two_of_no_fourCycle`. -/
private theorem tokenJump_frozen_witness_completeBipartiteGraph_fin_two :
    let G := completeBipartiteGraph (Fin 2) (Fin 2)
    let I : Finset (Fin 2 ⊕ Fin 2) := {Sum.inl 0, Sum.inl 1}
    let J : Finset (Fin 2 ⊕ Fin 2) := {Sum.inr 0, Sum.inr 1}
    G.IsIndepSet (I : Set (Fin 2 ⊕ Fin 2)) ∧
    G.IsIndepSet (J : Set (Fin 2 ⊕ Fin 2)) ∧
    (∀ K : Finset (Fin 2 ⊕ Fin 2), ¬ TokenJumpAdj G I K) ∧
    ¬ TokenJumpReachable G I J := by
  intro G I J
  have hI : G.IsIndepSet (I : Set (Fin 2 ⊕ Fin 2)) := by
    intro x hx y hy _ hadj
    simp only [I, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [G] at hadj
  have hJ : G.IsIndepSet (J : Set (Fin 2 ⊕ Fin 2)) := by
    intro x hx y hy _ hadj
    simp only [J, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [G] at hadj
  have hfrozen : ∀ K : Finset (Fin 2 ⊕ Fin 2), ¬ TokenJumpAdj G I K := by
    intro K hadj
    obtain ⟨_, hK, v, hv, w, hw, hmem⟩ := hadj
    have hwK : w ∈ K := (hmem w).mpr (Or.inl rfl)
    cases w with
    | inl i =>
      fin_cases i
      exacts [hw (Finset.mem_insert_self _ _),
        hw (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
    | inr j =>
      rcases Finset.mem_insert.mp hv with rfl | hv'
      · have h1K : Sum.inl 1 ∈ K :=
          (hmem (Sum.inl 1)).mpr
            (Or.inr ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), by decide⟩)
        exact hK h1K hwK (by simp) (Or.inl ⟨rfl, rfl⟩)
      · rw [Finset.mem_singleton.mp hv'] at hmem
        have h0K : Sum.inl 0 ∈ K :=
          (hmem (Sum.inl 0)).mpr (Or.inr ⟨Finset.mem_insert_self _ _, by decide⟩)
        exact hK h0K hwK (by simp) (Or.inl ⟨rfl, rfl⟩)
  refine ⟨hI, hJ, hfrozen, fun hreach ↦ ?_⟩
  rcases Relation.ReflTransGen.cases_head hreach with hEq | ⟨K, hadj, _⟩
  · have hmem : Sum.inl 0 ∈ J := hEq ▸ Finset.mem_insert_self _ _
    simp [J] at hmem
  · exact hfrozen K hadj

end Witnesses

end CslibFrontier.SimpleGraph
