/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Rooted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Data.Set.Card

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Quotient
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linarith

/-!
# Pathwidth, Interval Width, Balanced Treewidth Separators, and Vertex-Cover Dominance

Textbook-general foundations for graph width parameters and parameterized Vertex Cover algorithms:

* `IsPathDecomposition`, `IsPathDecompositionOfWidthLe`, `HasPathwidthLe`, `pathwidth`:
  path decompositions and pathwidth of simple graphs, monotonicity under edge/induced subgraphs and
  vertex deletion, and `treewidth_le_pathwidth` linking pathwidth to `SimpleGraph.treewidth`
  (`SimpleGraph.RootedTreeDecomposition`).
* `IsIntervalGraph`, `HasIntervalWidthLe`, `intervalWidth`, `hasIntervalWidthLe_iff_hasPathwidthLe`,
  `intervalWidth_le_iff_pathwidth_le`, `pathwidth_le_intervalWidth_sub_one`: equivalence between
  pathwidth and minimum interval-supergraph clique size.
* `Dominates`, `StrictlyDominates`, `IsDominant`, `orderedDominantSet`,
  `Dominates.vertexCoverNum_eq`, `orderedDominantSet_vertexCover_sound`: exact vertex-cover
  preservation under single and simultaneous degree-ordered vertex-dominance reduction.
* `SeparatesIn`, `exists_balanced_bag`, `exists_balanced_three_way_separator`: existence of a
  balanced separator bag and balanced 3-way vertex separator of cardinality at most `tw(G) + 1`
.
-/

public section

namespace CslibFrontier.SimpleGraph

open _root_.SimpleGraph

/-- A sequence of bags `X : Fin m → Set V` is a *path decomposition* of `G`. -/
@[expose]
def IsPathDecomposition {V : Type*} (G : SimpleGraph V) {m : ℕ} (X : Fin m → Set V) : Prop :=
  1 ≤ m ∧ (⋃ i, X i) = Set.univ ∧
    (∀ ⦃u v : V⦄, G.Adj u v → ∃ i : Fin m, u ∈ X i ∧ v ∈ X i) ∧
    (∀ ⦃i j l : Fin m⦄, i ≤ j → j ≤ l → X i ∩ X l ⊆ X j)

/-- A path decomposition of width at most `k` (maximum bag cardinality at most `k + 1`). -/
@[expose]
def IsPathDecompositionOfWidthLe {V : Type*} (G : SimpleGraph V) {m : ℕ}
    (X : Fin m → Set V) (k : ℕ) : Prop :=
  IsPathDecomposition G X ∧ ∀ i : Fin m, (X i).Finite ∧ (X i).ncard ≤ k + 1

/-- `G` has pathwidth at most `k`. -/
@[expose]
def HasPathwidthLe {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (X : Fin m → Set V), IsPathDecompositionOfWidthLe G X k

/-- Pathwidth `pw(G)` of a simple graph `G` (`0` if no finite-width path decomposition exists). -/
@[expose]
noncomputable def pathwidth {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | HasPathwidthLe G k}

/-- `H` is an *interval graph* represented by closed real intervals `a v ≤ b v` whose pairwise
intersections define adjacency. -/
@[expose]
def IsIntervalGraph {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ a b : V → ℝ, (∀ v, a v ≤ b v) ∧
    ∀ u v, H.Adj u v ↔ u ≠ v ∧ max (a u) (a v) ≤ min (b u) (b v)

/-- `G` has interval width at most `k` if it is a spanning subgraph of an interval graph `H`
whose maximum clique size is at most `k`. -/
@[expose]
def HasIntervalWidthLe {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ H : SimpleGraph V, G ≤ H ∧ IsIntervalGraph H ∧
    ∀ K : Finset V, H.IsClique (K : Set V) → K.card ≤ k

/-- Interval width `iw(G)` of a simple graph `G`: the minimum over all interval supergraphs `H` of
the maximum clique size of `H` (`0` if none exists). -/
@[expose]
noncomputable def intervalWidth {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | HasIntervalWidthLe G k}

/-- Vertex `u` *dominates* vertex `v` in `G` if `v ∈ N(u)` and `N(v) \ {u} ⊆ N(u)`. -/
@[expose]
def Dominates {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  G.Adj u v ∧ ∀ w : V, G.Adj v w → w ≠ u → G.Adj u w

/-- Vertex `u` *strictly dominates* vertex `v` in `G` if `u` dominates `v` and `v` does not
dominate `u` (equivalently `deg(v) < deg(u)` on finite graphs). -/
@[expose]
def StrictlyDominates {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  Dominates G u v ∧ ¬ Dominates G v u

/-- Vertex `u` is *dominant* in `G` if it dominates at least one vertex. -/
@[expose]
def IsDominant {V : Type*} (G : SimpleGraph V) (u : V) : Prop :=
  ∃ v : V, Dominates G u v

/-- Degree-ordered dominance set: vertices `u` dominating some neighbor `v` of strictly smaller
degree, or of equal degree with larger linear-order key (breaking twin ties cleanly). -/
@[expose]
def orderedDominantSet {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun u =>
    ∃ v : V, G.Adj u v ∧ (∀ w : V, G.Adj v w → w ≠ u → G.Adj u w) ∧
      (G.degree v < G.degree u ∨ (G.degree v = G.degree u ∧ u < v))


section PathwidthAPI

variable {V W : Type*}

lemma HasPathwidthLe.mono {G : SimpleGraph V} {k l : ℕ} (h : HasPathwidthLe G k) (hkl : k ≤ l) :
    HasPathwidthLe G l := by
  obtain ⟨m, X, hpd, hcard⟩ := h
  exact ⟨m, X, hpd, fun i => ⟨(hcard i).1, (hcard i).2.trans (Nat.add_le_add_right hkl 1)⟩⟩

lemma HasPathwidthLe.anti {G₁ G₂ : SimpleGraph V} {k : ℕ} (hle : G₁ ≤ G₂)
    (h : HasPathwidthLe G₂ k) : HasPathwidthLe G₁ k := by
  obtain ⟨m, X, ⟨hm, hcov, hadj, hcon⟩, hcard⟩ := h
  exact ⟨m, X, ⟨hm, hcov, fun u v huv => hadj (hle huv), hcon⟩, hcard⟩

lemma hasPathwidthLe_natCard_sub_one [Finite V] (G : SimpleGraph V) :
    HasPathwidthLe G (Nat.card V - 1) := by
  refine ⟨1, fun _ => Set.univ, ⟨le_rfl, ?_, fun u v _ => ⟨0, trivial, trivial⟩,
    fun _ _ _ _ _ _ h => h.1⟩, fun _ => ⟨Set.finite_univ, ?_⟩⟩
  · ext v; simp
  · rw [Set.ncard_univ]
    rcases Nat.eq_zero_or_pos (Nat.card V) with h0 | hpos <;> omega

lemma hasPathwidthLe_pathwidth [Finite V] (G : SimpleGraph V) :
    HasPathwidthLe G (pathwidth G) :=
  Nat.sInf_mem (s := {k : ℕ | HasPathwidthLe G k})
    ⟨Nat.card V - 1, hasPathwidthLe_natCard_sub_one G⟩

lemma pathwidth_le_iff [Finite V] {G : SimpleGraph V} {k : ℕ} :
    pathwidth G ≤ k ↔ HasPathwidthLe G k :=
  ⟨fun h => (hasPathwidthLe_pathwidth G).mono h, fun h => Nat.sInf_le h⟩

lemma pathwidth_mono [Finite V] {G₁ G₂ : SimpleGraph V} (hle : G₁ ≤ G₂) :
    pathwidth G₁ ≤ pathwidth G₂ :=
  pathwidth_le_iff.mpr ((hasPathwidthLe_pathwidth G₂).anti hle)

lemma HasPathwidthLe.induce {G : SimpleGraph V} {k : ℕ} (h : HasPathwidthLe G k) (S : Set V) :
    HasPathwidthLe (G.induce S) k := by
  obtain ⟨m, X, ⟨hm, hcov, hadj, hcon⟩, hcard⟩ := h
  refine ⟨m, fun i => Subtype.val ⁻¹' X i, ⟨hm, ?_, ?_, ?_⟩, fun i => ?_⟩
  · ext v
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
    have hv : v.val ∈ ⋃ i, X i := hcov ▸ Set.mem_univ v.val
    exact Set.mem_iUnion.mp hv
  · intro u v huv
    obtain ⟨i, hu, hv⟩ := hadj huv
    exact ⟨i, hu, hv⟩
  · intro i j l hij hjl v ⟨hvi, hvl⟩
    exact hcon hij hjl ⟨hvi, hvl⟩
  · refine ⟨(hcard i).1.preimage Subtype.val_injective.injOn, ?_⟩
    calc (Subtype.val ⁻¹' X i).ncard
        = (Subtype.val '' (Subtype.val ⁻¹' X i)).ncard :=
            (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (X i).ncard := Set.ncard_le_ncard (Set.image_preimage_subset _ _) (hcard i).1
      _ ≤ k + 1 := (hcard i).2

lemma pathwidth_induce_le [Finite V] (G : SimpleGraph V) (S : Set V) :
    pathwidth (G.induce S) ≤ pathwidth G :=
  pathwidth_le_iff.mpr ((hasPathwidthLe_pathwidth G).induce S)

lemma HasPathwidthLe.of_induce_compl_singleton {G : SimpleGraph V} {v : V} {k : ℕ}
    (h : HasPathwidthLe (G.induce ({v}ᶜ : Set V)) k) :
    HasPathwidthLe G (k + 1) := by
  obtain ⟨m, X, ⟨hm, hcov, hadj, hcon⟩, hcard⟩ := h
  let Y : Fin m → Set V := fun i => insert v (Subtype.val '' X i)
  refine ⟨m, Y, ⟨hm, ?_, ?_, ?_⟩, fun i => ?_⟩
  · ext u
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Y]
    by_cases huv : u = v
    · exact ⟨⟨0, hm⟩, Or.inl huv⟩
    · have hu : (⟨u, huv⟩ : ({v}ᶜ : Set V)) ∈ ⋃ i, X i := hcov ▸ Set.mem_univ _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
      exact ⟨i, Or.inr ⟨⟨u, huv⟩, hi, rfl⟩⟩
  · intro x y hxy
    by_cases hx : x = v
    · by_cases hy : y = v
      · exact absurd (hx.trans hy.symm) hxy.ne
      · have hy' : (⟨y, hy⟩ : ({v}ᶜ : Set V)) ∈ ⋃ i, X i := hcov ▸ Set.mem_univ _
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy'
        exact ⟨i, Or.inl hx, Or.inr ⟨⟨y, hy⟩, hi, rfl⟩⟩
    · by_cases hy : y = v
      · have hx' : (⟨x, hx⟩ : ({v}ᶜ : Set V)) ∈ ⋃ i, X i := hcov ▸ Set.mem_univ _
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
        exact ⟨i, Or.inr ⟨⟨x, hx⟩, hi, rfl⟩, Or.inl hy⟩
      · obtain ⟨i, hxi, hyi⟩ := hadj (show (G.induce ({v}ᶜ : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
        exact ⟨i, Or.inr ⟨_, hxi, rfl⟩, Or.inr ⟨_, hyi, rfl⟩⟩
  · intro i j l hij hjl u ⟨hui, hul⟩
    rcases hui with rfl | ⟨x, hxi, rfl⟩
    · exact Or.inl rfl
    · rcases hul with hxv | ⟨y, hyl, hyx⟩
      · exact absurd hxv (Set.mem_compl_singleton_iff.mp x.2)
      · have hxy : x = y := Subtype.ext hyx.symm
        subst hxy
        exact Or.inr ⟨x, hcon hij hjl ⟨hxi, hyl⟩, rfl⟩
  · refine ⟨((hcard i).1.image Subtype.val).insert v, ?_⟩
    calc (Y i).ncard ≤ (Subtype.val '' X i).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ (X i).ncard + 1 := Nat.add_le_add_right (Set.ncard_image_le (hcard i).1) 1
      _ ≤ (k + 1) + 1 := Nat.add_le_add_right (hcard i).2 1

lemma pathwidth_le_induce_compl_add_card [Finite V] (G : SimpleGraph V) (S : Finset V) :
    pathwidth G ≤ pathwidth (G.induce ((S : Set V)ᶜ)) + S.card := by
  classical
  suffices hgen : ∀ (k : ℕ) {W : Type _} [Finite W] (H : SimpleGraph W) (T : Finset W),
      T.card = k → pathwidth H ≤ pathwidth (H.induce ((T : Set W)ᶜ)) + T.card from
    hgen S.card G S rfl
  intro k
  induction k with
  | zero =>
    intro W _ H T hcard
    have hTe : T = ∅ := Finset.card_eq_zero.mp hcard
    subst hTe
    have hcompl : ((∅ : Finset W) : Set W)ᶜ = Set.univ := by simp
    simp only [Finset.card_empty, add_zero]
    rw [hcompl, pathwidth_le_iff]
    obtain ⟨m, X, ⟨hm, hcov, hadj, hcon⟩, hcardX⟩ := hasPathwidthLe_pathwidth (H.induce Set.univ)
    refine ⟨m, fun i => Subtype.val '' X i, ⟨hm, ?_, ?_, ?_⟩, fun i => ?_⟩
    · ext u
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Set.mem_image]
      have hu : (⟨u, trivial⟩ : (Set.univ : Set W)) ∈ ⋃ i, X i := hcov ▸ Set.mem_univ _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
      exact ⟨i, ⟨u, trivial⟩, hi, rfl⟩
    · intro u v huv
      obtain ⟨i, hu, hv⟩ := hadj (show (H.induce Set.univ).Adj ⟨u, trivial⟩ ⟨v, trivial⟩ from huv)
      exact ⟨i, ⟨_, hu, rfl⟩, ⟨_, hv, rfl⟩⟩
    · intro i j l hij hjl u ⟨⟨x, hxi, hxu⟩, ⟨y, hyl, hyu⟩⟩
      have : x = y := Subtype.ext (hxu.trans hyu.symm)
      subst this
      exact ⟨x, hcon hij hjl ⟨hxi, hyl⟩, hxu⟩
    · exact ⟨(hcardX i).1.image Subtype.val, (Set.ncard_image_le (hcardX i).1).trans (hcardX i).2⟩
  | succ k ih =>
    intro W _ H T hcard
    classical
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, haT⟩ := hTne
    let S := T.erase a
    have hS_card : S.card = k := by rw [Finset.card_erase_of_mem haT, hcard]; omega
    have hT_eq : insert a S = T := Finset.insert_erase haT
    have haS : a ∉ S := Finset.notMem_erase a T
    have hstep1 : pathwidth H ≤ pathwidth (H.induce ({a}ᶜ : Set W)) + 1 :=
      pathwidth_le_iff.mpr (HasPathwidthLe.of_induce_compl_singleton (hasPathwidthLe_pathwidth _))
    let S' : Finset ({a}ᶜ : Set W) := S.subtype fun x => x ∈ ({a}ᶜ : Set W)
    have hS'_card : S'.card = k := by
      rw [← hS_card]
      refine Finset.card_bij (fun x _ => x.val) (fun x hx => Finset.mem_subtype.mp hx)
        (fun _ _ _ _ h => Subtype.ext h) (fun y hy => ?_)
      have hya : y ≠ a := fun h => haS (h ▸ hy)
      exact ⟨⟨y, hya⟩, Finset.mem_subtype.mpr hy, rfl⟩
    have hih := ih (H.induce ({a}ᶜ : Set W)) S' hS'_card
    have hsub : pathwidth ((H.induce ({a}ᶜ : Set W)).induce ((S' : Set ({a}ᶜ : Set W))ᶜ)) ≤
        pathwidth (H.induce ((T : Set W)ᶜ)) := by
      rw [pathwidth_le_iff]
      obtain ⟨m, X, ⟨hm, hcov, hadj, hcon⟩, hcardX⟩ :=
        hasPathwidthLe_pathwidth (H.induce ((T : Set W)ᶜ))
      let f : {x : ({a}ᶜ : Set W) // x ∉ (S' : Set ({a}ᶜ : Set W))} →
          {x : W // x ∉ (T : Set W)} := fun x =>
        ⟨x.1.1, by
          intro hx
          rw [← hT_eq] at hx
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
          rcases hx with hxa | hS
          · exact absurd hxa (Set.mem_compl_singleton_iff.mp x.1.2)
          · exact x.2 (Finset.mem_subtype.mpr hS)⟩
      have hf_inj : Function.Injective f := fun x y h =>
        Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h))
      refine ⟨m, fun i => f ⁻¹' X i, ⟨hm, ?_, ?_, ?_⟩, fun i => ?_⟩
      · ext x
        simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
        have hx : f x ∈ ⋃ i, X i := hcov ▸ Set.mem_univ _
        exact Set.mem_iUnion.mp hx
      · intro u v huv
        exact hadj huv
      · intro i j l hij hjl x ⟨hxi, hxl⟩
        exact hcon hij hjl ⟨hxi, hxl⟩
      · refine ⟨(hcardX i).1.preimage hf_inj.injOn, ?_⟩
        calc (f ⁻¹' X i).ncard
            = (f '' (f ⁻¹' X i)).ncard := (Set.ncard_image_of_injective _ hf_inj).symm
          _ ≤ (X i).ncard := Set.ncard_le_ncard (Set.image_preimage_subset _ _) (hcardX i).1
          _ ≤ _ := (hcardX i).2
    omega

/-- Convert a path decomposition `X : Fin m → Set V` of width `≤ k` into a
`CslibFrontier` `SimpleGraph.RootedTreeDecomposition` on `Fin ((m - 1) + 1)` of width `≤ k`. -/
noncomputable def IsPathDecompositionOfWidthLe.toRootedTreeDecomposition
    {G : SimpleGraph V} {m k : ℕ} {X : Fin m → Set V}
    (hX : IsPathDecompositionOfWidthLe G X k) :
    G.RootedTreeDecomposition (m - 1) := by
  classical
  have hm : 1 ≤ m := hX.1.1
  have hm_eq : m - 1 + 1 = m := Nat.sub_add_cancel hm
  let bagFin : Fin (m - 1 + 1) → Finset V := fun i => (hX.2 (Fin.cast hm_eq i)).1.toFinset
  let par : Fin (m - 1 + 1) → Fin (m - 1 + 1) := fun i =>
    if h : i.val = 0 then 0 else ⟨i.val - 1, by omega⟩
  refine
    { parent := par
      parent_zero := by simp [par]
      parent_lt := fun i hi => by
        have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simp only [par, hi0, ↓reduceDIte]
        exact Fin.mk_lt_mk.mpr (by omega)
      bag := bagFin
      exists_mem_bag := fun v => by
        have hv : v ∈ ⋃ i, X i := hX.1.2.1 ▸ Set.mem_univ v
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
        exact ⟨Fin.cast hm_eq.symm i, by simp [bagFin, hi]⟩
      exists_adj_mem_bag := fun u v huv => by
        obtain ⟨i, hu, hv⟩ := hX.1.2.2.1 huv
        exact ⟨Fin.cast hm_eq.symm i, by simp [bagFin, hu], by simp [bagFin, hv]⟩
      top_unique := fun v i j hi htop_i hj htop_j => by
        by_contra hne
        wlog hlt : i < j generalizing i j
        · exact this j i hj htop_j hi htop_i (Ne.symm hne)
            (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
        have hj0 : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hlt)
        have hjp_not : v ∉ bagFin (par j) := htop_j.resolve_left hj0
        have hj0_val : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        have hle1 : Fin.cast hm_eq i ≤ Fin.cast hm_eq (par j) := by
          change i.val ≤ (par j).val
          simp only [par, hj0_val, ↓reduceDIte]
          have : i.val < j.val := hlt
          omega
        have hle2 : Fin.cast hm_eq (par j) ≤ Fin.cast hm_eq j := by
          change (par j).val ≤ j.val
          simp only [par, hj0_val, ↓reduceDIte]
          omega
        have hmem_p : v ∈ X (Fin.cast hm_eq (par j)) :=
          hX.1.2.2.2 hle1 hle2 ⟨(Set.Finite.mem_toFinset _).mp hi,
            (Set.Finite.mem_toFinset _).mp hj⟩
        exact hjp_not ((Set.Finite.mem_toFinset _).mpr hmem_p) }

lemma IsPathDecompositionOfWidthLe.toRootedTreeDecomposition_width_le
    {G : SimpleGraph V} {m k : ℕ} {X : Fin m → Set V}
    (hX : IsPathDecompositionOfWidthLe G X k) :
    hX.toRootedTreeDecomposition.toTreeDecomposition.width ≤ k := by
  classical
  rw [SimpleGraph.TreeDecomposition.width_le_iff,
    SimpleGraph.RootedTreeDecomposition.toTreeDecomposition_bag]
  intro t
  have hcard := (hX.2 (Fin.cast (Nat.sub_add_cancel hX.1.1) t)).2
  rw [Set.ncard_eq_toFinset_card _ (hX.2 (Fin.cast (Nat.sub_add_cancel hX.1.1) t)).1] at hcard
  exact hcard

/-- Pathwidth is an upper bound on `CslibFrontier`'s `SimpleGraph.treewidth`. -/
theorem treewidth_le_pathwidth [Finite V] (G : SimpleGraph V) :
    G.treewidth ≤ pathwidth G := by
  obtain ⟨m, X, hX⟩ := hasPathwidthLe_pathwidth G
  let R := hX.toRootedTreeDecomposition
  exact (SimpleGraph.treewidth_le_width R.toTreeDecomposition).trans
    hX.toRootedTreeDecomposition_width_le

end PathwidthAPI

/-! ### Interval Width and Equivalence with Pathwidth -/

section IntervalWidth

variable {V : Type*}

/-- Helly property for closed intervals on `ℝ`: every finite nonempty family of pairwise
intersecting closed intervals contains a common point (namely the maximum left endpoint). -/
lemma helly_closed_intervals {ι : Type*} {a b : ι → ℝ} {K : Finset ι} (hK : K.Nonempty)
    (hpair : ∀ i ∈ K, ∀ j ∈ K, max (a i) (a j) ≤ min (b i) (b j)) :
    ∃ x : ℝ, ∀ i ∈ K, a i ≤ x ∧ x ≤ b i := by
  obtain ⟨i₀, hi₀, hmax⟩ := K.exists_max_image a hK
  refine ⟨a i₀, fun j hj => ⟨hmax j hj, ?_⟩⟩
  have h := hpair i₀ hi₀ j hj
  exact (le_max_left (a i₀) (a j)).trans (h.trans (min_le_right (b i₀) (b j)))

/-- **Interval width vs. pathwidth**:
`HasIntervalWidthLe G (k + 1) ↔ HasPathwidthLe G k` for every finite graph `G`.
-/
theorem hasIntervalWidthLe_iff_hasPathwidthLe [Finite V] {G : SimpleGraph V} {k : ℕ} :
    HasIntervalWidthLe G (k + 1) ↔ HasPathwidthLe G k := by
  classical
  let : Fintype V := Fintype.ofFinite V
  constructor
  · rintro ⟨H, hGH, ⟨a, b, hab, hHadj⟩, hclique⟩
    rcases isEmpty_or_nonempty V with hV | hV
    · refine ⟨1, fun _ => ∅, ⟨le_rfl, ?_, fun u _ _ => isEmptyElim u,
        fun _ _ _ _ _ _ h => h.1⟩, fun _ => ⟨Set.finite_empty, by simp⟩⟩
      ext u; exact isEmptyElim u
    · let pts : Finset ℝ := Finset.univ.image a
      let L : List ℝ := pts.sort (· ≤ ·)
      have hL_pos : 1 ≤ L.length := by
        rw [Finset.length_sort]
        exact Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
      let X : Fin L.length → Set V := fun i => {v : V | a v ≤ L[i] ∧ L[i] ≤ b v}
      refine ⟨L.length, X, ⟨hL_pos, ?_, ?_, ?_⟩, fun i => ?_⟩
      · ext v
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true, X, Set.mem_ofPred_eq]
        have hmem : a v ∈ L :=
          (Finset.mem_sort _).mpr (Finset.mem_image_of_mem a (Finset.mem_univ v))
        obtain ⟨i, hi_lt, hi⟩ := List.mem_iff_getElem.mp hmem
        exact ⟨⟨i, hi_lt⟩, by simp [hi], by simp [hi, hab v]⟩
      · intro u v huv
        have hHad : H.Adj u v := hGH huv
        obtain ⟨_, hinter⟩ := (hHadj u v).mp hHad
        set x := max (a u) (a v)
        have hx_mem : x ∈ L := by
          rw [Finset.mem_sort]
          rcases le_total (a u) (a v) with h | h
          · simp only [x, max_eq_right h]; exact Finset.mem_image_of_mem a (Finset.mem_univ v)
          · simp only [x, max_eq_left h]; exact Finset.mem_image_of_mem a (Finset.mem_univ u)
        obtain ⟨i, hi_lt, hi⟩ := List.mem_iff_getElem.mp hx_mem
        refine ⟨⟨i, hi_lt⟩, ?_, ?_⟩
        · simp only [X, Set.mem_ofPred_eq, Fin.getElem_fin, hi]
          exact ⟨le_max_left _ _, hinter.trans (min_le_left _ _)⟩
        · simp only [X, Set.mem_ofPred_eq, Fin.getElem_fin, hi]
          exact ⟨le_max_right _ _, hinter.trans (min_le_right _ _)⟩
      · intro i j l hij hjl v ⟨hvi, hvl⟩
        have hsorted : L.Pairwise (· ≤ ·) := Finset.pairwise_sort pts (· ≤ ·)
        have hle_ij : L[i] ≤ L[j] := by
          rcases eq_or_lt_of_le hij with rfl | hlt
          · exact le_rfl
          · exact List.pairwise_iff_getElem.mp hsorted i.val j.val i.isLt j.isLt hlt
        have hle_jl : L[j] ≤ L[l] := by
          rcases eq_or_lt_of_le hjl with rfl | hlt
          · exact le_rfl
          · exact List.pairwise_iff_getElem.mp hsorted j.val l.val j.isLt l.isLt hlt
        exact ⟨hvi.1.trans hle_ij, hle_jl.trans hvl.2⟩
      · refine ⟨Set.toFinite _, ?_⟩
        rw [Set.ncard_eq_toFinset_card']
        refine hclique (X i).toFinset ?_
        intro u hu v hv hne
        simp only [Finset.mem_coe, Set.mem_toFinset] at hu hv
        rw [hHadj u v]
        exact ⟨hne, (max_le hu.1 hv.1).trans (le_min hu.2 hv.2)⟩
  · rintro ⟨m, X, ⟨hm, hcov, hadj, hcon⟩, hcard⟩
    have hex : ∀ v : V, (Finset.univ.filter fun i : Fin m => v ∈ X i).Nonempty := by
      intro v
      have hv : v ∈ ⋃ i, X i := hcov ▸ Set.mem_univ v
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    let a : V → ℝ := fun v => ((Finset.univ.filter fun i : Fin m => v ∈ X i).min' (hex v) : ℕ)
    let b : V → ℝ := fun v => ((Finset.univ.filter fun i : Fin m => v ∈ X i).max' (hex v) : ℕ)
    let H : SimpleGraph V :=
      { Adj := fun u v => u ≠ v ∧ max (a u) (a v) ≤ min (b u) (b v)
        symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by simpa only [max_comm, min_comm] using h⟩⟩
        loopless := ⟨fun _ h => h.1 rfl⟩ }
    refine ⟨H, ?_, ⟨a, b, ?_, fun _ _ => Iff.rfl⟩, ?_⟩
    · intro u v huv
      obtain ⟨i, hui, hvi⟩ := hadj huv
      refine ⟨huv.ne, ?_⟩
      have hau : a u ≤ (i : ℕ) := by
        dsimp only [a]
        exact Nat.cast_le.mpr (Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hui⟩))
      have hav : a v ≤ (i : ℕ) := by
        dsimp only [a]
        exact Nat.cast_le.mpr (Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvi⟩))
      have hbu : ((i : ℕ) : ℝ) ≤ b u := by
        dsimp only [b]
        exact Nat.cast_le.mpr (Finset.le_max' _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hui⟩))
      have hbv : ((i : ℕ) : ℝ) ≤ b v := by
        dsimp only [b]
        exact Nat.cast_le.mpr (Finset.le_max' _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvi⟩))
      exact (max_le hau hav).trans (le_min hbu hbv)
    · intro v
      dsimp only [a, b]
      exact Nat.cast_le.mpr (Finset.min'_le_max' _ (hex v))
    · intro K hK
      rcases K.eq_empty_or_nonempty with rfl | hKne
      · simp
      · have hab : ∀ v ∈ K, a v ≤ b v := fun v _ => by
          dsimp only [a, b]
          exact Nat.cast_le.mpr (Finset.min'_le_max' _ (hex v))
        have hpair : ∀ u ∈ K, ∀ v ∈ K, max (a u) (a v) ≤ min (b u) (b v) := by
          intro u hu v hv
          rcases eq_or_ne u v with rfl | hne
          · simpa using hab u hu
          · exact (hK hu hv hne).2
        obtain ⟨i₀, hi₀, hmax⟩ := K.exists_max_image
          (fun v => (Finset.univ.filter fun i : Fin m => v ∈ X i).min' (hex v)) hKne
        let j : Fin m := (Finset.univ.filter fun i : Fin m => i₀ ∈ X i).min' (hex i₀)
        have hsub : (K : Set V) ⊆ X j := by
          intro v hv
          have hv_mem : v ∈ K := hv
          let S_v := Finset.univ.filter fun i : Fin m => v ∈ X i
          have hmin_le : S_v.min' (hex v) ≤ j := hmax v hv_mem
          have hj_le_max : j ≤ S_v.max' (hex v) := by
            have hle : a i₀ ≤ b v :=
              (le_max_left _ _).trans ((hpair i₀ hi₀ v hv_mem).trans (min_le_right _ _))
            dsimp only [a, b] at hle
            exact Nat.cast_le.mp hle
          have hmem1 : v ∈ X (S_v.min' (hex v)) :=
            (Finset.mem_filter.mp (Finset.min'_mem S_v (hex v))).2
          have hmem2 : v ∈ X (S_v.max' (hex v)) :=
            (Finset.mem_filter.mp (Finset.max'_mem S_v (hex v))).2
          exact hcon hmin_le hj_le_max ⟨hmem1, hmem2⟩
        calc K.card = (K : Set V).ncard := (Set.ncard_coe_finset K).symm
          _ ≤ (X j).ncard := Set.ncard_le_ncard hsub (hcard j).1
          _ ≤ k + 1 := (hcard j).2

/-- **Interval width and pathwidth equivalence**:
`intervalWidth G ≤ k + 1 ↔ pathwidth G ≤ k`.
-/
theorem intervalWidth_le_iff_pathwidth_le [Finite V] (G : SimpleGraph V) (k : ℕ) :
    intervalWidth G ≤ k + 1 ↔ pathwidth G ≤ k := by
  have hne : {j : ℕ | HasIntervalWidthLe G j}.Nonempty :=
    ⟨Nat.card V - 1 + 1, hasIntervalWidthLe_iff_hasPathwidthLe.mpr
      (hasPathwidthLe_natCard_sub_one G)⟩
  have hmem : HasIntervalWidthLe G (intervalWidth G) := Nat.sInf_mem hne
  have hiw_iff : intervalWidth G ≤ k + 1 ↔ HasIntervalWidthLe G (k + 1) := by
    refine ⟨fun h => ?_, fun h => Nat.sInf_le h⟩
    obtain ⟨H, hGH, hH, hcl⟩ := hmem
    exact ⟨H, hGH, hH, fun K hK => (hcl K hK).trans h⟩
  rw [hiw_iff, hasIntervalWidthLe_iff_hasPathwidthLe, pathwidth_le_iff]

lemma pathwidth_le_intervalWidth_sub_one [Finite V] (G : SimpleGraph V) :
    pathwidth G ≤ intervalWidth G - 1 := by
  rcases Nat.eq_zero_or_pos (intervalWidth G) with h0 | hpos
  · have hle1 : intervalWidth G ≤ 0 + 1 := by omega
    have := (intervalWidth_le_iff_pathwidth_le G 0).mp hle1
    omega
  · have hle : intervalWidth G ≤ (intervalWidth G - 1) + 1 := by omega
    exact (intervalWidth_le_iff_pathwidth_le G (intervalWidth G - 1)).mp hle

end IntervalWidth

/-! ### Vertex-Cover Dominance Reduction -/

section Dominance

variable {V : Type*}

/-- Single-step dominance reduction soundness: if `u` dominates `v` in `G`,
then any vertex cover `S` not containing `u` can be swapped to a vertex cover containing `u` of
no larger cardinality by replacing `v` with `u`. -/
theorem Dominates.exists_vertexCover_mem_of_not_mem {G : SimpleGraph V} {u v : V}
    (hdom : Dominates G u v) {S : Set V} (hS : G.IsVertexCover S) :
    ∃ S' : Set V, G.IsVertexCover S' ∧ u ∈ S' ∧ S'.encard ≤ S.encard := by
  by_cases hu : u ∈ S
  · exact ⟨S, hS, hu, le_rfl⟩
  · refine ⟨insert u (S \ {v}), ?_, Set.mem_insert u _, ?_⟩
    · intro x y hxy
      by_cases hxu : x = u
      · subst hxu; exact Or.inl (Set.mem_insert x _)
      · by_cases hyu : y = u
        · subst hyu; exact Or.inr (Set.mem_insert y _)
        · by_cases hxv : x = v
          · have hy_adj : G.Adj u y := hdom.2 y (hxv ▸ hxy) hyu
            have hyS : y ∈ S := (hS hy_adj).resolve_left hu
            exact Or.inr (Set.mem_insert_of_mem u ⟨hyS, fun hyv => hxy.ne (hxv.trans hyv.symm)⟩)
          · by_cases hyv : y = v
            · have hx_adj : G.Adj u x := hdom.2 x (hyv ▸ hxy.symm) hxu
              have hxS : x ∈ S := (hS hx_adj).resolve_left hu
              exact Or.inl (Set.mem_insert_of_mem u ⟨hxS, hxv⟩)
            · rcases hS hxy with hxS | hyS
              · exact Or.inl (Set.mem_insert_of_mem u ⟨hxS, hxv⟩)
              · exact Or.inr (Set.mem_insert_of_mem u ⟨hyS, hyv⟩)
    · have hvS : v ∈ S := (hS hdom.1).resolve_left hu
      have hcard : (insert u (S \ {v})).encard ≤ (insert v (S \ {v})).encard := by
        calc (insert u (S \ {v})).encard
            ≤ (S \ {v}).encard + 1 := Set.encard_insert_le (S \ {v}) u
          _ = (insert v (S \ {v})).encard := by
              rw [Set.encard_insert_of_notMem (show v ∉ S \ {v} from fun h => h.2 rfl)]
      have heq : insert v (S \ {v}) = S := Set.insert_sdiff_self_of_mem hvS
      rwa [heq] at hcard

/-- Single-step dominance reduction exact cardinality equation:
if `u` dominates `v` in a graph `G`, then
`G.vertexCoverNum = 1 + (G.induce ({u}ᶜ : Set V)).vertexCoverNum`. -/
theorem Dominates.vertexCoverNum_eq {G : SimpleGraph V} {u v : V}
    (hdom : Dominates G u v) :
    G.vertexCoverNum = 1 + (G.induce ({u}ᶜ : Set V)).vertexCoverNum := by
  classical
  apply le_antisymm
  · obtain ⟨C', hC'_card, hC'_cov⟩ := (G.induce ({u}ᶜ : Set V)).vertexCoverNum_exists
    let S : Set V := insert u (Subtype.val '' C')
    have hS_cov : G.IsVertexCover S := by
      intro x y hxy
      by_cases hx : x = u
      · subst hx; exact Or.inl (Set.mem_insert x _)
      · by_cases hy : y = u
        · subst hy; exact Or.inr (Set.mem_insert y _)
        · rcases hC'_cov (show (G.induce ({u}ᶜ : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy) with h | h
          · exact Or.inl (Set.mem_insert_of_mem u ⟨_, h, rfl⟩)
          · exact Or.inr (Set.mem_insert_of_mem u ⟨_, h, rfl⟩)
    have hS_card : S.encard = 1 + C'.encard := by
      rw [Set.encard_insert_of_notMem (by rintro ⟨x, _, hx⟩; exact x.2 hx),
        Subtype.val_injective.encard_image, add_comm]
    calc G.vertexCoverNum ≤ S.encard := hS_cov.vertexCoverNum_le
      _ = 1 + (G.induce ({u}ᶜ : Set V)).vertexCoverNum := by rw [hS_card, hC'_card]
  · obtain ⟨S, hS_card, hS_cov⟩ := G.vertexCoverNum_exists
    obtain ⟨S', hS'_cov, huS', hS'_le⟩ := hdom.exists_vertexCover_mem_of_not_mem hS_cov
    let C' : Set ({u}ᶜ : Set V) := Subtype.val ⁻¹' S'
    have hC'_cov : (G.induce ({u}ᶜ : Set V)).IsVertexCover C' := by
      intro x y hxy
      exact hS'_cov hxy
    have hC'_card : 1 + C'.encard = S'.encard := by
      have himg : Subtype.val '' C' = S' \ {u} := by
        ext x
        simp only [Set.mem_image, Set.mem_preimage, C', Set.mem_sdiff, Set.mem_singleton_iff]
        exact ⟨fun ⟨y, hy, hyx⟩ => ⟨hyx ▸ hy, hyx ▸ y.2⟩, fun ⟨hx, hxu⟩ => ⟨⟨x, hxu⟩, hx, rfl⟩⟩
      rw [← Subtype.val_injective.encard_image, himg, add_comm,
        ← Set.encard_insert_of_notMem (show u ∉ S' \ {u} from fun h => h.2 rfl),
        Set.insert_sdiff_self_of_mem huS']
    calc 1 + (G.induce ({u}ᶜ : Set V)).vertexCoverNum
        ≤ 1 + C'.encard := add_le_add_right hC'_cov.vertexCoverNum_le 1
      _ = S'.encard := hC'_card
      _ ≤ S.encard := hS'_le
      _ = G.vertexCoverNum := hS_card

/-- **Simultaneous soundness of `orderedDominantSet G`**: on any finite graph `G` with a linear
order on vertices, removing all vertices in `orderedDominantSet G` simultaneously preserves the
exact minimum vertex cover number: `G.vertexCoverNum = (orderedDominantSet G).card +
(G.induce (orderedDominantSet G)ᶜ).vertexCoverNum`. -/
theorem orderedDominantSet_vertexCover_sound [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.vertexCoverNum = (orderedDominantSet G).card +
      (G.induce ((orderedDominantSet G : Set V)ᶜ)).vertexCoverNum := by
  classical
  -- Clean generalized induction over `W` with already-removed prefix `R`!
  suffices hgen : ∀ (k : ℕ) (R W : Finset V), W.card = k → Disjoint R W →
      (∀ x ∈ W, ∃ v : V, v ∉ R ∧ G.Adj x v ∧
        (∀ w : V, w ∉ R → G.Adj v w → w ≠ x → G.Adj x w) ∧
        (G.degree v < G.degree x ∨ (G.degree v = G.degree x ∧ x < v))) →
      (G.induce ((R : Set V)ᶜ)).vertexCoverNum =
        (W.card : ℕ∞) + (G.induce (((R ∪ W : Finset V) : Set V)ᶜ)).vertexCoverNum by
    have h := hgen (orderedDominantSet G).card ∅ (orderedDominantSet G) rfl
      (Finset.disjoint_empty_left _) (by
        intro x hx
        simp only [Finset.notMem_empty, not_false_eq_true, true_and]
        obtain ⟨v, hadj, hdom, hord⟩ := (Finset.mem_filter.mp hx).2
        exact ⟨v, hadj, fun w _ => hdom w, hord⟩)
    have h1 : (∅ ∪ orderedDominantSet G) = orderedDominantSet G := Finset.empty_union _
    have h2 : (((∅ : Finset V) : Set V)ᶜ) = Set.univ := by simp
    rw [h1, h2] at h
    let e : (G.induce (Set.univ : Set V)) ≃g G :=
      { toFun := Subtype.val, invFun := fun x => ⟨x, trivial⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl, map_rel_iff' := Iff.rfl }
    rw [← _root_.SimpleGraph.vertexCoverNum_congr e]
    exact h
  intro k
  induction k with
  | zero =>
    intro R W hcard _ _
    have hWe : W = ∅ := Finset.card_eq_zero.mp hcard
    subst hWe
    have hR : R ∪ ∅ = R := Finset.union_empty R
    rw [hR]
    simp
  | succ k ih =>
    intro R W hcard hdisj hW
    have hWne : W.Nonempty := Finset.card_pos.mp (by omega)
    let degMax := W.sup' hWne (fun x => G.degree x)
    let Wmax := W.filter fun x => G.degree x = degMax
    have hWmax_ne : Wmax.Nonempty := by
      obtain ⟨x, hxW, hx⟩ := W.exists_max_image (fun x => G.degree x) hWne
      refine ⟨x, Finset.mem_filter.mpr
        ⟨hxW, le_antisymm (Finset.le_sup' (f := fun z => G.degree z) hxW) ?_⟩⟩
      exact Finset.sup'_le hWne _ fun y hy => hx y hy
    let u := Wmax.min' hWmax_ne
    have huWmax : u ∈ Wmax := Finset.min'_mem Wmax hWmax_ne
    have huW : u ∈ W := (Finset.mem_filter.mp huWmax).1
    have hu_deg : G.degree u = degMax := (Finset.mem_filter.mp huWmax).2
    have huR : u ∉ R := fun h => Finset.disjoint_left.mp hdisj h huW
    obtain ⟨v, hvR, huv, hvdom, hvord⟩ := hW u huW
    -- `u` dominates `v` inside `G.induce (Rᶜ)`!
    have hdom_R : Dominates (G.induce ((R : Set V)ᶜ)) ⟨u, huR⟩ ⟨v, hvR⟩ :=
      ⟨huv, fun w hw hwu => hvdom w.val w.2 hw (fun heq => hwu (Subtype.ext heq))⟩
    have hstep := hdom_R.vertexCoverNum_eq
    -- Identify `((G.induce Rᶜ).induce {⟨u, huR⟩}ᶜ)` with `G.induce ((insert u R)ᶜ)`.
    let e₁ : ((G.induce ((R : Set V)ᶜ)).induce ({⟨u, huR⟩}ᶜ : Set _)) ≃g
        (G.induce (((insert u R : Finset V) : Set V)ᶜ)) :=
      { toFun := fun x => ⟨x.1.1, by
          intro hx
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
          rcases hx with hxu | hR
          · exact x.2 (Set.mem_singleton_iff.mpr (Subtype.ext hxu))
          · exact x.1.2 hR⟩
        invFun := fun x => ⟨⟨x.1, fun hR => x.2 (by simp [hR])⟩,
          fun heq => x.2 (by
            have hxu : x.1 = u := congrArg Subtype.val (Set.mem_singleton_iff.mp heq)
            simp [hxu])⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    have hcongr := _root_.SimpleGraph.vertexCoverNum_congr e₁
    rw [hcongr] at hstep
    -- Apply `ih` to `R' = insert u R` and `W' = W.erase u`!
    let R' := insert u R
    let W' := W.erase u
    have hW'_card : W'.card = k := by
      rw [Finset.card_erase_of_mem huW, hcard]; omega
    have hdisj' : Disjoint R' W' := by
      rw [Finset.disjoint_insert_left]
      exact ⟨Finset.notMem_erase u W, hdisj.mono_right (Finset.erase_subset u W)⟩
    have hW' : ∀ x ∈ W', ∃ y : V, y ∉ R' ∧ G.Adj x y ∧
        (∀ w : V, w ∉ R' → G.Adj y w → w ≠ x → G.Adj x w) ∧
        (G.degree y < G.degree x ∨ (G.degree y = G.degree x ∧ x < y)) := by
      intro x hxW'
      have hxW : x ∈ W := Finset.mem_of_mem_erase hxW'
      obtain ⟨y, hyR, hxy, hydom, hyord⟩ := hW x hxW
      have hyu : y ≠ u := by
        intro heq
        subst heq
        have hdeg_le : G.degree x ≤ G.degree u :=
          hu_deg ▸ Finset.le_sup' (f := fun z => G.degree z) hxW
        rcases hyord with hlt | ⟨heq_deg, hlt_idx⟩
        · omega
        · have hu_le : u ≤ x :=
            Finset.min'_le Wmax x (Finset.mem_filter.mpr ⟨hxW, heq_deg.symm.trans hu_deg⟩)
          exact not_lt_of_ge hu_le hlt_idx
      refine ⟨y, ?_, hxy, fun w hw => hydom w (fun hwR => hw (Finset.mem_insert_of_mem hwR)), hyord⟩
      intro hyR'
      rcases Finset.mem_insert.mp hyR' with rfl | hR
      · exact hyu rfl
      · exact hyR hR
    have hih := ih R' W' hW'_card hdisj' hW'
    have hunion : R' ∪ W' = R ∪ W := by
      ext z
      simp only [R', W', Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
      by_cases hzu : z = u
      · subst hzu; simp [huW]
      · simp [hzu]
    rw [hunion] at hih
    rw [hstep, hih, hcard, hW'_card, ← add_assoc, add_comm (1 : ℕ∞) (k : ℕ∞)]
    norm_cast

end Dominance

/-! ### Balanced Separators in Bounded-Treewidth Graphs -/

/-- `S` separates `X₁` from `X₂` inside the induced subgraph `G[U]`: no vertex of `X₁ ∩ (U \ S)`
can reach a vertex of `X₂ ∩ (U \ S)` in `G[U \ S]`. -/
def SeparatesIn {V : Type*} (G : SimpleGraph V) (U X₁ X₂ S : Set V) : Prop :=
  ∀ u₁ (hu₁ : u₁ ∈ U \ S), u₁ ∈ X₁ → ∀ u₂ (hu₂ : u₂ ∈ U \ S), u₂ ∈ X₂ →
    ¬ (G.induce (U \ S)).Reachable ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩

/-! ### Part 1: Balanced Separator Lemma on Rooted Tree Decompositions -/

/-- Node `j` lies in the rooted subtree of `t` in `R` if repeated `R.parent` steps reach `t`. -/
private def inSubtree {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (R : G.RootedTreeDecomposition n) (t j : Fin (n + 1)) : Prop :=
  ∃ a : ℕ, R.parent^[a] j = t

private lemma inSubtree_zero {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (R : G.RootedTreeDecomposition n) (j : Fin (n + 1)) : inSubtree R 0 j := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    rcases eq_or_ne j 0 with rfl | hj
    · exact ⟨0, rfl⟩
    · obtain ⟨a, ha⟩ := ih (R.parent j) (R.parent_lt j hj)
      exact ⟨a + 1, by rwa [Function.iterate_succ_apply]⟩

private lemma inSubtree_split_of_ne {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (R : G.RootedTreeDecomposition n) {t j : Fin (n + 1)}
    (h : inSubtree R t j) (hne : j ≠ t) :
    ∃ c : Fin (n + 1), c ≠ 0 ∧ R.parent c = t ∧ inSubtree R c j := by
  classical
  let a := Nat.find h
  have ha : R.parent^[a] j = t := Nat.find_spec h
  have ha_pos : 0 < a := by
    by_contra h0
    have : a = 0 := by omega
    rw [this, Function.iterate_zero_apply] at ha
    exact hne ha
  let b := a - 1
  have hab : a = b + 1 := by omega
  let c := R.parent^[b] j
  have hpc : R.parent c = t := by
    calc R.parent c = R.parent^[b + 1] j := (Function.iterate_succ_apply' R.parent b j).symm
      _ = t := by rw [← hab, ha]
  have hct : c ≠ t := fun hct => Nat.find_min h (show b < a by omega) hct
  have hc0 : c ≠ 0 := by
    intro hc0
    have hp0 : R.parent c = 0 := hc0 ▸ R.parent_zero
    exact hct (hc0.trans (hp0.symm.trans hpc))
  exact ⟨c, hc0, hpc, b, rfl⟩

private lemma inSubtree_child_iff_top {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (R : G.RootedTreeDecomposition n) {t c s : Fin (n + 1)} {v : V}
    (hpc : R.parent c = t) (hvt : v ∉ R.bag t) (hvs : v ∈ R.bag s) :
    inSubtree R c s ↔ inSubtree R c (R.top v) := by
  obtain ⟨p, hp⟩ := R.exists_iterate_eq_top hvs
  constructor
  · rintro ⟨b, hb⟩
    rcases le_or_gt p b with hpb | hbp
    · refine ⟨b - p, ?_⟩
      rw [← hp, ← Function.iterate_add_apply, show b - p + p = b by omega, hb]
    · exfalso
      have hmem : v ∈ R.bag (R.parent^[b + 1] s) :=
        R.mem_bag_parent_iterate hvs hp (by omega)
      rw [Function.iterate_succ_apply', hb, hpc] at hmem
      exact hvt hmem
  · rintro ⟨a, ha⟩
    exact ⟨a + p, by rw [Function.iterate_add_apply, hp, ha]⟩

private lemma reachable_inSubtree_child_iff {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (R : G.RootedTreeDecomposition n) {t c : Fin (n + 1)} (hpc : R.parent c = t)
    {u w : {x : V // x ∉ R.bag t}}
    (hreach : (G.induce {x | x ∉ R.bag t}).Reachable u w) :
    inSubtree R c (R.top u.1) ↔ inSubtree R c (R.top w.1) := by
  obtain ⟨wlk⟩ := hreach
  induction wlk with
  | nil => exact Iff.rfl
  | @cons x y _ hxy _ ih =>
    obtain ⟨s, hxs, hys⟩ := R.exists_adj_mem_bag hxy
    exact ((inSubtree_child_iff_top R hpc x.2 hxs).symm.trans
      (inSubtree_child_iff_top R hpc y.2 hys)).trans ih

/-- **Balanced Separator Lemma on Rooted Tree Decompositions**:
for any rooted tree decomposition `R` of `G` and any finite vertex set `W`, there is a tree node
`t` such that every connected component of `G - R.bag t` contains at most `W.card / 2` vertices
of `W`. -/
theorem exists_balanced_bag {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (R : G.RootedTreeDecomposition n) (W : Finset V) :
    ∃ t : Fin (n + 1), ∀ u : {x : V // x ∉ R.bag t},
      (@Finset.filter V (fun w =>
        ∃ hw : w ∉ R.bag t, (G.induce {x | x ∉ R.bag t}).Reachable u ⟨w, hw⟩)
        (Classical.decPred _) W).card ≤
        W.card / 2 := by
  classical
  have hdesc : ∀ d : ℕ, ∀ t : Fin (n + 1), n - t.1 ≤ d →
      (W.filter fun w => w ∉ R.bag t ∧ ¬ inSubtree R t (R.top w)).card ≤ W.card / 2 →
      ∃ t' : Fin (n + 1), ∀ u : {x : V // x ∉ R.bag t'},
        (W.filter fun w =>
          ∃ hw : w ∉ R.bag t', (G.induce {x | x ∉ R.bag t'}).Reachable u ⟨w, hw⟩).card ≤
          W.card / 2 := by
    intro d
    induction d with
    | zero =>
      intro t htd hout
      refine ⟨t, fun u => ?_⟩
      have hno_child : ∀ c : Fin (n + 1), c ≠ 0 → R.parent c = t → False := by
        intro c hc hpc
        have hlt : t < c := hpc ▸ R.parent_lt c hc
        omega
      refine (Finset.card_le_card fun w hw => ?_).trans hout
      obtain ⟨hwW, hwt, hreach⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_filter.mpr ⟨hwW, hwt, fun hsub => ?_⟩
      have hne : R.top w ≠ t := fun heq => hwt (heq ▸ R.mem_bag_top w)
      obtain ⟨c, hc0, hpc, _⟩ := inSubtree_split_of_ne R hsub hne
      exact hno_child c hc0 hpc
    | succ d ih =>
      intro t htd hout
      by_cases hheavy : ∃ c : Fin (n + 1), c ≠ 0 ∧ R.parent c = t ∧
          W.card / 2 < (W.filter fun w => w ∉ R.bag t ∧ inSubtree R c (R.top w)).card
      · obtain ⟨c, hc0, hpc, hgt⟩ := hheavy
        have hlt : t < c := hpc ▸ R.parent_lt c hc0
        apply ih c (by omega)
        let A := W.filter fun w => w ∉ R.bag c ∧ ¬ inSubtree R c (R.top w)
        let B := W.filter fun w => w ∉ R.bag t ∧ inSubtree R c (R.top w)
        have hdisj : Disjoint A B := Finset.disjoint_left.mpr fun w hwA hwB =>
          (Finset.mem_filter.mp hwA).2.2 (Finset.mem_filter.mp hwB).2.2
        have hunion : A ∪ B ⊆ W :=
          Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have hcard := (Finset.card_union_of_disjoint hdisj).symm.trans_le
          (Finset.card_le_card hunion)
        have hB : W.card / 2 + 1 ≤ B.card := hgt
        change A.card ≤ W.card / 2
        omega
      · push Not at hheavy
        refine ⟨t, fun u => ?_⟩
        by_cases hsub : inSubtree R t (R.top u.1)
        · have hne : R.top u.1 ≠ t := fun heq => by
            have hm := R.mem_bag_top u.1; rw [heq] at hm; exact u.2 hm
          obtain ⟨c, hc0, hpc, huc⟩ := inSubtree_split_of_ne R hsub hne
          refine (Finset.card_le_card fun w hw => ?_).trans (hheavy c hc0 hpc)
          obtain ⟨hwW, hwt, hreach⟩ := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr
            ⟨hwW, hwt, (reachable_inSubtree_child_iff R hpc hreach).mp huc⟩
        · refine (Finset.card_le_card fun w hw => ?_).trans hout
          obtain ⟨hwW, hwt, hreach⟩ := Finset.mem_filter.mp hw
          refine Finset.mem_filter.mpr ⟨hwW, hwt, fun hwsub => ?_⟩
          have hne : R.top w ≠ t := fun heq => hwt (heq ▸ R.mem_bag_top w)
          obtain ⟨c, _, hpc, hwc⟩ := inSubtree_split_of_ne R hwsub hne
          have ⟨a, ha⟩ : inSubtree R c (R.top u.1) :=
            (reachable_inSubtree_child_iff R hpc hreach).mpr hwc
          exact hsub ⟨a + 1, by rw [Function.iterate_succ_apply', ha, hpc]⟩
  obtain ⟨t, ht⟩ := hdesc n 0 (by omega) (by
    have hempty : (W.filter fun w => w ∉ R.bag 0 ∧ ¬ inSubtree R 0 (R.top w)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun w _ h => h.2 (inSubtree_zero R (R.top w))
    simp [hempty])
  exact ⟨t, fun u => by convert ht u⟩

/-- Greedy weight-grouping lemma for three-way balanced partitions:
if nonnegative integer weights `wt i ≤ (3 k + 4) / 2` sum to at least `2 k + 3`, some subset sums
into `[k + 2, 2 k + 2]`.
-/
private lemma exists_subset_sum_between {ι : Type*} (s : Finset ι)
    (wt : ι → ℕ) (k : ℕ) (hmax : ∀ i ∈ s, wt i ≤ (3 * k + 4) / 2)
    (hsum : 2 * k + 3 ≤ ∑ i ∈ s, wt i) :
    ∃ P ⊆ s, k + 2 ≤ ∑ i ∈ P, wt i ∧ ∑ i ∈ P, wt i ≤ 2 * k + 2 := by
  classical
  by_cases hbig : ∃ i ∈ s, k + 2 ≤ wt i
  · obtain ⟨i, his, hge⟩ := hbig
    refine ⟨{i}, Finset.singleton_subset_iff.mpr his, by simpa using hge, ?_⟩
    have hle := hmax i his
    simp only [Finset.sum_singleton]
    omega
  · push Not at hbig
    have haux : ∀ t ⊆ s, ∑ i ∈ t, wt i ≤ k + 1 ∨
        ∃ P ⊆ t, k + 2 ≤ ∑ i ∈ P, wt i ∧ ∑ i ∈ P, wt i ≤ 2 * k + 2 := by
      intro t
      induction t using Finset.induction_on with
      | empty => intro _; exact Or.inl (by simp)
      | @insert a t hat ih =>
        intro hts
        have hts' : t ⊆ s := (Finset.subset_insert a t).trans hts
        rcases ih hts' with hsmall | ⟨P, hPt, hlo, hhi⟩
        · have ha : wt a < k + 2 := hbig a (hts (Finset.mem_insert_self a t))
          rw [Finset.sum_insert hat]
          rcases le_or_gt (wt a + ∑ i ∈ t, wt i) (k + 1) with hle | hgt
          · exact Or.inl hle
          · exact Or.inr ⟨insert a t, Finset.Subset.rfl,
              by rw [Finset.sum_insert hat]; omega,
              by rw [Finset.sum_insert hat]; omega⟩
        · exact Or.inr ⟨P, hPt.trans (Finset.subset_insert a t), hlo, hhi⟩
    rcases haux s Finset.Subset.rfl with hsmall | hfound
    · omega
    · exact hfound

/-- **Three-Way Balanced Separator Theorem**:
if `G` has treewidth at most `k` and `X ⊆ W` has cardinality `3 k + 4`, then `X` splits into
pairwise disjoint sets `(X₀, X₁, X₂)` with `|X₀| ≤ k + 1` and `1 ≤ |X₁|, |X₂| ≤ 2 k + 2`,
together with `S' ⊆ W \ X` of cardinality `|S'| ≤ k + 1 - |X₀|`, such that `X₀ ∪ S'` separates
`X₁` from `X₂` in `G[W]`.
-/
theorem exists_balanced_three_way_separator {V : Type*} [Finite V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ} (htw : G.treewidth ≤ k) {W X : Finset V}
    (hXW : X ⊆ W) (hXcard : X.card = 3 * k + 4) :
    ∃ X₀ X₁ X₂ S' : Finset V,
      Disjoint X₀ X₁ ∧ Disjoint X₀ X₂ ∧ Disjoint X₁ X₂ ∧
      X₀ ∪ X₁ ∪ X₂ = X ∧
      X₀.card ≤ k + 1 ∧
      1 ≤ X₁.card ∧ X₁.card ≤ 2 * k + 2 ∧
      1 ≤ X₂.card ∧ X₂.card ≤ 2 * k + 2 ∧
      S' ⊆ W \ X ∧ S'.card ≤ k + 1 - X₀.card ∧
      SeparatesIn G (W : Set V) (X₁ : Set V) (X₂ : Set V) ((X₀ ∪ S' : Finset V) : Set V) := by
  classical
  cases nonempty_fintype V
  obtain ⟨m, R, hRw⟩ := treewidth_le_iff_exists_rooted.mp htw
  obtain ⟨t, hbal⟩ := exists_balanced_bag R X
  have hbag_le : (R.bag t).card ≤ k + 1 := R.width_le_iff.mp hRw t
  let X₀ : Finset V := X ∩ R.bag t
  let S' : Finset V := (W ∩ R.bag t) \ X
  have hS'_sub : S' ⊆ W \ X :=
    Finset.sdiff_subset_sdiff Finset.inter_subset_left Finset.Subset.rfl
  have hdisj_X₀S' : Disjoint X₀ S' :=
    Finset.disjoint_left.mpr fun v hv0 hvs =>
      (Finset.mem_sdiff.mp hvs).2 (Finset.mem_inter.mp hv0).1
  have hunion_sep : X₀ ∪ S' = W ∩ R.bag t := by
    ext v
    simp only [X₀, S', Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨hvX, hvB⟩ | ⟨⟨hvW, hvB⟩, _⟩)
      · exact ⟨hXW hvX, hvB⟩
      · exact ⟨hvW, hvB⟩
    · rintro ⟨hvW, hvB⟩
      by_cases hvX : v ∈ X
      · exact Or.inl ⟨hvX, hvB⟩
      · exact Or.inr ⟨⟨hvW, hvB⟩, hvX⟩
  have hsum_sep : X₀.card + S'.card ≤ k + 1 := by
    rw [← Finset.card_union_of_disjoint hdisj_X₀S', hunion_sep]
    exact (Finset.card_le_card Finset.inter_subset_right).trans hbag_le
  have hX₀_le : X₀.card ≤ k + 1 := by omega
  have hS'_le : S'.card ≤ k + 1 - X₀.card := by omega
  let Uset : Set V := (W : Set V) \ ((X₀ ∪ S' : Finset V) : Set V)
  let H : SimpleGraph Uset := G.induce Uset
  have : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let Rrem : Finset V := X \ X₀
  have hRrem_card : Rrem.card = 3 * k + 4 - X₀.card := by
    rw [Finset.card_sdiff_of_subset Finset.inter_subset_left, hXcard]
  have hRrem_in_U : ∀ x ∈ Rrem, x ∈ Uset := by
    intro x hx
    obtain ⟨hxX, hx0⟩ := Finset.mem_sdiff.mp hx
    refine ⟨hXW hxX, ?_⟩
    rw [hunion_sep, Finset.mem_coe, Finset.mem_inter]
    exact fun ⟨_, hxB⟩ => hx0 (Finset.mem_inter.mpr ⟨hxX, hxB⟩)
  let compOf : (x : V) → x ∈ Rrem → H.ConnectedComponent :=
    fun x hx => H.connectedComponentMk ⟨x, hRrem_in_U x hx⟩
  let fiber : H.ConnectedComponent → Finset V :=
    fun C => Rrem.attach.filter (fun x => compOf x.1 x.2 = C) |>.map
      ⟨Subtype.val, Subtype.val_injective⟩
  have hmem_fiber : ∀ C x, x ∈ fiber C ↔ ∃ hx : x ∈ Rrem, compOf x hx = C := by
    intro C x
    simp only [fiber, Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
      Function.Embedding.coeFn_mk, Subtype.exists]
    constructor
    · rintro ⟨a, ha, hC, rfl⟩; exact ⟨ha, hC⟩
    · rintro ⟨hx, hC⟩; exact ⟨x, hx, hC, rfl⟩
  have hsum_wt : ∑ C : H.ConnectedComponent, (fiber C).card = Rrem.card := by
    have hpart : Finset.univ.biUnion fiber = Rrem := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hmem_fiber]
      exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨compOf x hx, hx, rfl⟩⟩
    have hpdisj : (↑(Finset.univ : Finset H.ConnectedComponent) : Set H.ConnectedComponent)
        |>.PairwiseDisjoint fiber := by
      intro C₁ _ C₂ _ hne
      refine Finset.disjoint_left.mpr fun x hx₁ hx₂ => hne ?_
      obtain ⟨h1, rfl⟩ := (hmem_fiber C₁ x).mp hx₁
      obtain ⟨_, h2⟩ := (hmem_fiber C₂ x).mp hx₂
      exact h2
    rw [← Finset.card_biUnion hpdisj, hpart]
  have hmax_wt : ∀ C ∈ (Finset.univ : Finset H.ConnectedComponent),
      (fiber C).card ≤ (3 * k + 4) / 2 := by
    intro C _
    rcases (fiber C).eq_empty_or_nonempty with hemp | ⟨u, hu⟩
    · simp [hemp]
    · obtain ⟨huR, huC⟩ := (hmem_fiber C u).mp hu
      have hu_notB : u ∉ R.bag t := fun huB =>
        (Finset.mem_sdiff.mp huR).2 (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp huR).1, huB⟩)
      rw [← hXcard]
      refine (Finset.card_le_card fun w hw => ?_).trans (hbal ⟨u, hu_notB⟩)
      obtain ⟨hwR, hwC⟩ := (hmem_fiber C w).mp hw
      have hwX : w ∈ X := (Finset.mem_sdiff.mp hwR).1
      have hw_notB : w ∉ R.bag t := fun hwB =>
        (Finset.mem_sdiff.mp hwR).2 (Finset.mem_inter.mpr ⟨hwX, hwB⟩)
      suffices hmem_w : w ∈ X ∧ ∃ hw : w ∉ R.bag t,
          (G.induce {x | x ∉ R.bag t}).Reachable ⟨u, hu_notB⟩ ⟨w, hw⟩ by
        simpa only [Finset.mem_filter] using hmem_w
      refine ⟨hwX, hw_notB, ?_⟩
      have hreachH : H.Reachable ⟨u, hRrem_in_U u huR⟩ ⟨w, hRrem_in_U w hwR⟩ :=
        ConnectedComponent.exact (huC.trans hwC.symm)
      let hom : H →g G.induce {x | x ∉ R.bag t} :=
        { toFun := fun z => ⟨z.1, fun hzB =>
            z.2.2 (by rw [hunion_sep]; exact Finset.mem_inter.mpr ⟨z.2.1, hzB⟩)⟩
          map_rel' := fun h => h }
      exact hreachH.map hom
  obtain ⟨P, _, hP_lo, hP_hi⟩ := exists_subset_sum_between Finset.univ (fun C => (fiber C).card) k
    hmax_wt (by rw [hsum_wt, hRrem_card]; omega)
  let X₁ : Finset V := P.biUnion fiber
  let X₂ : Finset V := Rrem \ X₁
  have hpdisjP : (P : Set H.ConnectedComponent).PairwiseDisjoint fiber := by
    intro C₁ _ C₂ _ hne
    refine Finset.disjoint_left.mpr fun x hx₁ hx₂ => hne ?_
    obtain ⟨_, rfl⟩ := (hmem_fiber C₁ x).mp hx₁
    obtain ⟨_, h2⟩ := (hmem_fiber C₂ x).mp hx₂
    exact h2
  have hX₁_sub : X₁ ⊆ Rrem := Finset.biUnion_subset.mpr fun C _ x hx =>
    ((hmem_fiber C x).mp hx).1
  have hX₁_card : X₁.card = ∑ C ∈ P, (fiber C).card := Finset.card_biUnion hpdisjP
  have hX₂_card : X₂.card = Rrem.card - X₁.card := Finset.card_sdiff_of_subset hX₁_sub
  have hdisj01 : Disjoint X₀ X₁ :=
    Finset.disjoint_left.mpr fun x hx0 hx1 => (Finset.mem_sdiff.mp (hX₁_sub hx1)).2 hx0
  have hdisj02 : Disjoint X₀ X₂ :=
    Finset.disjoint_left.mpr fun x hx0 hx2 =>
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx2).1).2 hx0
  have hdisj12 : Disjoint X₁ X₂ := Finset.disjoint_sdiff
  have hunionX : X₀ ∪ X₁ ∪ X₂ = X := by
    rw [Finset.union_assoc, Finset.union_sdiff_of_subset hX₁_sub,
      Finset.union_sdiff_of_subset Finset.inter_subset_left]
  refine ⟨X₀, X₁, X₂, S', hdisj01, hdisj02, hdisj12, hunionX, hX₀_le,
    by omega, by omega, by omega, by omega, hS'_sub, hS'_le, ?_⟩
  intro u₁ hu₁ hu₁X₁ u₂ hu₂ hu₂X₂ hreach
  have hu₁R : u₁ ∈ Rrem := hX₁_sub hu₁X₁
  have hu₂R : u₂ ∈ Rrem := (Finset.mem_sdiff.mp hu₂X₂).1
  obtain ⟨C, hCP, hu₁C⟩ := Finset.mem_biUnion.mp hu₁X₁
  obtain ⟨_, hCeq⟩ := (hmem_fiber C u₁).mp hu₁C
  have heqC : compOf u₂ hu₂R = C :=
    (ConnectedComponent.sound hreach).symm.trans hCeq
  have hu₂X₁ : u₂ ∈ X₁ := Finset.mem_biUnion.mpr ⟨C, hCP, (hmem_fiber C u₂).mpr ⟨hu₂R, heqC⟩⟩
  exact (Finset.mem_sdiff.mp hu₂X₂).2 hu₂X₁

end CslibFrontier.SimpleGraph

end
