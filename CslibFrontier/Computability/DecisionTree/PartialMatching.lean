module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.RelClasses

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Partial Matchings, Exact Matching Counts, and Matching Decision Trees

This module formalizes partial matchings `PMatching U` on a finite type `U`, exact counting of
`m`-edge matchings via descending factorials (`matchingCount`) and the extension-ratio bound
(`card_extensions_ratio`), together with matching decision trees `MTree U`, matching DNFs `MDNF U`,
restriction, negation, and DNF conversion (`toMDNF`).

## Main definitions

- `CslibFrontier.Computability.DecisionTree.edgeVerts`: the two-element vertex finset of an edge
  `e : Sym2 U`.
- `CslibFrontier.Computability.DecisionTree.PMatching`: partial matchings on `U` (disjoint
  non-diagonal edges), with `support`, `free`, `partner`, `Compatible`, `union`, `sdiff`, `addEdge`,
  `IsPerfect`, `extensions`, and `matchingsOn`.
- `CslibFrontier.Computability.DecisionTree.PMatching.matchingCount`: exact number of `m`-edge
  partial matchings on `r` vertices.
- `CslibFrontier.Computability.DecisionTree.MTree`,
  `CslibFrontier.Computability.DecisionTree.MDNF`: matching decision trees and matching
  DNFs over `U`, with `MTree.depth`, `MTree.eval`, `MTree.neg`, `MTree.imp`, `MTree.restrict`,
  `MTree.Forces`, `MTree.toMDNF`, and `MDNF.eval`.

## Main results

- `CslibFrontier.Computability.DecisionTree.PMatching.card_matchingsOn`,
  `CslibFrontier.Computability.DecisionTree.PMatching.matchingCount_mul`,
  `CslibFrontier.Computability.DecisionTree.PMatching.card_extensions_eq_matchingCount`,
  `CslibFrontier.Computability.DecisionTree.PMatching.matchingCount_ratio`,
  `CslibFrontier.Computability.DecisionTree.PMatching.card_extensions_ratio`,
  `CslibFrontier.Computability.DecisionTree.PMatching.extensions_nonempty`: exact counting,
  nonemptiness, and
  extension-ratio bounds for partial matchings.
- `CslibFrontier.Computability.DecisionTree.MTree.eval_restrict`,
  `CslibFrontier.Computability.DecisionTree.MTree.toMDNF_width`,
  `CslibFrontier.Computability.DecisionTree.MTree.toMDNF_eval`,
  `CslibFrontier.Computability.DecisionTree.MTree.Forces.mono`,
  `CslibFrontier.Computability.DecisionTree.MTree.Forces.not_both`,
  `CslibFrontier.Computability.DecisionTree.exists_extension_forcing_leaf`,
  `CslibFrontier.Computability.DecisionTree.eval_eq_of_restrict_depth_zero`: evaluation,
  width-preserving DNF
  conversion, partial-matching forcing, and single-tree forcing-to-leaf.
-/

public section

namespace CslibFrontier.Computability.DecisionTree

open scoped BigOperators

universe u

/-! ### 1. Edge Vertex Sets and Partial Matchings -/

/-- The finset of vertices incident to a symmetric pair `e : Sym2 U`. -/
@[expose] def edgeVerts {U : Type u} [DecidableEq U] (e : Sym2 U) : Finset U :=
  Quot.lift (fun p : U × U ↦ ({p.1, p.2} : Finset U))
    (fun _ _ h ↦ by cases h with | refl => rfl | swap => exact Finset.pair_comm _ _) e

@[simp, grind =] lemma edgeVerts_s {U : Type u} [DecidableEq U] (x y : U) :
    edgeVerts s(x, y) = {x, y} := rfl

@[simp, grind =] lemma mem_edgeVerts {U : Type u} [DecidableEq U] {x : U} {e : Sym2 U} :
    x ∈ edgeVerts e ↔ x ∈ e := by
  induction e using Sym2.ind with
  | _ a b => simp [edgeVerts_s, Sym2.mem_iff]

lemma card_edgeVerts_of_not_isDiag {U : Type u} [DecidableEq U] {e : Sym2 U} (he : ¬ e.IsDiag) :
    (edgeVerts e).card = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [edgeVerts_s, Finset.card_pair]
    intro h
    exact he (h ▸ Sym2.mk_isDiag_iff.mpr rfl)

private lemma exists_mem_sym2 {U : Type u} (e : Sym2 U) : ∃ x : U, x ∈ e := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩

/-- A partial matching on `U`: a finset of pairwise vertex-disjoint non-diagonal edges. -/
@[ext] structure PMatching (U : Type u) [DecidableEq U] where
  /-- The underlying finset of edges. -/
  edges : Finset (Sym2 U)
  /-- Every edge in the matching is non-diagonal (`a ≠ b`). -/
  nonDiag : ∀ e ∈ edges, ¬ e.IsDiag
  /-- Distinct edges share no vertex. -/
  disjoint : ∀ e₁ ∈ edges, ∀ e₂ ∈ edges, e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂

namespace PMatching

variable {U : Type u} [DecidableEq U]

instance instDecidableEq : DecidableEq (PMatching U) :=
  fun ρ σ ↦ decidable_of_iff (ρ.edges = σ.edges) PMatching.ext_iff.symm

instance instFintype [Fintype U] : Fintype (PMatching U) := by
  classical
  refine Fintype.ofEquiv
    { E : Finset (Sym2 U) // (∀ e ∈ E, ¬ e.IsDiag) ∧
        ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂ }
    { toFun := fun ⟨E, h₁, h₂⟩ ↦ ⟨E, h₁, h₂⟩
      invFun := fun ρ ↦ ⟨ρ.edges, ρ.nonDiag, ρ.disjoint⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

instance instPartialOrder : PartialOrder (PMatching U) where
  le ρ σ := ρ.edges ⊆ σ.edges
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm _ _ h₁ h₂ := PMatching.ext (Finset.Subset.antisymm h₁ h₂)

instance instDecidableLE : DecidableRel (· ≤ · : PMatching U → PMatching U → Prop) :=
  fun ρ σ ↦ inferInstanceAs (Decidable (ρ.edges ⊆ σ.edges))

instance instBot : Bot (PMatching U) :=
  ⟨⟨∅, fun _ h ↦ (Finset.notMem_empty _ h).elim,
    fun _ h ↦ (Finset.notMem_empty _ h).elim⟩⟩

@[simp, grind =] lemma bot_edges : (⊥ : PMatching U).edges = ∅ := rfl

lemma le_iff_edges_subset {ρ σ : PMatching U} : ρ ≤ σ ↔ ρ.edges ⊆ σ.edges := Iff.rfl

/-- The set of matched vertices of `ρ`. -/
@[expose] def support (ρ : PMatching U) : Finset U :=
  ρ.edges.biUnion edgeVerts

@[simp, grind =] lemma bot_support : (⊥ : PMatching U).support = ∅ := by
  simp [support]

lemma mem_support_iff {ρ : PMatching U} {x : U} :
    x ∈ ρ.support ↔ ∃ e ∈ ρ.edges, x ∈ e := by
  simp [support, mem_edgeVerts]

lemma support_mono {ρ σ : PMatching U} (h : ρ ≤ σ) : ρ.support ⊆ σ.support :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

lemma card_support (ρ : PMatching U) : ρ.support.card = 2 * ρ.edges.card := by
  rw [support, Finset.card_biUnion]
  · simp_rw [Finset.sum_congr rfl fun e he ↦ card_edgeVerts_of_not_isDiag (ρ.nonDiag e he)]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  · intro e₁ he₁ e₂ he₂ hne
    change Disjoint (edgeVerts e₁) (edgeVerts e₂)
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    exact ρ.disjoint e₁ he₁ e₂ he₂ hne x (mem_edgeVerts.mp hx₁) (mem_edgeVerts.mp hx₂)

/-- The set of unmatched (free) vertices of `ρ`. -/
@[expose] def free [Fintype U] (ρ : PMatching U) : Finset U :=
  Finset.univ \ ρ.support

lemma mem_free_iff [Fintype U] {ρ : PMatching U} {x : U} :
    x ∈ ρ.free ↔ x ∉ ρ.support := by
  simp [free]

lemma free_subset_free [Fintype U] {ρ σ : PMatching U} (h : ρ ≤ σ) :
    σ.free ⊆ ρ.free :=
  Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (support_mono h)

lemma card_free_add [Fintype U] (ρ : PMatching U) :
    ρ.free.card + 2 * ρ.edges.card = Fintype.card U := by
  rw [← ρ.card_support, free, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),
    Finset.card_univ]

lemma card_free_le [Fintype U] {ρ σ : PMatching U} (h : ρ ≤ σ) :
    σ.free.card ≤ ρ.free.card :=
  Finset.card_le_card (free_subset_free h)

/-- A partial matching is perfect if every vertex is matched. -/
def IsPerfect [Fintype U] (ρ : PMatching U) : Prop :=
  ρ.free = ∅

lemma isPerfect_iff [Fintype U] {ρ : PMatching U} :
    ρ.IsPerfect ↔ ∀ x : U, x ∈ ρ.support := by
  simp [IsPerfect, free, Finset.sdiff_eq_empty_iff_subset, Finset.subset_iff]

/-- The matched partner of `x` in `ρ`, or `none` if `x` is free. -/
noncomputable def partner (ρ : PMatching U) (x : U) : Option U := by
  classical
  exact if h : ∃ y, s(x, y) ∈ ρ.edges then some (Classical.choose h) else none

lemma partner_eq_some_iff {ρ : PMatching U} {x y : U} :
    ρ.partner x = some y ↔ s(x, y) ∈ ρ.edges := by
  classical
  unfold partner
  split_ifs with h
  · constructor
    · intro heq
      have hy : Classical.choose h = y := Option.some.inj heq
      exact hy ▸ Classical.choose_spec h
    · intro hmem
      congr 1
      have hc := Classical.choose_spec h
      by_contra hne
      have hne_e : s(x, Classical.choose h) ≠ s(x, y) := by
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨_, hcy⟩ | ⟨hxy, _⟩
        · exact hne hcy
        · exact ρ.nonDiag _ hmem (hxy ▸ Sym2.mk_isDiag_iff.mpr rfl)
      exact ρ.disjoint _ hc _ hmem hne_e x (Sym2.mem_mk_left x _) (Sym2.mem_mk_left x _)
  · exact ⟨(fun heq ↦ by cases heq), fun hmem ↦ (h ⟨y, hmem⟩).elim⟩

lemma partner_eq_none_iff {ρ : PMatching U} {x : U} :
    ρ.partner x = none ↔ x ∉ ρ.support := by
  classical
  constructor
  · intro hnone hsup
    rw [mem_support_iff] at hsup
    rcases hsup with ⟨e, he, hxe⟩
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
    have hsome := partner_eq_some_iff.mpr he
    rw [hnone] at hsome
    cases hsome
  · intro hnsup
    unfold partner
    have hnot : ¬ ∃ y, s(x, y) ∈ ρ.edges := by
      rintro ⟨y, hy⟩
      exact hnsup (mem_support_iff.mpr ⟨s(x, y), hy, Sym2.mem_mk_left x y⟩)
    simp only [hnot, ↓reduceDIte]

lemma partner_ne_self {ρ : PMatching U} {x y : U} (h : ρ.partner x = some y) : y ≠ x := by
  intro heq
  subst heq
  exact ρ.nonDiag _ (partner_eq_some_iff.mp h) (Sym2.mk_isDiag_iff.mpr rfl)

lemma partner_symm {ρ : PMatching U} {x y : U} (h : ρ.partner x = some y) :
    ρ.partner y = some x :=
  partner_eq_some_iff.mpr (by rw [Sym2.eq_swap]; exact partner_eq_some_iff.mp h)

lemma partner_eq_some_of_le {ρ σ : PMatching U} {x y : U} (h : ρ ≤ σ)
    (hp : ρ.partner x = some y) : σ.partner x = some y :=
  partner_eq_some_iff.mpr (h (partner_eq_some_iff.mp hp))

lemma exists_partner_of_isPerfect [Fintype U] {ρ : PMatching U} (hρ : ρ.IsPerfect) (x : U) :
    ∃ y, ρ.partner x = some y := by
  have hx : x ∈ ρ.support := isPerfect_iff.mp hρ x
  cases hp : ρ.partner x with
  | none => exact absurd hx (partner_eq_none_iff.mp hp)
  | some y => exact ⟨y, rfl⟩

/-- Two partial matchings are compatible if their edge union is a valid partial matching. -/
@[expose] def Compatible (ρ σ : PMatching U) : Prop :=
  ∀ e₁ ∈ ρ.edges, ∀ e₂ ∈ σ.edges, e₁ ≠ e₂ → ∀ x, x ∈ e₁ → x ∉ e₂

instance instDecidableCompatible : DecidableRel (Compatible (U := U)) := fun ρ σ ↦
  decidable_of_iff
    (∀ e₁ ∈ ρ.edges, ∀ e₂ ∈ σ.edges, e₁ ≠ e₂ → ∀ x ∈ edgeVerts e₁, x ∉ edgeVerts e₂)
    (by
      constructor
      · intro h e₁ he₁ e₂ he₂ hne x hx₁ hx₂
        exact h e₁ he₁ e₂ he₂ hne x (mem_edgeVerts.mpr hx₁) (mem_edgeVerts.mpr hx₂)
      · intro h e₁ he₁ e₂ he₂ hne x hx₁ hx₂
        exact h e₁ he₁ e₂ he₂ hne x (mem_edgeVerts.mp hx₁) (mem_edgeVerts.mp hx₂))

lemma compatible_symm {ρ σ : PMatching U} (h : ρ.Compatible σ) : σ.Compatible ρ :=
  fun e₁ he₁ e₂ he₂ hne x hx₁ hx₂ ↦ h e₂ he₂ e₁ he₁ hne.symm x hx₂ hx₁

lemma compatible_of_le {ρ σ : PMatching U} (h : ρ ≤ σ) : ρ.Compatible σ :=
  fun e₁ he₁ e₂ he₂ hne x hx₁ hx₂ ↦ σ.disjoint e₁ (h he₁) e₂ he₂ hne x hx₁ hx₂

lemma compatible_of_disjoint_support {ρ σ : PMatching U} (h : Disjoint ρ.support σ.support) :
    ρ.Compatible σ := by
  intro e₁ he₁ e₂ he₂ _ x hx₁ hx₂
  exact Finset.disjoint_left.mp h (mem_support_iff.mpr ⟨e₁, he₁, hx₁⟩)
    (mem_support_iff.mpr ⟨e₂, he₂, hx₂⟩)

lemma compatible_mono_right {ρ σ₁ σ₂ : PMatching U} (h : ρ.Compatible σ₂) (hle : σ₁ ≤ σ₂) :
    ρ.Compatible σ₁ :=
  fun e₁ he₁ e₂ he₂ hne x hx₁ hx₂ ↦ h e₁ he₁ e₂ (hle he₂) hne x hx₁ hx₂

/-- Union of two compatible partial matchings. -/
@[expose] def union (ρ σ : PMatching U) (h : ρ.Compatible σ) : PMatching U where
  edges := ρ.edges ∪ σ.edges
  nonDiag := fun e he ↦ by
    rcases Finset.mem_union.mp he with h₁ | h₂
    · exact ρ.nonDiag e h₁
    · exact σ.nonDiag e h₂
  disjoint := fun e₁ he₁ e₂ he₂ hne x hx₁ hx₂ ↦ by
    rcases Finset.mem_union.mp he₁ with h₁ | h₁ <;>
      rcases Finset.mem_union.mp he₂ with h₂ | h₂
    · exact ρ.disjoint e₁ h₁ e₂ h₂ hne x hx₁ hx₂
    · exact h e₁ h₁ e₂ h₂ hne x hx₁ hx₂
    · exact h e₂ h₂ e₁ h₁ hne.symm x hx₂ hx₁
    · exact σ.disjoint e₁ h₁ e₂ h₂ hne x hx₁ hx₂

@[simp, grind =] lemma union_edges (ρ σ : PMatching U) (h : ρ.Compatible σ) :
    (ρ.union σ h).edges = ρ.edges ∪ σ.edges := rfl

lemma le_union_left (ρ σ : PMatching U) (h : ρ.Compatible σ) : ρ ≤ ρ.union σ h :=
  Finset.subset_union_left

lemma le_union_right (ρ σ : PMatching U) (h : ρ.Compatible σ) : σ ≤ ρ.union σ h :=
  Finset.subset_union_right

lemma union_support (ρ σ : PMatching U) (h : ρ.Compatible σ) :
    (ρ.union σ h).support = ρ.support ∪ σ.support := by
  ext x
  simp only [support, union_edges, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨e, h1 | h2, hx⟩
    · exact Or.inl ⟨e, h1, hx⟩
    · exact Or.inr ⟨e, h2, hx⟩
  · rintro (⟨e, h1, hx⟩ | ⟨e, h2, hx⟩)
    · exact ⟨e, Or.inl h1, hx⟩
    · exact ⟨e, Or.inr h2, hx⟩

/-- Set difference `ρ \ σ` of partial matchings (removing edges of `σ` from `ρ`). -/
@[expose] def sdiff (ρ σ : PMatching U) : PMatching U where
  edges := ρ.edges \ σ.edges
  nonDiag := fun e he ↦ ρ.nonDiag e (Finset.mem_sdiff.mp he).1
  disjoint := fun e₁ he₁ e₂ he₂ ↦
    ρ.disjoint e₁ (Finset.mem_sdiff.mp he₁).1 e₂ (Finset.mem_sdiff.mp he₂).1

@[simp, grind =] lemma sdiff_edges (ρ σ : PMatching U) :
    (ρ.sdiff σ).edges = ρ.edges \ σ.edges := rfl

lemma sdiff_le (ρ σ : PMatching U) : ρ.sdiff σ ≤ ρ :=
  Finset.sdiff_subset

lemma disjoint_support_sdiff_of_le {ρ σ : PMatching U} (h : ρ ≤ σ) :
    Disjoint ρ.support (σ.sdiff ρ).support := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  rw [mem_support_iff] at hx₁ hx₂
  rcases hx₁ with ⟨e₁, he₁, hxe₁⟩
  rcases hx₂ with ⟨e₂, he₂, hxe₂⟩
  have he₂' := Finset.mem_sdiff.mp he₂
  have hne : e₁ ≠ e₂ := fun heq ↦ he₂'.2 (heq ▸ he₁)
  exact σ.disjoint e₁ (h he₁) e₂ he₂'.1 hne x hxe₁ hxe₂

lemma union_sdiff_of_le {ρ σ : PMatching U} (h : ρ ≤ σ) :
    ρ.union (σ.sdiff ρ) (compatible_of_disjoint_support (disjoint_support_sdiff_of_le h)) = σ := by
  ext e
  simp only [union_edges, sdiff_edges, Finset.mem_union, Finset.mem_sdiff]
  exact ⟨fun h₁ ↦ h₁.elim (fun he ↦ h he) And.left,
    fun he ↦ by by_cases hρ : e ∈ ρ.edges <;> simp [hρ, he]⟩

/-- Adds a single non-diagonal edge `s(x, y)` on free vertices `x, y` to `ρ`. -/
@[expose] def addEdge (ρ : PMatching U) (x y : U) (hxy : x ≠ y) (hx : x ∉ ρ.support)
    (hy : y ∉ ρ.support) : PMatching U where
  edges := insert s(x, y) ρ.edges
  nonDiag := fun e he ↦ by
    rcases Finset.mem_insert.mp he with rfl | he'
    · exact fun hd ↦ hxy (Sym2.mk_isDiag_iff.mp hd)
    · exact ρ.nonDiag e he'
  disjoint := fun e₁ he₁ e₂ he₂ hne z hz₁ hz₂ ↦ by
    rcases Finset.mem_insert.mp he₁ with rfl | h₁ <;>
      rcases Finset.mem_insert.mp he₂ with rfl | h₂
    · exact hne rfl
    · rcases Sym2.mem_iff.mp hz₁ with rfl | rfl
      · exact hx (mem_support_iff.mpr ⟨e₂, h₂, hz₂⟩)
      · exact hy (mem_support_iff.mpr ⟨e₂, h₂, hz₂⟩)
    · rcases Sym2.mem_iff.mp hz₂ with rfl | rfl
      · exact hx (mem_support_iff.mpr ⟨e₁, h₁, hz₁⟩)
      · exact hy (mem_support_iff.mpr ⟨e₁, h₁, hz₁⟩)
    · exact ρ.disjoint e₁ h₁ e₂ h₂ hne z hz₁ hz₂

@[simp, grind =] lemma addEdge_edges (ρ : PMatching U) (x y : U) (hxy : x ≠ y)
    (hx : x ∉ ρ.support) (hy : y ∉ ρ.support) :
    (ρ.addEdge x y hxy hx hy).edges = insert s(x, y) ρ.edges := rfl

lemma addEdge_support (ρ : PMatching U) (x y : U) (hxy : x ≠ y)
    (hx : x ∉ ρ.support) (hy : y ∉ ρ.support) :
    (ρ.addEdge x y hxy hx hy).support = insert x (insert y ρ.support) := by
  simp [support, addEdge_edges, Finset.biUnion_insert, edgeVerts_s]

lemma card_addEdge_edges (ρ : PMatching U) (x y : U) (hxy : x ≠ y)
    (hx : x ∉ ρ.support) (hy : y ∉ ρ.support) :
    (ρ.addEdge x y hxy hx hy).edges.card = ρ.edges.card + 1 := by
  rw [addEdge_edges, Finset.card_insert_of_notMem]
  intro hmem
  exact hx (mem_support_iff.mpr ⟨s(x, y), hmem, Sym2.mem_mk_left x y⟩)

lemma le_addEdge (ρ : PMatching U) (x y : U) (hxy : x ≠ y)
    (hx : x ∉ ρ.support) (hy : y ∉ ρ.support) :
    ρ ≤ ρ.addEdge x y hxy hx hy :=
  Finset.subset_insert _ _

/-- Partial matchings extending `ρ₀` with exactly `r'` free vertices. -/
def extensions [Fintype U] (ρ₀ : PMatching U) (r' : ℕ) : Finset (PMatching U) :=
  Finset.univ.filter fun ρ ↦ ρ₀ ≤ ρ ∧ ρ.free.card = r'

lemma mem_extensions_iff [Fintype U] {ρ₀ ρ : PMatching U} {r' : ℕ} :
    ρ ∈ ρ₀.extensions r' ↔ ρ₀ ≤ ρ ∧ ρ.free.card = r' := by
  simp [extensions]

/-- All `m`-edge partial matchings whose support is contained in `S`. -/
def matchingsOn [Fintype U] (S : Finset U) (m : ℕ) : Finset (PMatching U) :=
  Finset.univ.filter fun σ ↦ σ.support ⊆ S ∧ σ.edges.card = m

lemma mem_matchingsOn_iff [Fintype U] {S : Finset U} {m : ℕ} {σ : PMatching U} :
    σ ∈ matchingsOn S m ↔ σ.support ⊆ S ∧ σ.edges.card = m := by
  simp [matchingsOn]

/-! ### 2. Exact Counting of Partial Matchings and Extension Ratio -/

/-- Exact number of `m`-edge partial matchings on an `r`-element vertex set. -/
def matchingCount (r m : ℕ) : ℕ :=
  Nat.descFactorial r (2 * m) / (2 ^ m * m.factorial)

lemma card_matchingsOn_mul [Fintype U] (S : Finset U) (m : ℕ) :
    (matchingsOn S m).card * (2 ^ m * m.factorial) = Nat.descFactorial S.card (2 * m) := by
  induction m generalizing S with
  | zero =>
    have h1 : matchingsOn S 0 = {⊥} := by
      ext σ
      simp only [mem_matchingsOn_iff, Finset.mem_singleton, Finset.card_eq_zero]
      constructor
      · intro ⟨_, h0⟩; ext e; simp [h0]
      · rintro rfl; simp
    rw [h1, Finset.card_singleton]
    simp
  | succ m ih =>
    -- Double-count pairs `((x, y), σ)` with `x ∈ S`, `y ∈ S.erase x`, `σ ∈ matchingsOn (S\{x,y}) m`
    -- against `(σ', x, y)` with `σ' ∈ matchingsOn S (m + 1)` and `s(x, y) ∈ σ'.edges`.
    let A : Finset ((U × U) × PMatching U) :=
      (S.biUnion fun x ↦ (S.erase x).image fun y ↦ (x, y)).biUnion fun p ↦
        (matchingsOn ((S.erase p.1).erase p.2) m).image fun σ ↦ (p, σ)
    have hA_card : A.card * (2 ^ m * m.factorial) = Nat.descFactorial S.card (2 * (m + 1)) := by
      have hdisj1 : Set.PairwiseDisjoint (S : Set U)
          (fun x ↦ (S.erase x).image fun y ↦ (x, y)) := by
        intro x₁ _ x₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p hp₁ hp₂
        rcases Finset.mem_image.mp hp₁ with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hp₂ with ⟨_, _, heq⟩
        exact hne (Prod.mk.inj heq).1.symm
      have hdisj2 : Set.PairwiseDisjoint
          ((S.biUnion fun x ↦ (S.erase x).image fun y ↦ (x, y)) : Set (U × U))
          (fun p ↦ (matchingsOn ((S.erase p.1).erase p.2) m).image fun σ ↦ (p, σ)) := by
        intro p₁ _ p₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro q hq₁ hq₂
        rcases Finset.mem_image.mp hq₁ with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hq₂ with ⟨_, _, heq⟩
        exact hne (Prod.mk.inj heq).1.symm
      rw [Finset.card_biUnion hdisj2, Finset.sum_mul]
      have hterm : ∀ p ∈ S.biUnion (fun x ↦ (S.erase x).image fun y ↦ (x, y)),
          ((matchingsOn ((S.erase p.1).erase p.2) m).image fun σ ↦ (p, σ)).card *
              (2 ^ m * m.factorial) =
            Nat.descFactorial (S.card - 2) (2 * m) := by
        intro p hp
        rcases Finset.mem_biUnion.mp hp with ⟨x, hx, hpx⟩
        rcases Finset.mem_image.mp hpx with ⟨y, hy, rfl⟩
        rw [Finset.card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).2), ih]
        have hyS : y ∈ S := Finset.mem_of_mem_erase hy
        have hxy : y ≠ x := Finset.ne_of_mem_erase hy
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy, hyS⟩),
          Finset.card_erase_of_mem hx, show S.card - 1 - 1 = S.card - 2 by omega]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Finset.card_biUnion hdisj1]
      have hinner : ∀ x ∈ S, ((S.erase x).image fun y ↦ (x, y)).card = S.card - 1 := by
        intro x hx
        rw [Finset.card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).2),
          Finset.card_erase_of_mem hx]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
      have hdesc2 : S.card * (S.card - 1) * Nat.descFactorial (S.card - 2) (2 * m) =
          Nat.descFactorial S.card (2 * (m + 1)) := by
        have hstep : ∀ k : ℕ,
            Nat.descFactorial S.card (2 + k) =
              S.card * (S.card - 1) * Nat.descFactorial (S.card - 2) k := by
          intro k
          induction k with
          | zero => simp [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_comm]
          | succ k ihk =>
            rw [show 2 + (k + 1) = (2 + k) + 1 by omega, Nat.descFactorial_succ, ihk,
              Nat.descFactorial_succ]
            rw [show S.card - (2 + k) = S.card - 2 - k by omega]
            ring
        rw [show 2 * (m + 1) = 2 + 2 * m by omega, hstep]
      exact hdesc2
    -- Now partition `A` by the resulting `(m + 1)`-edge matching `σ' = σ.addEdge x y`.
    let f : ((U × U) × PMatching U) → PMatching U := fun q ↦
      if h : q.1.1 ≠ q.1.2 ∧ q.1.1 ∉ q.2.support ∧ q.1.2 ∉ q.2.support then
        q.2.addEdge q.1.1 q.1.2 h.1 h.2.1 h.2.2
      else ⊥
    have hA_fibers : A.card = (matchingsOn S (m + 1)).card * (2 * (m + 1)) := by
      have hmaps : ∀ q ∈ A, f q ∈ matchingsOn S (m + 1) := by
        intro q hq
        rcases Finset.mem_biUnion.mp hq with ⟨p, hp, hqp⟩
        rcases Finset.mem_image.mp hqp with ⟨σ, hσ, rfl⟩
        rcases Finset.mem_biUnion.mp hp with ⟨x, hx, hpx⟩
        rcases Finset.mem_image.mp hpx with ⟨y, hy, rfl⟩
        rcases mem_matchingsOn_iff.mp hσ with ⟨hsub, hcard⟩
        have hne : x ≠ y := (Finset.ne_of_mem_erase hy).symm
        have hxσ : x ∉ σ.support := fun h ↦
          (Finset.notMem_erase x _) (Finset.mem_of_mem_erase (hsub h))
        have hyσ : y ∉ σ.support := fun h ↦ (Finset.notMem_erase y _) (hsub h)
        have hcond : x ≠ y ∧ x ∉ σ.support ∧ y ∉ σ.support := ⟨hne, hxσ, hyσ⟩
        dsimp only [f]
        split_ifs
        rw [mem_matchingsOn_iff, addEdge_support, card_addEdge_edges, hcard]
        refine ⟨?_, rfl⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact hx
        · rcases Finset.mem_insert.mp hz' with rfl | hz''
          · exact Finset.mem_of_mem_erase hy
          · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hsub hz''))
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      have hfib : ∀ τ ∈ matchingsOn S (m + 1),
          (A.filter fun q ↦ f q = τ).card = 2 * (m + 1) := by
        intro τ hτ
        rcases mem_matchingsOn_iff.mp hτ with ⟨hτsub, hτcard⟩
        -- Bijection between `A.filter (f q = τ)` and ordered pairs `(x, y)` in `τ.edges`.
        let B : Finset (U × U) := τ.edges.biUnion fun e ↦
          (edgeVerts e).biUnion fun x ↦ ((edgeVerts e).erase x).image fun y ↦ (x, y)
        have hB_card : B.card = 2 * (m + 1) := by
          have hdisj : Set.PairwiseDisjoint (τ.edges : Set (Sym2 U))
              (fun e ↦ (edgeVerts e).biUnion fun x ↦
                ((edgeVerts e).erase x).image fun y ↦ (x, y)) := by
            intro e₁ he₁ e₂ he₂ hne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro p hp₁ hp₂
            rcases Finset.mem_biUnion.mp hp₁ with ⟨x, hx₁, hpx₁⟩
            rcases Finset.mem_image.mp hpx₁ with ⟨y, _, rfl⟩
            rcases Finset.mem_biUnion.mp hp₂ with ⟨x', hx₂, hpx₂⟩
            rcases Finset.mem_image.mp hpx₂ with ⟨y', _, heq⟩
            have hxx : x = x' := (Prod.mk.inj heq).1.symm
            subst hxx
            exact τ.disjoint e₁ he₁ e₂ he₂ hne x (mem_edgeVerts.mp hx₁) (mem_edgeVerts.mp hx₂)
          rw [Finset.card_biUnion hdisj]
          have heach : ∀ e ∈ τ.edges,
              ((edgeVerts e).biUnion fun x ↦
                ((edgeVerts e).erase x).image fun y ↦ (x, y)).card = 2 := by
            intro e he
            have hdisj_x : Set.PairwiseDisjoint (edgeVerts e : Set U)
                (fun x ↦ ((edgeVerts e).erase x).image fun y ↦ (x, y)) := by
              intro x₁ _ x₂ _ hne
              change Disjoint _ _
              rw [Finset.disjoint_left]
              intro p hp₁ hp₂
              rcases Finset.mem_image.mp hp₁ with ⟨_, _, rfl⟩
              rcases Finset.mem_image.mp hp₂ with ⟨_, _, heq⟩
              exact hne (Prod.mk.inj heq).1.symm
            rw [Finset.card_biUnion hdisj_x]
            have hcard_e := card_edgeVerts_of_not_isDiag (τ.nonDiag e he)
            have hinner : ∀ x ∈ edgeVerts e,
                (((edgeVerts e).erase x).image fun y ↦ (x, y)).card = 1 := by
              intro x hx
              rw [Finset.card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).2),
                Finset.card_erase_of_mem hx, hcard_e]
            rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, hcard_e, mul_one]
          rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul, hτcard, mul_comm]
        rw [← hB_card]
        refine Finset.card_bij (fun q _ ↦ q.1) ?_ ?_ ?_
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqA, hfq⟩
          rcases Finset.mem_biUnion.mp hqA with ⟨p, hp, hqp⟩
          rcases Finset.mem_image.mp hqp with ⟨σ, hσ, rfl⟩
          rcases Finset.mem_biUnion.mp hp with ⟨x, hx, hpx⟩
          rcases Finset.mem_image.mp hpx with ⟨y, hy, rfl⟩
          rcases mem_matchingsOn_iff.mp hσ with ⟨hsub, _⟩
          have hne : x ≠ y := (Finset.ne_of_mem_erase hy).symm
          have hxσ : x ∉ σ.support := fun h ↦
            (Finset.notMem_erase x _) (Finset.mem_of_mem_erase (hsub h))
          have hyσ : y ∉ σ.support := fun h ↦ (Finset.notMem_erase y _) (hsub h)
          have hcond : x ≠ y ∧ x ∉ σ.support ∧ y ∉ σ.support := ⟨hne, hxσ, hyσ⟩
          dsimp only [f] at hfq
          split_ifs at hfq
          have hmem : s(x, y) ∈ τ.edges := by
            rw [← hfq]; exact Finset.mem_insert_self _ _
          exact Finset.mem_biUnion.mpr ⟨s(x, y), hmem,
            Finset.mem_biUnion.mpr ⟨x, by simp [edgeVerts_s],
              Finset.mem_image.mpr
                ⟨y, Finset.mem_erase.mpr ⟨hne.symm, by simp [edgeVerts_s]⟩, rfl⟩⟩⟩
        · intro q₁ hq₁ q₂ hq₂ heq
          rcases Finset.mem_filter.mp hq₁ with ⟨hq₁A, hfq₁⟩
          rcases Finset.mem_filter.mp hq₂ with ⟨hq₂A, hfq₂⟩
          rcases Finset.mem_biUnion.mp hq₁A with ⟨p₁, hp₁, hqp₁⟩
          rcases Finset.mem_image.mp hqp₁ with ⟨σ₁, hσ₁, rfl⟩
          rcases Finset.mem_biUnion.mp hq₂A with ⟨p₂, hp₂, hqp₂⟩
          rcases Finset.mem_image.mp hqp₂ with ⟨σ₂, hσ₂, rfl⟩
          dsimp only at heq
          subst heq
          rcases Finset.mem_biUnion.mp hp₁ with ⟨x, _, hpx⟩
          rcases Finset.mem_image.mp hpx with ⟨y, hy, rfl⟩
          have hne : x ≠ y := (Finset.ne_of_mem_erase hy).symm
          have hx₁ : x ∉ σ₁.support := fun h ↦
            (Finset.notMem_erase x _) (Finset.mem_of_mem_erase ((mem_matchingsOn_iff.mp hσ₁).1 h))
          have hy₁ : y ∉ σ₁.support := fun h ↦
            (Finset.notMem_erase y _) ((mem_matchingsOn_iff.mp hσ₁).1 h)
          have hx₂ : x ∉ σ₂.support := fun h ↦
            (Finset.notMem_erase x _) (Finset.mem_of_mem_erase ((mem_matchingsOn_iff.mp hσ₂).1 h))
          have hy₂ : y ∉ σ₂.support := fun h ↦
            (Finset.notMem_erase y _) ((mem_matchingsOn_iff.mp hσ₂).1 h)
          have hc1 : x ≠ y ∧ x ∉ σ₁.support ∧ y ∉ σ₁.support := ⟨hne, hx₁, hy₁⟩
          have hc2 : x ≠ y ∧ x ∉ σ₂.support ∧ y ∉ σ₂.support := ⟨hne, hx₂, hy₂⟩
          dsimp only [f] at hfq₁ hfq₂
          split_ifs at hfq₁ hfq₂
          have h12 : σ₁.addEdge x y hne hx₁ hy₁ = σ₂.addEdge x y hne hx₂ hy₂ :=
            hfq₁.trans hfq₂.symm
          have hσeq : σ₁ = σ₂ := by
            ext e
            have hm1 : s(x, y) ∉ σ₁.edges := fun hm ↦
              hx₁ (mem_support_iff.mpr ⟨_, hm, Sym2.mem_mk_left x y⟩)
            have hm2 : s(x, y) ∉ σ₂.edges := fun hm ↦
              hx₂ (mem_support_iff.mpr ⟨_, hm, Sym2.mem_mk_left x y⟩)
            have heq_e := congrArg PMatching.edges h12
            simp only [addEdge_edges] at heq_e
            have := Finset.ext_iff.mp heq_e e
            by_cases hes : e = s(x, y)
            · subst hes; simp [hm1, hm2]
            · simpa [Finset.mem_insert, hes] using this
          subst hσeq; rfl
        · intro p hpB
          rcases Finset.mem_biUnion.mp hpB with ⟨e, he, hpe⟩
          rcases Finset.mem_biUnion.mp hpe with ⟨x, hx, hpx⟩
          rcases Finset.mem_image.mp hpx with ⟨y, hy, rfl⟩
          have hne : x ≠ y := (Finset.ne_of_mem_erase hy).symm
          have he_eq : e = s(x, y) := by
            induction e using Sym2.ind with
            | _ a b =>
              have hx' : x = a ∨ x = b := by simpa [edgeVerts_s] using hx
              have hy' : y = a ∨ y = b := by
                simpa [edgeVerts_s] using (Finset.mem_of_mem_erase hy)
              rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
              · exact (hne rfl).elim
              · rfl
              · exact Sym2.eq_swap
              · exact (hne rfl).elim
          subst he_eq
          let σ : PMatching U :=
            ⟨τ.edges.erase s(x, y),
              fun e' he' ↦ τ.nonDiag e' (Finset.mem_of_mem_erase he'),
              fun e₁ he₁ e₂ he₂ ↦
                τ.disjoint e₁ (Finset.mem_of_mem_erase he₁) e₂ (Finset.mem_of_mem_erase he₂)⟩
          have hxσ : x ∉ σ.support := by
            intro hsup
            rcases mem_support_iff.mp hsup with ⟨e', he', hxe'⟩
            exact τ.disjoint s(x, y) he e' (Finset.mem_of_mem_erase he')
              (Finset.ne_of_mem_erase he').symm x (Sym2.mem_mk_left x y) hxe'
          have hyσ : y ∉ σ.support := by
            intro hsup
            rcases mem_support_iff.mp hsup with ⟨e', he', hye'⟩
            exact τ.disjoint s(x, y) he e' (Finset.mem_of_mem_erase he')
              (Finset.ne_of_mem_erase he').symm y (Sym2.mem_mk_right x y) hye'
          have hσ_mem : σ ∈ matchingsOn ((S.erase x).erase y) m := by
            rw [mem_matchingsOn_iff]
            refine ⟨?_, ?_⟩
            · intro z hz
              have hzS : z ∈ S := hτsub (support_mono (Finset.erase_subset _ _) hz)
              refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hzS⟩⟩
              · rintro rfl; exact hyσ hz
              · rintro rfl; exact hxσ hz
            · change (τ.edges.erase s(x, y)).card = m
              rw [Finset.card_erase_of_mem he, hτcard, Nat.add_sub_cancel]
          have hxS : x ∈ S := hτsub (mem_support_iff.mpr ⟨s(x, y), he, Sym2.mem_mk_left x y⟩)
          have hyS : y ∈ S := hτsub (mem_support_iff.mpr ⟨s(x, y), he, Sym2.mem_mk_right x y⟩)
          refine ⟨((x, y), σ), Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
          · exact Finset.mem_biUnion.mpr ⟨(x, y),
              Finset.mem_biUnion.mpr ⟨x, hxS,
                Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨hne.symm, hyS⟩, rfl⟩⟩,
              Finset.mem_image.mpr ⟨σ, hσ_mem, rfl⟩⟩
          · have hc : x ≠ y ∧ x ∉ σ.support ∧ y ∉ σ.support := ⟨hne, hxσ, hyσ⟩
            dsimp only [f]
            split_ifs
            ext e'
            simp [σ, Finset.insert_erase he]
      rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
    calc (matchingsOn S (m + 1)).card * (2 ^ (m + 1) * (m + 1).factorial)
        = (matchingsOn S (m + 1)).card * (2 * (m + 1)) * (2 ^ m * m.factorial) := by
            rw [pow_succ, Nat.factorial_succ]; ring
      _ = A.card * (2 ^ m * m.factorial) := by rw [hA_fibers]
      _ = Nat.descFactorial S.card (2 * (m + 1)) := hA_card

lemma matchingCount_mul (r m : ℕ) :
    matchingCount r m * (2 ^ m * m.factorial) = Nat.descFactorial r (2 * m) := by
  have h := card_matchingsOn_mul (Finset.univ : Finset (Fin r)) m
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hdvd : 2 ^ m * m.factorial ∣ Nat.descFactorial r (2 * m) :=
    ⟨(matchingsOn (Finset.univ : Finset (Fin r)) m).card,
      by rw [mul_comm (2 ^ m * m.factorial)]; exact h.symm⟩
  exact Nat.div_mul_cancel hdvd

lemma card_matchingsOn [Fintype U] (S : Finset U) (m : ℕ) :
    (matchingsOn S m).card = matchingCount S.card m := by
  have hpos : 0 < 2 ^ m * m.factorial := Nat.mul_pos (pow_pos (by omega) m) (Nat.factorial_pos m)
  exact Nat.eq_of_mul_eq_mul_right hpos
    ((card_matchingsOn_mul S m).trans (matchingCount_mul _ m).symm)

lemma card_extensions_eq_matchingCount [Fintype U] (ρ₀ : PMatching U) {r' m : ℕ}
    (hm : r' + 2 * m = ρ₀.free.card) :
    (ρ₀.extensions r').card = matchingCount ρ₀.free.card m := by
  rw [← card_matchingsOn ρ₀.free m]
  refine Finset.card_bij (fun ρ _ ↦ ρ.sdiff ρ₀) ?_ ?_ ?_
  · intro ρ hρ
    rcases mem_extensions_iff.mp hρ with ⟨hle, hfree⟩
    rw [mem_matchingsOn_iff]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [mem_free_iff]
      exact Finset.disjoint_right.mp (disjoint_support_sdiff_of_le hle) hx
    · have hcard_ρ := ρ.card_free_add
      have hcard_ρ₀ := ρ₀.card_free_add
      have hsub_card : (ρ.sdiff ρ₀).edges.card + ρ₀.edges.card = ρ.edges.card := by
        rw [sdiff_edges, Finset.card_sdiff_add_card_eq_card hle]
      omega
  · intro ρ₁ hρ₁ ρ₂ hρ₂ heq
    have h₁ := (mem_extensions_iff.mp hρ₁).1
    have h₂ := (mem_extensions_iff.mp hρ₂).1
    have hu₁ := union_sdiff_of_le h₁
    have hu₂ := union_sdiff_of_le h₂
    rw [← hu₁, ← hu₂]
    ext e
    simp [union_edges, heq]
  · intro σ hσ
    rcases mem_matchingsOn_iff.mp hσ with ⟨hsub, hcard⟩
    have hdisj : Disjoint ρ₀.support σ.support := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      exact (mem_free_iff.mp (hsub hx₂)) hx₁
    let ρ := ρ₀.union σ (compatible_of_disjoint_support hdisj)
    refine ⟨ρ, mem_extensions_iff.mpr ⟨le_union_left _ _ _, ?_⟩, ?_⟩
    · have h1 := ρ.card_free_add
      have h2 := ρ₀.card_free_add
      have he : ρ.edges.card = ρ₀.edges.card + σ.edges.card := by
        rw [union_edges, Finset.card_union_of_disjoint]
        rw [Finset.disjoint_left]
        intro e he₁ he₂
        obtain ⟨x, hx⟩ := exists_mem_sym2 e
        exact Finset.disjoint_left.mp hdisj (mem_support_iff.mpr ⟨e, he₁, hx⟩)
          (mem_support_iff.mpr ⟨e, he₂, hx⟩)
      omega
    · ext e
      simp only [ρ, sdiff_edges, union_edges, Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h₁ | h₂, hnot⟩
        · exact absurd h₁ hnot
        · exact h₂
      · intro he
        refine ⟨Or.inr he, fun h₁ ↦ ?_⟩
        obtain ⟨x, hx⟩ := exists_mem_sym2 e
        exact Finset.disjoint_left.mp hdisj (mem_support_iff.mpr ⟨e, h₁, hx⟩)
          (mem_support_iff.mpr ⟨e, he, hx⟩)

private lemma descFactorial_add (r a b : ℕ) :
    Nat.descFactorial r (a + b) = Nat.descFactorial r a * Nat.descFactorial (r - a) b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, Nat.descFactorial_succ, ih, Nat.descFactorial_succ,
      show r - a - b = r - (a + b) by omega]
    ring

lemma matchingCount_ratio (r m s : ℕ) :
    matchingCount r (m + s) * (2 * m) ^ s ≤ matchingCount r m * (r - 2 * m) ^ (2 * s) := by
  have hpos : 0 < 2 ^ (m + s) * (m + s).factorial :=
    Nat.mul_pos (pow_pos (by omega) _) (Nat.factorial_pos _)
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  have hL : matchingCount r (m + s) * (2 * m) ^ s * (2 ^ (m + s) * (m + s).factorial) =
      Nat.descFactorial r (2 * (m + s)) * (2 * m) ^ s := by
    calc matchingCount r (m + s) * (2 * m) ^ s * (2 ^ (m + s) * (m + s).factorial)
        = matchingCount r (m + s) * (2 ^ (m + s) * (m + s).factorial) * (2 * m) ^ s := by ring
      _ = Nat.descFactorial r (2 * (m + s)) * (2 * m) ^ s := by rw [matchingCount_mul]
  have hfac_pow : m ^ s * m.factorial ≤ (m + s).factorial := by
    clear hpos hL
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ, show m + (s + 1) = (m + s) + 1 by omega, Nat.factorial_succ]
      calc m ^ s * m * m.factorial = m * (m ^ s * m.factorial) := by ring
        _ ≤ (m + s + 1) * (m + s).factorial :=
          Nat.mul_le_mul (by omega) ih
  have hdesc_split : Nat.descFactorial r (2 * (m + s)) =
      Nat.descFactorial r (2 * m) * Nat.descFactorial (r - 2 * m) (2 * s) := by
    rw [show 2 * (m + s) = 2 * m + 2 * s by omega]
    exact descFactorial_add r (2 * m) (2 * s)
  have hdesc_le : Nat.descFactorial (r - 2 * m) (2 * s) ≤ (r - 2 * m) ^ (2 * s) :=
    Nat.descFactorial_le_pow (r - 2 * m) (2 * s)
  rw [hL, hdesc_split]
  calc Nat.descFactorial r (2 * m) * Nat.descFactorial (r - 2 * m) (2 * s) * (2 * m) ^ s
      ≤ Nat.descFactorial r (2 * m) * (r - 2 * m) ^ (2 * s) * (2 ^ s * m ^ s) := by
        rw [mul_pow]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdesc_le)
    _ = matchingCount r m * (r - 2 * m) ^ (2 * s) * (2 ^ (m + s) * (m ^ s * m.factorial)) := by
        rw [← matchingCount_mul, pow_add]; ring
    _ ≤ matchingCount r m * (r - 2 * m) ^ (2 * s) * (2 ^ (m + s) * (m + s).factorial) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfac_pow)

lemma card_extensions_ratio [Fintype U] (ρ₀ : PMatching U) {r' s : ℕ}
    (hr' : 2 * s ≤ r') (hr'le : r' ≤ ρ₀.free.card) (heven : Even (ρ₀.free.card - r')) :
    (ρ₀.extensions (r' - 2 * s)).card * (ρ₀.free.card - r') ^ s ≤
      (ρ₀.extensions r').card * r' ^ (2 * s) := by
  rcases heven with ⟨m, hm⟩
  have h1 : r' + 2 * m = ρ₀.free.card := by omega
  have h2 : (r' - 2 * s) + 2 * (m + s) = ρ₀.free.card := by omega
  rw [card_extensions_eq_matchingCount ρ₀ h2, card_extensions_eq_matchingCount ρ₀ h1]
  have h := matchingCount_ratio ρ₀.free.card m s
  have hsub : ρ₀.free.card - 2 * m = r' := by omega
  have hsub2 : ρ₀.free.card - r' = 2 * m := by omega
  rw [hsub] at h
  rw [hsub2]
  exact h

lemma extensions_nonempty [Fintype U] (ρ₀ : PMatching U) {r' : ℕ}
    (hr'le : r' ≤ ρ₀.free.card) (heven : Even (ρ₀.free.card - r')) :
    (ρ₀.extensions r').Nonempty := by
  rcases heven with ⟨m, hm⟩
  have h1 : r' + 2 * m = ρ₀.free.card := by omega
  rw [← Finset.card_pos, card_extensions_eq_matchingCount ρ₀ h1]
  have hpos : 0 < 2 ^ m * m.factorial := Nat.mul_pos (pow_pos (by omega) _) (Nat.factorial_pos _)
  have hdesc : 0 < Nat.descFactorial ρ₀.free.card (2 * m) :=
    Nat.descFactorial_pos.mpr (by omega)
  have hmul := matchingCount_mul ρ₀.free.card m
  by_contra h0
  simp only [not_lt, Nat.le_zero] at h0
  rw [h0, zero_mul] at hmul
  omega

end PMatching

/-! ### 3. Matching Decision Trees and Matching DNFs -/

/-- A matching decision tree over `U`: queries vertices and branches on their matched partner. -/
inductive MTree (U : Type u) : Type u
  | leaf (b : Bool) : MTree U
  | query (u : U) (child : U → MTree U) : MTree U

/-- A matching DNF: a list of partial matchings (terms), satisfied if some term is `≤ σ`.
-/
abbrev MDNF (U : Type u) [DecidableEq U] := List (PMatching U)

namespace MTree

variable {U : Type u}

/-- Query depth of a matching decision tree. -/
@[expose] def depth [Fintype U] : MTree U → ℕ
  | .leaf _ => 0
  | .query _ child => 1 + Finset.univ.sup (fun v ↦ (child v).depth)

/-- Evaluates a matching decision tree on a partial matching `σ`. -/
noncomputable def eval [DecidableEq U] : MTree U → PMatching U → Bool
  | .leaf b, _ => b
  | .query u child, σ =>
      match σ.partner u with
      | some v => (child v).eval σ
      | none => false

/-- Negates every leaf of a matching decision tree. -/
@[expose] def neg : MTree U → MTree U
  | .leaf b => .leaf (!b)
  | .query u child => .query u (fun v ↦ (child v).neg)

@[simp, grind =] lemma depth_leaf [Fintype U] (b : Bool) : (leaf b : MTree U).depth = 0 := rfl

@[simp, grind =] lemma depth_query [Fintype U] (u : U) (child : U → MTree U) :
    (query u child).depth = 1 + Finset.univ.sup (fun v ↦ (child v).depth) := rfl

@[simp, grind =] lemma eval_leaf [DecidableEq U] (b : Bool) (σ : PMatching U) :
    (leaf b).eval σ = b := by
  rfl

@[simp, grind =] lemma eval_query [DecidableEq U] (u : U) (child : U → MTree U) (σ : PMatching U) :
    (query u child).eval σ =
      match σ.partner u with
      | some v => (child v).eval σ
      | none => false := by
  cases h : σ.partner u <;> simp [eval, h]

lemma depth_neg [Fintype U] (T : MTree U) : T.neg.depth = T.depth := by
  induction T with
  | leaf _ => rfl
  | query u child ih =>
    simp only [neg, depth]
    congr 1
    exact Finset.sup_congr rfl fun v _ ↦ ih v

lemma eval_neg [DecidableEq U] (T : MTree U) {σ : PMatching U} [Fintype U]
    (hσ : σ.IsPerfect) : T.neg.eval σ = !T.eval σ := by
  induction T with
  | leaf _ => simp [neg]
  | query u child ih =>
    obtain ⟨v, hv⟩ := PMatching.exists_partner_of_isPerfect hσ u
    simp [neg, hv, ih]

/-- Restricts a matching decision tree along a partial matching `ρ` by collapsing queries whose
vertex is already matched in `ρ`. -/
noncomputable def restrict [DecidableEq U] (ρ : PMatching U) : MTree U → MTree U
  | .leaf b => .leaf b
  | .query u child =>
      match ρ.partner u with
      | some v => (child v).restrict ρ
      | none => .query u (fun v ↦ (child v).restrict ρ)

@[simp, grind =] lemma restrict_leaf [DecidableEq U] (ρ : PMatching U) (b : Bool) :
    (leaf b).restrict ρ = leaf b := by
  rfl

@[simp, grind =] lemma restrict_query [DecidableEq U] (ρ : PMatching U) (u : U)
    (child : U → MTree U) :
    (query u child).restrict ρ =
      match ρ.partner u with
      | some v => (child v).restrict ρ
      | none => query u (fun v ↦ (child v).restrict ρ) := by
  cases h : ρ.partner u <;> simp [restrict, h]

lemma depth_restrict_le [Fintype U] [DecidableEq U] (ρ : PMatching U) (T : MTree U) :
    (T.restrict ρ).depth ≤ T.depth := by
  induction T with
  | leaf _ => exact le_rfl
  | query u child ih =>
    simp only [restrict_query]
    cases hp : ρ.partner u with
    | some v =>
      calc ((child v).restrict ρ).depth ≤ (child v).depth := ih v
        _ ≤ Finset.univ.sup (fun w ↦ (child w).depth) :=
          Finset.le_sup (f := fun w ↦ (child w).depth) (Finset.mem_univ v)
        _ ≤ 1 + Finset.univ.sup (fun w ↦ (child w).depth) := Nat.le_add_left _ _
    | none =>
      simp only [depth]
      exact Nat.add_le_add_left (Finset.sup_mono_fun fun v _ ↦ ih v) 1

lemma eval_restrict [DecidableEq U] (ρ : PMatching U) (T : MTree U) {σ : PMatching U}
    (h : ρ ≤ σ) : (T.restrict ρ).eval σ = T.eval σ := by
  induction T with
  | leaf _ => simp
  | query u child ih =>
    simp only [restrict_query]
    cases hp : ρ.partner u with
    | some v =>
      have hσv : σ.partner u = some v := PMatching.partner_eq_some_of_le h hp
      simp [hσv, ih v]
    | none =>
      simp only [eval_query]
      cases σ.partner u with
      | some v => exact ih v
      | none => rfl

/-- Helper converting a matching decision tree to a matching DNF starting from branch matching `π`.
-/
noncomputable def toMDNFAux [Fintype U] [DecidableEq U] (π : PMatching U) : MTree U → MDNF U
  | .leaf true => [π]
  | .leaf false => []
  | .query u child =>
      if h : ∃ v, s(u, v) ∈ π.edges then
        toMDNFAux π (child (Classical.choose h))
      else
        (Finset.univ.filter fun v ↦ v ≠ u ∧ v ∉ π.support).toList.flatMap fun v ↦
          if hv : v ≠ u ∧ v ∉ π.support then
            toMDNFAux (π.addEdge u v hv.1.symm (by
              intro hu
              rcases PMatching.mem_support_iff.mp hu with ⟨e, he, hue⟩
              obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hue
              exact h ⟨w, he⟩) hv.2) (child v)
          else []

/-- Converts a matching decision tree into an equivalent matching DNF of width at most `T.depth`.
-/
noncomputable def toMDNF [Fintype U] [DecidableEq U] (T : MTree U) : MDNF U :=
  toMDNFAux ⊥ T

private lemma le_of_mem_toMDNFAux [Fintype U] [DecidableEq U] (T : MTree U) (π : PMatching U) :
    ∀ C ∈ toMDNFAux π T, π ≤ C := by
  induction T generalizing π with
  | leaf b =>
    cases b <;> simp [toMDNFAux]
  | query u child ih =>
    intro C hC
    simp only [toMDNFAux] at hC
    split_ifs at hC with h
    · exact ih (Classical.choose h) π C hC
    · simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
        true_and] at hC
      rcases hC with ⟨v, hv, hCv⟩
      split_ifs at hCv
      exact le_trans (PMatching.le_addEdge _ _ _ _ _ _) (ih v _ C hCv)

lemma toMDNFAux_width [Fintype U] [DecidableEq U] (π : PMatching U) (T : MTree U) :
    ∀ C ∈ toMDNFAux π T, C.edges.card ≤ π.edges.card + T.depth := by
  induction T generalizing π with
  | leaf b =>
    cases b <;> simp [toMDNFAux]
  | query u child ih =>
    intro C hC
    simp only [toMDNFAux] at hC
    split_ifs at hC with h
    · have hle := ih (Classical.choose h) π C hC
      have hs : (child (Classical.choose h)).depth ≤ Finset.univ.sup (fun v ↦ (child v).depth) :=
        Finset.le_sup (f := fun v ↦ (child v).depth) (Finset.mem_univ _)
      simp only [depth]; omega
    · simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
        true_and] at hC
      rcases hC with ⟨v, hv, hCv⟩
      split_ifs at hCv
      have hle := ih v _ C hCv
      rw [PMatching.card_addEdge_edges] at hle
      have hs : (child v).depth ≤ Finset.univ.sup (fun w ↦ (child w).depth) :=
        Finset.le_sup (f := fun w ↦ (child w).depth) (Finset.mem_univ v)
      simp only [depth]; omega

lemma toMDNF_width [Fintype U] [DecidableEq U] (T : MTree U) :
    ∀ C ∈ T.toMDNF, C.edges.card ≤ T.depth := by
  intro C hC
  simpa using toMDNFAux_width ⊥ T C hC

lemma toMDNFAux_eval [Fintype U] [DecidableEq U] (π : PMatching U) (T : MTree U)
    {σ : PMatching U} (hπ : π ≤ σ) (hσ : σ.IsPerfect) :
    T.eval σ = true ↔ ∃ C ∈ toMDNFAux π T, C ≤ σ := by
  induction T generalizing π with
  | leaf b =>
    cases b
    · simp [eval, toMDNFAux]
    · simp [eval, toMDNFAux, hπ]
  | query u child ih =>
    obtain ⟨w, hw⟩ := PMatching.exists_partner_of_isPerfect hσ u
    have hsw : s(u, w) ∈ σ.edges := PMatching.partner_eq_some_iff.mp hw
    have hwu : w ≠ u := PMatching.partner_ne_self hw
    simp only [eval, hw, toMDNFAux]
    split_ifs with h
    · have hcw : Classical.choose h = w := by
        have hc := Classical.choose_spec h
        have hpc : σ.partner u = some (Classical.choose h) :=
          PMatching.partner_eq_some_iff.mpr (hπ hc)
        exact Option.some.inj (hpc.symm.trans hw)
      rw [hcw]
      exact ih w π hπ
    · constructor
      · intro heval
        have hw_nsup : w ∉ π.support := by
          intro hsup
          rcases PMatching.mem_support_iff.mp hsup with ⟨e, he, hwe⟩
          have hne : e ≠ s(u, w) := fun heq ↦ h ⟨w, heq ▸ he⟩
          exact σ.disjoint e (hπ he) s(u, w) hsw hne w hwe (Sym2.mem_mk_right u w)
        have hcond : w ≠ u ∧ w ∉ π.support := ⟨hwu, hw_nsup⟩
        have hle' : π.addEdge u w hwu.symm (by
            intro hu
            rcases PMatching.mem_support_iff.mp hu with ⟨e, he, hue⟩
            obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hue
            exact h ⟨z, he⟩) hw_nsup ≤ σ := by
          intro e he
          rcases Finset.mem_insert.mp he with rfl | he'
          · exact hsw
          · exact hπ he'
        rcases (ih w _ hle').mp heval with ⟨C, hC, hCσ⟩
        refine ⟨C, List.mem_flatMap.mpr ⟨w, ?_, ?_⟩, hCσ⟩
        · exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcond⟩)
        · split_ifs
          exact hC
      · rintro ⟨C, hC, hCσ⟩
        simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
          true_and] at hC
        rcases hC with ⟨v, hv, hCv⟩
        split_ifs at hCv
        have hπ' : π.addEdge u v hv.1.symm (by
            intro hu
            rcases PMatching.mem_support_iff.mp hu with ⟨e, he, hue⟩
            obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hue
            exact h ⟨z, he⟩) hv.2 ≤ σ :=
          le_trans (le_of_mem_toMDNFAux (child v) _ C hCv) hCσ
        have hveq : v = w := by
          have hsv : s(u, v) ∈ σ.edges := hπ' (Finset.mem_insert_self _ _)
          exact Option.some.inj ((PMatching.partner_eq_some_iff.mpr hsv).symm.trans hw)
        subst hveq
        exact (ih v _ hπ').mpr ⟨C, hCv, hCσ⟩

lemma toMDNF_eval [Fintype U] [DecidableEq U] (T : MTree U) {σ : PMatching U}
    (hσ : σ.IsPerfect) :
    T.eval σ = true ↔ ∃ C ∈ T.toMDNF, C ≤ σ :=
  toMDNFAux_eval ⊥ T (Finset.empty_subset _) hσ

/-- Boolean implication `T₁ ⟹ T₂` of matching decision trees. -/
@[expose] def imp : MTree U → MTree U → MTree U
  | .leaf false, _ => .leaf true
  | .leaf true, T₂ => T₂
  | .query u child, T₂ => .query u (fun v ↦ (child v).imp T₂)

lemma depth_imp_le [Fintype U] (T₁ T₂ : MTree U) : (T₁.imp T₂).depth ≤ T₁.depth + T₂.depth := by
  induction T₁ with
  | leaf b => cases b <;> simp [imp]
  | query u child ih =>
    simp only [imp, depth_query]
    have hsup : Finset.univ.sup (fun v ↦ ((child v).imp T₂).depth) ≤
        Finset.univ.sup (fun v ↦ (child v).depth) + T₂.depth := by
      refine Finset.sup_le fun v _ ↦ le_trans (ih v) (Nat.add_le_add_right
        (Finset.le_sup (f := fun w ↦ (child w).depth) (Finset.mem_univ v)) _)
    omega

/-- Partial-matching forcing `ρ ⊩ T = b`: every consistent partial-matching completion of `T`
extending `ρ` ends at leaf `b`. -/
def Forces [DecidableEq U] (b : Bool) : PMatching U → MTree U → Prop
  | _, .leaf b' => b' = b
  | ρ, .query u child =>
      match ρ.partner u with
      | some v => (child v).Forces b ρ
      | none =>
          ∀ (v : U) (h : v ≠ u ∧ u ∉ ρ.support ∧ v ∉ ρ.support),
            (child v).Forces b (ρ.addEdge u v h.1.symm h.2.1 h.2.2)

@[simp, grind =] lemma forces_leaf [DecidableEq U] (b b' : Bool) (ρ : PMatching U) :
    (leaf b').Forces b ρ ↔ b' = b := by
  rfl

lemma forces_query_some [DecidableEq U] {ρ : PMatching U} {u v : U} {child : U → MTree U} {b : Bool}
    (hp : ρ.partner u = some v) :
    (query u child).Forces b ρ ↔ (child v).Forces b ρ := by
  simp [Forces, hp]

lemma forces_query_none [DecidableEq U] {ρ : PMatching U} {u : U} {child : U → MTree U} {b : Bool}
    (hp : ρ.partner u = none) :
    (query u child).Forces b ρ ↔
      ∀ (v : U) (h : v ≠ u ∧ u ∉ ρ.support ∧ v ∉ ρ.support),
        (child v).Forces b (ρ.addEdge u v h.1.symm h.2.1 h.2.2) := by
  simp [Forces, hp]

private lemma addEdge_le_of_partner {U : Type u} [DecidableEq U] {π ρ : PMatching U} {u v : U}
    (hπρ : π ≤ ρ) (hu : u ∉ π.support) (hp : ρ.partner u = some v) :
    ∃ hv : v ∉ π.support, π.addEdge u v (PMatching.partner_ne_self hp).symm hu hv ≤ ρ := by
  have hsv : s(u, v) ∈ ρ.edges := PMatching.partner_eq_some_iff.mp hp
  have hv : v ∉ π.support := fun hsup ↦ by
    rcases PMatching.mem_support_iff.mp hsup with ⟨e, he, hve⟩
    have hne : e ≠ s(u, v) := fun heq ↦
      hu (PMatching.mem_support_iff.mpr ⟨e, he, heq ▸ Sym2.mem_mk_left u v⟩)
    exact ρ.disjoint e (hπρ he) s(u, v) hsv hne v hve (Sym2.mem_mk_right u v)
  refine ⟨hv, fun e he ↦ ?_⟩
  rcases Finset.mem_insert.mp he with rfl | he'
  · exact hsv
  · exact hπρ he'

private lemma not_mem_support_of_no_edge {U : Type u} [DecidableEq U] {π : PMatching U} {u : U}
    (h : ¬ ∃ v, s(u, v) ∈ π.edges) : u ∉ π.support := fun hu ↦ by
  rcases PMatching.mem_support_iff.mp hu with ⟨e, he, hue⟩
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hue
  exact h ⟨w, he⟩

/-- Monotonicity of partial-matching forcing under extension. -/
lemma Forces.mono [DecidableEq U] {T : MTree U} {b : Bool} {ρ ρ' : PMatching U}
    (h : T.Forces b ρ) (hle : ρ ≤ ρ') : T.Forces b ρ' := by
  induction T generalizing ρ ρ' with
  | leaf b' => exact h
  | query u child ih =>
    cases hp : ρ.partner u with
    | some v =>
      rw [forces_query_some hp] at h
      rw [forces_query_some (PMatching.partner_eq_some_of_le hle hp)]
      exact ih v h hle
    | none =>
      rw [forces_query_none hp] at h
      have hu_nsup : u ∉ ρ.support := PMatching.partner_eq_none_iff.mp hp
      cases hp' : ρ'.partner u with
      | some v =>
        rw [forces_query_some hp']
        obtain ⟨hv_nsup, hle'⟩ := addEdge_le_of_partner hle hu_nsup hp'
        exact ih v (h v ⟨PMatching.partner_ne_self hp', hu_nsup, hv_nsup⟩) hle'
      | none =>
        rw [forces_query_none hp']
        intro v hv
        have hv_nsup : v ∉ ρ.support := fun hs ↦ hv.2.2 (PMatching.support_mono hle hs)
        have hle' : ρ.addEdge u v hv.1.symm hu_nsup hv_nsup ≤
            ρ'.addEdge u v hv.1.symm hv.2.1 hv.2.2 := fun e he ↦ by
          rcases Finset.mem_insert.mp he with rfl | he'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hle he')
        exact ih v (h v ⟨hv.1, hu_nsup, hv_nsup⟩) hle'

/-- Consistency of forcing: no partial matching with `2 * T.depth ≤ ρ.free.card` forces both
`true` and `false`. -/
lemma Forces.not_both [Fintype U] [DecidableEq U] {T : MTree U} {ρ : PMatching U}
    (hfree : 2 * T.depth ≤ ρ.free.card) (ht : T.Forces true ρ) (hf : T.Forces false ρ) :
    False := by
  induction T generalizing ρ with
  | leaf b =>
    rw [forces_leaf] at ht hf
    rw [ht] at hf
    cases hf
  | query u child ih =>
    have hdep_q : (query u child).depth = 1 + Finset.univ.sup (fun w ↦ (child w).depth) := rfl
    rw [hdep_q] at hfree
    cases hp : ρ.partner u with
    | some v =>
      rw [forces_query_some hp] at ht hf
      have hcv : (child v).depth ≤ Finset.univ.sup (fun w ↦ (child w).depth) :=
        Finset.le_sup (f := fun w ↦ (child w).depth) (Finset.mem_univ v)
      exact ih v (by omega) ht hf
    | none =>
      rw [forces_query_none hp] at ht hf
      have hu_free : u ∈ ρ.free := PMatching.mem_free_iff.mpr (PMatching.partner_eq_none_iff.mp hp)
      have hcard_er : 0 < (ρ.free.erase u).card := by
        rw [Finset.card_erase_of_mem hu_free]; omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard_er
      have hvu : v ≠ u := Finset.ne_of_mem_erase hv
      have hu_nsup : u ∉ ρ.support := PMatching.mem_free_iff.mp hu_free
      have hv_nsup : v ∉ ρ.support := PMatching.mem_free_iff.mp (Finset.mem_of_mem_erase hv)
      let ρ₁ := ρ.addEdge u v hvu.symm hu_nsup hv_nsup
      have hρ₁_card : ρ₁.edges.card = ρ.edges.card + 1 :=
        ρ.card_addEdge_edges u v hvu.symm hu_nsup hv_nsup
      have hρ₁_free : ρ₁.free.card + 2 = ρ.free.card := by
        have h1 := ρ₁.card_free_add
        have h2 := ρ.card_free_add
        omega
      have hcv : (child v).depth ≤ Finset.univ.sup (fun w ↦ (child w).depth) :=
        Finset.le_sup (f := fun w ↦ (child w).depth) (Finset.mem_univ v)
      exact ih v (by change 2 * (child v).depth ≤ ρ₁.free.card; omega)
        (ht v ⟨hvu, hu_nsup, hv_nsup⟩) (hf v ⟨hvu, hu_nsup, hv_nsup⟩)

lemma forces_neg_iff [DecidableEq U] {T : MTree U} {b : Bool} {ρ : PMatching U} :
    T.neg.Forces b ρ ↔ T.Forces (!b) ρ := by
  induction T generalizing ρ with
  | leaf b' =>
    simp only [neg, forces_leaf]
    cases b <;> cases b' <;> decide
  | query u child ih =>
    cases hp : ρ.partner u with
    | some v =>
      simp only [neg, forces_query_some hp, ih v]
    | none =>
      simp only [neg, forces_query_none hp]
      exact forall₂_congr fun v _ ↦ ih v

lemma forces_imp_true_of_false [DecidableEq U] {T₁ T₂ : MTree U} {ρ : PMatching U}
    (h : T₁.Forces false ρ) : (T₁.imp T₂).Forces true ρ := by
  induction T₁ generalizing ρ with
  | leaf b =>
    rw [forces_leaf] at h
    subst h
    simp [imp]
  | query u child ih =>
    cases hp : ρ.partner u with
    | some v =>
      rw [forces_query_some hp] at h
      simp only [imp, forces_query_some hp]
      exact ih v h
    | none =>
      rw [forces_query_none hp] at h
      simp only [imp, forces_query_none hp]
      exact fun v hv ↦ ih v (h v hv)

lemma forces_imp_true_of_right [DecidableEq U] {T₁ T₂ : MTree U} {ρ : PMatching U}
    (h : T₂.Forces true ρ) : (T₁.imp T₂).Forces true ρ := by
  induction T₁ generalizing ρ with
  | leaf b =>
    cases b <;> simp [imp, h]
  | query u child ih =>
    cases hp : ρ.partner u with
    | some v =>
      simp only [imp, forces_query_some hp]
      exact ih v h
    | none =>
      simp only [imp, forces_query_none hp]
      exact fun v hv ↦ ih v (h.mono (PMatching.le_addEdge _ _ _ _ _ _))

lemma forces_imp_false [DecidableEq U] {T₁ T₂ : MTree U} {ρ : PMatching U}
    (h₁ : T₁.Forces true ρ) (h₂ : T₂.Forces false ρ) : (T₁.imp T₂).Forces false ρ := by
  induction T₁ generalizing ρ with
  | leaf b =>
    rw [forces_leaf] at h₁
    subst h₁
    simpa [imp] using h₂
  | query u child ih =>
    cases hp : ρ.partner u with
    | some v =>
      rw [forces_query_some hp] at h₁
      simp only [imp, forces_query_some hp]
      exact ih v h₁ h₂
    | none =>
      rw [forces_query_none hp] at h₁
      simp only [imp, forces_query_none hp]
      exact fun v hv ↦ ih v (h₁ v hv) (h₂.mono (PMatching.le_addEdge _ _ _ _ _ _))

lemma forces_of_restrict_depth_zero [Fintype U] [DecidableEq U] {T : MTree U} {ρ : PMatching U}
    (h : (T.restrict ρ).depth = 0) : ∃ b : Bool, T.Forces b ρ := by
  induction T with
  | leaf b => exact ⟨b, rfl⟩
  | query u child ih =>
    rw [restrict_query] at h
    cases hp : ρ.partner u with
    | some v =>
      rw [hp] at h
      rcases ih v h with ⟨b, hb⟩
      exact ⟨b, (forces_query_some hp).mpr hb⟩
    | none =>
      rw [hp] at h
      simp [depth_query] at h

lemma forces_of_mem_toMDNFAux [Fintype U] [DecidableEq U] {T : MTree U} {π ρ C : PMatching U}
    (hC : C ∈ toMDNFAux π T) (hle : C ≤ ρ) : T.Forces true ρ := by
  induction T generalizing π with
  | leaf b =>
    cases b
    · simp [toMDNFAux] at hC
    · rfl
  | query u child ih =>
    simp only [toMDNFAux] at hC
    split_ifs at hC with h
    · have hπC : π ≤ C := le_of_mem_toMDNFAux _ _ C hC
      have hp : ρ.partner u = some (Classical.choose h) :=
        PMatching.partner_eq_some_iff.mpr (hle (hπC (Classical.choose_spec h)))
      exact (forces_query_some hp).mpr (ih _ hC)
    · simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
        true_and] at hC
      rcases hC with ⟨v, hv, hCv⟩
      split_ifs at hCv
      have hπC := le_of_mem_toMDNFAux _ _ C hCv
      have hp : ρ.partner u = some v :=
        PMatching.partner_eq_some_iff.mpr (hle (hπC (Finset.mem_insert_self _ _)))
      exact (forces_query_some hp).mpr (ih v hCv)

lemma forces_true_of_mem_toMDNF [Fintype U] [DecidableEq U] {T : MTree U} {ρ C : PMatching U}
    (hC : C ∈ T.toMDNF) (hle : C ≤ ρ) : T.Forces true ρ :=
  forces_of_mem_toMDNFAux hC hle

lemma forces_false_of_incompat_toMDNFAux [Fintype U] [DecidableEq U] {T : MTree U}
    {π ρ : PMatching U} (hπρ : π ≤ ρ) (hinc : ∀ C ∈ toMDNFAux π T, ¬ C.Compatible ρ) :
    T.Forces false ρ := by
  induction T generalizing π ρ with
  | leaf b =>
    cases b
    · rfl
    · exact absurd (PMatching.compatible_of_le hπρ) (hinc π (by simp [toMDNFAux]))
  | query u child ih =>
    simp only [toMDNFAux] at hinc
    split_ifs at hinc with h
    · have hp : ρ.partner u = some (Classical.choose h) :=
        PMatching.partner_eq_some_iff.mpr (hπρ (Classical.choose_spec h))
      exact (forces_query_some hp).mpr (ih _ hπρ hinc)
    · have hu_nπ : u ∉ π.support := not_mem_support_of_no_edge h
      cases hp : ρ.partner u with
      | some v =>
        rw [forces_query_some hp]
        obtain ⟨hv_nπ, hle'⟩ := addEdge_le_of_partner hπρ hu_nπ hp
        refine ih v hle' fun C hC ↦ hinc C (List.mem_flatMap.mpr ⟨v, ?_, ?_⟩)
        · exact Finset.mem_toList.mpr (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, PMatching.partner_ne_self hp, hv_nπ⟩)
        · split_ifs with h'
          · exact hC
          · exact (h' ⟨PMatching.partner_ne_self hp, hv_nπ⟩).elim
      | none =>
        rw [forces_query_none hp]
        intro v hv
        have hv_nπ : v ∉ π.support := fun hs ↦ hv.2.2 (PMatching.support_mono hπρ hs)
        have hle' : π.addEdge u v hv.1.symm hu_nπ hv_nπ ≤
            ρ.addEdge u v hv.1.symm hv.2.1 hv.2.2 := fun e he ↦ by
          rcases Finset.mem_insert.mp he with rfl | he'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hπρ he')
        refine ih v hle' fun C hC hcomp ↦ hinc C (List.mem_flatMap.mpr ⟨v, ?_, ?_⟩)
          (PMatching.compatible_mono_right hcomp (PMatching.le_addEdge _ _ _ _ _ _))
        · exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.1, hv_nπ⟩)
        · split_ifs with h'
          · exact hC
          · exact (h' ⟨hv.1, hv_nπ⟩).elim

lemma forces_false_of_incompat_toMDNF [Fintype U] [DecidableEq U] {T : MTree U} {ρ : PMatching U}
    (hinc : ∀ C ∈ T.toMDNF, ¬ C.Compatible ρ) : T.Forces false ρ :=
  forces_false_of_incompat_toMDNFAux (Finset.empty_subset _) hinc

lemma exists_mem_toMDNFAux_le_of_forces_true [Fintype U] [DecidableEq U] {T : MTree U}
    {π ρ : PMatching U} (hπρ : π ≤ ρ) (hdep : (T.restrict ρ).depth = 0)
    (ht : T.Forces true ρ) : ∃ C ∈ toMDNFAux π T, C ≤ ρ := by
  induction T generalizing π with
  | leaf b =>
    rw [forces_leaf] at ht
    subst ht
    exact ⟨π, by simp [toMDNFAux], hπρ⟩
  | query u child ih =>
    rw [restrict_query] at hdep
    cases hp : ρ.partner u with
    | none =>
      rw [hp] at hdep
      simp [depth_query] at hdep
    | some v =>
      rw [hp] at hdep
      rw [forces_query_some hp] at ht
      simp only [toMDNFAux]
      split_ifs with h
      · have hcw : Classical.choose h = v := Option.some.inj
          ((PMatching.partner_eq_some_iff.mpr (hπρ (Classical.choose_spec h))).symm.trans hp)
        rw [hcw]
        exact ih v hπρ hdep ht
      · obtain ⟨hv_nπ, hle'⟩ := addEdge_le_of_partner hπρ (not_mem_support_of_no_edge h) hp
        rcases ih v hle' hdep ht with ⟨C, hC, hCρ⟩
        refine ⟨C, List.mem_flatMap.mpr ⟨v, ?_, ?_⟩, hCρ⟩
        · exact Finset.mem_toList.mpr (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, PMatching.partner_ne_self hp, hv_nπ⟩)
        · split_ifs with h'
          · exact hC
          · exact (h' ⟨PMatching.partner_ne_self hp, hv_nπ⟩).elim

lemma exists_mem_toMDNF_le_of_forces_true [Fintype U] [DecidableEq U] {T : MTree U}
    {ρ : PMatching U} (hdep : (T.restrict ρ).depth = 0) (ht : T.Forces true ρ) :
    ∃ C ∈ T.toMDNF, C ≤ ρ :=
  exists_mem_toMDNFAux_le_of_forces_true (Finset.empty_subset _) hdep ht

end MTree

namespace MDNF

variable {U : Type u} [DecidableEq U]

/-- Evaluates a matching DNF `F` on a partial matching `σ`. -/
def eval (F : MDNF U) (σ : PMatching U) : Bool :=
  F.any fun C ↦ decide (C ≤ σ)

lemma eval_eq_true_iff {F : MDNF U} {σ : PMatching U} :
    F.eval σ = true ↔ ∃ C ∈ F, C ≤ σ := by
  simp [eval, List.any_eq_true]

end MDNF

/-- Extending `ρ` by at most `T.depth` edges forces any matching decision tree `T` to a constant
leaf (depth `0`), provided `ρ` has at least `2 * T.depth` free vertices. -/
theorem exists_extension_forcing_leaf {U : Type u} [Fintype U] [DecidableEq U] (T : MTree U)
    (ρ : PMatching U) (hfree : 2 * T.depth ≤ ρ.free.card) :
    ∃ ρ' : PMatching U, ρ ≤ ρ' ∧ ρ'.edges.card ≤ ρ.edges.card + T.depth ∧
      (T.restrict ρ').depth = 0 := by
  induction T generalizing ρ with
  | leaf b =>
    exact ⟨ρ, le_rfl, by simp, by simp⟩
  | query u child ih =>
    have hdep_q : (MTree.query u child).depth =
        1 + Finset.univ.sup (fun w ↦ (child w).depth) := rfl
    rw [hdep_q] at hfree
    cases hp : ρ.partner u with
    | some v =>
      have hcv : (child v).depth ≤ Finset.univ.sup (fun w ↦ (child w).depth) :=
        Finset.le_sup (f := fun w ↦ (child w).depth) (Finset.mem_univ v)
      rcases ih v ρ (by omega) with ⟨ρ', hle, hcard, hdep⟩
      refine ⟨ρ', hle, by omega, ?_⟩
      simp only [MTree.restrict_query, PMatching.partner_eq_some_of_le hle hp, hdep]
    | none =>
      have hu_free : u ∈ ρ.free := PMatching.mem_free_iff.mpr (PMatching.partner_eq_none_iff.mp hp)
      have hcard_er : 0 < (ρ.free.erase u).card := by
        rw [Finset.card_erase_of_mem hu_free]; omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard_er
      have hvu : v ≠ u := Finset.ne_of_mem_erase hv
      have hu_nsup : u ∉ ρ.support := PMatching.mem_free_iff.mp hu_free
      have hv_nsup : v ∉ ρ.support := PMatching.mem_free_iff.mp (Finset.mem_of_mem_erase hv)
      let ρ₁ := ρ.addEdge u v hvu.symm hu_nsup hv_nsup
      have hρ₁_card : ρ₁.edges.card = ρ.edges.card + 1 :=
        ρ.card_addEdge_edges u v hvu.symm hu_nsup hv_nsup
      have hρ₁_free : ρ₁.free.card + 2 = ρ.free.card := by
        have h1 := ρ₁.card_free_add
        have h2 := ρ.card_free_add
        omega
      have hcv : (child v).depth ≤ Finset.univ.sup (fun w ↦ (child w).depth) :=
        Finset.le_sup (f := fun w ↦ (child w).depth) (Finset.mem_univ v)
      rcases ih v ρ₁ (by omega) with ⟨ρ', hle, hcard, hdep⟩
      refine ⟨ρ', le_trans (PMatching.le_addEdge _ _ _ _ _ _) hle, by omega, ?_⟩
      have hp' : ρ'.partner u = some v :=
        PMatching.partner_eq_some_of_le hle
          (PMatching.partner_eq_some_iff.mpr (Finset.mem_insert_self _ _))
      simp only [MTree.restrict_query, hp', hdep]

/-- Constant-evaluation corollary of `exists_extension_forcing_leaf`. -/
lemma eval_eq_of_restrict_depth_zero {U : Type u} [Fintype U] [DecidableEq U] {T : MTree U}
    {ρ : PMatching U} (h : (T.restrict ρ).depth = 0) :
    ∃ b : Bool, ∀ σ : PMatching U, ρ ≤ σ → T.eval σ = b := by
  cases hr : T.restrict ρ with
  | leaf b =>
    refine ⟨b, fun σ hσ ↦ ?_⟩
    rw [← MTree.eval_restrict ρ T hσ, hr, MTree.eval_leaf]
  | query u child =>
    rw [hr] at h
    simp [MTree.depth] at h

end CslibFrontier.Computability.DecisionTree
