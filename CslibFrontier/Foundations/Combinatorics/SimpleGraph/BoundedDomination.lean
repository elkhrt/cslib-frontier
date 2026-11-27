module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/BoundedDomination.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.DominatingSet
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

/-!
# Bounded Domination, Claw-Free Graphs, and Interval Graphs

Foundations for `[1, j]`-dominating sets in simple graphs, the `[1, j]`-domination number
`γ_{[1, j]}(G)`, the equality of minimum dominating cardinality and `[1, 2]`-domination number on
finite claw-free and proper interval graphs, and right-endpoint vertex orderings of finite interval
graphs.

## Main definitions

* `SimpleGraph.IsBoundedDominatingSet`: a vertex subset `D` in which every vertex `v ∉ D` has at
  least `1` and at most `j` neighbors in `D`.
* `SimpleGraph.boundedDominationNumber`: the minimum cardinality of a finite `[1, j]`-dominating
  set.
* `SimpleGraph.IsClosedIntervalRepr`, `SimpleGraph.IsIntervalGraph`: closed real-interval
  representations and interval graphs.
* `SimpleGraph.IsProperIntervalRepr`, `SimpleGraph.IsProperIntervalGraph`: proper closed
  real-interval representations and proper interval graphs.
* `SimpleGraph.IsRROrdering`: a vertex bijection `e : Fin n ≃ V` such that `i < j < k` and
  `G.Adj (e i) (e k)` imply `G.Adj (e j) (e k)`.

## Main results

* `SimpleGraph.IsBoundedDominatingSet.isDominatingSet`, `SimpleGraph.boundedDominationNumber_congr`,
  `SimpleGraph.boundedDominationNumber_mono_bound`: basic properties, monotonicity in `j`, and
  isomorphism invariance.
* `SimpleGraph.exists_isIndepSet_isBoundedDominatingSet_two_le_card_of_no_claw`,
  `SimpleGraph.boundedDominationNumber_two_le_card_of_isDominatingSet_of_no_claw`: every finite
  claw-free graph admits an independent `[1, 2]`-dominating set of minimum dominating cardinality.
* `SimpleGraph.IsProperIntervalGraph.no_claw`,
  `SimpleGraph.IsProperIntervalGraph.boundedDominationNumber_two_le_card_of_isDominatingSet`:
  proper interval graphs are claw-free and satisfy `γ_{[1, 2]}(G) ≤ |S|` for every dominating set.
* `SimpleGraph.IsIntervalGraph.exists_isRROrdering`: every finite interval graph admits a
  right-endpoint vertex ordering satisfying the umbrella property.
-/

public section

namespace SimpleGraph

variable {V W : Type*}

/-! ### 1. `[1, j]`-Dominating Sets and `[1, j]`-Domination Number -/

section BoundedDomination

/-- A vertex subset `D` is a **`[1, j]`-dominating set** of `G` if every vertex `v ∉ D` has at
least `1` and at most `j` neighbors in `D`. -/
def IsBoundedDominatingSet (G : SimpleGraph V) (j : ℕ) (D : Set V) : Prop :=
  ∀ v : V, v ∉ D →
    (G.neighborSet v ∩ D).Finite ∧
    1 ≤ (G.neighborSet v ∩ D).ncard ∧
    (G.neighborSet v ∩ D).ncard ≤ j

/-- Logical characterization of `IsBoundedDominatingSet`. -/
theorem isBoundedDominatingSet_iff {G : SimpleGraph V} {j : ℕ} {D : Set V} :
    G.IsBoundedDominatingSet j D ↔
      ∀ v : V, v ∉ D →
        (G.neighborSet v ∩ D).Finite ∧
        1 ≤ (G.neighborSet v ∩ D).ncard ∧
        (G.neighborSet v ∩ D).ncard ≤ j :=
  Iff.rfl

/-- Characterization of `[1, j]`-domination for a `Finset` via `Finset.card`. -/
theorem isBoundedDominatingSet_finset_iff {G : SimpleGraph V}
    [DecidableRel G.Adj] {j : ℕ} {D : Finset V} :
    G.IsBoundedDominatingSet j (D : Set V) ↔
      ∀ v : V, v ∉ D → 1 ≤ (D.filter (G.Adj v)).card ∧ (D.filter (G.Adj v)).card ≤ j := by
  refine forall₂_congr fun v _ ↦ ?_
  have heq : G.neighborSet v ∩ (D : Set V) = (D.filter (G.Adj v) : Set V) := by
    ext u
    simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Finset.mem_coe,
      Finset.mem_filter, and_comm]
  rw [heq, Set.ncard_coe_finset]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Set.toFinite _, h⟩⟩

/-- Computable decidability of `[1, j]`-domination for a `Finset` in a finite graph. -/
instance instDecidableIsBoundedDominatingSetFinset [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (D : Finset V) :
    Decidable (G.IsBoundedDominatingSet j (D : Set V)) :=
  decidable_of_iff
    (∀ v : V, v ∉ D → 1 ≤ (D.filter (G.Adj v)).card ∧ (D.filter (G.Adj v)).card ≤ j)
    isBoundedDominatingSet_finset_iff.symm

/-- The full vertex set `Set.univ` is a `[1, j]`-dominating set of every graph. -/
theorem isBoundedDominatingSet_univ (G : SimpleGraph V) (j : ℕ) :
    G.IsBoundedDominatingSet j Set.univ :=
  fun _ hv ↦ absurd (Set.mem_univ _) hv

/-- Every `[1, j]`-dominating set is a dominating set. -/
theorem IsBoundedDominatingSet.isDominatingSet {G : SimpleGraph V} {j : ℕ} {D : Set V}
    (hD : G.IsBoundedDominatingSet j D) : G.IsDominatingSet D := by
  rw [SimpleGraph.isDominatingSet_iff]
  intro v
  by_cases hv : v ∈ D
  · exact Or.inl hv
  · obtain ⟨hfin, hpos, _⟩ := hD v hv
    obtain ⟨u, hu⟩ := (Set.ncard_pos hfin).mp (Nat.succ_le_iff.mp hpos)
    exact Or.inr ⟨u, hu.2, hu.1⟩

/-- Monotonicity of `[1, j]`-domination in the upper bound `j`. -/
@[gcongr]
theorem IsBoundedDominatingSet.mono_bound {G : SimpleGraph V} {j₁ j₂ : ℕ} {D : Set V}
    (hD : G.IsBoundedDominatingSet j₁ D) (hj : j₁ ≤ j₂) :
    G.IsBoundedDominatingSet j₂ D :=
  fun v hv ↦ let ⟨hf, h1, h2⟩ := hD v hv; ⟨hf, h1, h2.trans hj⟩

/-- Graph isomorphism invariance of `[1, j]`-domination. -/
theorem isBoundedDominatingSet_image_iff {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (j : ℕ) (D : Set V) :
    H.IsBoundedDominatingSet j (e '' D) ↔ G.IsBoundedDominatingSet j D := by
  have himg : ∀ v : V, H.neighborSet (e v) ∩ (e '' D) = e '' (G.neighborSet v ∩ D) := by
    intro v; ext w; constructor
    · rintro ⟨hw, u, hu, rfl⟩
      exact ⟨u, ⟨e.map_adj_iff.mp hw, hu⟩, rfl⟩
    · rintro ⟨u, ⟨huG, huD⟩, rfl⟩
      exact ⟨e.map_adj_iff.mpr huG, u, huD, rfl⟩
  constructor
  · intro h v hv
    have hev : e v ∉ e '' D := fun ⟨u, hu, heq⟩ ↦ hv (e.injective heq ▸ hu)
    obtain ⟨hfin, h1, h2⟩ := h (e v) hev
    rw [himg v] at hfin h1 h2
    rw [Set.ncard_image_of_injective _ e.injective] at h1 h2
    exact ⟨hfin.of_finite_image e.injective.injOn, h1, h2⟩
  · intro h w hw
    have hv : e.symm w ∉ D := fun hu ↦ hw ⟨e.symm w, hu, e.apply_symm_apply w⟩
    obtain ⟨hfin, h1, h2⟩ := h (e.symm w) hv
    have hw' : w = e (e.symm w) := (e.apply_symm_apply w).symm
    rw [hw', himg (e.symm w)]
    rw [Set.ncard_image_of_injective _ e.injective]
    exact ⟨hfin.image _, h1, h2⟩

/-- The `[1, j]`-domination number `γ_{[1, j]}(G)`: the minimum cardinality of a finite
`[1, j]`-dominating set (`0` if none exists). -/
noncomputable def boundedDominationNumber (G : SimpleGraph V) (j : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ D : Finset V, G.IsBoundedDominatingSet j (D : Set V) ∧ D.card = n}

/-- Existence of a `[1, j]`-dominating set attaining `G.boundedDominationNumber j`. -/
theorem exists_isBoundedDominatingSet_card_eq [Finite V] (G : SimpleGraph V) (j : ℕ) :
    ∃ D : Finset V, G.IsBoundedDominatingSet j (D : Set V) ∧
      D.card = G.boundedDominationNumber j := by
  have := Fintype.ofFinite V
  have hne :
      {n : ℕ | ∃ D : Finset V, G.IsBoundedDominatingSet j (D : Set V) ∧ D.card = n}.Nonempty :=
    ⟨Fintype.card V, Finset.univ, by simpa using G.isBoundedDominatingSet_univ j, Finset.card_univ⟩
  exact Nat.sInf_mem hne

/-- Upper bound on `G.boundedDominationNumber j` from any `[1, j]`-dominating `Finset`. -/
theorem boundedDominationNumber_le_of_isBoundedDominatingSet
    {G : SimpleGraph V} {j : ℕ} {D : Finset V}
    (hD : G.IsBoundedDominatingSet j (D : Set V)) :
    G.boundedDominationNumber j ≤ D.card :=
  Nat.sInf_le ⟨D, hD, rfl⟩

/-- Always `γ_{[1, j]}(G) ≤ |V|`. -/
theorem boundedDominationNumber_le_card [Fintype V] (G : SimpleGraph V) (j : ℕ) :
    G.boundedDominationNumber j ≤ Fintype.card V := by
  simpa using boundedDominationNumber_le_of_isBoundedDominatingSet
    (D := Finset.univ) (by simpa using G.isBoundedDominatingSet_univ j)

/-- Antitonicity of `boundedDominationNumber` in the upper bound `j`. -/
@[gcongr]
theorem boundedDominationNumber_mono_bound [Finite V] (G : SimpleGraph V)
    {j₁ j₂ : ℕ} (hj : j₁ ≤ j₂) :
    G.boundedDominationNumber j₂ ≤ G.boundedDominationNumber j₁ := by
  obtain ⟨D, hD, hcard⟩ := G.exists_isBoundedDominatingSet_card_eq j₁
  exact (boundedDominationNumber_le_of_isBoundedDominatingSet (hD.mono_bound hj)).trans hcard.le

private theorem boundedDominationNumber_le_of_iso [Finite V] {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G ≃g H) (j : ℕ) :
    H.boundedDominationNumber j ≤ G.boundedDominationNumber j := by
  classical
  obtain ⟨D, hD, hcard⟩ := G.exists_isBoundedDominatingSet_card_eq j
  have hDf : H.IsBoundedDominatingSet j
      ((D.map f.toEquiv.toEmbedding : Finset W) : Set W) := by
    have hcoe : ((D.map f.toEquiv.toEmbedding : Finset W) : Set W) = f '' (D : Set V) := by
      simp [Finset.coe_map]
    rw [hcoe, isBoundedDominatingSet_image_iff f]
    exact hD
  calc H.boundedDominationNumber j ≤ (D.map f.toEquiv.toEmbedding).card :=
        boundedDominationNumber_le_of_isBoundedDominatingSet hDf
    _ = D.card := Finset.card_map _
    _ = G.boundedDominationNumber j := hcard

/-- Graph isomorphism invariance of `boundedDominationNumber`. -/
theorem boundedDominationNumber_congr [Finite V] {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (j : ℕ) :
    G.boundedDominationNumber j = H.boundedDominationNumber j := by
  have : Finite W := Finite.of_equiv V e.toEquiv
  exact le_antisymm (boundedDominationNumber_le_of_iso e.symm j)
    (boundedDominationNumber_le_of_iso e j)

end BoundedDomination

/-! ### 2. `[1, 2]`-Domination in Claw-Free Graphs -/

section ClawFreeBoundedDomination

/-- Every independent dominating set in a claw-free graph is a `[1, 2]`-dominating set. -/
theorem isBoundedDominatingSet_two_of_isIndepSet_of_no_claw
    {G : SimpleGraph V} {D : Set V}
    (hclaw : ∀ v a b c : V, G.Adj v a → G.Adj v b → G.Adj v c →
      a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c)
    (hind : G.IsIndepSet D) (hdom : G.IsDominatingSet D) :
    G.IsBoundedDominatingSet 2 D := by
  classical
  intro v hv
  obtain ⟨u, huD, huv⟩ := (SimpleGraph.isDominatingSet_iff.mp hdom v).resolve_left hv
  have hsub : (G.neighborSet v ∩ D).ncard ≤ 2 ∧ (G.neighborSet v ∩ D).Finite := by
    by_cases hfin : (G.neighborSet v ∩ D).Finite
    · refine ⟨?_, hfin⟩
      by_contra hgt
      have h3 : 3 ≤ hfin.toFinset.card := by
        rw [← Set.ncard_eq_toFinset_card _ hfin]; omega
      obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq h3
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
      have ha : a ∈ G.neighborSet v ∩ D := hfin.mem_toFinset.mp (ht (by simp))
      have hb : b ∈ G.neighborSet v ∩ D := hfin.mem_toFinset.mp (ht (by simp))
      have hc : c ∈ G.neighborSet v ∩ D := hfin.mem_toFinset.mp (ht (by simp))
      rcases hclaw v a b c ha.1 hb.1 hc.1 hab hac hbc with h | h | h
      · exact hind ha.2 hb.2 hab h
      · exact hind ha.2 hc.2 hac h
      · exact hind hb.2 hc.2 hbc h
    · exfalso
      obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hfin 3
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
      have ha : a ∈ G.neighborSet v ∩ D := ht (by simp)
      have hb : b ∈ G.neighborSet v ∩ D := ht (by simp)
      have hc : c ∈ G.neighborSet v ∩ D := ht (by simp)
      rcases hclaw v a b c ha.1 hb.1 hc.1 hab hac hbc with h | h | h
      · exact hind ha.2 hb.2 hab h
      · exact hind ha.2 hc.2 hac h
      · exact hind hb.2 hc.2 hbc h
  have hpos : 1 ≤ (G.neighborSet v ∩ D).ncard :=
    Nat.succ_le_iff.mpr ((Set.ncard_pos hsub.2).mpr ⟨u, huv, huD⟩)
  exact ⟨hsub.2, hpos, hsub.1⟩

/-- Every finite claw-free graph admits an independent `[1, 2]`-dominating set of minimum
dominating cardinality. -/
theorem exists_isIndepSet_isBoundedDominatingSet_two_le_card_of_no_claw [Finite V]
    {G : SimpleGraph V}
    (hclaw : ∀ v a b c : V, G.Adj v a → G.Adj v b → G.Adj v c →
      a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c) :
    ∃ D : Finset V, G.IsIndepSet (D : Set V) ∧ G.IsBoundedDominatingSet 2 (D : Set V) ∧
      ∀ S : Finset V, G.IsDominatingSet (S : Set V) → D.card ≤ S.card := by
  classical
  have := Fintype.ofFinite V
  let γ : ℕ := sInf {n : ℕ | ∃ S : Finset V, G.IsDominatingSet (S : Set V) ∧ S.card = n}
  have hγ_ne : {n : ℕ | ∃ S : Finset V, G.IsDominatingSet (S : Set V) ∧ S.card = n}.Nonempty :=
    ⟨Fintype.card V, Finset.univ, by simpa using G.isDominatingSet_univ, Finset.card_univ⟩
  have hγ_le : ∀ S : Finset V, G.IsDominatingSet (S : Set V) → γ ≤ S.card :=
    fun S hS ↦ Nat.sInf_le ⟨S, hS, rfl⟩
  let internalEdges (S : Finset V) : ℕ :=
    (S ×ˢ S).filter (fun p ↦ G.Adj p.1 p.2) |>.card
  let P : ℕ → Prop := fun m ↦
    ∃ S : Finset V, G.IsDominatingSet (S : Set V) ∧ S.card = γ ∧ internalEdges S = m
  have hne : ∃ m, P m := by
    obtain ⟨S, hS, hcard⟩ := Nat.sInf_mem hγ_ne
    exact ⟨internalEdges S, S, hS, hcard, rfl⟩
  let m₀ := Nat.find hne
  obtain ⟨S, hSdom, hScard, hSedges⟩ := Nat.find_spec hne
  have hind : G.IsIndepSet (S : Set V) := by
    intro a ha b hb hab hadj
    have haS : a ∈ S := Finset.mem_coe.mp ha
    have hbS : b ∈ S := Finset.mem_coe.mp hb
    let epn : Finset V :=
      Finset.univ.filter fun x ↦ x ∉ S ∧ G.Adj x a ∧ ∀ s ∈ S, s ≠ a → ¬ G.Adj x s
    have hepn_ne : epn.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have hdom' : G.IsDominatingSet ((S.erase a : Finset V) : Set V) := by
        rw [SimpleGraph.isDominatingSet_iff]
        intro v
        by_cases hv : v ∈ S
        · by_cases hva : v = a
          · subst hva
            exact Or.inr ⟨b, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hab.symm, hbS⟩), hadj⟩
          · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hva, hv⟩))
        · rcases SimpleGraph.isDominatingSet_iff.mp hSdom v with hv' | ⟨s, hs, hvs⟩
          · exact absurd hv' hv
          · by_cases hsa : s = a
            · subst hsa
              have hnotmem : v ∉ epn := by rw [hemp]; exact Finset.notMem_empty v
              simp only [epn, Finset.mem_filter, Finset.mem_univ, true_and, not_and,
                not_forall, Classical.not_not] at hnotmem
              obtain ⟨s', hs', hs'a, hvs'⟩ := hnotmem hv hvs
              exact Or.inr ⟨s', Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hs'a, hs'⟩), hvs'⟩
            · exact Or.inr ⟨s, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hsa, hs⟩), hvs⟩
      have hle := hγ_le _ hdom'
      have hlt : (S.erase a).card < γ := by
        rw [Finset.card_erase_of_mem haS, hScard]
        have hpos : 0 < γ := by rw [← hScard]; exact Finset.card_pos.mpr ⟨a, haS⟩
        omega
      omega
    obtain ⟨x, hx⟩ := hepn_ne
    simp only [epn, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxS, hxa, hxpriv⟩ := hx
    let S' : Finset V := insert x (S.erase a)
    have hS'card : S'.card = γ := by
      have hxnot : x ∉ S.erase a := fun h ↦ hxS (Finset.mem_of_mem_erase h)
      rw [Finset.card_insert_of_notMem hxnot, Finset.card_erase_of_mem haS]
      have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨a, haS⟩
      omega
    have hS'dom : G.IsDominatingSet (S' : Set V) := by
      rw [SimpleGraph.isDominatingSet_iff]
      intro v
      by_cases hv : v ∈ S'
      · exact Or.inl hv
      · have hvx : v ≠ x := fun h ↦ hv (h ▸ Finset.mem_coe.mpr (Finset.mem_insert_self x _))
        by_cases hva : v = a
        · subst hva
          exact Or.inr ⟨x, Finset.mem_coe.mpr (Finset.mem_insert_self x _), hxa.symm⟩
        · have hvS : v ∉ S := fun h ↦
            hv (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hva, h⟩)))
          rcases (SimpleGraph.isDominatingSet_iff.mp hSdom v).resolve_left hvS with
            ⟨s, hs, hvs⟩
          by_cases hsa : s = a
          · rw [hsa] at hvs
            by_cases hother : ∃ s' ∈ S, s' ≠ a ∧ G.Adj v s'
            · obtain ⟨s', hs', hs'a, hvs'⟩ := hother
              exact Or.inr ⟨s', Finset.mem_coe.mpr
                (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hs'a, hs'⟩)), hvs'⟩
            · push Not at hother
              have hvx_adj : G.Adj v x := by
                have hba : G.Adj a b := hadj
                have hax : G.Adj a x := hxa.symm
                have hav : G.Adj a v := hvs.symm
                have hbv : ¬ G.Adj b v := fun h ↦ hother b hbS hab.symm h.symm
                have hbx : ¬ G.Adj b x := fun h ↦ hxpriv b hbS hab.symm h.symm
                have hvb : v ≠ b := fun h ↦ hvS (h ▸ hbS)
                have hxb : x ≠ b := fun h ↦ hxS (h ▸ hbS)
                rcases hclaw a v x b hav hax hba hvx hvb hxb with h | h | h
                · exact h
                · exact absurd h.symm hbv
                · exact absurd h.symm hbx
              exact Or.inr ⟨x, Finset.mem_coe.mpr (Finset.mem_insert_self x _), hvx_adj⟩
          · exact Or.inr ⟨s, Finset.mem_coe.mpr
              (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hsa, hs⟩)), hvs⟩
    have hS'lt : internalEdges S' < internalEdges S := by
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, S', Finset.mem_insert,
          Finset.mem_erase] at hp ⊢
        rcases hp with ⟨⟨hp1 | ⟨_, hp1⟩, hp2 | ⟨_, hp2⟩⟩, hpadj⟩
        · rw [hp1, hp2] at hpadj; exact absurd hpadj (G.loopless.irrefl _)
        · rw [hp1] at hpadj; exact absurd hpadj (hxpriv p.2 hp2 ‹_›)
        · rw [hp2] at hpadj; exact absurd hpadj.symm (hxpriv p.1 hp1 ‹_›)
        · exact ⟨⟨hp1, hp2⟩, hpadj⟩
      · intro heq
        have hab_mem : (a, b) ∈ (S ×ˢ S).filter (fun p ↦ G.Adj p.1 p.2) :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haS, hbS⟩, hadj⟩
        rw [← heq, Finset.mem_filter, Finset.mem_product] at hab_mem
        rcases Finset.mem_insert.mp hab_mem.1.1 with hax | ha'
        · exact hxS (hax ▸ haS)
        · exact (Finset.mem_erase.mp ha').1 rfl
    have hlt_m0 : internalEdges S' < m₀ := by dsimp [m₀]; rw [← hSedges]; exact hS'lt
    exact Nat.find_min hne hlt_m0 ⟨S', hS'dom, hS'card, rfl⟩
  exact ⟨S, hind, isBoundedDominatingSet_two_of_isIndepSet_of_no_claw hclaw hind hSdom,
    fun T hT ↦ hScard ▸ hγ_le T hT⟩

/-- In every finite claw-free graph, `γ_{[1, 2]}(G) ≤ |S|` for every dominating `Finset` `S`. -/
theorem boundedDominationNumber_two_le_card_of_isDominatingSet_of_no_claw [Finite V]
    {G : SimpleGraph V}
    (hclaw : ∀ v a b c : V, G.Adj v a → G.Adj v b → G.Adj v c →
      a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c)
    {S : Finset V} (hS : G.IsDominatingSet (S : Set V)) :
    G.boundedDominationNumber 2 ≤ S.card := by
  obtain ⟨D, _, hD12, hmin⟩ :=
    exists_isIndepSet_isBoundedDominatingSet_two_le_card_of_no_claw hclaw
  exact (boundedDominationNumber_le_of_isBoundedDominatingSet hD12).trans (hmin S hS)

end ClawFreeBoundedDomination

/-! ### 3. Interval Graphs, Proper Interval Graphs, and Right-Endpoint Orderings -/

section IntervalGraphs

/-- A pair of maps `l r : V → ℝ` is a **closed real-interval representation** of `G` if
`l v ≤ r v` for all `v` and distinct vertices `u ≠ v` are adjacent iff `[l u, r u]` intersects
`[l v, r v]`. -/
def IsClosedIntervalRepr (G : SimpleGraph V) (l r : V → ℝ) : Prop :=
  (∀ v : V, l v ≤ r v) ∧
  ∀ u v : V, u ≠ v → (G.Adj u v ↔ (Set.Icc (l u) (r u) ∩ Set.Icc (l v) (r v)).Nonempty)

/-- Logical characterization of `IsClosedIntervalRepr`. -/
theorem isClosedIntervalRepr_iff {G : SimpleGraph V} {l r : V → ℝ} :
    G.IsClosedIntervalRepr l r ↔
      (∀ v : V, l v ≤ r v) ∧
      ∀ u v : V, u ≠ v → (G.Adj u v ↔ (Set.Icc (l u) (r u) ∩ Set.Icc (l v) (r v)).Nonempty) :=
  Iff.rfl

private theorem nonempty_Icc_inter_Icc_iff {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    (Set.Icc a₁ b₁ ∩ Set.Icc a₂ b₂).Nonempty ↔ a₁ ≤ b₂ ∧ a₂ ≤ b₁ := by
  rw [Set.Icc_inter_Icc, Set.nonempty_Icc, sup_le_iff, le_inf_iff, le_inf_iff]
  exact ⟨fun h ↦ ⟨h.1.2, h.2.1⟩, fun ⟨h12, h21⟩ ↦ ⟨⟨h₁, h12⟩, ⟨h21, h₂⟩⟩⟩

/-- A simple graph is an **interval graph** if it admits a closed real-interval representation. -/
def IsIntervalGraph (G : SimpleGraph V) : Prop :=
  ∃ l r : V → ℝ, G.IsClosedIntervalRepr l r

/-- Logical characterization of `IsIntervalGraph`. -/
theorem isIntervalGraph_iff {G : SimpleGraph V} :
    G.IsIntervalGraph ↔ ∃ l r : V → ℝ, G.IsClosedIntervalRepr l r :=
  Iff.rfl

/-- A closed interval representation `(l, r)` is **proper** if no interval is contained in
another. -/
def IsProperIntervalRepr (G : SimpleGraph V) (l r : V → ℝ) : Prop :=
  G.IsClosedIntervalRepr l r ∧
  ∀ u v : V, u ≠ v → ¬ (Set.Icc (l v) (r v) ⊆ Set.Icc (l u) (r u))

/-- Logical characterization of `IsProperIntervalRepr`. -/
theorem isProperIntervalRepr_iff {G : SimpleGraph V} {l r : V → ℝ} :
    G.IsProperIntervalRepr l r ↔
      G.IsClosedIntervalRepr l r ∧
      ∀ u v : V, u ≠ v → ¬ (Set.Icc (l v) (r v) ⊆ Set.Icc (l u) (r u)) :=
  Iff.rfl

/-- A simple graph is a **proper interval graph** if it admits a proper closed real-interval
representation. -/
def IsProperIntervalGraph (G : SimpleGraph V) : Prop :=
  ∃ l r : V → ℝ, G.IsProperIntervalRepr l r

/-- Logical characterization of `IsProperIntervalGraph`. -/
theorem isProperIntervalGraph_iff {G : SimpleGraph V} :
    G.IsProperIntervalGraph ↔ ∃ l r : V → ℝ, G.IsProperIntervalRepr l r :=
  Iff.rfl

/-- Every proper interval graph is an interval graph. -/
theorem IsProperIntervalGraph.isIntervalGraph {G : SimpleGraph V}
    (hG : G.IsProperIntervalGraph) : G.IsIntervalGraph :=
  let ⟨l, r, hrepr, _⟩ := hG; ⟨l, r, hrepr⟩

/-- Every proper interval graph is claw-free. -/
theorem IsProperIntervalGraph.no_claw {G : SimpleGraph V}
    (hG : G.IsProperIntervalGraph) :
    ∀ v a b c : V, G.Adj v a → G.Adj v b → G.Adj v c →
      a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
  obtain ⟨l, r, ⟨hlr, hadj⟩, hprop⟩ := hG
  intro v a b c hva hvb hvc hab hac hbc
  by_contra hnone
  push Not at hnone
  obtain ⟨hnab, hnac, hnbc⟩ := hnone
  have hd_ab : r a < l b ∨ r b < l a := by
    have h := (hadj a b hab).not.mp hnab
    rw [nonempty_Icc_inter_Icc_iff (hlr a) (hlr b)] at h
    rcases not_and_or.mp h with h1 | h2
    · exact Or.inr (lt_of_not_ge h1)
    · exact Or.inl (lt_of_not_ge h2)
  have hd_ac : r a < l c ∨ r c < l a := by
    have h := (hadj a c hac).not.mp hnac
    rw [nonempty_Icc_inter_Icc_iff (hlr a) (hlr c)] at h
    rcases not_and_or.mp h with h1 | h2
    · exact Or.inr (lt_of_not_ge h1)
    · exact Or.inl (lt_of_not_ge h2)
  have hd_bc : r b < l c ∨ r c < l b := by
    have h := (hadj b c hbc).not.mp hnbc
    rw [nonempty_Icc_inter_Icc_iff (hlr b) (hlr c)] at h
    rcases not_and_or.mp h with h1 | h2
    · exact Or.inr (lt_of_not_ge h1)
    · exact Or.inl (lt_of_not_ge h2)
  have hmid : ∀ x y z : V,
      x ≠ v → y ≠ v → z ≠ v →
      G.Adj v x → G.Adj v z →
      r x < l y → r y < l z → False := by
    intro x y z hxv hyv hzv hvx hvz hxy hyz
    have h1 := (hadj v x hxv.symm).mp hvx
    rw [nonempty_Icc_inter_Icc_iff (hlr v) (hlr x)] at h1
    have h2 := (hadj v z hzv.symm).mp hvz
    rw [nonempty_Icc_inter_Icc_iff (hlr v) (hlr z)] at h2
    have hsub : Set.Icc (l y) (r y) ⊆ Set.Icc (l v) (r v) := by
      intro t ⟨ht1, ht2⟩
      exact ⟨(h1.1.trans hxy.le).trans ht1, ht2.trans (hyz.le.trans h2.2)⟩
    exact hprop v y hyv.symm hsub
  have hav : a ≠ v := fun h ↦ G.loopless.irrefl v (h ▸ hva)
  have hbv : b ≠ v := fun h ↦ G.loopless.irrefl v (h ▸ hvb)
  have hcv : c ≠ v := fun h ↦ G.loopless.irrefl v (h ▸ hvc)
  rcases hd_ab with h1 | h1 <;> rcases hd_ac with h2 | h2 <;> rcases hd_bc with h3 | h3
  · exact hmid a b c hav hbv hcv hva hvc h1 h3
  · exact hmid a c b hav hcv hbv hva hvb h2 h3
  · exact lt_irrefl (l a) (((hlr a).trans_lt h1).trans (((hlr b).trans_lt h3).trans
      ((hlr c).trans_lt h2)))
  · exact hmid c a b hcv hav hbv hvc hvb h2 h1
  · exact hmid b a c hbv hav hcv hvb hvc h1 h2
  · exact lt_irrefl (l a) (((hlr a).trans_lt h2).trans (((hlr c).trans_lt h3).trans
      ((hlr b).trans_lt h1)))
  · exact hmid b c a hbv hcv hav hvb hva h3 h2
  · exact hmid c b a hcv hbv hav hvc hva h3 h1

/-- In every finite proper interval graph, `γ_{[1, 2]}(G) ≤ |S|` for every dominating `Finset`. -/
theorem IsProperIntervalGraph.boundedDominationNumber_two_le_card_of_isDominatingSet [Finite V]
    {G : SimpleGraph V} (hG : G.IsProperIntervalGraph)
    {S : Finset V} (hS : G.IsDominatingSet (S : Set V)) :
    G.boundedDominationNumber 2 ≤ S.card :=
  boundedDominationNumber_two_le_card_of_isDominatingSet_of_no_claw hG.no_claw hS

/-- A vertex numbering `e : Fin n ≃ V` satisfies the right-endpoint umbrella property if
`i < j < k` and `G.Adj (e i) (e k)` imply `G.Adj (e j) (e k)`. -/
def IsRROrdering {n : ℕ} (G : SimpleGraph V) (e : Fin n ≃ V) : Prop :=
  ∀ ⦃i j k : Fin n⦄, i < j → j < k → G.Adj (e i) (e k) → G.Adj (e j) (e k)

/-- Logical characterization of `IsRROrdering`. -/
theorem isRROrdering_iff {n : ℕ} {G : SimpleGraph V} {e : Fin n ≃ V} :
    G.IsRROrdering e ↔
      ∀ ⦃i j k : Fin n⦄, i < j → j < k → G.Adj (e i) (e k) → G.Adj (e j) (e k) :=
  Iff.rfl

/-- Every finite interval graph of order `n` admits a vertex numbering `e : Fin n ≃ V` satisfying
the umbrella property (`i < j < k` and `G.Adj (e i) (e k)` imply `G.Adj (e j) (e k)`). -/
theorem IsIntervalGraph.exists_isRROrdering [Fintype V] {G : SimpleGraph V}
    (hG : G.IsIntervalGraph) :
    ∃ e : Fin (Fintype.card V) ≃ V, G.IsRROrdering e := by
  classical
  obtain ⟨l, r, hlr, hadj⟩ := hG
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let perm := Tuple.sort (r ∘ e)
  let σ : Fin (Fintype.card V) ≃ V := perm.trans e
  have hmono : Monotone (r ∘ σ) := Tuple.monotone_sort (r ∘ e)
  refine ⟨σ, fun i j k hij hjk hik ↦ ?_⟩
  have hne_ik : σ i ≠ σ k := σ.injective.ne (ne_of_lt (hij.trans hjk))
  have hne_jk : σ j ≠ σ k := σ.injective.ne (ne_of_lt hjk)
  have hinter := (hadj (σ i) (σ k) hne_ik).mp hik
  rw [nonempty_Icc_inter_Icc_iff (hlr (σ i)) (hlr (σ k))] at hinter
  have hri_rj : r (σ i) ≤ r (σ j) := hmono hij.le
  have hrj_rk : r (σ j) ≤ r (σ k) := hmono hjk.le
  refine (hadj (σ j) (σ k) hne_jk).mpr ?_
  rw [nonempty_Icc_inter_Icc_iff (hlr (σ j)) (hlr (σ k))]
  exact ⟨(hlr (σ j)).trans hrj_rk, hinter.2.trans hri_rj⟩

end IntervalGraphs

end SimpleGraph
