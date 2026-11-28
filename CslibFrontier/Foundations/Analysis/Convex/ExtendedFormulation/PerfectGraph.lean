module

public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.StableSet
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Matrix.ColumnRowPartitioned

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stable Set Polytope of Perfect Graphs (Chvátal–Lovász Theorem)

Formalizes Lovász's Replication Lemma, Lovász's Weak Perfect Graph Theorem, and the Chvátal–Lovász
polyhedral characterization of the stable set polytope of finite perfect graphs:

- `IsClawFree`: absence of an induced `K_{1,3}` (three pairwise non-adjacent neighbors of a vertex).
- `IsPerfectGraph`: every finite induced subgraph satisfies `χ(G[S]) = ω(G[S])`.
- `isPerfectGraph_dup` and `isPerfectGraph_trueWeightRep`: Lovász's Replication Lemma.
- `isPerfectGraph_compl`: Lovász's Weak Perfect Graph Theorem (`G` perfect implies `Gᶜ` perfect).
- `qstabPolytope`: fractional stable set polytope `QSTAB(G)` defined by non-negativity and clique
  inequalities.
- `isPerfectGraph_imp_stabPolytope_eq_qstabPolytope` and `stabPolytope_eq_setOf_mulVec_le`:
  Chvátal–Lovász characterization `STAB(G) = QSTAB(G)` for finite perfect graphs.
-/

public section

namespace CslibFrontier.ExtendedFormulation

open Matrix SimpleGraph

section Definitions

variable {V : Type*}

/-- A simple graph `G` is **claw-free** if no vertex has three pairwise non-adjacent neighbors
in `G`. -/
@[expose] def IsClawFree (G : SimpleGraph V) : Prop :=
  ∀ u : V, ∀ t : Finset V, (t : Set V) ⊆ G.neighborSet u →
    ¬ (G.IsIndepSet (t : Set V) ∧ t.card = 3)

/-- A simple graph `G` is **perfect** if every finite induced subgraph satisfies
`χ(G[S]) = ω(G[S])`. -/
@[expose] def IsPerfectGraph (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, (G.induce (S : Set V)).chromaticNumber = (G.induce (S : Set V)).cliqueNum

/-- The **fractional stable set polytope** `QSTAB(G)`: nonnegative vectors `x : V → ℝ`
satisfying `∑ v ∈ K, x v ≤ 1` for
every finite clique `K` of `G`. -/
@[expose] def qstabPolytope (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ ∀ K : Finset V, G.IsClique (K : Set V) → ∑ v ∈ K, x v ≤ 1}

end Definitions

/-! ### Helper lemmas on induced subgraphs, cliques, and colorings -/

section GraphHelpers

variable {V W : Type*}

private lemma cliqueNum_le_of_iso [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : G.cliqueNum ≤ H.cliqueNum := by
  classical
  obtain ⟨K, hK⟩ := G.exists_isNClique_cliqueNum
  have hcl : H.IsClique ((K.image f : Finset W) : Set W) := by
    intro a ha b hb hab
    rcases Finset.mem_image.1 (Finset.mem_coe.1 ha) with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.1 (Finset.mem_coe.1 hb) with ⟨y, hy, rfl⟩
    exact f.map_rel_iff.2 (hK.1 hx hy (fun h => hab (congrArg f h)))
  have hcard : (K.image f).card = K.card := Finset.card_image_of_injective _ f.injective
  calc G.cliqueNum = K.card := hK.2.symm
    _ = (K.image f).card := hcard.symm
    _ ≤ H.cliqueNum := hcl.card_le_cliqueNum

private lemma cliqueNum_congr [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.cliqueNum = H.cliqueNum :=
  le_antisymm (cliqueNum_le_of_iso e) (cliqueNum_le_of_iso e.symm)

private lemma isPerfectGraph_of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : IsPerfectGraph G) : IsPerfectGraph H := by
  classical
  intro S
  let T : Finset V := S.image e.symm
  let iso : G.induce (T : Set V) ≃g H.induce (S : Set W) :=
    { toFun := fun x => ⟨e x.1, by
        rcases Finset.mem_image.1 (Finset.mem_coe.1 x.2) with ⟨y, hy, hyx⟩
        have : e x.1 = y := by rw [← hyx, e.apply_symm_apply]
        exact Finset.mem_coe.2 (this ▸ hy)⟩
      invFun := fun y => ⟨e.symm y.1,
        Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 y.2))⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_rel_iff' := fun {a b} => e.map_rel_iff }
  rw [← chromaticNumber_congr iso, ← cliqueNum_congr iso]
  exact hG T

private lemma isPerfectGraph_induce {G : SimpleGraph V} (hG : IsPerfectGraph G) (U : Set V) :
    IsPerfectGraph (G.induce U) := by
  classical
  intro S
  let T : Finset V := S.image Subtype.val
  let iso : (G.induce U).induce (S : Set U) ≃g G.induce (T : Set V) :=
    { toFun := fun x => ⟨x.1.1,
        Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 x.2))⟩
      invFun := fun y =>
        let hmem := Finset.mem_image.1 (Finset.mem_coe.1 y.2)
        ⟨hmem.choose, Finset.mem_coe.2 hmem.choose_spec.1⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        have hmem := Finset.mem_image.1 (Finset.mem_coe.1
          (Finset.mem_coe.2 (Finset.mem_image_of_mem Subtype.val (Finset.mem_coe.1 x.2))))
        exact hmem.choose_spec.2
      right_inv := fun y => by
        apply Subtype.ext
        have hmem := Finset.mem_image.1 (Finset.mem_coe.1 y.2)
        exact hmem.choose_spec.2
      map_rel_iff' := fun {a b} => Iff.rfl }
  rw [chromaticNumber_congr iso, cliqueNum_congr iso]
  exact hG T

private def induceUnivIso (G : SimpleGraph V) : G.induce (Set.univ : Set V) ≃g G where
  toFun x := x.1
  invFun v := ⟨v, trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private lemma chromaticNumber_eq_cliqueNum_of_isPerfectGraph [Finite V] {G : SimpleGraph V}
    (hG : IsPerfectGraph G) : G.chromaticNumber = G.cliqueNum := by
  let _ : Fintype V := Fintype.ofFinite V
  have h := hG Finset.univ
  have hcoe : (Finset.univ : Finset V) = (Set.univ : Set V) := Finset.coe_univ
  rw [hcoe] at h
  rwa [chromaticNumber_congr (induceUnivIso G), cliqueNum_congr (induceUnivIso G)] at h

private lemma colorable_cliqueNum_of_isPerfectGraph [Finite V] {G : SimpleGraph V}
    (hG : IsPerfectGraph G) : G.Colorable G.cliqueNum := by
  rw [← SimpleGraph.chromaticNumber_le_iff_colorable,
    chromaticNumber_eq_cliqueNum_of_isPerfectGraph hG]

private lemma card_clique_le_cliqueNum [Finite V] {G : SimpleGraph V} {K : Finset V}
    (hK : G.IsClique (K : Set V)) : K.card ≤ G.cliqueNum :=
  hK.card_le_cliqueNum

private lemma card_inter_le_one_of_isClique_isIndepSet [DecidableEq V] {G : SimpleGraph V}
    {K I : Finset V} (hK : G.IsClique (K : Set V)) (hI : G.IsIndepSet (I : Set V)) :
    (K ∩ I).card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  by_contra hne
  exact hI (Finset.mem_inter.1 ha).2 (Finset.mem_inter.1 hb).2 hne
    (hK (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 hb).1 hne)

end GraphHelpers

/-! ### Lovász's Replication Lemma -/

section ReplicationLemma

variable {V : Type*}

/-- True-twin duplication of a vertex `v₀` in `G`: `none` is adjacent to `some v₀` and all
neighbors of `v₀`. -/
private def dupGraph (G : SimpleGraph V) (v₀ : V) : SimpleGraph (Option V) where
  Adj a b :=
    match a, b with
    | some u, some w => G.Adj u w
    | none, some w => w = v₀ ∨ G.Adj v₀ w
    | some u, none => u = v₀ ∨ G.Adj v₀ u
    | none, none => False
  symm := ⟨fun a b h => by
    cases a <;> cases b <;> simp only at h ⊢
    · exact h
    · exact h
    · exact G.adj_symm h⟩
  loopless := ⟨fun a h => by
    cases a with
    | none => exact h
    | some u => exact G.loopless.irrefl u h⟩

/-- **Lovász's Replication Lemma (single vertex)**: duplicating a vertex as a true twin preserves
perfection. -/
private lemma isPerfectGraph_dup {G : SimpleGraph V} (hG : IsPerfectGraph G) (v₀ : V) :
    IsPerfectGraph (dupGraph G v₀) := by
  classical
  let H := dupGraph G v₀
  intro S
  refine le_antisymm ?_ SimpleGraph.cliqueNum_le_chromaticNumber
  rw [SimpleGraph.chromaticNumber_le_iff_colorable]
  -- Case 1: `none ∉ S` — `H[S]` embeds as an induced subgraph of `G`.
  by_cases hnone : (none : Option V) ∈ S
  · -- Case 2: `some v₀ ∉ S` — map `none ↦ v₀`, embedding `H[S]` as an induced subgraph of `G`.
    by_cases hv₀ : some v₀ ∈ S
    · -- Main case: both `none` and `some v₀` lie in `S`.
      let T : Finset V := (S.erase none).preimage some (fun _ _ _ _ h => Option.some.inj h)
      have hS_eq : ∀ u : V, some u ∈ S ↔ u ∈ T := fun u =>
        ⟨fun h => Finset.mem_preimage.2 (Finset.mem_erase.2 ⟨Option.some_ne_none u, h⟩),
         fun h => Finset.mem_of_mem_erase (Finset.mem_preimage.1 h)⟩
      have hv₀T : v₀ ∈ T := (hS_eq v₀).1 hv₀
      let ω := (G.induce (T : Set V)).cliqueNum
      have hω_le : ω ≤ (H.induce (S : Set (Option V))).cliqueNum := by
        obtain ⟨K, hK⟩ := (G.induce (T : Set V)).exists_isNClique_cliqueNum
        let K' : Finset (S : Set (Option V)) :=
          K.image fun x => ⟨some x.1, (hS_eq x.1).2 (Finset.mem_coe.1 x.2)⟩
        have hK'_card : K'.card = K.card := Finset.card_image_of_injective _ fun a b hab => by
          apply Subtype.ext
          exact Option.some.inj (congrArg Subtype.val hab)
        have hK'_cl : (H.induce (S : Set (Option V))).IsClique (K' : Set (S : Set (Option V))) := by
          intro a ha b hb hab
          rcases Finset.mem_image.1 (Finset.mem_coe.1 ha) with ⟨x, hx, rfl⟩
          rcases Finset.mem_image.1 (Finset.mem_coe.1 hb) with ⟨y, hy, rfl⟩
          have hxy : x ≠ y := fun h => hab (by subst h; rfl)
          exact hK.1 hx hy hxy
        calc ω = K.card := hK.2.symm
          _ = K'.card := hK'_card.symm
          _ ≤ (H.induce (S : Set (Option V))).cliqueNum := card_clique_le_cliqueNum hK'_cl
      -- Check if `v₀` lies in an `ω`-clique of `G[T]`.
      by_cases hcl : ∃ K : Finset (T : Set V),
          (G.induce (T : Set V)).IsNClique ω K ∧ ⟨v₀, Finset.mem_coe.2 hv₀T⟩ ∈ K
      · -- Subcase A: `v₀` lies in an `ω`-clique `K` of `G[T]`, giving an `(ω+1)`-clique.
        obtain ⟨K, hK, hv₀K⟩ := hcl
        let noneS : (S : Set (Option V)) := ⟨none, Finset.mem_coe.2 hnone⟩
        let Kimg : Finset (S : Set (Option V)) :=
          K.image fun x => ⟨some x.1, (hS_eq x.1).2 (Finset.mem_coe.1 x.2)⟩
        have hnone_notMem : noneS ∉ Kimg := by
          simp [Kimg, noneS]
        let K' : Finset (S : Set (Option V)) := insert noneS Kimg
        have hK'_card : K'.card = ω + 1 := by
          rw [Finset.card_insert_of_notMem hnone_notMem,
            Finset.card_image_of_injective _
              (fun a b hab => Subtype.ext (Option.some.inj (congrArg Subtype.val hab))),
            hK.2]
        have hK'_cl : (H.induce (S : Set (Option V))).IsClique (K' : Set (S : Set (Option V))) := by
          intro a ha b hb hab
          rw [Finset.mem_coe, Finset.mem_insert] at ha hb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact absurd rfl hab
          · rcases Finset.mem_image.1 hb with ⟨y, hy, rfl⟩
            change H.Adj none (some y.1)
            by_cases hyv : y.1 = v₀
            · exact Or.inl hyv
            · exact Or.inr (hK.1 hv₀K hy (fun h => hyv (congrArg Subtype.val h).symm))
          · rcases Finset.mem_image.1 ha with ⟨x, hx, rfl⟩
            change H.Adj (some x.1) none
            by_cases hxv : x.1 = v₀
            · exact Or.inl hxv
            · exact Or.inr (hK.1 hv₀K hx (fun h => hxv (congrArg Subtype.val h).symm))
          · rcases Finset.mem_image.1 ha with ⟨x, hx, rfl⟩
            rcases Finset.mem_image.1 hb with ⟨y, hy, rfl⟩
            have hxy : x ≠ y := fun h => hab (by subst h; rfl)
            exact hK.1 hx hy hxy
        have hω1_le : ω + 1 ≤ (H.induce (S : Set (Option V))).cliqueNum :=
          hK'_card ▸ card_clique_le_cliqueNum hK'_cl
        obtain ⟨c⟩ := colorable_cliqueNum_of_isPerfectGraph (isPerfectGraph_induce hG (T : Set V))
        refine SimpleGraph.Colorable.mono hω1_le ⟨SimpleGraph.Coloring.mk (fun x =>
          match x with
          | ⟨none, _⟩ => Fin.last ω
          | ⟨some u, hu⟩ => (c ⟨u, Finset.mem_coe.2 ((hS_eq u).1 (Finset.mem_coe.1 hu))⟩).castSucc)
          fun {a b} hadj => ?_⟩
        rcases a with ⟨a | u, ha⟩ <;> rcases b with ⟨b | w, hb⟩
        · exact absurd hadj id
        · exact (Fin.castSucc_ne_last _).symm
        · exact Fin.castSucc_ne_last _
        · simp only [ne_eq, Fin.castSucc_inj]
          exact c.valid hadj
      · -- Subcase B: `v₀` lies in no `ω`-clique of `G[T]`.
        obtain ⟨c⟩ := colorable_cliqueNum_of_isPerfectGraph (isPerfectGraph_induce hG (T : Set V))
        have hω_pos : 0 < ω := by
          have h1 : ({⟨v₀, Finset.mem_coe.2 hv₀T⟩} : Finset (T : Set V)).card ≤ ω :=
            card_clique_le_cliqueNum (by simp)
          simp at h1
          omega
        let c₀ : Fin ω := c ⟨v₀, Finset.mem_coe.2 hv₀T⟩
        let A : Finset V := T.filter fun u => ∃ hu : u ∈ T, c ⟨u, Finset.mem_coe.2 hu⟩ = c₀
        let A' : Finset V := A.erase v₀
        let T' : Finset V := T \ A'
        have hω'_lt : (G.induce (T' : Set V)).cliqueNum < ω := by
          by_contra hge
          push Not at hge
          obtain ⟨K', hK'⟩ := (G.induce (T' : Set V)).exists_isNClique_cliqueNum
          have hsub_le : ω ≤ K'.card := hK'.2 ▸ hge
          obtain ⟨K₀, hK₀_sub, hK₀_card⟩ := Finset.exists_subset_card_eq hsub_le
          let emb : ↥(T' : Set V) → ↥(T : Set V) := fun x =>
            ⟨x.1, Finset.mem_coe.2 (Finset.mem_sdiff.1 (Finset.mem_coe.1 x.2)).1⟩
          let K : Finset (T : Set V) := K₀.image emb
          have hK_card : K.card = ω := by
            have hemb_inj : Function.Injective emb :=
              fun a b hab => Subtype.ext (congrArg (Subtype.val : ↥(T : Set V) → V) hab)
            calc K.card = K₀.card := Finset.card_image_of_injective K₀ hemb_inj
              _ = ω := hK₀_card
          have hK_cl : (G.induce (T : Set V)).IsClique (K : Set (T : Set V)) := by
            intro a ha b hb hab
            rcases Finset.mem_image.1 (Finset.mem_coe.1 ha) with ⟨x, hx, rfl⟩
            rcases Finset.mem_image.1 (Finset.mem_coe.1 hb) with ⟨y, hy, rfl⟩
            exact hK'.1 (hK₀_sub hx) (hK₀_sub hy) (fun h => hab (by subst h; rfl))
          have hsurj := c.surjOn_of_card_le_isClique hK_cl (by simp [hK_card, ω])
          obtain ⟨z, hzK, hzc⟩ := hsurj (Set.mem_univ c₀)
          rcases Finset.mem_image.1 hzK with ⟨x, hxK₀, rfl⟩
          have hxT' : x.1 ∈ T' := Finset.mem_coe.1 x.2
          have hxA : x.1 ∈ A := Finset.mem_filter.2
            ⟨(Finset.mem_sdiff.1 hxT').1, (Finset.mem_sdiff.1 hxT').1, hzc⟩
          have hxv₀ : x.1 = v₀ := by
            by_contra hne
            exact (Finset.mem_sdiff.1 hxT').2 (Finset.mem_erase.2 ⟨hne, hxA⟩)
          refine hcl ⟨K, ⟨hK_cl, hK_card⟩, ?_⟩
          have hzv₀ : (⟨v₀, Finset.mem_coe.2 hv₀T⟩ : (T : Set V)) =
              ⟨x.1, Finset.mem_coe.2 (Finset.mem_sdiff.1 hxT').1⟩ :=
            Subtype.ext hxv₀.symm
          exact hzv₀ ▸ hzK
        have hω'_le : (G.induce (T' : Set V)).cliqueNum ≤ ω - 1 := by omega
        obtain ⟨c'⟩ := SimpleGraph.Colorable.mono hω'_le
          (colorable_cliqueNum_of_isPerfectGraph (isPerfectGraph_induce hG (T' : Set V)))
        have hω_eq : ω - 1 + 1 = ω := Nat.sub_add_cancel hω_pos
        refine SimpleGraph.Colorable.mono hω_le ⟨SimpleGraph.Coloring.mk (fun x =>
          finCongr hω_eq <|
            match x with
            | ⟨none, _⟩ => Fin.last (ω - 1)
            | ⟨some u, _⟩ =>
              if hu : u ∈ T' then (c' ⟨u, Finset.mem_coe.2 hu⟩).castSucc
              else Fin.last (ω - 1)) fun {a b} hadj => ?_⟩
        have hA'_not_adj_v₀ : ∀ u ∈ A', u ≠ v₀ ∧ ¬ G.Adj v₀ u := by
          intro u hu
          have hne := (Finset.mem_erase.1 hu).1
          have ⟨huT, _, hcu⟩ := Finset.mem_filter.1 (Finset.mem_erase.1 hu).2
          refine ⟨hne, fun hadj => c.valid (v := ⟨v₀, Finset.mem_coe.2 hv₀T⟩)
            (w := ⟨u, Finset.mem_coe.2 huT⟩) hadj hcu.symm⟩
        have hA'_indep : ∀ u ∈ A', ∀ w ∈ A', ¬ G.Adj u w := by
          intro u hu w hw hadj
          have ⟨huT, _, hcu⟩ := Finset.mem_filter.1 (Finset.mem_erase.1 hu).2
          have ⟨hwT, _, hcw⟩ := Finset.mem_filter.1 (Finset.mem_erase.1 hw).2
          exact c.valid (v := ⟨u, Finset.mem_coe.2 huT⟩) (w := ⟨w, Finset.mem_coe.2 hwT⟩)
            hadj (hcu.trans hcw.symm)
        simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
        rcases a with ⟨a | u, ha⟩ <;> rcases b with ⟨b | w, hb⟩
        · exact absurd hadj id
        · have hwT : w ∈ T := (hS_eq w).1 (Finset.mem_coe.1 hb)
          have hwT' : w ∈ T' := by
            refine Finset.mem_sdiff.2 ⟨hwT, fun hwA' => ?_⟩
            rcases hadj with rfl | hvw
            · exact (hA'_not_adj_v₀ w hwA').1 rfl
            · exact (hA'_not_adj_v₀ w hwA').2 hvw
          simp only [hwT', ↓reduceDIte]
          exact (Fin.castSucc_ne_last _).symm
        · have huT : u ∈ T := (hS_eq u).1 (Finset.mem_coe.1 ha)
          have huT' : u ∈ T' := by
            refine Finset.mem_sdiff.2 ⟨huT, fun huA' => ?_⟩
            rcases hadj with rfl | hvu
            · exact (hA'_not_adj_v₀ u huA').1 rfl
            · exact (hA'_not_adj_v₀ u huA').2 hvu
          simp only [huT', ↓reduceDIte]
          exact Fin.castSucc_ne_last _
        · have huT : u ∈ T := (hS_eq u).1 (Finset.mem_coe.1 ha)
          have hwT : w ∈ T := (hS_eq w).1 (Finset.mem_coe.1 hb)
          by_cases hu : u ∈ T' <;> by_cases hw : w ∈ T'
          · simp only [hu, hw, ↓reduceDIte, Fin.castSucc_inj]
            exact c'.valid hadj
          · simp only [hu, hw, ↓reduceDIte]
            exact Fin.castSucc_ne_last _
          · simp only [hu, hw, ↓reduceDIte]
            exact (Fin.castSucc_ne_last _).symm
          · exfalso
            have huA' : u ∈ A' := by
              by_contra h; exact hu (Finset.mem_sdiff.2 ⟨huT, h⟩)
            have hwA' : w ∈ A' := by
              by_contra h; exact hw (Finset.mem_sdiff.2 ⟨hwT, h⟩)
            exact hA'_indep u huA' w hwA' hadj
    · -- `none ∈ S`, `some v₀ ∉ S`: send `none ↦ v₀`, `some u ↦ u`.
      let f : Option V → V := fun o => o.getD v₀
      let T : Finset V := S.image f
      have hf_inj : Set.InjOn f (S : Set (Option V)) := by
        intro a ha b hb hab
        cases a <;> cases b
        · rfl
        · rename_i w
          simp only [f, Option.getD_none, Option.getD_some] at hab
          exact absurd (hab ▸ Finset.mem_coe.1 hb) hv₀
        · rename_i u
          simp only [f, Option.getD_none, Option.getD_some] at hab
          exact absurd (hab.symm ▸ Finset.mem_coe.1 ha) hv₀
        · simp only [f, Option.getD_some] at hab; exact congrArg some hab
      let iso : H.induce (S : Set (Option V)) ≃g G.induce (T : Set V) :=
        { toFun := fun x => ⟨f x.1,
          Finset.mem_coe.2 (Finset.mem_image_of_mem f (Finset.mem_coe.1 x.2))⟩
          invFun := fun y =>
            let h := Finset.mem_image.1 (Finset.mem_coe.1 y.2)
            ⟨h.choose, Finset.mem_coe.2 h.choose_spec.1⟩
          left_inv := fun x => by
            apply Subtype.ext
            have h := Finset.mem_image.1 (Finset.mem_coe.1
              (Finset.mem_coe.2 (Finset.mem_image_of_mem f (Finset.mem_coe.1 x.2))))
            exact hf_inj (Finset.mem_coe.2 h.choose_spec.1) x.2 h.choose_spec.2
          right_inv := fun y => by
            apply Subtype.ext
            exact (Finset.mem_image.1 (Finset.mem_coe.1 y.2)).choose_spec.2
          map_rel_iff' := fun {a b} => by
            change G.Adj (f a.1) (f b.1) ↔ H.Adj a.1 b.1
            cases ha : a.1 <;> cases hb : b.1
            · simp [f, H, dupGraph]
            · rename_i w
              have hw : w ≠ v₀ := fun h => hv₀ (h ▸ hb ▸ Finset.mem_coe.1 b.2)
              simp [f, H, dupGraph, hw]
            · rename_i u
              have hu : u ≠ v₀ := fun h => hv₀ (h ▸ ha ▸ Finset.mem_coe.1 a.2)
              simp [f, H, dupGraph, hu, SimpleGraph.adj_comm]
            · simp [f, H, dupGraph] }
      change (H.induce (S : Set (Option V))).Colorable (H.induce (S : Set (Option V))).cliqueNum
      rw [SimpleGraph.colorable_congr iso, cliqueNum_congr iso]
      exact colorable_cliqueNum_of_isPerfectGraph (isPerfectGraph_induce hG (T : Set V))
  · -- `none ∉ S`: send `some u ↦ u`.
    let T : Finset V := S.preimage some (fun _ _ _ _ h => Option.some.inj h)
    let iso : H.induce (S : Set (Option V)) ≃g G.induce (T : Set V) :=
      { toFun := fun x =>
          match h : x.1 with
          | none => absurd (h ▸ Finset.mem_coe.1 x.2) hnone
          | some u => ⟨u, Finset.mem_coe.2 (Finset.mem_preimage.2 (h ▸ Finset.mem_coe.1 x.2))⟩
        invFun := fun y => ⟨some y.1,
          Finset.mem_coe.2 (Finset.mem_preimage.1 (Finset.mem_coe.1 y.2))⟩
        left_inv := fun x => by
          rcases x with ⟨_ | u, hx⟩
          · exact absurd (Finset.mem_coe.1 hx) hnone
          · rfl
        right_inv := fun y => by apply Subtype.ext; simp
        map_rel_iff' := fun {a b} => by
          rcases a with ⟨_ | u, ha⟩
          · exact absurd (Finset.mem_coe.1 ha) hnone
          · rcases b with ⟨_ | w, hb⟩
            · exact absurd (Finset.mem_coe.1 hb) hnone
            · rfl }
    change (H.induce (S : Set (Option V))).Colorable (H.induce (S : Set (Option V))).cliqueNum
    rw [SimpleGraph.colorable_congr iso, cliqueNum_congr iso]
    exact colorable_cliqueNum_of_isPerfectGraph (isPerfectGraph_induce hG (T : Set V))

/-- True-twin weight replication of `G` with weights `w : V → ℕ`: replaces each vertex `v` by a
clique of size `w v` of true twins. -/
def trueWeightRep (G : SimpleGraph V) (w : V → ℕ) : SimpleGraph ((v : V) × Fin (w v)) where
  Adj p q := G.Adj p.1 q.1 ∨ (p.1 = q.1 ∧ p.2.1 ≠ q.2.1)
  symm := ⟨fun p q h => by
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (G.adj_symm h)
    · exact Or.inr ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun p h => by
    rcases h with h | ⟨_, h2⟩
    · exact G.loopless.irrefl p.1 h
    · exact h2 rfl⟩

/-- **Lovász's Replication Lemma (weighted form)**: true-twin weight replication preserves
perfection for every weight function `w : V → ℕ` on a finite perfect graph. -/
theorem isPerfectGraph_trueWeightRep [Finite V] {G : SimpleGraph V}
    (hG : IsPerfectGraph G) (w : V → ℕ) :
    IsPerfectGraph (trueWeightRep G w) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  -- Prove by strong induction on `N = ∑ v, w v`.
  suffices h : ∀ N : ℕ, ∀ (w : V → ℕ), (∑ v : V, w v) ≤ N → IsPerfectGraph (trueWeightRep G w) from
    h (∑ v : V, w v) w le_rfl
  intro N
  induction N with
  | zero =>
    intro w hw
    have hw0 : ∀ v, w v = 0 := fun v => by
      have hle : w v ≤ ∑ u : V, w u :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
      omega
    intro S
    have hS : S = ∅ := by
      ext p
      have h1 := p.2.isLt
      have h2 := hw0 p.1
      omega
    subst hS
    have : IsEmpty ↑((∅ : Finset ((v : V) × Fin (w v))) : Set ((v : V) × Fin (w v))) :=
      ⟨fun ⟨_, hx⟩ => by simp at hx⟩
    have hch : ((trueWeightRep G w).induce
        ((∅ : Finset ((v : V) × Fin (w v))) : Set _)).chromaticNumber = 0 := by
      rw [← le_zero_iff]
      change ((trueWeightRep G w).induce
        ((∅ : Finset ((v : V) × Fin (w v))) : Set _)).chromaticNumber ≤ (0 : ℕ)
      rw [SimpleGraph.chromaticNumber_le_iff_colorable]
      exact SimpleGraph.Colorable.of_isEmpty 0
    have hcl : ((trueWeightRep G w).induce
        ((∅ : Finset ((v : V) × Fin (w v))) : Set _)).cliqueNum = 0 :=
      SimpleGraph.cliqueNum_of_isEmpty _
    rw [hch, hcl, Nat.cast_zero]
  | succ N ih =>
    intro w hw
    by_cases hgt : ∃ v₀ : V, 2 ≤ w v₀
    · obtain ⟨v₀, hv₀⟩ := hgt
      let w' : V → ℕ := Function.update w v₀ (w v₀ - 1)
      have hw'_sum : ∑ v : V, w' v ≤ N := by
        have hsplit : ∑ v : V, w' v + 1 = ∑ v : V, w v := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v₀),
            ← Finset.add_sum_erase _ w (Finset.mem_univ v₀)]
          have hrest : ∑ v ∈ Finset.univ.erase v₀, w' v = ∑ v ∈ Finset.univ.erase v₀, w v :=
            Finset.sum_congr rfl fun v hv => Function.update_of_ne (Finset.mem_erase.1 hv).1 _ _
          have hself : w' v₀ = w v₀ - 1 := Function.update_self v₀ (w v₀ - 1) w
          rw [hrest, hself]
          omega
        omega
      have hperf' : IsPerfectGraph (trueWeightRep G w') := ih w' hw'_sum
      have hdup := isPerfectGraph_dup hperf' ⟨v₀, ⟨0, by simp [w']; omega⟩⟩
      let e : Option ((v : V) × Fin (w' v)) ≃ ((v : V) × Fin (w v)) :=
        { toFun := fun o =>
            match o with
            | none => ⟨v₀, ⟨w v₀ - 1, by omega⟩⟩
            | some ⟨v, i⟩ =>
              if h : v = v₀ then
                ⟨v₀, ⟨i.1, by have := i.2; simp [w', h] at this; omega⟩⟩
              else
                ⟨v, ⟨i.1, by have := i.2; simpa [w', h] using this⟩⟩
          invFun := fun ⟨v, i⟩ =>
            if h : v = v₀ then
              if hi : i.1 < w v₀ - 1 then
                some ⟨v₀, ⟨i.1, by simp [w', hi]⟩⟩
              else
                none
            else
              some ⟨v, ⟨i.1, by simp [w', h]⟩⟩
          left_inv := fun o => by
            cases o with
            | none => simp
            | some p =>
              rcases p with ⟨v, i⟩
              by_cases h : v = v₀
              · subst h
                have hi : i.1 < w v - 1 := by simpa [w'] using i.2
                dsimp only
                rw [dite_eq_left rfl, dite_eq_left rfl, dite_eq_left hi]
              · dsimp only
                rw [dite_eq_right h, dite_eq_right h]
          right_inv := fun ⟨v, i⟩ => by
            by_cases h : v = v₀
            · subst h
              by_cases hi : i.1 < w v - 1
              · simp [hi]
              · have heq : i.1 = w v - 1 := by omega
                simp only [↓reduceDIte, hi]
                exact Sigma.ext rfl (heq_of_eq (Fin.ext heq.symm))
            · simp [h] }
      let iso : dupGraph (trueWeightRep G w') ⟨v₀, ⟨0, by simp [w']; omega⟩⟩ ≃g
          trueWeightRep G w :=
        { toEquiv := e
          map_rel_iff' := fun {a b} => by
            cases a with
            | none =>
              cases b with
              | none => simp [dupGraph, trueWeightRep, e]
              | some q =>
                rcases q with ⟨v, j⟩
                by_cases h : v = v₀
                · subst h
                  have hj : j.1 < w v - 1 := by simpa [w'] using j.2
                  have hne : w v - 1 ≠ j.1 := by omega
                  simp only [dupGraph, trueWeightRep, e, Equiv.coe_fn_mk, ↓reduceDIte,
                    G.loopless.irrefl, false_or, true_and, hne, ne_eq, not_false_eq_true, true_iff]
                  by_cases hj0 : j.1 = 0
                  · left; exact Sigma.ext rfl (heq_of_eq (Fin.ext hj0))
                  · right; exact Ne.symm hj0
                · simp [dupGraph, trueWeightRep, e, h, Ne.symm h]
            | some p =>
              rcases p with ⟨u, i⟩
              cases b with
              | none =>
                by_cases h : u = v₀
                · subst h
                  have hi : i.1 < w u - 1 := by simpa [w'] using i.2
                  have hne : i.1 ≠ w u - 1 := by omega
                  simp only [dupGraph, trueWeightRep, e, Equiv.coe_fn_mk, ↓reduceDIte,
                    G.loopless.irrefl, false_or, true_and, hne, ne_eq, not_false_eq_true, true_iff]
                  by_cases hi0 : i.1 = 0
                  · left; exact Sigma.ext rfl (heq_of_eq (Fin.ext hi0))
                  · right; exact Ne.symm hi0
                · simp [dupGraph, trueWeightRep, e, h, Ne.symm h, SimpleGraph.adj_comm]
              | some q =>
                rcases q with ⟨v, j⟩
                by_cases hu : u = v₀ <;> by_cases hv : v = v₀
                · subst hu; subst hv
                  simp [dupGraph, trueWeightRep, e]
                · subst hu; simp [dupGraph, trueWeightRep, e, hv]
                · subst hv; simp [dupGraph, trueWeightRep, e, hu]
                · simp [dupGraph, trueWeightRep, e, hu, hv] }
      exact isPerfectGraph_of_iso iso hdup
    · -- Every vertex has `w v ≤ 1`, so `trueWeightRep G w` is an induced subgraph of `G`.
      push Not at hgt
      let U : Set V := {v | w v = 1}
      let iso : G.induce U ≃g trueWeightRep G w :=
        { toFun := fun v => ⟨v.1, ⟨0, by have hv : w v.1 = 1 := v.2; omega⟩⟩
          invFun := fun p => ⟨p.1, by have h1 := hgt p.1; have h2 := p.2.isLt; simp [U]; omega⟩
          left_inv := fun v => Subtype.ext rfl
          right_inv := fun ⟨v, i⟩ => by
            have h1 := hgt v
            have h2 := i.isLt
            have hi0 : i.1 = 0 := by omega
            exact Sigma.ext rfl (heq_of_eq (Fin.ext hi0.symm))
          map_rel_iff' := fun {a b} => by
            simp [trueWeightRep] }
      exact isPerfectGraph_of_iso iso (isPerfectGraph_induce hG U)

end ReplicationLemma

/-! ### Lovász's Weak Perfect Graph Theorem -/

section WeakPerfectGraphTheorem

variable {V : Type*}

/-- Key lemma for Lovász's Weak Perfect Graph Theorem: in any nonempty finite perfect graph `G`,
some clique `K` intersects every maximum independent set of `G`. -/
private lemma exists_clique_hitting_max_indep [Finite V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} (hG : IsPerfectGraph G) :
    ∃ K : Finset V, G.IsClique (K : Set V) ∧
      ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.card = Gᶜ.cliqueNum → (K ∩ I).Nonempty := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  set α := Gᶜ.cliqueNum
  have hα_pos : 0 < α := by
    obtain ⟨v₀⟩ := ‹Nonempty V›
    have h1 : ({v₀} : Finset V).card ≤ α :=
      card_clique_le_cliqueNum (G := Gᶜ) (by simp)
    simp at h1
    omega
  by_contra h
  push Not at h
  have hdisj : ∀ K : {K : Finset V // G.IsClique (K : Set V)},
      ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ I.card = α ∧ Disjoint K.1 I := fun K => by
    obtain ⟨I, hI_ind, hI_card, hI_empty⟩ := h K.1 K.2
    exact ⟨I, hI_ind, hI_card, Finset.disjoint_iff_inter_eq_empty.2 hI_empty⟩
  choose I hI_ind hI_card hI_disj using hdisj
  let C : Finset {K : Finset V // G.IsClique (K : Set V)} := Finset.univ
  let w : V → ℕ := fun v => (C.filter fun K => v ∈ I K).card
  let H := trueWeightRep G w
  have hH_perf : IsPerfectGraph H := isPerfectGraph_trueWeightRep hG w
  obtain ⟨c⟩ := colorable_cliqueNum_of_isPerfectGraph hH_perf
  -- Bound `|V(H)|` from above by `ω(H) * α`.
  have hcard_le : Fintype.card ((v : V) × Fin (w v)) ≤ H.cliqueNum * α := by
    let fiber (a : Fin H.cliqueNum) : Finset ((v : V) × Fin (w v)) :=
      Finset.univ.filter fun p => c p = a
    have hpart : Fintype.card ((v : V) × Fin (w v)) =
        ∑ a : Fin H.cliqueNum, (fiber a).card := by
      have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := c)
        (fun _ _ => Finset.mem_univ _)
      simpa [fiber] using this
    rw [hpart]
    calc ∑ a : Fin H.cliqueNum, (fiber a).card
        ≤ ∑ _a : Fin H.cliqueNum, α := by
          refine Finset.sum_le_sum fun a _ => ?_
          have hinj : Set.InjOn Sigma.fst (fiber a : Set ((v : V) × Fin (w v))) := by
            intro p hp q hq hpq
            by_contra hne
            have hcp : c p = a := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
            have hcq : c q = a := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
            have hp2 : p.2.1 ≠ q.2.1 := fun heq => by
              rcases p with ⟨v₁, i₁⟩
              rcases q with ⟨v₂, i₂⟩
              dsimp only at hpq heq
              subst hpq
              exact hne (congrArg (Sigma.mk v₁) (Fin.ext heq))
            exact c.valid (Or.inr ⟨hpq, hp2⟩) (hcp.trans hcq.symm)
          have himg_ind : Gᶜ.IsClique (((fiber a).image Sigma.fst : Finset V) : Set V) := by
            intro u hu v hv huv
            rcases Finset.mem_image.1 (Finset.mem_coe.1 hu) with ⟨p, hp, rfl⟩
            rcases Finset.mem_image.1 (Finset.mem_coe.1 hv) with ⟨q, hq, rfl⟩
            have hcp : c p = a := (Finset.mem_filter.1 hp).2
            have hcq : c q = a := (Finset.mem_filter.1 hq).2
            exact ⟨huv, fun hadj => c.valid (Or.inl hadj) (hcp.trans hcq.symm)⟩
          calc (fiber a).card = ((fiber a).image Sigma.fst).card :=
                (Finset.card_image_of_injOn hinj).symm
            _ ≤ α := card_clique_le_cliqueNum himg_ind
      _ = H.cliqueNum * α := by simp
  -- Compute `|V(H)| = |C| * α`.
  have hcard_eq : Fintype.card ((v : V) × Fin (w v)) = C.card * α := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, w]
    calc ∑ v : V, (C.filter fun K => v ∈ I K).card
        = ∑ v : V, ∑ K ∈ C, if v ∈ I K then 1 else 0 := by
            refine Finset.sum_congr rfl fun v _ => ?_
            simp [Finset.sum_boole]
      _ = ∑ K ∈ C, ∑ v : V, if v ∈ I K then 1 else 0 := Finset.sum_comm
      _ = ∑ K ∈ C, (I K).card := by
            refine Finset.sum_congr rfl fun K _ => by simp
      _ = ∑ _K ∈ C, α := Finset.sum_congr rfl fun K _ => hI_card K
      _ = C.card * α := by simp
  have hC_le : C.card ≤ H.cliqueNum :=
    Nat.le_of_mul_le_mul_right (hcard_eq ▸ hcard_le) hα_pos
  -- Project a maximum clique `Q` of `H` to a clique `K₀` of `G` and double-count `∑_{v ∈ K₀} w v`.
  obtain ⟨Q, hQ⟩ := H.exists_isNClique_cliqueNum
  let K₀ : Finset V := Q.image Sigma.fst
  have hK₀_cl : G.IsClique (K₀ : Set V) := by
    intro u hu v hv huv
    rcases Finset.mem_image.1 (Finset.mem_coe.1 hu) with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.1 (Finset.mem_coe.1 hv) with ⟨q, hq, rfl⟩
    have hpq : p ≠ q := fun h => huv (congrArg Sigma.fst h)
    rcases hQ.1 hp hq hpq with hadj | ⟨heq, _⟩
    · exact hadj
    · exact absurd heq huv
  have hQ_sub : Q ⊆ K₀.sigma fun v => (Finset.univ : Finset (Fin (w v))) := fun p hp =>
    Finset.mem_sigma.2 ⟨Finset.mem_image_of_mem Sigma.fst hp, Finset.mem_univ _⟩
  have hω_le : H.cliqueNum ≤ ∑ v ∈ K₀, w v :=
    hQ.2 ▸ (Finset.card_le_card hQ_sub).trans_eq (by simp [Finset.card_sigma])
  have hdouble : ∑ v ∈ K₀, w v = ∑ K ∈ C, (K₀ ∩ I K).card := by
    calc ∑ v ∈ K₀, (C.filter fun K => v ∈ I K).card
        = ∑ v ∈ K₀, ∑ K ∈ C, if v ∈ I K then 1 else 0 := by
            refine Finset.sum_congr rfl fun v _ => by simp [Finset.sum_boole]
      _ = ∑ K ∈ C, ∑ v ∈ K₀, if v ∈ I K then 1 else 0 := Finset.sum_comm
      _ = ∑ K ∈ C, (K₀ ∩ I K).card := by
            refine Finset.sum_congr rfl fun K _ => by simp
  let K₀' : {K : Finset V // G.IsClique (K : Set V)} := ⟨K₀, hK₀_cl⟩
  have hsum_lt : ∑ K ∈ C, (K₀ ∩ I K).card < C.card := by
    have hK₀'_mem : K₀' ∈ C := Finset.mem_univ _
    rw [← Finset.add_sum_erase _ _ hK₀'_mem]
    have h0 : (K₀ ∩ I K₀').card = 0 :=
      Finset.card_eq_zero.2 (Finset.disjoint_iff_inter_eq_empty.1 (hI_disj K₀'))
    have hrest : ∑ K ∈ C.erase K₀', (K₀ ∩ I K).card ≤ (C.erase K₀').card := by
      calc ∑ K ∈ C.erase K₀', (K₀ ∩ I K).card
          ≤ ∑ _K ∈ C.erase K₀', 1 :=
            Finset.sum_le_sum fun K _ => card_inter_le_one_of_isClique_isIndepSet hK₀_cl (hI_ind K)
        _ = (C.erase K₀').card := by simp
    have hcard_erase : (C.erase K₀').card + 1 = C.card :=
      Finset.card_erase_add_one hK₀'_mem
    omega
  omega

/-- **Lovász's Weak Perfect Graph Theorem**: the complement of a perfect graph is
perfect.
-/
theorem isPerfectGraph_compl {G : SimpleGraph V} (hG : IsPerfectGraph G) :
    IsPerfectGraph Gᶜ := by
  classical
  -- Prove `Gᶜ.Colorable Gᶜ.cliqueNum` for all finite perfect graphs by strong induction on `|V|`.
  suffices hmain : ∀ n : ℕ, ∀ (W : Type _) [Fintype W] (H : SimpleGraph W),
      Fintype.card W ≤ n → IsPerfectGraph H → Hᶜ.Colorable Hᶜ.cliqueNum by
    intro S
    refine le_antisymm ?_ SimpleGraph.cliqueNum_le_chromaticNumber
    rw [SimpleGraph.chromaticNumber_le_iff_colorable]
    have hH : IsPerfectGraph (G.induce (S : Set V)) := isPerfectGraph_induce hG (S : Set V)
    have hiso : (Gᶜ).induce (S : Set V) ≃g (G.induce (S : Set V))ᶜ :=
      { toEquiv := Equiv.refl _
        map_rel_iff' := fun {a b} => by
          simp only [Equiv.refl_apply, SimpleGraph.compl_adj, SimpleGraph.induce_adj, ne_eq,
            Subtype.ext_iff] }
    rw [SimpleGraph.colorable_congr hiso, cliqueNum_congr hiso]
    exact hmain (Fintype.card (S : Set V)) (S : Set V) (G.induce (S : Set V)) le_rfl hH
  intro n
  induction n with
  | zero =>
    intro W _ H hW _
    have : IsEmpty W := Fintype.card_eq_zero_iff.1 (Nat.eq_zero_of_le_zero hW)
    exact SimpleGraph.Colorable.of_isEmpty _
  | succ n ih =>
    intro W _ H hW hH
    by_cases hempty : IsEmpty W
    · exact SimpleGraph.Colorable.of_isEmpty _
    · rw [not_isEmpty_iff] at hempty
      obtain ⟨K, hK_cl, hK_hit⟩ := exists_clique_hitting_max_indep hH
      have hK_ne : K.Nonempty := by
        obtain ⟨I, hI⟩ := Hᶜ.exists_isNClique_cliqueNum
        have hI_ind : H.IsIndepSet (I : Set W) := H.isClique_compl.1 hI.1
        obtain ⟨v, hv⟩ := hK_hit I hI_ind hI.2
        exact ⟨v, (Finset.mem_inter.1 hv).1⟩
      let U : Set W := (K : Set W)ᶜ
      have hU_card : Fintype.card U ≤ n := by
        have hcard : Fintype.card U + K.card = Fintype.card W := by
          have hc : Fintype.card U = Fintype.card W - Fintype.card {v : W // v ∈ K} :=
            Fintype.card_subtype_compl (fun v => v ∈ K)
          rw [hc, Fintype.card_coe]
          exact Nat.sub_add_cancel (Finset.card_le_univ K)
        have hKpos : 0 < K.card := hK_ne.card_pos
        omega
      have hα_pos : 0 < Hᶜ.cliqueNum := by
        obtain ⟨v₀⟩ := hempty
        have h1 : ({v₀} : Finset W).card ≤ Hᶜ.cliqueNum :=
          card_clique_le_cliqueNum (G := Hᶜ) (by simp)
        simp only [Finset.card_singleton] at h1
        omega
      have hU_cl_lt : ((H.induce U)ᶜ).cliqueNum < Hᶜ.cliqueNum := by
        by_contra hge
        push Not at hge
        obtain ⟨I', hI'⟩ := ((H.induce U)ᶜ).exists_isNClique_cliqueNum
        obtain ⟨I₀, hI₀_sub, hI₀_card⟩ := Finset.exists_subset_card_eq (hI'.2 ▸ hge)
        let I : Finset W := I₀.image Subtype.val
        have hI_card : I.card = Hᶜ.cliqueNum := by
          rw [Finset.card_image_of_injective _ Subtype.val_injective, hI₀_card]
        have hI_ind : H.IsIndepSet (I : Set W) := by
          intro u hu v hv huv hadj
          rcases Finset.mem_image.1 (Finset.mem_coe.1 hu) with ⟨x, hx, rfl⟩
          rcases Finset.mem_image.1 (Finset.mem_coe.1 hv) with ⟨y, hy, rfl⟩
          have hxy : x ≠ y := fun h => huv (congrArg Subtype.val h)
          exact (hI'.1 (hI₀_sub hx) (hI₀_sub hy) hxy).2 hadj
        obtain ⟨v, hv⟩ := hK_hit I hI_ind hI_card
        rcases Finset.mem_image.1 (Finset.mem_inter.1 hv).2 with ⟨x, _, rfl⟩
        exact x.2 (Finset.mem_coe.2 (Finset.mem_inter.1 hv).1)
      have hU_col : ((H.induce U)ᶜ).Colorable (Hᶜ.cliqueNum - 1) :=
        SimpleGraph.Colorable.mono (by omega)
          (ih U (H.induce U) hU_card (isPerfectGraph_induce hH U))
      obtain ⟨c⟩ := hU_col
      have hα_eq : Hᶜ.cliqueNum - 1 + 1 = Hᶜ.cliqueNum := Nat.sub_add_cancel hα_pos
      refine ⟨SimpleGraph.Coloring.mk (fun v =>
        finCongr hα_eq <|
          if hv : v ∈ K then Fin.last (Hᶜ.cliqueNum - 1)
          else (c ⟨v, hv⟩).castSucc) fun {u v} hadj => ?_⟩
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
      by_cases hu : u ∈ K <;> by_cases hv : v ∈ K
      · exact absurd (hK_cl hu hv hadj.1) hadj.2
      · simp only [hu, hv, ↓reduceDIte]
        exact (Fin.castSucc_ne_last _).symm
      · simp only [hu, hv, ↓reduceDIte]
        exact Fin.castSucc_ne_last _
      · simp only [hu, hv, ↓reduceDIte, Fin.castSucc_inj]
        exact c.valid ⟨fun h => hadj.1 (congrArg Subtype.val h), hadj.2⟩

end WeakPerfectGraphTheorem

/-! ### Chvátal–Lovász Polyhedral Characterization `STAB(G) = QSTAB(G)` -/

section ChvatalLovasz

variable {V : Type*}

/-- Every stable set incidence vector belongs to `QSTAB(G)`. -/
theorem stabPolytope_subset_qstabPolytope [DecidableEq V] (G : SimpleGraph V) :
    stabPolytope ℝ G ⊆ qstabPolytope G := by
  have hconv : Convex ℝ (qstabPolytope G) := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun v => add_nonneg (mul_nonneg ha (hx.1 v)) (mul_nonneg hb (hy.1 v)), fun K hK => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    calc a * ∑ v ∈ K, x v + b * ∑ v ∈ K, y v
        ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2 K hK) ha)
            (mul_le_mul_of_nonneg_left (hy.2 K hK) hb)
      _ = 1 := by linarith
  refine convexHull_min ?_ hconv
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  refine ⟨fun v => by simp only [stabVertex]; split_ifs <;> norm_num, fun K hK => ?_⟩
  have hsum : ∑ v ∈ K, stabVertex ℝ S v = ((K ∩ S).card : ℝ) := by
    simp [stabVertex]
  rw [hsum]
  exact_mod_cast card_inter_le_one_of_isClique_isIndepSet hK hS

/-- Weighted clique-cover bound on finite perfect graphs under standard Lean axioms. -/
private lemma sum_natWeight_mul_le_of_isPerfectGraph [Fintype V] {G : SimpleGraph V}
    (hG : IsPerfectGraph G) (w : V → ℕ) {M : ℕ}
    (hM : ∀ I : Finset V, G.IsIndepSet (I : Set V) → ∑ v ∈ I, w v ≤ M)
    {x : V → ℝ} (hx : x ∈ qstabPolytope G) :
    ∑ v : V, (w v : ℝ) * x v ≤ (M : ℝ) := by
  classical
  let H := trueWeightRep Gᶜ w
  have hH_perf : IsPerfectGraph H := isPerfectGraph_trueWeightRep (isPerfectGraph_compl hG) w
  have hcl_le : H.cliqueNum ≤ M := by
    obtain ⟨S, hS⟩ := H.exists_isNClique_cliqueNum
    let I : Finset V := S.image Sigma.fst
    have hI : G.IsIndepSet (I : Set V) := by
      intro u hu v hv huv hadj
      rcases Finset.mem_image.1 (Finset.mem_coe.1 hu) with ⟨p, hp, rfl⟩
      rcases Finset.mem_image.1 (Finset.mem_coe.1 hv) with ⟨q, hq, rfl⟩
      have hpq : p ≠ q := fun h => huv (congrArg Sigma.fst h)
      rcases hS.1 hp hq hpq with ⟨_, hnadj⟩ | ⟨heq, _⟩
      · exact hnadj hadj
      · exact absurd heq huv
    have hsub : S ⊆ I.sigma fun v => (Finset.univ : Finset (Fin (w v))) := fun p hp =>
      Finset.mem_sigma.2 ⟨Finset.mem_image_of_mem Sigma.fst hp, Finset.mem_univ _⟩
    have hcard : S.card ≤ ∑ v ∈ I, w v :=
      (Finset.card_le_card hsub).trans_eq (by simp [Finset.card_sigma])
    exact hS.2 ▸ hcard.trans (hM I hI)
  obtain ⟨c⟩ := SimpleGraph.Colorable.mono hcl_le (colorable_cliqueNum_of_isPerfectGraph hH_perf)
  let fiber (a : Fin M) : Finset ((v : V) × Fin (w v)) := Finset.univ.filter fun p => c p = a
  have hfiber_sum : ∀ a : Fin M, ∑ p ∈ fiber a, x p.1 ≤ 1 := fun a => by
    have hinj : Set.InjOn Sigma.fst (fiber a : Set ((v : V) × Fin (w v))) := by
      intro p hp q hq hpq
      by_contra hne
      have hcp : c p = a := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
      have hcq : c q = a := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
      have hp2 : p.2.1 ≠ q.2.1 := fun heq => by
        rcases p with ⟨v₁, i₁⟩
        rcases q with ⟨v₂, i₂⟩
        dsimp only at hpq heq
        subst hpq
        exact hne (congrArg (Sigma.mk v₁) (Fin.ext heq))
      exact c.valid (Or.inr ⟨hpq, hp2⟩) (hcp.trans hcq.symm)
    let K : Finset V := (fiber a).image Sigma.fst
    have hK : G.IsClique (K : Set V) := by
      intro u hu v hv huv
      rcases Finset.mem_image.1 (Finset.mem_coe.1 hu) with ⟨p, hp, rfl⟩
      rcases Finset.mem_image.1 (Finset.mem_coe.1 hv) with ⟨q, hq, rfl⟩
      have hcp : c p = a := (Finset.mem_filter.1 hp).2
      have hcq : c q = a := (Finset.mem_filter.1 hq).2
      by_contra hnadj
      exact c.valid (Or.inl ⟨huv, hnadj⟩) (hcp.trans hcq.symm)
    have heq : ∑ p ∈ fiber a, x p.1 = ∑ v ∈ K, x v := (Finset.sum_image hinj).symm
    exact heq ▸ hx.2 K hK
  have hsum_sigma : ∑ v : V, (w v : ℝ) * x v = ∑ p : (v : V) × Fin (w v), x p.1 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun v _ => by simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsum_sigma]
  have hpart : ∑ p : (v : V) × Fin (w v), x p.1 = ∑ a : Fin M, ∑ p ∈ fiber a, x p.1 := by
    simpa [fiber] using (Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.univ) (g := c) (f := fun p => x p.1)
      (fun _ _ => Finset.mem_univ _)).symm
  rw [hpart]
  calc ∑ a : Fin M, ∑ p ∈ fiber a, x p.1
      ≤ ∑ _a : Fin M, (1 : ℝ) := Finset.sum_le_sum fun a _ => hfiber_sum a
    _ = (M : ℝ) := by simp

/-- **Chvátal–Lovász Polyhedral Theorem for Perfect Graphs**: for every finite perfect graph
`G`, `STAB(G) = QSTAB(G)`. -/
theorem isPerfectGraph_imp_stabPolytope_eq_qstabPolytope [Finite V] [DecidableEq V]
    {G : SimpleGraph V} (hG : IsPerfectGraph G) :
    stabPolytope ℝ G = qstabPolytope G := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  refine Set.Subset.antisymm (stabPolytope_subset_qstabPolytope G) fun x hx => ?_
  by_contra hxS
  have hclosed : IsClosed (stabPolytope ℝ G) :=
    ((Set.finite_range _).isCompact_convexHull (𝕜 := ℝ)).isClosed
  obtain ⟨f, u, hfu, hux⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hclosed hxS
  let r : V → ℝ := fun v => f (Pi.single v (1 : ℝ))
  have hf_eq : ∀ y : V → ℝ, f y = ∑ v : V, r v * y v := fun y => by
    have hy : y = ∑ v : V, y v • Pi.single v (1 : ℝ) := by
      ext v; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    refine Finset.sum_congr rfl fun v _ => by rw [map_smul, smul_eq_mul, mul_comm]
  let r' : V → ℝ := fun v => max (r v) 0
  have hr'_nonneg : ∀ v : V, 0 ≤ r' v := fun v => le_max_right _ _
  have hr'_x : u < ∑ v : V, r' v * x v :=
    calc u < f x := hux
      _ = ∑ v : V, r v * x v := hf_eq x
      _ ≤ ∑ v : V, r' v * x v :=
          Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hx.1 v)
  have hr'_indep : ∀ I : Finset V, G.IsIndepSet (I : Set V) → ∑ v ∈ I, r' v < u := fun I hI => by
    let I' : Finset V := I.filter fun v => 0 ≤ r v
    have hI' : G.IsIndepSet (I' : Set V) :=
      hI.mono (Finset.coe_subset.2 (Finset.filter_subset _ _))
    have hsum_eq : ∑ v ∈ I, r' v = ∑ v ∈ I', r v := by
      rw [← Finset.sum_filter_add_sum_filter_not I (fun v => 0 ≤ r v)]
      have h1 : ∑ v ∈ I', r' v = ∑ v ∈ I', r v :=
        Finset.sum_congr rfl fun v hv => max_eq_left (Finset.mem_filter.1 hv).2
      have h2 : ∑ v ∈ I.filter (fun v => ¬ 0 ≤ r v), r' v = 0 :=
        Finset.sum_eq_zero fun v hv => max_eq_right (le_of_not_ge (Finset.mem_filter.1 hv).2)
      rw [h1, h2, add_zero]
    rw [hsum_eq]
    have hmem : stabVertex ℝ I' ∈ stabPolytope ℝ G :=
      subset_convexHull ℝ _ ⟨⟨I', hI'⟩, rfl⟩
    have hval : f (stabVertex ℝ I') = ∑ v ∈ I', r v := by
      rw [hf_eq]
      simp [stabVertex, Finset.sum_ite_mem]
    exact hval ▸ hfu _ hmem
  let δ : ℝ := (∑ v : V, r' v * x v) - u
  have hδ : 0 < δ := sub_pos.2 hr'_x
  obtain ⟨N, hN⟩ := exists_nat_gt ((Fintype.card V : ℝ) / δ)
  let w : V → ℕ := fun v => ⌊(N : ℝ) * r' v⌋₊
  let S : Finset (Finset V) := Finset.univ.filter fun I => G.IsIndepSet (I : Set V)
  have hSne : S.Nonempty := ⟨∅, by simp [S]⟩
  obtain ⟨I₀, hI₀_mem, hI₀_max⟩ := S.exists_max_image (fun I : Finset V => ∑ v ∈ I, w v) hSne
  have hI₀ : G.IsIndepSet (I₀ : Set V) := (Finset.mem_filter.1 hI₀_mem).2
  let M : ℕ := ∑ v ∈ I₀, w v
  have hM : ∀ I : Finset V, G.IsIndepSet (I : Set V) → ∑ v ∈ I, w v ≤ M :=
    fun I hI => hI₀_max I (Finset.mem_filter.2 ⟨Finset.mem_univ _, hI⟩)
  have hM_le : (M : ℝ) ≤ (N : ℝ) * u :=
    calc (M : ℝ) = ∑ v ∈ I₀, (w v : ℝ) := by simp [M]
      _ ≤ ∑ v ∈ I₀, (N : ℝ) * r' v :=
          Finset.sum_le_sum fun v _ => Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hr'_nonneg v))
      _ = (N : ℝ) * ∑ v ∈ I₀, r' v := by rw [← Finset.mul_sum]
      _ ≤ (N : ℝ) * u := mul_le_mul_of_nonneg_left (hr'_indep I₀ hI₀).le (Nat.cast_nonneg N)
  have hwx_le : ∑ v : V, (w v : ℝ) * x v ≤ (M : ℝ) :=
    sum_natWeight_mul_le_of_isPerfectGraph hG w hM hx
  have hNr_le : (N : ℝ) * (∑ v : V, r' v * x v) ≤ ∑ v : V, (w v : ℝ) * x v + Fintype.card V := by
    rw [Finset.mul_sum]
    have hcard : (Fintype.card V : ℝ) = ∑ _v : V, (1 : ℝ) := by simp
    rw [hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have hfloor : (N : ℝ) * r' v ≤ (w v : ℝ) + 1 := (Nat.lt_floor_add_one _).le
    have hx1 : x v ≤ 1 := by
      simpa using hx.2 {v} (by simp)
    have hx0 : 0 ≤ x v := hx.1 v
    calc (N : ℝ) * (r' v * x v) = ((N : ℝ) * r' v) * x v := by ring
      _ ≤ ((w v : ℝ) + 1) * x v := mul_le_mul_of_nonneg_right hfloor hx0
      _ = (w v : ℝ) * x v + x v := by ring
      _ ≤ (w v : ℝ) * x v + 1 := by linarith
  have hN_mul : (Fintype.card V : ℝ) < (N : ℝ) * δ := (div_lt_iff₀ hδ).1 hN
  dsimp [δ] at hN_mul
  linarith

/-- Clique inequality matrix for `QSTAB(G)` indexed by all finite cliques of `G`. -/
@[expose] def cliqueMatrix [DecidableEq V] (G : SimpleGraph V) :
    Matrix {K : Finset V // G.IsClique (K : Set V)} V ℝ :=
  Matrix.of fun K v => if v ∈ K.1 then 1 else 0

/-- Full H-description matrix for `QSTAB(G)` split into non-negativity rows `V` and clique rows. -/
@[expose] def stabFullMatrix [DecidableEq V] (G : SimpleGraph V) :
    Matrix (V ⊕ {K : Finset V // G.IsClique (K : Set V)}) V ℝ :=
  Matrix.fromRows (-1 : Matrix V V ℝ) (cliqueMatrix G)

/-- Full right-hand side for `QSTAB(G)`. -/
@[expose] def stabFullRHS (G : SimpleGraph V) :
    V ⊕ {K : Finset V // G.IsClique (K : Set V)} → ℝ :=
  Sum.elim 0 (fun _ => 1)

/-- Entry formula for the clique inequality matrix `cliqueMatrix G`. -/
theorem cliqueMatrix_apply [DecidableEq V] (G : SimpleGraph V)
    (K : {K : Finset V // G.IsClique (K : Set V)}) (v : V) :
    cliqueMatrix G K v = if v ∈ K.1 then 1 else 0 := rfl

/-- Non-negativity row entry of `stabFullMatrix G`. -/
theorem stabFullMatrix_apply_inl [DecidableEq V] (G : SimpleGraph V) (v w : V) :
    stabFullMatrix G (Sum.inl v) w = -(if v = w then (1 : ℝ) else 0) := by
  simp [stabFullMatrix, Matrix.one_apply]

/-- Clique row entry of `stabFullMatrix G`. -/
theorem stabFullMatrix_apply_inr [DecidableEq V] (G : SimpleGraph V)
    (K : {K : Finset V // G.IsClique (K : Set V)}) (v : V) :
    stabFullMatrix G (Sum.inr K) v = if v ∈ K.1 then 1 else 0 := rfl

/-- Non-negativity row right-hand side of `stabFullRHS G`. -/
theorem stabFullRHS_apply_inl (G : SimpleGraph V) (v : V) :
    stabFullRHS G (Sum.inl v) = 0 := rfl

/-- Clique row right-hand side of `stabFullRHS G`. -/
theorem stabFullRHS_apply_inr (G : SimpleGraph V)
    (K : {K : Finset V // G.IsClique (K : Set V)}) :
    stabFullRHS G (Sum.inr K) = 1 := rfl

/-- Matrix form of `STAB(G) = QSTAB(G)` for finite perfect graphs. -/
theorem stabPolytope_eq_setOf_mulVec_le [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : IsPerfectGraph G) :
    stabPolytope ℝ G = {x | stabFullMatrix G *ᵥ x ≤ stabFullRHS G} := by
  rw [isPerfectGraph_imp_stabPolytope_eq_qstabPolytope hG]
  ext x
  simp only [qstabPolytope, Set.mem_ofPred_eq, Pi.le_def, stabFullMatrix, stabFullRHS]
  constructor
  · rintro ⟨h0, hcl⟩ (v | K)
    · rw [Matrix.fromRows_mulVec]
      simp [Matrix.neg_mulVec, Matrix.one_mulVec, h0 v]
    · rw [Matrix.fromRows_mulVec]
      simp only [Sum.elim_inr, Matrix.mulVec, dotProduct, cliqueMatrix, Matrix.of_apply, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
      exact hcl K.1 K.2
  · intro h
    refine ⟨fun v => ?_, fun K hK => ?_⟩
    · have hv := h (Sum.inl v)
      rw [Matrix.fromRows_mulVec] at hv
      simpa [Matrix.neg_mulVec, Matrix.one_mulVec] using hv
    · have h1 := h (Sum.inr ⟨K, hK⟩)
      rw [Matrix.fromRows_mulVec] at h1
      simpa [Matrix.mulVec, dotProduct, cliqueMatrix, Finset.sum_ite_mem] using h1

end ChvatalLovasz

end CslibFrontier.ExtendedFormulation
