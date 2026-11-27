/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TrianglePartition.Gluing
import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree.Syntax
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

/-!
# NP-Hardness of Triangle Edge-Partition on $K_4$-Free Graphs

Completes the polynomial-time Karp reduction `ThreeSATThree ≤ₚ K4FreeTrianglePartition`
, proving both directions of `threeSATThreeToTriGraph_mem_iff` and concluding
`K4FreeTrianglePartition_npHard`.

## Main results
- `threeSATThreeToTriGraph_mem_iff`: exact Karp equivalence with `ThreeSATThree`.
- `K4FreeTrianglePartition_npHard`: NP-hardness of `K4FreeTrianglePartition`.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL

/-! ### Forward Direction: `Satisfiable → IsTriangleEdgePartition` -/

private theorem buildGluedGraph_fwd {ψ : CNF ℕ} (hψ : NormProps ψ)
    (hsat : ψ.Satisfiable) : IsTriangleEdgePartition (buildGluedGraph ψ) := by
  classical
  obtain ⟨σ, hσ⟩ := hsat
  set m := ψ.length
  set vars := ψ.distinctVars
  set k := vars.length
  set N := 9 * m + 48 * k
  have hmemN : ∀ x < N, x ∈ (buildGluedGraph ψ).vertices := fun x hx =>
    (mem_buildGluedGraph_vertices_iff ψ x).2 hx
  let mkV (x : ℕ) (hx : x < N) : {v // v ∈ (buildGluedGraph ψ).vertices} := ⟨x, hmemN x hx⟩
  have hsat_r : ∀ j : Fin m, ∃ r < (ψ.getD j.1 []).length,
      σ (((ψ.getD j.1 []).getD r (0, false)).1) = ((ψ.getD j.1 []).getD r (0, false)).2 := by
    intro j
    have hcmem : ψ.getD j.1 [] ∈ ψ := by
      rw [List.getD_eq_getElem _ _ j.2]; exact List.getElem_mem j.2
    have hev := (CNF.eval_eq_true_iff σ ψ).1 hσ _ hcmem
    obtain ⟨l, hl, hlev⟩ := (Clause.eval_eq_true_iff σ _).1 hev
    obtain ⟨r, hr, hreq⟩ := List.mem_iff_getElem.1 hl
    refine ⟨r, hr, ?_⟩
    rw [List.getD_eq_getElem _ _ hr, hreq]
    exact hlev
  let rStar (j : Fin m) : ℕ := Classical.choose (hsat_r j)
  have hrStar_lt : ∀ j : Fin m, rStar j < (ψ.getD j.1 []).length := fun j =>
    (Classical.choose_spec (hsat_r j)).1
  have hrStar_sat : ∀ j : Fin m,
      σ (((ψ.getD j.1 []).getD (rStar j) (0, false)).1) =
        ((ψ.getD j.1 []).getD (rStar j) (0, false)).2 := fun j =>
    (Classical.choose_spec (hsat_r j)).2
  have hrStar_lt3 : ∀ j : Fin m, rStar j < 3 := fun j =>
    lt_of_lt_of_le (hrStar_lt j)
      (hψ.clause_len_le _ (by rw [List.getD_eq_getElem _ _ j.2]; exact List.getElem_mem j.2))
  let clauseTri (j : Fin m) (t : ℕ × ℕ × ℕ) (ht : t ∈ k333PartTris (rStar j)) :
      Finset {v // v ∈ (buildGluedGraph ψ).vertices} :=
    have hvalid := k333_part_valid ⟨rStar j, hrStar_lt3 j⟩ t ht
    have h1 : t.1 < 9 := (k333Adj_bounds hvalid.1).1
    have h2 : t.2.1 < 9 := (k333Adj_bounds hvalid.1).2.1
    have h3 : t.2.2 < 9 := (k333Adj_bounds hvalid.2.1).2.1
    {mkV (9 * j.1 + t.1) (by omega), mkV (9 * j.1 + t.2.1) (by omega),
     mkV (9 * j.1 + t.2.2) (by omega)}
  let 𝒯_c : Finset (Finset {v // v ∈ (buildGluedGraph ψ).vertices}) :=
    Finset.univ.biUnion fun j : Fin m =>
      (k333PartTris (rStar j)).attach.toFinset.image fun t => clauseTri j t.1 t.2
  let isOmittedPort (vi : Fin k) (xy : Fin 12 × Fin 4) : Prop :=
    ∃ j : Fin m,
      ((ψ.getD j.1 []).getD (rStar j) (0, false)).1 = vars.getD vi.1 0 ∧
      xy.1.1 = 4 * ((CNF.vars (ψ.take j.1)).count (vars.getD vi.1 0)) ∧
      xy.2.1 = 0
  let torusTri (vi : Fin k) (xy : Fin 12 × Fin 4) :
      Finset {v // v ∈ (buildGluedGraph ψ).vertices} :=
    let l := if σ (vars.getD vi.1 0) then torusUpTri xy.1.1 xy.2.1
             else torusDownTri xy.1.1 xy.2.1
    have hb : l.getD 0 0 < 48 ∧ l.getD 1 0 < 48 ∧ l.getD 2 0 < 48 := by
      dsimp only [l]; split_ifs
      · have h := torus_up_adj xy.1 xy.2; exact ⟨h.1, h.2.1, h.2.2.1⟩
      · have h := torus_down_adj xy.1 xy.2; exact ⟨h.1, h.2.1, h.2.2.1⟩
    {mkV (torusVertexId ψ vars vi.1 (l.getD 0 0)) (torusVertexId_lt_bound hψ vi.2 hb.1),
     mkV (torusVertexId ψ vars vi.1 (l.getD 1 0)) (torusVertexId_lt_bound hψ vi.2 hb.2.1),
     mkV (torusVertexId ψ vars vi.1 (l.getD 2 0)) (torusVertexId_lt_bound hψ vi.2 hb.2.2)}
  let 𝒯_t : Finset (Finset {v // v ∈ (buildGluedGraph ψ).vertices}) :=
    Finset.univ.biUnion fun vi : Fin k =>
      (Finset.univ.filter fun xy : Fin 12 × Fin 4 => ¬ isOmittedPort vi xy).image (torusTri vi)
  rw [isTriangleEdgePartition_iff]
  refine ⟨𝒯_c ∪ 𝒯_t, ?_, ?_⟩
  · intro T hT
    rcases Finset.mem_union.1 hT with hTc | hTt
    · rcases Finset.mem_biUnion.1 hTc with ⟨j, _, hTj⟩
      rcases Finset.mem_image.1 hTj with ⟨⟨t, ht⟩, _, rfl⟩
      have hv := k333_part_valid ⟨rStar j, hrStar_lt3 j⟩ t ht
      have hdisj := k333_part_disjoint_removed ⟨rStar j, hrStar_lt3 j⟩ t ht
      have hmk : ∀ a b : ℕ, k333Adj a b = true →
          (rStar j ≠ 0 → isInTri 0 3 6 a b = false) →
          (rStar j ≠ 1 → isInTri 1 4 6 a b = false) →
          (rStar j ≠ 2 → isInTri 7 2 5 a b = false) →
          k333ClauseAdj (ψ.getD j.1 []).length a b = true := by
        intro a b hab _ h1 h2
        have hrlt := hrStar_lt j
        exact (k333ClauseAdj_eq_true_iff _ a b).2 ⟨hab, fun hle2 => h2 (by omega),
          fun hle1 => h1 (by omega)⟩
      have h12 : k333ClauseAdj (ψ.getD j.1 []).length t.1 t.2.1 = true := by
        obtain ⟨ha, hb, hne⟩ := k333Adj_bounds hv.1
        have hd := hdisj ⟨t.1, ha⟩ ⟨t.2.1, hb⟩ ((isInTri_eq_true_iff _ _ _ _ _).2
          ⟨Or.inl rfl, Or.inr (Or.inl rfl), hne⟩)
        exact hmk t.1 t.2.1 hv.1 hd.1 hd.2.1 hd.2.2
      have h13 : k333ClauseAdj (ψ.getD j.1 []).length t.1 t.2.2 = true := by
        obtain ⟨ha, hc, hne⟩ := k333Adj_bounds hv.2.1
        have hd := hdisj ⟨t.1, ha⟩ ⟨t.2.2, hc⟩ ((isInTri_eq_true_iff _ _ _ _ _).2
          ⟨Or.inl rfl, Or.inr (Or.inr rfl), hne⟩)
        exact hmk t.1 t.2.2 hv.2.1 hd.1 hd.2.1 hd.2.2
      have h23 : k333ClauseAdj (ψ.getD j.1 []).length t.2.1 t.2.2 = true := by
        obtain ⟨hb, hc, hne⟩ := k333Adj_bounds hv.2.2
        have hd := hdisj ⟨t.2.1, hb⟩ ⟨t.2.2, hc⟩ ((isInTri_eq_true_iff _ _ _ _ _).2
          ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), hne⟩)
        exact hmk t.2.1 t.2.2 hv.2.2 hd.1 hd.2.1 hd.2.2
      have ha12 : (buildGluedGraph ψ).toSimpleGraph.Adj (9 * j.1 + t.1) (9 * j.1 + t.2.1) :=
        (glued_adj_iff hψ).2 (Or.inl ⟨j.1, j.2, t.1, t.2.1, h12, rfl, rfl⟩)
      have ha13 : (buildGluedGraph ψ).toSimpleGraph.Adj (9 * j.1 + t.1) (9 * j.1 + t.2.2) :=
        (glued_adj_iff hψ).2 (Or.inl ⟨j.1, j.2, t.1, t.2.2, h13, rfl, rfl⟩)
      have ha23 : (buildGluedGraph ψ).toSimpleGraph.Adj (9 * j.1 + t.2.1) (9 * j.1 + t.2.2) :=
        (glued_adj_iff hψ).2 (Or.inl ⟨j.1, j.2, t.2.1, t.2.2, h23, rfl, rfl⟩)
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        simp only [clauseTri, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rw [Graph.induced_adj]
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        all_goals first | exact (hxy rfl).elim | exact ha12 | exact ha13 | exact ha23 |
          exact ha12.symm | exact ha13.symm | exact ha23.symm
      · dsimp only [clauseTri]
        have ⟨ht1, ht2, ht3⟩ : t.1 < 9 ∧ t.2.1 < 9 ∧ t.2.2 < 9 :=
          ⟨(k333Adj_bounds hv.1).1, (k333Adj_bounds hv.1).2.1, (k333Adj_bounds hv.2.1).2.1⟩
        have hn12 : mkV (9 * j.1 + t.1) (by dsimp only [N]; omega) ≠
            mkV (9 * j.1 + t.2.1) (by dsimp only [N]; omega) := fun h =>
          ha12.ne (congrArg Subtype.val h)
        have hn13 : mkV (9 * j.1 + t.1) (by dsimp only [N]; omega) ≠
            mkV (9 * j.1 + t.2.2) (by dsimp only [N]; omega) := fun h =>
          ha13.ne (congrArg Subtype.val h)
        have hn23 : mkV (9 * j.1 + t.2.1) (by dsimp only [N]; omega) ≠
            mkV (9 * j.1 + t.2.2) (by dsimp only [N]; omega) := fun h =>
          ha23.ne (congrArg Subtype.val h)
        rw [Finset.card_insert_of_notMem (by simp [hn12, hn13]),
          Finset.card_insert_of_notMem (by simp [hn23]), Finset.card_singleton]
    · rcases Finset.mem_biUnion.1 hTt with ⟨vi, _, hTvi⟩
      rcases Finset.mem_image.1 hTvi with ⟨xy, _, rfl⟩
      dsimp only [torusTri]
      set l := if σ (vars.getD vi.1 0) then torusUpTri xy.1.1 xy.2.1
               else torusDownTri xy.1.1 xy.2.1
      have hta : l.getD 0 0 < 48 ∧ l.getD 1 0 < 48 ∧ l.getD 2 0 < 48 ∧
          torusAdj (l.getD 0 0) (l.getD 1 0) = true ∧
          torusAdj (l.getD 0 0) (l.getD 2 0) = true ∧
          torusAdj (l.getD 1 0) (l.getD 2 0) = true := by
        dsimp only [l]; split_ifs
        · exact torus_up_adj xy.1 xy.2
        · exact torus_down_adj xy.1 xy.2
      have ha12 : (buildGluedGraph ψ).toSimpleGraph.Adj
          (torusVertexId ψ vars vi.1 (l.getD 0 0)) (torusVertexId ψ vars vi.1 (l.getD 1 0)) :=
        (glued_adj_iff hψ).2 (Or.inr ⟨vi.1, vi.2, _, _, hta.2.2.2.1, rfl, rfl⟩)
      have ha13 : (buildGluedGraph ψ).toSimpleGraph.Adj
          (torusVertexId ψ vars vi.1 (l.getD 0 0)) (torusVertexId ψ vars vi.1 (l.getD 2 0)) :=
        (glued_adj_iff hψ).2 (Or.inr ⟨vi.1, vi.2, _, _, hta.2.2.2.2.1, rfl, rfl⟩)
      have ha23 : (buildGluedGraph ψ).toSimpleGraph.Adj
          (torusVertexId ψ vars vi.1 (l.getD 1 0)) (torusVertexId ψ vars vi.1 (l.getD 2 0)) :=
        (glued_adj_iff hψ).2 (Or.inr ⟨vi.1, vi.2, _, _, hta.2.2.2.2.2, rfl, rfl⟩)
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rw [Graph.induced_adj]
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        all_goals first | exact (hxy rfl).elim | exact ha12 | exact ha13 | exact ha23 |
          exact ha12.symm | exact ha13.symm | exact ha23.symm
      · dsimp only [l] at ha12 ha13 ha23
        rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV]
            exact fun h => h.elim ha12.ne ha13.ne),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton, Subtype.ext_iff, mkV]
            exact ha23.ne),
          Finset.card_singleton]
  · intro u v huv
    rw [Graph.induced_adj] at huv
    have hcov_c : ∀ j : Fin m, ∀ t : ℕ × ℕ × ℕ, ∀ ht : t ∈ k333PartTris (rStar j),
        (u ∈ clauseTri j t ht ∧ v ∈ clauseTri j t ht) ↔
          ∃ a b : ℕ, a < 9 ∧ b < 9 ∧ u.1 = 9 * j.1 + a ∧ v.1 = 9 * j.1 + b ∧
            isInTri t.1 t.2.1 t.2.2 a b = true := by
      intro j t ht
      have hv := k333_part_valid ⟨rStar j, hrStar_lt3 j⟩ t ht
      have h1 : t.1 < 9 := (k333Adj_bounds hv.1).1
      have h2 : t.2.1 < 9 := (k333Adj_bounds hv.1).2.1
      have h3 : t.2.2 < 9 := (k333Adj_bounds hv.2.1).2.1
      constructor
      · rintro ⟨hu, hv'⟩
        simp only [clauseTri, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV]
          at hu hv'
        have hne : u.1 ≠ v.1 := huv.ne
        rcases hu with hu | hu | hu <;> rcases hv' with hv' | hv' | hv'
        all_goals first
          | exact (hne (hu.trans hv'.symm)).elim
          | exact ⟨_, _, by omega, by omega, hu, hv',
              (isInTri_eq_true_iff _ _ _ _ _).2 ⟨by simp, by simp, by omega⟩⟩
      · rintro ⟨a, b, _, _, hu, hv', hin⟩
        rw [isInTri_eq_true_iff] at hin
        simp only [clauseTri, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV]
        rcases hin.1 with rfl | rfl | rfl <;> rcases hin.2.1 with rfl | rfl | rfl
        all_goals simp [hu, hv']
    have hcov_t : ∀ vi : Fin k, ∀ xy : Fin 12 × Fin 4,
        (u ∈ torusTri vi xy ∧ v ∈ torusTri vi xy) ↔
          ∃ p q : ℕ, p < 48 ∧ q < 48 ∧
            u.1 = torusVertexId ψ vars vi.1 p ∧ v.1 = torusVertexId ψ vars vi.1 q ∧
            p ≠ q ∧
            p ∈ (if σ (vars.getD vi.1 0) then torusUpTri xy.1.1 xy.2.1
                 else torusDownTri xy.1.1 xy.2.1) ∧
            q ∈ (if σ (vars.getD vi.1 0) then torusUpTri xy.1.1 xy.2.1
                 else torusDownTri xy.1.1 xy.2.1) := by
      intro vi xy
      set l := if σ (vars.getD vi.1 0) then torusUpTri xy.1.1 xy.2.1
               else torusDownTri xy.1.1 xy.2.1
      have hta : l.getD 0 0 < 48 ∧ l.getD 1 0 < 48 ∧ l.getD 2 0 < 48 := by
        dsimp only [l]; split_ifs
        · have h := torus_up_adj xy.1 xy.2; exact ⟨h.1, h.2.1, h.2.2.1⟩
        · have h := torus_down_adj xy.1 xy.2; exact ⟨h.1, h.2.1, h.2.2.1⟩
      have hl3 : l.length = 3 := by dsimp only [l]; split_ifs <;> rfl
      have hmem_l : ∀ z, z ∈ l ↔ z = l.getD 0 0 ∨ z = l.getD 1 0 ∨ z = l.getD 2 0 := by
        intro z; match l, hl3 with | [a, b, c], _ => simp
      constructor
      · rintro ⟨hu, hv'⟩
        simp only [torusTri, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV]
          at hu hv'
        have hne : u.1 ≠ v.1 := huv.ne
        rcases hu with hu | hu | hu <;> rcases hv' with hv' | hv' | hv'
        all_goals first
          | exact (hne (hu.trans hv'.symm)).elim
          | exact ⟨_, _, hta.1, hta.2.1, hu, hv',
              fun heq => hne (hu.trans (heq ▸ hv'.symm)),
              (hmem_l _).2 (Or.inl rfl), (hmem_l _).2 (Or.inr (Or.inl rfl))⟩
          | exact ⟨_, _, hta.1, hta.2.2, hu, hv',
              fun heq => hne (hu.trans (heq ▸ hv'.symm)),
              (hmem_l _).2 (Or.inl rfl), (hmem_l _).2 (Or.inr (Or.inr rfl))⟩
          | exact ⟨_, _, hta.2.1, hta.1, hu, hv',
              fun heq => hne (hu.trans (heq ▸ hv'.symm)),
              (hmem_l _).2 (Or.inr (Or.inl rfl)), (hmem_l _).2 (Or.inl rfl)⟩
          | exact ⟨_, _, hta.2.1, hta.2.2, hu, hv',
              fun heq => hne (hu.trans (heq ▸ hv'.symm)),
              (hmem_l _).2 (Or.inr (Or.inl rfl)), (hmem_l _).2 (Or.inr (Or.inr rfl))⟩
          | exact ⟨_, _, hta.2.2, hta.1, hu, hv',
              fun heq => hne (hu.trans (heq ▸ hv'.symm)),
              (hmem_l _).2 (Or.inr (Or.inr rfl)), (hmem_l _).2 (Or.inl rfl)⟩
          | exact ⟨_, _, hta.2.2, hta.2.1, hu, hv',
              fun heq => hne (hu.trans (heq ▸ hv'.symm)),
              (hmem_l _).2 (Or.inr (Or.inr rfl)), (hmem_l _).2 (Or.inr (Or.inl rfl))⟩
      · rintro ⟨p, q, _, _, hu, hv', _, hpl, hql⟩
        rw [hmem_l] at hpl hql
        dsimp only [torusTri]
        simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV]
        change (u.1 = torusVertexId ψ vars vi.1 (l.getD 0 0) ∨
            u.1 = torusVertexId ψ vars vi.1 (l.getD 1 0) ∨
            u.1 = torusVertexId ψ vars vi.1 (l.getD 2 0)) ∧
          (v.1 = torusVertexId ψ vars vi.1 (l.getD 0 0) ∨
            v.1 = torusVertexId ψ vars vi.1 (l.getD 1 0) ∨
            v.1 = torusVertexId ψ vars vi.1 (l.getD 2 0))
        rcases hpl with rfl | rfl | rfl <;> rcases hql with rfl | rfl | rfl <;>
          simp only [hu, hv', true_or, or_true, and_self]
    have hdisj_ct : ∀ T1 ∈ 𝒯_c, ∀ T2 ∈ 𝒯_t, ¬ (u ∈ T1 ∧ v ∈ T1 ∧ u ∈ T2 ∧ v ∈ T2) := by
      intro T1 hT1 T2 hT2 ⟨hu1, hv1, hu2, hv2⟩
      rcases Finset.mem_biUnion.1 hT1 with ⟨j, _, hTj⟩
      rcases Finset.mem_image.1 hTj with ⟨⟨t, ht⟩, _, rfl⟩
      rcases Finset.mem_biUnion.1 hT2 with ⟨vi, _, hTvi⟩
      rcases Finset.mem_image.1 hTvi with ⟨xy, hxy, rfl⟩
      have hnomit : ¬ isOmittedPort vi xy := (Finset.mem_filter.1 hxy).2
      obtain ⟨a, b, ha, hb, hua, hvb, hin⟩ := (hcov_c j t ht).1 ⟨hu1, hv1⟩
      obtain ⟨p, q, hp, hq, hup, hvq, _, hpl, hql⟩ := (hcov_t vi xy).1 ⟨hu2, hv2⟩
      obtain ⟨hr, hpos1, ha_eq⟩ :=
        (torusVertexId_eq_clause_iff hψ vi.2 hp j.2 ha).1 (hup.symm.trans hua)
      obtain ⟨_, hpos2, hb_eq⟩ :=
        (torusVertexId_eq_clause_iff hψ vi.2 hq j.2 hb).1 (hvq.symm.trans hvb)
      set r := clauseLitPos (ψ.getD j.1 []) (vars.getD vi.1 0)
      have hdisj_r := k333_part_disjoint_removed ⟨rStar j, hrStar_lt3 j⟩ t ht ⟨a, ha⟩ ⟨b, hb⟩ hin
      have hr_eq : r = rStar j := by
        by_contra hne
        have hab_ne : a ≠ b := ((isInTri_eq_true_iff _ _ _ _ _).1 hin).2.2
        set pos1 := torusPortPos ((CNF.vars (ψ.take j.1)).count (vars.getD vi.1 0))
            (((ψ.getD j.1 []).getD r (0, false)).2) p
        set pos2 := torusPortPos ((CNF.vars (ψ.take j.1)).count (vars.getD vi.1 0))
            (((ψ.getD j.1 []).getD r (0, false)).2) q
        have hpos_ne : pos1 ≠ pos2 := fun h => hab_ne (by rw [ha_eq, hb_eq, h])
        have hdec_in : ∀ r0 p1 p2 : Fin 3, p1.1 ≠ p2.1 →
            (r0.1 = 0 → isInTri 0 3 6 (k333PortVert r0.1 p1.1) (k333PortVert r0.1 p2.1) = true) ∧
            (r0.1 = 1 → isInTri 1 4 6 (k333PortVert r0.1 p1.1) (k333PortVert r0.1 p2.1) = true) ∧
            (r0.1 = 2 →
              isInTri 7 2 5 (k333PortVert r0.1 p1.1) (k333PortVert r0.1 p2.1) = true) := by
          decide
        have hin3 := hdec_in ⟨r, hr⟩ ⟨pos1, hpos1⟩ ⟨pos2, hpos2⟩ hpos_ne
        have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
        rcases hr_cases with hr0 | hr1 | hr2
        · have h0 := hdisj_r.1 (fun h => hne (hr0.trans h.symm))
          have h1 := hin3.1 hr0
          rw [← ha_eq, ← hb_eq] at h1; simp [h1] at h0
        · have h0 := hdisj_r.2.1 (fun h => hne (hr1.trans h.symm))
          have h1 := hin3.2.1 hr1
          rw [← ha_eq, ← hb_eq] at h1; simp [h1] at h0
        · have h0 := hdisj_r.2.2 (fun h => hne (hr2.trans h.symm))
          have h1 := hin3.2.2 hr2
          rw [← ha_eq, ← hb_eq] at h1; simp [h1] at h0
      have hv_eq : ((ψ.getD j.1 []).getD (rStar j) (0, false)).1 = vars.getD vi.1 0 := by
        rw [← hr_eq]; exact ((clauseLitPos_spec hψ j.2).1 hr).2
      have hpol : σ (vars.getD vi.1 0) = ((ψ.getD j.1 []).getD r (0, false)).2 := by
        rw [hr_eq, ← hv_eq]; exact hrStar_sat j
      set occ := (CNF.vars (ψ.take j.1)).count (vars.getD vi.1 0)
      have hocc_lt : occ < 3 := by
        have hspec := (clauseLitPos_spec hψ j.2).1 hr
        dsimp only [occ]; rw [← hspec.2]; exact occ_lt_three hψ j.2 hspec.1
      apply hnomit; refine ⟨j, hv_eq, ?_⟩
      have hport_in : ∀ z, z < 48 → torusPortPos occ (σ (vars.getD vi.1 0)) z < 3 →
          z ∈ (if σ (vars.getD vi.1 0) then torusUpTri (4 * occ) 0
               else torusDownTri (4 * occ) 0) := by
        have hdec : ∀ o : Fin 3, ∀ pol : Bool, ∀ z : Fin 48,
            torusPortPos o.1 pol z.1 < 3 →
            z.1 ∈ (if pol then torusUpTri (4 * o.1) 0 else torusDownTri (4 * o.1) 0) := by decide
        intro z hz hzp; exact hdec ⟨occ, hocc_lt⟩ _ ⟨z, hz⟩ hzp
      have hp_port := hport_in p hp (by rwa [hpol])
      have hq_port := hport_in q hq (by rwa [hpol])
      have hpadj : torusAdj p q = true := glued_torus_induced hψ vi.2 hp hq (hup ▸ hvq ▸ huv)
      cases hsig : σ (vars.getD vi.1 0)
      · simp only [hsig, Bool.false_eq_true, ↓reduceIte] at hpl hql hp_port hq_port
        have hu1 : xy = (⟨4 * occ, by omega⟩, (0 : Fin 4)) :=
          (torus_edge_unique_down ⟨p, hp⟩ ⟨q, hq⟩ hpadj).unique ⟨hpl, hql⟩ ⟨hp_port, hq_port⟩
        exact ⟨congrArg (fun z : Fin 12 × Fin 4 => z.1.1) hu1,
          congrArg (fun z : Fin 12 × Fin 4 => z.2.1) hu1⟩
      · simp only [hsig, ↓reduceIte] at hpl hql hp_port hq_port
        have hu1 : xy = (⟨4 * occ, by omega⟩, (0 : Fin 4)) :=
          (torus_edge_unique_up ⟨p, hp⟩ ⟨q, hq⟩ hpadj).unique ⟨hpl, hql⟩ ⟨hp_port, hq_port⟩
        exact ⟨congrArg (fun z : Fin 12 × Fin 4 => z.1.1) hu1,
          congrArg (fun z : Fin 12 × Fin 4 => z.2.1) hu1⟩
    have huniq_c : ∀ T1 ∈ 𝒯_c, ∀ T2 ∈ 𝒯_c, u ∈ T1 ∧ v ∈ T1 → u ∈ T2 ∧ v ∈ T2 → T1 = T2 := by
      intro T1 hT1 T2 hT2 h1 h2
      rcases Finset.mem_biUnion.1 hT1 with ⟨j1, _, hTj1⟩
      rcases Finset.mem_image.1 hTj1 with ⟨⟨t1, ht1⟩, _, rfl⟩
      rcases Finset.mem_biUnion.1 hT2 with ⟨j2, _, hTj2⟩
      rcases Finset.mem_image.1 hTj2 with ⟨⟨t2, ht2⟩, _, rfl⟩
      obtain ⟨a1, b1, ha1, hb1, hua1, hvb1, hin1⟩ := (hcov_c j1 t1 ht1).1 h1
      obtain ⟨a2, b2, _, _, hua2, hvb2, hin2⟩ := (hcov_c j2 t2 ht2).1 h2
      have hjeq : j1 = j2 := Fin.ext (by omega)
      subst hjeq
      have haeq : a1 = a2 := by omega
      have hbeq : b1 = b2 := by omega
      subst haeq; subst hbeq
      have hfl := (k333_part_exact ⟨rStar j1, hrStar_lt3 j1⟩ ⟨a1, ha1⟩ ⟨b1, hb1⟩).1
      have hdisj :=
        k333_part_disjoint_removed ⟨rStar j1, hrStar_lt3 j1⟩ t1 ht1 ⟨a1, ha1⟩ ⟨b1, hb1⟩ hin1
      have hadj_ab : k333Adj a1 b1 = true :=
        k333ClauseAdj_to_k333Adj (glued_clause_induced hψ j1.2 ha1 hb1 (hua1 ▸ hvb1 ▸ huv))
      obtain ⟨t0, ht0⟩ := List.length_eq_one_iff.1 (hfl ⟨hadj_ab, hdisj⟩)
      have h1in : t1 ∈ (k333PartTris (rStar j1)).filter (fun t => isInTri t.1 t.2.1 t.2.2 a1 b1) :=
        List.mem_filter.2 ⟨ht1, hin1⟩
      have h2in : t2 ∈ (k333PartTris (rStar j1)).filter (fun t => isInTri t.1 t.2.1 t.2.2 a1 b1) :=
        List.mem_filter.2 ⟨ht2, hin2⟩
      rw [ht0] at h1in h2in
      have ht12 : t1 = t2 := (List.mem_singleton.1 h1in).trans (List.mem_singleton.1 h2in).symm
      subst ht12; rfl
    have huniq_t : ∀ T1 ∈ 𝒯_t, ∀ T2 ∈ 𝒯_t, u ∈ T1 ∧ v ∈ T1 → u ∈ T2 ∧ v ∈ T2 → T1 = T2 := by
      intro T1 hT1 T2 hT2 h1 h2
      rcases Finset.mem_biUnion.1 hT1 with ⟨vi1, _, hTv1⟩
      rcases Finset.mem_image.1 hTv1 with ⟨xy1, _, rfl⟩
      rcases Finset.mem_biUnion.1 hT2 with ⟨vi2, _, hTv2⟩
      rcases Finset.mem_image.1 hTv2 with ⟨xy2, _, rfl⟩
      obtain ⟨p1, q1, hp1, hq1, hup1, hvq1, _, hpl1, hql1⟩ := (hcov_t vi1 xy1).1 h1
      obtain ⟨p2, q2, hp2, hq2, hup2, hvq2, _, hpl2, hql2⟩ := (hcov_t vi2 xy2).1 h2
      have hvi_eq : vi1 = vi2 := by
        by_contra hne
        exact torus_inter_no_adj hψ vi1.2 vi2.2 (fun h => hne (Fin.ext h))
          hp1 hp2 hq1 hq2 (hup1.symm.trans hup2) (hvq1.symm.trans hvq2)
          (glued_torus_induced hψ vi1.2 hp1 hq1 (hup1 ▸ hvq1 ▸ huv))
      subst hvi_eq
      have hpeq : p1 = p2 := torusVertexId_inj hψ vi1.2 hp1 hp2 (hup1.symm.trans hup2)
      have hqeq : q1 = q2 := torusVertexId_inj hψ vi1.2 hq1 hq2 (hvq1.symm.trans hvq2)
      subst hpeq; subst hqeq
      have hpadj : torusAdj p1 q1 = true := glued_torus_induced hψ vi1.2 hp1 hq1 (hup1 ▸ hvq1 ▸ huv)
      have hxyeq : xy1 = xy2 := by
        cases hsig : σ (vars.getD vi1.1 0)
        · simp only [hsig, Bool.false_eq_true, ↓reduceIte] at hpl1 hql1 hpl2 hql2
          exact (torus_edge_unique_down ⟨p1, hp1⟩ ⟨q1, hq1⟩ hpadj).unique
            ⟨hpl1, hql1⟩ ⟨hpl2, hql2⟩
        · simp only [hsig, ↓reduceIte] at hpl1 hql1 hpl2 hql2
          exact (torus_edge_unique_up ⟨p1, hp1⟩ ⟨q1, hq1⟩ hpadj).unique
            ⟨hpl1, hql1⟩ ⟨hpl2, hql2⟩
      subst hxyeq; rfl
    have hex : ∃ T ∈ 𝒯_c ∪ 𝒯_t, u ∈ T ∧ v ∈ T := by
      rcases (glued_adj_iff hψ).1 huv with ⟨j, hj, a, b, hc, hua, hvb⟩ |
          ⟨vi, hvi, p, q, ht, hup, hvq⟩
      · obtain ⟨ha, hb, _⟩ := k333ClauseAdj_bounds hc
        have hadj_ab : k333Adj a b = true := k333ClauseAdj_to_k333Adj hc
        by_cases hrem : (rStar ⟨j, hj⟩ ≠ 0 → isInTri 0 3 6 a b = false) ∧
            (rStar ⟨j, hj⟩ ≠ 1 → isInTri 1 4 6 a b = false) ∧
            (rStar ⟨j, hj⟩ ≠ 2 → isInTri 7 2 5 a b = false)
        · have hlen1 := (k333_part_exact ⟨rStar ⟨j, hj⟩, hrStar_lt3 ⟨j, hj⟩⟩ ⟨a, ha⟩ ⟨b, hb⟩).1
            ⟨hadj_ab, hrem⟩
          obtain ⟨t, ht_eq⟩ := List.length_eq_one_iff.1 hlen1
          have ht_mem : t ∈ (k333PartTris (rStar ⟨j, hj⟩)).filter
              (fun t => isInTri t.1 t.2.1 t.2.2 a b) := by
            rw [ht_eq]; exact List.mem_singleton_self t
          obtain ⟨ht_in, hin⟩ := List.mem_filter.1 ht_mem
          refine ⟨clauseTri ⟨j, hj⟩ t ht_in, Finset.mem_union_left _ ?_,
            (hcov_c ⟨j, hj⟩ t ht_in).2 ⟨a, b, ha, hb, hua, hvb, hin⟩⟩
          exact Finset.mem_biUnion.2 ⟨⟨j, hj⟩, Finset.mem_univ _,
            Finset.mem_image.2 ⟨⟨t, ht_in⟩, by simp, rfl⟩⟩
        · have hsome : ∃ r : ℕ, r < (ψ.getD j []).length ∧ r ≠ rStar ⟨j, hj⟩ ∧
              isInTri (k333PortVert r 0) (k333PortVert r 1) (k333PortVert r 2) a b = true := by
            by_cases h0 : rStar ⟨j, hj⟩ ≠ 0 ∧ isInTri 0 3 6 a b = true
            · exact ⟨0, hψ.clause_len_pos _ (by
                rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj), h0.1.symm, h0.2⟩
            · by_cases h1 : rStar ⟨j, hj⟩ ≠ 1 ∧ isInTri 1 4 6 a b = true
              · have hge2 : 2 ≤ (ψ.getD j []).length := by
                  by_contra hlt
                  have h0' := ((k333ClauseAdj_eq_true_iff _ _ _).1 hc).2.2 (by omega)
                  rw [h1.2] at h0'; simp at h0'
                exact ⟨1, by omega, h1.1.symm, h1.2⟩
              · have h2 : rStar ⟨j, hj⟩ ≠ 2 ∧ isInTri 7 2 5 a b = true := by
                  by_contra h2n; apply hrem
                  refine ⟨fun hr0 => ?_, fun hr1 => ?_, fun hr2 => ?_⟩
                  · cases h : isInTri 0 3 6 a b
                    · rfl
                    · exact (h0 ⟨hr0, h⟩).elim
                  · cases h : isInTri 1 4 6 a b
                    · rfl
                    · exact (h1 ⟨hr1, h⟩).elim
                  · cases h : isInTri 7 2 5 a b
                    · rfl
                    · exact (h2n ⟨hr2, h⟩).elim
                have hge3 : 3 ≤ (ψ.getD j []).length := by
                  by_contra hlt
                  have h0' := ((k333ClauseAdj_eq_true_iff _ _ _).1 hc).2.1 (by omega)
                  rw [h2.2] at h0'; simp at h0'
                exact ⟨2, by omega, h2.1.symm, h2.2⟩
          obtain ⟨r, hr_len, hr_ne, hin_r⟩ := hsome
          set v0 := ((ψ.getD j []).getD r (0, false)).1
          set b0 := ((ψ.getD j []).getD r (0, false)).2
          have hv0_mem : v0 ∈ vars := by
            rw [CNF.mem_distinctVars, CNF.mem_vars]
            refine ⟨ψ.getD j [], by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj,
              b0, ?_⟩
            change (ψ.getD j []).getD r (0, false) ∈ ψ.getD j []
            rw [List.getD_eq_getElem _ _ hr_len]; exact List.getElem_mem hr_len
          set vi := vars.idxOf v0
          have hvi : vi < k := List.idxOf_lt_length_iff.2 hv0_mem
          have hv_get : vars.getD vi 0 = v0 := by
            rw [List.getD_eq_getElem _ _ hvi]; exact List.getElem_idxOf hvi
          set occ := (CNF.vars (ψ.take j)).count v0
          have hocc_lt : occ < 3 := occ_lt_three hψ hj hr_len
          have hr_pos : clauseLitPos (ψ.getD j []) v0 = r := clauseLitPos_unique hψ hj hr_len
          have hr_lt3 : r < 3 := lt_of_lt_of_le hr_len (hψ.clause_len_le _
            (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj))
          have hport_lift : ∀ z : ℕ, (z = k333PortVert r 0 ∨ z = k333PortVert r 1 ∨
              z = k333PortVert r 2) →
              ∃ p < 48, torusPortPos occ b0 p < 3 ∧
                torusVertexId ψ vars vi p = 9 * j + z ∧
                p ∈ (if b0 then torusUpTri (4 * occ) 0 else torusDownTri (4 * occ) 0) := by
            intro z hz
            have hchoose : ∃ pos < 3, z = k333PortVert r pos := by
              rcases hz with rfl | rfl | rfl
              · exact ⟨0, by decide, rfl⟩
              · exact ⟨1, by decide, rfl⟩
              · exact ⟨2, by decide, rfl⟩
            obtain ⟨pos, hpos, rfl⟩ := hchoose
            let p := if pos = 0 then 4 * (4 * occ)
                     else if pos = 1 then 4 * (4 * occ + 1)
                     else if b0 then 4 * (4 * occ) + 1 else 4 * (4 * occ + 1) + 3
            have hp48 : p < 48 := by dsimp only [p]; split_ifs <;> omega
            have hpp : torusPortPos occ b0 p = pos := torusPortPos_eq_self occ b0 pos hpos
            have hmem_t :
                p ∈ (if b0 then torusUpTri (4 * occ) 0 else torusDownTri (4 * occ) 0) := by
              have hdec : ∀ o : Fin 3, ∀ pol : Bool, ∀ pos : Fin 3,
                  (if pos.1 = 0 then 4 * (4 * o.1)
                   else if pos.1 = 1 then 4 * (4 * o.1 + 1)
                   else if pol then 4 * (4 * o.1) + 1 else 4 * (4 * o.1 + 1) + 3) ∈
                  (if pol then torusUpTri (4 * o.1) 0 else torusDownTri (4 * o.1) 0) := by decide
              exact hdec ⟨occ, hocc_lt⟩ b0 ⟨pos, hpos⟩
            have hvid : torusVertexId ψ vars vi p = 9 * j + k333PortVert r pos := by
              have hz9 : k333PortVert r pos < 9 := k333PortVert_lt_nine r pos
              rw [torusVertexId_eq_clause_iff hψ hvi hp48 hj hz9]
              simp only [vars, hv_get, hr_pos, hr_lt3, true_and]
              dsimp only [occ, b0] at hpp ⊢
              rw [hpp]; exact ⟨hpos, rfl⟩
            exact ⟨p, hp48, by omega, hvid, hmem_t⟩
          rw [isInTri_eq_true_iff] at hin_r
          obtain ⟨p, hp, _, hvp, hpm⟩ := hport_lift a hin_r.1
          obtain ⟨q, hq, _, hvq, hqm⟩ := hport_lift b hin_r.2.1
          have hpadj : torusAdj p q = true :=
            glued_torus_induced hψ hvi hp hq (hvp.symm ▸ hvq.symm ▸ hua ▸ hvb ▸ huv)
          have hxy_ex : ∃ xy : Fin 12 × Fin 4, ¬ isOmittedPort ⟨vi, hvi⟩ xy ∧
              p ∈ (if σ v0 then torusUpTri xy.1.1 xy.2.1 else torusDownTri xy.1.1 xy.2.1) ∧
              q ∈ (if σ v0 then torusUpTri xy.1.1 xy.2.1 else torusDownTri xy.1.1 xy.2.1) := by
            by_cases hsig : σ v0 = b0
            · refine ⟨(⟨4 * occ, by omega⟩, 0), ?_,
                by rw [hsig]; exact hpm, by rw [hsig]; exact hqm⟩
              rintro ⟨j', hv', hx', _⟩
              have hj'eq : j' = ⟨j, hj⟩ := by
                by_contra hnej
                have hocc' : (CNF.vars (ψ.take j'.1)).count v0 ≠ occ := by
                  have hne_val : j'.1 ≠ j := fun h => hnej (Fin.ext h)
                  rcases lt_or_gt_of_ne hne_val with hlt' | hgt'
                  · exact ne_of_lt (by
                      dsimp only [occ]; rw [← hv_get, ← hv']
                      exact occ_strict_mono hlt' hj (hrStar_lt j'))
                  · exact ne_of_gt (occ_strict_mono hgt' j'.2 hr_len)
                dsimp only [occ] at hocc'; simp only [hv_get] at hx'; omega
              subst hj'eq
              have hcl_eq : clauseLitPos (ψ.getD j []) v0 = rStar ⟨j, hj⟩ := by
                rw [← hv_get, ← hv']; exact clauseLitPos_unique hψ hj (hrStar_lt ⟨j, hj⟩)
              exact hr_ne (hr_pos.symm.trans hcl_eq)
            · cases hsb : σ v0
              · obtain ⟨xy, hxy, _⟩ := torus_edge_unique_down ⟨p, hp⟩ ⟨q, hq⟩ hpadj
                refine ⟨xy, ?_, by simp only [Bool.false_eq_true, ↓reduceIte, hxy.1],
                  by simp only [Bool.false_eq_true, ↓reduceIte, hxy.2]⟩
                rintro ⟨j', hv', hx', hy'⟩
                have hb0_t : b0 = true := by
                  cases h : b0
                  · exact (hsig (hsb.trans h.symm)).elim
                  · rfl
                have hj'_ne : j'.1 ≠ j := by
                  intro hjeq; have hfin : j' = ⟨j, hj⟩ := Fin.ext hjeq; subst hfin
                  have hr_eq : r = rStar ⟨j, hj⟩ := by
                    rw [← hr_pos, ← hv_get, ← hv']
                    exact clauseLitPos_unique hψ hj (hrStar_lt ⟨j, hj⟩)
                  have hsat' := hrStar_sat ⟨j, hj⟩
                  rw [← hr_eq] at hsat'; exact hsig hsat'
                have hocc' : (CNF.vars (ψ.take j'.1)).count v0 < 3 := by
                  rw [← hv_get, ← hv']; exact occ_lt_three hψ j'.2 (hrStar_lt j')
                have hocc_ne : (CNF.vars (ψ.take j'.1)).count v0 ≠ occ := by
                  rcases lt_or_gt_of_ne hj'_ne with hlt' | hgt'
                  · exact ne_of_lt (by
                      dsimp only [occ]; rw [← hv_get, ← hv']
                      exact occ_strict_mono hlt' hj (hrStar_lt j'))
                  · exact ne_of_gt (occ_strict_mono hgt' j'.2 hr_len)
                have hp_in_o' : p ∈ torusPortAll ((CNF.vars (ψ.take j'.1)).count v0) := by
                  have hdec : ∀ o : Fin 3, ∀ z : Fin 48,
                      z.1 ∈ torusDownTri (4 * o.1) 0 → z.1 ∈ torusPortAll o.1 := by decide
                  rw [hv_get] at hx'
                  exact hdec ⟨_, hocc'⟩ ⟨p, hp⟩ (by rw [← hx', ← hy']; exact hxy.1)
                have hp_in_o : p ∈ torusPortAll occ := by
                  have hdec : ∀ o : Fin 3, ∀ z : Fin 48,
                      z.1 ∈ torusUpTri (4 * o.1) 0 → z.1 ∈ torusPortAll o.1 := by decide
                  exact hdec ⟨occ, hocc_lt⟩ ⟨p, hp⟩ (by simpa [hb0_t] using hpm)
                exact (torus_port_not_adj hocc' hocc_lt hocc_ne hp_in_o' hp_in_o).1 rfl
              · obtain ⟨xy, hxy, _⟩ := torus_edge_unique_up ⟨p, hp⟩ ⟨q, hq⟩ hpadj
                refine ⟨xy, ?_, by simp only [↓reduceIte, hxy.1],
                  by simp only [↓reduceIte, hxy.2]⟩
                rintro ⟨j', hv', hx', hy'⟩
                have hb0_f : b0 = false := by
                  cases h : b0
                  · rfl
                  · exact (hsig (hsb.trans h.symm)).elim
                have hj'_ne : j'.1 ≠ j := by
                  intro hjeq; have hfin : j' = ⟨j, hj⟩ := Fin.ext hjeq; subst hfin
                  have hr_eq : r = rStar ⟨j, hj⟩ := by
                    rw [← hr_pos, ← hv_get, ← hv']
                    exact clauseLitPos_unique hψ hj (hrStar_lt ⟨j, hj⟩)
                  have hsat' := hrStar_sat ⟨j, hj⟩
                  rw [← hr_eq] at hsat'; exact hsig hsat'
                have hocc' : (CNF.vars (ψ.take j'.1)).count v0 < 3 := by
                  rw [← hv_get, ← hv']; exact occ_lt_three hψ j'.2 (hrStar_lt j')
                have hocc_ne : (CNF.vars (ψ.take j'.1)).count v0 ≠ occ := by
                  rcases lt_or_gt_of_ne hj'_ne with hlt' | hgt'
                  · exact ne_of_lt (by
                      dsimp only [occ]; rw [← hv_get, ← hv']
                      exact occ_strict_mono hlt' hj (hrStar_lt j'))
                  · exact ne_of_gt (occ_strict_mono hgt' j'.2 hr_len)
                have hp_in_o' : p ∈ torusPortAll ((CNF.vars (ψ.take j'.1)).count v0) := by
                  have hdec : ∀ o : Fin 3, ∀ z : Fin 48,
                      z.1 ∈ torusUpTri (4 * o.1) 0 → z.1 ∈ torusPortAll o.1 := by decide
                  rw [hv_get] at hx'
                  exact hdec ⟨_, hocc'⟩ ⟨p, hp⟩ (by rw [← hx', ← hy']; exact hxy.1)
                have hp_in_o : p ∈ torusPortAll occ := by
                  have hdec : ∀ o : Fin 3, ∀ z : Fin 48,
                      z.1 ∈ torusDownTri (4 * o.1) 0 → z.1 ∈ torusPortAll o.1 := by decide
                  exact hdec ⟨occ, hocc_lt⟩ ⟨p, hp⟩ (by simpa [hb0_f] using hpm)
                exact (torus_port_not_adj hocc' hocc_lt hocc_ne hp_in_o' hp_in_o).1 rfl
          obtain ⟨xy, hnomit, hpxy, hqxy⟩ := hxy_ex
          refine ⟨torusTri ⟨vi, hvi⟩ xy, Finset.mem_union_right _ ?_,
            (hcov_t ⟨vi, hvi⟩ xy).2 ⟨p, q, hp, hq, hua.trans hvp.symm, hvb.trans hvq.symm,
              fun heq => huv.ne (hua.trans (hvp.symm.trans (heq ▸ hvq.trans hvb.symm))),
              by rw [hv_get]; exact hpxy, by rw [hv_get]; exact hqxy⟩⟩
          exact Finset.mem_biUnion.2 ⟨⟨vi, hvi⟩, Finset.mem_univ _,
            Finset.mem_image.2 ⟨xy, Finset.mem_filter.2 ⟨Finset.mem_univ _, hnomit⟩, rfl⟩⟩
      · obtain ⟨hp, hq⟩ := torusAdj_bounds ht
        have hpq : p ≠ q := fun heq => by subst heq; rw [torusAdj_irrefl] at ht; simp at ht
        obtain ⟨xy, hxy⟩ : ∃ xy : Fin 12 × Fin 4,
            p ∈ (if σ (vars.getD vi 0) then torusUpTri xy.1.1 xy.2.1
                 else torusDownTri xy.1.1 xy.2.1) ∧
            q ∈ (if σ (vars.getD vi 0) then torusUpTri xy.1.1 xy.2.1
                 else torusDownTri xy.1.1 xy.2.1) := by
          cases hsig : σ (vars.getD vi 0)
          · obtain ⟨xy, hxy, _⟩ := torus_edge_unique_down ⟨p, hp⟩ ⟨q, hq⟩ ht
            exact ⟨xy, by simp [hxy.1], by simp [hxy.2]⟩
          · obtain ⟨xy, hxy, _⟩ := torus_edge_unique_up ⟨p, hp⟩ ⟨q, hq⟩ ht
            exact ⟨xy, by simp [hxy.1], by simp [hxy.2]⟩
        by_cases hom : isOmittedPort ⟨vi, hvi⟩ xy
        · obtain ⟨j, hvj, hxj, hyj⟩ := hom
          set r := rStar j
          set b0 := ((ψ.getD j.1 []).getD r (0, false)).2
          have hsig : σ (vars.getD vi 0) = b0 := by rw [← hvj]; exact hrStar_sat j
          set occ := (CNF.vars (ψ.take j.1)).count (vars.getD vi 0)
          have hocc_lt : occ < 3 := by
            dsimp only [occ]; rw [← hvj]; exact occ_lt_three hψ j.2 (hrStar_lt j)
          have hr_pos : clauseLitPos (ψ.getD j.1 []) (vars.getD vi 0) = r := by
            rw [← hvj]; exact clauseLitPos_unique hψ j.2 (hrStar_lt j)
          have hport_map : ∀ z < 48,
              z ∈ (if b0 then torusUpTri (4 * occ) 0 else torusDownTri (4 * occ) 0) →
              ∃ a < 9, torusVertexId ψ vars vi z = 9 * j.1 + a ∧
                (a = k333PortVert r 0 ∨ a = k333PortVert r 1 ∨ a = k333PortVert r 2) := by
            intro z hz hzm
            have hpp : torusPortPos occ b0 z < 3 := by
              have hdec : ∀ o : Fin 3, ∀ pol : Bool, ∀ z : Fin 48,
                  z.1 ∈ (if pol then torusUpTri (4 * o.1) 0 else torusDownTri (4 * o.1) 0) →
                  torusPortPos o.1 pol z.1 < 3 := by decide
              exact hdec ⟨occ, hocc_lt⟩ b0 ⟨z, hz⟩ hzm
            refine ⟨k333PortVert r (torusPortPos occ b0 z), k333PortVert_lt_nine r _, ?_, ?_⟩
            · rw [torusVertexId_eq_clause_iff hψ hvi hz j.2 (k333PortVert_lt_nine r _)]
              exact ⟨by rw [hr_pos]; exact hrStar_lt3 j, by rw [hr_pos]; exact hpp,
                by rw [hr_pos]⟩
            · have : torusPortPos occ b0 z = 0 ∨ torusPortPos occ b0 z = 1 ∨
                  torusPortPos occ b0 z = 2 := by omega
              rcases this with h0 | h1 | h2
              · simp [h0]
              · simp [h1]
              · simp [h2]
          have hpx' : p ∈ (if b0 then torusUpTri (4 * occ) 0 else torusDownTri (4 * occ) 0) := by
            dsimp only [occ]; rw [← hsig]; rw [hxj, hyj] at hxy; exact hxy.1
          have hqx' : q ∈ (if b0 then torusUpTri (4 * occ) 0 else torusDownTri (4 * occ) 0) := by
            dsimp only [occ]; rw [← hsig]; rw [hxj, hyj] at hxy; exact hxy.2
          obtain ⟨a, ha, hva, ha_p⟩ := hport_map p hp hpx'
          obtain ⟨b, hb, hvb, hb_p⟩ := hport_map q hq hqx'
          have hab_ne : a ≠ b := fun heq => by
            subst heq; exact huv.ne (hup.trans (hva.trans hvb.symm) |>.trans hvq.symm)
          have hdisj_r : (rStar j ≠ 0 → isInTri 0 3 6 a b = false) ∧
              (rStar j ≠ 1 → isInTri 1 4 6 a b = false) ∧
              (rStar j ≠ 2 → isInTri 7 2 5 a b = false) :=
            k333PortVert_disjoint_other (hrStar_lt3 j) ha_p hb_p hab_ne
          have hadj_ab : k333Adj a b = true :=
            k333ClauseAdj_to_k333Adj
              (glued_clause_induced hψ j.2 ha hb (hva ▸ hvb ▸ hup ▸ hvq ▸ huv))
          have hlen1 := (k333_part_exact ⟨rStar j, hrStar_lt3 j⟩ ⟨a, ha⟩ ⟨b, hb⟩).1
            ⟨hadj_ab, hdisj_r⟩
          obtain ⟨t, ht_eq⟩ := List.length_eq_one_iff.1 hlen1
          have ht_mem : t ∈ (k333PartTris (rStar j)).filter
              (fun t => isInTri t.1 t.2.1 t.2.2 a b) := by
            rw [ht_eq]; exact List.mem_singleton_self t
          obtain ⟨ht_in, hin⟩ := List.mem_filter.1 ht_mem
          refine ⟨clauseTri j t ht_in, Finset.mem_union_left _ ?_,
            (hcov_c j t ht_in).2 ⟨a, b, ha, hb, hup.trans hva, hvq.trans hvb, hin⟩⟩
          exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
            Finset.mem_image.2 ⟨⟨t, ht_in⟩, by simp, rfl⟩⟩
        · refine ⟨torusTri ⟨vi, hvi⟩ xy, Finset.mem_union_right _ ?_,
            (hcov_t ⟨vi, hvi⟩ xy).2 ⟨p, q, hp, hq, hup, hvq, hpq, hxy.1, hxy.2⟩⟩
          exact Finset.mem_biUnion.2 ⟨⟨vi, hvi⟩, Finset.mem_univ _,
            Finset.mem_image.2 ⟨xy, Finset.mem_filter.2 ⟨Finset.mem_univ _, hom⟩, rfl⟩⟩
    obtain ⟨T, hT, hTuv⟩ := hex
    refine ⟨T, ⟨hT, hTuv⟩, fun T' ⟨hT', hT'uv⟩ => ?_⟩
    rcases Finset.mem_union.1 hT with hTc | hTt <;> rcases Finset.mem_union.1 hT' with hT'c | hT't
    · exact (huniq_c T hTc T' hT'c hTuv hT'uv).symm
    · exact (hdisj_ct T hTc T' hT't ⟨hTuv.1, hTuv.2, hT'uv.1, hT'uv.2⟩).elim
    · exact (hdisj_ct T' hT'c T hTt ⟨hT'uv.1, hT'uv.2, hTuv.1, hTuv.2⟩).elim
    · exact (huniq_t T hTt T' hT't hTuv hT'uv).symm

/-! ### Backward Direction: `IsTriangleEdgePartition → Satisfiable` -/

private theorem torus_horiz_nonport_decide :
    ∀ x : Fin 12, ∀ y : Fin 4, ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
      let p := 4 * x.1 + y.1; let q := 4 * ((x.1 + 1) % 12) + y.1
      torusAdj p q = true ∧
      (∀ o : Fin 3, ¬ (p ∈ torusPortAll o.1 ∧ q ∈ torusPortAll o.1)) ∧
      p ∈ torusUpTri x.1 y.1 ∧ q ∈ torusUpTri x.1 y.1 ∧
      p ∈ torusDownTri x.1 y.1 ∧ q ∈ torusDownTri x.1 y.1 := by
  decide

private theorem torus_vert_nonport_decide :
    ∀ x : Fin 12, ∀ y : Fin 4,
      ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
      ¬ ((y + 1).1 = 0 ∧ ((x - 1).1 = 0 ∨ (x - 1).1 = 4 ∨ (x - 1).1 = 8)) →
      let p := 4 * x.1 + y.1; let q := 4 * x.1 + (y.1 + 1) % 4
      torusAdj p q = true ∧
      (∀ o : Fin 3, ¬ (p ∈ torusPortAll o.1 ∧ q ∈ torusPortAll o.1)) ∧
      p ∈ torusUpTri x.1 y.1 ∧ q ∈ torusUpTri x.1 y.1 ∧
      p ∈ torusDownTri (x - 1).1 (y + 1).1 ∧ q ∈ torusDownTri (x - 1).1 (y + 1).1 := by
  decide

private theorem torus_diag_nonport_decide :
    ∀ x : Fin 12, ∀ y : Fin 4,
      ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
      ¬ ((y + 1).1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
      let p := 4 * ((x.1 + 1) % 12) + y.1; let q := 4 * x.1 + (y.1 + 1) % 4
      torusAdj p q = true ∧
      (∀ o : Fin 3, ¬ (p ∈ torusPortAll o.1 ∧ q ∈ torusPortAll o.1)) ∧
      p ∈ torusUpTri x.1 y.1 ∧ q ∈ torusUpTri x.1 y.1 ∧
      p ∈ torusDownTri x.1 (y + 1).1 ∧ q ∈ torusDownTri x.1 (y + 1).1 := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    (intro h1 h2; dsimp only at h1 h2 ⊢; first
      | (exfalso; apply h1; decide)
      | (exfalso; apply h2; decide)
      | exact ⟨by decide, fun o => by fin_cases o <;> decide,
          by decide, by decide, by decide, by decide⟩)

private theorem buildGluedGraph_bwd {ψ : CNF ℕ} (hψ : NormProps ψ)
    (hpart : IsTriangleEdgePartition (buildGluedGraph ψ)) : ψ.Satisfiable := by
  classical
  obtain ⟨𝒯, hcl, hcov⟩ := (isTriangleEdgePartition_iff _).1 hpart
  set m := ψ.length
  set vars := ψ.distinctVars
  set k := vars.length
  set N := 9 * m + 48 * k
  have hmemN : ∀ x < N, x ∈ (buildGluedGraph ψ).vertices := fun x hx =>
    (mem_buildGluedGraph_vertices_iff ψ x).2 hx
  let mkV (x : ℕ) (hx : x < N) : {v // v ∈ (buildGluedGraph ψ).vertices} := ⟨x, hmemN x hx⟩
  let torusSet (vi : Fin k) (l : List ℕ)
      (hb : l.getD 0 0 < 48 ∧ l.getD 1 0 < 48 ∧ l.getD 2 0 < 48) :
      Finset {v // v ∈ (buildGluedGraph ψ).vertices} :=
    {mkV (torusVertexId ψ vars vi.1 (l.getD 0 0)) (torusVertexId_lt_bound hψ vi.2 hb.1),
     mkV (torusVertexId ψ vars vi.1 (l.getD 1 0)) (torusVertexId_lt_bound hψ vi.2 hb.2.1),
     mkV (torusVertexId ψ vars vi.1 (l.getD 2 0)) (torusVertexId_lt_bound hψ vi.2 hb.2.2)}
  let inUp (vi : Fin k) (xy : Fin 12 × Fin 4) : Prop :=
    torusSet vi (torusUpTri xy.1.1 xy.2.1)
      (let h := torus_up_adj xy.1 xy.2; ⟨h.1, h.2.1, h.2.2.1⟩) ∈ 𝒯
  let inDown (vi : Fin k) (xy : Fin 12 × Fin 4) : Prop :=
    torusSet vi (torusDownTri xy.1.1 xy.2.1)
      (let h := torus_down_adj xy.1 xy.2; ⟨h.1, h.2.1, h.2.2.1⟩) ∈ 𝒯
  have htor_edge_dichot : ∀ vi : Fin k, ∀ p q : Fin 48, torusAdj p.1 q.1 = true →
      (∀ occ : Fin 3, ¬ (p.1 ∈ torusPortAll occ.1 ∧ q.1 ∈ torusPortAll occ.1)) →
      ∀ xyU xyD : Fin 12 × Fin 4,
        (p.1 ∈ torusUpTri xyU.1.1 xyU.2.1 ∧ q.1 ∈ torusUpTri xyU.1.1 xyU.2.1) →
        (p.1 ∈ torusDownTri xyD.1.1 xyD.2.1 ∧ q.1 ∈ torusDownTri xyD.1.1 xyD.2.1) →
        (inUp vi xyU ↔ ¬ inDown vi xyD) := by
    intro vi p q hpq hnotp xyU xyD hU hD
    set u := mkV (torusVertexId ψ vars vi.1 p.1) (torusVertexId_lt_bound hψ vi.2 p.2)
    set v := mkV (torusVertexId ψ vars vi.1 q.1) (torusVertexId_lt_bound hψ vi.2 q.2)
    have huv : (buildGluedGraph ψ).induced.Adj u v := by
      rw [Graph.induced_adj]
      exact (glued_adj_iff hψ).2 (Or.inr ⟨vi.1, vi.2, p.1, q.1, hpq, rfl, rfl⟩)
    obtain ⟨T, ⟨hT, huT, hvT⟩, hTuniq⟩ := hcov u v huv
    have hmem_ts : ∀ (l : List ℕ) (hb) (z : Fin 48),
        mkV (torusVertexId ψ vars vi.1 z.1) (torusVertexId_lt_bound hψ vi.2 z.2) ∈
          torusSet vi l hb ↔
        z.1 = l.getD 0 0 ∨ z.1 = l.getD 1 0 ∨ z.1 = l.getD 2 0 := by
      intro l hb z
      simp only [torusSet, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (torusVertexId_inj hψ vi.2 z.2 hb.1 h)
        · exact Or.inr (Or.inl (torusVertexId_inj hψ vi.2 z.2 hb.2.1 h))
        · exact Or.inr (Or.inr (torusVertexId_inj hψ vi.2 z.2 hb.2.2 h))
      · rintro (h | h | h) <;> simp [h]
    have hbU : (torusUpTri xyU.1.1 xyU.2.1).getD 0 0 < 48 ∧
        (torusUpTri xyU.1.1 xyU.2.1).getD 1 0 < 48 ∧
        (torusUpTri xyU.1.1 xyU.2.1).getD 2 0 < 48 :=
      let h := torus_up_adj xyU.1 xyU.2; ⟨h.1, h.2.1, h.2.2.1⟩
    have hbD : (torusDownTri xyD.1.1 xyD.2.1).getD 0 0 < 48 ∧
        (torusDownTri xyD.1.1 xyD.2.1).getD 1 0 < 48 ∧
        (torusDownTri xyD.1.1 xyD.2.1).getD 2 0 < 48 :=
      let h := torus_down_adj xyD.1 xyD.2; ⟨h.1, h.2.1, h.2.2.1⟩
    have huU : u ∈ torusSet vi (torusUpTri xyU.1.1 xyU.2.1) hbU :=
      (hmem_ts _ hbU p).2 ((mem_torusUpTri_iff _ _ _).1 hU.1)
    have hvU : v ∈ torusSet vi (torusUpTri xyU.1.1 xyU.2.1) hbU :=
      (hmem_ts _ hbU q).2 ((mem_torusUpTri_iff _ _ _).1 hU.2)
    have huD : u ∈ torusSet vi (torusDownTri xyD.1.1 xyD.2.1) hbD :=
      (hmem_ts _ hbD p).2 ((mem_torusDownTri_iff _ _ _).1 hD.1)
    have hvD : v ∈ torusSet vi (torusDownTri xyD.1.1 xyD.2.1) hbD :=
      (hmem_ts _ hbD q).2 ((mem_torusDownTri_iff _ _ _).1 hD.2)
    have hnot_both : ¬ (inUp vi xyU ∧ inDown vi xyD) := by
      rintro ⟨h1, h2⟩
      have hset_eq := (hTuniq _ ⟨h1, huU, hvU⟩).trans (hTuniq _ ⟨h2, huD, hvD⟩).symm
      apply torus_up_ne_down xyU.1 xyD.1 xyU.2 xyD.2
      ext z
      by_cases hz48 : z < 48
      · have := Finset.ext_iff.1 hset_eq
          (mkV (torusVertexId ψ vars vi.1 z) (torusVertexId_lt_bound hψ vi.2 hz48))
        rw [hmem_ts (torusUpTri xyU.1.1 xyU.2.1)
            (let h := torus_up_adj xyU.1 xyU.2; ⟨h.1, h.2.1, h.2.2.1⟩) ⟨z, hz48⟩,
          hmem_ts (torusDownTri xyD.1.1 xyD.2.1)
            (let h := torus_down_adj xyD.1 xyD.2; ⟨h.1, h.2.1, h.2.2.1⟩) ⟨z, hz48⟩] at this
        simpa [mem_torusUpTri_iff, mem_torusDownTri_iff] using this
      · have h1' : z ∉ torusUpTri xyU.1.1 xyU.2.1 := fun hm => by
          have := torus_up_adj xyU.1 xyU.2
          rw [mem_torusUpTri_iff] at hm
          rcases hm with rfl | rfl | rfl <;> omega
        have h2' : z ∉ torusDownTri xyD.1.1 xyD.2.1 := fun hm => by
          have := torus_down_adj xyD.1 xyD.2
          rw [mem_torusDownTri_iff] at hm
          rcases hm with rfl | rfl | rfl <;> omega
        simp [h1', h2']
    have hT_eq : T = torusSet vi (torusUpTri xyU.1.1 xyU.2.1) hbU ∨
        T = torusSet vi (torusDownTri xyD.1.1 xyD.2.1) hbD := by
      have hT3 := hcl T hT
      have hcard_er : (T.erase u |>.erase v).card = 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨huv.ne.symm, hvT⟩),
          Finset.card_erase_of_mem huT, hT3.2]
      obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.1 hcard_er
      have hwT : w ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
        (hw_eq ▸ Finset.mem_singleton_self w))
      have hwu : w ≠ u := (Finset.mem_erase.1 (Finset.mem_of_mem_erase
        (hw_eq ▸ Finset.mem_singleton_self w))).1
      have hwv : w ≠ v := (Finset.mem_erase.1 (hw_eq ▸ Finset.mem_singleton_self w)).1
      have hT_triple : T = {u, v, w} := by
        ext x; constructor
        · intro hx
          by_cases hxu : x = u
          · simp [hxu]
          · by_cases hxv : x = v
            · simp [hxv]
            · have : x ∈ (T.erase u).erase v :=
                Finset.mem_erase.2 ⟨hxv, Finset.mem_erase.2 ⟨hxu, hx⟩⟩
              rw [hw_eq, Finset.mem_singleton] at this; simp [this]
        · intro hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
      have huw : (buildGluedGraph ψ).toSimpleGraph.Adj u.1 w.1 :=
        Graph.induced_adj.1 (hT3.1 huT hwT hwu.symm)
      have hvw : (buildGluedGraph ψ).toSimpleGraph.Adj v.1 w.1 :=
        Graph.induced_adj.1 (hT3.1 hvT hwT hwv.symm)
      have huv' : (buildGluedGraph ψ).toSimpleGraph.Adj u.1 v.1 := Graph.induced_adj.1 huv
      rcases glued_triangle_in_gadget hψ huv' hvw huw with
          ⟨j, hj, a, b, _, ha, hb, _, hua, hvb, _⟩ |
          ⟨vi', hvi', p', q', r', hp', hq', hr', hup', hvq', hwr'⟩
      · exfalso
        obtain ⟨hr1, hpos1, _⟩ := (torusVertexId_eq_clause_iff hψ vi.2 p.2 hj ha).1 hua
        obtain ⟨_, hpos2, _⟩ := (torusVertexId_eq_clause_iff hψ vi.2 q.2 hj hb).1 hvb
        have hspec := (clauseLitPos_spec hψ hj).1 hr1
        have hocc_lt : (CNF.vars (ψ.take j)).count (vars.getD vi.1 0) < 3 := by
          rw [← hspec.2]; exact occ_lt_three hψ hj hspec.1
        exact hnotp ⟨_, hocc_lt⟩ ⟨torusPortPos_lt_three_mem hpos1, torusPortPos_lt_three_mem hpos2⟩
      · have hvi_eq : vi.1 = vi' := by
          by_contra hne
          exact torus_inter_no_adj hψ vi.2 hvi' hne p.2 hp' q.2 hq' hup' hvq' hpq
        subst hvi_eq
        have hp_eq : p.1 = p' := torusVertexId_inj hψ vi.2 p.2 hp' hup'
        have hq_eq : q.1 = q' := torusVertexId_inj hψ vi.2 q.2 hq' hvq'
        subst hp_eq; subst hq_eq
        have hpr : torusAdj p.1 r' = true := glued_torus_induced hψ vi.2 p.2 hr' (hwr' ▸ huw)
        have hqr : torusAdj q.1 r' = true := glued_torus_induced hψ vi.2 q.2 hr' (hwr' ▸ hvw)
        have hclass := torus_tri_class_aux p q.1 ((mem_torusNbrs_iff p q.1).2 hpq)
          r' ((mem_torusNbrs_iff p r').2 hpr) hqr
        have hmatch_tri : ∀ (isU : Bool) (x0 : Fin 12) (y0 : Fin 4),
            let l := if isU then torusUpTri x0.1 y0.1 else torusDownTri x0.1 y0.1
            isSameTri p.1 q.1 r' (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) = true →
            T = torusSet vi l (by
              dsimp only [l]; cases isU
              · have h := torus_down_adj x0 y0; exact ⟨h.1, h.2.1, h.2.2.1⟩
              · have h := torus_up_adj x0 y0; exact ⟨h.1, h.2.1, h.2.2.1⟩) ∧
            p.1 ∈ l ∧ q.1 ∈ l := by
          intro isU x0 y0 l hsame
          rw [isSameTri_eq_true_iff] at hsame
          have hmem_l : ∀ z, z ∈ l ↔ z = l.getD 0 0 ∨ z = l.getD 1 0 ∨ z = l.getD 2 0 := by
            intro z; dsimp only [l]
            cases isU
            · exact mem_torusDownTri_iff x0.1 y0.1 z
            · exact mem_torusUpTri_iff x0.1 y0.1 z
          refine ⟨?_, (hmem_l _).2 hsame.1, (hmem_l _).2 hsame.2.1⟩
          rw [hT_triple]
          ext z; simp only [Finset.mem_insert, Finset.mem_singleton, torusSet]
          constructor
          · rintro (rfl | rfl | rfl)
            · rcases hsame.1 with h | h | h <;> simp [u, mkV, h]
            · rcases hsame.2.1 with h | h | h <;> simp [v, mkV, h]
            · rcases hsame.2.2.1 with h | h | h
              · left; exact Subtype.ext (by rw [hwr']; dsimp only [mkV]; rw [h])
              · right; left; exact Subtype.ext (by rw [hwr']; dsimp only [mkV]; rw [h])
              · right; right; exact Subtype.ext (by rw [hwr']; dsimp only [mkV]; rw [h])
          · rintro (h | h | h)
            · rcases hsame.2.2.2.1 with h' | h' | h'
              · left; exact Subtype.ext (by rw [h]; dsimp only [u, mkV]; rw [h'])
              · right; left; exact Subtype.ext (by rw [h]; dsimp only [v, mkV]; rw [h'])
              · right; right; exact Subtype.ext (by rw [h, hwr']; dsimp only [mkV]; rw [h'])
            · rcases hsame.2.2.2.2.1 with h' | h' | h'
              · left; exact Subtype.ext (by rw [h]; dsimp only [u, mkV]; rw [h'])
              · right; left; exact Subtype.ext (by rw [h]; dsimp only [v, mkV]; rw [h'])
              · right; right; exact Subtype.ext (by rw [h, hwr']; dsimp only [mkV]; rw [h'])
            · rcases hsame.2.2.2.2.2 with h' | h' | h'
              · left; exact Subtype.ext (by rw [h]; dsimp only [u, mkV]; rw [h'])
              · right; left; exact Subtype.ext (by rw [h]; dsimp only [v, mkV]; rw [h'])
              · right; right; exact Subtype.ext (by rw [h, hwr']; dsimp only [mkV]; rw [h'])
        rw [torusTriClass_eq_true_iff] at hclass
        have hfin_lt : ∀ n : ℕ, n % 12 < 12 := fun n => Nat.mod_lt _ (by decide)
        have hfin_lt4 : ∀ n : ℕ, n % 4 < 4 := fun n => Nat.mod_lt _ (by decide)
        have hxp : p.1 / 4 < 12 := by have := p.2; omega
        have hyp : p.1 % 4 < 4 := Nat.mod_lt _ (by decide)
        rcases hclass with h | h | h | h | h | h
        · obtain ⟨hTeq, hp1, hq1⟩ := hmatch_tri true ⟨p.1 / 4, hxp⟩ ⟨p.1 % 4, hyp⟩ h
          have heq : (⟨p.1 / 4, hxp⟩, ⟨p.1 % 4, hyp⟩) = xyU :=
            (torus_edge_unique_up p q hpq).unique ⟨hp1, hq1⟩ hU
          left; cases heq; exact hTeq
        · obtain ⟨hTeq, hp1, hq1⟩ := hmatch_tri true ⟨(p.1 / 4 + 11) % 12, hfin_lt _⟩
            ⟨p.1 % 4, hyp⟩ h
          have heq : (⟨(p.1 / 4 + 11) % 12, hfin_lt _⟩, ⟨p.1 % 4, hyp⟩) = xyU :=
            (torus_edge_unique_up p q hpq).unique ⟨hp1, hq1⟩ hU
          left; cases heq; exact hTeq
        · obtain ⟨hTeq, hp1, hq1⟩ := hmatch_tri true ⟨p.1 / 4, hxp⟩
            ⟨(p.1 % 4 + 3) % 4, hfin_lt4 _⟩ h
          have heq : (⟨p.1 / 4, hxp⟩, ⟨(p.1 % 4 + 3) % 4, hfin_lt4 _⟩) = xyU :=
            (torus_edge_unique_up p q hpq).unique ⟨hp1, hq1⟩ hU
          left; cases heq; exact hTeq
        · obtain ⟨hTeq, hp1, hq1⟩ := hmatch_tri false ⟨p.1 / 4, hxp⟩ ⟨p.1 % 4, hyp⟩ h
          have heq : (⟨p.1 / 4, hxp⟩, ⟨p.1 % 4, hyp⟩) = xyD :=
            (torus_edge_unique_down p q hpq).unique ⟨hp1, hq1⟩ hD
          right; cases heq; exact hTeq
        · obtain ⟨hTeq, hp1, hq1⟩ := hmatch_tri false ⟨(p.1 / 4 + 11) % 12, hfin_lt _⟩
            ⟨p.1 % 4, hyp⟩ h
          have heq : (⟨(p.1 / 4 + 11) % 12, hfin_lt _⟩, ⟨p.1 % 4, hyp⟩) = xyD :=
            (torus_edge_unique_down p q hpq).unique ⟨hp1, hq1⟩ hD
          right; cases heq; exact hTeq
        · obtain ⟨hTeq, hp1, hq1⟩ := hmatch_tri false ⟨(p.1 / 4 + 11) % 12, hfin_lt _⟩
            ⟨(p.1 % 4 + 1) % 4, hfin_lt4 _⟩ h
          have heq : (⟨(p.1 / 4 + 11) % 12, hfin_lt _⟩, ⟨(p.1 % 4 + 1) % 4, hfin_lt4 _⟩) = xyD :=
            (torus_edge_unique_down p q hpq).unique ⟨hp1, hq1⟩ hD
          right; cases heq; exact hTeq
    constructor
    · intro h1 h2; exact hnot_both ⟨h1, h2⟩
    · intro hnotD
      rcases hT_eq with rfl | rfl
      · exact hT
      · exact (hnotD hT).elim
  have hforced : ∀ vi : Fin k, ∀ x : Fin 12, ∀ y : Fin 4,
      ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
      (inUp vi (x, y) ↔ inUp vi (0, 1)) ∧ (inDown vi (x, y) ↔ ¬ inUp vi (0, 1)) := by
    intro vi
    have hhoriz_aux : ∀ x : Fin 12, ∀ y : Fin 4,
        ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
        (inUp vi (x, y) ↔ ¬ inDown vi (x, y)) := by
      intro x y hnp
      set p : Fin 48 := ⟨4 * x.1 + y.1, by omega⟩
      set q : Fin 48 := ⟨4 * ((x.1 + 1) % 12) + y.1,
        by have := Nat.mod_lt (x.1 + 1) (by decide : 0 < 12); omega⟩
      have hd := torus_horiz_nonport_decide x y hnp
      exact htor_edge_dichot vi p q hd.1 hd.2.1 (x, y) (x, y)
        ⟨hd.2.2.1, hd.2.2.2.1⟩ ⟨hd.2.2.2.2.1, hd.2.2.2.2.2⟩
    have hvert_aux : ∀ x : Fin 12, ∀ y : Fin 4,
        ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
        ¬ ((y + 1).1 = 0 ∧ ((x - 1).1 = 0 ∨ (x - 1).1 = 4 ∨ (x - 1).1 = 8)) →
        (inUp vi (x, y) ↔ ¬ inDown vi (x - 1, y + 1)) := by
      intro x y hnp1 hnp2
      set p : Fin 48 := ⟨4 * x.1 + y.1, by omega⟩
      set q : Fin 48 := ⟨4 * x.1 + (y.1 + 1) % 4,
        by have := Nat.mod_lt (y.1 + 1) (by decide : 0 < 4); omega⟩
      have hd := torus_vert_nonport_decide x y hnp1 hnp2
      exact htor_edge_dichot vi p q hd.1 hd.2.1 (x, y) (x - 1, y + 1)
        ⟨hd.2.2.1, hd.2.2.2.1⟩ ⟨hd.2.2.2.2.1, hd.2.2.2.2.2⟩
    have hdiag_aux : ∀ x : Fin 12, ∀ y : Fin 4,
        ¬ (y.1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
        ¬ ((y + 1).1 = 0 ∧ (x.1 = 0 ∨ x.1 = 4 ∨ x.1 = 8)) →
        (inUp vi (x, y) ↔ ¬ inDown vi (x, y + 1)) := by
      intro x y hnp1 hnp2
      set p : Fin 48 := ⟨4 * ((x.1 + 1) % 12) + y.1,
        by have := Nat.mod_lt (x.1 + 1) (by decide : 0 < 12); omega⟩
      set q : Fin 48 := ⟨4 * x.1 + (y.1 + 1) % 4,
        by have := Nat.mod_lt (y.1 + 1) (by decide : 0 < 4); omega⟩
      have hd := torus_diag_nonport_decide x y hnp1 hnp2
      exact htor_edge_dichot vi p q hd.1 hd.2.1 (x, y) (x, y + 1)
        ⟨hd.2.2.1, hd.2.2.2.1⟩ ⟨hd.2.2.2.2.1, hd.2.2.2.2.2⟩
    exact torus_nonport_forcing (inUp vi) (inDown vi) hhoriz_aux hvert_aux hdiag_aux
  let σ : ℕ → Bool := fun v =>
    if hv : v ∈ vars then decide (inUp ⟨vars.idxOf v, List.idxOf_lt_length_iff.2 hv⟩ (0, 1))
    else false
  refine ⟨σ, (CNF.eval_eq_true_iff σ ψ).2 fun c hc => ?_⟩
  obtain ⟨j, hj, hcj⟩ := List.mem_iff_getElem.1 hc
  rw [← List.getD_eq_getElem ψ [] hj] at hcj
  subst hcj
  by_contra hunsat
  have hblocked : ∀ r < (ψ.getD j []).length,
      ∃ T0 ∈ 𝒯,
        mkV (9 * j + k333PortVert r 1) (by
          have := k333PortVert_lt_nine r 1; omega) ∈ T0 ∧
        mkV (9 * j + k333PortVert r 2) (by
          have := k333PortVert_lt_nine r 2; omega) ∈ T0 ∧
        ∃ x0 : {v // v ∈ (buildGluedGraph ψ).vertices}, x0 ∈ T0 ∧ x0.1 ≥ 9 * m := by
    intro r hr
    set l := (ψ.getD j []).getD r (0, false)
    have hl_mem : l ∈ ψ.getD j [] := by
      dsimp only [l]; rw [List.getD_eq_getElem _ _ hr]; exact List.getElem_mem hr
    have hfal : σ l.1 ≠ l.2 := fun heq =>
      hunsat ((Clause.eval_eq_true_iff σ _).2 ⟨l, hl_mem, heq⟩)
    have hv_mem : l.1 ∈ vars := by
      rw [CNF.mem_distinctVars, CNF.mem_vars]
      exact ⟨ψ.getD j [], hc, l.2, hl_mem⟩
    set vi : Fin k := ⟨vars.idxOf l.1, List.idxOf_lt_length_iff.2 hv_mem⟩
    have hv_get : vars.getD vi.1 0 = l.1 := by
      rw [List.getD_eq_getElem _ _ vi.2]; exact List.getElem_idxOf vi.2
    set occ := (CNF.vars (ψ.take j)).count l.1
    have hocc_lt : occ < 3 := occ_lt_three hψ hj hr
    have hr_pos : clauseLitPos (ψ.getD j []) l.1 = r := clauseLitPos_unique hψ hj hr
    have hr_lt3 : r < 3 := lt_of_lt_of_le hr (hψ.clause_len_le _ hc)
    let p1 : ℕ := 4 * (4 * occ + 1)
    let p2 : ℕ := if l.2 then 4 * (4 * occ) + 1 else 4 * (4 * occ + 1) + 3
    have hp1 : p1 < 48 := by omega
    have hp2 : p2 < 48 := by dsimp only [p2]; split_ifs <;> omega
    have hvp1 : torusVertexId ψ vars vi.1 p1 = 9 * j + k333PortVert r 1 := by
      rw [torusVertexId_eq_clause_iff hψ vi.2 hp1 hj (k333PortVert_lt_nine r 1)]
      simp only [vars, hv_get, hr_pos, hr_lt3, true_and]
      have hpp1 : torusPortPos occ l.2 p1 = 1 := torusPortPos_eq_self occ l.2 1 (by decide)
      dsimp only [occ, l] at hpp1 ⊢
      rw [hpp1]; exact ⟨by decide, rfl⟩
    have hvp2 : torusVertexId ψ vars vi.1 p2 = 9 * j + k333PortVert r 2 := by
      rw [torusVertexId_eq_clause_iff hψ vi.2 hp2 hj (k333PortVert_lt_nine r 2)]
      simp only [vars, hv_get, hr_pos, hr_lt3, true_and]
      have hpp2 : torusPortPos occ l.2 p2 = 2 := torusPortPos_eq_self occ l.2 2 (by decide)
      dsimp only [occ, l] at hpp2 ⊢
      rw [hpp2]; exact ⟨by decide, rfl⟩
    cases hb : l.2
    · have hsig_t : inUp vi (0, 1) := by
        have : σ l.1 = true := by cases h : σ l.1 <;> simp_all
        simpa [σ, hv_mem] using this
      set xy0 : Fin 12 × Fin 4 := (⟨4 * occ + 1, by omega⟩, 3)
      have hb0 : (torusUpTri xy0.1.1 xy0.2.1).getD 0 0 < 48 ∧
          (torusUpTri xy0.1.1 xy0.2.1).getD 1 0 < 48 ∧
          (torusUpTri xy0.1.1 xy0.2.1).getD 2 0 < 48 :=
        let h := torus_up_adj xy0.1 xy0.2; ⟨h.1, h.2.1, h.2.2.1⟩
      have hT0_in : torusSet vi (torusUpTri xy0.1.1 xy0.2.1) hb0 ∈ 𝒯 :=
        ((hforced vi xy0.1 xy0.2 (by dsimp [xy0]; omega)).1).2 hsig_t
      set p3 : ℕ := 4 * ((4 * occ + 2) % 12) + 3
      have hp3_lt : p3 < 48 := by have := Nat.mod_lt (4 * occ + 2) (by decide : 0 < 12); omega
      have hp_mem : p1 ∈ torusUpTri xy0.1.1 xy0.2.1 ∧ p2 ∈ torusUpTri xy0.1.1 xy0.2.1 ∧
          p3 ∈ torusUpTri xy0.1.1 xy0.2.1 := by
        have hdec : ∀ o : Fin 3,
            4 * (4 * o.1 + 1) ∈ torusUpTri (4 * o.1 + 1) 3 ∧
            4 * (4 * o.1 + 1) + 3 ∈ torusUpTri (4 * o.1 + 1) 3 ∧
            4 * ((4 * o.1 + 2) % 12) + 3 ∈ torusUpTri (4 * o.1 + 1) 3 := by decide
        simpa [p1, p2, hb, p3, xy0] using hdec ⟨occ, hocc_lt⟩
      have hp3_own : torusVertexId ψ vars vi.1 p3 ≥ 9 * m := by
        by_contra hlt; push Not at hlt
        set j3 := torusVertexId ψ vars vi.1 p3 / 9
        set u3 := torusVertexId ψ vars vi.1 p3 % 9
        have hj3 : j3 < m := by omega
        have hu3 : u3 < 9 := by omega
        obtain ⟨hr3, hpos3, _⟩ :=
          (torusVertexId_eq_clause_iff hψ vi.2 hp3_lt hj3 hu3).1
            (by dsimp only [j3, u3, vars]; omega)
        have hp3_port := torusPortPos_lt_three_mem hpos3
        have hspec3 := (clauseLitPos_spec hψ hj3).1 hr3
        have hocc3 : (CNF.vars (ψ.take j3)).count l.1 < 3 := by
          rw [← hv_get, ← hspec3.2]; exact occ_lt_three hψ hj3 hspec3.1
        have hdec : ∀ o : Fin 3, ∀ o' : Fin 3,
            4 * ((4 * o.1 + 2) % 12) + 3 ∉ torusPortAll o'.1 := by decide
        exact hdec ⟨occ, hocc_lt⟩ ⟨_, hocc3⟩ (by
          change p3 ∈ torusPortAll ((CNF.vars (ψ.take j3)).count (vars.getD vi.1 0)) at hp3_port
          rw [hv_get] at hp3_port; exact hp3_port)
      refine ⟨torusSet vi (torusUpTri xy0.1.1 xy0.2.1) hb0, hT0_in, ?_, ?_,
        mkV (torusVertexId ψ vars vi.1 p3) (torusVertexId_lt_bound hψ vi.2 hp3_lt), ?_, hp3_own⟩
      · simp only [torusSet, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV, ← hvp1]
        rcases (mem_torusUpTri_iff _ _ _).1 hp_mem.1 with h | h | h <;> simp [h]
      · simp only [torusSet, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV, ← hvp2]
        rcases (mem_torusUpTri_iff _ _ _).1 hp_mem.2.1 with h | h | h <;> simp [h]
      · simp only [torusSet, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV]
        rcases (mem_torusUpTri_iff _ _ _).1 hp_mem.2.2 with h | h | h <;> simp [h]
    · have hsig_f : ¬ inUp vi (0, 1) := by
        have : σ l.1 = false := by cases h : σ l.1 <;> simp_all
        simpa [σ, hv_mem] using this
      set xy0 : Fin 12 × Fin 4 := (⟨4 * occ, by omega⟩, 1)
      have hb0 : (torusDownTri xy0.1.1 xy0.2.1).getD 0 0 < 48 ∧
          (torusDownTri xy0.1.1 xy0.2.1).getD 1 0 < 48 ∧
          (torusDownTri xy0.1.1 xy0.2.1).getD 2 0 < 48 :=
        let h := torus_down_adj xy0.1 xy0.2; ⟨h.1, h.2.1, h.2.2.1⟩
      have hT0_in : torusSet vi (torusDownTri xy0.1.1 xy0.2.1) hb0 ∈ 𝒯 :=
        ((hforced vi xy0.1 xy0.2 (by dsimp [xy0]; omega)).2).2 hsig_f
      set p3 : ℕ := 4 * (4 * occ + 1) + 1
      have hp3_lt : p3 < 48 := by omega
      have hp_mem : p1 ∈ torusDownTri xy0.1.1 xy0.2.1 ∧ p2 ∈ torusDownTri xy0.1.1 xy0.2.1 ∧
          p3 ∈ torusDownTri xy0.1.1 xy0.2.1 := by
        have hdec : ∀ o : Fin 3,
            4 * (4 * o.1 + 1) ∈ torusDownTri (4 * o.1) 1 ∧
            4 * (4 * o.1) + 1 ∈ torusDownTri (4 * o.1) 1 ∧
            4 * (4 * o.1 + 1) + 1 ∈ torusDownTri (4 * o.1) 1 := by decide
        simpa [p1, p2, hb, p3, xy0] using hdec ⟨occ, hocc_lt⟩
      have hp3_own : torusVertexId ψ vars vi.1 p3 ≥ 9 * m := by
        by_contra hlt; push Not at hlt
        set j3 := torusVertexId ψ vars vi.1 p3 / 9
        set u3 := torusVertexId ψ vars vi.1 p3 % 9
        have hj3 : j3 < m := by omega
        have hu3 : u3 < 9 := by omega
        obtain ⟨hr3, hpos3, _⟩ :=
          (torusVertexId_eq_clause_iff hψ vi.2 hp3_lt hj3 hu3).1
            (by dsimp only [j3, u3, vars]; omega)
        have hp3_port := torusPortPos_lt_three_mem hpos3
        have hspec3 := (clauseLitPos_spec hψ hj3).1 hr3
        have hocc3 : (CNF.vars (ψ.take j3)).count l.1 < 3 := by
          rw [← hv_get, ← hspec3.2]; exact occ_lt_three hψ hj3 hspec3.1
        have hdec : ∀ o : Fin 3, ∀ o' : Fin 3,
            4 * (4 * o.1 + 1) + 1 ∉ torusPortAll o'.1 := by decide
        exact hdec ⟨occ, hocc_lt⟩ ⟨_, hocc3⟩ (by
          change p3 ∈ torusPortAll ((CNF.vars (ψ.take j3)).count (vars.getD vi.1 0)) at hp3_port
          rw [hv_get] at hp3_port; exact hp3_port)
      refine ⟨torusSet vi (torusDownTri xy0.1.1 xy0.2.1) hb0, hT0_in, ?_, ?_,
        mkV (torusVertexId ψ vars vi.1 p3) (torusVertexId_lt_bound hψ vi.2 hp3_lt), ?_, hp3_own⟩
      · simp only [torusSet, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV, ← hvp1]
        rcases (mem_torusDownTri_iff _ _ _).1 hp_mem.1 with h | h | h <;> simp [h]
      · simp only [torusSet, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV, ← hvp2]
        rcases (mem_torusDownTri_iff _ _ _).1 hp_mem.2.1 with h | h | h <;> simp [h]
      · simp only [torusSet, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, mkV]
        rcases (mem_torusDownTri_iff _ _ _).1 hp_mem.2.2 with h | h | h <;> simp [h]
  set u2 := mkV (9 * j + 2) (by omega)
  set v6 := mkV (9 * j + 6) (by omega)
  have h26 : (buildGluedGraph ψ).induced.Adj u2 v6 := by
    rw [Graph.induced_adj]
    exact (glued_adj_iff hψ).2 (Or.inl ⟨j, hj, 2, 6, k333ClauseAdj_two_six _, rfl, rfl⟩)
  obtain ⟨T, ⟨hT, hu2T, hv6T⟩, _⟩ := hcov u2 v6 h26
  have hT3 := hcl T hT
  have hcard_er : (T.erase u2 |>.erase v6).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨h26.ne.symm, hv6T⟩),
      Finset.card_erase_of_mem hu2T, hT3.2]
  obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.1 hcard_er
  have hwT : w ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
    (hw_eq ▸ Finset.mem_singleton_self w))
  have hwu : w ≠ u2 := (Finset.mem_erase.1 (Finset.mem_of_mem_erase
    (hw_eq ▸ Finset.mem_singleton_self w))).1
  have hwv : w ≠ v6 := (Finset.mem_erase.1 (hw_eq ▸ Finset.mem_singleton_self w)).1
  have h2w : (buildGluedGraph ψ).toSimpleGraph.Adj (9 * j + 2) w.1 :=
    Graph.induced_adj.1 (hT3.1 hu2T hwT hwu.symm)
  have h6w : (buildGluedGraph ψ).toSimpleGraph.Adj (9 * j + 6) w.1 :=
    Graph.induced_adj.1 (hT3.1 hv6T hwT hwv.symm)
  have h26' : (buildGluedGraph ψ).toSimpleGraph.Adj (9 * j + 2) (9 * j + 6) :=
    Graph.induced_adj.1 h26
  rcases glued_triangle_in_gadget hψ h26' h6w h2w with
      ⟨j', _, a, b, c, _, _, hc', h1, h2, h3⟩ | ⟨vi, hvi, p, q, _, hp, hq, _, h1, h2, _⟩
  · have hjeq : j' = j := by omega
    subst j'
    have ha2 : a = 2 := by omega
    have hb6 : b = 6 := by omega
    subst ha2; subst hb6
    have hc2w : k333ClauseAdj (ψ.getD j []).length 2 c = true :=
      glued_clause_induced hψ hj (by omega) hc' (h3 ▸ h2w)
    have hc6w : k333ClauseAdj (ψ.getD j []).length 6 c = true :=
      glued_clause_induced hψ hj (by omega) hc' (h3 ▸ h6w)
    have hlen_pos := hψ.clause_len_pos _ hc
    have hmem_T3 : ∀ x0 ∈ T, x0 = u2 ∨ x0 = v6 ∨ x0 = w := fun x0 hx0 => by
      by_cases h1' : x0 = u2
      · exact Or.inl h1'
      · by_cases h2' : x0 = v6
        · exact Or.inr (Or.inl h2')
        · have : x0 ∈ (T.erase u2).erase v6 :=
            Finset.mem_erase.2 ⟨h2', Finset.mem_erase.2 ⟨h1', hx0⟩⟩
          rw [hw_eq, Finset.mem_singleton] at this; exact Or.inr (Or.inr this)
    rcases k333_edge26_blocked (ψ.getD j []).length hlen_pos c hc2w hc6w with
        ⟨rfl, _⟩ | ⟨rfl, hge2, _⟩ | ⟨rfl, hge3, _⟩
    · obtain ⟨T0, hT0, h3_in, h6_in, x0, hx0, hx0_ge⟩ := hblocked 0 hlen_pos
      have h36 : (buildGluedGraph ψ).induced.Adj
          (mkV (9 * j + 3) (by omega)) (mkV (9 * j + 6) (by omega)) := by
        rw [Graph.induced_adj]; dsimp only [mkV]; rw [← h3]; exact h6w.symm
      have heq1 : T = T0 := (hcov _ _ h36).unique
        ⟨hT, by rw [show mkV (9 * j + 3) (by omega) = w from Subtype.ext h3.symm]; exact hwT, hv6T⟩
        ⟨hT0, h3_in, h6_in⟩
      subst heq1
      rcases hmem_T3 x0 hx0 with rfl | rfl | rfl <;> simp [u2, v6, mkV] at hx0_ge <;> omega
    · obtain ⟨T0, hT0, h4_in, h6_in, x0, hx0, hx0_ge⟩ := hblocked 1 (by omega)
      have h46 : (buildGluedGraph ψ).induced.Adj
          (mkV (9 * j + 4) (by omega)) (mkV (9 * j + 6) (by omega)) := by
        rw [Graph.induced_adj]; dsimp only [mkV]; rw [← h3]; exact h6w.symm
      have heq1 : T = T0 := (hcov _ _ h46).unique
        ⟨hT, by rw [show mkV (9 * j + 4) (by omega) = w from Subtype.ext h3.symm]; exact hwT, hv6T⟩
        ⟨hT0, h4_in, h6_in⟩
      subst heq1
      rcases hmem_T3 x0 hx0 with rfl | rfl | rfl <;> simp [u2, v6, mkV] at hx0_ge <;> omega
    · obtain ⟨T0, hT0, h2_in, h5_in, x0, hx0, hx0_ge⟩ := hblocked 2 (by omega)
      have h25 : (buildGluedGraph ψ).induced.Adj
          (mkV (9 * j + 2) (by omega)) (mkV (9 * j + 5) (by omega)) := by
        rw [Graph.induced_adj]; dsimp only [mkV]; rw [← h3]; exact h2w
      have heq1 : T = T0 := (hcov _ _ h25).unique
        ⟨hT, hu2T, by rw [show mkV (9 * j + 5) (by omega) = w from Subtype.ext h3.symm]; exact hwT⟩
        ⟨hT0, h2_in, h5_in⟩
      subst heq1
      rcases hmem_T3 x0 hx0 with rfl | rfl | rfl <;> simp [u2, v6, mkV] at hx0_ge <;> omega
  · obtain ⟨_, _, hu2_eq⟩ := (torusVertexId_eq_clause_iff hψ hvi hp hj (by omega)).1 h1.symm
    obtain ⟨_, _, hv6_eq⟩ := (torusVertexId_eq_clause_iff hψ hvi hq hj (by omega)).1 h2.symm
    exact k333PortVert_ne_two_six _ _ _ ⟨hu2_eq.symm, hv6_eq.symm⟩

/-! ### Equivalence and NP-Hardness -/

/-- Exact Karp equivalence between `ThreeSATThree` and `K4FreeTrianglePartition`. -/
theorem threeSATThreeToTriGraph_mem_iff (φ : CNF ℕ) :
    threeSATThreeToTriGraph φ ∈ K4FreeTrianglePartition ↔ φ ∈ ThreeSATThree := by
  rw [mem_K4FreeTrianglePartition, threeSATThreeToTriGraph_eq]
  dsimp only
  by_cases hsyn : ThreeSATThree.syntaxCheck φ = true
  · rw [ite_eq_left hsyn]
    have hsyn' := (ThreeSATThree.syntaxCheck_iff φ).1 hsyn
    by_cases hany : (normCNF φ).any List.isEmpty = true
    · rw [ite_eq_left hany]
      simp only [noTriGraph_not_triPart, and_false, false_iff]
      intro hmem
      obtain ⟨σ, hσ⟩ := hmem.2.2
      obtain ⟨c, hc, hce⟩ := List.any_eq_true.1 hany
      have hev := (CNF.eval_eq_true_iff σ (normCNF φ)).1
        (by rw [normCNF_eval hsyn'.1 σ]; exact hσ) c hc
      have hnil : c = [] := List.isEmpty_iff.1 hce
      subst hnil; simp at hev
    · rw [ite_eq_right hany]
      have hne : (normCNF φ).any List.isEmpty = false := Bool.eq_false_iff.2 hany
      by_cases hlen : (normCNF φ).length = 0
      · rw [ite_eq_left hlen]
        have hempty := mem_K4FreeTrianglePartition.1 emptyTriGraph_mem
        refine ⟨fun _ => ?_, fun _ => hempty⟩
        refine ⟨hsyn'.1, hsyn'.2, ?_⟩
        have hnil : normCNF φ = [] := List.eq_nil_of_length_eq_zero hlen
        exact ⟨fun _ => false, by rw [← normCNF_eval hsyn'.1, hnil]; rfl⟩
      · rw [ite_eq_right hlen]
        have hprops := normCNF_props hsyn' hne
        have hsat_iff : (normCNF φ).Satisfiable ↔ φ.Satisfiable := by
          unfold CNF.Satisfiable
          exact exists_congr fun σ => by rw [normCNF_eval hsyn'.1 σ]
        constructor
        · intro ⟨_, hpart⟩
          exact ⟨hsyn'.1, hsyn'.2, hsat_iff.1 (buildGluedGraph_bwd hprops hpart)⟩
        · intro hmem
          exact ⟨buildGluedGraph_k4Free hprops,
            buildGluedGraph_fwd hprops (hsat_iff.2 hmem.2.2)⟩
  · rw [ite_eq_right hsyn]
    simp only [noTriGraph_not_triPart, and_false, false_iff]
    intro hmem
    exact hsyn ((ThreeSATThree.syntaxCheck_iff φ).2 ⟨hmem.1, hmem.2.1⟩)

/-- **NP-hardness of triangle edge-partition on $K_4$-free graphs**, proved directly under
standard Lean axioms from `Cslib.Complexity.ThreeSATThree_npHard`. -/
theorem K4FreeTrianglePartition_npHard : NPHard encGraph K4FreeTrianglePartition :=
  ThreeSATThree_npHard.trans
    ⟨threeSATThreeToTriGraph, computableInPolyTime_threeSATThreeToTriGraph,
      fun φ => (threeSATThreeToTriGraph_mem_iff φ).symm⟩

end Cslib.Complexity
