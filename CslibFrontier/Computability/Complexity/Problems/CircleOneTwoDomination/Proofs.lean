module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CircleOneTwoDomination.Gadget

import Mathlib.Data.Finset.Max
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

/-!
# Soundness and Completeness of the Circle-Graph `[1, 2]`-Domination Gadget

Proves forward completeness (`sat_imp_dom`) and reverse soundness (`dom_imp_sat`) for the
clause-and-consistency circle-graph reduction from `EUThreeSAT`.
-/

public section

namespace Cslib.Complexity.CircleOneTwoDomination

open Cslib.Logic.PL Cslib.Complexity

/-! ### Soundness and Completeness of the Reduction Gadget -/

private theorem clauseDomList_tf_mem (b0 b1 b2 : Bool) (r : Fin 3) (fl' : Bool) :
    (⟨6 * r.1 + (if fl' then 0 else 5), by
      have := r.2; cases fl' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩ : Fin 34) ∈
      clauseDomList b0 b1 b2 ↔
      (match r.1 with | 0 => b0 | 1 => b1 | _ => b2) = fl' := by
  revert b0 b1 b2 r fl'; decide

private theorem not_adj_clause_claw {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct)
    {v iu bu qu : ℕ} (hv : v < 34 * φ.length) (hiu : iu < 3 * φ.length)
    (hnu : (nextOcc φ iu).isSome = true) (hbu : bu < 2) (hqu1 : 1 ≤ qu) (hqu : qu < 5)
    (hadj : (reductionGraph φ).toSimpleGraph.Adj v (34 * φ.length + 5 * (2 * iu + bu) + qu)) :
    False := by
  have hclaw := (claw_adj_iff hφ hiu hnu hbu hqu1 hqu (mem_redVertices_iff.mpr (Or.inl hv))).mp hadj
  split_ifs at hclaw
  · rcases hclaw with h | h | h | h <;> omega
  · omega

private theorem list_range_split {n k : ℕ} (hk : k < n) :
    List.range n = List.range k ++ k :: (List.range n).drop (k + 1) := by
  conv_lhs => rw [← List.take_append_drop k (List.range n)]
  rw [List.take_range, min_eq_left (le_of_lt hk), List.drop_eq_getElem_cons (by simp [hk]),
    List.getElem_range]

private theorem dom_adj_of_adjBool {φ : CNF ℕ} {D : Finset ℕ}
    (hD_dom' : ∀ v ∈ redVertices φ, v ∉ D →
      1 ≤ (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true).card ∧
      (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true).card ≤ 2) :
    ∀ v ∈ redVertices φ, v ∉ D →
      1 ≤ (by classical exact (D.filter ((reductionGraph φ).toSimpleGraph.Adj v)).card) ∧
      (by classical exact (D.filter ((reductionGraph φ).toSimpleGraph.Adj v)).card) ≤ 2 := by
  classical
  intro v hv hvD
  have hfilt : (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true) =
      D.filter ((reductionGraph φ).toSimpleGraph.Adj v) :=
    Finset.filter_congr fun u _ ↦ Graph.adjBool_eq_true_iff _ _ _
  rw [← hfilt]; exact hD_dom' v hv hvD

private theorem allFalse_forces_a1 {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct)
    {D : Finset ℕ} (hD_sub : ∀ v ∈ D, v ∈ redVertices φ)
    (hD_dom' : ∀ v ∈ redVertices φ, v ∉ D →
      1 ≤ (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true).card ∧
      (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true).card ≤ 2)
    {j : ℕ} (hj : j < φ.length)
    (hc1 : 34 * j + 21 ∈ D) (hc2 : 34 * j + 30 ∈ D)
    (hf0 : 34 * j + 5 ∈ D) (hf1 : 34 * j + 11 ∈ D) (hf2 : 34 * j + 17 ∈ D)
    {g1 g2 : Fin 34}
    (hg1 : g1 ∈ ([1, 2, 7, 8, 13, 14, 22, 23, 24, 25, 26, 27, 28, 29] : List (Fin 34)))
    (hg2 : g2 ∈ ([1, 2, 7, 8, 13, 14, 22, 23, 24, 25, 26, 27, 28, 29] : List (Fin 34)))
    (hv12 : 34 * j + g1.1 ≠ 34 * j + g2.1)
    (hv1D : 34 * j + g1.1 ∈ D) (hv2D : 34 * j + g2.1 ∈ D)
    (hD_clause_mem : ∀ v : Fin 34, 34 * j + v.1 ∈ D →
      v ∈ ([5, 11, 17, 21, 30, g1, g2] : List (Fin 34)))
    (he_not_D : ∀ idx < 3 * φ.length, (nextOcc φ idx).isSome → ∀ b < 2,
      34 * φ.length + 5 * (2 * idx + b) + 0 ∉ D) :
    34 * j + 7 ∈ D ∨ 34 * j + 8 ∈ D := by
  classical
  have hD_dom := dom_adj_of_adjBool hD_dom'
  let m := φ.length
  let G := (reductionGraph φ).toSimpleGraph
  have hclause_ok : ∀ v : Fin 34, v ∉ ([5, 11, 17, 21, 30, g1, g2] : List (Fin 34)) →
      let c := (([5, 11, 17, 21, 30, g1, g2] : List (Fin 34)).filter (clauseAdj v)).length
      1 ≤ c ∧ c ≤ 2 := by
    intro v hv_not
    have hv_not_D : 34 * j + v.1 ∉ D := fun hmem ↦ hv_not (hD_clause_mem v hmem)
    have hdom_v := hD_dom (34 * j + v.1) (mem_redVertices_iff.mpr (Or.inl (by omega))) hv_not_D
    have hcard_eq : (D.filter (G.Adj (34 * j + v.1))).card =
        (([5, 11, 17, 21, 30, g1, g2] : List (Fin 34)).filter (clauseAdj v)).length := by
      have hnodup7 : ([5, 11, 17, 21, 30, g1, g2] : List (Fin 34)).Nodup := by
        have hnd5 : ∀ a ∈ ([1, 2, 7, 8, 13, 14, 22, 23, 24, 25, 26, 27, 28, 29] : List (Fin 34)),
            a.1 ≠ 5 ∧ a.1 ≠ 11 ∧ a.1 ≠ 17 ∧ a.1 ≠ 21 ∧ a.1 ≠ 30 := by decide
        have ha1 := hnd5 g1 hg1
        have ha2 := hnd5 g2 hg2
        have hg12 : g1 ≠ g2 := fun h ↦ hv12 (by rw [h])
        simp [List.nodup_cons, Fin.ext_iff, hg12]; omega
      rw [← List.toFinset_card_of_nodup (hnodup7.filter _)]
      refine Finset.card_bij (fun (u : ℕ) _ ↦ (⟨u % 34, Nat.mod_lt _ (by decide)⟩ : Fin 34))
        (fun u hu ↦ ?_) (fun u1 hu1 u2 hu2 heq ↦ ?_) (fun g hh ↦ ?_)
      · simp only [Finset.mem_filter] at hu
        rcases mem_redVertices_iff.mp (hD_sub u hu.1) with hu_cl | ⟨iu, hiu, hnu, bu, hbu, qu,
          hqu, rfl⟩
        · have hadj := (adj_clause_clause hj (by omega : u / 34 < m) v
            ⟨u % 34, Nat.mod_lt _ (by decide)⟩ (by
            have := G.ne_of_adj hu.2; dsimp; omega)).mp (by convert hu.2; dsimp; omega)
          rw [List.mem_toFinset, List.mem_filter]
          refine ⟨?_, hadj.2⟩
          have hu_eq : u = 34 * j + (⟨u % 34, Nat.mod_lt _ (by decide)⟩ : Fin 34).1 := by
            dsimp; omega
          exact hD_clause_mem ⟨u % 34, Nat.mod_lt _ (by decide)⟩ (hu_eq ▸ hu.1)
        · exfalso
          rcases (show qu = 0 ∨ 1 ≤ qu by omega) with rfl | hqu1
          · exact he_not_D iu hiu hnu bu hbu hu.1
          · exact not_adj_clause_claw hφ (by omega) hiu hnu hbu hqu1 hqu hu.2
      · simp only [Finset.mem_filter] at hu1 hu2
        have hj_of : ∀ u, u ∈ D → G.Adj (34 * j + v.1) u → u / 34 = j := fun u huD hadj ↦ by
          rcases mem_redVertices_iff.mp (hD_sub u huD) with hu_cl | ⟨iu, hiu, hnu, bu, hbu, qu,
            hqu, rfl⟩
          · exact ((adj_clause_clause hj (by omega) v ⟨u % 34, Nat.mod_lt _ (by decide)⟩
              (by have := G.ne_of_adj hadj; dsimp; omega)).mp
              (by convert hadj; dsimp; omega)).1.symm
          · exfalso; rcases (show qu = 0 ∨ 1 ≤ qu by omega) with rfl | hqu1
            · exact he_not_D iu hiu hnu bu hbu huD
            · exact not_adj_clause_claw hφ (by omega) hiu hnu hbu hqu1 hqu hadj
        have h1 := hj_of u1 hu1.1 hu1.2; have h2 := hj_of u2 hu2.1 hu2.2
        have hm := congrArg Fin.val heq; dsimp at hm; omega
      · rw [List.mem_toFinset, List.mem_filter] at hh
        have hgD : 34 * j + g.1 ∈ D := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          rcases hh.1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hf0
          · exact hf1
          · exact hf2
          · exact hc1
          · exact hc2
          · exact hv1D
          · exact hv2D
        have hvg : v ≠ g := fun h ↦ by
          rw [h] at hh
          exact chordsAlternate_irrefl _ _ ((chordsAlternateBool_eq_true_iff _ _ _ _).mp hh.2)
        refine ⟨34 * j + g.1, Finset.mem_filter.mpr ⟨hgD,
          (adj_clause_clause hj hj v g (by have := Fin.val_ne_of_ne hvg; omega)).mpr
            ⟨rfl, hh.2⟩⟩, Fin.ext (by dsimp; omega)⟩
    rw [← hcard_eq]; exact hdom_v
  have hres := clause_all_false_forces_a1 g1 hg1 g2 hg2 hclause_ok
  rcases hres with rfl | rfl | rfl | rfl
  · exact Or.inl hv1D
  · exact Or.inr hv1D
  · exact Or.inl hv2D
  · exact Or.inr hv2D

/-- If `φ` is a satisfiable exact-three distinct-variable formula, then `reductionGraph φ`
admits a `[1, 2]`-dominating set of size `reductionBound φ = 7m + 2t`. -/
theorem sat_imp_dom {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) (hsat : φ.Satisfiable) :
    ∃ D : Finset ℕ, (∀ v ∈ D, v ∈ redVertices φ) ∧
      (∀ v ∈ redVertices φ, v ∉ D →
        1 ≤ (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true).card ∧
        (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true).card ≤ 2) ∧
      D.card = reductionBound φ := by
  classical
  obtain ⟨σ, hσ⟩ := hsat
  let m := φ.length
  let evalIdx (idx : ℕ) : Bool := Literal.eval σ (literalAt φ idx)
  let Dclause : Finset ℕ :=
    (Finset.range m).biUnion fun j ↦
      (clauseDomList (evalIdx (3 * j)) (evalIdx (3 * j + 1)) (evalIdx (3 * j + 2))).toFinset.image
        fun g : Fin 34 ↦ 34 * j + g.1
  let activeIdx : Finset ℕ := (Finset.range (3 * m)).filter fun idx ↦ (nextOcc φ idx).isSome
  let Dconn : Finset ℕ :=
    activeIdx.biUnion fun idx ↦
      {34 * m + 5 * (2 * idx + 0) + 1, 34 * m + 5 * (2 * idx + 1) + 1}
  let D := Dclause ∪ Dconn
  have hcl_sat : ∀ j < m, evalIdx (3 * j) = true ∨ evalIdx (3 * j + 1) = true ∨
    evalIdx (3 * j + 2) = true := by
    intro j hj
    have hc := (CNF.eval_eq_true_iff σ φ).mp hσ (φ[j]) (List.getElem_mem hj)
    have hlen := (hφ (φ[j]) (List.getElem_mem hj)).1
    have hval := (Clause.eval_eq_true_iff σ (φ[j])).mp hc
    obtain ⟨l, hl, hlv⟩ := hval
    obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hl
    have hr3 : r < 3 := by omega
    have hlit : literalAt φ (3 * j + r) = (φ[j])[r] :=
      literalAt_getElem φ hj hr3 hr
    have hev : evalIdx (3 * j + r) = true := by simp [evalIdx, hlit, hlv]
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
    · exact Or.inl hev
    · exact Or.inr (Or.inl hev)
    · exact Or.inr (Or.inr hev)
  have hD_sub : ∀ v ∈ D, v ∈ redVertices φ := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv1 | hv2
    · obtain ⟨j, hj, hg⟩ := Finset.mem_biUnion.mp hv1
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hg
      simp only [Finset.mem_range] at hj
      exact mem_redVertices_iff.mpr (Or.inl (by omega))
    · obtain ⟨idx, hidx, hmem⟩ := Finset.mem_biUnion.mp hv2
      simp only [activeIdx, Finset.mem_filter, Finset.mem_range] at hidx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact mem_redVertices_iff.mpr (Or.inr ⟨idx, hidx.1, hidx.2, 0, by decide, 1, by decide,
        rfl⟩)
      · exact mem_redVertices_iff.mpr (Or.inr ⟨idx, hidx.1, hidx.2, 1, by decide, 1, by decide,
        rfl⟩)
  have hD_card : D.card = reductionBound φ := by
    have hdisj : Disjoint Dclause Dconn := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      obtain ⟨j, hj, hg⟩ := Finset.mem_biUnion.mp hx1
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨idx, _, hmem⟩ := Finset.mem_biUnion.mp hx2
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h <;> omega
    have hc1 : Dclause.card = 7 * m := by
      rw [Finset.card_biUnion]
      · trans ∑ _ ∈ Finset.range m, 7
        · refine Finset.sum_congr rfl fun j hj ↦ ?_
          simp only [Finset.mem_range] at hj
          rw [Finset.card_image_of_injective _ (fun a b h ↦ Fin.ext (by omega))]
          have hval := clauseDomList_valid _ _ _ (hcl_sat j hj)
          rw [List.toFinset_card_of_nodup hval.1, hval.2.1]
        · simp [mul_comm]
      · intro j1 _ j2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]; intro x hx1 hx2
        obtain ⟨g1, _, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨g2, _, h⟩ := Finset.mem_image.mp hx2; omega
    have hc2 : Dconn.card = 2 * repetitionCount φ := by
      rw [Finset.card_biUnion]
      · trans ∑ _ ∈ activeIdx, 2
        · refine Finset.sum_congr rfl fun idx _ ↦ Finset.card_pair (by omega)
        · simp only [Finset.sum_const, smul_eq_mul, mul_comm 2]
          exact congrArg (· * 2) (repetitionCount_eq_card_filter φ).symm
      · intro i1 _ i2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
        rcases hx1 with rfl | rfl <;> rcases hx2 with h | h <;> omega
    rw [Finset.card_union_of_disjoint hdisj, hc1, hc2]; rfl
  -- Verify `[1, 2]`-domination for every `v ∈ redVertices φ \ D`.
  have hD_dom : ∀ v ∈ redVertices φ, v ∉ D →
      1 ≤ (D.filter ((reductionGraph φ).toSimpleGraph.Adj v)).card ∧
      (D.filter ((reductionGraph φ).toSimpleGraph.Adj v)).card ≤ 2 := by
    intro v hv hvD
    rcases mem_redVertices_iff.mp hv with hv_cl | ⟨idx, hidx, hnext, b, hb, q, hq, rfl⟩
    · -- Case 1: `v = 34 * j + g` (clause vertex)
      let j := v / 34
      let g : Fin 34 := ⟨v % 34, Nat.mod_lt _ (by decide)⟩
      have hv_eq : v = 34 * j + g.1 := by dsimp [j, g]; omega
      have hj : j < m := by omega
      have hval := clauseDomList_valid _ _ _ (hcl_sat j hj)
      have hg_not : g ∉ clauseDomList (evalIdx (3 * j)) (evalIdx (3 * j + 1)) (evalIdx (3 * j +
        2)) := by
        intro hmem; apply hvD; refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,
          Finset.mem_range.mpr hj, ?_⟩)
        exact Finset.mem_image.mpr ⟨g, List.mem_toFinset.mpr hmem, hv_eq.symm⟩
      have hfilt_eq : (D.filter ((reductionGraph φ).toSimpleGraph.Adj v)).card =
          ((clauseDomList (evalIdx (3 * j)) (evalIdx (3 * j + 1)) (evalIdx (3 * j + 2))).filter
            (clauseAdj g)).length := by
        rw [← List.toFinset_card_of_nodup (hval.1.filter _)]
        refine Finset.card_bij (fun (u : ℕ) _ ↦ (⟨u % 34, Nat.mod_lt _ (by decide)⟩ : Fin 34))
          (fun u hu ↦ ?_) (fun u1 hu1 u2 hu2 heq ↦ ?_) (fun h hh ↦ ?_)
        · simp only [Finset.mem_filter] at hu
          have hu_ne : u ≠ v := ((reductionGraph φ).toSimpleGraph.ne_of_adj hu.2).symm
          rcases Finset.mem_union.mp hu.1 with hu_cl | hu_conn
          · obtain ⟨ju, hju, hgu⟩ := Finset.mem_biUnion.mp hu_cl
            obtain ⟨gu, hgu_mem, rfl⟩ := Finset.mem_image.mp hgu
            simp only [Finset.mem_range] at hju
            have hadj := (adj_clause_clause hj hju g gu (by omega)).mp
              (hv_eq ▸ hu.2)
            rw [List.mem_toFinset, List.mem_filter]
            have hgu_eq : (⟨(34 * ju + gu.1) % 34, Nat.mod_lt _ (by decide)⟩ : Fin 34) = gu :=
              Fin.ext (by dsimp; omega)
            rw [hgu_eq]; rw [← hadj.1] at hgu_mem
            exact ⟨List.mem_toFinset.mp hgu_mem, hadj.2⟩
          · exfalso
            obtain ⟨iu, hiu, hmem⟩ := Finset.mem_biUnion.mp hu_conn
            simp only [activeIdx, Finset.mem_filter, Finset.mem_range] at hiu
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl <;>
              exact not_adj_clause_claw hφ hv_cl hiu.1 hiu.2 (by decide) (by decide) (by decide)
                hu.2
        · simp only [Finset.mem_filter] at hu1 hu2
          have hj1 : u1 / 34 = j := by
            rcases Finset.mem_union.mp hu1.1 with hu_cl | hu_conn
            · obtain ⟨ju, hju, hgu⟩ := Finset.mem_biUnion.mp hu_cl
              obtain ⟨gu, _, rfl⟩ := Finset.mem_image.mp hgu
              simp only [Finset.mem_range] at hju
              have := ((adj_clause_clause hj hju g gu (by
                have := (reductionGraph φ).toSimpleGraph.ne_of_adj hu1.2
                omega)).mp (hv_eq ▸ hu1.2)).1
              omega
            · exfalso
              obtain ⟨iu, hiu, hmem⟩ := Finset.mem_biUnion.mp hu_conn
              simp only [activeIdx, Finset.mem_filter, Finset.mem_range] at hiu
              simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
              rcases hmem with rfl | rfl <;>
                exact not_adj_clause_claw hφ hv_cl hiu.1 hiu.2 (by decide) (by decide) (by decide)
                  hu1.2
          have hj2 : u2 / 34 = j := by
            rcases Finset.mem_union.mp hu2.1 with hu_cl | hu_conn
            · obtain ⟨ju, hju, hgu⟩ := Finset.mem_biUnion.mp hu_cl
              obtain ⟨gu, _, rfl⟩ := Finset.mem_image.mp hgu
              simp only [Finset.mem_range] at hju
              have := ((adj_clause_clause hj hju g gu (by
                have := (reductionGraph φ).toSimpleGraph.ne_of_adj hu2.2
                omega)).mp (hv_eq ▸ hu2.2)).1
              omega
            · exfalso
              obtain ⟨iu, hiu, hmem⟩ := Finset.mem_biUnion.mp hu_conn
              simp only [activeIdx, Finset.mem_filter, Finset.mem_range] at hiu
              simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
              rcases hmem with rfl | rfl <;>
                exact not_adj_clause_claw hφ hv_cl hiu.1 hiu.2 (by decide) (by decide) (by decide)
                  hu2.2
          have hm_eq := congrArg Fin.val heq; dsimp at hm_eq; omega
        · rw [List.mem_toFinset, List.mem_filter] at hh
          refine ⟨34 * j + h.1, Finset.mem_filter.mpr ⟨Finset.mem_union_left _
            (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
              Finset.mem_image.mpr ⟨h, List.mem_toFinset.mpr hh.1, rfl⟩⟩), ?_⟩,
                Fin.ext (by dsimp; omega)⟩
          have hne_gh : g ≠ h := fun heq ↦ by
            have := hh.2; rw [← heq] at this
            exact chordsAlternate_irrefl _ _
              ((chordsAlternateBool_eq_true_iff _ _ _ _).mp this)
          rw [hv_eq]
          exact (adj_clause_clause hj hj g h (by
          have := Fin.val_ne_of_ne hne_gh; omega)).mpr ⟨rfl, hh.2⟩
      rw [hfilt_eq]; exact hval.2.2 g hg_not
    · -- Case 2: connection block vertex `(idx, b, q)`
      rcases (show q = 0 ∨ q = 1 ∨ (2 ≤ q ∧ q < 5) by omega) with rfl | rfl | ⟨hq2, hq5⟩
      · -- `q = 0` (`e`): neighbors in `D` are `s_e` + EXACTLY ONE of its two `{t, f}` endpoints!
        obtain ⟨idx', hnext_eq⟩ := Option.isSome_iff_exists.mp hnext
        obtain ⟨_, hidx', hvar_eq, hcl_lt, _⟩ := nextOcc_spec hφ hnext_eq
        let isTrue := decide (b = 0)
        let isTrue' := if decide ((literalAt φ idx).2 =
          (literalAt φ idx').2) then !isTrue else isTrue
        let e := 34 * m + 5 * (2 * idx + b) + 0
        let se := 34 * m + 5 * (2 * idx + b) + 1
        let ep1 := 34 * (idx / 3) + (6 * (idx % 3) + (if isTrue then 0 else 5))
        let ep2 := 34 * (idx' / 3) + (6 * (idx' % 3) + (if isTrue' then 0 else 5))
        have hse_in : se ∈ D.filter ((reductionGraph φ).toSimpleGraph.Adj e) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hidx, hnext⟩,
              ?_⟩), ?_⟩
          · rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp [se]
          · exact (claw_adj_iff hφ hidx hnext hb (by decide) (by decide) hv).mpr (by simp)
        -- Determine which of `ep1, ep2` is in `D`:
        have hlit_mem : ∀ k < 3 * m, ∀ fl : Bool,
            34 * (k / 3) + (6 * (k % 3) + (if fl then 0 else 5)) ∈ D ↔ evalIdx k = fl := by
          intro k hk fl
          have hjk : k / 3 < m := by omega
          have hrk : k % 3 < 3 := Nat.mod_lt _ (by decide)
          have htarget_lt : 6 * (k % 3) + (if fl then 0 else 5) < 34 := by
            cases fl <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
          constructor
          · intro hmem
            rcases Finset.mem_union.mp hmem with h1 | h2
            · obtain ⟨j, hj, hg⟩ := Finset.mem_biUnion.mp h1
              obtain ⟨g, hg_mem, hgeq⟩ := Finset.mem_image.mp hg
              simp only [Finset.mem_range] at hj
              have hjeq : j = k / 3 := by omega
              have hgeq' : g.1 = 6 * (k % 3) + (if fl then 0 else 5) := by omega
              subst hjeq
              have hmem' := List.mem_toFinset.mp hg_mem
              have h3 : 3 * (k / 3) + 0 = 3 * (k / 3) := by omega
              have hg_fin : g = ⟨6 * (k % 3) + (if fl then 0 else 5), htarget_lt⟩ := Fin.ext hgeq'
              rw [hg_fin] at hmem'
              have hres := (clauseDomList_tf_mem (evalIdx (3 * (k / 3))) (evalIdx (3 * (k / 3) + 1))
                (evalIdx (3 * (k / 3) + 2)) ⟨k % 3, hrk⟩ fl).mp hmem'
              rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with hr | hr | hr <;>
                simp [hr] at hres
              · simpa [show 3 * (k / 3) = k by omega] using hres
              · simpa [show 3 * (k / 3) + 1 = k by omega] using hres
              · simpa [show 3 * (k / 3) + 2 = k by omega] using hres
            · exfalso
              obtain ⟨i', _, hmem'⟩ := Finset.mem_biUnion.mp h2
              simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
              rcases hmem' with h | h <;> omega
          · intro hev
            refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k / 3, Finset.mem_range.mpr hjk,
              ?_⟩)
            refine Finset.mem_image.mpr ⟨⟨6 * (k % 3) + (if fl then 0 else 5), htarget_lt⟩,
              List.mem_toFinset.mpr ?_, rfl⟩
            rw [clauseDomList_tf_mem _ _ _ ⟨k % 3, hrk⟩ fl]
            rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with hr | hr | hr <;>
              simp [hr]
            · simpa [show 3 * (k / 3) = k by omega] using hev
            · simpa [show 3 * (k / 3) + 1 = k by omega] using hev
            · simpa [show 3 * (k / 3) + 2 = k by omega] using hev
        -- Exactly one of `ep1, ep2` is in `D` because `evalIdx idx' = (samePol ? evalIdx idx :
        -- !evalIdx idx)`!
        have hexor : (evalIdx idx = isTrue ∧ evalIdx idx' ≠ isTrue') ∨
            (evalIdx idx ≠ isTrue ∧ evalIdx idx' = isTrue') := by
          simp only [evalIdx, Literal.eval, isTrue', hvar_eq]
          cases h1 : σ (literalAt φ idx).1 <;> cases h2 : (literalAt φ idx).2 <;>
            cases h3 : (literalAt φ idx').2 <;> cases isTrue <;> decide
        -- Every neighbor of `e` in `D` is in `{se, ep1, ep2}` (no `a` chords in `D`, no other `s_e`
        -- crosses `e`).
        have hsub : D.filter ((reductionGraph φ).toSimpleGraph.Adj e) ⊆
            (if evalIdx idx = isTrue then {se, ep1} else {se, ep2}) := by
          intro u hu
          simp only [Finset.mem_filter] at hu
          rcases Finset.mem_union.mp hu.1 with hu_cl | hu_conn
          · obtain ⟨j, hj, hg⟩ := Finset.mem_biUnion.mp hu_cl
            obtain ⟨g, hg_mem, rfl⟩ := Finset.mem_image.mp hg
            simp only [Finset.mem_range] at hj
            have hcr := (adj_conn_clause_iff hφ hidx hnext_eq hb hj g).mp hu.2
            have hno_a : ∀ s : Fin 3, g.1 ≠ 6 * s.1 + 1 ∧ g.1 ≠ 6 * s.1 + 2 := by
              intro s
              have hna0 := clauseDomList_no_a (evalIdx (3 * j)) (evalIdx (3 * j + 1))
                (evalIdx (3 * j + 2)) s 0
              have hna1 := clauseDomList_no_a (evalIdx (3 * j)) (evalIdx (3 * j + 1))
                (evalIdx (3 * j + 2)) s 1
              have hgm := List.mem_toFinset.mp hg_mem
              exact ⟨fun h ↦ hna0 (by rwa [show (⟨6 * s.1 + 1 + (0 : Fin 2).1, by omega⟩ : Fin 34)
                  = g from Fin.ext (by dsimp; omega)]),
                fun h ↦ hna1 (by rwa [show (⟨6 * s.1 + 1 + (1 : Fin 2).1, by omega⟩ : Fin 34)
                  = g from Fin.ext (by dsimp; omega)])⟩
            rcases hcr with ⟨rfl, h1 | ⟨s, _, h2 | h2⟩⟩ | ⟨rfl, h1 | ⟨s, _, h2 | h2⟩⟩
            · have he1 : 34 * (idx / 3) + g.1 = ep1 := by dsimp [ep1]; rw [h1]
              rw [he1] at hu ⊢
              have hev1 : evalIdx idx = isTrue := (hlit_mem idx hidx isTrue).mp hu.1
              simp [hev1]
            · exact absurd h2 (hno_a s).1
            · exact absurd h2 (hno_a s).2
            · have he2 : 34 * (idx' / 3) + g.1 = ep2 := by dsimp [ep2]; rw [h1]
              rw [he2] at hu ⊢
              have hev2 : evalIdx idx' = isTrue' := (hlit_mem idx' hidx' isTrue').mp hu.1
              rcases hexor with ⟨_, h2'⟩ | ⟨h1', _⟩
              · exact absurd hev2 h2'
              · simp [h1']
            · exact absurd h2 (hno_a s).1
            · exact absurd h2 (hno_a s).2
          · obtain ⟨iu, hiu, hmem⟩ := Finset.mem_biUnion.mp hu_conn
            simp only [activeIdx, Finset.mem_filter, Finset.mem_range] at hiu
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl
            · have hclaw :=
                (claw_adj_iff hφ hiu.1 hiu.2 (by decide) (by decide) (by decide) hv).mp hu.2
              simp only [↓reduceIte] at hclaw
              rcases hclaw with h | h | h | h
              · have : iu = idx ∧ 0 = b := by omega
                have hse_eq : 34 * m + 5 * (2 * iu + 0) + 1 = se := by dsimp [se]; omega
                rw [hse_eq]; split_ifs <;> simp
              all_goals omega
            · have hclaw :=
                (claw_adj_iff hφ hiu.1 hiu.2 (by decide) (by decide) (by decide) hv).mp hu.2
              simp only [↓reduceIte] at hclaw
              rcases hclaw with h | h | h | h
              · have : iu = idx ∧ 1 = b := by omega
                have hse_eq : 34 * m + 5 * (2 * iu + 1) + 1 = se := by dsimp [se]; omega
                rw [hse_eq]; split_ifs <;> simp
              all_goals omega
        -- And the chosen pair is a subset of `D.filter (Adj e)`, giving exact count `2`!
        have hsup : (if evalIdx idx = isTrue then ({se, ep1} : Finset ℕ) else {se, ep2}) ⊆
            D.filter ((reductionGraph φ).toSimpleGraph.Adj e) := by
          split_ifs with hev1
          · intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl
            · exact hse_in
            · refine Finset.mem_filter.mpr ⟨(hlit_mem idx hidx isTrue).mpr hev1, ?_⟩
              exact (adj_conn_clause_iff hφ hidx hnext_eq hb (by omega)
                ⟨6 * (idx % 3) + (if isTrue then 0 else 5), by
                  cases isTrue <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩).mpr
                (Or.inl ⟨rfl, Or.inl rfl⟩)
          · have hev2 : evalIdx idx' = isTrue' := by
              rcases hexor with ⟨h, _⟩ | ⟨_, h⟩
              · exact absurd h hev1
              · exact h
            intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl
            · exact hse_in
            · refine Finset.mem_filter.mpr ⟨(hlit_mem idx' hidx' isTrue').mpr hev2, ?_⟩
              exact (adj_conn_clause_iff hφ hidx hnext_eq hb (by omega)
                ⟨6 * (idx' % 3) + (if isTrue' then 0 else 5), by
                  cases isTrue' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩).mpr
                (Or.inr ⟨rfl, Or.inl rfl⟩)
        have heq_f : D.filter ((reductionGraph φ).toSimpleGraph.Adj e) =
            if evalIdx idx = isTrue then {se, ep1} else {se, ep2} :=
              Finset.Subset.antisymm hsub hsup
        rw [heq_f]
        split_ifs
        · rw [Finset.card_pair (by
            dsimp [se, ep1]; cases isTrue <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)]
          exact ⟨by decide, le_rfl⟩
        · rw [Finset.card_pair (by
            dsimp [se, ep2]
            cases isTrue' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)]
          exact ⟨by decide, le_rfl⟩
      · -- `q = 1`: `s_e ∈ D`, contradiction with `v ∉ D`!
        exfalso; apply hvD; refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hidx, hnext⟩, ?_⟩)
        rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp [m]
      · -- `q ∈ {2, 3, 4}`: sole neighbor in `D` is `s_e`
        have hq1 : q ≠ 1 := by omega
        have hfilt_eq : D.filter ((reductionGraph φ).toSimpleGraph.Adj
            (34 * m + 5 * (2 * idx + b) + q)) = {34 * m + 5 * (2 * idx + b) + 1} := by
          ext u; simp only [Finset.mem_filter, Finset.mem_singleton]
          refine ⟨fun ⟨huD, hadj⟩ ↦ ?_,
            fun h ↦ h ▸ ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr
              ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hidx, hnext⟩,
               by rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp [m]⟩), ?_⟩⟩
          · have hEq := (claw_adj_iff hφ hidx hnext hb (by omega : 1 ≤ q) hq5
              (hD_sub u huD)).mp hadj.symm
            simpa [hq1, m] using hEq
          · have hmem1 : 34 * m + 5 * (2 * idx + b) + 1 ∈ redVertices φ :=
              mem_redVertices_iff.mpr (Or.inr ⟨idx, hidx, hnext, b, hb, 1, by decide, rfl⟩)
            exact ((claw_adj_iff hφ hidx hnext hb (by omega : 1 ≤ q) hq5 hmem1).mpr
              (by simp [hq1, m])).symm
        rw [hfilt_eq, Finset.card_singleton]; exact ⟨le_rfl, by decide⟩
  refine ⟨D, hD_sub, fun v hv hvD ↦ ?_, hD_card⟩
  have hfilt : (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true) =
      D.filter ((reductionGraph φ).toSimpleGraph.Adj v) :=
    Finset.filter_congr fun u _ ↦ Graph.adjBool_eq_true_iff _ _ _
  rw [hfilt]; exact hD_dom v hv hvD

private theorem claw_centers_mem {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct)
    {D : Finset ℕ} (hD_sub : ∀ v ∈ D, v ∈ redVertices φ)
    (hD_dom' : ∀ v ∈ redVertices φ, v ∉ D →
      1 ≤ (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true).card ∧
      (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true).card ≤ 2) :
    (∀ j < φ.length, 34 * j + 21 ∈ D) ∧
    (∀ j < φ.length, 34 * j + 30 ∈ D) ∧
    (∀ idx < 3 * φ.length, (nextOcc φ idx).isSome → ∀ b < 2,
      34 * φ.length + 5 * (2 * idx + b) + 1 ∈ D) := by
  classical
  have hD_dom := dom_adj_of_adjBool hD_dom'
  let m := φ.length
  let G := (reductionGraph φ).toSimpleGraph
  have hc1_mem : ∀ j < m, 34 * j + 21 ∈ D := by
    intro j hj
    by_contra hnot
    have hleaf_in : ∀ l ∈ ([18, 19, 20] : List (Fin 34)), 34 * j + l.1 ∈ D := by
      intro l hl
      by_contra hlnot
      have hlv : 34 * j + l.1 ∈ redVertices φ := mem_redVertices_iff.mpr (Or.inl (by omega))
      obtain ⟨u, hu⟩ :=
        Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hD_dom _ hlv hlnot).1)
      simp only [Finset.mem_filter] at hu
      rcases mem_redVertices_iff.mp (hD_sub u hu.1) with hu_cl | ⟨iu, hiu, hnu, bu, hbu, qu, hqu,
        rfl⟩
      · have := (adj_clause_clause hj (by omega : u / 34 < m) l ⟨u % 34, Nat.mod_lt _ (by decide)⟩
          (by have := G.ne_of_adj hu.2; dsimp; omega)).mp (by convert hu.2; dsimp; omega)
        have hl21 := (clause_c_leaves_only.1 l hl _).mp this.2
        have : u = 34 * j + 21 := by have := congrArg Fin.val hl21; dsimp at this; omega
        exact hnot (this ▸ hu.1)
      · rcases (show qu = 0 ∨ 1 ≤ qu by omega) with rfl | hqu1
        · obtain ⟨iu', hnu_eq⟩ := Option.isSome_iff_exists.mp hnu
          have hcr := (adj_conn_clause_iff hφ hiu hnu_eq hbu hj l).mp hu.2.symm
          have hbad : ∀ l' ∈ ([18, 19, 20] : List (Fin 34)), ∀ r : Fin 3, ∀ fl : Bool,
              l'.1 ≠ 6 * r.1 + (if fl then 0 else 5) ∧ l'.1 ≠ 6 * r.1 + 1 ∧
              l'.1 ≠ 6 * r.1 + 2 := by decide
          rcases hcr with ⟨_, h1 | ⟨s, _, h2 | h2⟩⟩ | ⟨_, h1 | ⟨s, _, h2 | h2⟩⟩
          · exact (hbad l hl ⟨iu % 3, Nat.mod_lt _ (by decide)⟩ _).1 h1
          · exact (hbad l hl s false).2.1 h2
          · exact (hbad l hl s false).2.2 h2
          · exact (hbad l hl ⟨iu' % 3, Nat.mod_lt _ (by decide)⟩ _).1 h1
          · exact (hbad l hl s false).2.1 h2
          · exact (hbad l hl s false).2.2 h2
        · exact not_adj_clause_claw hφ (by omega) hiu hnu hbu hqu1 hqu hu.2
    have h3 : ({34 * j + 18, 34 * j + 19, 34 * j + 20} : Finset ℕ) ⊆ D.filter (G.Adj (34 * j +
      21)) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · exact ⟨hleaf_in 18 (by simp), (adj_clause_clause hj hj 21 18 (by omega)).mpr ⟨rfl,
        by decide⟩⟩
      · exact ⟨hleaf_in 19 (by simp), (adj_clause_clause hj hj 21 19 (by omega)).mpr ⟨rfl,
        by decide⟩⟩
      · exact ⟨hleaf_in 20 (by simp), (adj_clause_clause hj hj 21 20 (by omega)).mpr ⟨rfl,
        by decide⟩⟩
    have hc3 : ({34 * j + 18, 34 * j + 19, 34 * j + 20} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by omega)]
    have := (Finset.card_le_card h3).trans
      (hD_dom _ (mem_redVertices_iff.mpr (Or.inl (by omega))) hnot).2
    omega
  have hc2_mem : ∀ j < m, 34 * j + 30 ∈ D := by
    intro j hj
    by_contra hnot
    have hleaf_in : ∀ l ∈ ([31, 32, 33] : List (Fin 34)), 34 * j + l.1 ∈ D := by
      intro l hl
      by_contra hlnot
      have hlv : 34 * j + l.1 ∈ redVertices φ := mem_redVertices_iff.mpr (Or.inl (by omega))
      obtain ⟨u, hu⟩ :=
        Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hD_dom _ hlv hlnot).1)
      simp only [Finset.mem_filter] at hu
      rcases mem_redVertices_iff.mp (hD_sub u hu.1) with hu_cl | ⟨iu, hiu, hnu, bu, hbu, qu, hqu,
        rfl⟩
      · have := (adj_clause_clause hj (by omega : u / 34 < m) l ⟨u % 34, Nat.mod_lt _ (by decide)⟩
          (by have := G.ne_of_adj hu.2; dsimp; omega)).mp (by convert hu.2; dsimp; omega)
        have hl30 := (clause_c_leaves_only.2 l hl _).mp this.2
        have : u = 34 * j + 30 := by have := congrArg Fin.val hl30; dsimp at this; omega
        exact hnot (this ▸ hu.1)
      · rcases (show qu = 0 ∨ 1 ≤ qu by omega) with rfl | hqu1
        · obtain ⟨iu', hnu_eq⟩ := Option.isSome_iff_exists.mp hnu
          have hcr := (adj_conn_clause_iff hφ hiu hnu_eq hbu hj l).mp hu.2.symm
          have hbad : ∀ l' ∈ ([31, 32, 33] : List (Fin 34)), ∀ r : Fin 3, ∀ fl : Bool,
              l'.1 ≠ 6 * r.1 + (if fl then 0 else 5) ∧ l'.1 ≠ 6 * r.1 + 1 ∧
              l'.1 ≠ 6 * r.1 + 2 := by decide
          rcases hcr with ⟨_, h1 | ⟨s, _, h2 | h2⟩⟩ | ⟨_, h1 | ⟨s, _, h2 | h2⟩⟩
          · exact (hbad l hl ⟨iu % 3, Nat.mod_lt _ (by decide)⟩ _).1 h1
          · exact (hbad l hl s false).2.1 h2
          · exact (hbad l hl s false).2.2 h2
          · exact (hbad l hl ⟨iu' % 3, Nat.mod_lt _ (by decide)⟩ _).1 h1
          · exact (hbad l hl s false).2.1 h2
          · exact (hbad l hl s false).2.2 h2
        · exact not_adj_clause_claw hφ (by omega) hiu hnu hbu hqu1 hqu hu.2
    have h3 : ({34 * j + 31, 34 * j + 32, 34 * j + 33} : Finset ℕ) ⊆ D.filter (G.Adj (34 * j +
      30)) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · exact ⟨hleaf_in 31 (by simp), (adj_clause_clause hj hj 30 31 (by omega)).mpr ⟨rfl,
        by decide⟩⟩
      · exact ⟨hleaf_in 32 (by simp), (adj_clause_clause hj hj 30 32 (by omega)).mpr ⟨rfl,
        by decide⟩⟩
      · exact ⟨hleaf_in 33 (by simp), (adj_clause_clause hj hj 30 33 (by omega)).mpr ⟨rfl,
        by decide⟩⟩
    have hc3 : ({34 * j + 31, 34 * j + 32, 34 * j + 33} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by omega)]
    have := (Finset.card_le_card h3).trans
      (hD_dom _ (mem_redVertices_iff.mpr (Or.inl (by omega))) hnot).2
    omega
  have hs_mem : ∀ idx < 3 * m, (nextOcc φ idx).isSome → ∀ b < 2,
      34 * m + 5 * (2 * idx + b) + 1 ∈ D := by
    intro idx hidx hnext b hb
    by_contra hnot
    let se := 34 * m + 5 * (2 * idx + b) + 1
    have hleaf_in : ∀ q, 2 ≤ q → q < 5 → 34 * m + 5 * (2 * idx + b) + q ∈ D := by
      intro q hq2 hq5
      by_contra hqnot
      have hqv : 34 * m + 5 * (2 * idx + b) + q ∈ redVertices φ :=
        mem_redVertices_iff.mpr (Or.inr ⟨idx, hidx, hnext, b, hb, q, hq5, rfl⟩)
      obtain ⟨u, hu⟩ :=
        Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hD_dom _ hqv hqnot).1)
      simp only [Finset.mem_filter] at hu
      have hEq := (claw_adj_iff hφ hidx hnext hb (by omega) hq5 (hD_sub u hu.1)).mp hu.2.symm
      simp only [show ¬ (q = 1) by omega, ↓reduceIte] at hEq
      exact hnot (hEq ▸ hu.1)
    have h3 : ({34 * m + 5 * (2 * idx + b) + 2, 34 * m + 5 * (2 * idx + b) + 3,
        34 * m + 5 * (2 * idx + b) + 4} : Finset ℕ) ⊆ D.filter (G.Adj se) := by
      have hmem1 : 34 * m + 5 * (2 * idx + b) + 1 ∈ redVertices φ :=
        mem_redVertices_iff.mpr (Or.inr ⟨idx, hidx, hnext, b, hb, 1, by decide, rfl⟩)
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · exact ⟨hleaf_in 2 le_rfl (by decide),
          (claw_adj_iff hφ hidx hnext hb (q := 2) (by decide) (by decide) hmem1).mpr
            (by simp [m])⟩
      · exact ⟨hleaf_in 3 (by decide) (by decide),
          (claw_adj_iff hφ hidx hnext hb (q := 3) (by decide) (by decide) hmem1).mpr
            (by simp [m])⟩
      · exact ⟨hleaf_in 4 (by decide) (by decide),
          (claw_adj_iff hφ hidx hnext hb (q := 4) (by decide) (by decide) hmem1).mpr
            (by simp [m])⟩
    have hc3 : ({34 * m + 5 * (2 * idx + b) + 2, 34 * m + 5 * (2 * idx + b) + 3,
        34 * m + 5 * (2 * idx + b) + 4} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by omega)]
    have := (Finset.card_le_card h3).trans
      (hD_dom _ (mem_redVertices_iff.mpr (Or.inr ⟨idx, hidx, hnext, b, hb, 1, by decide,
        rfl⟩)) hnot).2
    omega
  exact ⟨hc1_mem, hc2_mem, hs_mem⟩

/-- If `reductionGraph φ` admits a `[1, 2]`-dominating set of size at most
`reductionBound φ = 7m + 2t`, then `φ` is satisfiable. -/
theorem dom_imp_sat {φ : CNF ℕ} (hφ : φ.IsExactThreeDistinct) {D : Finset ℕ}
    (hD_sub : ∀ v ∈ D, v ∈ redVertices φ)
    (hD_dom' : ∀ v ∈ redVertices φ, v ∉ D →
      1 ≤ (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true).card ∧
      (D.filter fun u ↦ (reductionGraph φ).adjBool v u = true).card ≤ 2)
    (hD_card : D.card ≤ reductionBound φ) :
    φ.Satisfiable := by
  classical
  have hD_dom := dom_adj_of_adjBool hD_dom'
  let m := φ.length
  let G := (reductionGraph φ).toSimpleGraph
  obtain ⟨hc1_mem, hc2_mem, hs_mem⟩ := claw_centers_mem hφ hD_sub hD_dom'
  -- Step 2: Disjoint bucket counting!
  let Blit (j r : ℕ) : Finset ℕ :=
    {34 * j + 6 * r, 34 * j + 6 * r + 3, 34 * j + 6 * r + 4, 34 * j + 6 * r + 5}
  let B5list : List (Fin 34) := [1, 2, 7, 8, 13, 14, 22, 23, 24, 25, 26, 27, 28, 29]
  let B5 (j : ℕ) : Finset ℕ := B5list.toFinset.image fun g : Fin 34 ↦ 34 * j + g.1
  let Bclause (j : ℕ) : Finset ℕ :=
    Blit j 0 ∪ Blit j 1 ∪ Blit j 2 ∪ {34 * j + 21, 34 * j + 30} ∪ B5 j
  let activeIdx : Finset ℕ := (Finset.range (3 * m)).filter fun idx ↦ (nextOcc φ idx).isSome
  let Dconn : Finset ℕ :=
    activeIdx.biUnion fun idx ↦ {34 * m + 5 * (2 * idx + 0) + 1, 34 * m + 5 * (2 * idx + 1) + 1}
  -- Every literal bucket `Blit j r` has `|D ∩ Blit j r| ≥ 1` (to dominate `p_ra`).
  have hBlit_ge : ∀ j < m, ∀ r < 3, 1 ≤ (D ∩ Blit j r).card := by
    intro j hj r hr
    by_cases hpa : 34 * j + 6 * r + 3 ∈ D
    · exact Finset.one_le_card.mpr ⟨_, Finset.mem_inter.mpr ⟨hpa, by simp [Blit]⟩⟩
    · have hpav : 34 * j + 6 * r + 3 ∈ redVertices φ := mem_redVertices_iff.mpr (Or.inl (by omega))
      obtain ⟨u, hu⟩ :=
        Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hD_dom _ hpav hpa).1)
      simp only [Finset.mem_filter] at hu
      rcases mem_redVertices_iff.mp (hD_sub u hu.1) with hu_cl | ⟨iu, hiu, hnu, bu, hbu, qu, hqu,
        rfl⟩
      · have hadj := (adj_clause_clause hj (by omega : u / 34 < m) ⟨6 * r + 3, by omega⟩
          ⟨u % 34, Nat.mod_lt _ (by decide)⟩ (by
          have := G.ne_of_adj hu.2; dsimp; omega)).mp (by convert hu.2; dsimp; omega)
        have hpn := clause_p_neighbors ⟨r, hr⟩ 0 ⟨u % 34, Nat.mod_lt _ (by decide)⟩ hadj.2
        dsimp at hpn
        refine Finset.one_le_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hu.1, ?_⟩⟩
        rcases hpn with h | h <;> simp [Blit] <;> omega
      · exfalso
        rcases (show qu = 0 ∨ 1 ≤ qu by omega) with rfl | hqu1
        · obtain ⟨iu', hnu_eq⟩ := Option.isSome_iff_exists.mp hnu
          have hcr := (adj_conn_clause_iff hφ hiu hnu_eq hbu hj ⟨6 * r + 3, by omega⟩).mp hu.2.symm
          have hbad : ∀ r1 r2 : Fin 3, ∀ fl : Bool,
              6 * r1.1 + 3 ≠ 6 * r2.1 + (if fl then 0 else 5) ∧
              6 * r1.1 + 3 ≠ 6 * r2.1 + 1 ∧ 6 * r1.1 + 3 ≠ 6 * r2.1 + 2 := by decide
          rcases hcr with ⟨_, h1 | ⟨s, _, h2 | h2⟩⟩ | ⟨_, h1 | ⟨s, _, h2 | h2⟩⟩
          · exact (hbad ⟨r, hr⟩ ⟨iu % 3, Nat.mod_lt _ (by decide)⟩ _).1 h1
          · exact (hbad ⟨r, hr⟩ s false).2.1 h2
          · exact (hbad ⟨r, hr⟩ s false).2.2 h2
          · exact (hbad ⟨r, hr⟩ ⟨iu' % 3, Nat.mod_lt _ (by decide)⟩ _).1 h1
          · exact (hbad ⟨r, hr⟩ s false).2.1 h2
          · exact (hbad ⟨r, hr⟩ s false).2.2 h2
        · exact not_adj_clause_claw hφ (by omega) hiu hnu hbu hqu1 hqu hu.2
  -- Every `B5 j` has `|D ∩ B5 j| ≥ 2` (no single vertex dominates all 6 of `u/w`).
  have hB5_ge : ∀ j < m, 2 ≤ (D ∩ B5 j).card := by
    intro j hj
    have hdom_uw : ∀ u ∈ ([23, 24, 25, 26, 27, 28] : List (Fin 34)),
        ∃ w ∈ D ∩ B5 j, w = 34 * j + u.1 ∨ G.Adj (34 * j + u.1) w := by
      intro u hu
      by_cases huD : 34 * j + u.1 ∈ D
      · have huB5 : u ∈ B5list := by
          have : ∀ x ∈ ([23, 24, 25, 26, 27, 28] : List (Fin 34)), x ∈ B5list := by decide
          exact this u hu
        refine ⟨34 * j + u.1, Finset.mem_inter.mpr ⟨huD, Finset.mem_image.mpr
          ⟨u, List.mem_toFinset.mpr huB5, rfl⟩⟩, Or.inl rfl⟩
      · have huv : 34 * j + u.1 ∈ redVertices φ := mem_redVertices_iff.mpr (Or.inl (by omega))
        obtain ⟨w, hw⟩ :=
          Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hD_dom _ huv huD).1)
        simp only [Finset.mem_filter] at hw
        rcases mem_redVertices_iff.mp (hD_sub w hw.1) with hw_cl | ⟨iw, hiw, hnw, bw, hbw, qw, hqw,
          rfl⟩
        · have hadj := (adj_clause_clause hj (by omega : w / 34 < m) u
            ⟨w % 34, Nat.mod_lt _ (by decide)⟩ (by
            have := G.ne_of_adj hw.2; dsimp; omega)).mp (by convert hw.2; dsimp; omega)
          have hinB5 := clause_uw_neighbors_in_B5 u hu _ hadj.2
          refine ⟨w, Finset.mem_inter.mpr ⟨hw.1, Finset.mem_image.mpr
            ⟨⟨w % 34, Nat.mod_lt _ (by decide)⟩, List.mem_toFinset.mpr hinB5, by dsimp; omega⟩⟩,
              Or.inr hw.2⟩
        · exfalso
          rcases (show qw = 0 ∨ 1 ≤ qw by omega) with rfl | hqw1
          · obtain ⟨iw', hnw_eq⟩ := Option.isSome_iff_exists.mp hnw
            have hcr := (adj_conn_clause_iff hφ hiw hnw_eq hbw hj u).mp hw.2.symm
            have hbad : ∀ u' ∈ ([23, 24, 25, 26, 27, 28] : List (Fin 34)), ∀ r : Fin 3, ∀ fl : Bool,
                u'.1 ≠ 6 * r.1 + (if fl then 0 else 5) ∧ u'.1 ≠ 6 * r.1 + 1 ∧
                  u'.1 ≠ 6 * r.1 + 2 := by decide
            rcases hcr with ⟨_, h1 | ⟨s, _, h2 | h2⟩⟩ | ⟨_, h1 | ⟨s, _, h2 | h2⟩⟩
            · exact (hbad u hu ⟨iw % 3, Nat.mod_lt _ (by decide)⟩ _).1 h1
            · exact (hbad u hu s false).2.1 h2
            · exact (hbad u hu s false).2.2 h2
            · exact (hbad u hu ⟨iw' % 3, Nat.mod_lt _ (by decide)⟩ _).1 h1
            · exact (hbad u hu s false).2.1 h2
            · exact (hbad u hu s false).2.2 h2
          · exact not_adj_clause_claw hφ (by omega) hiw hnw hbw hqw1 hqw hw.2
    by_contra hlt2; push Not at hlt2
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : (D ∩ B5 j).card ≤ 1) with h0 | h1
    · obtain ⟨w, hw, _⟩ := hdom_uw 23 (by simp)
      rw [Finset.card_eq_zero.mp h0] at hw; exact Finset.notMem_empty w hw
    · obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp h1
      have hw_mem : w ∈ B5 j := (Finset.mem_inter.mp (hw_eq ▸ Finset.mem_singleton_self w)).2
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hw_mem
      obtain ⟨u, hu, hug, hna⟩ := clause_no_single_dom_uw g
      obtain ⟨w', hw', hdom⟩ := hdom_uw u hu
      rw [hw_eq, Finset.mem_singleton] at hw'; subst hw'
      rcases hdom with heq | hadj
      · exact hug (Fin.ext (by omega))
      · have := ((adj_clause_clause hj hj u g (by have := Fin.val_ne_of_ne hug; omega)).mp hadj).2
        rw [hna] at this; exact Bool.false_ne_true this
  -- Sum over all disjoint buckets to prove exact equality on EVERY bucket and `D ⊆ allBuckets`!
  have hBclause_sum : ∀ j < m, (D ∩ Bclause j).card = (D ∩ Blit j 0).card + (D ∩ Blit j 1).card +
      (D ∩ Blit j 2).card + 2 + (D ∩ B5 j).card := by
    intro j hj
    have hdisj01 : Disjoint (D ∩ Blit j 0) (D ∩ Blit j 1) :=
      Finset.disjoint_left.mpr fun x h1 h2 ↦ by
        have a := (Finset.mem_inter.mp h1).2; have b := (Finset.mem_inter.mp h2).2
        simp only [Blit, Finset.mem_insert, Finset.mem_singleton] at a b
        rcases a with rfl | rfl | rfl | rfl <;> rcases b with h | h | h | h <;> omega
    have hdisj01_2 : Disjoint (D ∩ (Blit j 0 ∪ Blit j 1)) (D ∩ Blit j 2) :=
      Finset.disjoint_left.mpr fun x h1 h2 ↦ by
        have a := (Finset.mem_inter.mp h1).2; have b := (Finset.mem_inter.mp h2).2
        simp only [Blit, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at a b
        rcases a with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
          rcases b with h | h | h | h <;> omega
    have hdisj_c : Disjoint (D ∩ (Blit j 0 ∪ Blit j 1 ∪ Blit j 2)) (D ∩ {34 * j + 21, 34 * j +
      30}) :=
      Finset.disjoint_left.mpr fun x h1 h2 ↦ by
        have a := (Finset.mem_inter.mp h1).2; have b := (Finset.mem_inter.mp h2).2
        simp only [Blit, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at a b
        rcases a with ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) |
          (rfl | rfl | rfl | rfl) <;>
          rcases b with h | h <;> omega
    have hdisj_b5 : Disjoint (D ∩ (Blit j 0 ∪ Blit j 1 ∪ Blit j 2 ∪ {34 * j + 21, 34 * j +
      30})) (D ∩ B5 j) :=
      Finset.disjoint_left.mpr fun x h1 h2 ↦ by
        have a := (Finset.mem_inter.mp h1).2; have b := (Finset.mem_inter.mp h2).2
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp b
        have hgm := List.mem_toFinset.mp hg
        simp only [Blit, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at a
        have : ∀ g' ∈ B5list, g'.1 ≠ 0 ∧ g'.1 ≠ 3 ∧ g'.1 ≠ 4 ∧ g'.1 ≠ 5 ∧
            g'.1 ≠ 6 ∧ g'.1 ≠ 9 ∧ g'.1 ≠ 10 ∧ g'.1 ≠ 11 ∧
            g'.1 ≠ 12 ∧ g'.1 ≠ 15 ∧ g'.1 ≠ 16 ∧ g'.1 ≠ 17 ∧ g'.1 ≠ 21 ∧ g'.1 ≠ 30 := by decide
        have := this g hgm
        rcases a with (((h | h | h | h) | (h | h | h | h)) |
          (h | h | h | h)) | (h | h) <;> omega
    have hc_eq : (D ∩ {34 * j + 21, 34 * j + 30}).card = 2 := by
      have : D ∩ {34 * j + 21, 34 * j + 30} = {34 * j + 21, 34 * j + 30} :=
        Finset.inter_eq_right.mpr (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hc1_mem j hj
          · exact hc2_mem j hj)
      rw [this, Finset.card_pair (by omega)]
    dsimp only [Bclause]
    rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdisj_b5,
      Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdisj_c,
      Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdisj01_2,
      Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdisj01, hc_eq]
  have hBclause_ge : ∀ j < m, 7 ≤ (D ∩ Bclause j).card := by
    intro j hj
    have hsum := hBclause_sum j hj
    have h0 := hBlit_ge j hj 0 (by decide)
    have h1 := hBlit_ge j hj 1 (by decide)
    have h2 := hBlit_ge j hj 2 (by decide)
    have h5 := hB5_ge j hj
    omega
  have hDconn_sub : Dconn ⊆ D := by
    intro x hx
    obtain ⟨idx, hidx, hmem⟩ := Finset.mem_biUnion.mp hx
    simp only [activeIdx, Finset.mem_filter, Finset.mem_range] at hidx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact hs_mem idx hidx.1 hidx.2 0 (by decide)
    · exact hs_mem idx hidx.1 hidx.2 1 (by decide)
  have hDconn_card : Dconn.card = 2 * repetitionCount φ := by
    rw [Finset.card_biUnion]
    · trans ∑ _ ∈ activeIdx, 2
      · exact Finset.sum_congr rfl fun _ _ ↦ Finset.card_pair (by omega)
      · simp only [Finset.sum_const, smul_eq_mul, mul_comm 2]
        exact congrArg (· * 2) (repetitionCount_eq_card_filter φ).symm
    · intro i1 _ i2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      rcases hx1 with rfl | rfl <;> rcases hx2 with h | h <;> omega
  let Ball := ((Finset.range m).biUnion fun j ↦ D ∩ Bclause j) ∪ Dconn
  have hBall_sub : Ball ⊆ D := Finset.union_subset
    (Finset.biUnion_subset.mpr fun _ _ ↦ Finset.inter_subset_left) hDconn_sub
  have hBall_card : Ball.card = (∑ j ∈ Finset.range m, (D ∩ Bclause j).card) + Dconn.card := by
    have hdisj_all : Disjoint ((Finset.range m).biUnion fun j ↦ D ∩ Bclause j) Dconn := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx1
      obtain ⟨idx, _, hmem⟩ := Finset.mem_biUnion.mp hx2
      simp only [Finset.mem_range] at hj
      have hxb := (Finset.mem_inter.mp hxj).2
      have hxlt : x < 34 * m := by
        simp only [Bclause, Blit, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hxb
        rcases hxb with ((((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) |
          (rfl | rfl | rfl | rfl)) | (rfl | rfl)) | h5
        all_goals first | omega | (obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp h5; omega)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl <;> omega
    rw [Finset.card_union_of_disjoint hdisj_all, Finset.card_biUnion]
    intro j1 _ j2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have h1 := (Finset.mem_inter.mp hx1).2; have h2 := (Finset.mem_inter.mp hx2).2
    have hrange_j : ∀ j y, y ∈ Bclause j → y / 34 = j := by
      intro j y hy
      simp only [Bclause, Blit, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with ((((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) |
        (rfl | rfl | rfl | rfl)) | (rfl | rfl)) | h5
      all_goals first | omega | (obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp h5; omega)
    exact hne ((hrange_j j1 x h1).symm.trans (hrange_j j2 x h2))
  have hsum_ge : 7 * m ≤ ∑ j ∈ Finset.range m, (D ∩ Bclause j).card := by
    calc 7 * m = ∑ _ ∈ Finset.range m, 7 := by simp [mul_comm]
      _ ≤ ∑ j ∈ Finset.range m, (D ∩ Bclause j).card :=
        Finset.sum_le_sum fun j hj ↦ hBclause_ge j (Finset.mem_range.mp hj)
  have hBall_eq_D : Ball = D := Finset.eq_of_subset_of_card_le hBall_sub (by
    rw [hBall_card, hDconn_card]; rw [reductionBound_eq] at hD_card; omega)
  have hBclause_eq : ∀ j < m, (D ∩ Bclause j).card = 7 := by
    intro j hj
    by_contra hne
    have hgt : 7 < (D ∩ Bclause j).card := by have := hBclause_ge j hj; omega
    have hsum_gt : 7 * m < ∑ i ∈ Finset.range m, (D ∩ Bclause i).card := by
      calc 7 * m = ∑ _ ∈ Finset.range m, 7 := by simp [mul_comm]
        _ < ∑ i ∈ Finset.range m, (D ∩ Bclause i).card :=
          Finset.sum_lt_sum (fun i hi ↦ hBclause_ge i (Finset.mem_range.mp hi))
            ⟨j, Finset.mem_range.mpr hj, hgt⟩
    have hle := Finset.card_le_card hBall_sub
    rw [hBall_card, hDconn_card] at hle
    rw [reductionBound_eq] at hD_card; omega
  -- Exact equality on every sub-bucket!
  have hBlit_eq_one : ∀ j < m, ∀ r < 3, (D ∩ Blit j r).card = 1 := by
    intro j hj r hr
    have htot := hBclause_eq j hj
    have hsum := hBclause_sum j hj
    have h0 := hBlit_ge j hj 0 (by decide)
    have h1 := hBlit_ge j hj 1 (by decide)
    have h2 := hBlit_ge j hj 2 (by decide)
    have h5 := hB5_ge j hj
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl <;> omega
  have hB5_eq_two : ∀ j < m, (D ∩ B5 j).card = 2 := by
    intro j hj
    have htot := hBclause_eq j hj
    have hsum := hBclause_sum j hj
    have h0 := hBlit_eq_one j hj 0 (by decide)
    have h1 := hBlit_eq_one j hj 1 (by decide)
    have h2 := hBlit_eq_one j hj 2 (by decide)
    omega
  -- No connection chord `e` is in `D`!
  have he_not_D : ∀ idx < 3 * m, (nextOcc φ idx).isSome → ∀ b < 2,
      34 * m + 5 * (2 * idx + b) + 0 ∉ D := by
    intro idx _ _ b hb hmem
    rw [← hBall_eq_D] at hmem
    rcases Finset.mem_union.mp hmem with h1 | h2
    · obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp h1
      simp only [Finset.mem_range] at hj
      have hxb := (Finset.mem_inter.mp hxj).2
      simp only [Bclause, Blit, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hxb
      rcases hxb with ((((h | h | h | h) | (h | h | h | h)) | (h | h | h | h)) | (h | h)) | h5
      all_goals first | omega | (obtain ⟨g, _, h⟩ := Finset.mem_image.mp h5; omega)
    · obtain ⟨i', _, hmem'⟩ := Finset.mem_biUnion.mp h2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
      rcases hmem' with h | h <;> omega
  -- Every literal `(j, r)` has EXACTLY ONE of `t_r` or `f_r` in `D`!
  have htf_xor : ∀ j < m, ∀ r < 3,
      (34 * j + 6 * r ∈ D ∧ 34 * j + 6 * r + 5 ∉ D) ∨
      (34 * j + 6 * r ∉ D ∧ 34 * j + 6 * r + 5 ∈ D) := by
    intro j hj r hr
    obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp (hBlit_eq_one j hj r hr)
    have hx_in : x ∈ D ∩ Blit j r := hx_eq ▸ Finset.mem_singleton_self x
    have hxD : x ∈ D := (Finset.mem_inter.mp hx_in).1
    have hxB : x ∈ Blit j r := (Finset.mem_inter.mp hx_in).2
    have hnot_other : ∀ y ∈ Blit j r, y ≠ x → y ∉ D := fun y hyB hyx hyD ↦ by
      have : y ∈ D ∩ Blit j r := Finset.mem_inter.mpr ⟨hyD, hyB⟩
      rw [hx_eq, Finset.mem_singleton] at this; exact hyx this
    simp only [Blit, Finset.mem_insert, Finset.mem_singleton] at hxB
    rcases hxB with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨hxD, hnot_other _ (by simp [Blit]) (by omega)⟩
    · -- `p_ra ∈ D` leaves `p_rb` undominated!
      exfalso
      have hpb_not : 34 * j + 6 * r + 4 ∉ D := hnot_other _ (by simp [Blit]) (by omega)
      have hpbv : 34 * j + 6 * r + 4 ∈ redVertices φ := mem_redVertices_iff.mpr (Or.inl (by omega))
      obtain ⟨u, hu⟩ :=
        Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hD_dom _ hpbv hpb_not).1)
      simp only [Finset.mem_filter] at hu
      rcases mem_redVertices_iff.mp (hD_sub u hu.1) with hu_cl | ⟨iu, hiu, hnu, bu, hbu, qu, hqu,
        rfl⟩
      · have hadj := (adj_clause_clause hj (by omega : u / 34 < m) ⟨6 * r + 4, by omega⟩
          ⟨u % 34, Nat.mod_lt _ (by decide)⟩ (by
          have := G.ne_of_adj hu.2; dsimp; omega)).mp (by convert hu.2; dsimp; omega)
        have hpn := clause_p_neighbors ⟨r, hr⟩ 1 ⟨u % 34, Nat.mod_lt _ (by decide)⟩ hadj.2
        dsimp at hpn
        rcases hpn with h | h
        · exact hnot_other (34 * j + 6 * r) (by simp [Blit]) (by omega) (by convert hu.1; omega)
        · exact hnot_other (34 * j + 6 * r + 5) (by simp [Blit]) (by omega) (by convert hu.1; omega)
      · rcases (show qu = 0 ∨ 1 ≤ qu by omega) with rfl | hqu1
        · exact he_not_D iu hiu hnu bu hbu hu.1
        · exact not_adj_clause_claw hφ (by omega) hiu hnu hbu hqu1 hqu hu.2
    · -- `p_rb ∈ D` leaves `p_ra` undominated!
      exfalso
      have hpa_not : 34 * j + 6 * r + 3 ∉ D := hnot_other _ (by simp [Blit]) (by omega)
      have hpav : 34 * j + 6 * r + 3 ∈ redVertices φ := mem_redVertices_iff.mpr (Or.inl (by omega))
      obtain ⟨u, hu⟩ :=
        Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (hD_dom _ hpav hpa_not).1)
      simp only [Finset.mem_filter] at hu
      rcases mem_redVertices_iff.mp (hD_sub u hu.1) with hu_cl | ⟨iu, hiu, hnu, bu, hbu, qu, hqu,
        rfl⟩
      · have hadj := (adj_clause_clause hj (by omega : u / 34 < m) ⟨6 * r + 3, by omega⟩
          ⟨u % 34, Nat.mod_lt _ (by decide)⟩ (by
          have := G.ne_of_adj hu.2; dsimp; omega)).mp (by convert hu.2; dsimp; omega)
        have hpn := clause_p_neighbors ⟨r, hr⟩ 0 ⟨u % 34, Nat.mod_lt _ (by decide)⟩ hadj.2
        dsimp at hpn
        rcases hpn with h | h
        · exact hnot_other (34 * j + 6 * r) (by simp [Blit]) (by omega) (by convert hu.1; omega)
        · exact hnot_other (34 * j + 6 * r + 5) (by simp [Blit]) (by omega) (by convert hu.1; omega)
      · rcases (show qu = 0 ∨ 1 ≤ qu by omega) with rfl | hqu1
        · exact he_not_D iu hiu hnu bu hbu hu.1
        · exact not_adj_clause_claw hφ (by omega) hiu hnu hbu hqu1 hqu hu.2
    · exact Or.inr ⟨hnot_other _ (by simp [Blit]) (by omega), hxD⟩
  -- Step 3: Consistency along every `nextOcc` link!
  let chosenTrue (idx : ℕ) : Bool := decide (34 * (idx / 3) + 6 * (idx % 3) ∈ D)
  have hlink_consistent : ∀ idx idx', nextOcc φ idx = some idx' →
      (if decide ((literalAt φ idx).2 = (literalAt φ idx').2)
       then chosenTrue idx' = chosenTrue idx
       else chosenTrue idx' = !chosenTrue idx) := by
    intro idx idx' hnext
    obtain ⟨hidx_lt, hidx'_lt, _, hcl_lt, _⟩ := nextOcc_spec hφ hnext
    have hidx : idx < 3 * m := hidx_lt.trans hidx'_lt
    -- Check both `b = 0` (`isTrue = true`) and `b = 1` (`isTrue = false`):
    have hforbid : ∀ b < 2,
        let isTrue := decide (b = 0)
        let isTrue' := if decide ((literalAt φ idx).2 =
          (literalAt φ idx').2) then !isTrue else isTrue
        ¬ (chosenTrue idx = isTrue ∧ chosenTrue idx' = isTrue') := by
      intro b hb isTrue isTrue' ⟨hc1, hc2⟩
      let e := 34 * m + 5 * (2 * idx + b) + 0
      let se := 34 * m + 5 * (2 * idx + b) + 1
      let ep1 := 34 * (idx / 3) + (6 * (idx % 3) + (if isTrue then 0 else 5))
      let ep2 := 34 * (idx' / 3) + (6 * (idx' % 3) + (if isTrue' then 0 else 5))
      have hev : e ∈ redVertices φ :=
        mem_redVertices_iff.mpr (Or.inr ⟨idx, hidx, by simp [hnext], b, hb, 0, by decide, rfl⟩)
      have henot : e ∉ D := he_not_D idx hidx (by simp [hnext]) b hb
      have hep1_in : ep1 ∈ D := by
        rcases htf_xor (idx / 3) (by omega) (idx % 3) (Nat.mod_lt _ (by decide)) with ⟨ht,
          _⟩ | ⟨ht, hf⟩
        · have : isTrue = true := by rw [← hc1]; simp [chosenTrue, ht]
          simpa [ep1, this] using ht
        · have : isTrue = false := by rw [← hc1]; simp [chosenTrue, ht]
          simpa [ep1, this, Nat.add_assoc] using hf
      have hep2_in : ep2 ∈ D := by
        rcases htf_xor (idx' / 3) (by omega) (idx' % 3) (Nat.mod_lt _ (by decide)) with ⟨ht,
          _⟩ | ⟨ht, hf⟩
        · have : isTrue' = true := by rw [← hc2]; simp [chosenTrue, ht]
          simpa [ep2, this] using ht
        · have : isTrue' = false := by rw [← hc2]; simp [chosenTrue, ht]
          simpa [ep2, this, Nat.add_assoc] using hf
      have h3 : ({se, ep1, ep2} : Finset ℕ) ⊆ D.filter (G.Adj e) := by
        intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hu ⊢
        rcases hu with rfl | rfl | rfl
        · exact ⟨hs_mem idx hidx (by simp [hnext]) b hb,
            (claw_adj_iff hφ hidx (by simp [hnext]) hb (by decide)
              (by decide) hev).mpr (by simp [e, m])⟩
        · exact ⟨hep1_in, (adj_conn_clause_iff hφ hidx hnext hb (by omega)
            ⟨6 * (idx % 3) + (if isTrue then 0 else 5), by
              cases isTrue <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩).mpr
            (Or.inl ⟨rfl, Or.inl rfl⟩)⟩
        · exact ⟨hep2_in, (adj_conn_clause_iff hφ hidx hnext hb (by omega)
            ⟨6 * (idx' % 3) + (if isTrue' then 0 else 5), by
              cases isTrue' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩).mpr
            (Or.inr ⟨rfl, Or.inl rfl⟩)⟩
      have hc3 : ({se, ep1, ep2} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, se, ep1, ep2]
          cases isTrue <;> cases isTrue' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega),
          Finset.card_pair (by
            dsimp [ep1, ep2]
            cases isTrue <;> cases isTrue' <;>
              simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)]
      have := (Finset.card_le_card h3).trans (hD_dom e hev henot).2; omega
    have h0 := hforbid 0 (by decide)
    have h1 := hforbid 1 (by decide)
    simp only [decide_true, Bool.not_true] at h0 h1
    split_ifs at h0 h1 ⊢ <;> cases hci : chosenTrue idx <;>
      cases hci' : chosenTrue idx' <;> simp_all
  -- Define base assignment `σ₀` from the first occurrence of each variable!
  let firstOcc (x : ℕ) : Option ℕ :=
    (List.range (3 * m)).find? fun idx ↦ decide ((literalAt φ idx).1 = x)
  let σ₀ (x : ℕ) : Bool :=
    match firstOcc x with
    | some idx => if chosenTrue idx then (literalAt φ idx).2 else !(literalAt φ idx).2
    | none => false
  -- Prove by strong induction on `idx < 3 * m` that `σ₀` matches `chosenTrue` everywhere!
  have hσ₀_match : ∀ idx < 3 * m, (σ₀ (literalAt φ idx).1 == (literalAt φ idx).2) =
    chosenTrue idx := by
    intro idx
    induction idx using Nat.strongRecOn with
    | ind idx ih =>
      intro hidx
      let x := (literalAt φ idx).1
      -- Check if there is any earlier occurrence `prev < idx` with variable `x`.
      by_cases hearlier : ∃ prev < idx, (literalAt φ prev).1 = x
      · -- Take the largest such `prev < idx`!
        let S := (Finset.range idx).filter fun p ↦ (literalAt φ p).1 = x
        have hSne : S.Nonempty := by
          obtain ⟨p, hp1, hp2⟩ := hearlier
          exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp1, hp2⟩⟩
        let prev := S.max' hSne
        have hprev_mem := Finset.max'_mem S hSne
        simp only [S, Finset.mem_filter, Finset.mem_range] at hprev_mem
        have hnext_prev : nextOcc φ prev = some idx := by
          rw [nextOcc_eq_find?, List.find?_eq_some_iff_append]
          refine ⟨by simp only [Bool.and_eq_true, decide_eq_true_eq]
                     exact ⟨hprev_mem.1, hprev_mem.2.symm⟩,
            List.range idx, (List.range (3 * m)).drop (idx + 1), list_range_split hidx, ?_⟩
          intro mid hmid
          simp only [List.mem_range] at hmid
          rw [Bool.not_eq_true', Bool.and_eq_false_iff]
          simp only [decide_eq_false_iff_not, not_lt]
          by_cases hle : mid ≤ prev
          · exact Or.inl hle
          · right; intro heq
            have : mid ∈ S :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmid, heq.trans hprev_mem.2⟩
            have := Finset.le_max' S mid this; omega
        have hcons := hlink_consistent prev idx hnext_prev
        have hih := ih prev hprev_mem.1 (hprev_mem.1.trans hidx)
        rw [hprev_mem.2] at hih
        dsimp [x] at hprev_mem hih ⊢
        split_ifs at hcons with hpol
        · rw [decide_eq_true_iff] at hpol; rw [hpol] at hih; rw [hcons, ← hih]
        · have hpol' : (literalAt φ idx).2 = !(literalAt φ prev).2 := by
            cases h1 : (literalAt φ prev).2 <;> cases h2 : (literalAt φ idx).2 <;> simp_all
          rw [hpol', hcons,
            ← hih]; cases σ₀ (literalAt φ idx).1 <;> cases (literalAt φ prev).2 <;> decide
      · -- `idx` is the FIRST occurrence of `x`, so `firstOcc x = some idx`!
        push Not at hearlier
        have hfirst : firstOcc x = some idx := by
          unfold firstOcc
          rw [List.find?_eq_some_iff_append]
          refine ⟨by simp [x], List.range idx, (List.range (3 * m)).drop (idx + 1),
            list_range_split hidx, ?_⟩
          intro mid hmid; simp only [List.mem_range] at hmid
          simp [hearlier mid hmid]
        dsimp only [σ₀]
        rw [hfirst]
        dsimp only
        cases h1 : chosenTrue idx <;> cases h2 : (literalAt φ idx).2 <;> simp
  -- Step 4: Handle isolated literal-1 variables (`a1a`/`a1b` in an all-false clause).
  let isAllFalseIso (j : ℕ) : Bool :=
    decide (j < m) && !chosenTrue (3 * j) && !chosenTrue (3 * j + 1) && !chosenTrue (3 * j + 2)
  let σ (x : ℕ) : Bool :=
    match (List.range m).find? fun j ↦
        isAllFalseIso j && decide ((literalAt φ (3 * j + 1)).1 = x) with
    | some j => (literalAt φ (3 * j + 1)).2
    | none => σ₀ x
  -- Key property: if `isAllFalseIso j = true`, then `3 * j + 1` is the UNIQUE occurrence of its
  -- variable!
  have hiso_unique : ∀ j < m, isAllFalseIso j = true →
      ∀ idx < 3 * m, (literalAt φ idx).1 = (literalAt φ (3 * j + 1)).1 → idx = 3 * j + 1 := by
    intro j hj hiso idx hidx hvar
    have hfalse0 : chosenTrue (3 * j) = false := by
      simp only [isAllFalseIso, Bool.and_eq_true, Bool.not_eq_true'] at hiso; exact hiso.1.1.2
    have hfalse1 : chosenTrue (3 * j + 1) = false := by
      simp only [isAllFalseIso, Bool.and_eq_true, Bool.not_eq_true'] at hiso; exact hiso.1.2
    have hfalse2 : chosenTrue (3 * j + 2) = false := by
      simp only [isAllFalseIso, Bool.and_eq_true, Bool.not_eq_true'] at hiso; exact hiso.2
    have hf0 : 34 * j + 5 ∈ D := by
      rcases htf_xor j hj 0 (by decide) with ⟨ht, _⟩ | ⟨_, hf⟩
      · exfalso
        simp only [chosenTrue, show (3 * j) / 3 = j by omega, show (3 * j) % 3 = 0 by omega,
          decide_eq_false_iff_not] at hfalse0
        exact hfalse0 (by simpa using ht)
      · exact hf
    have hf1 : 34 * j + 11 ∈ D := by
      rcases htf_xor j hj 1 (by decide) with ⟨ht, _⟩ | ⟨_, hf⟩
      · exfalso
        simp only [chosenTrue, show (3 * j + 1) / 3 = j by omega,
          show (3 * j + 1) % 3 = 1 by omega, decide_eq_false_iff_not] at hfalse1
        exact hfalse1 (by simpa using ht)
      · exact hf
    have hf2 : 34 * j + 17 ∈ D := by
      rcases htf_xor j hj 2 (by decide) with ⟨ht, _⟩ | ⟨_, hf⟩
      · exfalso
        simp only [chosenTrue, show (3 * j + 2) / 3 = j by omega,
          show (3 * j + 2) % 3 = 2 by omega, decide_eq_false_iff_not] at hfalse2
        exact hfalse2 (by simpa using ht)
      · exact hf
    -- By `hB5_eq_two j hj`, `D ∩ B5 j = {34*j + x, 34*j + y}`, and by `clause_all_false_forces_a1`,
    -- `a1a ∈ D ∨ a1b ∈ D`!
    obtain ⟨v1, v2, hv12, hB5_eq⟩ := Finset.card_eq_two.mp (hB5_eq_two j hj)
    have hv1m : v1 ∈ D ∩ B5 j := by rw [hB5_eq]; simp
    have hv2m : v2 ∈ D ∩ B5 j := by rw [hB5_eq]; simp
    obtain ⟨g1, hg1, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv1m).2
    obtain ⟨g2, hg2, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv2m).2
    have ha1_in : 34 * j + 7 ∈ D ∨ 34 * j + 8 ∈ D := by
      have hD_clause_mem : ∀ v : Fin 34, 34 * j + v.1 ∈ D →
          v ∈ ([5, 11, 17, 21, 30, g1, g2] : List (Fin 34)) := by
        intro v hmem
        rw [← hBall_eq_D] at hmem
        rcases Finset.mem_union.mp hmem with h1 | h2
        · obtain ⟨j', _, hxj⟩ := Finset.mem_biUnion.mp h1
          have hxb := (Finset.mem_inter.mp hxj).2
          have hj_eq : j' = j := by
            simp only [Bclause, Blit, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton] at hxb
            rcases hxb with ((((h | h | h | h) | (h | h | h | h)) |
              (h | h | h | h)) | (h | h)) | h5
            all_goals first | omega | (obtain ⟨g, _, h⟩ := Finset.mem_image.mp h5; omega)
          rw [hj_eq] at hxj hxb
          have hD_in : 34 * j + v.1 ∈ D := (Finset.mem_inter.mp hxj).1
          simp only [Bclause, Finset.mem_union] at hxb
          rcases hxb with (((h0 | h1') | h2') | hc) | h5
          · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hBlit_eq_one j hj 0 (by decide))
            have h1'' : 34 * j + 5 ∈ ({z} : Finset ℕ) :=
              hz ▸ Finset.mem_inter.mpr ⟨hf0, by simp [Blit]⟩
            have h2'' : 34 * j + v.1 ∈ ({z} : Finset ℕ) :=
              hz ▸ Finset.mem_inter.mpr ⟨hD_in, h0⟩
            simp at h1'' h2''; rw [show v = 5 from Fin.ext (by dsimp; omega)]; simp
          · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hBlit_eq_one j hj 1 (by decide))
            have h1'' : 34 * j + 11 ∈ ({z} : Finset ℕ) :=
              hz ▸ Finset.mem_inter.mpr ⟨hf1, by simp [Blit]⟩
            have h2'' : 34 * j + v.1 ∈ ({z} : Finset ℕ) :=
              hz ▸ Finset.mem_inter.mpr ⟨hD_in, h1'⟩
            simp at h1'' h2''; rw [show v = 11 from Fin.ext (by dsimp; omega)]; simp
          · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hBlit_eq_one j hj 2 (by decide))
            have h1'' : 34 * j + 17 ∈ ({z} : Finset ℕ) :=
              hz ▸ Finset.mem_inter.mpr ⟨hf2, by simp [Blit]⟩
            have h2'' : 34 * j + v.1 ∈ ({z} : Finset ℕ) :=
              hz ▸ Finset.mem_inter.mpr ⟨hD_in, h2'⟩
            simp at h1'' h2''; rw [show v = 17 from Fin.ext (by dsimp; omega)]; simp
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
            rcases hc with h | h
            · rw [show v = 21 from Fin.ext (by dsimp; omega)]; simp
            · rw [show v = 30 from Fin.ext (by dsimp; omega)]; simp
          · have : 34 * j + v.1 ∈ D ∩ B5 j := Finset.mem_inter.mpr ⟨hD_in, h5⟩
            rw [hB5_eq, Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h | h
            · rw [show v = g1 from Fin.ext (by omega)]; simp
            · rw [show v = g2 from Fin.ext (by omega)]; simp
        · obtain ⟨i', _, hmem'⟩ := Finset.mem_biUnion.mp h2
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
          rcases hmem' with h | h <;> omega
      exact allFalse_forces_a1 hφ hD_sub hD_dom' hj (hc1_mem j hj) (hc2_mem j hj)
        hf0 hf1 hf2 (List.mem_toFinset.mp hg1) (List.mem_toFinset.mp hg2)
        hv12 (Finset.mem_inter.mp hv1m).1 (Finset.mem_inter.mp hv2m).1 hD_clause_mem
        he_not_D
  -- Now if `idx ≠ 3 * j + 1` had the same variable, then `3 * j + 1` would have either an incoming
  -- or outgoing connection chord `e` attached to its false slot, contradicting `hD_dom e`!
    by_contra hne_idx
    have hconn_contrad : ∀ (i1 b1 : ℕ), i1 < 3 * m → b1 < 2 →
        ∀ i2, nextOcc φ i1 = some i2 →
        let isT1 := decide (b1 = 0)
        let isT2 := if decide ((literalAt φ i1).2 = (literalAt φ i2).2) then !isT1 else isT1
        ((i1 = 3 * j + 1 ∧ isT1 = false) ∨ (i2 = 3 * j + 1 ∧ isT2 = false)) → False := by
      intro i1 b1 hi1 hb1 i2 hnext1 isT1 isT2 hattach
      let e := 34 * m + 5 * (2 * i1 + b1) + 0
      let se := 34 * m + 5 * (2 * i1 + b1) + 1
      have hev : e ∈ redVertices φ :=
        mem_redVertices_iff.mpr (Or.inr ⟨i1, hi1, by simp [hnext1], b1, hb1, 0, by decide, rfl⟩)
      have henot : e ∉ D := he_not_D i1 hi1 (by simp [hnext1]) b1 hb1
      have hse_adj : G.Adj e se :=
        (claw_adj_iff hφ hi1 (by simp [hnext1]) hb1 (by decide) (by decide) hev).mpr
          (by simp [e, m])
      have hse_in : se ∈ D := hs_mem i1 hi1 (by simp [hnext1]) b1 hb1
      have hf1_adj : G.Adj e (34 * j + 11) := by
        rcases hattach with ⟨hi1_eq, hisT1⟩ | ⟨hi2_eq, hisT2⟩
        · dsimp only [isT1] at hisT1
          exact (adj_conn_clause_iff hφ hi1 hnext1 hb1 hj 11).mpr
            (Or.inl ⟨by omega, Or.inl (by simp [hisT1, hi1_eq])⟩)
        · dsimp only [isT2, isT1] at hisT2
          exact (adj_conn_clause_iff hφ hi1 hnext1 hb1 hj 11).mpr
            (Or.inr ⟨by omega, Or.inl (by rw [hisT2]; simp [hi2_eq])⟩)
      rcases ha1_in with ha7 | ha8
      · have ha_adj : G.Adj e (34 * j + 7) := by
          rcases hattach with ⟨hi1_eq, hisT1⟩ | ⟨hi2_eq, hisT2⟩
          · dsimp only [isT1] at hisT1
            exact (adj_conn_clause_iff hφ hi1 hnext1 hb1 hj 7).mpr
              (Or.inl ⟨by omega, Or.inr ⟨1, by simp [hisT1, hi1_eq], Or.inl rfl⟩⟩)
          · dsimp only [isT2, isT1] at hisT2
            exact (adj_conn_clause_iff hφ hi1 hnext1 hb1 hj 7).mpr
              (Or.inr ⟨by omega, Or.inr ⟨1, by rw [hisT2]; simp [hi2_eq], Or.inl rfl⟩⟩)
        have h3 : ({se, 34 * j + 11, 34 * j + 7} : Finset ℕ) ⊆ D.filter (G.Adj e) := by
          intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hu ⊢
          rcases hu with rfl | rfl | rfl
          · exact ⟨hse_in, hse_adj⟩
          · exact ⟨hf1, hf1_adj⟩
          · exact ⟨ha7, ha_adj⟩
        have hc3 : ({se, 34 * j + 11, 34 * j + 7} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [se]; omega), Finset.card_pair (by omega)]
        have := (Finset.card_le_card h3).trans (hD_dom e hev henot).2; omega
      · have ha_adj : G.Adj e (34 * j + 8) := by
          rcases hattach with ⟨hi1_eq, hisT1⟩ | ⟨hi2_eq, hisT2⟩
          · dsimp only [isT1] at hisT1
            exact (adj_conn_clause_iff hφ hi1 hnext1 hb1 hj 8).mpr
              (Or.inl ⟨by omega, Or.inr ⟨1, by simp [hisT1, hi1_eq], Or.inr rfl⟩⟩)
          · dsimp only [isT2, isT1] at hisT2
            exact (adj_conn_clause_iff hφ hi1 hnext1 hb1 hj 8).mpr
              (Or.inr ⟨by omega, Or.inr ⟨1, by rw [hisT2]; simp [hi2_eq], Or.inr rfl⟩⟩)
        have h3 : ({se, 34 * j + 11, 34 * j + 8} : Finset ℕ) ⊆ D.filter (G.Adj e) := by
          intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hu ⊢
          rcases hu with rfl | rfl | rfl
          · exact ⟨hse_in, hse_adj⟩
          · exact ⟨hf1, hf1_adj⟩
          · exact ⟨ha8, ha_adj⟩
        have hc3 : ({se, 34 * j + 11, 34 * j + 8} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [se]; omega), Finset.card_pair (by omega)]
        have := (Finset.card_le_card h3).trans (hD_dom e hev henot).2; omega
    rcases lt_or_gt_of_ne hne_idx with hlt | hgt
    · -- `idx < 3 * j + 1`: largest `prev < 3 * j + 1` of same variable gives `nextOcc`
      let S := (Finset.range (3 * j + 1)).filter fun p ↦ (literalAt φ p).1 =
        (literalAt φ (3 * j + 1)).1
      have hSne : S.Nonempty := ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hvar⟩⟩
      let prev := S.max' hSne
      have hpm := Finset.max'_mem S hSne
      simp only [S, Finset.mem_filter, Finset.mem_range] at hpm
      have hnext_prev : nextOcc φ prev = some (3 * j + 1) := by
        rw [nextOcc_eq_find?, List.find?_eq_some_iff_append]
        refine ⟨by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hpm.1, hpm.2.symm⟩,
          List.range (3 * j + 1), (List.range (3 * m)).drop (3 * j + 2),
          list_range_split (by omega), ?_⟩
        intro mid hmid; simp only [List.mem_range] at hmid
        rw [Bool.not_eq_true', Bool.and_eq_false_iff]
        simp only [decide_eq_false_iff_not, not_lt]
        by_cases hle : mid ≤ prev
        · exact Or.inl hle
        · right; intro heq
          have := Finset.le_max' S mid (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmid,
            heq.trans hpm.2⟩)
          omega
      by_cases hpol : (literalAt φ prev).2 = (literalAt φ (3 * j + 1)).2
      · exact hconn_contrad prev 0 (hpm.1.trans (by omega)) (by decide) (3 * j + 1) hnext_prev
          (Or.inr ⟨rfl, by simp [hpol]⟩)
      · exact hconn_contrad prev 1 (hpm.1.trans (by omega)) (by decide) (3 * j + 1) hnext_prev
          (Or.inr ⟨rfl, by simp [hpol]⟩)
    · -- `3 * j + 1 < idx`: `nextOcc φ (3 * j + 1)` is `some i2`, giving outgoing false-slot chord!
      have hne_find : ((List.range (3 * m)).find? fun idx' ↦
          decide (3 * j + 1 < idx') && decide ((literalAt φ idx').1 =
            (literalAt φ (3 * j + 1)).1)).isSome := by
        rw [List.find?_isSome]
        exact ⟨idx, List.mem_range.mpr hidx, by simp [hgt, hvar]⟩
      obtain ⟨i2, hnext_eq⟩ := Option.isSome_iff_exists.mp hne_find
      exact hconn_contrad (3 * j + 1) 1 (by omega) (by decide) i2 hnext_eq (Or.inl ⟨rfl, by decide⟩)
  -- Finally verify `φ.eval σ = true`!
  refine ⟨σ, (CNF.eval_eq_true_iff σ φ).mpr fun c hc ↦ ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
  have hlen := (hφ (φ[j]) (List.getElem_mem hj)).1
  rw [Clause.eval_eq_true_iff σ]
  by_cases hsome : chosenTrue (3 * j) = true ∨ chosenTrue (3 * j + 1) = true ∨
    chosenTrue (3 * j + 2) = true
  · -- Some literal `r` has `chosenTrue (3 * j + r) = true`; `σ` agrees with `σ₀` on its variable!
    have hex_r : ∃ r < 3, chosenTrue (3 * j + r) = true := by
      rcases hsome with h | h | h
      · exact ⟨0, by decide, h⟩
      · exact ⟨1, by decide, h⟩
      · exact ⟨2, by decide, h⟩
    obtain ⟨r, hr, htr⟩ := hex_r
    refine ⟨(φ[j])[r]'(by omega), List.getElem_mem _, ?_⟩
    have hlit : literalAt φ (3 * j + r) = (φ[j])[r] :=
      literalAt_getElem φ hj hr (by omega)
    rw [← hlit]
    have hσ_eq : σ (literalAt φ (3 * j + r)).1 = σ₀ (literalAt φ (3 * j + r)).1 := by
      unfold σ
      cases hf : (List.range m).find? fun j' ↦
          isAllFalseIso j' && decide ((literalAt φ (3 * j' + 1)).1 =
            (literalAt φ (3 * j + r)).1) with
      | none => rfl
      | some j' =>
        exfalso
        have hm' := List.mem_of_find?_eq_some hf
        have hp' := List.find?_some hf
        simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hm' hp'
        have heq_idx := hiso_unique j' hm' hp'.1 (3 * j + r) (by omega) hp'.2.symm
        have hj_eq : j' = j := by omega
        have hr_eq : r = 1 := by omega
        subst hj_eq; subst hr_eq
        simp [isAllFalseIso, htr] at hp'
    rw [hσ_eq]
    have hm := hσ₀_match (3 * j + r) (by omega)
    rw [htr] at hm; exact beq_iff_eq.mp hm
  · -- All three literals have `chosenTrue = false`, so `isAllFalseIso j = true`!
    push Not at hsome
    have hiso_j : isAllFalseIso j = true := by
      simp only [isAllFalseIso, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      exact ⟨⟨⟨hj, Bool.eq_false_iff.mpr hsome.1⟩, Bool.eq_false_iff.mpr hsome.2.1⟩,
        Bool.eq_false_iff.mpr hsome.2.2⟩
    refine ⟨(φ[j])[1]'(by omega), List.getElem_mem _, ?_⟩
    have hlit : literalAt φ (3 * j + 1) = (φ[j])[1] :=
      literalAt_getElem φ hj (by decide) (by omega)
    rw [← hlit]
    have hfind : ((List.range m).find? fun j' ↦
        isAllFalseIso j' && decide ((literalAt φ (3 * j' + 1)).1 =
          (literalAt φ (3 * j + 1)).1)).isSome := by
      rw [List.find?_isSome]; exact ⟨j, List.mem_range.mpr hj, by simp [hiso_j]⟩
    obtain ⟨j', hj'_eq⟩ := Option.isSome_iff_exists.mp hfind
    have hm' := List.mem_of_find?_eq_some hj'_eq
    have hp' := List.find?_some hj'_eq
    simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hm' hp'
    have hidx_eq := hiso_unique j' hm' hp'.1 (3 * j + 1) (by omega) hp'.2.symm
    have hj_eq : j' = j := by omega
    rw [hj_eq] at hj'_eq
    dsimp only [σ]; rw [hj'_eq]

end Cslib.Complexity.CircleOneTwoDomination
