/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.BrooksColoring
public import CslibFrontier.Computability.Complexity.Problems.Graph.BrooksColoring.Cherry

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Constructive Polynomial-Time Brooks Coloring (Main Correctness Proof)

This module proves `colorComponent_spec` and `brooksColoring_spec` from `BrooksColoring.lean`
using `reverseBfs_greedyColor_spec` and `exists_lovasz_cherry_abstract`.
-/

public section

namespace Cslib.Complexity

open Finset Cslib.Complexity

/-! ### 3. Correctness of `colorComponent` and `brooksColoring` -/

private theorem swapColor_lt (c1 c2 k c : ℕ) (h1 : c1 < k) (h2 : c2 < k) (hc : c < k) :
    swapColor c1 c2 c < k := by
  unfold swapColor; split_ifs <;> assumption

private theorem swapColor_inj (c1 c2 a b : ℕ) (h : swapColor c1 c2 a = swapColor c1 c2 b) :
    a = b := by
  unfold swapColor at h
  split_ifs at h <;> first | exact h | omega

private theorem swapColor_right (c1 c2 : ℕ) : swapColor c1 c2 c2 = c1 := by
  unfold swapColor; split_ifs with h1 h2
  · exact h1
  · rfl
  · exact (h2 rfl).elim

private theorem colorComponent_case1 (H : Graph) (k : ℕ) (C : List ℕ)
    (h : (!(C.filter fun v ↦ decide (subsetDegBool H C v < k)).isEmpty) = true) :
    let lowDeg := C.filter fun v ↦ decide (subsetDegBool H C v < k)
    colorComponent H k C = greedyColor H k (bfsOrder H C (lowDeg.headD 0)).reverse [] := by
  unfold colorComponent; dsimp only; simp only [h, ↓reduceIte]

private theorem colorComponent_case2 (H : Graph) (k : ℕ) (C : List ℕ)
    (h1 : ¬ (!(C.filter fun v ↦ decide (subsetDegBool H C v < k)).isEmpty) = true)
    (h2 : (!(C.filter fun v ↦
      let Cv := C.filter fun w ↦ decide (w ≠ v)
      decide ((bfsOrder H Cv (Cv.headD 0)).length < Cv.length)).isEmpty) = true) :
    let cutVerts := C.filter fun v ↦
      let Cv := C.filter fun w ↦ decide (w ≠ v)
      decide ((bfsOrder H Cv (Cv.headD 0)).length < Cv.length)
    let x := cutVerts.headD 0
    let Cx := C.filter fun w ↦ decide (w ≠ x)
    let S1 := bfsOrder H Cx (Cx.headD 0)
    let S2 := Cx.filter fun w ↦ !S1.contains w
    let col1 := greedyColor H k (bfsOrder H (x :: S1) x).reverse []
    let col2 := greedyColor H k (bfsOrder H (x :: S2) x).reverse []
    let c1 := lookupColor col1 x
    let c2 := lookupColor col2 x
    colorComponent H k C =
      col1 ++ (col2.filter fun p ↦ decide (p.1 ≠ x)).map fun p ↦ (p.1, swapColor c1 c2 p.2) := by
  unfold colorComponent; dsimp only
  simp only [Bool.eq_false_iff.mpr h1, Bool.false_eq_true, h2, ↓reduceIte]

private theorem colorComponent_case3 (H : Graph) (k : ℕ) (C : List ℕ)
    (h1 : ¬ (!(C.filter fun v ↦ decide (subsetDegBool H C v < k)).isEmpty) = true)
    (h2 : ¬ (!(C.filter fun v ↦
      let Cv := C.filter fun w ↦ decide (w ≠ v)
      decide ((bfsOrder H Cv (Cv.headD 0)).length < Cv.length)).isEmpty) = true)
    (h3 : (!((C.flatMap fun x ↦ C.flatMap fun y ↦ C.map fun z ↦ ((x, y), z)).filter
      (isLovaszCherry H C)).isEmpty) = true) :
    let cherries := (C.flatMap fun x ↦ C.flatMap fun y ↦ C.map fun z ↦ ((x, y), z)).filter
      (isLovaszCherry H C)
    let t := cherries.headD ((0, 0), 0)
    let x := t.1.1
    let y := t.1.2
    let z := t.2
    let rem := C.filter fun w ↦ decide (w ≠ y) && decide (w ≠ z)
    colorComponent H k C = greedyColor H k (bfsOrder H rem x).reverse [(y, 0), (z, 0)] := by
  unfold colorComponent; dsimp only
  simp only [Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2, Bool.false_eq_true, h3, ↓reduceIte]

/-- Helper: `colorComponent H k C` properly `k`-colors a connected component `C` of `H`
whenever `k ≥ 3`, every vertex in `C` has `H`-degree `≤ k`, and `C` is not a `K_{k+1}`
component. -/
theorem colorComponent_spec (H : Graph) (k : ℕ) (hk : 3 ≤ k) (C : List ℕ)
    (hC_ne : C ≠ []) (hC_nd : C.Nodup) (hC_sub : ∀ x ∈ C, x ∈ H.vertices)
    (hC_closed : ∀ x ∈ C, ∀ w ∈ H.vertices, H.adjBool x w = true → w ∈ C)
    (hC_conn : ∀ x (hx : x ∈ C) y (hy : y ∈ C),
      (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ C}).Reachable
        ⟨⟨x, hC_sub x hx⟩, hx⟩ ⟨⟨y, hC_sub y hy⟩, hy⟩)
    (hΔ : ∀ v : {w // w ∈ H.vertices}, H.induced.degree v ≤ k)
    (hnot_K : ¬ (C.length = k + 1 ∧ ∀ x ∈ C, subsetDegBool H H.distinctVertices x = k)) :
    let cols := colorComponent H k C
    (cols.map Prod.fst).Nodup ∧
    (∀ p ∈ cols, p.2 < k) ∧
    (∀ p ∈ cols, ∀ q ∈ cols, H.adjBool p.1 q.1 = true → p.2 ≠ q.2) ∧
    (∀ v, v ∈ cols.map Prod.fst ↔ v ∈ C) := by
  classical
  have hk_pos : 0 < k := by omega
  have hdeg_C_eq : ∀ x ∈ C, subsetDegBool H C x = subsetDegBool H H.distinctVertices x := by
    intro x hx
    unfold subsetDegBool
    rw [← List.toFinset_card_of_nodup (hC_nd.filter _),
      ← List.toFinset_card_of_nodup (H.nodup_distinctVertices.filter _)]
    congr 1; ext w
    simp only [List.mem_toFinset, List.mem_filter]
    exact ⟨fun ⟨hw, ha⟩ ↦ ⟨H.mem_distinctVertices.mpr (hC_sub w hw), ha⟩,
      fun ⟨hw, ha⟩ ↦ ⟨hC_closed x hx w (H.mem_distinctVertices.mp hw) ha, ha⟩⟩
  have hdeg_C_le : ∀ x (hx : x ∈ C), subsetDegBool H C x ≤ k := fun x hx ↦ by
    rw [hdeg_C_eq x hx, subsetDegBool_eq_degree H ⟨x, hC_sub x hx⟩]
    exact hΔ ⟨x, hC_sub x hx⟩
  -- Helper: `bfsOrder H C r` covers all of `C` when `r ∈ C`.
  have hbfs_full : ∀ r ∈ C, (bfsOrder H C r).length = C.length := by
    intro r hr
    obtain ⟨hB_nd, hB_sub, _, _, _, hB_reach⟩ := bfsOrder_spec H C hC_nd hC_sub hr
    rw [← List.toFinset_card_of_nodup hB_nd, ← List.toFinset_card_of_nodup hC_nd]
    congr 1; ext x; simp only [List.mem_toFinset]
    exact ⟨hB_sub x, fun hx ↦ (hB_reach x hx).mpr (hC_conn r hr x hx)⟩
  set lowDeg := C.filter fun v ↦ decide (subsetDegBool H C v < k)
  by_cases hlow : (!lowDeg.isEmpty) = true
  · -- **Case 1**: some `r ∈ C` has `deg_C(r) < k`!
    have hcol_eq : colorComponent H k C =
        greedyColor H k (bfsOrder H C (lowDeg.headD 0)).reverse [] :=
      colorComponent_case1 H k C hlow
    have hlow_ne : lowDeg ≠ [] := List.isEmpty_eq_false_iff.mp (by simpa using hlow)
    have hr_mem : lowDeg.headD 0 ∈ lowDeg := by
      cases h : lowDeg with | nil => exact (hlow_ne h).elim | cons a as => simp
    have hrC : lowDeg.headD 0 ∈ C := (List.mem_filter.mp hr_mem).1
    have hr_lt : subsetDegBool H C (lowDeg.headD 0) < k :=
      decide_eq_true_eq.mp (List.mem_filter.mp hr_mem).2
    have hres := reverseBfs_greedyColor_spec H k hk_pos C hC_nd hC_sub hrC (hbfs_full _ hrC) []
      (by simp) (by simp) (by simp) (by simp)
      (fun x hx _ ↦ by simpa [subsetDegBool] using hdeg_C_le x hx)
      (Or.inl (by simpa [subsetDegBool] using hr_lt))
    dsimp only; rw [hcol_eq]
    exact ⟨hres.1, hres.2.1, hres.2.2.1, fun v ↦ by simpa using hres.2.2.2 v⟩
  · -- All vertices in `C` have `deg_C = k`!
    have hreg_C : ∀ x (hx : x ∈ C), subsetDegBool H C x = k := by
      intro x hx
      have hle := hdeg_C_le x hx
      have hnot_lt : ¬ subsetDegBool H C x < k := fun hlt ↦ by
        have hmem : x ∈ lowDeg := List.mem_filter.mpr ⟨hx, decide_eq_true_eq.mpr hlt⟩
        have hne := List.ne_nil_of_mem hmem
        simp [List.isEmpty_eq_false_iff.mpr hne] at hlow
      omega
    have hC_ge4 : 4 ≤ C.length := by
      obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil C hC_ne
      have hd := hreg_C x₀ hx₀
      unfold subsetDegBool at hd
      have hsub_er : (C.filter fun w ↦ H.adjBool x₀ w).toFinset ⊆ C.toFinset.erase x₀ := by
        intro w hw
        have hf := List.mem_filter.mp (List.mem_toFinset.mp hw)
        exact Finset.mem_erase.mpr ⟨fun hEq ↦ by
          have := (H.adjBool_eq_true_iff x₀ w).mp hf.2
          exact H.toSimpleGraph.ne_of_adj this hEq.symm, List.mem_toFinset.mpr hf.1⟩
      have hc := Finset.card_le_card hsub_er
      rw [List.toFinset_card_of_nodup (hC_nd.filter _), Finset.card_erase_of_mem
        (List.mem_toFinset.mpr hx₀), List.toFinset_card_of_nodup hC_nd] at hc
      omega
    set cutVerts := C.filter fun v ↦
      let Cv := C.filter fun w ↦ decide (w ≠ v)
      decide ((bfsOrder H Cv (Cv.headD 0)).length < Cv.length)
    by_cases hcut : (!cutVerts.isEmpty) = true
    · -- **Case 2**: `x := cutVerts.headD 0` is a cut-vertex of `C`!
      have hcut_ne : cutVerts ≠ [] := List.isEmpty_eq_false_iff.mp (by simpa using hcut)
      have hx_mem : cutVerts.headD 0 ∈ cutVerts := by
        cases h : cutVerts with | nil => exact (hcut_ne h).elim | cons a as => simp
      set x := cutVerts.headD 0
      have hxC : x ∈ C := (List.mem_filter.mp hx_mem).1
      set Cx := C.filter fun w ↦ decide (w ≠ x)
      have hCx_nd : Cx.Nodup := hC_nd.filter _
      have hCx_sub : ∀ y ∈ Cx, y ∈ H.vertices := fun y hy ↦ hC_sub y (List.mem_filter.mp hy).1
      have hCx_len : Cx.length = C.length - 1 := by
        rw [← List.toFinset_card_of_nodup hCx_nd, ← List.toFinset_card_of_nodup hC_nd,
          ← Finset.card_erase_of_mem (List.mem_toFinset.mpr hxC)]
        congr 1; ext w; simp [Cx, Finset.mem_erase, and_comm]
      have hCx_ne : Cx ≠ [] := fun h ↦ by rw [h] at hCx_len; simp at hCx_len; omega
      have ha_mem : Cx.headD 0 ∈ Cx := by
        cases h : Cx with | nil => exact (hCx_ne h).elim | cons a as => simp
      set S1 := bfsOrder H Cx (Cx.headD 0)
      set S2 := Cx.filter fun w ↦ !S1.contains w
      have hS1_lt : S1.length < Cx.length := decide_eq_true_eq.mp (List.mem_filter.mp hx_mem).2
      obtain ⟨hS1_nd, hS1_sub, ha_S1, _, hS1_closed, hS1_reach⟩ :=
        bfsOrder_spec H Cx hCx_nd hCx_sub ha_mem
      have hS2_nd : S2.Nodup := hCx_nd.filter _
      have hS2_ne : S2 ≠ [] := by
        intro hnil
        have hsub : Cx.toFinset ⊆ S1.toFinset := fun w hw ↦ by
          by_contra hns
          have hmem : w ∈ S2 := List.mem_filter.mpr ⟨List.mem_toFinset.mp hw,
            by simpa using List.mem_toFinset.mp.mt hns⟩
          rw [hnil] at hmem; cases hmem
        have := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup hCx_nd, List.toFinset_card_of_nodup hS1_nd] at this
        dsimp only [S1] at hS1_lt; omega
      have hS12_disj : ∀ u ∈ S1, u ∉ S2 := fun u hu1 hu2 ↦ by
        have := (List.mem_filter.mp hu2).2; simp [hu1] at this
      have hS12_noEdge : ∀ u ∈ S1, ∀ v ∈ S2, H.adjBool u v = false := by
        intro u hu1 v hv2
        exact Bool.eq_false_iff.mpr fun hadj ↦
          hS12_disj v (hS1_closed u hu1 v (List.mem_filter.mp hv2).1 hadj) hv2
      have hx_not_S1 : x ∉ S1 := fun h ↦
        decide_eq_true_eq.mp (List.mem_filter.mp (hS1_sub x h)).2 rfl
      have hx_not_S2 : x ∉ S2 := fun h ↦
        decide_eq_true_eq.mp (List.mem_filter.mp (List.mem_filter.mp h).1).2 rfl
      -- Both `x :: S1` and `x :: S2` are connected and give `x` strictly `< k` neighbors!
      have hx_nb_S1 : ∃ u ∈ S1, H.adjBool x u = true := by
        by_contra hno; push Not at hno
        obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil S2 hS2_ne
        have hbC : b ∈ C := (List.mem_filter.mp (List.mem_filter.mp hb).1).1
        have haC : Cx.headD 0 ∈ C := (List.mem_filter.mp ha_mem).1
        obtain ⟨p⟩ := hC_conn _ haC _ hbC
        have hstay : ∀ {u v : {v : {w // w ∈ H.vertices} | v.1 ∈ C}}
            (q : (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ C}).Walk u v),
            u.1.1 ∈ S1 → v.1.1 ∈ S1 := by
          intro u v q
          induction q with
          | nil => exact id
          | @cons u₁ v₁ _ hadj _ ih =>
            intro hu
            have h1 : H.adjBool u₁.1.1 v₁.1.1 = true := (H.adjBool_eq_true_iff _ _).mpr hadj
            have hvx : v₁.1.1 ≠ x := fun hEq ↦ by
              have := hno u₁.1.1 hu; rw [H.adjBool_eq_true_iff] at h1
              have h2 : H.adjBool x u₁.1.1 = true := (H.adjBool_eq_true_iff _ _).mpr
                (hEq ▸ h1.symm)
              rw [h2] at this; exact absurd this (by decide)
            exact ih (hS1_closed u₁.1.1 hu v₁.1.1
              (List.mem_filter.mpr ⟨v₁.2, decide_eq_true_eq.mpr hvx⟩) h1)
        exact hS12_disj b (hstay p ha_S1) hb
      have hx_nb_S2 : ∃ v ∈ S2, H.adjBool x v = true := by
        by_contra hno; push Not at hno
        obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil S2 hS2_ne
        have hbC : b ∈ C := (List.mem_filter.mp (List.mem_filter.mp hb).1).1
        have haC : Cx.headD 0 ∈ C := (List.mem_filter.mp ha_mem).1
        obtain ⟨p⟩ := hC_conn _ hbC _ haC
        have hstay : ∀ {u v : {v : {w // w ∈ H.vertices} | v.1 ∈ C}}
            (q : (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ C}).Walk u v),
            u.1.1 ∈ S2 → v.1.1 ∈ S2 := by
          intro u v q
          induction q with
          | nil => exact id
          | @cons u₁ v₁ _ hadj _ ih =>
            intro hu
            have h1 : H.adjBool u₁.1.1 v₁.1.1 = true := (H.adjBool_eq_true_iff _ _).mpr hadj
            have hvx : v₁.1.1 ≠ x := fun hEq ↦ by
              have := hno u₁.1.1 hu
              have h2 : H.adjBool x u₁.1.1 = true := (H.adjBool_eq_true_iff _ _).mpr
                (hEq ▸ hadj.symm)
              rw [h2] at this; exact absurd this (by decide)
            have hv1_not_S1 : v₁.1.1 ∉ S1 := fun hv1 ↦ by
              have h2 : H.adjBool v₁.1.1 u₁.1.1 = true := (H.adjBool_eq_true_iff _ _).mpr hadj.symm
              exact hS12_disj u₁.1.1 (hS1_closed v₁.1.1 hv1 u₁.1.1
                (List.mem_filter.mp hu).1 h2) hu
            exact ih (List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨v₁.2, decide_eq_true_eq.mpr hvx⟩,
              by simp [hv1_not_S1]⟩)
        exact hS12_disj _ ha_S1 (hstay p hb)
      -- Connectedness of `x :: S1` and `x :: S2`:
      have hxS1_full : (bfsOrder H (x :: S1) x).length = (x :: S1).length := by
        obtain ⟨hB_nd, hB_sub, hr_B, _, hB_cl, _⟩ := bfsOrder_spec H (x :: S1)
          (List.nodup_cons.mpr ⟨hx_not_S1, hS1_nd⟩)
          (fun y hy ↦ (List.mem_cons.mp hy).elim (fun h ↦ h ▸ hC_sub x hxC)
            (fun h ↦ hCx_sub y (hS1_sub y h))) (List.mem_cons_self)
        rw [← List.toFinset_card_of_nodup hB_nd, ← List.toFinset_card_of_nodup
          (List.nodup_cons.mpr ⟨hx_not_S1, hS1_nd⟩)]
        congr 1; ext w; simp only [List.mem_toFinset]
        refine ⟨hB_sub w, fun hw ↦ ?_⟩
        rcases List.mem_cons.mp hw with rfl | hw1
        · exact hr_B
        · obtain ⟨u, hu1, hxu⟩ := hx_nb_S1
          have hu_B : u ∈ bfsOrder H (x :: S1) x :=
            hB_cl x hr_B u (List.mem_cons_of_mem _ hu1) hxu
          obtain ⟨q⟩ := ((hS1_reach u (hS1_sub u hu1)).mp hu1).symm.trans
            ((hS1_reach w (hS1_sub w hw1)).mp hw1)
          have hlift : ∀ {a b : {v : {w // w ∈ H.vertices} | v.1 ∈ Cx}}
              (p : (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ Cx}).Walk a b),
              a.1.1 ∈ S1 → a.1.1 ∈ bfsOrder H (x :: S1) x → b.1.1 ∈ bfsOrder H (x :: S1) x := by
            intro a b p
            induction p with
            | nil => exact fun _ h ↦ h
            | @cons a₁ b₁ _ hadj _ ih =>
              intro ha1 haB
              have hb1 : b₁.1.1 ∈ S1 :=
                hS1_closed a₁.1.1 ha1 b₁.1.1 b₁.2 ((H.adjBool_eq_true_iff _ _).mpr hadj)
              exact ih hb1 (hB_cl a₁.1.1 haB b₁.1.1 (List.mem_cons_of_mem _ hb1)
                ((H.adjBool_eq_true_iff _ _).mpr hadj))
          exact hlift q hu1 hu_B
      have hxS2_full : (bfsOrder H (x :: S2) x).length = (x :: S2).length := by
        obtain ⟨hB_nd, hB_sub, hr_B, _, hB_cl, _⟩ := bfsOrder_spec H (x :: S2)
          (List.nodup_cons.mpr ⟨hx_not_S2, hS2_nd⟩)
          (fun y hy ↦ (List.mem_cons.mp hy).elim (fun h ↦ h ▸ hC_sub x hxC)
            (fun h ↦ hCx_sub y (List.mem_filter.mp h).1)) (List.mem_cons_self)
        rw [← List.toFinset_card_of_nodup hB_nd, ← List.toFinset_card_of_nodup
          (List.nodup_cons.mpr ⟨hx_not_S2, hS2_nd⟩)]
        congr 1; ext w; simp only [List.mem_toFinset]
        refine ⟨hB_sub w, fun hw ↦ ?_⟩
        rcases List.mem_cons.mp hw with rfl | hw2
        · exact hr_B
        · -- Walk from `w` to `x` in `C`: look at the FIRST visit to `x`!
          have hwC : w ∈ C := (List.mem_filter.mp (List.mem_filter.mp hw2).1).1
          obtain ⟨p⟩ := hC_conn w hwC x hxC
          suffices ∀ {a b : {v : {w // w ∈ H.vertices} | v.1 ∈ C}}
              (q : (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ C}).Walk a b),
              b = ⟨⟨x, hC_sub x hxC⟩, hxC⟩ →
              a.1.1 ∈ x :: S2 → a.1.1 ∈ bfsOrder H (x :: S2) x from
            this p rfl (List.mem_cons_of_mem _ hw2)
          intro a b q
          induction q with
          | nil => intro hEq _; exact (congrArg (fun p ↦ p.1.1) hEq) ▸ hr_B
          | @cons a₁ b₁ _ hadj _ ih =>
            intro hEq ha
            rcases List.mem_cons.mp ha with ha_x | ha2
            · exact ha_x ▸ hr_B
            · have hb_in : b₁.1.1 ∈ x :: S2 := by
                by_cases hbx : b₁.1.1 = x
                · exact hbx ▸ List.mem_cons_self
                · right
                  have hb_not_S1 : b₁.1.1 ∉ S1 := fun hb1 ↦
                    hS12_disj a₁.1.1 (hS1_closed b₁.1.1 hb1 a₁.1.1 (List.mem_filter.mp ha2).1
                      ((H.adjBool_eq_true_iff _ _).mpr hadj.symm)) ha2
                  exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨b₁.2, decide_eq_true_eq.mpr hbx⟩,
                    by simp [hb_not_S1]⟩
              have hbB := ih hEq hb_in
              exact hB_cl b₁.1.1 hbB a₁.1.1 (List.mem_cons_of_mem _ ha2)
                ((H.adjBool_eq_true_iff _ _).mpr hadj.symm)
      -- Degree of `x` in `x :: S1` and `x :: S2` is strictly `< k`!
      have hdeg_x_S1 : ((x :: S1).filter fun w ↦ H.adjBool x w).length < k := by
        obtain ⟨v, hv2, hxv⟩ := hx_nb_S2
        have hsub : ((x :: S1).filter fun w ↦ H.adjBool x w).toFinset ⊆
            (C.filter fun w ↦ H.adjBool x w).toFinset.erase v := by
          intro w hw
          have hf := List.mem_filter.mp (List.mem_toFinset.mp hw)
          have hwC : w ∈ C := (List.mem_cons.mp hf.1).elim (fun h ↦ h ▸ hxC)
            (fun h ↦ (List.mem_filter.mp (hS1_sub w h)).1)
          refine Finset.mem_erase.mpr ⟨fun hEq ↦ ?_, List.mem_toFinset.mpr
            (List.mem_filter.mpr ⟨hwC, hf.2⟩)⟩
          rcases List.mem_cons.mp hf.1 with hwx | hw1
          · exact hx_not_S2 (hwx ▸ hEq ▸ hv2)
          · exact hS12_disj w hw1 (hEq ▸ hv2)
        have hc := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup ((List.nodup_cons.mpr ⟨hx_not_S1, hS1_nd⟩).filter _),
          Finset.card_erase_of_mem (List.mem_toFinset.mpr (List.mem_filter.mpr
            ⟨(List.mem_filter.mp (List.mem_filter.mp hv2).1).1, hxv⟩)),
          List.toFinset_card_of_nodup (hC_nd.filter _)] at hc
        have hd := hreg_C x hxC
        change (C.filter (H.adjBool x)).length = k at hd
        change ((x :: S1).filter (H.adjBool x)).length ≤ (C.filter (H.adjBool x)).length - 1 at hc
        change ((x :: S1).filter (H.adjBool x)).length < k
        omega
      have hdeg_x_S2 : ((x :: S2).filter fun w ↦ H.adjBool x w).length < k := by
        obtain ⟨u, hu1, hxu⟩ := hx_nb_S1
        have hsub : ((x :: S2).filter fun w ↦ H.adjBool x w).toFinset ⊆
            (C.filter fun w ↦ H.adjBool x w).toFinset.erase u := by
          intro w hw
          have hf := List.mem_filter.mp (List.mem_toFinset.mp hw)
          have hwC : w ∈ C := (List.mem_cons.mp hf.1).elim (fun h ↦ h ▸ hxC)
            (fun h ↦ (List.mem_filter.mp (List.mem_filter.mp h).1).1)
          refine Finset.mem_erase.mpr ⟨fun hEq ↦ ?_, List.mem_toFinset.mpr
            (List.mem_filter.mpr ⟨hwC, hf.2⟩)⟩
          rcases List.mem_cons.mp hf.1 with hwx | hw2
          · exact hx_not_S1 (hwx ▸ hEq ▸ hu1)
          · exact hS12_disj u hu1 (hEq ▸ hw2)
        have hc := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup ((List.nodup_cons.mpr ⟨hx_not_S2, hS2_nd⟩).filter _),
          Finset.card_erase_of_mem (List.mem_toFinset.mpr (List.mem_filter.mpr
            ⟨(List.mem_filter.mp (hS1_sub u hu1)).1, hxu⟩)),
          List.toFinset_card_of_nodup (hC_nd.filter _)] at hc
        have hd := hreg_C x hxC
        change (C.filter (H.adjBool x)).length = k at hd
        change ((x :: S2).filter (H.adjBool x)).length ≤ (C.filter (H.adjBool x)).length - 1 at hc
        change ((x :: S2).filter (H.adjBool x)).length < k
        omega
      -- Run `reverseBfs_greedyColor_spec` on both `x :: S1` and `x :: S2`!
      have hcol1 := reverseBfs_greedyColor_spec H k hk_pos (x :: S1)
        (List.nodup_cons.mpr ⟨hx_not_S1, hS1_nd⟩)
        (fun y hy ↦ (List.mem_cons.mp hy).elim (fun h ↦ h ▸ hC_sub x hxC)
          (fun h ↦ hCx_sub y (hS1_sub y h))) List.mem_cons_self hxS1_full []
        (by simp) (by simp) (by simp) (by simp)
        (fun y hy _ ↦ by
          have hyC : y ∈ C := (List.mem_cons.mp hy).elim (fun h ↦ h ▸ hxC)
            (fun h ↦ (List.mem_filter.mp (hS1_sub y h)).1)
          have hsub : ((x :: S1).filter fun w ↦ H.adjBool y w).length ≤ subsetDegBool H C y := by
            rw [← List.toFinset_card_of_nodup ((List.nodup_cons.mpr ⟨hx_not_S1, hS1_nd⟩).filter _),
              subsetDegBool, ← List.toFinset_card_of_nodup (hC_nd.filter _)]
            refine Finset.card_le_card fun w hw ↦ ?_
            have hf := List.mem_filter.mp (List.mem_toFinset.mp hw)
            exact List.mem_toFinset.mpr (List.mem_filter.mpr
              ⟨(List.mem_cons.mp hf.1).elim (fun h ↦ h ▸ hxC)
                (fun h ↦ (List.mem_filter.mp (hS1_sub w h)).1), hf.2⟩)
          have := hdeg_C_le y hyC; simp only [List.filter_nil, List.length_nil, add_zero]; omega)
        (Or.inl (by simpa using hdeg_x_S1))
      have hcol2 := reverseBfs_greedyColor_spec H k hk_pos (x :: S2)
        (List.nodup_cons.mpr ⟨hx_not_S2, hS2_nd⟩)
        (fun y hy ↦ (List.mem_cons.mp hy).elim (fun h ↦ h ▸ hC_sub x hxC)
          (fun h ↦ hCx_sub y (List.mem_filter.mp h).1)) List.mem_cons_self hxS2_full []
        (by simp) (by simp) (by simp) (by simp)
        (fun y hy _ ↦ by
          have hyC : y ∈ C := (List.mem_cons.mp hy).elim (fun h ↦ h ▸ hxC)
            (fun h ↦ (List.mem_filter.mp (List.mem_filter.mp h).1).1)
          have hsub : ((x :: S2).filter fun w ↦ H.adjBool y w).length ≤ subsetDegBool H C y := by
            rw [← List.toFinset_card_of_nodup ((List.nodup_cons.mpr ⟨hx_not_S2, hS2_nd⟩).filter _),
              subsetDegBool, ← List.toFinset_card_of_nodup (hC_nd.filter _)]
            refine Finset.card_le_card fun w hw ↦ ?_
            have hf := List.mem_filter.mp (List.mem_toFinset.mp hw)
            exact List.mem_toFinset.mpr (List.mem_filter.mpr
              ⟨(List.mem_cons.mp hf.1).elim (fun h ↦ h ▸ hxC)
                (fun h ↦ (List.mem_filter.mp (List.mem_filter.mp h).1).1), hf.2⟩)
          have := hdeg_C_le y hyC; simp only [List.filter_nil, List.length_nil, add_zero]; omega)
        (Or.inl (by simpa using hdeg_x_S2))
      obtain ⟨hnd1, hlt1, hprop1, hcov1⟩ := hcol1
      obtain ⟨hnd2, hlt2, hprop2, hcov2⟩ := hcol2
      set col1 := greedyColor H k (bfsOrder H (x :: S1) x).reverse []
      set col2 := greedyColor H k (bfsOrder H (x :: S2) x).reverse []
      set c1 := lookupColor col1 x
      set c2 := lookupColor col2 x
      have hlookup : ∀ (cols : List (ℕ × ℕ)) (hnd_c : (cols.map Prod.fst).Nodup)
          (v : ℕ) (hv : v ∈ cols.map Prod.fst), (v, lookupColor cols v) ∈ cols := by
        intro cols hnd_c v hv
        obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hv
        have hfilt_ne : (cols.filter fun q ↦ decide (q.1 = v)) ≠ [] :=
          List.ne_nil_of_mem (List.mem_filter.mpr ⟨hp, decide_eq_true_eq.mpr hpe⟩)
        have hhd_mem : ((cols.filter fun q ↦ decide (q.1 = v)).headD (0, 0)) ∈
            cols.filter fun q ↦ decide (q.1 = v) := by
          cases h : cols.filter fun q ↦ decide (q.1 = v) with
          | nil => exact (hfilt_ne h).elim
          | cons a as => simp
        have hf := List.mem_filter.mp hhd_mem
        have hEq : ((cols.filter fun q ↦ decide (q.1 = v)).headD (0, 0)).1 = v :=
          decide_eq_true_eq.mp hf.2
        have hpair : (v, lookupColor cols v) =
            (cols.filter fun q ↦ decide (q.1 = v)).headD (0, 0) :=
          Prod.ext hEq.symm rfl
        exact hpair ▸ hf.1
      have hxc1 : (x, c1) ∈ col1 :=
        hlookup col1 hnd1 x ((hcov1 x).mpr (Or.inr List.mem_cons_self))
      have hxc2 : (x, c2) ∈ col2 :=
        hlookup col2 hnd2 x ((hcov2 x).mpr (Or.inr List.mem_cons_self))
      have hc1_lt : c1 < k := hlt1 (x, c1) hxc1
      have hc2_lt : c2 < k := hlt2 (x, c2) hxc2
      have hswap_lt : ∀ c < k, swapColor c1 c2 c < k := fun c hc ↦
        swapColor_lt c1 c2 k c hc1_lt hc2_lt hc
      have hswap_inj : ∀ a b, swapColor c1 c2 a = swapColor c1 c2 b → a = b :=
        swapColor_inj c1 c2
      have hswap_c2 : swapColor c1 c2 c2 = c1 := swapColor_right c1 c2
      -- Verify the stitched coloring `col1 ++ (col2.filter (·.1 ≠ x)).map (swap c1 c2)`:
      set col2' := (col2.filter fun p ↦ decide (p.1 ≠ x)).map fun p ↦ (p.1, swapColor c1 c2 p.2)
      have hcol_eq : colorComponent H k C = col1 ++ col2' :=
        colorComponent_case2 H k C hlow hcut
      dsimp only; rw [hcol_eq]
      have hmem_col1_iff : ∀ v, v ∈ col1.map Prod.fst ↔ v = x ∨ v ∈ S1 := fun v ↦ by
        rw [hcov1 v]; simp
      have hmem_col2'_iff : ∀ v, v ∈ col2'.map Prod.fst ↔ v ∈ S2 := fun v ↦ by
        simp only [col2', List.map_map, Function.comp_def, List.mem_map, List.mem_filter,
          decide_eq_true_eq]
        constructor
        · rintro ⟨p, ⟨hp, hpx⟩, rfl⟩
          rcases List.mem_cons.mp ((hcov2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩) |>.resolve_left
              (by simp)) with h | h
          · exact (hpx h).elim
          · exact h
        · intro hv2
          obtain ⟨p, hp, rfl⟩ :=
            List.mem_map.mp ((hcov2 v).mpr (Or.inr (List.mem_cons_of_mem _ hv2)))
          exact ⟨p, ⟨hp, fun h ↦ hx_not_S2 (h ▸ hv2)⟩, rfl⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨hnd1, ?_, fun v hv1 w hv2 hEq ↦ ?_⟩
        · have hmap_eq : col2'.map Prod.fst =
          (col2.filter fun p ↦ decide (p.1 ≠ x)).map Prod.fst := by
            simp [col2', Function.comp_def]
          rw [hmap_eq]
          exact hnd2.sublist (List.filter_sublist.map Prod.fst)
        · subst hEq
          rcases (hmem_col1_iff v).mp hv1 with rfl | hvS1
          · exact hx_not_S2 ((hmem_col2'_iff x).mp hv2)
          · exact hS12_disj v hvS1 ((hmem_col2'_iff v).mp hv2)
      · intro p hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · exact hlt1 p hp1
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp2
          exact hswap_lt q.2 (hlt2 q (List.mem_filter.mp hq).1)
      · intro p hp q hq hadj
        rcases List.mem_append.mp hp with hp1 | hp2 <;> rcases List.mem_append.mp hq with hq1 | hq2
        · exact hprop1 p hp1 q hq1 hadj
        · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq2
          have hq'm := (List.mem_filter.mp hq').1
          have hq'S2 : q'.1 ∈ S2 := (hmem_col2'_iff q'.1).mp (List.mem_map.mpr
            ⟨(q'.1, swapColor c1 c2 q'.2), hq2, rfl⟩)
          rcases (hmem_col1_iff p.1).mp (List.mem_map.mpr ⟨p, hp1, rfl⟩) with hpx | hpS1
          · have hp_eq : p = (x, c1) := by
              obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp1
              obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hxc1
              have hij : i = j := by
                have h := (List.nodup_iff_injective_getElem.mp hnd1)
                  (a₁ := ⟨i, by simpa using hi⟩) (a₂ := ⟨j, by simpa using hj⟩)
                  (by simp only [List.getElem_map]; rw [hje]; exact hpx)
                exact congrArg Fin.val h
              subst hij; exact hje
            rw [hp_eq]
            intro hEq
            dsimp only at hEq
            conv at hEq => lhs; rw [← hswap_c2]
            have hq2' : q'.2 = c2 := (hswap_inj _ _ hEq).symm
            exact hprop2 (x, c2) hxc2 q' hq'm (hpx ▸ hadj) hq2'.symm
          · have := hS12_noEdge p.1 hpS1 q'.1 hq'S2
            rw [hadj] at this; exact absurd this (by decide)
        · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp2
          have hp'm := (List.mem_filter.mp hp').1
          have hp'S2 : p'.1 ∈ S2 := (hmem_col2'_iff p'.1).mp (List.mem_map.mpr
            ⟨(p'.1, swapColor c1 c2 p'.2), hp2, rfl⟩)
          rcases (hmem_col1_iff q.1).mp (List.mem_map.mpr ⟨q, hq1, rfl⟩) with hqx | hqS1
          · have hq_eq : q = (x, c1) := by
              obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq1
              obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hxc1
              have hij : i = j := by
                have h := (List.nodup_iff_injective_getElem.mp hnd1)
                  (a₁ := ⟨i, by simpa using hi⟩) (a₂ := ⟨j, by simpa using hj⟩)
                  (by simp only [List.getElem_map]; rw [hje]; exact hqx)
                exact congrArg Fin.val h
              subst hij; exact hje
            rw [hq_eq]
            intro hEq
            dsimp only at hEq
            conv at hEq => rhs; rw [← hswap_c2]
            have hp2' : p'.2 = c2 := hswap_inj _ _ hEq
            exact hprop2 p' hp'm (x, c2) hxc2 (hqx ▸ hadj) hp2'
          · have hsym : H.adjBool q.1 p'.1 = true := by
              rw [H.adjBool_eq_true_iff] at hadj ⊢; exact hadj.symm
            have := hS12_noEdge q.1 hqS1 p'.1 hp'S2
            rw [hsym] at this; exact absurd this (by decide)
        · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp2
          obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq2
          intro hEq
          exact hprop2 p' (List.mem_filter.mp hp').1 q' (List.mem_filter.mp hq').1 hadj
            (hswap_inj _ _ hEq)
      · intro v
        rw [List.map_append, List.mem_append, hmem_col1_iff v, hmem_col2'_iff v]
        constructor
        · rintro ((rfl | h1) | h2)
          · exact hxC
          · exact (List.mem_filter.mp (hS1_sub v h1)).1
          · exact (List.mem_filter.mp (List.mem_filter.mp h2).1).1
        · intro hvC
          by_cases hvx : v = x
          · exact Or.inl (Or.inl hvx)
          · have hvCx : v ∈ Cx := List.mem_filter.mpr ⟨hvC, decide_eq_true_eq.mpr hvx⟩
            by_cases hv1 : v ∈ S1
            · exact Or.inl (Or.inr hv1)
            · exact Or.inr (List.mem_filter.mpr ⟨hvCx, by simp [hv1]⟩)
    · -- **Case 3**: `C` is `k`-regular, `2`-connected, and not `K_{k+1}` → Lovász cherry!
      set cherries := (C.flatMap fun x ↦ C.flatMap fun y ↦ C.map fun z ↦ ((x, y), z)).filter
        (isLovaszCherry H C)
      -- Show `cherries ≠ []` using `exists_lovasz_cherry_abstract`!
      have hcherries_ne : cherries ≠ [] := by
        let CV := {v : {w // w ∈ H.vertices} | v.1 ∈ C}
        let GC := H.induced.induce CV
        have hcard_CV : Fintype.card CV = C.length := by
          rw [← List.toFinset_card_of_nodup hC_nd]
          refine Finset.card_bij (fun (v : CV) _ ↦ v.1.1)
            (fun v _ ↦ List.mem_toFinset.mpr v.2)
            (fun _ _ _ _ h ↦ Subtype.ext (Subtype.ext h))
            (fun x hx ↦ ⟨⟨⟨x, hC_sub x (List.mem_toFinset.mp hx)⟩, List.mem_toFinset.mp hx⟩,
              Finset.mem_univ _, rfl⟩)
        have hGC_conn : GC.Connected := by
          obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil C hC_ne
          have : Nonempty CV := ⟨⟨⟨x₀, hC_sub x₀ hx₀⟩, hx₀⟩⟩
          exact ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ hC_conn a.1 ha b.1 hb⟩
        have hGC_reg : ∀ v : CV, GC.degree v = k := by
          intro v
          rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hreg_C v.1.1 v.2]
          unfold subsetDegBool
          rw [← List.toFinset_card_of_nodup (hC_nd.filter _)]
          refine Finset.card_bij (fun (w : CV) _ ↦ w.1.1) ?_
            (fun _ _ _ _ h ↦ Subtype.ext (Subtype.ext h)) ?_
          · intro w hw
            exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨w.2,
              (H.adjBool_eq_true_iff _ _).mpr ((SimpleGraph.mem_neighborFinset GC _ _).mp hw)⟩)
          · intro w hw
            have hf := List.mem_filter.mp (List.mem_toFinset.mp hw)
            exact ⟨⟨⟨w, hC_sub w hf.1⟩, hf.1⟩, (SimpleGraph.mem_neighborFinset _ _ _).mpr
              ((H.adjBool_eq_true_iff _ _).mp hf.2), rfl⟩
        have hGC_not_compl : Fintype.card CV ≠ k + 1 := by
          rw [hcard_CV]
          intro hlen
          refine hnot_K ⟨hlen, fun x hx ↦ ?_⟩
          rw [← hdeg_C_eq x hx]; exact hreg_C x hx
        have hGC_2conn : ∀ x : CV, (GC.induce {v : CV | v ≠ x}).Connected := by
          intro x
          have hnot_cut : ¬ (bfsOrder H (C.filter fun w ↦ decide (w ≠ x.1.1))
              ((C.filter fun w ↦ decide (w ≠ x.1.1)).headD 0)).length <
              (C.filter fun w ↦ decide (w ≠ x.1.1)).length := by
            intro hlt
            have hmem : x.1.1 ∈ cutVerts := List.mem_filter.mpr ⟨x.2, decide_eq_true_eq.mpr hlt⟩
            have hne := List.ne_nil_of_mem hmem
            simp [List.isEmpty_eq_false_iff.mpr hne] at hcut
          set Cx := C.filter fun w ↦ decide (w ≠ x.1.1)
          have hCx_nd : Cx.Nodup := hC_nd.filter _
          have hCx_sub : ∀ w ∈ Cx, w ∈ H.vertices := fun w hw ↦ hC_sub w (List.mem_filter.mp hw).1
          have hCx_len : Cx.length = C.length - 1 := by
            rw [← List.toFinset_card_of_nodup hCx_nd, ← List.toFinset_card_of_nodup hC_nd,
              ← Finset.card_erase_of_mem (List.mem_toFinset.mpr x.2)]
            congr 1; ext w; simp [Cx, Finset.mem_erase, and_comm]
          have hCx_ne : Cx ≠ [] := fun h ↦ by rw [h] at hCx_len; simp at hCx_len; omega
          have ha_mem : Cx.headD 0 ∈ Cx := by
            cases h : Cx with | nil => exact (hCx_ne h).elim | cons a as => simp
          obtain ⟨hB_nd, hB_sub, _, _, _, hB_reach⟩ := bfsOrder_spec H Cx hCx_nd hCx_sub ha_mem
          have hB_len_le : (bfsOrder H Cx (Cx.headD 0)).length ≤ Cx.length := by
            rw [← List.toFinset_card_of_nodup hB_nd, ← List.toFinset_card_of_nodup hCx_nd]
            exact Finset.card_le_card fun w hw ↦ List.mem_toFinset.mpr
              (hB_sub w (List.mem_toFinset.mp hw))
          have hB_eq : ∀ w, w ∈ Cx → w ∈ bfsOrder H Cx (Cx.headD 0) := by
            intro w hw
            have hEq : (bfsOrder H Cx (Cx.headD 0)).toFinset = Cx.toFinset :=
              Finset.eq_of_subset_of_card_le
                (fun z hz ↦ List.mem_toFinset.mpr (hB_sub z (List.mem_toFinset.mp hz)))
                (by rw [List.toFinset_card_of_nodup hB_nd, List.toFinset_card_of_nodup hCx_nd]
                    omega)
            exact List.mem_toFinset.mp (hEq.symm ▸ List.mem_toFinset.mpr hw)
          have hto_root : ∀ u : {v : CV | v ≠ x},
              (GC.induce {v : CV | v ≠ x}).Reachable
                ⟨⟨⟨Cx.headD 0, hCx_sub _ ha_mem⟩, (List.mem_filter.mp ha_mem).1⟩,
                  fun h ↦ decide_eq_true_eq.mp (List.mem_filter.mp ha_mem).2
                    (congrArg (fun p : CV ↦ p.1.1) h)⟩ u := by
            intro ⟨⟨⟨u, huG⟩, huC⟩, hux⟩
            have huCx : u ∈ Cx := List.mem_filter.mpr
              ⟨huC, decide_eq_true_eq.mpr fun hEq ↦ hux (Subtype.ext (Subtype.ext hEq))⟩
            obtain ⟨q⟩ := (hB_reach u huCx).mp (hB_eq u huCx)
            have hlift : ∀ {a b : {v : {w // w ∈ H.vertices} | v.1 ∈ Cx}}
                (p : (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ Cx}).Walk a b),
                (GC.induce {v : CV | v ≠ x}).Reachable
                  ⟨⟨a.1, (List.mem_filter.mp a.2).1⟩,
                    fun h ↦ decide_eq_true_eq.mp (List.mem_filter.mp a.2).2
                      (congrArg (fun z : CV ↦ z.1.1) h)⟩
                  ⟨⟨b.1, (List.mem_filter.mp b.2).1⟩,
                    fun h ↦ decide_eq_true_eq.mp (List.mem_filter.mp b.2).2
                      (congrArg (fun z : CV ↦ z.1.1) h)⟩ := by
              intro a b p
              induction p with
              | nil => exact SimpleGraph.Reachable.refl _
              | @cons a₁ b₁ _ hadj _ ih =>
                exact (SimpleGraph.Adj.reachable (show (GC.induce {v : CV | v ≠ x}).Adj
                  ⟨⟨a₁.1, (List.mem_filter.mp a₁.2).1⟩,
                    fun h ↦ decide_eq_true_eq.mp (List.mem_filter.mp a₁.2).2
                      (congrArg (fun z : CV ↦ z.1.1) h)⟩
                  ⟨⟨b₁.1, (List.mem_filter.mp b₁.2).1⟩,
                    fun h ↦ decide_eq_true_eq.mp (List.mem_filter.mp b₁.2).2
                      (congrArg (fun z : CV ↦ z.1.1) h)⟩ from hadj)).trans ih
            exact hlift q
          have : Nonempty {v : CV | v ≠ x} :=
            ⟨⟨⟨⟨Cx.headD 0, hCx_sub _ ha_mem⟩, (List.mem_filter.mp ha_mem).1⟩,
              fun h ↦ decide_eq_true_eq.mp (List.mem_filter.mp ha_mem).2
                (congrArg (fun p : CV ↦ p.1.1) h)⟩⟩
          exact ⟨fun u v ↦ (hto_root u).symm.trans (hto_root v)⟩
        obtain ⟨x, y, z, hyz, hxy, hxz, hnayz, hrem_conn⟩ :=
          exists_lovasz_cherry_abstract GC k hk hGC_conn hGC_reg hGC_not_compl hGC_2conn
        -- Show `((x.1.1, y.1.1), z.1.1) ∈ cherries`!
        have hmem_triples : ((x.1.1, y.1.1), z.1.1) ∈
            C.flatMap fun a ↦ C.flatMap fun b ↦ C.map fun c ↦ ((a, b), c) :=
          List.mem_flatMap.mpr ⟨x.1.1, x.2, List.mem_flatMap.mpr ⟨y.1.1, y.2,
            List.mem_map.mpr ⟨z.1.1, z.2, rfl⟩⟩⟩
        have his : isLovaszCherry H C ((x.1.1, y.1.1), z.1.1) = true := by
          unfold isLovaszCherry
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
          refine ⟨⟨⟨⟨(H.adjBool_eq_true_iff _ _).mpr hxy, (H.adjBool_eq_true_iff _ _).mpr hxz⟩,
            Bool.eq_false_iff.mpr fun h ↦ hnayz ((H.adjBool_eq_true_iff _ _).mp h)⟩,
            fun hEq ↦ hyz (Subtype.ext (Subtype.ext hEq))⟩, ?_⟩
          set rem := C.filter fun w ↦ decide (w ≠ y.1.1) && decide (w ≠ z.1.1)
          have hrem_nd : rem.Nodup := hC_nd.filter _
          have hrem_sub : ∀ w ∈ rem, w ∈ H.vertices := fun w hw ↦ hC_sub w (List.mem_filter.mp hw).1
          have hx_rem : x.1.1 ∈ rem := List.mem_filter.mpr ⟨x.2, (Bool.and_eq_true _ _).mpr
            ⟨decide_eq_true_eq.mpr fun h ↦ GC.ne_of_adj hxy (Subtype.ext (Subtype.ext h)),
             decide_eq_true_eq.mpr fun h ↦ GC.ne_of_adj hxz (Subtype.ext (Subtype.ext h))⟩⟩
          obtain ⟨hB_nd, hB_sub, _, _, _, hB_reach⟩ := bfsOrder_spec H rem hrem_nd hrem_sub hx_rem
          rw [← List.toFinset_card_of_nodup hB_nd, ← List.toFinset_card_of_nodup hrem_nd]
          congr 1; ext w; simp only [List.mem_toFinset]
          refine ⟨hB_sub w, fun hw ↦ (hB_reach w hw).mpr ?_⟩
          have hwf := List.mem_filter.mp hw
          have hwyz := (Bool.and_eq_true _ _).mp hwf.2
          have hw_ne_y : (⟨⟨w, hC_sub w hwf.1⟩, hwf.1⟩ : CV) ≠ y :=
            fun h ↦ decide_eq_true_eq.mp hwyz.1 (congrArg (fun p : CV ↦ p.1.1) h)
          have hw_ne_z : (⟨⟨w, hC_sub w hwf.1⟩, hwf.1⟩ : CV) ≠ z :=
            fun h ↦ decide_eq_true_eq.mp hwyz.2 (congrArg (fun p : CV ↦ p.1.1) h)
          have hx_ne_y : x ≠ y := GC.ne_of_adj hxy
          have hx_ne_z : x ≠ z := GC.ne_of_adj hxz
          obtain ⟨q⟩ := hrem_conn ⟨x, hx_ne_y, hx_ne_z⟩ ⟨⟨⟨w, hC_sub w hwf.1⟩, hwf.1⟩, hw_ne_y,
            hw_ne_z⟩
          have hlift : ∀ {a b : {v : CV | v ≠ y ∧ v ≠ z}}
              (p : (GC.induce {v : CV | v ≠ y ∧ v ≠ z}).Walk a b),
              (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ rem}).Reachable
                ⟨a.1.1, List.mem_filter.mpr ⟨a.1.2, (Bool.and_eq_true _ _).mpr
                  ⟨decide_eq_true_eq.mpr fun h ↦ a.2.1 (Subtype.ext (Subtype.ext h)),
                   decide_eq_true_eq.mpr fun h ↦ a.2.2 (Subtype.ext (Subtype.ext h))⟩⟩⟩
                ⟨b.1.1, List.mem_filter.mpr ⟨b.1.2, (Bool.and_eq_true _ _).mpr
                  ⟨decide_eq_true_eq.mpr fun h ↦ b.2.1 (Subtype.ext (Subtype.ext h)),
                   decide_eq_true_eq.mpr fun h ↦ b.2.2 (Subtype.ext (Subtype.ext h))⟩⟩⟩ := by
            intro a b p
            induction p with
            | nil => exact SimpleGraph.Reachable.refl _
            | @cons a₁ b₁ _ hadj _ ih =>
              exact (SimpleGraph.Adj.reachable
                (show (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ rem}).Adj
                  ⟨a₁.1.1, List.mem_filter.mpr ⟨a₁.1.2, (Bool.and_eq_true _ _).mpr
                    ⟨decide_eq_true_eq.mpr fun h ↦ a₁.2.1 (Subtype.ext (Subtype.ext h)),
                     decide_eq_true_eq.mpr fun h ↦ a₁.2.2 (Subtype.ext (Subtype.ext h))⟩⟩⟩
                  ⟨b₁.1.1, List.mem_filter.mpr ⟨b₁.1.2, (Bool.and_eq_true _ _).mpr
                    ⟨decide_eq_true_eq.mpr fun h ↦ b₁.2.1 (Subtype.ext (Subtype.ext h)),
                     decide_eq_true_eq.mpr fun h ↦ b₁.2.2 (Subtype.ext (Subtype.ext h))⟩⟩⟩
                  from hadj)).trans ih
          exact hlift q
        exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hmem_triples, his⟩)
      have hch_true : (!cherries.isEmpty) = true := by
        simp [List.isEmpty_eq_false_iff.mpr hcherries_ne]
      have ht_mem : cherries.headD ((0, 0), 0) ∈ cherries := by
        cases h : cherries with | nil => exact (hcherries_ne h).elim | cons a as => simp
      set t := cherries.headD ((0, 0), 0)
      set x := t.1.1; set y := t.1.2; set z := t.2
      have htf := List.mem_filter.mp ht_mem
      obtain ⟨_, hxC, hm1⟩ := List.mem_flatMap.mp htf.1
      obtain ⟨_, hyC, hm2⟩ := List.mem_flatMap.mp hm1
      obtain ⟨_, hzC, ht_eq⟩ := List.mem_map.mp hm2
      have hxC' : x ∈ C := by simpa [x, ← ht_eq] using hxC
      have hyC' : y ∈ C := by simpa [y, ← ht_eq] using hyC
      have hzC' : z ∈ C := by simpa [z, ← ht_eq] using hzC
      have his := htf.2; unfold isLovaszCherry at his
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at his
      obtain ⟨⟨⟨⟨hxy, hxz⟩, hnayz⟩, hyz⟩, hbfs_rem⟩ := his
      set rem := C.filter fun w ↦ decide (w ≠ y) && decide (w ≠ z)
      have hrem_nd : rem.Nodup := hC_nd.filter _
      have hrem_sub : ∀ w ∈ rem, w ∈ H.vertices := fun w hw ↦ hC_sub w (List.mem_filter.mp hw).1
      have hx_rem : x ∈ rem := List.mem_filter.mpr ⟨hxC', (Bool.and_eq_true _ _).mpr
        ⟨decide_eq_true_eq.mpr fun h ↦
          H.toSimpleGraph.ne_of_adj ((H.adjBool_eq_true_iff _ _).mp hxy) h,
         decide_eq_true_eq.mpr fun h ↦
          H.toSimpleGraph.ne_of_adj ((H.adjBool_eq_true_iff _ _).mp hxz) h⟩⟩
      have hinit_nd : (([(y, 0), (z, 0)] : List (ℕ × ℕ)).map Prod.fst).Nodup := by
        simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
          List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
        exact hyz
      have hinit_lt : ∀ p ∈ ([(y, 0), (z, 0)] : List (ℕ × ℕ)), p.2 < k := fun p hp ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> omega
      have hinit_prop : ∀ p ∈ ([(y, 0), (z, 0)] : List (ℕ × ℕ)),
          ∀ q ∈ ([(y, 0), (z, 0)] : List (ℕ × ℕ)), H.adjBool p.1 q.1 = true → p.2 ≠ q.2 := by
        intro p hp q hq hadj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
        · exfalso; exact H.toSimpleGraph.ne_of_adj ((H.adjBool_eq_true_iff _ _).mp hadj) rfl
        · rw [hnayz] at hadj; exact absurd hadj (by decide)
        · have := (H.adjBool_eq_true_iff _ _).mp hadj
          have h2 : H.adjBool y z = true := (H.adjBool_eq_true_iff _ _).mpr this.symm
          rw [hnayz] at h2; exact absurd h2 (by decide)
        · exfalso; exact H.toSimpleGraph.ne_of_adj ((H.adjBool_eq_true_iff _ _).mp hadj) rfl
      have hdisj : ∀ w ∈ rem, w ∉ ([(y, 0), (z, 0)] : List (ℕ × ℕ)).map Prod.fst := by
        intro w hw hm
        have hwyz := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hw).2
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact decide_eq_true_eq.mp hwyz.1 rfl
        · exact decide_eq_true_eq.mp hwyz.2 rfl
      have hdeg_sum : ∀ w ∈ rem,
          (rem.filter fun u ↦ H.adjBool w u).length +
            (([(y, 0), (z, 0)] : List (ℕ × ℕ)).filter fun p ↦ H.adjBool w p.1).length ≤ k := by
        intro w hw
        have hwC : w ∈ C := (List.mem_filter.mp hw).1
        rw [← List.toFinset_card_of_nodup (hrem_nd.filter _),
          ← List.toFinset_card_of_nodup ((hinit_nd.of_map _).filter _)]
        have hcard_init : (([(y, 0), (z, 0)] : List (ℕ × ℕ)).filter fun p ↦
            H.adjBool w p.1).toFinset.card =
            ((([(y, 0), (z, 0)] : List (ℕ × ℕ)).filter fun p ↦
              H.adjBool w p.1).map Prod.fst).toFinset.card := by
          rw [List.toFinset_card_of_nodup ((hinit_nd.of_map _).filter _),
            List.toFinset_card_of_nodup (hinit_nd.sublist (List.filter_sublist.map Prod.fst)),
            List.length_map]
        rw [hcard_init, ← Finset.card_union_of_disjoint]
        · have hsub : (rem.filter fun u ↦ H.adjBool w u).toFinset ∪
              (((([(y, 0), (z, 0)] : List (ℕ × ℕ)).filter fun p ↦
                H.adjBool w p.1).map Prod.fst).toFinset) ⊆
              (C.filter fun u ↦ H.adjBool w u).toFinset := by
            intro u hu
            rcases Finset.mem_union.mp hu with h1 | h2
            · have hf := List.mem_filter.mp (List.mem_toFinset.mp h1)
              exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨(List.mem_filter.mp hf.1).1, hf.2⟩)
            · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h2)
              have hf := List.mem_filter.mp hp
              have hpC : p.1 ∈ C := by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
                rcases hf.1 with rfl | rfl <;> assumption
              exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hpC, hf.2⟩)
          calc _ ≤ (C.filter fun u ↦ H.adjBool w u).toFinset.card := Finset.card_le_card hsub
            _ = subsetDegBool H C w := List.toFinset_card_of_nodup (hC_nd.filter _)
            _ = k := hreg_C w hwC
        · rw [Finset.disjoint_left]
          intro u hu1 hu2
          have h1 := (List.mem_filter.mp (List.mem_toFinset.mp hu1)).1
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hu2)
          exact hdisj p.1 h1 (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩)
      have hres := reverseBfs_greedyColor_spec H k hk_pos rem hrem_nd hrem_sub hx_rem hbfs_rem
        [(y, 0), (z, 0)] hinit_nd hinit_lt hinit_prop hdisj (fun w hw _ ↦ hdeg_sum w hw)
        (Or.inr ⟨hdeg_sum x hx_rem, (y, 0), List.mem_cons_self,
          (z, 0), List.mem_cons_of_mem _ List.mem_cons_self, hyz, hxy, hxz, rfl⟩)
      have hcol_eq : colorComponent H k C =
          greedyColor H k (bfsOrder H rem x).reverse [(y, 0), (z, 0)] :=
        colorComponent_case3 H k C hlow hcut hch_true
      dsimp only; rw [hcol_eq]
      refine ⟨hres.1, hres.2.1, hres.2.2.1, fun v ↦ ?_⟩
      rw [hres.2.2.2 v]
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        rem, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ((rfl | rfl) | ⟨hvC, _⟩) <;> assumption
      · intro hvC
        by_cases hvy : v = y
        · exact Or.inl (Or.inl hvy)
        · by_cases hvz : v = z
          · exact Or.inl (Or.inr hvz)
          · exact Or.inr ⟨hvC, hvy, hvz⟩

/-- **Constructive Polynomial-Time Brooks' Theorem**: for every graph `H`, every `k ≥ 3` with
`Δ(H) ≤ k`, if `H` has no `K_{k+1}` connected component (`hasCompleteCompBool H k = false`), then
`brooksColoring H k` is a valid partition of `H.vertices` into at most `k` nonempty independent
sets of `H`. -/
theorem brooksColoring_spec (H : Graph) (k : ℕ) (hk : 3 ≤ k)
    (hΔ : ∀ v : {w // w ∈ H.vertices}, H.induced.degree v ≤ k)
    (hnoK : hasCompleteCompBool H k = false) :
    let parts := brooksColoring H k
    (∀ part ∈ parts, part ≠ [] ∧ part.Nodup ∧ (∀ v ∈ part, v ∈ H.vertices) ∧
      ∀ u ∈ part, ∀ v ∈ part, H.adjBool u v = false) ∧
    parts.Pairwise (fun a b ↦ ∀ v ∈ a, v ∉ b) ∧
    (∀ v ∈ H.vertices, ∃ part ∈ parts, v ∈ part) ∧
    parts.length ≤ k := by
  classical
  set V := H.distinctVertices
  set comps := canonicalComponents H
  -- Step 1: Properties of `canonicalComponents H`:
  have hcomp_spec :
      (∀ C ∈ comps, ∃ (hC_sub : ∀ x ∈ C, x ∈ H.vertices), C ≠ [] ∧ C.Nodup ∧
        (∀ x ∈ C, ∀ w ∈ H.vertices, H.adjBool x w = true → w ∈ C) ∧
        (∀ x (hx : x ∈ C) y (hy : y ∈ C),
          (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ C}).Reachable
            ⟨⟨x, hC_sub x hx⟩, hx⟩ ⟨⟨y, hC_sub y hy⟩, hy⟩) ∧
        ¬ (C.length = k + 1 ∧ ∀ x ∈ C, subsetDegBool H V x = k)) ∧
      (∀ v ∈ H.vertices, ∃ C ∈ comps, v ∈ C) ∧
      comps.Pairwise (fun a b ↦ ∀ x ∈ a, x ∉ b) := by
    have hitem : ∀ C ∈ comps, ∃ (hC_sub : ∀ x ∈ C, x ∈ H.vertices), C ≠ [] ∧ C.Nodup ∧
        (∀ x ∈ C, ∀ w ∈ H.vertices, H.adjBool x w = true → w ∈ C) ∧
        (∀ x (hx : x ∈ C) y (hy : y ∈ C),
          (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ C}).Reachable
            ⟨⟨x, hC_sub x hx⟩, hx⟩ ⟨⟨y, hC_sub y hy⟩, hy⟩) ∧
        ¬ (C.length = k + 1 ∧ ∀ x ∈ C, subsetDegBool H V x = k) := by
      intro C hC
      obtain ⟨u, huV, hCu⟩ := List.mem_flatMap.mp hC
      dsimp only at hCu
      split_ifs at hCu with hmin
      · rw [List.mem_singleton] at hCu; subst hCu
        obtain ⟨hB_nd, hB_sub, hu_B, _, hB_cl, hB_reach⟩ :=
          bfsOrder_spec H V H.nodup_distinctVertices (fun y hy ↦ H.mem_distinctVertices.mp hy) huV
        have hB_subG : ∀ x ∈ bfsOrder H V u, x ∈ H.vertices := fun x hx ↦
          H.mem_distinctVertices.mp (hB_sub x hx)
        have hB_clG : ∀ x ∈ bfsOrder H V u, ∀ w ∈ H.vertices, H.adjBool x w = true →
            w ∈ bfsOrder H V u := fun x hx w hw ↦ hB_cl x hx w (H.mem_distinctVertices.mpr hw)
        refine ⟨hB_subG, List.ne_nil_of_mem hu_B, hB_nd, hB_clG, ?_, ?_⟩
        · -- Reachability inside `C`:
          intro x hx y hy
          have hlift : ∀ z (hz : z ∈ bfsOrder H V u),
              (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ bfsOrder H V u}).Reachable
                ⟨⟨u, hB_subG u hu_B⟩, hu_B⟩ ⟨⟨z, hB_subG z hz⟩, hz⟩ := by
            intro z hz
            obtain ⟨q⟩ := (hB_reach z (hB_sub z hz)).mp hz
            -- Every vertex on a walk from `u` in `H[V]` stays in `bfsOrder H V u`!
            suffices ∀ {a b : {v : {w // w ∈ H.vertices} | v.1 ∈ V}}
                (p : (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ V}).Walk a b),
                ∀ (ha : a.1.1 ∈ bfsOrder H V u) (hb : b.1.1 ∈ bfsOrder H V u),
                (H.induced.induce {v : {w // w ∈ H.vertices} | v.1 ∈ bfsOrder H V u}).Reachable
                  ⟨a.1, ha⟩ ⟨b.1, hb⟩ from this q hu_B hz
            intro a b p
            induction p with
            | nil => intro _ _; exact SimpleGraph.Reachable.refl _
            | @cons a₁ b₁ _ hadj _ ih =>
              intro ha hb
              have hb1 : b₁.1.1 ∈ bfsOrder H V u :=
                hB_cl a₁.1.1 ha b₁.1.1 b₁.2 ((H.adjBool_eq_true_iff _ _).mpr hadj)
              exact (SimpleGraph.Adj.reachable
                (show (H.induced.induce
                    {v : {w // w ∈ H.vertices} | v.1 ∈ bfsOrder H V u}).Adj
                  ⟨a₁.1, ha⟩ ⟨b₁.1, hb1⟩ from hadj)).trans (ih hb1 hb)
          exact (hlift x hx).symm.trans (hlift y hy)
        · intro hK
          have htrue : hasCompleteCompBool H k = true :=
            (hasCompleteCompBool_eq_true_iff H k).mpr ⟨⟨u, H.mem_distinctVertices.mp huV⟩, hK⟩
          rw [htrue] at hnoK; exact absurd hnoK (by decide)
      · cases hCu
    have hcov : ∀ v ∈ H.vertices, ∃ C ∈ comps, v ∈ C := by
      intro v hv
      have hvV : v ∈ V := H.mem_distinctVertices.mpr hv
      obtain ⟨hB_nd, hB_sub, hv_B, _, hB_cl, hB_reach⟩ :=
        bfsOrder_spec H V H.nodup_distinctVertices (fun y hy ↦ H.mem_distinctVertices.mp hy) hvV
      set Bv := bfsOrder H V v
      obtain ⟨u₀, hu₀, hmin⟩ := Finset.exists_min_image Bv.toFinset id
        ⟨v, List.mem_toFinset.mpr hv_B⟩
      have hu₀B : u₀ ∈ Bv := List.mem_toFinset.mp hu₀
      have hu₀V : u₀ ∈ V := hB_sub u₀ hu₀B
      -- `bfsOrder H V u₀` has the EXACT same elements as `Bv`!
      obtain ⟨hB0_nd, hB0_sub, hu₀_B0, _, hB0_cl, hB0_reach⟩ :=
        bfsOrder_spec H V H.nodup_distinctVertices (fun y hy ↦ H.mem_distinctVertices.mp hy) hu₀V
      have hsame : ∀ x, x ∈ bfsOrder H V u₀ ↔ x ∈ Bv := fun x ↦ by
        constructor
        · intro hx0
          have hxV := hB0_sub x hx0
          exact (hB_reach x hxV).mpr (((hB_reach u₀ hu₀V).mp hu₀B).trans
            ((hB0_reach x hxV).mp hx0))
        · intro hxv
          have hxV := hB_sub x hxv
          exact (hB0_reach x hxV).mpr (((hB_reach u₀ hu₀V).mp hu₀B).symm.trans
            ((hB_reach x hxV).mp hxv))
      have hC_mem : bfsOrder H V u₀ ∈ comps := by
        unfold comps canonicalComponents
        refine List.mem_flatMap.mpr ⟨u₀, hu₀V, ?_⟩
        have hall : (bfsOrder H V u₀).all (fun x ↦ decide (u₀ ≤ x)) = true :=
          List.all_eq_true.mpr fun x hx ↦ decide_eq_true_eq.mpr
            (hmin x (List.mem_toFinset.mpr ((hsame x).mp hx)))
        dsimp only [V] at hall ⊢
        simp only [hall, ↓reduceIte, List.mem_singleton]
      exact ⟨bfsOrder H V u₀, hC_mem, (hsame v).mpr hv_B⟩
    have hpair : comps.Pairwise (fun a b ↦ ∀ x ∈ a, x ∉ b) := by
      have hnd_comps : comps.Nodup := by
        unfold comps canonicalComponents
        refine List.nodup_flatMap.mpr ⟨fun u _ ↦ by dsimp only; split_ifs <;> simp, ?_⟩
        refine List.Pairwise.imp_of_mem (fun {u₁ u₂} hu₁ hu₂ hne C hC1 hC2 ↦ ?_)
          H.nodup_distinctVertices
        dsimp only at hC1 hC2
        split_ifs at hC1 with hm1
        · split_ifs at hC2 with hm2
          · rw [List.mem_singleton] at hC1 hC2
            have hu1_in : u₁ ∈ C := hC1 ▸ (bfsOrder_spec H V H.nodup_distinctVertices
              (fun y hy ↦ H.mem_distinctVertices.mp hy) hu₁).2.2.1
            have hu2_in : u₂ ∈ C := hC2 ▸ (bfsOrder_spec H V H.nodup_distinctVertices
              (fun y hy ↦ H.mem_distinctVertices.mp hy) hu₂).2.2.1
            have h1 := decide_eq_true_eq.mp (List.all_eq_true.mp hm1 u₂ (hC1 ▸ hu2_in))
            have h2 := decide_eq_true_eq.mp (List.all_eq_true.mp hm2 u₁ (hC2 ▸ hu1_in))
            exact hne (Nat.le_antisymm h1 h2)
          · cases hC2
        · cases hC1
      refine hnd_comps.pairwise_of_forall_ne fun C₁ hC₁ C₂ hC₂ hne x hx1 hx2 ↦ ?_
      obtain ⟨u₁, hu₁V, hCu₁⟩ := List.mem_flatMap.mp hC₁
      obtain ⟨u₂, hu₂V, hCu₂⟩ := List.mem_flatMap.mp hC₂
      dsimp only at hCu₁ hCu₂
      split_ifs at hCu₁ with hm1
      · split_ifs at hCu₂ with hm2
        · rw [List.mem_singleton] at hCu₁ hCu₂; subst hCu₁ hCu₂
          obtain ⟨_, hB1_sub, hu1_B, _, _, hB1_r⟩ := bfsOrder_spec H V H.nodup_distinctVertices
            (fun y hy ↦ H.mem_distinctVertices.mp hy) hu₁V
          obtain ⟨_, hB2_sub, hu2_B, _, _, hB2_r⟩ := bfsOrder_spec H V H.nodup_distinctVertices
            (fun y hy ↦ H.mem_distinctVertices.mp hy) hu₂V
          have hxV := hB1_sub x hx1
          have hr12 := ((hB1_r x hxV).mp hx1).trans ((hB2_r x hxV).mp hx2).symm
          have hu2_in : u₂ ∈ bfsOrder H V u₁ := (hB1_r u₂ hu₂V).mpr hr12
          have hu1_in : u₁ ∈ bfsOrder H V u₂ := (hB2_r u₁ hu₁V).mpr hr12.symm
          have hle1 := decide_eq_true_eq.mp (List.all_eq_true.mp hm1 u₂ hu2_in)
          have hle2 := decide_eq_true_eq.mp (List.all_eq_true.mp hm2 u₁ hu1_in)
          have hu_eq : u₁ = u₂ := Nat.le_antisymm hle1 hle2
          exact hne (hu_eq ▸ rfl)
        · cases hCu₂
      · cases hCu₁
    exact ⟨hitem, hcov, hpair⟩
  obtain ⟨hcomp_item, hcomp_cov, hcomp_pair⟩ := hcomp_spec
  -- Step 2: Combine per-component colorings into `allCols`!
  set allCols := comps.flatMap (colorComponent H k)
  have hall_nd_clean : (allCols.map Prod.fst).Nodup := by
    rw [List.map_flatMap, List.nodup_flatMap]
    refine ⟨fun C hC ↦ ?_, ?_⟩
    · obtain ⟨h3, h1, h2, h4, h5, h6⟩ := hcomp_item C hC
      exact (colorComponent_spec H k hk C h1 h2 h3 h4 h5 hΔ h6).1
    · have hpw : comps.Pairwise (fun C₁ C₂ ↦
          ∀ v ∈ (colorComponent H k C₁).map Prod.fst,
            v ∉ (colorComponent H k C₂).map Prod.fst) := by
        refine List.Pairwise.imp_of_mem (fun {C₁ C₂} hC₁ hC₂ hdisj v hv1 hv2 ↦ ?_) hcomp_pair
        obtain ⟨h3, h1, h2, h4, h5, h6⟩ := hcomp_item C₁ hC₁
        obtain ⟨g3, g1, g2, g4, g5, g6⟩ := hcomp_item C₂ hC₂
        exact hdisj v ((colorComponent_spec H k hk C₁ h1 h2 h3 h4 h5 hΔ h6).2.2.2 v |>.mp hv1)
          ((colorComponent_spec H k hk C₂ g1 g2 g3 g4 g5 hΔ g6).2.2.2 v |>.mp hv2)
      exact hpw
  have hall_lt : ∀ p ∈ allCols, p.2 < k := by
    intro p hp
    obtain ⟨C, hC, hpC⟩ := List.mem_flatMap.mp hp
    obtain ⟨h3, h1, h2, h4, h5, h6⟩ := hcomp_item C hC
    exact (colorComponent_spec H k hk C h1 h2 h3 h4 h5 hΔ h6).2.1 p hpC
  have hall_prop : ∀ p ∈ allCols, ∀ q ∈ allCols, H.adjBool p.1 q.1 = true → p.2 ≠ q.2 := by
    intro p hp q hq hadj
    obtain ⟨C₁, hC₁, hpC⟩ := List.mem_flatMap.mp hp
    obtain ⟨C₂, hC₂, hqC⟩ := List.mem_flatMap.mp hq
    obtain ⟨h3, h1, h2, h4, h5, h6⟩ := hcomp_item C₁ hC₁
    obtain ⟨g3, g1, g2, g4, g5, g6⟩ := hcomp_item C₂ hC₂
    have hp1 := (colorComponent_spec H k hk C₁ h1 h2 h3 h4 h5 hΔ h6).2.2.2 p.1 |>.mp
      (List.mem_map.mpr ⟨p, hpC, rfl⟩)
    have hq2 := (colorComponent_spec H k hk C₂ g1 g2 g3 g4 g5 hΔ g6).2.2.2 q.1 |>.mp
      (List.mem_map.mpr ⟨q, hqC, rfl⟩)
    have hCeq : C₁ = C₂ := by
      by_contra hne
      have hdisj : ∀ (cs : List (List ℕ)), cs.Pairwise (fun a b ↦ ∀ x ∈ a, x ∉ b) →
          C₁ ∈ cs → C₂ ∈ cs → ∀ x ∈ C₁, x ∉ C₂ := by
        intro cs hpw h1' h2'
        induction cs with
        | nil => cases h1'
        | cons a as ih =>
          rw [List.pairwise_cons] at hpw
          rcases List.mem_cons.mp h1' with rfl | h1'' <;>
          rcases List.mem_cons.mp h2' with rfl | h2''
          · exact (hne rfl).elim
          · exact hpw.1 C₂ h2''
          · exact fun x hx1 hx2 ↦ hpw.1 C₁ h1'' x hx2 hx1
          · exact ih hpw.2 h1'' h2''
      exact hdisj comps hcomp_pair hC₁ hC₂ q.1 (h4 p.1 hp1 q.1 (g3 q.1 hq2) hadj) hq2
    subst hCeq
    exact (colorComponent_spec H k hk C₁ h1 h2 h3 h4 h5 hΔ h6).2.2.1 p hpC q hqC hadj
  have hall_cov : ∀ v, v ∈ allCols.map Prod.fst ↔ v ∈ H.vertices := fun v ↦ by
    constructor
    · intro hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      obtain ⟨C, hC, hpC⟩ := List.mem_flatMap.mp hp
      obtain ⟨h3, h1, h2, h4, h5, h6⟩ := hcomp_item C hC
      exact h3 p.1 ((colorComponent_spec H k hk C h1 h2 h3 h4 h5 hΔ h6).2.2.2 p.1 |>.mp
        (List.mem_map.mpr ⟨p, hpC, rfl⟩))
    · intro hv
      obtain ⟨C, hC, hvC⟩ := hcomp_cov v hv
      obtain ⟨h3, h1, h2, h4, h5, h6⟩ := hcomp_item C hC
      obtain ⟨p, hpC, rfl⟩ := List.mem_map.mp
        ((colorComponent_spec H k hk C h1 h2 h3 h4 h5 hΔ h6).2.2.2 v |>.mpr hvC)
      exact List.mem_map.mpr ⟨p, List.mem_flatMap.mpr ⟨C, hC, hpC⟩, rfl⟩
  -- Step 3: Deduce validity of `colorClasses k allCols`:
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro part hp
    simp only [brooksColoring, colorClasses, List.mem_filter, List.mem_map, List.mem_range] at hp
    obtain ⟨⟨c, _, rfl⟩, hne⟩ := hp
    refine ⟨List.isEmpty_eq_false_iff.mp (by simpa using hne), ?_, ?_, ?_⟩
    · exact hall_nd_clean.sublist (List.filter_sublist.map Prod.fst)
    · intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      exact (hall_cov p.1).mp (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩)
    · intro u hu v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      have hpf := List.mem_filter.mp hp; have hqf := List.mem_filter.mp hq
      exact Bool.eq_false_iff.mpr fun hadj ↦
        hall_prop p hpf.1 q hqf.1 hadj
          ((decide_eq_true_eq.mp hpf.2).trans (decide_eq_true_eq.mp hqf.2).symm)
  · simp only [brooksColoring, colorClasses]
    refine List.Pairwise.filter _ ?_
    refine (List.nodup_range.pairwise_of_forall_ne fun c₁ _ c₂ _ hne ↦ hne).map _ ?_
    intro c₁ c₂ hne v hv₁ hv₂
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv₁
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hv₂
    have hpf := List.mem_filter.mp hp; have hqf := List.mem_filter.mp hq
    have hpq : p = q := by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hpf.1
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hqf.1
      have hij : i = j := by
        have h := (List.nodup_iff_injective_getElem.mp hall_nd_clean)
          (a₁ := ⟨i, by rw [List.length_map]; exact hi⟩)
          (a₂ := ⟨j, by rw [List.length_map]; exact hj⟩)
          (by simpa [allCols] using hqp.symm)
        exact congrArg Fin.val h
      subst hij; rfl
    subst hpq
    exact hne ((decide_eq_true_eq.mp hpf.2).symm.trans (decide_eq_true_eq.mp hqf.2))
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((hall_cov v).mpr hv)
    refine ⟨(allCols.filter fun q ↦ decide (q.2 = p.2)).map Prod.fst, ?_,
      List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, decide_eq_true_eq.mpr rfl⟩, rfl⟩⟩
    simp only [brooksColoring, colorClasses, List.mem_filter, List.mem_map, List.mem_range]
    refine ⟨⟨p.2, hall_lt p hp, rfl⟩, ?_⟩
    have hne : ((allCols.filter fun q ↦ decide (q.2 = p.2)).map Prod.fst) ≠ [] :=
      List.ne_nil_of_mem (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, decide_eq_true_eq.mpr rfl⟩,
        rfl⟩)
    simp [List.isEmpty_eq_false_iff.mpr hne]
  · calc (brooksColoring H k).length
        ≤ ((List.range k).map fun c ↦ (allCols.filter fun p ↦ decide (p.2 =
          c)).map Prod.fst).length :=
          List.length_filter_le _ _
      _ = k := by simp

end Cslib.Complexity
