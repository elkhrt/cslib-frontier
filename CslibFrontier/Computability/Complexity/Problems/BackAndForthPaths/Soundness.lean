/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.BackAndForthPaths.Basic
public import CslibFrontier.Computability.Complexity.Problems.BackAndForthPaths.Switch

import Mathlib.Data.List.GetD

/-!
# Soundness of the Fortune–Hopcroft–Wyllie Switch Reduction

This module proves the soundness direction (`sound_of_paths`) of the 14-vertex interlocking switch
reduction from `SAT` to `BFP` under standard Lean axioms.
-/

public section

namespace Cslib.Complexity.BackAndForthPaths

open Cslib.Complexity Cslib.Logic.PL

private lemma some_ne_some {α : Type*} {a b : α} (h : a ≠ b) : some a ≠ some b :=
  fun heq ↦ h (Option.some.inj heq)

theorem sound_of_paths {φ : CNF ℕ} {P₁ P₂ : List ℕ}
    (hP₁ : IsDirPath (toBFP φ).graph s1Node t1Node P₁)
    (hP₂ : IsDirPath (toBFP φ).graph s2Node t2Node P₂)
    (hdisj : ∀ v, v ∈ P₁ → v ∈ P₂ → False) :
    φ ∈ SAT := by
  set K := (litList φ).length
  have hlock_step : ∀ k < K, swNode k swA ∈ P₁ → swNode k swB ∈ P₂ →
      ((IsAdjInList P₁ (swNode k swX) (swNode k swU) ∧
        swNode k swC ∈ P₁ ∧ swNode k swX ∈ P₁ ∧ swNode k swU ∈ P₁ ∧
        swNode k swB ∈ P₂ ∧ swNode k swV ∈ P₂ ∧ swNode k swX2 ∈ P₂ ∧ swNode k swD ∈ P₂) ∨
       (IsAdjInList P₁ (swNode k swY) (swNode k swV) ∧
        swNode k swC ∈ P₁ ∧ swNode k swY ∈ P₁ ∧ swNode k swV ∈ P₁ ∧
        swNode k swB ∈ P₂ ∧ swNode k swU ∈ P₂ ∧ swNode k swY2 ∈ P₂ ∧ swNode k swD ∈ P₂)) := by
    intro k _ hA hB
    obtain ⟨u, huA_adj, huA⟩ := exists_pred_in_path hP₁.2.2.2.2 hA (by
      rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term k swA).1.symm)
    obtain ⟨v, hBv_adj, hBv⟩ := exists_succ_in_path hP₂.2.2.2.2 hB (by
      rw [hP₂.2.2.2.1]; exact some_ne_some (swNode_ne_term k swB).2.2.2.symm)
    have hu := isAdjInList_mem_left huA_adj
    have hv := isAdjInList_mem_right hBv_adj
    rcases in_swA huA with rfl | rfl <;> rcases out_swB hBv with rfl | rfl
    · exact absurd hv (hdisj _ hu)
    · obtain ⟨x, hxU_adj, hxU⟩ := exists_pred_in_path hP₁.2.2.2.2 hu (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term k swU).1.symm)
      have hx_eq : x = swNode k swX := (in_swU hxU).resolve_left fun heq ↦
        hdisj _ (heq ▸ isAdjInList_mem_left hxU_adj) hB
      subst hx_eq
      have hx := isAdjInList_mem_left hxU_adj
      obtain ⟨x2, hVx2_adj, hVx2⟩ := exists_succ_in_path hP₂.2.2.2.2 hv (by
        rw [hP₂.2.2.2.1]; exact some_ne_some (swNode_ne_term k swV).2.2.2.symm)
      have hx2_eq : x2 = swNode k swX2 := (out_swV hVx2).resolve_right fun heq ↦
        hdisj _ hA (heq ▸ isAdjInList_mem_right hVx2_adj)
      subst hx2_eq
      have hx2 := isAdjInList_mem_right hVx2_adj
      obtain ⟨c, hcX_adj, hcX⟩ := exists_pred_in_path hP₁.2.2.2.2 hx (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term k swX).1.symm)
      have hc_eq : c = swNode k swC := (in_swX hcX).resolve_right fun heq ↦
        hdisj _ (heq ▸ isAdjInList_mem_left hcX_adj) hx2
      obtain ⟨d, hX2d_adj, hX2d⟩ := exists_succ_in_path hP₂.2.2.2.2 hx2 (by
        rw [hP₂.2.2.2.1]; exact some_ne_some (swNode_ne_term k swX2).2.2.2.symm)
      have hd_eq : d = swNode k swD := (out_swX2 hX2d).resolve_left fun heq ↦
        hdisj _ hx (heq ▸ isAdjInList_mem_right hX2d_adj)
      exact Or.inl ⟨hxU_adj, hc_eq ▸ isAdjInList_mem_left hcX_adj, hx, hu,
        hB, hv, hx2, hd_eq ▸ isAdjInList_mem_right hX2d_adj⟩
    · obtain ⟨y, hyV_adj, hyV⟩ := exists_pred_in_path hP₁.2.2.2.2 hu (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term k swV).1.symm)
      have hy_eq : y = swNode k swY := (in_swV hyV).resolve_left fun heq ↦
        hdisj _ (heq ▸ isAdjInList_mem_left hyV_adj) hB
      subst hy_eq
      have hy := isAdjInList_mem_left hyV_adj
      obtain ⟨y2, hUy2_adj, hUy2⟩ := exists_succ_in_path hP₂.2.2.2.2 hv (by
        rw [hP₂.2.2.2.1]; exact some_ne_some (swNode_ne_term k swU).2.2.2.symm)
      have hy2_eq : y2 = swNode k swY2 := (out_swU hUy2).resolve_right fun heq ↦
        hdisj _ hA (heq ▸ isAdjInList_mem_right hUy2_adj)
      subst hy2_eq
      have hy2 := isAdjInList_mem_right hUy2_adj
      obtain ⟨c, hcY_adj, hcY⟩ := exists_pred_in_path hP₁.2.2.2.2 hy (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term k swY).1.symm)
      have hc_eq : c = swNode k swC := (in_swY hcY).resolve_right fun heq ↦
        hdisj _ (heq ▸ isAdjInList_mem_left hcY_adj) hy2
      obtain ⟨d, hY2d_adj, hY2d⟩ := exists_succ_in_path hP₂.2.2.2.2 hy2 (by
        rw [hP₂.2.2.2.1]; exact some_ne_some (swNode_ne_term k swY2).2.2.2.symm)
      have hd_eq : d = swNode k swD := (out_swY2 hY2d).resolve_left fun heq ↦
        hdisj _ hy (heq ▸ isAdjInList_mem_right hY2d_adj)
      exact Or.inr ⟨hyV_adj, hc_eq ▸ isAdjInList_mem_left hcY_adj, hy, hu,
        hB, hv, hy2, hd_eq ▸ isAdjInList_mem_right hY2d_adj⟩
    · exact absurd hv (hdisj _ hu)
  have hAB : ∀ k < K, swNode k swA ∈ P₁ ∧ swNode k swB ∈ P₂ := by
    intro k
    induction k with
    | zero =>
      intro h0
      have ht1 : t1Node ∈ P₁ := List.mem_of_getLast? hP₁.2.2.2.1
      obtain ⟨u, hu_adj, hut⟩ := exists_pred_in_path hP₁.2.2.2.2 ht1 (by
        rw [hP₁.2.2.1]; decide)
      have huA : u = swNode 0 swA := by
        rcases in_t1Node hut with ⟨hK0, _⟩ | ⟨_, hA⟩ <;> [omega; exact hA]
      have hs2 : s2Node ∈ P₂ := List.mem_of_head? hP₂.2.2.1
      obtain ⟨v, hv_adj, hsv⟩ := exists_succ_in_path hP₂.2.2.2.2 hs2 (by
        rw [hP₂.2.2.2.1]; decide)
      have hvB : v = swNode 0 swB := by
        rcases out_s2Node hsv with ⟨hK0, _⟩ | ⟨_, hB⟩ <;> [omega; exact hB]
      exact ⟨huA ▸ isAdjInList_mem_left hu_adj, hvB ▸ isAdjInList_mem_right hv_adj⟩
    | succ k ih =>
      intro hk1
      obtain ⟨hA, hB⟩ := ih (by omega)
      have hCD : swNode k swC ∈ P₁ ∧ swNode k swD ∈ P₂ := by
        rcases hlock_step k (by omega) hA hB with h | h
        · exact ⟨h.2.1, h.2.2.2.2.2.2.2⟩
        · exact ⟨h.2.1, h.2.2.2.2.2.2.2⟩
      obtain ⟨a', ha'_adj, ha'C⟩ := exists_pred_in_path hP₁.2.2.2.2 hCD.1 (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term k swC).1.symm)
      obtain ⟨b', hb'_adj, hDb'⟩ := exists_succ_in_path hP₂.2.2.2.2 hCD.2 (by
        rw [hP₂.2.2.2.1]; exact some_ne_some (swNode_ne_term k swD).2.2.2.symm)
      have ha'_eq : a' = swNode (k + 1) swA := by
        rcases in_swC (by omega) ha'C with ⟨_, h⟩ | ⟨hK, _⟩ <;> [exact h; omega]
      have hb'_eq : b' = swNode (k + 1) swB := by
        rcases out_swD (by omega) hDb' with ⟨_, h⟩ | ⟨hK, _⟩ <;> [exact h; omega]
      exact ⟨ha'_eq ▸ isAdjInList_mem_left ha'_adj, hb'_eq ▸ isAdjInList_mem_right hb'_adj⟩
  have hlock : ∀ k < K,
      (IsAdjInList P₁ (swNode k swX) (swNode k swU) ∧
        swNode k swC ∈ P₁ ∧ swNode k swX ∈ P₁ ∧ swNode k swU ∈ P₁ ∧
        swNode k swB ∈ P₂ ∧ swNode k swV ∈ P₂ ∧ swNode k swX2 ∈ P₂ ∧ swNode k swD ∈ P₂) ∨
      (IsAdjInList P₁ (swNode k swY) (swNode k swV) ∧
        swNode k swC ∈ P₁ ∧ swNode k swY ∈ P₁ ∧ swNode k swV ∈ P₁ ∧
        swNode k swB ∈ P₂ ∧ swNode k swU ∈ P₂ ∧ swNode k swY2 ∈ P₂ ∧ swNode k swD ∈ P₂) :=
    fun k hk ↦ hlock_step k hk (hAB k hk).1 (hAB k hk).2
  have hrout_forces_right : ∀ k < K, swNode k swRout ∈ P₁ → swNode k swV ∈ P₁ := by
    intro k hk hrout
    rcases hlock k hk with ⟨hXU, _, _, _, _, _, _, _⟩ | ⟨_, _, _, hV, _, _, _, _⟩
    · exfalso
      obtain ⟨u, hu_adj, huR⟩ := exists_pred_in_path hP₁.2.2.2.2 hrout (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term k swRout).1.symm)
      have huX : u = swNode k swX := in_swRout huR
      subst huX
      have heq := isAdjInList_succ_unique hP₁.1 hXU hu_adj
      exact absurd (swNode_inj (by decide) (by decide) heq).2 (by decide)
    · exact hV
  have hlout_forces_left : ∀ k < K, swNode k swLout ∈ P₁ → swNode k swV ∉ P₁ := by
    intro k hk hlout hV
    rcases hlock k hk with ⟨_, _, _, hU, _, hV2, _, _⟩ | ⟨hYV, _, _, _, _, _, _, _⟩
    · exact hdisj _ hV hV2
    · obtain ⟨u, hu_adj, huL⟩ := exists_pred_in_path hP₁.2.2.2.2 hlout (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term k swLout).1.symm)
      have huY : u = swNode k swY := in_swLout huL
      subst huY
      have heq := isAdjInList_succ_unique hP₁.1 hYV hu_adj
      exact absurd (swNode_inj (by decide) (by decide) heq).2 (by decide)
  have hclauseM : clauseNode φ.length ∈ P₁ := by
    by_cases hK : K = 0
    · have ht1 : t1Node ∈ P₁ := List.mem_of_getLast? hP₁.2.2.2.1
      obtain ⟨u, hu_adj, hut⟩ := exists_pred_in_path hP₁.2.2.2.2 ht1 (by
        rw [hP₁.2.2.1]; decide)
      rcases in_t1Node hut with ⟨_, rfl⟩ | ⟨hpos, _⟩
      · exact isAdjInList_mem_left hu_adj
      · omega
    · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
      have hC : swNode (K - 1) swC ∈ P₁ := by
        rcases hlock (K - 1) (by omega) with h | h <;> exact h.2.1
      obtain ⟨u, hu_adj, huC⟩ := exists_pred_in_path hP₁.2.2.2.2 hC (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
      rcases in_swC (by omega) huC with ⟨hlt, _⟩ | ⟨_, rfl⟩
      · omega
      · exact isAdjInList_mem_left hu_adj
  have hclause_step : ∀ j < φ.length, clauseNode (j + 1) ∈ P₁ →
      clauseNode j ∈ P₁ ∧ ∃ k < K,
        ((litList φ).getD k ((0, 0), false)).1.1 = j ∧ swNode k swV ∈ P₁ := by
    intro j _ hcj1
    obtain ⟨u, hu_adj, huc⟩ := exists_pred_in_path hP₁.2.2.2.2 hcj1 (by
      rw [hP₁.2.2.1]; exact some_ne_some (clauseNode_ne_term _).1.symm)
    obtain ⟨k, hk, hkj, rfl⟩ := in_clauseNode_succ huc
    have hrout : swNode k swRout ∈ P₁ := isAdjInList_mem_left hu_adj
    have hV : swNode k swV ∈ P₁ := hrout_forces_right k hk hrout
    have hlock_r : swNode k swY ∈ P₁ ∧ swNode k swV ∈ P₁ ∧ swNode k swU ∈ P₂ ∧
        swNode k swY2 ∈ P₂ := by
      rcases hlock k hk with ⟨_, _, _, _, _, hV2, _, _⟩ | ⟨_, _, hY, hV1, _, hU2, hY2, _⟩
      · exact absurd hV2 (hdisj _ hV)
      · exact ⟨hY, hV1, hU2, hY2⟩
    obtain ⟨x, hx_adj, hxR⟩ := exists_pred_in_path hP₁.2.2.2.2 hrout (by
      rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
    have hx_eq : x = swNode k swX := in_swRout hxR
    subst hx_eq
    have hX : swNode k swX ∈ P₁ := isAdjInList_mem_left hx_adj
    obtain ⟨x2, hx2_adj, hx2X⟩ := exists_pred_in_path hP₁.2.2.2.2 hX (by
      rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
    have hx2_eq : x2 = swNode k swX2 := by
      rcases in_swX hx2X with rfl | rfl
      · exfalso
        obtain ⟨c', hc'_adj, hc'Y⟩ := exists_pred_in_path hP₁.2.2.2.2 hlock_r.1 (by
          rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
        have hc'_eq : c' = swNode k swC := (in_swY hc'Y).resolve_right fun heq ↦
          hdisj _ (heq ▸ isAdjInList_mem_left hc'_adj) hlock_r.2.2.2
        subst hc'_eq
        have heq := isAdjInList_succ_unique hP₁.1 hx2_adj hc'_adj
        exact absurd (swNode_inj (by decide) (by decide) heq).2 (by decide)
      · rfl
    subst hx2_eq
    have hX2 : swNode k swX2 ∈ P₁ := isAdjInList_mem_left hx2_adj
    obtain ⟨rin, hrin_adj, hrinX2⟩ := exists_pred_in_path hP₁.2.2.2.2 hX2 (by
      rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
    have hrin_eq : rin = swNode k swRin := by
      rcases in_swX2 hrinX2 with rfl | rfl
      · rfl
      · exfalso
        obtain ⟨a', ha'_adj, ha'A⟩ := exists_pred_in_path hP₁.2.2.2.2 (hAB k hk).1 (by
          rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
        have ha'_eq : a' = swNode k swV := (in_swA ha'A).resolve_left fun heq ↦
          hdisj _ (heq ▸ isAdjInList_mem_left ha'_adj) hlock_r.2.2.1
        subst ha'_eq
        have heq := isAdjInList_succ_unique hP₁.1 hrin_adj ha'_adj
        exact absurd (swNode_inj (by decide) (by decide) heq).2 (by decide)
    subst hrin_eq
    have hRin : swNode k swRin ∈ P₁ := isAdjInList_mem_left hrin_adj
    obtain ⟨cj, hcj_adj, hcjRin⟩ := exists_pred_in_path hP₁.2.2.2.2 hRin (by
      rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
    have hcj_eq : cj = clauseNode j := by rw [in_swRin hcjRin, hkj]
    exact ⟨hcj_eq ▸ isAdjInList_mem_left hcj_adj, k, hk, hkj, hV⟩
  have hclauses : ∀ j ≤ φ.length, clauseNode j ∈ P₁ ∧
      (j < φ.length → ∃ k < K,
        ((litList φ).getD k ((0, 0), false)).1.1 = j ∧ swNode k swV ∈ P₁) := by
    intro j hj
    obtain ⟨d, hd_le, rfl⟩ : ∃ d ≤ φ.length, j = φ.length - d := ⟨φ.length - j, by omega, by omega⟩
    induction d with
    | zero => exact ⟨by simpa using hclauseM, fun h ↦ by omega⟩
    | succ d ih =>
      have hprev := (ih (by omega) (by omega)).1
      have heq : φ.length - (d + 1) + 1 = φ.length - d := by omega
      rw [← heq] at hprev
      obtain ⟨hcur, hex⟩ := hclause_step (φ.length - (d + 1)) (by omega) hprev
      exact ⟨hcur, fun _ ↦ hex⟩
  have hvarN : varNode φ.vars.length ∈ P₁ := by
    have hc0 : clauseNode 0 ∈ P₁ := (hclauses 0 (Nat.zero_le _)).1
    obtain ⟨u, hu_adj, huc0⟩ := exists_pred_in_path hP₁.2.2.2.2 hc0 (by
      rw [hP₁.2.2.1]; exact some_ne_some (clauseNode_ne_term _).1.symm)
    rw [← in_clauseNode_zero huc0]
    exact isAdjInList_mem_left hu_adj
  have htrace_chain : ∀ (i : ℕ) (val : Bool), i < φ.vars.length →
      ∀ (idx : ℕ), idx < (varOccs φ i val).length →
        swNode ((varOccs φ i val).getD idx 0) swLout ∈ P₁ →
        varNode i ∈ P₁ ∧ ∀ m ≤ idx,
          swNode ((varOccs φ i val).getD m 0) swV ∉ P₁ := by
    intro i val hi idx
    induction idx with
    | zero =>
      intro h0 hlout
      set k := (varOccs φ i val).getD 0 0
      have hk_mem : k ∈ varOccs φ i val := by
        dsimp only [k]; rw [List.getD_eq_getElem _ _ h0]; exact List.getElem_mem h0
      have hk : k < K := (mem_varOccs_iff.mp hk_mem).1
      have hnotV : swNode k swV ∉ P₁ := hlout_forces_left k hk hlout
      have hlock_l : swNode k swX ∈ P₁ ∧ swNode k swU ∈ P₁ ∧ swNode k swV ∈ P₂ ∧
          swNode k swX2 ∈ P₂ := by
        rcases hlock k hk with ⟨_, _, hX, hU, _, hV2, hX2, _⟩ | ⟨_, _, _, hV1, _, _, _, _⟩
        · exact ⟨hX, hU, hV2, hX2⟩
        · exact absurd hV1 hnotV
      obtain ⟨y, hy_adj, hyL⟩ := exists_pred_in_path hP₁.2.2.2.2 hlout (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
      have hy_eq : y = swNode k swY := in_swLout hyL
      subst hy_eq
      have hY : swNode k swY ∈ P₁ := isAdjInList_mem_left hy_adj
      obtain ⟨y2, hy2_adj, hy2Y⟩ := exists_pred_in_path hP₁.2.2.2.2 hY (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
      have hy2_eq : y2 = swNode k swY2 := by
        rcases in_swY hy2Y with rfl | rfl
        · exfalso
          obtain ⟨c', hc'_adj, hc'X⟩ := exists_pred_in_path hP₁.2.2.2.2 hlock_l.1 (by
            rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
          have hc'_eq : c' = swNode k swC := (in_swX hc'X).resolve_right fun heq ↦
            hdisj _ (heq ▸ isAdjInList_mem_left hc'_adj) hlock_l.2.2.2
          subst hc'_eq
          have heq := isAdjInList_succ_unique hP₁.1 hy2_adj hc'_adj
          exact absurd (swNode_inj (by decide) (by decide) heq).2 (by decide)
        · rfl
      subst hy2_eq
      have hY2 : swNode k swY2 ∈ P₁ := isAdjInList_mem_left hy2_adj
      obtain ⟨lin, hlin_adj, hlinY2⟩ := exists_pred_in_path hP₁.2.2.2.2 hY2 (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
      have hlin_eq : lin = swNode k swLin := by
        rcases in_swY2 hlinY2 with rfl | rfl
        · rfl
        · exfalso
          obtain ⟨a', ha'_adj, ha'A⟩ := exists_pred_in_path hP₁.2.2.2.2 (hAB k hk).1 (by
            rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
          have ha'_eq : a' = swNode k swU := (in_swA ha'A).resolve_right fun heq ↦
            hdisj _ (heq ▸ isAdjInList_mem_left ha'_adj) hlock_l.2.2.1
          subst ha'_eq
          have heq := isAdjInList_succ_unique hP₁.1 hlin_adj ha'_adj
          exact absurd (swNode_inj (by decide) (by decide) heq).2 (by decide)
      subst hlin_eq
      have hLin : swNode k swLin ∈ P₁ := isAdjInList_mem_left hlin_adj
      obtain ⟨prev, hprev_adj, hprevLin⟩ := exists_pred_in_path hP₁.2.2.2.2 hLin (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
      obtain ⟨i', hi', hch⟩ := in_swLin hprevLin
      have hprev_eq : prev = varNode i := by
        have hcheck_ks : ∀ (val' : Bool) (h : (prev, swNode k swLin) ∈
            chainArcs (varNode i') (varNode (i' + 1)) (varOccs φ i' val')), prev = varNode i := by
          intro val' h
          cases hks : varOccs φ i' val' with
          | nil =>
            rw [hks] at h
            rcases mem_chainArcs_cases h with ⟨_, _, hv⟩ | ⟨_, hm, _, _⟩ | ⟨_, _, hm, _, _, _⟩ |
              ⟨_, hm, _, _⟩
            · exact absurd hv (varNode_ne_swNode _ _ _).symm
            all_goals simp at hm
          | cons k₀ rest =>
            rw [hks] at h
            rw [mem_chainArcs_cons_iff] at h
            have hsame : i' = i ∧ val' = val := by
              have hk_in : k ∈ varOccs φ i' val' := by
                rw [hks]
                rcases h with ⟨_, hv⟩ | ⟨t, ht, _, hv⟩ | ⟨_, hv⟩
                · have := (swNode_inj (by decide) (by decide) hv).1; subst this
                  exact List.mem_cons_self
                · have hkeq := (swNode_inj (by decide) (by decide) hv).1
                  rw [hkeq]
                  have ht' : t + 1 < (k₀ :: rest).length := by omega
                  rw [List.getD_eq_getElem _ _ ht']; exact List.getElem_mem ht'
                · exact absurd hv (varNode_ne_swNode _ _ _).symm
              have h1 := mem_varOccs_iff.mp hk_mem
              have h2 := mem_varOccs_iff.mp hk_in
              refine ⟨h2.2.1.symm.trans h1.2.1, ?_⟩
              rw [List.getD_eq_getElem _ _ hk] at h1 h2
              cases val <;> cases val' <;> simp_all
            rcases hsame with ⟨rfl, rfl⟩
            rcases h with ⟨rfl, _⟩ | ⟨t, ht, _, hv⟩ | ⟨_, hv⟩
            · rfl
            · exfalso
              have hk_eq := (swNode_inj (by decide) (by decide) hv).1
              have hnd : (varOccs φ i' val').Nodup := List.nodup_range.filter _
              rw [hks] at hnd
              have ht1 : t + 1 < (k₀ :: rest).length := by omega
              have hget0 : k = k₀ := by
                have : k = (varOccs φ i' val').getD 0 0 := rfl
                rw [hks] at this; exact this
              have hget1 : (k₀ :: rest).getD (t + 1) 0 = k₀ := hk_eq.symm.trans hget0
              rw [List.getD_eq_getElem _ _ ht1] at hget1
              have h0_lt : 0 < (k₀ :: rest).length := by simp
              have heq_idx : (⟨t + 1, ht1⟩ : Fin (k₀ :: rest).length) = ⟨0, h0_lt⟩ :=
                (List.nodup_iff_injective_getElem.mp hnd) (by simpa using hget1)
              have : t + 1 = 0 := congrArg Fin.val heq_idx
              omega
            · exact absurd hv (varNode_ne_swNode _ _ _).symm
        rcases hch with h | h
        · exact hcheck_ks true h
        · exact hcheck_ks false h
      exact ⟨hprev_eq ▸ isAdjInList_mem_left hprev_adj, fun m hm ↦ by
        have : m = 0 := by omega
        subst this; exact hnotV⟩
    | succ idx ih =>
      intro hidx hlout
      set k := (varOccs φ i val).getD (idx + 1) 0
      have hk_mem : k ∈ varOccs φ i val := by
        dsimp only [k]; rw [List.getD_eq_getElem _ _ hidx]; exact List.getElem_mem hidx
      have hk : k < K := (mem_varOccs_iff.mp hk_mem).1
      have hnotV : swNode k swV ∉ P₁ := hlout_forces_left k hk hlout
      have hlock_l : swNode k swX ∈ P₁ ∧ swNode k swU ∈ P₁ ∧ swNode k swV ∈ P₂ ∧
          swNode k swX2 ∈ P₂ := by
        rcases hlock k hk with ⟨_, _, hX, hU, _, hV2, hX2, _⟩ | ⟨_, _, _, hV1, _, _, _, _⟩
        · exact ⟨hX, hU, hV2, hX2⟩
        · exact absurd hV1 hnotV
      obtain ⟨y, hy_adj, hyL⟩ := exists_pred_in_path hP₁.2.2.2.2 hlout (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
      have hy_eq : y = swNode k swY := in_swLout hyL
      subst hy_eq
      have hY : swNode k swY ∈ P₁ := isAdjInList_mem_left hy_adj
      obtain ⟨y2, hy2_adj, hy2Y⟩ := exists_pred_in_path hP₁.2.2.2.2 hY (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
      have hy2_eq : y2 = swNode k swY2 := by
        rcases in_swY hy2Y with rfl | rfl
        · exfalso
          obtain ⟨c', hc'_adj, hc'X⟩ := exists_pred_in_path hP₁.2.2.2.2 hlock_l.1 (by
            rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
          have hc'_eq : c' = swNode k swC := (in_swX hc'X).resolve_right fun heq ↦
            hdisj _ (heq ▸ isAdjInList_mem_left hc'_adj) hlock_l.2.2.2
          subst hc'_eq
          have heq := isAdjInList_succ_unique hP₁.1 hy2_adj hc'_adj
          exact absurd (swNode_inj (by decide) (by decide) heq).2 (by decide)
        · rfl
      subst hy2_eq
      have hY2 : swNode k swY2 ∈ P₁ := isAdjInList_mem_left hy2_adj
      obtain ⟨lin, hlin_adj, hlinY2⟩ := exists_pred_in_path hP₁.2.2.2.2 hY2 (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
      have hlin_eq : lin = swNode k swLin := by
        rcases in_swY2 hlinY2 with rfl | rfl
        · rfl
        · exfalso
          obtain ⟨a', ha'_adj, ha'A⟩ := exists_pred_in_path hP₁.2.2.2.2 (hAB k hk).1 (by
            rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
          have ha'_eq : a' = swNode k swU := (in_swA ha'A).resolve_right fun heq ↦
            hdisj _ (heq ▸ isAdjInList_mem_left ha'_adj) hlock_l.2.2.1
          subst ha'_eq
          have heq := isAdjInList_succ_unique hP₁.1 hlin_adj ha'_adj
          exact absurd (swNode_inj (by decide) (by decide) heq).2 (by decide)
      subst hlin_eq
      have hLin : swNode k swLin ∈ P₁ := isAdjInList_mem_left hlin_adj
      obtain ⟨prev, hprev_adj, hprevLin⟩ := exists_pred_in_path hP₁.2.2.2.2 hLin (by
        rw [hP₁.2.2.1]; exact some_ne_some (swNode_ne_term _ _).1.symm)
      obtain ⟨i', hi', hch⟩ := in_swLin hprevLin
      have hprev_eq : prev = swNode ((varOccs φ i val).getD idx 0) swLout := by
        have hcheck_ks : ∀ (val' : Bool) (h : (prev, swNode k swLin) ∈
            chainArcs (varNode i') (varNode (i' + 1)) (varOccs φ i' val')),
            prev = swNode ((varOccs φ i val).getD idx 0) swLout := by
          intro val' h
          cases hks : varOccs φ i' val' with
          | nil =>
            rw [hks] at h
            rcases mem_chainArcs_cases h with ⟨_, _, hv⟩ | ⟨_, hm, _, _⟩ | ⟨_, _, hm, _, _, _⟩ |
              ⟨_, hm, _, _⟩
            · exact absurd hv (varNode_ne_swNode _ _ _).symm
            all_goals simp at hm
          | cons k₀ rest =>
            rw [hks] at h
            rw [mem_chainArcs_cons_iff] at h
            have hsame : i' = i ∧ val' = val := by
              have hk_in : k ∈ varOccs φ i' val' := by
                rw [hks]
                rcases h with ⟨_, hv⟩ | ⟨t, ht, _, hv⟩ | ⟨_, hv⟩
                · have := (swNode_inj (by decide) (by decide) hv).1; subst this
                  exact List.mem_cons_self
                · have hkeq := (swNode_inj (by decide) (by decide) hv).1
                  rw [hkeq]
                  have ht' : t + 1 < (k₀ :: rest).length := by omega
                  rw [List.getD_eq_getElem _ _ ht']; exact List.getElem_mem ht'
                · exact absurd hv (varNode_ne_swNode _ _ _).symm
              have h1 := mem_varOccs_iff.mp hk_mem
              have h2 := mem_varOccs_iff.mp hk_in
              refine ⟨h2.2.1.symm.trans h1.2.1, ?_⟩
              rw [List.getD_eq_getElem _ _ hk] at h1 h2
              cases val <;> cases val' <;> simp_all
            rcases hsame with ⟨rfl, rfl⟩
            have hnd : (varOccs φ i' val').Nodup := List.nodup_range.filter _
            rw [hks] at hnd hidx
            rcases h with ⟨_, hv⟩ | ⟨t, ht, rfl, hv⟩ | ⟨_, hv⟩
            · exfalso
              have hk_eq := (swNode_inj (by decide) (by decide) hv).1
              have hget : (k₀ :: rest)[idx + 1]'hidx = (k₀ :: rest)[0]'(by simp) := by
                have : k = (k₀ :: rest).getD (idx + 1) 0 := by rw [← hks]
                rw [List.getD_eq_getElem _ _ hidx] at this
                exact this.symm.trans hk_eq
              have hfin : (⟨idx + 1, hidx⟩ : Fin (k₀ :: rest).length) = ⟨0, by simp⟩ :=
                (List.nodup_iff_injective_getElem.mp hnd) hget
              have : idx + 1 = 0 := congrArg Fin.val hfin
              omega
            · have hk_eq := (swNode_inj (by decide) (by decide) hv).1
              have ht1 : t + 1 < (k₀ :: rest).length := by omega
              have hget : (k₀ :: rest)[t + 1]'ht1 = (k₀ :: rest)[idx + 1]'hidx := by
                have h1 : (k₀ :: rest).getD (t + 1) 0 = k := hk_eq.symm
                have h2 : (k₀ :: rest).getD (idx + 1) 0 = k := by rw [← hks]
                rw [List.getD_eq_getElem _ _ ht1] at h1
                rw [List.getD_eq_getElem _ _ hidx] at h2
                exact h1.trans h2.symm
              have hfin : (⟨t + 1, ht1⟩ : Fin (k₀ :: rest).length) = ⟨idx + 1, hidx⟩ :=
                (List.nodup_iff_injective_getElem.mp hnd) hget
              have hti : t + 1 = idx + 1 := congrArg Fin.val hfin
              have : t = idx := by omega
              subst this
              rw [hks]
            · exact absurd hv (varNode_ne_swNode _ _ _).symm
        rcases hch with h | h
        · exact hcheck_ks true h
        · exact hcheck_ks false h
      obtain ⟨hvi, hprev_notV⟩ := ih (by omega) (hprev_eq ▸ isAdjInList_mem_left hprev_adj)
      refine ⟨hvi, fun m hm ↦ ?_⟩
      by_cases hmeq : m = idx + 1
      · subst hmeq; exact hnotV
      · exact hprev_notV m (by omega)
  have hvar_step : ∀ i < φ.vars.length, varNode (i + 1) ∈ P₁ →
      varNode i ∈ P₁ ∧ ∃ val : Bool, ∀ k ∈ varOccs φ i val, swNode k swV ∉ P₁ := by
    intro i hi hvi1
    obtain ⟨u, hu_adj, huvi1⟩ := exists_pred_in_path hP₁.2.2.2.2 hvi1 (by
      rw [hP₁.2.2.1]; exact some_ne_some (varNode_ne_term _).1.symm)
    have hbranch : ∀ val : Bool,
        (u, varNode (i + 1)) ∈ chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i val) →
        varNode i ∈ P₁ ∧ ∀ k ∈ varOccs φ i val, swNode k swV ∉ P₁ := by
      intro val hch
      rcases mem_chainArcs_cases hch with ⟨hemp, rfl, _⟩ | ⟨_, _, _, hv⟩ |
        ⟨_, _, _, _, _, hv⟩ | ⟨k, hk_mem, _, _⟩
      · exact ⟨isAdjInList_mem_left hu_adj, fun _ h ↦ by simp [hemp] at h⟩
      · exact absurd hv (varNode_ne_swNode _ _ _)
      · exact absurd hv (varNode_ne_swNode _ _ _)
      · have hlen_pos : 0 < (varOccs φ i val).length := List.length_pos_of_mem hk_mem
        have hlast_eq : u = swNode ((varOccs φ i val).getD ((varOccs φ i val).length - 1) 0)
            swLout := by
          cases hks : varOccs φ i val with
          | nil => simp [hks] at hk_mem
          | cons k₀ rest =>
            rw [hks] at hch
            rw [mem_chainArcs_cons_iff] at hch
            rcases hch with ⟨_, hv⟩ | ⟨_, _, _, hv⟩ | ⟨hu', _⟩
            · exact absurd hv (varNode_ne_swNode _ _ _)
            · exact absurd hv (varNode_ne_swNode _ _ _)
            · exact hu'
        obtain ⟨hvi, hall⟩ := htrace_chain i val hi ((varOccs φ i val).length - 1) (by omega)
          (hlast_eq ▸ isAdjInList_mem_left hu_adj)
        refine ⟨hvi, fun k' hk' ↦ ?_⟩
        obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hk'
        have := hall m (by omega)
        rwa [List.getD_eq_getElem _ _ hm] at this
    rcases in_varNode_succ huvi1 with h | h
    · obtain ⟨hvi, hall⟩ := hbranch true h; exact ⟨hvi, true, hall⟩
    · obtain ⟨hvi, hall⟩ := hbranch false h; exact ⟨hvi, false, hall⟩
  have hvars : ∀ i ≤ φ.vars.length, varNode i ∈ P₁ ∧
      (i < φ.vars.length → ∃ val : Bool, ∀ k ∈ varOccs φ i val, swNode k swV ∉ P₁) := by
    intro i hi
    obtain ⟨d, hd_le, rfl⟩ : ∃ d ≤ φ.vars.length, i = φ.vars.length - d :=
      ⟨φ.vars.length - i, by omega, by omega⟩
    induction d with
    | zero => exact ⟨by simpa using hvarN, fun h ↦ by omega⟩
    | succ d ih =>
      have hprev := (ih (by omega) (by omega)).1
      have heq : φ.vars.length - (d + 1) + 1 = φ.vars.length - d := by omega
      rw [← heq] at hprev
      obtain ⟨hcur, hex⟩ := hvar_step (φ.vars.length - (d + 1)) (by omega) hprev
      exact ⟨hcur, fun _ ↦ hex⟩
  classical
  let dir : ℕ → Bool := fun i ↦
    if hi : i < φ.vars.length then ((hvars i (le_of_lt hi)).2 hi).choose else false
  have hdir : ∀ i (hi : i < φ.vars.length), ∀ k ∈ varOccs φ i (dir i), swNode k swV ∉ P₁ :=
    fun i hi ↦ by simpa [dir, hi] using ((hvars i (le_of_lt hi)).2 hi).choose_spec
  refine ⟨fun x ↦ dir (φ.vars.idxOf x), (CNF.eval_eq_true_iff _ _).mpr fun c hc ↦ ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨k, hk, hkj, hkV⟩ := (hclauses j (le_of_lt hj)).2 hj
  obtain ⟨j', hj', l, hl, hlit⟩ := litList_getD_eq hk
  rw [hlit] at hkj
  dsimp only at hkj
  subst hkj
  refine (Clause.eval_eq_true_iff _ _).mpr ⟨l, hl, ?_⟩
  have hl_var : l.1 ∈ φ.vars :=
    List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨_, List.getElem_mem hj, hl⟩, rfl⟩
  have hi : φ.vars.idxOf l.1 < φ.vars.length := List.idxOf_lt_length_iff.mpr hl_var
  by_contra hne
  have hk_occ : k ∈ varOccs φ (φ.vars.idxOf l.1) (dir (φ.vars.idxOf l.1)) :=
    mem_varOccs_iff.mpr ⟨hk, by rw [hlit], by rw [hlit]; exact fun h ↦ hne h.symm⟩
  exact hdir _ hi k hk_occ hkV


end Cslib.Complexity.BackAndForthPaths
