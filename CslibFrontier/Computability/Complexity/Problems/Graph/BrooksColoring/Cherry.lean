/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.BrooksColoring

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Constructive Polynomial-Time Brooks Coloring (Lovász Cherry Lemma and Correctness Proof)

This module proves the correctness of `brooksColoring` from `BrooksColoring.lean`:
for every graph `H` with maximum degree `≤ k` (`k ≥ 3`) and no `K_{k+1}` connected component
(`hasCompleteCompBool H k = false`), `brooksColoring H k` returns a valid partition of `H.vertices`
into at most `k` nonempty independent sets of `H`.
-/

public section

namespace Cslib.Complexity

open Finset Cslib.Complexity

/-! ### 1. Reverse-BFS Greedy Coloring Helper -/

/-- Helper: running `greedyColor` along `(bfsOrder H S r).reverse` extending a proper
`< k`-coloring `initCol` (disjoint from `S`) produces a proper `< k`-coloring of
`initCol.keys ∪ S`, provided every `v ∈ S \ {r}` has total degree `≤ k` in `S ∪ initCol.keys`
and `r` either has total degree `< k` or has two distinct same-colored neighbors in `initCol`
with total degree `≤ k`. -/
theorem reverseBfs_greedyColor_spec (H : Graph) (k : ℕ) (hk : 0 < k) (S : List ℕ)
    (hnd : S.Nodup) (hS : ∀ y ∈ S, y ∈ H.vertices) {r : ℕ} (hr : r ∈ S)
    (hreach : (bfsOrder H S r).length = S.length)
    (initCol : List (ℕ × ℕ))
    (hinit_nd : (initCol.map Prod.fst).Nodup)
    (hinit_lt : ∀ p ∈ initCol, p.2 < k)
    (hinit_prop : ∀ p ∈ initCol, ∀ q ∈ initCol, H.adjBool p.1 q.1 = true → p.2 ≠ q.2)
    (hdisj : ∀ x ∈ S, x ∉ initCol.map Prod.fst)
    (hdeg : ∀ x ∈ S, x ≠ r →
      (S.filter fun w ↦ H.adjBool x w).length +
        (initCol.filter fun p ↦ H.adjBool x p.1).length ≤ k)
    (hroot :
      ((S.filter fun w ↦ H.adjBool r w).length +
        (initCol.filter fun p ↦ H.adjBool r p.1).length < k) ∨
      ((S.filter fun w ↦ H.adjBool r w).length +
        (initCol.filter fun p ↦ H.adjBool r p.1).length ≤ k ∧
        ∃ p₁ ∈ initCol, ∃ p₂ ∈ initCol, p₁.1 ≠ p₂.1 ∧
          H.adjBool r p₁.1 = true ∧ H.adjBool r p₂.1 = true ∧ p₁.2 = p₂.2)) :
    let cols := greedyColor H k (bfsOrder H S r).reverse initCol
    (cols.map Prod.fst).Nodup ∧
    (∀ p ∈ cols, p.2 < k) ∧
    (∀ p ∈ cols, ∀ q ∈ cols, H.adjBool p.1 q.1 = true → p.2 ≠ q.2) ∧
    (∀ v, v ∈ cols.map Prod.fst ↔ v ∈ initCol.map Prod.fst ∨ v ∈ S) := by
  classical
  obtain ⟨hB_nd, hB_sub, hr_B, hB_par, _, _⟩ := bfsOrder_spec H S hnd hS hr
  set B := bfsOrder H S r
  set order := B.reverse
  have hB_mem : ∀ x, x ∈ B ↔ x ∈ S := fun x ↦ by
    have hEq : B.toFinset = S.toFinset :=
      Finset.eq_of_subset_of_card_le
        (fun y hy ↦ List.mem_toFinset.mpr (hB_sub y (List.mem_toFinset.mp hy)))
        (by rw [List.toFinset_card_of_nodup hB_nd, List.toFinset_card_of_nodup hnd, hreach])
    simpa only [List.mem_toFinset] using Finset.ext_iff.mp hEq x
  have horder_nd : order.Nodup := List.nodup_reverse.mpr hB_nd
  have horder_mem : ∀ x, x ∈ order ↔ x ∈ S := fun x ↦ by rw [List.mem_reverse, hB_mem]
  have hstep_inv : ∀ m (hm : m ≤ order.length),
      let pre := (order.take m).foldl (greedyColorStep H k) initCol
      (pre.map Prod.fst).Nodup ∧
      (∀ v, v ∈ pre.map Prod.fst ↔ v ∈ initCol.map Prod.fst ∨ v ∈ order.take m) ∧
      (∀ p ∈ initCol, p ∈ pre) := by
    intro m
    induction m with
    | zero =>
      intro _; exact ⟨hinit_nd, fun v ↦ by simp, fun p hp ↦ hp⟩
    | succ m ih =>
      intro hm
      obtain ⟨hnd_m, hcov_m, hsub_m⟩ := ih (by omega)
      set pre := (order.take m).foldl (greedyColorStep H k) initCol
      rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      set v := order[m]'(by omega)
      have hstep_eq : greedyColorStep H k pre v =
          if pre.any (fun p ↦ decide (p.1 = v)) = true then pre
          else (v, firstFreeColor H k pre v) :: pre := rfl
      dsimp only
      rw [hstep_eq]
      by_cases hseen : pre.any (fun p ↦ decide (p.1 = v)) = true
      · simp only [hseen, ↓reduceIte]
        refine ⟨hnd_m, fun u ↦ ?_, hsub_m⟩
        rw [hcov_m u, List.mem_append, List.mem_singleton]
        constructor
        · exact fun h ↦ h.elim Or.inl (fun h' ↦ Or.inr (Or.inl h'))
        · rintro (h | h | rfl)
          · exact Or.inl h
          · exact Or.inr h
          · obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hseen
            exact (hcov_m v).mp (List.mem_map.mpr ⟨p, hp, decide_eq_true_eq.mp hpe⟩)
      · simp only [Bool.eq_false_iff.mpr hseen, Bool.false_eq_true, ↓reduceIte]
        have hv_not : v ∉ pre.map Prod.fst := fun hm' ↦ by
          obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm'
          exact hseen (List.any_eq_true.mpr ⟨p, hp, decide_eq_true_eq.mpr hpe⟩)
        refine ⟨List.nodup_cons.mpr ⟨hv_not, hnd_m⟩, fun u ↦ ?_,
          fun p hp ↦ List.mem_cons_of_mem _ (hsub_m p hp)⟩
        rw [List.map_cons, List.mem_cons, hcov_m u, List.mem_append, List.mem_singleton]
        tauto
  have hfree : ∀ i (hi : i < order.length),
      let pre := (order.take i).foldl (greedyColorStep H k) initCol
      let v := order[i]'hi
      ¬ pre.any (fun p ↦ decide (p.1 = v)) = true →
      ((pre.filter fun p ↦ H.adjBool v p.1).map Prod.snd).toFinset.card < k := by
    intro i hi pre v _
    obtain ⟨hpre_nd, hpre_cov, hpre_init⟩ := hstep_inv i (le_of_lt hi)
    have hvS : v ∈ S := (horder_mem v).mp (List.getElem_mem hi)
    have hpre_nb_le : (pre.filter fun p ↦ H.adjBool v p.1).length ≤
        (S.filter fun w ↦ H.adjBool v w).length +
          (initCol.filter fun p ↦ H.adjBool v p.1).length := by
      have hsub_keys : (pre.filter fun p ↦ H.adjBool v p.1).length =
          (((pre.filter fun p ↦ H.adjBool v p.1).map Prod.fst).toFinset).card := by
        rw [List.toFinset_card_of_nodup (hpre_nd.sublist (List.filter_sublist.map Prod.fst)),
          List.length_map]
      rw [hsub_keys, ← List.toFinset_card_of_nodup (hnd.filter _),
        ← List.toFinset_card_of_nodup ((hinit_nd.of_map _).filter _)]
      have hcard_init : ((initCol.filter fun p ↦ H.adjBool v p.1).toFinset).card =
          (((initCol.filter fun p ↦ H.adjBool v p.1).map Prod.fst).toFinset).card := by
        rw [List.toFinset_card_of_nodup ((hinit_nd.of_map _).filter _),
          List.toFinset_card_of_nodup (hinit_nd.sublist (List.filter_sublist.map Prod.fst)),
          List.length_map]
      rw [hcard_init, ← Finset.card_union_of_disjoint]
      · refine Finset.card_le_card fun w hw ↦ ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
        have hpf := List.mem_filter.mp hp
        have hcov := (hpre_cov p.1).mp (List.mem_map.mpr ⟨p, hpf.1, rfl⟩)
        rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset]
        rcases hcov with hinit | hord
        · right
          obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hinit
          exact List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, hqp ▸ hpf.2⟩, hqp⟩
        · left
          exact List.mem_filter.mpr ⟨(horder_mem p.1).mp (List.mem_of_mem_take hord), hpf.2⟩
      · rw [Finset.disjoint_left]
        intro w hw1 hw2
        have h1 := (List.mem_filter.mp (List.mem_toFinset.mp hw1)).1
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw2)
        exact hdisj p.1 h1 (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩)
    by_cases hvr : v = r
    · rcases hroot with hlt | ⟨hle, p₁, hp₁, p₂, hp₂, hne12, hadj1, hadj2, hcol12⟩
      · calc ((pre.filter fun p ↦ H.adjBool v p.1).map Prod.snd).toFinset.card
            ≤ (pre.filter fun p ↦ H.adjBool v p.1).length :=
              (List.toFinset_card_le _).trans_eq (List.length_map _)
          _ < k := by rw [hvr] at hpre_nb_le ⊢; omega
      · -- `p₁, p₂` are two distinct elements of `pre.filter (H.adjBool v ·.1)` with equal `.2`:
        have hp1_f : p₁ ∈ (pre.filter fun p ↦ H.adjBool v p.1).toFinset :=
          List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hpre_init p₁ hp₁, hvr ▸ hadj1⟩)
        have hp2_f : p₂ ∈ (pre.filter fun p ↦ H.adjBool v p.1).toFinset :=
          List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hpre_init p₂ hp₂, hvr ▸ hadj2⟩)
        have hne_p : p₁ ≠ p₂ := fun h ↦ hne12 (congrArg Prod.fst h)
        have himg : ((pre.filter fun p ↦ H.adjBool v p.1).map Prod.snd).toFinset =
            ((pre.filter fun p ↦ H.adjBool v p.1).toFinset.erase p₂).image Prod.snd := by
          ext c
          simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, Finset.mem_erase]
          constructor
          · rintro ⟨p, hp, rfl⟩
            by_cases hp2' : p = p₂
            · exact ⟨p₁, ⟨hne_p, List.mem_toFinset.mp hp1_f⟩, hp2' ▸ hcol12⟩
            · exact ⟨p, ⟨hp2', hp⟩, rfl⟩
          · rintro ⟨p, ⟨_, hp⟩, rfl⟩
            exact ⟨p, hp, rfl⟩
        rw [himg]
        have hpos_f : 0 < (pre.filter fun p ↦ H.adjBool v p.1).toFinset.card :=
          Finset.card_pos.mpr ⟨p₂, hp2_f⟩
        have hcard_f : (pre.filter fun p ↦ H.adjBool v p.1).toFinset.card ≤ k := by
          calc _ ≤ (pre.filter fun p ↦ H.adjBool v p.1).length := List.toFinset_card_le _
            _ ≤ k := by rw [hvr] at hpre_nb_le ⊢; omega
        calc (((pre.filter fun p ↦ H.adjBool v p.1).toFinset.erase p₂).image Prod.snd).card
            ≤ ((pre.filter fun p ↦ H.adjBool v p.1).toFinset.erase p₂).card :=
              Finset.card_image_le
          _ = (pre.filter fun p ↦ H.adjBool v p.1).toFinset.card - 1 :=
              Finset.card_erase_of_mem hp2_f
          _ < k := by omega
    · -- `v ≠ r`: `v` has a BFS parent `u ∈ B` strictly earlier in `B`, hence NOT in `pre`!
      obtain ⟨u, huB, hidx_lt, hadj_uv⟩ := hB_par v ((hB_mem v).mpr hvS) hvr
      have huS : u ∈ S := (hB_mem u).mp huB
      have hu_not_pre : u ∉ pre.map Prod.fst := by
        intro hm
        rcases (hpre_cov u).mp hm with hinit | hord
        · exact hdisj u huS hinit
        · obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp hord
          have hj_len : j < i := by simp only [List.length_take] at hj; omega
          have hord_j : order[j]'(by omega) = u := by
            have := List.getElem_take (xs := order) (i := j) (j := i) (h := hj)
            rw [← hju]; exact this.symm
          have hB_idx : B.idxOf u = B.length - 1 - j := by
            have hget : B[B.length - 1 - j]'(by
                simp only [order, List.length_reverse] at hi; omega) = u := by
              rw [← hord_j]
              simp only [order, List.getElem_reverse]
            rw [← hget]
            exact List.Nodup.idxOf_getElem hB_nd _ _
          have hB_idx_v : B.idxOf v = B.length - 1 - i := by
            have hget : B[B.length - 1 - i]'(by
                simp only [order, List.length_reverse] at hi; omega) = v := by
              simp only [v, order, List.getElem_reverse]
            rw [← hget]
            exact List.Nodup.idxOf_getElem hB_nd _ _
          simp only [order, List.length_reverse] at hi
          omega
      have hadj_vu : H.adjBool v u = true := by
        rw [H.adjBool_eq_true_iff] at hadj_uv ⊢; exact hadj_uv.symm
      -- Now `pre` misses `u ∈ S.filter (H.adjBool v)`, giving strictly `< k` neighbors!
      have hstrict : (pre.filter fun p ↦ H.adjBool v p.1).length <
          (S.filter fun w ↦ H.adjBool v w).length +
            (initCol.filter fun p ↦ H.adjBool v p.1).length := by
        have hsub_keys : (pre.filter fun p ↦ H.adjBool v p.1).length =
            (((pre.filter fun p ↦ H.adjBool v p.1).map Prod.fst).toFinset).card := by
          rw [List.toFinset_card_of_nodup (hpre_nd.sublist (List.filter_sublist.map Prod.fst)),
            List.length_map]
        rw [hsub_keys, ← List.toFinset_card_of_nodup (hnd.filter _),
          ← List.toFinset_card_of_nodup ((hinit_nd.of_map _).filter _)]
        have hcard_init : ((initCol.filter fun p ↦ H.adjBool v p.1).toFinset).card =
            (((initCol.filter fun p ↦ H.adjBool v p.1).map Prod.fst).toFinset).card := by
          rw [List.toFinset_card_of_nodup ((hinit_nd.of_map _).filter _),
            List.toFinset_card_of_nodup (hinit_nd.sublist (List.filter_sublist.map Prod.fst)),
            List.length_map]
        rw [hcard_init, ← Finset.card_union_of_disjoint]
        · refine Finset.card_lt_card ⟨fun w hw ↦ ?_, fun hsub ↦ ?_⟩
          · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
            have hpf := List.mem_filter.mp hp
            rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset]
            rcases (hpre_cov p.1).mp (List.mem_map.mpr ⟨p, hpf.1, rfl⟩) with hinit | hord
            · right; obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hinit
              exact List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, hqp ▸ hpf.2⟩, hqp⟩
            · left; exact List.mem_filter.mpr ⟨(horder_mem p.1).mp (List.mem_of_mem_take hord),
                hpf.2⟩
          · have hu_in : u ∈ (S.filter fun w ↦ H.adjBool v w).toFinset ∪
                ((initCol.filter fun p ↦ H.adjBool v p.1).map Prod.fst).toFinset :=
              Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_filter.mpr ⟨huS, hadj_vu⟩))
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (hsub hu_in))
            exact hu_not_pre (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩)
        · rw [Finset.disjoint_left]
          intro w hw1 hw2
          have h1 := (List.mem_filter.mp (List.mem_toFinset.mp hw1)).1
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw2)
          exact hdisj p.1 h1 (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩)
      have hdeg_v := hdeg v hvS hvr
      calc ((pre.filter fun p ↦ H.adjBool v p.1).map Prod.snd).toFinset.card
          ≤ (pre.filter fun p ↦ H.adjBool v p.1).length :=
            (List.toFinset_card_le _).trans_eq (List.length_map _)
        _ < k := by omega
  obtain ⟨h1, h2, h3, h4⟩ := greedyColor_spec H k hk order initCol hinit_nd hinit_lt hinit_prop
    hfree
  exact ⟨h1, h2, h3, fun v ↦ by rw [h4 v, horder_mem v]⟩

/-! ### 2. Lovász Cherry Existence Lemma -/

/-- Helper: in any `2`-connected `k`-regular (`k ≥ 3`) non-complete connected graph `HC`,
there exists a Lovász cherry `(x, y, z)`: `x` adjacent to `y` and `z`, `y ≠ z`, `¬ HC.Adj y z`,
and `HC` restricted to `V \ {y, z}` is connected. -/
theorem exists_lovasz_cherry_abstract {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) (hk : 3 ≤ k)
    (hconn : G.Connected)
    (hreg : ∀ v : α, G.degree v = k)
    (hnot_compl : Fintype.card α ≠ k + 1)
    (h2conn : ∀ x : α, (G.induce {v : α | v ≠ x}).Connected) :
    ∃ x y z : α, y ≠ z ∧ G.Adj x y ∧ G.Adj x z ∧ ¬ G.Adj y z ∧
      (G.induce {v : α | v ≠ y ∧ v ≠ z}).Connected := by
  classical
  have hcard_ge : k + 1 ≤ Fintype.card α := by
    obtain ⟨v₀⟩ := hconn.nonempty
    have h := SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := v₀)
    have hsub : G.neighborFinset v₀ ⊆ Finset.univ.erase v₀ := fun w hw ↦
      Finset.mem_erase.mpr ⟨(G.ne_of_adj ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)).symm,
        Finset.mem_univ w⟩
    have hc := Finset.card_le_card hsub
    rw [h, hreg v₀, Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ] at hc
    omega
  -- Existence of a non-adjacent distinct pair (since `G` is not complete):
  have hex_nonadj : ∃ u v : α, u ≠ v ∧ ¬ G.Adj u v := by
    by_contra hall
    push Not at hall
    obtain ⟨v₀⟩ := hconn.nonempty
    have hEq : G.neighborFinset v₀ = Finset.univ.erase v₀ := by
      ext w; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h ↦ (G.ne_of_adj h).symm, fun h ↦ hall v₀ w h.symm⟩
    have hc := congrArg Finset.card hEq
    rw [SimpleGraph.card_neighborFinset_eq_degree, hreg v₀,
      Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ] at hc
    omega
  -- Case 3b: deleting any two distinct vertices leaves `G` connected!
  by_cases h3conn : ∀ y z : α, y ≠ z → (G.induce {v : α | v ≠ y ∧ v ≠ z}).Connected
  · obtain ⟨u, v, huv, hna⟩ := hex_nonadj
    -- Take a minimum-length walk from `u` to `v` in `G`:
    have hex_d : ∃ d, ∃ p : G.Walk u v, p.length = d := by
      obtain ⟨p⟩ := hconn u v; exact ⟨p.length, p, rfl⟩
    let d := Nat.find hex_d
    obtain ⟨p, hp⟩ := Nat.find_spec hex_d
    have hmin : ∀ q : G.Walk u v, d ≤ q.length := fun q ↦ Nat.find_min' hex_d ⟨q, rfl⟩
    cases p with
    | nil => exact (huv rfl).elim
    | @cons _ x _ h1 p₁ =>
      cases p₁ with
      | nil => exact (hna h1).elim
      | @cons _ z _ h2 p₂ =>
        have hyz : u ≠ z := fun hEq ↦ by
          subst hEq
          have := hmin p₂
          simp only [SimpleGraph.Walk.length_cons] at hp; omega
        have hnayz : ¬ G.Adj u z := fun hadj ↦ by
          have := hmin (.cons hadj p₂)
          simp only [SimpleGraph.Walk.length_cons] at hp this; omega
        exact ⟨x, u, z, hyz, h1.symm, h2, hnayz, h3conn u z hyz⟩
  · -- Case 3a: some `w` has `G' := G \ {w}` NOT 2-connected!
    push Not at h3conn
    obtain ⟨w, c₀, hwc₀, hdisc₀⟩ := h3conn
    -- Work in `G' := G.induce {v | v ≠ w}`:
    let G' := G.induce {v : α | v ≠ w}
    have hG'conn : G'.Connected := h2conn w
    -- Note `G' \ {c}` is `G \ {w, c}`:
    have hsub_eq : ∀ c : {v : α | v ≠ w},
        ¬ (G'.induce {u : {v : α | v ≠ w} | u ≠ c}).Connected →
        ∃ a b : {v : α | v ≠ w}, ∃ (ha : a ≠ c) (hb : b ≠ c),
          ¬ (G'.induce {u : {v : α | v ≠ w} | u ≠ c}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro c hnc
      by_contra hall
      push Not at hall
      have hge3 : 3 ≤ Fintype.card {v : α | v ≠ w} := by
        have h1 : Fintype.card {v : α | v ≠ w} = (Finset.univ.erase w).card :=
          Fintype.card_of_subtype (Finset.univ.erase w) fun x ↦ by simp
        rw [h1, Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ]
        omega
      obtain ⟨u, _, hu⟩ := Finset.exists_mem_ne (s := (Finset.univ : Finset {v : α | v ≠ w}))
        (by rw [Finset.card_univ]; omega) c
      have : Nonempty {u : {v : α | v ≠ w} | u ≠ c} := ⟨⟨u, hu⟩⟩
      exact hnc ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ hall a b ha hb⟩
    -- Define cut-components of `G'` (components of `G' \ {c}`):
    let IsCutComp (c : {v : α | v ≠ w}) (A : Finset {v : α | v ≠ w}) : Prop :=
      c ∉ A ∧ A.Nonempty ∧ (∃ b : {v : α | v ≠ w}, b ≠ c ∧ b ∉ A) ∧
      ∀ u ∈ A, ∀ v : {v : α | v ≠ w}, v ≠ c → G'.Adj u v → v ∈ A
    -- Helper: given `a ≠ c` and `b ≠ c` unreachable in `G' \ {c}`, the component of `a` is a
    -- cut-component of `c`!
    have mkCutComp : ∀ (c a b : {v : α | v ≠ w}) (ha : a ≠ c) (hb : b ≠ c),
        ¬ (G'.induce {u : {v : α | v ≠ w} | u ≠ c}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ →
        ∃ A : Finset {v : α | v ≠ w}, IsCutComp c A ∧ a ∈ A ∧ b ∉ A ∧
          ∀ u ∈ A, ∀ hu : u ≠ c,
            (G'.induce {v : {v : α | v ≠ w} | v ≠ c}).Reachable ⟨a, ha⟩ ⟨u, hu⟩ := by
      intro c a b ha hb hnr
      let A : Finset {v : α | v ≠ w} := Finset.univ.filter fun u ↦
        ∃ hu : u ≠ c, (G'.induce {v : {v : α | v ≠ w} | v ≠ c}).Reachable ⟨a, ha⟩ ⟨u, hu⟩
      refine ⟨A, ⟨?_, ⟨a, ?_⟩, ⟨b, hb, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
      · intro hcA; obtain ⟨h, _⟩ := (Finset.mem_filter.mp hcA).2; exact h rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, SimpleGraph.Reachable.refl _⟩
      · intro hbA; obtain ⟨_, hr⟩ := (Finset.mem_filter.mp hbA).2; exact hnr hr
      · intro u hu v hv hadj
        obtain ⟨hu', hru⟩ := (Finset.mem_filter.mp hu).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv,
          hru.trans (SimpleGraph.Adj.reachable hadj)⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, SimpleGraph.Reachable.refl _⟩
      · intro hbA; obtain ⟨_, hr⟩ := (Finset.mem_filter.mp hbA).2; exact hnr hr
      · intro u hu _; exact (Finset.mem_filter.mp hu).2.2
    -- Helper: in any cut-component `A` of `c`, every vertex outside `A ∪ {c}` reaches `c` in
    -- `G' \ A`!
    have hreach_outside : ∀ (c : {v : α | v ≠ w}) (A : Finset {v : α | v ≠ w}),
        IsCutComp c A → ∀ u : {v : α | v ≠ w}, u ∉ A →
        ∃ q : G'.Walk u c, ∀ v ∈ q.support, v ∉ A := by
      intro c A hA u hu
      obtain ⟨p⟩ := hG'conn u c
      -- Induction on walk length:
      suffices ∀ n (x : {v : α | v ≠ w}) (q : G'.Walk x c), q.length = n → x ∉ A →
          ∃ q' : G'.Walk x c, ∀ v ∈ q'.support, v ∉ A from this p.length u p rfl hu
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro x q hlen hx
        cases q with
        | nil =>
          exact ⟨.nil, fun v hv ↦ by
            simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
            exact hv ▸ hx⟩
        | @cons _ y _ hxy q₁ =>
          by_cases hyA : y ∈ A
          · -- Since `x ∉ A` and `G'.Adj x y` and `y ∈ A` is closed in `G' \ {c}`, `x = c`!
            have hxc : x = c := by
              by_contra hne
              exact hx (hA.2.2.2 y hyA x hne hxy.symm)
            subst hxc
            exact ⟨.nil, fun v hv ↦ by
              simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
              exact hv ▸ hx⟩
          · have hlt_n : q₁.length < n := by
              simp only [SimpleGraph.Walk.length_cons] at hlen; omega
            obtain ⟨q', hq'⟩ := ih q₁.length hlt_n y q₁ rfl hyA
            refine ⟨.cons hxy q', fun v hv ↦ ?_⟩
            rcases List.mem_cons.mp hv with rfl | hv'
            · exact hx
            · exact hq' v hv'
    -- Helper: `w` has a neighbor in EVERY cut-component `A` of `c` (since `G \ {c}` is connected)!
    have hw_nb_in : ∀ (c : {v : α | v ≠ w}) (A : Finset {v : α | v ≠ w}),
        IsCutComp c A → ∃ y ∈ A, G.Adj w y.1 := by
      intro c A hA
      by_contra hnone
      push Not at hnone
      obtain ⟨a, ha⟩ := hA.2.1
      obtain ⟨b, hbc, hbA⟩ := hA.2.2.1
      have hconn_c := h2conn c.1
      have ha_ne : a.1 ≠ c.1 := fun h ↦ hA.1 (Subtype.ext h ▸ ha)
      have hw_ne : w ≠ c.1 := c.2.symm
      obtain ⟨p⟩ := hconn_c ⟨a.1, ha_ne⟩ ⟨w, hw_ne⟩
      have hstay : ∀ {x y : {v : α | v ≠ c.1}} (q : (G.induce {v : α | v ≠ c.1}).Walk x y),
          (∃ hx : x.1 ≠ w, (⟨x.1, hx⟩ : {v : α | v ≠ w}) ∈ A) →
          ∃ hy : y.1 ≠ w, (⟨y.1, hy⟩ : {v : α | v ≠ w}) ∈ A := by
        intro x y q
        induction q with
        | nil => exact id
        | @cons x₁ y₁ z₁ hadj q' ih =>
          rintro ⟨hxw, hxA⟩
          have hyw : y₁.1 ≠ w := fun hEq ↦ hnone ⟨x₁.1, hxw⟩ hxA (by
            have hadj' : G.Adj x₁.1 y₁.1 := hadj; rw [hEq] at hadj'; exact hadj'.symm)
          have hyA : (⟨y₁.1, hyw⟩ : {v : α | v ≠ w}) ∈ A :=
            hA.2.2.2 ⟨x₁.1, hxw⟩ hxA ⟨y₁.1, hyw⟩ (fun h ↦ y₁.2 (congrArg Subtype.val h)) hadj
          exact ih ⟨hyw, hyA⟩
      obtain ⟨hww, _⟩ := hstay p ⟨a.2, ha⟩
      exact hww rfl
    -- Helper: if `A` is a minimal cut-component inside a universe `U ⊆ G'` (closed outside `c`),
    -- then for every `y ∈ A`, every `u ∈ A \ {y}` reaches `c` inside `A ∪ {c} \ {y}`!
    -- Even better: directly prove `∀ y ∈ A`, `u ∈ A \ {y}` reaches `c` in `G' \ {y}` via a walk
    -- inside `A ∪ {c} \ {y}`!
    have hmin_reach : ∀ (c : {v : α | v ≠ w}) (A : Finset {v : α | v ≠ w}) (hA : IsCutComp c A)
        (hmin : ∀ (c' : {v : α | v ≠ w}) (A' : Finset {v : α | v ≠ w}),
          IsCutComp c' A' → A' ⊆ A → A.card ≤ A'.card)
        (y : {v : α | v ≠ w}) (hy : y ∈ A) (u : {v : α | v ≠ w}) (hu : u ∈ A) (huy : u ≠ y),
        ∃ q : G'.Walk u c, ∀ v ∈ q.support, v ≠ y ∧ (v ∈ A ∨ v = c) := by
      intro c A hA hmin y hy u hu huy
      by_contra hno
      -- Every vertex in `G' \ A` reaches `c` inside `G' \ A` (hence avoiding `y ∈ A`),
      -- so the component `K` of `u` in `G' \ {y}` is contained in `A \ {y}`!
      have hnr : ¬ (G'.induce {v : {v : α | v ≠ w} | v ≠ y}).Reachable ⟨u, huy⟩
          ⟨c, fun h ↦ hA.1 (h ▸ hy)⟩ := by
        intro hr
        obtain ⟨q⟩ := hr
        -- Project `q` to a walk in `G'` from `u` to `c` avoiding `y`:
        let qG' : G'.Walk u c := q.map (SimpleGraph.Embedding.induce _).toHom
        have hq_av : ∀ v ∈ qG'.support, v ≠ y := by
          intro v hv
          have hsup : qG'.support = q.support.map Subtype.val := SimpleGraph.Walk.support_map _ q
          rw [hsup, List.mem_map] at hv
          obtain ⟨⟨z, hz⟩, _, rfl⟩ := hv; exact hz
        have hprefix : ∀ (x d : {v : α | v ≠ w}) (p : G'.Walk x d), d = c →
            x ∈ A → (∀ v ∈ p.support, v ≠ y) →
            ∃ p' : G'.Walk x c, ∀ v ∈ p'.support, v ≠ y ∧ (v ∈ A ∨ v = c) := by
          intro x d p
          induction p with
          | nil =>
            intro hd hxA _
            exact (hA.1 (hd ▸ hxA)).elim
          | @cons x₁ z₁ d₁ hxz p₁ ih =>
            intro hd hxA hpav; subst d₁
            by_cases hzc : z₁ = c
            · subst hzc
              refine ⟨.cons hxz .nil, fun v hv ↦ ?_⟩
              simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
                List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl
              · exact ⟨hpav _ (by simp), Or.inl hxA⟩
              · exact ⟨hpav _ (by simp), Or.inr rfl⟩
            · have hzA : z₁ ∈ A := hA.2.2.2 x₁ hxA z₁ hzc hxz
              obtain ⟨p', hp'⟩ := ih rfl hzA (fun v hv ↦ hpav v (List.mem_cons_of_mem _ hv))
              refine ⟨.cons hxz p', fun v hv ↦ ?_⟩
              rcases List.mem_cons.mp hv with rfl | hv'
              · exact ⟨hpav _ (by simp), Or.inl hxA⟩
              · exact hp' v hv'
        exact hno (hprefix u c qG' rfl hu hq_av)
      obtain ⟨K, hK, huK, hcK, hK_reach⟩ := mkCutComp y u c huy (fun h ↦ hA.1 (h ▸ hy)) hnr
      have hK_sub : K ⊆ A := by
        intro v hv
        by_contra hvA
        obtain ⟨qv, hqv⟩ := hreach_outside c A hA v hvA
        have hvc : v ≠ y := fun h ↦ hK.1 (h ▸ hv)
        have hqv_in : (G'.induce {z : {v : α | v ≠ w} | z ≠ y}).Reachable ⟨v, hvc⟩
            ⟨c, fun h ↦ hA.1 (h ▸ hy)⟩ := by
          have hlift : ∀ {a b : {v : α | v ≠ w}} (q : G'.Walk a b), (∀ z ∈ q.support, z ≠ y) →
              ∀ (ha : a ≠ y) (hb : b ≠ y),
              (G'.induce {z : {v : α | v ≠ w} | z ≠ y}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
            intro a b q
            induction q with
            | nil => intro _ _ _; exact SimpleGraph.Reachable.refl _
            | @cons a₁ b₁ _ hab q' ih =>
              intro hav ha _
              have hb : b₁ ≠ y :=
                hav b₁ (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support _))
              exact (SimpleGraph.Adj.reachable (G := G'.induce _) hab).trans
                (ih (fun z hz ↦ hav z (List.mem_cons_of_mem _ hz)) hb _)
          exact hlift qv (fun z hz hzy ↦ hqv z hz (hzy ▸ hy)) hvc _
        exact hnr ((hK_reach v hv hvc).trans hqv_in)
      have hcard_lt : K.card < A.card := by
        have hsub_er : K ⊆ A.erase y := fun v hv ↦
          Finset.mem_erase.mpr ⟨fun h ↦ hK.1 (h ▸ hv), hK_sub hv⟩
        have := Finset.card_le_card hsub_er
        rw [Finset.card_erase_of_mem hy] at this
        have := Finset.card_pos.mpr ⟨y, hy⟩; omega
      have := hmin y K hK hK_sub
      omega
    -- Now find `A₁` of globally minimum cardinality, and `A₂ ⊆ B` of minimum cardinality inside
    -- `B`!
    have hne_pairs : (Finset.univ.filter fun p : {v : α | v ≠ w} × Finset {v : α | v ≠ w} ↦
        IsCutComp p.1 p.2).Nonempty := by
      have hnc : ¬ (G'.induce {u : {v : α | v ≠ w} | u ≠ ⟨c₀, hwc₀.symm⟩}).Connected := by
        intro hc
        have : Nonempty {v : α | v ≠ w ∧ v ≠ c₀} := by
          obtain ⟨⟨⟨u, hu1⟩, hu2⟩⟩ := hc.nonempty
          exact ⟨⟨u, hu1, fun h ↦ hu2 (Subtype.ext h)⟩⟩
        refine hdisc₀ ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ?_⟩
        obtain ⟨q⟩ := hc.preconnected ⟨⟨a, ha.1⟩, fun h ↦ ha.2 (congrArg Subtype.val h)⟩
          ⟨⟨b, hb.1⟩, fun h ↦ hb.2 (congrArg Subtype.val h)⟩
        have hlift : ∀ {x y : {u : {v : α | v ≠ w} | u ≠ ⟨c₀, hwc₀.symm⟩}}
            (p : (G'.induce {u : {v : α | v ≠ w} | u ≠ ⟨c₀, hwc₀.symm⟩}).Walk x y),
            (G.induce {v : α | v ≠ w ∧
              v ≠ c₀}).Reachable ⟨x.1.1, x.1.2, fun h ↦ x.2 (Subtype.ext h)⟩
              ⟨y.1.1, y.1.2, fun h ↦ y.2 (Subtype.ext h)⟩ := by
          intro x y p
          induction p with
          | nil => exact SimpleGraph.Reachable.refl _
          | @cons x₁ y₁ _ hadj _ ih =>
            exact (SimpleGraph.Adj.reachable
              (show (G.induce {v : α | v ≠ w ∧ v ≠ c₀}).Adj
                ⟨x₁.1.1, x₁.1.2, fun h ↦ x₁.2 (Subtype.ext h)⟩
                ⟨y₁.1.1, y₁.1.2, fun h ↦ y₁.2 (Subtype.ext h)⟩ from hadj)).trans ih
        exact hlift q
      obtain ⟨a, b, ha, hb, hnr⟩ := hsub_eq ⟨c₀, hwc₀.symm⟩ hnc
      obtain ⟨A, hA, _, _, _⟩ := mkCutComp ⟨c₀, hwc₀.symm⟩ a b ha hb hnr
      exact ⟨(⟨c₀, hwc₀.symm⟩, A), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩⟩
    obtain ⟨⟨c₁, A₁⟩, hmem1, hmin1⟩ :=
      Finset.exists_min_image _ (fun p ↦ p.2.card) hne_pairs
    have hA₁ : IsCutComp c₁ A₁ := (Finset.mem_filter.mp hmem1).2
    obtain ⟨y, hyA₁, hwy⟩ := hw_nb_in c₁ A₁ hA₁
    -- Pick a second cut-component `B` of `c₁` disjoint from `A₁`:
    obtain ⟨b₀, hb₀c₁, hb₀A₁⟩ := hA₁.2.2.1
    have hnr_b₀ : ¬ (G'.induce {u : {v : α | v ≠ w} | u ≠ c₁}).Reachable ⟨b₀, hb₀c₁⟩
        ⟨Classical.choose hA₁.2.1, fun h ↦ hA₁.1 (h ▸ Classical.choose_spec hA₁.2.1)⟩ := by
      intro hr
      obtain ⟨q⟩ := hr.symm
      have hstay : ∀ {x y : {u : {v : α | v ≠ w} | u ≠ c₁}}
          (p : (G'.induce {u : {v : α | v ≠ w} | u ≠ c₁}).Walk x y), x.1 ∈ A₁ → y.1 ∈ A₁ := by
        intro x y p
        induction p with
        | nil => exact id
        | @cons x₁ y₁ _ hadj _ ih => intro hx; exact ih (hA₁.2.2.2 x₁.1 hx y₁.1 y₁.2 hadj)
      exact hb₀A₁ (hstay q (Classical.choose_spec hA₁.2.1))
    obtain ⟨B, hB, hb₀B, _, hB_reach⟩ := mkCutComp c₁ b₀ _ hb₀c₁ _ hnr_b₀
    have hA₁B_disj : Disjoint A₁ B := by
      rw [Finset.disjoint_left]
      intro u huA huB
      have huc : u ≠ c₁ := fun h ↦ hA₁.1 (h ▸ huA)
      obtain ⟨q⟩ := (hB_reach u huB huc).symm
      have hstay : ∀ {x y : {v : {v : α | v ≠ w} | v ≠ c₁}}
          (p : (G'.induce {v : {v : α | v ≠ w} | v ≠ c₁}).Walk x y), x.1 ∈ A₁ → y.1 ∈ A₁ := by
        intro x y p
        induction p with
        | nil => exact id
        | @cons x₁ y₁ _ hadj _ ih => intro hx; exact ih (hA₁.2.2.2 x₁.1 hx y₁.1 y₁.2 hadj)
      exact hb₀A₁ (hstay q huA)
    have hA₁_min : ∀ c' A', IsCutComp c' A' → A' ⊆ A₁ → A₁.card ≤ A'.card :=
      fun c' A' hA' _ ↦ hmin1 (c', A') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA'⟩)
    -- Now pick `(c₂, A₂)` minimal with `IsCutComp c₂ A₂ ∧ A₂ ⊆ B` (using `(c₁, B)` as witness!):
    let pairsB := Finset.univ.filter fun p : {v : α | v ≠ w} × Finset {v : α | v ≠ w} ↦
      IsCutComp p.1 p.2 ∧ p.2 ⊆ B
    have hneB : pairsB.Nonempty := ⟨(c₁, B), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB,
      Finset.Subset.refl B⟩⟩
    obtain ⟨⟨c₂, A₂⟩, hmem2, hmin2⟩ := Finset.exists_min_image pairsB (fun p ↦ p.2.card) hneB
    have hA₂ : IsCutComp c₂ A₂ := (Finset.mem_filter.mp hmem2).2.1
    have hA₂_sub : A₂ ⊆ B := (Finset.mem_filter.mp hmem2).2.2
    obtain ⟨z, hzA₂, hwz⟩ := hw_nb_in c₂ A₂ hA₂
    have hzB : z ∈ B := hA₂_sub hzA₂
    have hyz : y.1 ≠ z.1 := fun hEq ↦
      Finset.disjoint_left.mp hA₁B_disj hyA₁ (Subtype.ext hEq ▸ hzB)
    have hnayz : ¬ G.Adj y.1 z.1 := fun hadj ↦ by
      have hz_ne_c₁ : z ≠ c₁ := fun h ↦ hB.1 (h ▸ hzB)
      exact Finset.disjoint_left.mp hA₁B_disj (hA₁.2.2.2 y hyA₁ z hz_ne_c₁ hadj) hzB
    -- Prove `G' \ {y, z}` (i.e. `G \ {y, z}` excluding `w` — wait: we ALSO include `w`? No,
    -- `w = x` is NOT in `{y, z}` and `w` is adjacent to `y` and `z`, WAIT: is `G \ {y, z}`
    -- connected?! YES, because `G' \ {y, z}` is connected AND `w` has a neighbor in `G' \ {y, z}`
    -- since `deg_G(w) = k ≥ 3` so `w` has at least 1 neighbor outside `{y, z}`!)
    have hA₁A₂_disj : Disjoint A₁ A₂ := Disjoint.mono_right hA₂_sub hA₁B_disj
    have hc₁_not_A₂ : c₁ ∉ A₂ := fun h ↦ hB.1 (hA₂_sub h)
    have hc₂_not_A₁ : c₂ ∉ A₁ := by
      intro hc₂A₁
      -- `G'` is connected, so `c₂` must have a neighbor in `A₂ ⊆ B`!
      obtain ⟨a₂, ha₂⟩ := hA₂.2.1
      obtain ⟨q, hq⟩ := hreach_outside c₂ A₂ hA₂ c₂ hA₂.1
      -- Actually: pick a walk from `a₂` to `c₂` in `G'`; its last vertex in `A₂` is adjacent to
      -- `c₂`!
      obtain ⟨p⟩ := hG'conn a₂ c₂
      have hex_nb : ∃ u ∈ A₂, G'.Adj u c₂ := by
        suffices ∀ (a d : {v : α | v ≠ w}) (q : G'.Walk a d), d = c₂ →
            a ∈ A₂ → ∃ u ∈ A₂, G'.Adj u c₂ from this a₂ c₂ p rfl ha₂
        intro a d q
        induction q with
        | nil => intro hd ha; exact (hA₂.1 (hd ▸ ha)).elim
        | @cons a₁ b₁ d₁ hab q' ih =>
          intro hd ha; subst d₁
          by_cases hb : b₁ = c₂
          · exact ⟨a₁, ha, by rw [← hb]; exact hab⟩
          · exact ih rfl (hA₂.2.2.2 a₁ ha b₁ hb hab)
      obtain ⟨u, huA₂, huc₂⟩ := hex_nb
      have huB : u ∈ B := hA₂_sub huA₂
      have hu_ne : u ≠ c₁ := fun h ↦ hB.1 (h ▸ huB)
      have hc₂B : c₂ ∈ B := hB.2.2.2 u huB c₂ (fun h ↦ hA₁.1 (h ▸ hc₂A₁)) huc₂
      exact Finset.disjoint_left.mp hA₁B_disj hc₂A₁ hc₂B
    -- Helper: every `u ∈ G' \ (A₁ ∪ A₂)` reaches `c₁` inside `G' \ (A₁ ∪ A₂)`!
    have hmid_reach : ∀ u : {v : α | v ≠ w}, u ∉ A₁ → u ∉ A₂ →
        ∃ q : G'.Walk u c₁, ∀ v ∈ q.support, v ∉ A₁ ∧ v ∉ A₂ := by
      intro u hu1 hu2
      obtain ⟨q0, hq0⟩ := hreach_outside c₁ A₁ hA₁ u hu1
      suffices ∀ n (a : {v : α | v ≠ w}) (q : G'.Walk a c₁), q.length = n →
          (∀ v ∈ q.support, v ∉ A₁) → a ∉ A₂ →
          ∃ q' : G'.Walk a c₁, ∀ v ∈ q'.support, v ∉ A₁ ∧ v ∉ A₂ from
        this q0.length u q0 rfl hq0 hu2
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro a q hlen hqA₁ haA₂
        cases q with
        | nil =>
          exact ⟨.nil, fun v hv ↦ by
            simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
            exact hv ▸ ⟨hqA₁ _ (by simp), haA₂⟩⟩
        | @cons _ b₁ _ hab q₁ =>
          by_cases hbA₂ : b₁ ∈ A₂
          · -- Since `a ∉ A₂`, `G'.Adj a b₁`, `b₁ ∈ A₂`: `a = c₂`!
            have ha_c₂ : a = c₂ := by
              by_contra hne; exact haA₂ (hA₂.2.2.2 b₁ hbA₂ a hne hab.symm)
            -- Find the first vertex of `q₁` not in `A₂` (exists since endpoint `c₁ ∉ A₂`):
            have hdrop : ∀ (x d : {v : α | v ≠ w}) (r : G'.Walk x d), d = c₁ → x ∈ A₂ →
                ∃ (r' : G'.Walk c₂ c₁), r'.length < r.length + 1 ∧
                  (∀ v ∈ r'.support, v ∈ r.support) := by
              intro x d r
              induction r with
              | nil => intro hd hx; exact (hc₁_not_A₂ (hd ▸ hx)).elim
              | @cons x₁ y₁ d₁ hxy r₁ ih_r =>
                intro hd hx; subst d₁
                by_cases hy : y₁ ∈ A₂
                · obtain ⟨r', hr'len, hr'sub⟩ := ih_r rfl hy
                  exact ⟨r', by simp only [SimpleGraph.Walk.length_cons] at hr'len ⊢; omega,
                    fun v hv ↦ List.mem_cons_of_mem _ (hr'sub v hv)⟩
                · have hyc₂ : y₁ = c₂ := by
                    by_contra hne; exact hy (hA₂.2.2.2 x₁ hx y₁ hne hxy)
                  subst hyc₂
                  exact ⟨r₁, by simp, fun v hv ↦ List.mem_cons_of_mem _ hv⟩
            obtain ⟨r', hr'len, hr'sub⟩ := hdrop b₁ c₁ q₁ rfl hbA₂
            subst ha_c₂
            exact ih r'.length (by simp only [SimpleGraph.Walk.length_cons] at hlen; omega) a r'
              rfl (fun v hv ↦ hqA₁ v (List.mem_cons_of_mem _ (hr'sub v hv))) haA₂
          · obtain ⟨q', hq'⟩ := ih q₁.length
              (by simp only [SimpleGraph.Walk.length_cons] at hlen; omega)
              b₁ q₁ rfl (fun v hv ↦ hqA₁ v (List.mem_cons_of_mem _ hv)) hbA₂
            refine ⟨.cons hab q', fun v hv ↦ ?_⟩
            rcases List.mem_cons.mp hv with rfl | hv'
            · exact ⟨hqA₁ _ (by simp), haA₂⟩
            · exact hq' v hv'
    -- Lift any `G'.Walk a b` avoiding `y` and `z` to `G.induce {v | v ≠ y.1 ∧ v ≠ z.1}`:
    have hlift : ∀ {a b : {v : α | v ≠ w}} (q : G'.Walk a b),
        (∀ v ∈ q.support, v ≠ y ∧ v ≠ z) →
        ∀ (ha : a.1 ≠ y.1 ∧ a.1 ≠ z.1) (hb : b.1 ≠ y.1 ∧ b.1 ≠ z.1),
        (G.induce {v : α | v ≠ y.1 ∧ v ≠ z.1}).Reachable ⟨a.1, ha⟩ ⟨b.1, hb⟩ := by
      intro a b q
      induction q with
      | nil => intro _ _ _; exact SimpleGraph.Reachable.refl _
      | @cons a₁ b₁ _ hab q' ih =>
        intro hav ha hb
        have hb' : b₁.1 ≠ y.1 ∧ b₁.1 ≠ z.1 := by
          have := hav b₁ (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support _))
          exact ⟨fun h ↦ this.1 (Subtype.ext h), fun h ↦ this.2 (Subtype.ext h)⟩
        exact (SimpleGraph.Adj.reachable
          (show (G.induce {v : α | v ≠ y.1 ∧ v ≠ z.1}).Adj ⟨a₁.1, ha⟩ ⟨b₁.1, hb'⟩ from hab)).trans
          (ih (fun v hv ↦ hav v (List.mem_cons_of_mem _ hv)) hb' hb)
    -- `w` has a neighbor `w_nb` in `G' \ {y, z}` (since `deg_G(w) = k ≥ 3`):
    have hw_extra : ∃ u : {v : α | v ≠ w}, u ≠ y ∧ u ≠ z ∧ G.Adj w u.1 := by
      have hcard_nb : (G.neighborFinset w).card = k := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, hreg w]
      have h2_lt : ({y.1, z.1} : Finset α).card < (G.neighborFinset w).card := by
        rw [hcard_nb, Finset.card_pair hyz]; omega
      obtain ⟨u, hu_nb, hu_not⟩ := Finset.exists_mem_notMem_of_card_lt_card h2_lt
      have huw : u ≠ w := (G.ne_of_adj ((SimpleGraph.mem_neighborFinset _ _ _).mp hu_nb)).symm
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu_not
      exact ⟨⟨u, huw⟩, fun h ↦ hu_not.1 (congrArg Subtype.val h),
        fun h ↦ hu_not.2 (congrArg Subtype.val h), (SimpleGraph.mem_neighborFinset _ _ _).mp hu_nb⟩
    -- Every `u : G'` with `u ≠ y, u ≠ z` reaches `c₁` in `G \ {y, z}`!
    have hall_c₁ : ∀ (u : {v : α | v ≠ w}) (hu : u.1 ≠ y.1 ∧ u.1 ≠ z.1),
        (G.induce {v : α | v ≠ y.1 ∧ v ≠ z.1}).Reachable ⟨u.1, hu⟩
          ⟨c₁.1, fun h ↦ hA₁.1 (Subtype.ext h ▸ hyA₁),
                 fun h ↦ hc₁_not_A₂ (Subtype.ext h ▸ hzA₂)⟩ := by
      intro u hu
      have hc₁_yz : c₁.1 ≠ y.1 ∧ c₁.1 ≠ z.1 :=
        ⟨fun h ↦ hA₁.1 (Subtype.ext h ▸ hyA₁), fun h ↦ hc₁_not_A₂ (Subtype.ext h ▸ hzA₂)⟩
      have hc₂_yz : c₂.1 ≠ y.1 ∧ c₂.1 ≠ z.1 :=
        ⟨fun h ↦ hc₂_not_A₁ (Subtype.ext h ▸ hyA₁), fun h ↦ hA₂.1 (Subtype.ext h ▸ hzA₂)⟩
      by_cases hu1 : u ∈ A₁
      · obtain ⟨q, hq⟩ := hmin_reach c₁ A₁ hA₁ hA₁_min y hyA₁ u hu1
          (fun h ↦ hu.1 (congrArg Subtype.val h))
        refine hlift q (fun v hv ↦ ?_) hu hc₁_yz
        refine ⟨(hq v hv).1, fun hEq ↦ ?_⟩
        rcases (hq v hv).2 with hv1 | rfl
        · exact Finset.disjoint_left.mp hA₁A₂_disj hv1 (hEq ▸ hzA₂)
        · exact hc₁_not_A₂ (hEq ▸ hzA₂)
      · by_cases hu2 : u ∈ A₂
        · obtain ⟨q1, hq1⟩ := hmin_reach c₂ A₂ hA₂
            (fun c' A' hA' hsub ↦ hmin2 (c', A') (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hA', hsub.trans hA₂_sub⟩))
            z hzA₂ u hu2 (fun h ↦ hu.2 (congrArg Subtype.val h))
          have hr1 : (G.induce {v : α | v ≠ y.1 ∧ v ≠ z.1}).Reachable ⟨u.1, hu⟩ ⟨c₂.1, hc₂_yz⟩ := by
            refine hlift q1 (fun v hv ↦ ?_) hu hc₂_yz
            refine ⟨fun hEq ↦ ?_, (hq1 v hv).1⟩
            rcases (hq1 v hv).2 with hv2 | rfl
            · exact Finset.disjoint_left.mp hA₁A₂_disj (hEq ▸ hyA₁) hv2
            · exact hc₂_not_A₁ (hEq ▸ hyA₁)
          obtain ⟨q2, hq2⟩ := hmid_reach c₂ hc₂_not_A₁ hA₂.1
          have hr2 : (G.induce {v : α | v ≠ y.1 ∧ v ≠ z.1}).Reachable ⟨c₂.1, hc₂_yz⟩
              ⟨c₁.1, hc₁_yz⟩ :=
            hlift q2 (fun v hv ↦ ⟨fun h ↦ (hq2 v hv).1 (h ▸ hyA₁),
              fun h ↦ (hq2 v hv).2 (h ▸ hzA₂)⟩) hc₂_yz hc₁_yz
          exact hr1.trans hr2
        · obtain ⟨q, hq⟩ := hmid_reach u hu1 hu2
          exact hlift q (fun v hv ↦ ⟨fun h ↦ (hq v hv).1 (h ▸ hyA₁),
            fun h ↦ (hq v hv).2 (h ▸ hzA₂)⟩) hu hc₁_yz
    -- Conclude `(G.induce {v | v ≠ y.1 ∧ v ≠ z.1}).Connected`:
    have hGyz_conn : (G.induce {v : α | v ≠ y.1 ∧ v ≠ z.1}).Connected := by
      have hw_yz : w ≠ y.1 ∧ w ≠ z.1 := ⟨y.2.symm, z.2.symm⟩
      have hc₁_yz : c₁.1 ≠ y.1 ∧ c₁.1 ≠ z.1 :=
        ⟨fun h ↦ hA₁.1 (Subtype.ext h ▸ hyA₁), fun h ↦ hc₁_not_A₂ (Subtype.ext h ▸ hzA₂)⟩
      obtain ⟨u₀, hu₀y, hu₀z, hwu₀⟩ := hw_extra
      have hw_to_c₁ : (G.induce {v : α | v ≠ y.1 ∧ v ≠ z.1}).Reachable ⟨w, hw_yz⟩
          ⟨c₁.1, hc₁_yz⟩ :=
        (SimpleGraph.Adj.reachable (show (G.induce {v : α | v ≠ y.1 ∧ v ≠ z.1}).Adj ⟨w, hw_yz⟩
          ⟨u₀.1, fun h ↦ hu₀y (Subtype.ext h), fun h ↦ hu₀z (Subtype.ext h)⟩ from hwu₀)).trans
          (hall_c₁ u₀ ⟨fun h ↦ hu₀y (Subtype.ext h), fun h ↦ hu₀z (Subtype.ext h)⟩)
      have : Nonempty {v : α | v ≠ y.1 ∧ v ≠ z.1} := ⟨⟨w, hw_yz⟩⟩
      refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ?_⟩
      have ha_c₁ : (G.induce {v : α | v ≠ y.1 ∧ v ≠ z.1}).Reachable ⟨a, ha⟩ ⟨c₁.1, hc₁_yz⟩ := by
        by_cases haw : a = w
        · subst haw; exact hw_to_c₁
        · exact hall_c₁ ⟨a, haw⟩ ha
      have hb_c₁ : (G.induce {v : α | v ≠ y.1 ∧ v ≠ z.1}).Reachable ⟨b, hb⟩ ⟨c₁.1, hc₁_yz⟩ := by
        by_cases hbw : b = w
        · subst hbw; exact hw_to_c₁
        · exact hall_c₁ ⟨b, hbw⟩ hb
      exact ha_c₁.trans hb_c₁.symm
    exact ⟨w, y.1, z.1, hyz, hwy, hwz, hnayz, hGyz_conn⟩


end Cslib.Complexity
