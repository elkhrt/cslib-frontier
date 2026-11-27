module

public import CslibFrontier.Computability.Complexity.Problems.UndirectedEdgeGeography.Invariant

/-!
# Backward-Walk and Branch-Traversal Strategies for Undirected Edge Geography

Establishes the backward-walk winning lemmas (`wins_backwalk_u1`, `wins_backwalk_u2`) and the
forward branch-traversal lemmas (`walk_branch_wins`, `walk_branch_loses`) for the
Fraenkel–Scheinerman–Ullman reduction graph `formulaGraph`.

## Main results

* `Cslib.Complexity.UndirectedEdgeGeography.wins_backwalk_u1`, `wins_backwalk_u2`: backward
  walks along an untraversed branch always win.
* `Cslib.Complexity.UndirectedEdgeGeography.walk_branch_wins`, `walk_branch_loses`: clean and
  cheat-proof forward walks down a branch.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Cslib.Logic.PL

namespace UndirectedEdgeGeography

/-- If `w` is the unique legal move from `v` (every other neighbor already has its edge in `used`),
then `v` wins iff `w` loses after consuming `s(v, w)`. -/
theorem edgeGeographyWins_of_unique_move {G : Graph} {used : List (Sym2 ℕ)} {v w : ℕ}
    (hadj : G.toSimpleGraph.Adj v w) (hw : w ∈ G.vertices) (hnot : s(v, w) ∉ used)
    (huniq : ∀ u, G.toSimpleGraph.Adj v u → s(v, u) ∉ used → u = w) :
    EdgeGeographyWins G used v ↔ ¬EdgeGeographyWins G (s(v, w) :: used) w := by
  rw [edgeGeographyWins_iff]
  constructor
  · rintro ⟨u, hu, -, hnu, hlos⟩
    rwa [huniq u hu hnu] at hlos
  · intro hlos
    exact ⟨w, hadj, hw, hnot, hlos⟩

/-- If `w` is a legal move from `v` and every edge incident to `w` is already in
`s(v, w) :: used`, then the player to move at `v` wins immediately. -/
theorem edgeGeographyWins_of_adj_dead {G : Graph} {used : List (Sym2 ℕ)} {v w : ℕ}
    (hadj : G.toSimpleGraph.Adj v w) (hw : w ∈ G.vertices) (hnot : s(v, w) ∉ used)
    (hdead : ∀ u, G.toSimpleGraph.Adj w u → s(w, u) ∈ s(v, w) :: used) :
    EdgeGeographyWins G used v := by
  rw [edgeGeographyWins_iff]
  refine ⟨w, hadj, hw, hnot, ?_⟩
  rw [not_edgeGeographyWins_iff]
  intro u hu _ hnu
  exact absurd (hdead u hu) hnu

/-! ### Backward-walk winning lemmas -/

/-- Backward walk along an untraversed branch `b` from `u1Node j b k`. -/
theorem wins_backwalk_u1 {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {b : Bool}
    (hj : j < xs.length) :
    ∀ (k : ℕ), k < segCount xs ψ j b → ∀ (used : List (Sym2 ℕ)),
      (j % 2 = 0 →
        s(wNode j b, cNode j b) ∉ used ∧ s(cNode j b, u1Node j b 0) ∉ used ∧
        s(topNode j, aNode j b) ∉ used ∧ s(aNode j b, wNode j b) ∉ used ∧
        ((s(topNode j, wNode j (!b)) ∉ used ∧
          ∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j (!b)) u →
            s(wNode j (!b), u) ∈ s(topNode j, wNode j (!b)) :: used) ∨
         (s(topNode j, wNode j b) ∉ used ∧
          s(topNode j, aNode j (!b)) ∉ used ∧ s(aNode j (!b), wNode j (!b)) ∉ used ∧
          (∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j (!b)) u →
            s(wNode j (!b), u) ∈ s(aNode j (!b), wNode j (!b)) :: used) ∧
          (∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) u →
            u = aNode j b ∨ u = aNode j (!b) ∨
              s(topNode j, u) ∈ s(wNode j b, topNode j) :: used)))) →
      (j % 2 = 1 → s(topNode j, u1Node j b 0) ∉ used ∧
        (∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) u →
          s(topNode j, u) ∈ s(topNode j, u1Node j b 0) :: used)) →
      (∀ t < k,
        s(u2Node j b t, vNode j b t) ∉ used ∧ s(vNode j b t, u1Node j b (t + 1)) ∉ used ∧
        s(u1Node j b t, mNode j b t) ∉ used ∧ s(mNode j b t, u2Node j b t) ∉ used) →
      EdgeGeographyWins (formulaGraph xs ψ) used (u1Node j b k)
  | 0, hk, used, heven, hodd, _ => by
    rcases Nat.mod_two_eq_zero_or_one j with hpar | hpar
    · obtain ⟨hwc, hcu, hta, haw, htop⟩ := heven hpar
      have hadj_uc : (formulaGraph xs ψ).toSimpleGraph.Adj (u1Node j b 0) (cNode j b) :=
        (adj_cNode_iff hj hpar).2 (Or.inr rfl) |>.symm
      rw [edgeGeographyWins_iff]
      refine ⟨cNode j b, hadj_uc, mem_vertices_of_adj hadj_uc, by rwa [Sym2.eq_swap], ?_⟩
      have hadj_cw : (formulaGraph xs ψ).toSimpleGraph.Adj (cNode j b) (wNode j b) :=
        (adj_cNode_iff hj hpar).2 (Or.inl rfl)
      rw [edgeGeographyWins_of_unique_move hadj_cw (mem_vertices_of_adj hadj_cw) (by
        simp only [List.mem_cons, not_or]
        exact ⟨sym2_ne_of_tags (by decide), by rwa [Sym2.eq_swap]⟩)
        (fun u hu hnu => by
          rw [adj_cNode_iff hj hpar] at hu
          rcases hu with rfl | rfl
          · rfl
          · exact absurd (Sym2.eq_swap ▸ List.mem_cons_self) hnu)]
      rw [not_not]
      rcases htop with ⟨htw, hdead⟩ | ⟨htw_b, hta', haw', hdead, htop_dead⟩
      · have hadj_wa : (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j b) (aNode j b) :=
          (adj_wNode_iff hj hpar).2 (Or.inl rfl)
        rw [edgeGeographyWins_iff]
        refine ⟨aNode j b, hadj_wa, mem_vertices_of_adj hadj_wa, by
          simp only [List.mem_cons, not_or]
          exact ⟨sym2_ne_of_tags (by decide),
            sym2_ne_of_tags (by decide), by rwa [Sym2.eq_swap]⟩, ?_⟩
        have hadj_at : (formulaGraph xs ψ).toSimpleGraph.Adj (aNode j b) (topNode j) :=
          (adj_aNode_iff hj hpar).2 (Or.inl rfl)
        rw [edgeGeographyWins_of_unique_move hadj_at (mem_vertices_of_adj hadj_at) (by
          simp only [List.mem_cons, not_or]
          exact ⟨sym2_ne_of_tags (by decide),
            sym2_ne_of_tags (by decide),
            sym2_ne_of_tags (by decide), by rwa [Sym2.eq_swap]⟩)
          (fun u hu hnu => by
            rw [adj_aNode_iff hj hpar] at hu
            rcases hu with rfl | rfl
            · rfl
            · exact absurd (Sym2.eq_swap ▸ List.mem_cons_self) hnu)]
        rw [not_not]
        have hadj_tw : (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) (wNode j (!b)) :=
          (adj_topNode_iff (le_of_lt hj)).2 (Or.inr (Or.inl ⟨hj, hpar, !b, Or.inr rfl⟩))
        refine edgeGeographyWins_of_adj_dead hadj_tw (mem_vertices_of_adj hadj_tw) ?_ ?_
        · simp only [List.mem_cons, not_or]
          refine ⟨sym2_ne_of_tags (by decide), ?_,
            sym2_ne_of_tags (by decide),
            sym2_ne_of_tags (by decide), htw⟩
          intro h
          rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact pair_ne_of_ne (by decide) h1
          · exact pair_ne_of_ne (by decide) h1
        · intro u hu
          simp only [List.mem_cons]
          rcases List.mem_cons.1 (hdead u hu) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · have hadj_wt : (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j b) (topNode j) :=
          (adj_wNode_iff hj hpar).2 (Or.inr (Or.inl rfl))
        rw [edgeGeographyWins_iff]
        refine ⟨topNode j, hadj_wt, mem_vertices_of_adj hadj_wt, by
          simp only [List.mem_cons, not_or]
          exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            by rwa [Sym2.eq_swap]⟩, ?_⟩
        rw [not_edgeGeographyWins_iff]
        intro u hu _ hnu
        rcases htop_dead u hu with rfl | rfl | hd
        · have hadj_aw : (formulaGraph xs ψ).toSimpleGraph.Adj (aNode j b) (wNode j b) :=
            (adj_aNode_iff hj hpar).2 (Or.inr rfl)
          refine edgeGeographyWins_of_adj_dead hadj_aw (mem_vertices_of_adj hadj_aw) ?_ ?_
          · simp only [List.mem_cons, not_or]
            exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
              sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide), haw⟩
          · intro x hx
            rw [adj_wNode_iff hj hpar] at hx
            rcases hx with rfl | rfl | rfl
            · rw [Sym2.eq_swap]; exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (by rw [Sym2.eq_swap]; exact List.mem_cons_self)))
        · have hadj_aw' : (formulaGraph xs ψ).toSimpleGraph.Adj (aNode j (!b)) (wNode j (!b)) :=
            (adj_aNode_iff hj hpar).2 (Or.inr rfl)
          refine edgeGeographyWins_of_adj_dead hadj_aw' (mem_vertices_of_adj hadj_aw') ?_ ?_
          · simp only [List.mem_cons, not_or]
            exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
              sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide), haw'⟩
          · intro x hx
            simp only [List.mem_cons]
            rcases List.mem_cons.1 (hdead x hx) with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
        · rcases List.mem_cons.1 hd with h | h
          · exact absurd (by rw [h, Sym2.eq_swap]; exact List.mem_cons_self) hnu
          · exact absurd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ h))) hnu
    · obtain ⟨htu, hdead⟩ := hodd hpar
      have hadj_ut : (formulaGraph xs ψ).toSimpleGraph.Adj (u1Node j b 0) (topNode j) :=
        (adj_u1Node_iff hj hk).2 (Or.inl ⟨rfl, Or.inr ⟨hpar, rfl⟩⟩)
      refine edgeGeographyWins_of_adj_dead hadj_ut (mem_vertices_of_adj hadj_ut)
        (by rwa [Sym2.eq_swap]) (fun u hu => ?_)
      have h := hdead u hu
      rwa [Sym2.eq_swap (a := topNode j)] at h
  | k + 1, hk, used, heven, hodd, hseg => by
    obtain ⟨huv, hvu, hum, hmu⟩ := hseg k (Nat.lt_succ_self k)
    have hk' : k < segCount xs ψ j b - 1 := by omega
    have hadj_uv : (formulaGraph xs ψ).toSimpleGraph.Adj (u1Node j b (k + 1)) (vNode j b k) :=
      (adj_vNode_iff hj hk').2 (Or.inr rfl) |>.symm
    rw [edgeGeographyWins_iff]
    refine ⟨vNode j b k, hadj_uv, mem_vertices_of_adj hadj_uv, by rwa [Sym2.eq_swap], ?_⟩
    have hadj_vu : (formulaGraph xs ψ).toSimpleGraph.Adj (vNode j b k) (u2Node j b k) :=
      (adj_vNode_iff hj hk').2 (Or.inl rfl)
    rw [edgeGeographyWins_of_unique_move hadj_vu (mem_vertices_of_adj hadj_vu) (by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide), by rwa [Sym2.eq_swap]⟩)
      (fun u hu hnu => by
        rw [adj_vNode_iff hj hk'] at hu
        rcases hu with rfl | rfl
        · rfl
        · exact absurd (Sym2.eq_swap ▸ List.mem_cons_self) hnu)]
    rw [not_not]
    have hadj_um : (formulaGraph xs ψ).toSimpleGraph.Adj (u2Node j b k) (mNode j b k) :=
      (adj_mNode_iff hj (by omega)).2 (Or.inr rfl) |>.symm
    rw [edgeGeographyWins_iff]
    refine ⟨mNode j b k, hadj_um, mem_vertices_of_adj hadj_um, by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide),
        sym2_ne_of_tags (by decide), by rwa [Sym2.eq_swap]⟩, ?_⟩
    have hadj_mu : (formulaGraph xs ψ).toSimpleGraph.Adj (mNode j b k) (u1Node j b k) :=
      (adj_mNode_iff hj (by omega)).2 (Or.inl rfl)
    rw [edgeGeographyWins_of_unique_move hadj_mu (mem_vertices_of_adj hadj_mu) (by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide),
        sym2_ne_of_tags (by decide),
        sym2_ne_of_tags (by decide), by rwa [Sym2.eq_swap]⟩)
      (fun u hu hnu => by
        rw [adj_mNode_iff hj (by omega)] at hu
        rcases hu with rfl | rfl
        · rfl
        · exact absurd (Sym2.eq_swap ▸ List.mem_cons_self) hnu)]
    rw [not_not]
    have hnot4 : ∀ {e : Sym2 ℕ},
        e ≠ s(mNode j b k, u1Node j b k) → e ≠ s(u2Node j b k, mNode j b k) →
        e ≠ s(vNode j b k, u2Node j b k) → e ≠ s(u1Node j b (k + 1), vNode j b k) →
        e ∉ used →
        e ∉ s(mNode j b k, u1Node j b k) :: s(u2Node j b k, mNode j b k) ::
            s(vNode j b k, u2Node j b k) :: s(u1Node j b (k + 1), vNode j b k) :: used := by
      intro e h1 h2 h3 h4 h5; simp [List.mem_cons, h1, h2, h3, h4, h5]
    refine wins_backwalk_u1 hj k (by omega) _ ?_ ?_ ?_
    · intro hpar
      obtain ⟨hwc, hcu, hta, haw, htop⟩ := heven hpar
      refine ⟨hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) hwc,
        hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) hcu,
        hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) hta,
        hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) haw, ?_⟩
      rcases htop with ⟨htw, hdead⟩ | ⟨htw_b, hta', haw', hdead, htop_dead⟩
      · left
        refine ⟨hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) htw,
          fun u hu => ?_⟩
        simp only [List.mem_cons]
        rcases List.mem_cons.1 (hdead u hu) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · right
        refine ⟨hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) htw_b,
          hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) hta',
          hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) haw',
          fun u hu => ?_, fun u hu => ?_⟩
        · simp only [List.mem_cons]
          rcases List.mem_cons.1 (hdead u hu) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
        · rcases htop_dead u hu with h | h | hd
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · right; right; simp only [List.mem_cons]
            rcases List.mem_cons.1 hd with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · intro hpar
      obtain ⟨htu, hdead⟩ := hodd hpar
      refine ⟨hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) htu,
        fun u hu => ?_⟩
      simp only [List.mem_cons]
      rcases List.mem_cons.1 (hdead u hu) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · intro t ht
      obtain ⟨h1, h2, h3, h4⟩ := hseg t (by omega)
      have htk : t ≠ k := by omega
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        · refine hnot4 ?_ ?_ ?_ ?_ (by assumption) <;>
          · intro h; rcases pair_sym2_eq h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
              first
              | exact pair_ne_of_ne (by decide) ha
              | exact pair_ne_of_ne (by decide) hb
              | (simp only [u1Node_eq_pair, u2Node_eq_pair, Nat.pair_eq_pair] at ha hb; omega)

/-- Companion backward-walk lemma from `u2Node j b k`. -/
theorem wins_backwalk_u2 {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {b : Bool}
    (hj : j < xs.length) (k : ℕ) (hk : k < segCount xs ψ j b) (used : List (Sym2 ℕ))
    (heven : j % 2 = 0 →
      s(wNode j b, cNode j b) ∉ used ∧ s(cNode j b, u1Node j b 0) ∉ used ∧
      s(topNode j, aNode j b) ∉ used ∧ s(aNode j b, wNode j b) ∉ used ∧
      ((s(topNode j, wNode j (!b)) ∉ used ∧
        ∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j (!b)) u →
          s(wNode j (!b), u) ∈ s(topNode j, wNode j (!b)) :: used) ∨
       (s(topNode j, wNode j b) ∉ used ∧
        s(topNode j, aNode j (!b)) ∉ used ∧ s(aNode j (!b), wNode j (!b)) ∉ used ∧
        (∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j (!b)) u →
          s(wNode j (!b), u) ∈ s(aNode j (!b), wNode j (!b)) :: used) ∧
        (∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) u →
          u = aNode j b ∨ u = aNode j (!b) ∨
            s(topNode j, u) ∈ s(wNode j b, topNode j) :: used))))
    (hodd : j % 2 = 1 → s(topNode j, u1Node j b 0) ∉ used ∧
      (∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) u →
        s(topNode j, u) ∈ s(topNode j, u1Node j b 0) :: used))
    (hseg : ∀ t ≤ k,
      s(u1Node j b t, mNode j b t) ∉ used ∧ s(mNode j b t, u2Node j b t) ∉ used)
    (hconn : ∀ t < k,
      s(u2Node j b t, vNode j b t) ∉ used ∧ s(vNode j b t, u1Node j b (t + 1)) ∉ used) :
    EdgeGeographyWins (formulaGraph xs ψ) used (u2Node j b k) := by
  obtain ⟨hum, hmu⟩ := hseg k le_rfl
  have hadj_u2m : (formulaGraph xs ψ).toSimpleGraph.Adj (u2Node j b k) (mNode j b k) :=
    (adj_mNode_iff hj hk).2 (Or.inr rfl) |>.symm
  rw [edgeGeographyWins_iff]
  refine ⟨mNode j b k, hadj_u2m, mem_vertices_of_adj hadj_u2m, by rwa [Sym2.eq_swap], ?_⟩
  have hadj_mu1 : (formulaGraph xs ψ).toSimpleGraph.Adj (mNode j b k) (u1Node j b k) :=
    (adj_mNode_iff hj hk).2 (Or.inl rfl)
  rw [edgeGeographyWins_of_unique_move hadj_mu1 (mem_vertices_of_adj hadj_mu1) (by
    simp only [List.mem_cons, not_or]
    exact ⟨sym2_ne_of_tags (by decide), by rwa [Sym2.eq_swap]⟩)
    (fun u hu hnu => by
      rw [adj_mNode_iff hj hk] at hu
      rcases hu with rfl | rfl
      · rfl
      · exact absurd (Sym2.eq_swap ▸ List.mem_cons_self) hnu)]
  rw [not_not]
  have hnot2 : ∀ {e : Sym2 ℕ},
      e ≠ s(mNode j b k, u1Node j b k) → e ≠ s(u2Node j b k, mNode j b k) → e ∉ used →
      e ∉ s(mNode j b k, u1Node j b k) :: s(u2Node j b k, mNode j b k) :: used := by
    intro e h1 h2 h3; simp [List.mem_cons, h1, h2, h3]
  refine wins_backwalk_u1 hj k hk _ ?_ ?_ ?_
  · intro hpar
    obtain ⟨hwc, hcu, hta, haw, htop⟩ := heven hpar
    refine ⟨hnot2 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) hwc,
      hnot2 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) hcu,
      hnot2 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) hta,
      hnot2 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) haw, ?_⟩
    rcases htop with ⟨htw, hdead⟩ | ⟨htw_b, hta', haw', hdead, htop_dead⟩
    · left
      refine ⟨hnot2 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) htw,
        fun u hu => ?_⟩
      simp only [List.mem_cons]
      rcases List.mem_cons.1 (hdead u hu) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
    · right
      refine ⟨hnot2 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) htw_b,
        hnot2 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) hta',
        hnot2 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) haw',
        fun u hu => ?_, fun u hu => ?_⟩
      · simp only [List.mem_cons]
        rcases List.mem_cons.1 (hdead u hu) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))
      · rcases htop_dead u hu with h | h | hd
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · right; right; simp only [List.mem_cons]
          rcases List.mem_cons.1 hd with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
  · intro hpar
    obtain ⟨htu, hdead⟩ := hodd hpar
    refine ⟨hnot2 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) htu,
      fun u hu => ?_⟩
    simp only [List.mem_cons]
    rcases List.mem_cons.1 (hdead u hu) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · intro t ht
    obtain ⟨h1, h2⟩ := hseg t (le_of_lt ht)
    obtain ⟨h3, h4⟩ := hconn t ht
    have htk : t ≠ k := by omega
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · refine hnot2 ?_ ?_ (by assumption) <;>
        · intro h; rcases pair_sym2_eq h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
            first
            | exact pair_ne_of_ne (by decide) ha
            | exact pair_ne_of_ne (by decide) hb
            | exact htk (by
                simp only [mNode_eq_pair, u1Node_eq_pair, Nat.pair_eq_pair, true_and] at ha
                exact ha)

theorem validUsed_even_backwalk_hyp {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {used : List (Sym2 ℕ)} (hV : ValidUsed xs ψ z used) {j : ℕ} (hj : j < z.length)
    (hjx : j < xs.length) (hpar : j % 2 = 0) :
    let b := !z[j]
    s(wNode j b, cNode j b) ∉ used ∧ s(cNode j b, u1Node j b 0) ∉ used ∧
    s(topNode j, aNode j b) ∉ used ∧ s(aNode j b, wNode j b) ∉ used ∧
    ((s(topNode j, wNode j (!b)) ∉ used ∧
      ∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j (!b)) u →
        s(wNode j (!b), u) ∈ s(topNode j, wNode j (!b)) :: used) ∨
     (s(topNode j, wNode j b) ∉ used ∧
      s(topNode j, aNode j (!b)) ∉ used ∧ s(aNode j (!b), wNode j (!b)) ∉ used ∧
      (∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j (!b)) u →
        s(wNode j (!b), u) ∈ s(aNode j (!b), wNode j (!b)) :: used) ∧
      (∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) u →
        u = aNode j b ∨ u = aNode j (!b) ∨
          s(topNode j, u) ∈ s(wNode j b, topNode j) :: used))) := by
  obtain ⟨hwc_c, hcu_c, -, -, h3, hta_u, haw_u, htw_u, hwc_u, hcu_u⟩ := (hV.1 j hj).1 hpar
  dsimp only
  refine ⟨hwc_u, hcu_u, hta_u, haw_u, ?_⟩
  rcases h3 with ⟨hta_c, haw_c, htw_c⟩ | ⟨htw_c, hta_c, haw_c⟩
  · left
    refine ⟨by simpa using htw_c, fun u hu => ?_⟩
    rw [adj_wNode_iff hjx hpar] at hu
    simp only [Bool.not_not] at hu ⊢
    rcases hu with rfl | rfl | rfl
    · exact List.mem_cons_of_mem _ (by rw [Sym2.eq_swap]; exact haw_c)
    · rw [Sym2.eq_swap]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hwc_c
  · right
    refine ⟨htw_u, by simpa using hta_c, by simpa using haw_c, fun u hu => ?_, fun u hu => ?_⟩
    · rw [adj_wNode_iff hjx hpar] at hu
      simp only [Bool.not_not] at hu ⊢
      rcases hu with rfl | rfl | rfl
      · rw [Sym2.eq_swap]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (by rw [Sym2.eq_swap]; exact htw_c)
      · exact List.mem_cons_of_mem _ hwc_c
    · rw [adj_topNode_iff (le_of_lt hjx)] at hu
      rcases hu with ⟨hpos, ⟨hp', rfl⟩ | ⟨hp', rfl⟩⟩ | ⟨-, -, b', rfl | rfl⟩ | ⟨-, hp', _⟩ |
        ⟨he, _⟩
      · right; right; apply List.mem_cons_of_mem
        have := ((hV.1 (j - 1) (by omega)).1 hp').2.2.2.1
        rwa [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this
      · right; right; apply List.mem_cons_of_mem
        have := ((hV.1 (j - 1) (by omega)).2.1 hp').2
        rwa [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this
      · by_cases hb' : b' = z[j]
        · subst hb'; right; left; simp
        · left; congr 1; cases hzj : z[j] <;> cases b' <;> simp_all
      · right; right
        by_cases hb' : b' = z[j]
        · subst hb'; exact List.mem_cons_of_mem _ htw_c
        · have : b' = !z[j] := by cases hzj : z[j] <;> cases b' <;> simp_all
          subst this; rw [Sym2.eq_swap]; exact List.mem_cons_self
      · omega
      · omega

theorem validUsed_dead_topNode_odd {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {used : List (Sym2 ℕ)} (hV : ValidUsed xs ψ z used) {j : ℕ} (hj : j < z.length)
    (hz : z.length ≤ xs.length) (hpar : j % 2 = 1) :
    ∀ u, (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) u →
      s(topNode j, u) ∈ s(topNode j, u1Node j (!z[j]) 0) :: used := by
  intro u hadj
  rw [adj_topNode_iff (by omega)] at hadj
  rcases hadj with ⟨hpos, ⟨hpar', rfl⟩ | ⟨hpar', rfl⟩⟩ | ⟨-, hpar', _⟩ | ⟨-, -, b, rfl⟩ | ⟨h, _⟩
  · have hj1 : j - 1 < z.length := by omega
    exact List.mem_cons_of_mem _ (by
      have := ((hV.1 (j - 1) hj1).1 hpar').2.2.2.1
      rwa [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this)
  · omega
  · omega
  · by_cases hb : b = z[j]
    · subst hb
      exact List.mem_cons_of_mem _ ((hV.1 j hj).2.1 hpar).1
    · have : b = !z[j] := by cases b <;> cases hzj : z[j] <;> simp_all
      subst this
      exact List.mem_cons_self
  · omega

/-! ### Forward walks down a branch -/

/-- Walking cleanly down branch `(j, b)` from `u1Node j b k` to `botNode j`. -/
theorem walk_branch_wins {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {b : Bool}
    (hj : j < xs.length) :
    ∀ (m k : ℕ), 0 < m → k + m = segCount xs ψ j b → ∀ (used : List (Sym2 ℕ)),
      (∀ t, k ≤ t → t < segCount xs ψ j b →
        s(u1Node j b t, mNode j b t) ∉ used ∧ s(mNode j b t, u2Node j b t) ∉ used) →
      (∀ t, k ≤ t → t < segCount xs ψ j b - 1 →
        s(u2Node j b t, vNode j b t) ∉ used ∧ s(vNode j b t, u1Node j b (t + 1)) ∉ used) →
      s(u2Node j b (segCount xs ψ j b - 1), botNode j) ∉ used →
      (∀ used' : List (Sym2 ℕ),
        (∀ e, e ∈ used' ↔
          e ∈ used ∨
          (∃ t, k ≤ t ∧ t < segCount xs ψ j b ∧
            (e = s(u1Node j b t, mNode j b t) ∨ e = s(mNode j b t, u2Node j b t))) ∨
          (∃ t, k ≤ t ∧ t < segCount xs ψ j b - 1 ∧
            (e = s(u2Node j b t, vNode j b t) ∨ e = s(vNode j b t, u1Node j b (t + 1)))) ∨
          e = s(u2Node j b (segCount xs ψ j b - 1), botNode j)) →
        ¬ EdgeGeographyWins (formulaGraph xs ψ) used' (botNode j)) →
      EdgeGeographyWins (formulaGraph xs ψ) used (u1Node j b k)
  | 0, _, hm, _, _, _, _, _, _ => absurd hm (Nat.not_lt_zero _)
  | 1, k, _, hkm, used, hseg, hconn, hbot, hfin => by
    have hk_eq : k = segCount xs ψ j b - 1 := by omega
    have hk : k < segCount xs ψ j b := by omega
    obtain ⟨hum, hmu⟩ := hseg k le_rfl hk
    have hadj_um : (formulaGraph xs ψ).toSimpleGraph.Adj (u1Node j b k) (mNode j b k) :=
      (adj_mNode_iff hj hk).2 (Or.inl rfl) |>.symm
    rw [edgeGeographyWins_iff]
    refine ⟨mNode j b k, hadj_um, mem_vertices_of_adj hadj_um, hum, ?_⟩
    have hadj_mu : (formulaGraph xs ψ).toSimpleGraph.Adj (mNode j b k) (u2Node j b k) :=
      (adj_mNode_iff hj hk).2 (Or.inr rfl)
    rw [edgeGeographyWins_of_unique_move hadj_mu (mem_vertices_of_adj hadj_mu) (by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide), hmu⟩)
      (fun u hu hnu => by
        rw [adj_mNode_iff hj hk] at hu
        rcases hu with rfl | rfl
        · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnu
        · rfl)]
    rw [not_not]
    have hadj_ub : (formulaGraph xs ψ).toSimpleGraph.Adj (u2Node j b k) (botNode j) :=
      (adj_u2Node_iff hj hk).2 (Or.inr (Or.inr (Or.inl ⟨hk_eq, rfl⟩)))
    rw [edgeGeographyWins_iff]
    refine ⟨botNode j, hadj_ub, mem_vertices_of_adj hadj_ub, ?_, ?_⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
        hk_eq ▸ hbot⟩
    · refine hfin _ fun e => ?_
      simp only [List.mem_cons]
      constructor
      · rintro (rfl | rfl | rfl | h)
        · exact Or.inr (Or.inr (Or.inr (hk_eq ▸ rfl)))
        · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inr rfl⟩)
        · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inl rfl⟩)
        · exact Or.inl h
      · rintro (h | ⟨t, ht1, ht2, rfl | rfl⟩ | ⟨t, ht1, ht2, _⟩ | rfl)
        · exact Or.inr (Or.inr (Or.inr h))
        · have : t = k := by omega
          subst this; exact Or.inr (Or.inr (Or.inl rfl))
        · have : t = k := by omega
          subst this; exact Or.inr (Or.inl rfl)
        · omega
        · exact Or.inl (hk_eq ▸ rfl)
  | m + 2, k, _, hkm, used, hseg, hconn, hbot, hfin => by
    have hk : k < segCount xs ψ j b := by omega
    have hk' : k < segCount xs ψ j b - 1 := by omega
    obtain ⟨hum, hmu⟩ := hseg k le_rfl hk
    obtain ⟨huv, hvu⟩ := hconn k le_rfl hk'
    have hadj_um : (formulaGraph xs ψ).toSimpleGraph.Adj (u1Node j b k) (mNode j b k) :=
      (adj_mNode_iff hj hk).2 (Or.inl rfl) |>.symm
    rw [edgeGeographyWins_iff]
    refine ⟨mNode j b k, hadj_um, mem_vertices_of_adj hadj_um, hum, ?_⟩
    have hadj_mu : (formulaGraph xs ψ).toSimpleGraph.Adj (mNode j b k) (u2Node j b k) :=
      (adj_mNode_iff hj hk).2 (Or.inr rfl)
    rw [edgeGeographyWins_of_unique_move hadj_mu (mem_vertices_of_adj hadj_mu) (by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide), hmu⟩)
      (fun u hu hnu => by
        rw [adj_mNode_iff hj hk] at hu
        rcases hu with rfl | rfl
        · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnu
        · rfl)]
    rw [not_not]
    have hadj_uv : (formulaGraph xs ψ).toSimpleGraph.Adj (u2Node j b k) (vNode j b k) :=
      (adj_vNode_iff hj hk').2 (Or.inl rfl) |>.symm
    rw [edgeGeographyWins_iff]
    refine ⟨vNode j b k, hadj_uv, mem_vertices_of_adj hadj_uv, by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide),
        sym2_ne_of_tags (by decide), huv⟩, ?_⟩
    have hadj_vu : (formulaGraph xs ψ).toSimpleGraph.Adj (vNode j b k) (u1Node j b (k + 1)) :=
      (adj_vNode_iff hj hk').2 (Or.inr rfl)
    rw [edgeGeographyWins_of_unique_move hadj_vu (mem_vertices_of_adj hadj_vu) (by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide),
        sym2_ne_of_tags (by decide),
        sym2_ne_of_tags (by decide), hvu⟩)
      (fun u hu hnu => by
        rw [adj_vNode_iff hj hk'] at hu
        rcases hu with rfl | rfl
        · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnu
        · rfl)]
    rw [not_not]
    have hnot4 : ∀ {e : Sym2 ℕ},
        e ≠ s(vNode j b k, u1Node j b (k + 1)) → e ≠ s(u2Node j b k, vNode j b k) →
        e ≠ s(mNode j b k, u2Node j b k) → e ≠ s(u1Node j b k, mNode j b k) → e ∉ used →
        e ∉ s(vNode j b k, u1Node j b (k + 1)) :: s(u2Node j b k, vNode j b k) ::
            s(mNode j b k, u2Node j b k) :: s(u1Node j b k, mNode j b k) :: used := by
      intro e h1 h2 h3 h4 h5; simp [List.mem_cons, h1, h2, h3, h4, h5]
    refine walk_branch_wins hj (m + 1) (k + 1) (Nat.succ_pos _) (by omega) _ ?_ ?_ ?_ ?_
    · intro t ht1 ht2
      obtain ⟨h1, h2⟩ := hseg t (by omega) ht2
      have htk : t ≠ k := by omega
      refine ⟨?_, ?_⟩ <;>
        · refine hnot4 ?_ ?_ ?_ ?_ (by assumption) <;>
          · intro h; rcases pair_sym2_eq h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
              first
              | exact pair_ne_of_ne (by decide) ha
              | exact pair_ne_of_ne (by decide) hb
              | (simp only [u1Node_eq_pair, u2Node_eq_pair, Nat.pair_eq_pair] at ha hb; omega)
    · intro t ht1 ht2
      obtain ⟨h1, h2⟩ := hconn t (by omega) ht2
      have htk : t ≠ k := by omega
      refine ⟨?_, ?_⟩ <;>
        · refine hnot4 ?_ ?_ ?_ ?_ (by assumption) <;>
          · intro h; rcases pair_sym2_eq h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
              first
              | exact pair_ne_of_ne (by decide) ha
              | exact pair_ne_of_ne (by decide) hb
              | (simp only [u1Node_eq_pair, u2Node_eq_pair, Nat.pair_eq_pair] at ha hb; omega)
    · refine hnot4 (sym2_ne_of_tags (by decide))
        (by intro h; rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
            · exact pair_ne_of_ne (by decide) hb
            · exact pair_ne_of_ne (by decide) ha)
        (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) hbot
    · intro used' hused'
      refine hfin used' fun e => ?_
      rw [hused']
      simp only [List.mem_cons]
      constructor
      · rintro ((rfl | rfl | rfl | rfl | h) | ⟨t, ht1, ht2, h⟩ | ⟨t, ht1, ht2, h⟩ | rfl)
        · exact Or.inr (Or.inr (Or.inl ⟨k, le_rfl, hk', Or.inr rfl⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨k, le_rfl, hk', Or.inl rfl⟩))
        · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inr rfl⟩)
        · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inl rfl⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨t, by omega, ht2, h⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨t, by omega, ht2, h⟩))
        · exact Or.inr (Or.inr (Or.inr rfl))
      · rintro (h | ⟨t, ht1, ht2, h⟩ | ⟨t, ht1, ht2, h⟩ | rfl)
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
        · by_cases htk : t = k
          · subst htk; rcases h with rfl | rfl
            · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inl ⟨t, by omega, ht2, h⟩)
        · by_cases htk : t = k
          · subst htk; rcases h with rfl | rfl
            · exact Or.inl (Or.inr (Or.inl rfl))
            · exact Or.inl (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl ⟨t, by omega, ht2, h⟩))
        · exact Or.inr (Or.inr (Or.inr rfl))

/-- Cheat-proof losing walk down branch `(j, b)` from `u1Node j b k` to `botNode j`, recording
`∀ e ∈ used, e ∈ used'` so `validUsed_extend` applies directly. -/
theorem walk_branch_loses {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {b : Bool}
    (hj : j < xs.length) :
    ∀ (m k : ℕ), 0 < m → k + m = segCount xs ψ j b → ∀ (used : List (Sym2 ℕ)),
      (∀ t, t < k →
        s(u2Node j b t, vNode j b t) ∈ used ∧ s(vNode j b t, u1Node j b (t + 1)) ∈ used) →
      (∀ t, t < k →
        (s(u1Node j b t, mNode j b t) ∈ used ∧ s(mNode j b t, u2Node j b t) ∈ used) ∨
        (∃ ht : t < (occClauses xs ψ j b).length,
          let i := (occClauses xs ψ j b)[t]
          s(clauseNode i, u1Node j b t) ∈ used ∧ s(clauseNode i, u2Node j b t) ∈ used)) →
      (∀ t, k ≤ t → t < segCount xs ψ j b →
        s(u1Node j b t, mNode j b t) ∉ used ∧ s(mNode j b t, u2Node j b t) ∉ used ∧
        ∀ (ht : t < (occClauses xs ψ j b).length),
          let i := (occClauses xs ψ j b)[t]
          s(clauseNode i, u1Node j b t) ∉ used ∧ s(clauseNode i, u2Node j b t) ∉ used) →
      (∀ t, k ≤ t → t < segCount xs ψ j b - 1 →
        s(u2Node j b t, vNode j b t) ∉ used ∧ s(vNode j b t, u1Node j b (t + 1)) ∉ used) →
      s(u2Node j b (segCount xs ψ j b - 1), botNode j) ∉ used →
      (k = 0 → (j % 2 = 0 → s(cNode j b, u1Node j b 0) ∈ used) ∧
               (j % 2 = 1 → s(topNode j, u1Node j b 0) ∈ used)) →
      (∀ used' : List (Sym2 ℕ),
        (∀ e ∈ used, e ∈ used') →
        (∀ t, t < segCount xs ψ j b - 1 →
          s(u2Node j b t, vNode j b t) ∈ used' ∧ s(vNode j b t, u1Node j b (t + 1)) ∈ used') →
        s(u2Node j b (segCount xs ψ j b - 1), botNode j) ∈ used' →
        (∀ t, t < segCount xs ψ j b →
          (s(u1Node j b t, mNode j b t) ∈ used' ∧ s(mNode j b t, u2Node j b t) ∈ used') ∨
          (∃ ht : t < (occClauses xs ψ j b).length,
            let i := (occClauses xs ψ j b)[t]
            s(clauseNode i, u1Node j b t) ∈ used' ∧ s(clauseNode i, u2Node j b t) ∈ used')) →
        (∀ e ∈ used', e ∈ used ∨
          (∃ t, k ≤ t ∧ t < segCount xs ψ j b ∧
            (e = s(u1Node j b t, mNode j b t) ∨ e = s(mNode j b t, u2Node j b t) ∨
             ∃ ht : t < (occClauses xs ψ j b).length,
               let i := (occClauses xs ψ j b)[t]
               e = s(clauseNode i, u1Node j b t) ∨ e = s(clauseNode i, u2Node j b t))) ∨
          (∃ t, k ≤ t ∧ t < segCount xs ψ j b - 1 ∧
            (e = s(u2Node j b t, vNode j b t) ∨ e = s(vNode j b t, u1Node j b (t + 1)))) ∨
          e = s(u2Node j b (segCount xs ψ j b - 1), botNode j)) →
        EdgeGeographyWins (formulaGraph xs ψ) used' (botNode j)) →
      ¬ EdgeGeographyWins (formulaGraph xs ψ) used (u1Node j b k)
  | 0, _, hm, _, _, _, _, _, _, _, _, _ => absurd hm (Nat.not_lt_zero _)
  | m + 1, k, _, hkm, used, hprev_c, hprev_s, hfut_s, hfut_c, hbot, hk0, hfin => by
    have hk : k < segCount xs ψ j b := by omega
    obtain ⟨hum, hmu, hcl_k⟩ := hfut_s k le_rfl hk
    have hfrom_u2 : ∀ (e1 e2 : Sym2 ℕ),
        (e1 = s(u1Node j b k, mNode j b k) ∧ e2 = s(mNode j b k, u2Node j b k) ∨
         ∃ hko : k < (occClauses xs ψ j b).length,
           e1 = s(clauseNode ((occClauses xs ψ j b)[k]), u1Node j b k) ∧
           e2 = s(clauseNode ((occClauses xs ψ j b)[k]), u2Node j b k)) →
        ¬ EdgeGeographyWins (formulaGraph xs ψ) (e2 :: e1 :: used) (u2Node j b k) := by
      intro e1 e2 he12
      rw [not_edgeGeographyWins_iff]
      intro w hadj _ hnot
      rw [adj_u2Node_iff hj hk] at hadj
      rcases hadj with rfl | ⟨hk', rfl⟩ | ⟨hk_eq, rfl⟩ | ⟨hkocc, rfl⟩
      · rcases he12 with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩
        · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnot
        · have hadj_mu : (formulaGraph xs ψ).toSimpleGraph.Adj (mNode j b k) (u1Node j b k) :=
            (adj_mNode_iff hj hk).2 (Or.inl rfl)
          refine edgeGeographyWins_of_adj_dead hadj_mu (mem_vertices_of_adj hadj_mu) ?_ ?_
          · simp only [List.mem_cons, not_or]
            exact ⟨sym2_ne_of_tags (by decide),
              sym2_ne_of_tags (by decide),
              sym2_ne_of_tags (by decide), by rwa [Sym2.eq_swap]⟩
          · intro u hu
            rw [adj_u1Node_iff hj hk] at hu
            rcases hu with ⟨rfl, ⟨hpar, rfl⟩ | ⟨hpar, rfl⟩⟩ | ⟨hkpos, rfl⟩ | rfl | ⟨_, rfl⟩
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (by rw [Sym2.eq_swap]; exact (hk0 rfl).1 hpar))))
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (by rw [Sym2.eq_swap]; exact (hk0 rfl).2 hpar))))
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (by
                  rw [Sym2.eq_swap]
                  have := (hprev_c (k - 1) (by omega)).2
                  rwa [Nat.sub_add_cancel (by omega)] at this))))
            · rw [Sym2.eq_swap]; exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (by rw [Sym2.eq_swap]; exact List.mem_cons_self)))
      · cases m with
        | zero => omega
        | succ m' =>
          have hadj_vu : (formulaGraph xs ψ).toSimpleGraph.Adj (vNode j b k) (u1Node j b (k + 1)) :=
            (adj_vNode_iff hj hk').2 (Or.inr rfl)
          rw [edgeGeographyWins_iff]
          refine ⟨u1Node j b (k + 1), hadj_vu, mem_vertices_of_adj hadj_vu, ?_, ?_⟩
          · simp only [List.mem_cons, not_or]
            refine ⟨sym2_ne_of_tags (by decide), ?_, ?_, (hfut_c k le_rfl hk').2⟩
            · rcases he12 with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;>
                exact sym2_ne_of_tags (by decide)
            · rcases he12 with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;>
                exact sym2_ne_of_tags (by decide)
          · have hnot4 : ∀ {e : Sym2 ℕ},
                e ≠ s(vNode j b k, u1Node j b (k + 1)) → e ≠ s(u2Node j b k, vNode j b k) →
                e ≠ e2 → e ≠ e1 → e ∉ used →
                e ∉ s(vNode j b k, u1Node j b (k + 1)) :: s(u2Node j b k, vNode j b k) ::
                    e2 :: e1 :: used := by
              intro e h1 h2 h3 h4 h5; simp [List.mem_cons, h1, h2, h3, h4, h5]
            refine walk_branch_loses hj (m' + 1) (k + 1) (Nat.succ_pos _) (by omega) _
              ?_ ?_ ?_ ?_ ?_ (fun h => by omega) ?_
            · intro t ht
              by_cases htk : t = k
              · subst htk; exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self⟩
              · obtain ⟨h1, h2⟩ := hprev_c t (by omega)
                exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ h1))),
                  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ h2)))⟩
            · intro t ht
              by_cases htk : t = k
              · subst htk
                rcases he12 with ⟨rfl, rfl⟩ | ⟨hko, rfl, rfl⟩
                · left
                  exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    List.mem_cons_self)),
                    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
                · right
                  exact ⟨hko, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ List.mem_cons_self)),
                    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
              · rcases hprev_s t (by omega) with ⟨h1, h2⟩ | ⟨hko, h1, h2⟩
                · left
                  exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ h1))),
                    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ h2)))⟩
                · right
                  exact ⟨hko, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ h1))),
                    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ h2)))⟩
            · intro t ht1 ht2
              obtain ⟨h1, h2, h3⟩ := hfut_s t (by omega) ht2
              have htk : t ≠ k := by omega
              have hdisj : ∀ e : Sym2 ℕ,
                  (e = s(u1Node j b t, mNode j b t) ∨ e = s(mNode j b t, u2Node j b t) ∨
                   ∃ hto : t < (occClauses xs ψ j b).length,
                     e = s(clauseNode ((occClauses xs ψ j b)[t]), u1Node j b t) ∨
                     e = s(clauseNode ((occClauses xs ψ j b)[t]), u2Node j b t)) →
                  e ∉ used →
                  e ∉ s(vNode j b k, u1Node j b (k + 1)) :: s(u2Node j b k, vNode j b k) ::
                      e2 :: e1 :: used := by
                intro e he hu
                have hne12 : e ≠ e2 ∧ e ≠ e1 := by
                  rcases he12 with ⟨rfl, rfl⟩ | ⟨hko, rfl, rfl⟩
                  · rcases he with rfl | rfl | ⟨_, rfl | rfl⟩
                    · exact ⟨sym2_ne_of_tags (by decide), fun h => by
                        rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
                        · simp only [u1Node_eq_pair, Nat.pair_eq_pair, true_and] at ha; omega
                        · exact pair_ne_of_ne (by decide) ha⟩
                    · exact ⟨fun h => by
                        rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
                        · simp only [mNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; omega
                        · exact pair_ne_of_ne (by decide) ha,
                        sym2_ne_of_tags (by decide)⟩
                    · exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩
                    · exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩
                  · rcases he with rfl | rfl | ⟨_, rfl | rfl⟩
                    · exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩
                    · exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩
                    · exact ⟨sym2_ne_of_tags (by decide), fun h => by
                        rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
                        · simp only [u1Node_eq_pair, Nat.pair_eq_pair, true_and] at hb; omega
                        · exact pair_ne_of_ne (by decide) ha⟩
                    · exact ⟨fun h => by
                        rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
                        · simp only [u2Node_eq_pair, Nat.pair_eq_pair, true_and] at hb; omega
                        · exact pair_ne_of_ne (by decide) ha,
                        sym2_ne_of_tags (by decide)⟩
                have hne_vu : e ≠ s(vNode j b k, u1Node j b (k + 1)) := by
                  rcases he with rfl | rfl | ⟨_, rfl | rfl⟩ <;>
                    exact sym2_ne_of_tags (by decide)
                have hne_uv : e ≠ s(u2Node j b k, vNode j b k) := by
                  rcases he with rfl | rfl | ⟨_, rfl | rfl⟩ <;>
                    exact sym2_ne_of_tags (by decide)
                exact hnot4 hne_vu hne_uv hne12.1 hne12.2 hu
              refine ⟨hdisj _ (Or.inl rfl) h1, hdisj _ (Or.inr (Or.inl rfl)) h2,
                fun hto => ⟨hdisj _ (Or.inr (Or.inr ⟨hto, Or.inl rfl⟩)) (h3 hto).1,
                  hdisj _ (Or.inr (Or.inr ⟨hto, Or.inr rfl⟩)) (h3 hto).2⟩⟩
            · intro t ht1 ht2
              obtain ⟨h1, h2⟩ := hfut_c t (by omega) ht2
              have htk : t ≠ k := by omega
              have hne12 : ∀ e, (e = s(u2Node j b t, vNode j b t) ∨
                  e = s(vNode j b t, u1Node j b (t + 1))) → e ≠ e2 ∧ e ≠ e1 := by
                intro e he
                rcases he12 with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;>
                  rcases he with rfl | rfl <;>
                  exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩
              refine ⟨hnot4 (sym2_ne_of_tags (by decide)) (fun h => by
                  rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
                  · simp only [u2Node_eq_pair, Nat.pair_eq_pair, true_and] at ha; omega
                  · exact pair_ne_of_ne (by decide) ha) (hne12 _ (Or.inl rfl)).1
                  (hne12 _ (Or.inl rfl)).2 h1,
                hnot4 (fun h => by
                  rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
                  · simp only [vNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; omega
                  · exact pair_ne_of_ne (by decide) ha) (sym2_ne_of_tags (by decide))
                  (hne12 _ (Or.inr rfl)).1 (hne12 _ (Or.inr rfl)).2 h2⟩
            · have hne12 : s(u2Node j b (segCount xs ψ j b - 1), botNode j) ≠ e2 ∧
                  s(u2Node j b (segCount xs ψ j b - 1), botNode j) ≠ e1 := by
                rcases he12 with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;>
                  exact ⟨(sym2_ne_of_tags (by decide)).symm,
                    (sym2_ne_of_tags (by decide)).symm⟩
              exact hnot4 (sym2_ne_of_tags (by decide))
                (by intro h; rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
                    · exact pair_ne_of_ne (by decide) hb
                    · exact pair_ne_of_ne (by decide) ha) hne12.1 hne12.2 hbot
            · intro used' hsub' h1 h2 h3 h4
              refine hfin used' (fun e he => hsub' e (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)))))
                h1 h2 h3 fun e he => ?_
              rcases h4 e he with h | ⟨t, ht1, ht2, h⟩ | ⟨t, ht1, ht2, h⟩ | rfl
              · simp only [List.mem_cons] at h
                rcases h with rfl | rfl | rfl | rfl | h
                · exact Or.inr (Or.inr (Or.inl ⟨k, le_rfl, hk', Or.inr rfl⟩))
                · exact Or.inr (Or.inr (Or.inl ⟨k, le_rfl, hk', Or.inl rfl⟩))
                · rcases he12 with ⟨rfl, rfl⟩ | ⟨hko, rfl, rfl⟩
                  · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inr (Or.inl rfl)⟩)
                  · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inr (Or.inr ⟨hko, Or.inr rfl⟩)⟩)
                · rcases he12 with ⟨rfl, rfl⟩ | ⟨hko, rfl, rfl⟩
                  · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inl rfl⟩)
                  · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inr (Or.inr ⟨hko, Or.inl rfl⟩)⟩)
                · exact Or.inl h
              · exact Or.inr (Or.inl ⟨t, by omega, ht2, h⟩)
              · exact Or.inr (Or.inr (Or.inl ⟨t, by omega, ht2, h⟩))
              · exact Or.inr (Or.inr (Or.inr rfl))
      · have hm0 : m = 0 := by omega
        subst hm0
        refine hfin (s(u2Node j b k, botNode j) :: e2 :: e1 :: used)
          (fun e he => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)))
          ?_ ?_ ?_ ?_
        · intro t ht
          obtain ⟨h1, h2⟩ := hprev_c t (by omega)
          exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1)),
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2))⟩
        · rw [← hk_eq]; exact List.mem_cons_self
        · intro t ht
          by_cases htk : t = k
          · subst htk
            rcases he12 with ⟨rfl, rfl⟩ | ⟨hko, rfl, rfl⟩
            · left
              exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
                List.mem_cons_of_mem _ List.mem_cons_self⟩
            · right
              exact ⟨hko, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
                List.mem_cons_of_mem _ List.mem_cons_self⟩
          · rcases hprev_s t (by omega) with ⟨h1, h2⟩ | ⟨hko, h1, h2⟩
            · left
              exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1)),
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2))⟩
            · right
              exact ⟨hko,
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1)),
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2))⟩
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | rfl | rfl | h
          · exact Or.inr (Or.inr (Or.inr (hk_eq ▸ rfl)))
          · rcases he12 with ⟨rfl, rfl⟩ | ⟨hko, rfl, rfl⟩
            · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inr (Or.inl rfl)⟩)
            · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inr (Or.inr ⟨hko, Or.inr rfl⟩)⟩)
          · rcases he12 with ⟨rfl, rfl⟩ | ⟨hko, rfl, rfl⟩
            · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inl rfl⟩)
            · exact Or.inr (Or.inl ⟨k, le_rfl, hk, Or.inr (Or.inr ⟨hko, Or.inl rfl⟩)⟩)
          · exact Or.inl h
      · rcases he12 with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩
        · have hadj_cu : (formulaGraph xs ψ).toSimpleGraph.Adj
              (clauseNode ((occClauses xs ψ j b)[k])) (u1Node j b k) :=
            (adj_u1Node_iff hj hk).2 (Or.inr (Or.inr (Or.inr ⟨hkocc, rfl⟩))) |>.symm
          refine edgeGeographyWins_of_adj_dead hadj_cu (mem_vertices_of_adj hadj_cu) ?_ ?_
          · simp only [List.mem_cons, not_or]
            exact ⟨sym2_ne_of_tags (by decide),
              sym2_ne_of_tags (by decide),
              sym2_ne_of_tags (by decide), (hcl_k hkocc).1⟩
          · intro u hu
            rw [adj_u1Node_iff hj hk] at hu
            rcases hu with ⟨rfl, ⟨hpar, rfl⟩ | ⟨hpar, rfl⟩⟩ | ⟨hkpos, rfl⟩ | rfl | ⟨_, rfl⟩
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (by rw [Sym2.eq_swap]; exact (hk0 rfl).1 hpar))))
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (by rw [Sym2.eq_swap]; exact (hk0 rfl).2 hpar))))
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (by
                  rw [Sym2.eq_swap]
                  have := (hprev_c (k - 1) (by omega)).2
                  rwa [Nat.sub_add_cancel (by omega)] at this))))
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ List.mem_cons_self))
            · rw [Sym2.eq_swap]; exact List.mem_cons_self
        · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnot
    rw [not_edgeGeographyWins_iff]
    intro w hadj _ hnot
    rw [adj_u1Node_iff hj hk] at hadj
    rcases hadj with ⟨rfl, ⟨hpar, rfl⟩ | ⟨hpar, rfl⟩⟩ | ⟨hkpos, rfl⟩ | rfl | ⟨hkocc, rfl⟩
    · exact absurd (by rw [Sym2.eq_swap]; exact (hk0 rfl).1 hpar) hnot
    · exact absurd (by rw [Sym2.eq_swap]; exact (hk0 rfl).2 hpar) hnot
    · have := (hprev_c (k - 1) (by omega)).2
      rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this
      exact absurd this hnot
    · have hadj_mu : (formulaGraph xs ψ).toSimpleGraph.Adj (mNode j b k) (u2Node j b k) :=
        (adj_mNode_iff hj hk).2 (Or.inr rfl)
      rw [edgeGeographyWins_iff]
      refine ⟨u2Node j b k, hadj_mu, mem_vertices_of_adj hadj_mu, by
        simp only [List.mem_cons, not_or]
        exact ⟨sym2_ne_of_tags (by decide), hmu⟩, ?_⟩
      exact hfrom_u2 _ _ (Or.inl ⟨rfl, rfl⟩)
    · have hadj_cu2 : (formulaGraph xs ψ).toSimpleGraph.Adj
          (clauseNode ((occClauses xs ψ j b)[k])) (u2Node j b k) :=
        (adj_u2Node_iff hj hk).2 (Or.inr (Or.inr (Or.inr ⟨hkocc, rfl⟩))) |>.symm
      rw [edgeGeographyWins_iff]
      refine ⟨u2Node j b k, hadj_cu2, mem_vertices_of_adj hadj_cu2, by
        simp only [List.mem_cons, not_or]
        exact ⟨sym2_ne_of_tags (by decide), (hcl_k hkocc).2⟩, ?_⟩
      exact hfrom_u2 _ _ (Or.inr ⟨hkocc, Sym2.eq_swap, rfl⟩)

end UndirectedEdgeGeography

end Cslib.Complexity
