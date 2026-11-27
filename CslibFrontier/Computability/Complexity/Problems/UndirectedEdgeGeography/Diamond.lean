module

public import CslibFrontier.Computability.Complexity.Problems.UndirectedEdgeGeography.Strategy

/-!
# Even Variable-Diamond Traversal for Undirected Edge Geography

Proves `cross_even_wins` and `cross_even_loses` for crossing an existential (even-index) variable
diamond in `formulaGraph`, ruling out chord shortcuts and 3-edge entry loops.

## Main results

* `Cslib.Complexity.UndirectedEdgeGeography.validUsed_not_mem_unplayed`: unplayed gadgets carry
  no edges in `ValidUsed`.
* `Cslib.Complexity.UndirectedEdgeGeography.cross_even_wins`, `cross_even_loses`: exact
  existential-choice semantics across an even variable diamond.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Cslib.Logic.PL

namespace UndirectedEdgeGeography

/-! ### Phase 1: crossing even and odd variable diamonds -/

/-- An unplayed gadget `j ≥ z.length` has no edges in any `ValidUsed` set. -/
theorem validUsed_not_mem_unplayed {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {used : List (Sym2 ℕ)} (hV : ValidUsed xs ψ z used) (b : Bool) :
    let j := z.length
    s(topNode j, aNode j b) ∉ used ∧ s(aNode j b, wNode j b) ∉ used ∧
    s(topNode j, wNode j b) ∉ used ∧
    s(botNode j, midNode j) ∉ used ∧ s(midNode j, topNode (j + 1)) ∉ used ∧
    s(botNode j, topNode (j + 1)) ∉ used ∧
    ∀ (t : ℕ) (ht : t < (occClauses xs ψ j b).length),
      s(clauseNode ((occClauses xs ψ j b)[t]), u1Node j b t) ∉ used ∧
      s(clauseNode ((occClauses xs ψ j b)[t]), u2Node j b t) ∉ used := by
  set j := z.length
  have hcheck : ∀ e : Sym2 ℕ,
      (∀ j' b', e ∈ normalBranchEdges xs ψ j' b' → j' = j) →
      (∀ j', e ∈ bridgeEdges j' → j' = j) →
      (∀ j' b', e = s(topNode j', wNode j' b') ∨ e = s(topNode j', aNode j' b') ∨
        e = s(aNode j' b', wNode j' b') → j' = j) →
      (∀ j' b' k i, e = s(clauseNode i, u1Node j' b' k) ∨ e = s(clauseNode i, u2Node j' b' k) →
        j' = j) →
      e ∉ used := by
    intro e h1 h2 h3 h4 hm
    obtain ⟨j', hj', h⟩ := hV.2 e hm
    rcases h with h | h | ⟨_, h | h | h | h⟩ | ⟨k, _, h | h⟩
    · exact absurd (h1 _ _ h) (by omega)
    · exact absurd (h2 _ h) (by omega)
    · exact absurd (h3 _ _ (Or.inl h)) (by omega)
    · exact absurd (h3 _ _ (Or.inr (Or.inl h))) (by omega)
    · exact absurd (h3 _ _ (Or.inr (Or.inr h))) (by omega)
    · exact absurd (h3 _ _ (Or.inl h)) (by omega)
    · exact absurd (h4 _ _ _ _ (Or.inl h)) (by omega)
    · exact absurd (h4 _ _ _ _ (Or.inr h)) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun t _ => ⟨?_, ?_⟩⟩
  · exact hcheck _ (fun _ _ h => (normalBranchEdges_idx.1 h).1)
      (fun _ h => absurd h (not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide) ∘
        (Sym2.eq_swap ▸ ·)))
      (fun _ _ h => by
        rcases h with h | h | h
        · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
          · exact absurd hb (pair_ne_of_ne (by decide))
          · exact absurd ha (pair_ne_of_ne (by decide))
        · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
          · simp only [topNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; exact ha.symm
          · exact absurd ha (pair_ne_of_ne (by decide))
        · exact absurd h (sym2_ne_of_tags (by decide)))
      (fun _ _ _ _ h => by
        rcases h with h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
  · exact hcheck _ (fun _ _ h => (normalBranchEdges_idx.2.1 h).1)
      (fun _ h => absurd h (not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide)))
      (fun _ _ h => by
        rcases h with h | h | h
        · exact absurd h (sym2_ne_of_tags (by decide))
        · exact absurd h (sym2_ne_of_tags (by decide))
        · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
          · simp only [aNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; exact ha.1.symm
          · exact absurd ha (pair_ne_of_ne (by decide)))
      (fun _ _ _ _ h => by
        rcases h with h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
  · exact hcheck _ (fun _ _ h => absurd h normalBranchEdges_idx.2.2.1)
      (fun _ h => absurd h (not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide) ∘
        (Sym2.eq_swap ▸ ·)))
      (fun _ _ h => by
        rcases h with h | h | h
        · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
          · simp only [topNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; exact ha.symm
          · exact absurd ha (pair_ne_of_ne (by decide))
        · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
          · exact absurd hb (pair_ne_of_ne (by decide))
          · exact absurd ha (pair_ne_of_ne (by decide))
        · exact absurd h (sym2_ne_of_tags (by decide)))
      (fun _ _ _ _ h => by
        rcases h with h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
  · exact hcheck _ (fun _ _ h => absurd (Sym2.eq_swap ▸ h)
      (not_mem_normalBranchEdges_of_tag (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)))
      (fun _ h => bridgeEdges_idx.1 h)
      (fun _ _ h => by
        rcases h with h | h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
      (fun _ _ _ _ h => by
        rcases h with h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
  · exact hcheck _ (fun _ _ h => absurd h
      (not_mem_normalBranchEdges_of_tag (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)))
      (fun _ h => bridgeEdges_idx.2.1 h)
      (fun _ _ h => by
        rcases h with h | h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
      (fun _ _ _ _ h => by
        rcases h with h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
  · exact hcheck _ (fun _ _ h => by
      -- `s(botNode j, topNode (j + 1))` cannot lie in `normalBranchEdges` because tag 0 never pairs
      -- with tag 1!
      exfalso
      simp only [normalBranchEdges_eq_append, List.mem_append, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with (((h | ⟨k, _, h | h⟩) | ⟨k, _, h | h⟩) | h)
      · split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        · rcases h with h | h | h | h
          · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
            · exact pair_ne_of_ne (by decide) hb
            · exact pair_ne_of_ne (by decide) ha
          · exact sym2_ne_of_tags (by decide) h
          · exact sym2_ne_of_tags (by decide) h
          · exact sym2_ne_of_tags (by decide) h
        · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
          · exact pair_ne_of_ne (by decide) hb
          · exact pair_ne_of_ne (by decide) ha
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨_, hb⟩
        · exact pair_ne_of_ne (by decide) ha
        · exact pair_ne_of_ne (by decide) hb)
      (fun _ h => bridgeEdges_idx.2.2 h)
      (fun _ _ h => by
        rcases h with h | h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
      (fun _ _ _ _ h => by
        rcases h with h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
  · exact hcheck _ (fun _ _ h => absurd h
      (not_mem_normalBranchEdges_of_tag (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)))
      (fun _ h => absurd h (not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide)))
      (fun _ _ h => by
        rcases h with h | h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
      (fun _ _ _ _ h => by
        rcases h with h | h
        · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
          · simp only [u1Node_eq_pair, Nat.pair_eq_pair, true_and] at hb; exact hb.1.symm
          · exact absurd ha (pair_ne_of_ne (by decide))
        · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
          · exact absurd hb (pair_ne_of_ne (by decide))
          · exact absurd ha (pair_ne_of_ne (by decide)))
  · exact hcheck _ (fun _ _ h => absurd h
      (not_mem_normalBranchEdges_of_tag (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)))
      (fun _ h => absurd h (not_mem_bridgeEdges_of_tag (by decide) (by decide) (by decide)))
      (fun _ _ h => by
        rcases h with h | h | h <;> exact absurd h (sym2_ne_of_tags (by decide)))
      (fun _ _ _ _ h => by
        rcases h with h | h
        · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
          · exact absurd hb (pair_ne_of_ne (by decide))
          · exact absurd ha (pair_ne_of_ne (by decide))
        · rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
          · simp only [u2Node_eq_pair, Nat.pair_eq_pair, true_and] at hb; exact hb.1.symm
          · exact absurd ha (pair_ne_of_ne (by decide)))

/-- Edge membership in `normalUsed` after appending one more variable choice `b`. -/
theorem mem_normalUsed_append {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool} {b : Bool}
    {e : Sym2 ℕ} :
    e ∈ normalUsed xs ψ (z ++ [b]) ↔
      e ∈ normalUsed xs ψ z ∨ e ∈ normalBranchEdges xs ψ z.length b ∨ e ∈ bridgeEdges z.length := by
  simp only [normalUsed_eq_flatMap, List.mem_flatMap, List.mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff, List.mem_append, List.length_append, List.length_singleton]
  constructor
  · rintro ⟨⟨b', j'⟩, ⟨hj', hget⟩, hm⟩
    by_cases hlt : j' < z.length
    · rw [List.getElem_append_left hlt] at hget
      exact Or.inl ⟨(b', j'), ⟨hlt, hget⟩, hm⟩
    · have hjeq : j' = z.length := by omega
      subst hjeq
      have hbeq : b' = b := by simpa using hget.symm
      subst hbeq
      exact Or.inr hm
  · rintro (⟨⟨b', j'⟩, ⟨hj', hget⟩, hm⟩ | hm)
    · exact ⟨(b', j'), ⟨by omega, by rw [List.getElem_append_left hj']; exact hget⟩, hm⟩
    · exact ⟨(b, z.length), ⟨by omega, by simp⟩, hm⟩

/-- Player 1 wins across an even variable diamond by choosing branch `b`. -/
theorem cross_even_wins {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    (hj : z.length < xs.length) (hpar : z.length % 2 = 0) {b : Bool}
    (hnext : ¬ EdgeGeographyWins (formulaGraph xs ψ) (normalUsed xs ψ (z ++ [b]))
      (topNode (z.length + 1))) :
    EdgeGeographyWins (formulaGraph xs ψ) (normalUsed xs ψ z) (topNode z.length) := by
  set j := z.length
  have hV := validUsed_normalUsed xs ψ z
  have hbr := validUsed_not_mem_branch hV (j := j) (b := b) (fun h => by omega)
  have hbr' := validUsed_not_mem_branch hV (j := j) (b := !b) (fun h => by omega)
  have hunp := validUsed_not_mem_unplayed hV b
  have hunp' := validUsed_not_mem_unplayed hV (!b)
  have hadj_ta : (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) (aNode j b) :=
    (adj_aNode_iff hj hpar).2 (Or.inl rfl) |>.symm
  rw [edgeGeographyWins_iff]
  refine ⟨aNode j b, hadj_ta, mem_vertices_of_adj hadj_ta, hunp.1, ?_⟩
  have hadj_aw : (formulaGraph xs ψ).toSimpleGraph.Adj (aNode j b) (wNode j b) :=
    (adj_aNode_iff hj hpar).2 (Or.inr rfl)
  rw [edgeGeographyWins_of_unique_move hadj_aw (mem_vertices_of_adj hadj_aw) (by
    simp only [List.mem_cons, not_or]
    exact ⟨sym2_ne_of_tags (by decide), hunp.2.1⟩)
    (fun u hu hnu => by
      rw [adj_aNode_iff hj hpar] at hu
      rcases hu with rfl | rfl
      · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnu
      · rfl)]
  rw [not_not]
  have hadj_wc : (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j b) (cNode j b) :=
    (adj_cNode_iff hj hpar).2 (Or.inl rfl) |>.symm
  rw [edgeGeographyWins_iff]
  refine ⟨cNode j b, hadj_wc, mem_vertices_of_adj hadj_wc, by
    simp only [List.mem_cons, not_or]
    exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
      (hbr.2.2.1 hpar).1⟩, ?_⟩
  have hadj_cu : (formulaGraph xs ψ).toSimpleGraph.Adj (cNode j b) (u1Node j b 0) :=
    (adj_cNode_iff hj hpar).2 (Or.inr rfl)
  rw [edgeGeographyWins_of_unique_move hadj_cu (mem_vertices_of_adj hadj_cu) (by
    simp only [List.mem_cons, not_or]
    exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
      sym2_ne_of_tags (by decide), (hbr.2.2.1 hpar).2⟩)
    (fun u hu hnu => by
      rw [adj_cNode_iff hj hpar] at hu
      rcases hu with rfl | rfl
      · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnu
      · rfl)]
  rw [not_not]
  have hnot4 : ∀ {e : Sym2 ℕ},
      e ≠ s(cNode j b, u1Node j b 0) → e ≠ s(wNode j b, cNode j b) →
      e ≠ s(aNode j b, wNode j b) → e ≠ s(topNode j, aNode j b) → e ∉ normalUsed xs ψ z →
      e ∉ s(cNode j b, u1Node j b 0) :: s(wNode j b, cNode j b) ::
          s(aNode j b, wNode j b) :: s(topNode j, aNode j b) :: normalUsed xs ψ z := by
    intro e h1 h2 h3 h4 h5; simp [List.mem_cons, h1, h2, h3, h4, h5]
  refine walk_branch_wins hj (segCount xs ψ j b) 0 (one_le_segCount _ _ _ _) (zero_add _) _
    ?_ ?_ ?_ ?_
  · intro t _ _
    exact ⟨hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) (hbr.1 t).1,
      hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) (hbr.1 t).2.1⟩
  · intro t _ _
    exact ⟨hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) (hbr.1 t).2.2.1,
      hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) (hbr.1 t).2.2.2⟩
  · exact hnot4 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
      (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) hbr.2.1
  · intro used' hused'
    have hused'_nb : ∀ e, e ∈ used' ↔ e ∈ normalUsed xs ψ z ∨ e ∈ normalBranchEdges xs ψ j b := by
      intro e
      rw [hused']
      simp only [List.mem_cons, normalBranchEdges_eq_append, hpar, beq_self_eq_true, ↓reduceIte,
        List.mem_append, List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false]
      constructor
      · rintro ((rfl | rfl | rfl | rfl | h) | ⟨t, _, ht, h⟩ | ⟨t, _, ht, h⟩ | rfl)
        · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr rfl))))))
        · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl))))))
        · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
        · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl rfl))))
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨t, ht, h⟩)))
        · exact Or.inr (Or.inl (Or.inr ⟨t, ht, h⟩))
        · exact Or.inr (Or.inr rfl)
      · rintro (h | (((rfl | rfl | rfl | rfl) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | rfl)
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr (Or.inl ⟨t, Nat.zero_le _, ht, h⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨t, Nat.zero_le _, ht, h⟩))
        · exact Or.inr (Or.inr (Or.inr rfl))
    rw [not_edgeGeographyWins_iff]
    intro w hadj _ hnot
    rw [adj_botNode_iff hj] at hadj
    rcases hadj with ⟨b', rfl⟩ | ⟨-, rfl⟩ | ⟨hpar', _⟩
    · by_cases hb' : b' = b
      · subst hb'
        exact absurd ((hused'_nb _).2 (Or.inr (by simp [normalBranchEdges_eq_append]))) hnot
      · have hb'eq : b' = !b := by cases b <;> cases b' <;> simp_all
        subst hb'eq
        have hnot_u' : ∀ {e : Sym2 ℕ},
            (∀ j' b', e ∈ normalBranchEdges xs ψ j' b' → j' = j ∧ b' = !b) →
            e ≠ s(botNode j, u2Node j (!b) (segCount xs ψ j (!b) - 1)) →
            e ∉ normalUsed xs ψ z →
            e ∉ s(botNode j, u2Node j (!b) (segCount xs ψ j (!b) - 1)) :: used' := by
          intro e hnb h1 h2 hm
          rcases List.mem_cons.1 hm with rfl | hm'
          · exact h1 rfl
          · rcases (hused'_nb e).1 hm' with hu | hnb'
            · exact h2 hu
            · have := (hnb j b hnb').2; cases b <;> simp at this
        have hk_last : segCount xs ψ j (!b) - 1 < segCount xs ψ j (!b) := by
          have := one_le_segCount xs ψ j (!b); omega
        refine wins_backwalk_u2 hj (segCount xs ψ j (!b) - 1) hk_last _ ?_ (fun h => by omega)
          ?_ ?_
        · intro _
          have hwc_c : s(wNode j b, cNode j b) ∈ used' :=
            (hused'_nb _).2 (Or.inr (by simp [normalBranchEdges_eq_append, hpar]))
          have haw_c : s(aNode j b, wNode j b) ∈ used' :=
            (hused'_nb _).2 (Or.inr (by simp [normalBranchEdges_eq_append, hpar]))
          have htw_u : s(topNode j, wNode j b) ∉
              s(botNode j, u2Node j (!b) (segCount xs ψ j (!b) - 1)) :: used' := by
            intro hm
            rcases List.mem_cons.1 hm with h | hm'
            · exact sym2_ne_of_tags (by decide) h
            · rcases (hused'_nb _).1 hm' with hu | hnb'
              · exact hunp.2.2.1 hu
              · exact normalBranchEdges_idx.2.2.1 hnb'
          refine ⟨hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.1)
              (sym2_ne_of_tags (by decide)).symm (hbr'.2.2.1 hpar).1,
            hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.2.1)
              (sym2_ne_of_tags (by decide)).symm (hbr'.2.2.1 hpar).2,
            ⟨hnot_u' (fun _ _ => normalBranchEdges_idx.1)
                (sym2_ne_of_tags (by decide)).symm hunp'.1,
              hnot_u' (fun _ _ => normalBranchEdges_idx.2.1)
                (sym2_ne_of_tags (by decide)).symm hunp'.2.1,
              Or.inl ⟨by simpa using htw_u, fun u hu => ?_⟩⟩⟩
          rw [adj_wNode_iff hj hpar] at hu
          simp only [Bool.not_not] at hu ⊢
          rcases hu with rfl | rfl | rfl
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (by rw [Sym2.eq_swap]; exact haw_c))
          · rw [Sym2.eq_swap]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hwc_c)
        · intro t _
          exact ⟨hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.1 t)
              (sym2_ne_of_tags (by decide)) (hbr'.1 t).1,
            hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.2.1 t)
              (sym2_ne_of_tags (by decide)) (hbr'.1 t).2.1⟩
        · intro t _
          exact ⟨hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.2.2.1 t)
              (sym2_ne_of_tags (by decide)) (hbr'.1 t).2.2.1,
            hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.2.2.2.1 t)
              (sym2_ne_of_tags (by decide)) (hbr'.1 t).2.2.2⟩
    · have hadj_mt : (formulaGraph xs ψ).toSimpleGraph.Adj (midNode j) (topNode (j + 1)) :=
        (adj_midNode_iff hj hpar).2 (Or.inr rfl)
      rw [edgeGeographyWins_iff]
      refine ⟨topNode (j + 1), hadj_mt, mem_vertices_of_adj hadj_mt, ?_, ?_⟩
      · simp only [List.mem_cons, not_or]
        refine ⟨sym2_ne_of_tags (by decide), fun hm => ?_⟩
        rcases (hused'_nb _).1 hm with hu | hnb'
        · exact hunp.2.2.2.2.1 hu
        · exact not_mem_normalBranchEdges_of_tag (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) hnb'
      · refine (not_iff_not.2 (edgeGeographyWins_congr ?_ _)).2 hnext
        intro e
        rw [mem_normalUsed_append]
        have hbr_j : e ∈ bridgeEdges z.length ↔
            e = s(botNode j, midNode j) ∨ e = s(midNode j, topNode (j + 1)) := by
          simp [hpar, j]
        dsimp only [j] at hused'_nb hbr_j ⊢
        simp only [List.mem_cons, hused'_nb, hbr_j]
        constructor
        · rintro (rfl | rfl | h | h)
          · exact Or.inr (Or.inr (Or.inr rfl))
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rintro (h | h | rfl | rfl)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
    · omega

/-- Helper for `cross_even_loses`: from `u1Node j b 0` with an entry prefix `pre`,
Player 1 loses. -/
private theorem cross_even_loses_from_u1 {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {used : List (Sym2 ℕ)} (hV : ValidUsed xs ψ z used)
    (hj : z.length < xs.length) (hpar : z.length % 2 = 0)
    (hnext : ∀ (b : Bool) (used' : List (Sym2 ℕ)),
      ValidUsed xs ψ (z ++ [b]) used' →
      EdgeGeographyWins (formulaGraph xs ψ) used' (topNode (z.length + 1)))
    (b : Bool) (pre : List (Sym2 ℕ)) :
    let j := z.length
    (∀ e ∈ pre, e = s(topNode j, aNode j b) ∨ e = s(aNode j b, wNode j b) ∨
      e = s(topNode j, wNode j b) ∨ e = s(wNode j b, cNode j b) ∨
      e = s(cNode j b, u1Node j b 0) ∨
      e = s(topNode j, aNode j (!b)) ∨ e = s(aNode j (!b), wNode j (!b)) ∨
      e = s(topNode j, wNode j (!b))) →
    s(wNode j b, cNode j b) ∈ pre → s(cNode j b, u1Node j b 0) ∈ pre →
    ((s(topNode j, aNode j b) ∈ pre ∧ s(aNode j b, wNode j b) ∈ pre ∧
        s(topNode j, wNode j b) ∉ pre) ∨
     (s(topNode j, wNode j b) ∈ pre ∧ s(topNode j, aNode j b) ∉ pre ∧
        s(aNode j b, wNode j b) ∉ pre)) →
    (s(topNode j, aNode j (!b)) ∉ pre ∧ s(aNode j (!b), wNode j (!b)) ∉ pre ∧
        s(topNode j, wNode j (!b)) ∉ pre) →
    s(wNode j (!b), cNode j (!b)) ∉ pre → s(cNode j (!b), u1Node j (!b) 0) ∉ pre →
    ¬ EdgeGeographyWins (formulaGraph xs ψ) (pre ++ used) (u1Node j b 0) := by
  set j := z.length
  have hbr := fun b : Bool => validUsed_not_mem_branch hV (j := j) (b := b) (fun h => by omega)
  have hunp := fun b : Bool => validUsed_not_mem_unplayed hV b
  dsimp only
  intro hpre hwc hcu h3 h4 hwc' hcu'
  have hnot_pre : ∀ {e : Sym2 ℕ},
      e ≠ s(topNode j, aNode j b) → e ≠ s(aNode j b, wNode j b) →
      e ≠ s(topNode j, wNode j b) → e ≠ s(wNode j b, cNode j b) →
      e ≠ s(cNode j b, u1Node j b 0) →
      e ≠ s(topNode j, aNode j (!b)) → e ≠ s(aNode j (!b), wNode j (!b)) →
      e ≠ s(topNode j, wNode j (!b)) → e ∉ used → e ∉ pre ++ used := by
    intro e h1 h2 h3' h4' h5 h6 h7 h8 hu hmem
    rcases List.mem_append.1 hmem with hp | hu'
    · rcases hpre e hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact h1 rfl | exact h2 rfl | exact h3' rfl | exact h4' rfl |
                exact h5 rfl | exact h6 rfl | exact h7 rfl | exact h8 rfl
    · exact hu hu'
  refine walk_branch_loses hj (segCount xs ψ j b) 0 (one_le_segCount _ _ _ _) (zero_add _)
    (pre ++ used) (fun _ h => by omega) (fun _ h => by omega) ?_ ?_ ?_
    (fun _ => ⟨fun _ => List.mem_append_left _ hcu, fun h => by omega⟩) ?_
  · intro t _ _
    exact ⟨hnot_pre (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) ((hbr b).1 t).1,
      hnot_pre (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) ((hbr b).1 t).2.1,
      fun ht => ⟨hnot_pre (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          ((hunp b).2.2.2.2.2.2 t ht).1,
        hnot_pre (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          ((hunp b).2.2.2.2.2.2 t ht).2⟩⟩
  · intro t _ _
    exact ⟨hnot_pre (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) ((hbr b).1 t).2.2.1,
      hnot_pre (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
        (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) ((hbr b).1 t).2.2.2⟩
  · exact hnot_pre (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
      (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
      (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
      (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide)) (hbr b).2.1
  · intro used' hsub' hconn' hbot' hseg' hmem'
    have hadj_bm : (formulaGraph xs ψ).toSimpleGraph.Adj (botNode j) (midNode j) :=
      (adj_midNode_iff hj hpar).2 (Or.inl rfl) |>.symm
    have hadj_mt : (formulaGraph xs ψ).toSimpleGraph.Adj (midNode j) (topNode (j + 1)) :=
      (adj_midNode_iff hj hpar).2 (Or.inr rfl)
    have hnot_bm' : s(botNode j, midNode j) ∉ used' := by
      intro hm
      rcases hmem' _ hm with h | ⟨t, _, _, h | h | ⟨_, h | h⟩⟩ | ⟨t, _, _, h | h⟩ | h
      · exact hnot_pre (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (hunp b).2.2.2.1 h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
    have hnot_mt' : s(midNode j, topNode (j + 1)) ∉ used' := by
      intro hm
      rcases hmem' _ hm with h | ⟨t, _, _, h | h | ⟨_, h | h⟩⟩ | ⟨t, _, _, h | h⟩ | h
      · exact hnot_pre (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (hunp b).2.2.2.2.1 h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
    rw [edgeGeographyWins_iff]
    refine ⟨midNode j, hadj_bm, mem_vertices_of_adj hadj_bm, hnot_bm', ?_⟩
    rw [edgeGeographyWins_of_unique_move hadj_mt (mem_vertices_of_adj hadj_mt) (by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide), hnot_mt'⟩)
      (fun u hu hnu => by
        rw [adj_midNode_iff hj hpar] at hu
        rcases hu with rfl | rfl
        · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnu
        · rfl)]
    rw [not_not]
    have hnot_fin : ∀ {e : Sym2 ℕ},
        e ≠ s(midNode j, topNode (j + 1)) → e ≠ s(botNode j, midNode j) →
        (∀ t, e ≠ s(u1Node j b t, mNode j b t) ∧ e ≠ s(mNode j b t, u2Node j b t) ∧
          e ≠ s(u2Node j b t, vNode j b t) ∧ e ≠ s(vNode j b t, u1Node j b (t + 1)) ∧
          ∀ ht : t < (occClauses xs ψ j b).length,
            e ≠ s(clauseNode ((occClauses xs ψ j b)[t]), u1Node j b t) ∧
            e ≠ s(clauseNode ((occClauses xs ψ j b)[t]), u2Node j b t)) →
        e ≠ s(u2Node j b (segCount xs ψ j b - 1), botNode j) →
        e ∉ pre → e ∉ used →
        e ∉ s(midNode j, topNode (j + 1)) :: s(botNode j, midNode j) :: used' := by
      intro e h1 h2 ht h3 hp hu hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | rfl | hm'
      · exact h1 rfl
      · exact h2 rfl
      · rcases hmem' e hm' with h | ⟨t, _, _, h | h | ⟨hto, h | h⟩⟩ | ⟨t, _, _, h | h⟩ | h
        · rcases List.mem_append.1 h with hp' | hu'
          · exact hp hp'
          · exact hu hu'
        · exact (ht t).1 h
        · exact (ht t).2.1 h
        · exact ((ht t).2.2.2.2 hto).1 h
        · exact ((ht t).2.2.2.2 hto).2 h
        · exact (ht t).2.2.1 h
        · exact (ht t).2.2.2.1 h
        · exact h3 h
    refine hnext b _ (validUsed_extend hV
      (fun e he => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (hsub' e (List.mem_append_right _ he))))
      (fun e he => ?_) (fun _ => ?_) (fun h => by omega)
      (fun k hk => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hconn' k hk).1),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hconn' k hk).2)⟩)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hbot'))
      (fun k hk => (hseg' k hk).imp
        (fun ⟨a, c⟩ => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ a),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ c)⟩)
        (fun ⟨hko, a, c⟩ => ⟨hko, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ a),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ c)⟩)))
    · simp only [List.mem_cons] at he
      rcases he with rfl | rfl | he'
      · exact Or.inr (Or.inr (Or.inl (by simp [hpar, j])))
      · exact Or.inr (Or.inr (Or.inl (by simp [hpar, j])))
      · rcases hmem' e he' with h | ⟨t, _, ht, h | h | ⟨hto, h | h⟩⟩ | ⟨t, _, ht, h | h⟩ | rfl
        · rcases List.mem_append.1 h with hp | hu
          · rcases hpre e hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inr (Or.inl (by simp [normalBranchEdges_eq_append, hpar, j]))
            · exact Or.inr (Or.inl (by simp [normalBranchEdges_eq_append, hpar, j]))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hpar, Or.inl rfl⟩)))
            · exact Or.inr (Or.inl (by simp [normalBranchEdges_eq_append, hpar, j]))
            · exact Or.inr (Or.inl (by simp [normalBranchEdges_eq_append, hpar, j]))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hpar, Or.inr (Or.inl rfl)⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hpar, Or.inr (Or.inr (Or.inl rfl))⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hpar, Or.inr (Or.inr (Or.inr rfl))⟩)))
          · exact Or.inl hu
        · exact Or.inr (Or.inl (by
            simp only [normalBranchEdges_eq_append, List.mem_append, List.mem_flatMap,
              List.mem_range, List.mem_cons]
            exact Or.inl (Or.inl (Or.inr ⟨t, ht, Or.inl h⟩))))
        · exact Or.inr (Or.inl (by
            simp only [normalBranchEdges_eq_append, List.mem_append, List.mem_flatMap,
              List.mem_range, List.mem_cons]
            exact Or.inl (Or.inl (Or.inr ⟨t, ht, Or.inr (Or.inl h)⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, hto, Or.inl h⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, hto, Or.inr h⟩)))
        · exact Or.inr (Or.inl (by
            simp only [normalBranchEdges_eq_append, List.mem_append, List.mem_flatMap,
              List.mem_range, List.mem_cons]
            exact Or.inl (Or.inr ⟨t, ht, Or.inl h⟩)))
        · exact Or.inr (Or.inl (by
            simp only [normalBranchEdges_eq_append, List.mem_append, List.mem_flatMap,
              List.mem_range, List.mem_cons]
            exact Or.inl (Or.inr ⟨t, ht, Or.inr (Or.inl h)⟩)))
        · exact Or.inr (Or.inl (by simp [normalBranchEdges_eq_append, j]))
    · refine ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (hsub' _ (List.mem_append_left _ hwc))),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub' _ (List.mem_append_left _ hcu))),
        List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rcases h3 with ⟨a, c, d⟩ | ⟨a, c, d⟩
        · left
          refine ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hsub' _ (List.mem_append_left _ a))),
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub' _ (List.mem_append_left _ c))),
            hnot_fin (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
                sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
                fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩⟩)
              (sym2_ne_of_tags (by decide)) d (hunp b).2.2.1⟩
        · right
          refine ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hsub' _ (List.mem_append_left _ a))),
            hnot_fin (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
                sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
                fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩⟩)
              (sym2_ne_of_tags (by decide)) c (hunp b).1,
            hnot_fin (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
                sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
                fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩⟩)
              (sym2_ne_of_tags (by decide)) d (hunp b).2.1⟩
      · exact hnot_fin (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩⟩)
          (sym2_ne_of_tags (by decide)) h4.1 (hunp (!b)).1
      · exact hnot_fin (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩⟩)
          (sym2_ne_of_tags (by decide)) h4.2.1 (hunp (!b)).2.1
      · exact hnot_fin (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩⟩)
          (sym2_ne_of_tags (by decide)) h4.2.2 (hunp (!b)).2.2.1
      · exact hnot_fin (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩⟩)
          (sym2_ne_of_tags (by decide)) hwc' ((hbr (!b)).2.2.1 hpar).1
      · exact hnot_fin (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
          (fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
            fun _ => ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩⟩)
          (sym2_ne_of_tags (by decide)) hcu' ((hbr (!b)).2.2.1 hpar).2
/-- Player 1 loses across an even variable diamond when both branches lose. -/
theorem cross_even_loses {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {used : List (Sym2 ℕ)} (hV : ValidUsed xs ψ z used)
    (hj : z.length < xs.length) (hpar : z.length % 2 = 0)
    (hnext : ∀ (b : Bool) (used' : List (Sym2 ℕ)),
      ValidUsed xs ψ (z ++ [b]) used' →
      EdgeGeographyWins (formulaGraph xs ψ) used' (topNode (z.length + 1))) :
    ¬ EdgeGeographyWins (formulaGraph xs ψ) used (topNode z.length) := by
  set j := z.length
  have hbr := fun b : Bool => validUsed_not_mem_branch hV (j := j) (b := b) (fun h => by omega)
  have hunp := fun b : Bool => validUsed_not_mem_unplayed hV b
  have hfrom_u1 := cross_even_loses_from_u1 hV hj hpar hnext
  -- Analyze Player 1's move from `topNode j`!
  rw [not_edgeGeographyWins_iff]
  intro w hadj _ hnot
  rw [adj_topNode_iff (le_of_lt hj)] at hadj
  rcases hadj with ⟨hpos, ⟨hpar', rfl⟩ | ⟨hpar', rfl⟩⟩ | ⟨-, -, b, rfl | rfl⟩ | ⟨-, hpar',
    _⟩ | ⟨heq, _⟩
  · have := ((hV.1 (j - 1) (by omega)).1 hpar').2.2.2.1
    rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this; exact absurd this hnot
  · have := ((hV.1 (j - 1) (by omega)).2.1 hpar').2
    rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this; exact absurd this hnot
  · -- Case 1: `topNode j → aNode j b`
    have hadj_aw : (formulaGraph xs ψ).toSimpleGraph.Adj (aNode j b) (wNode j b) :=
      (adj_aNode_iff hj hpar).2 (Or.inr rfl)
    rw [edgeGeographyWins_iff]
    refine ⟨wNode j b, hadj_aw, mem_vertices_of_adj hadj_aw, by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide), (hunp b).2.1⟩, ?_⟩
    rw [not_edgeGeographyWins_iff]
    intro u hadj_u _ hnot_u
    rw [adj_wNode_iff hj hpar] at hadj_u
    rcases hadj_u with rfl | rfl | rfl
    · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnot_u
    · -- Subcase 1a: `wNode j b → topNode j`, P2 plays `topNode j → aNode j (!b)`, forcing P1 to
      -- `wNode j (!b)`, where P2 returns to `topNode j` and leaves P1 with no moves!
      have hadj_ta' : (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) (aNode j (!b)) :=
        (adj_aNode_iff hj hpar).2 (Or.inl rfl) |>.symm
      have hadj_aw' : (formulaGraph xs ψ).toSimpleGraph.Adj (aNode j (!b)) (wNode j (!b)) :=
        (adj_aNode_iff hj hpar).2 (Or.inr rfl)
      have hadj_wt' : (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j (!b)) (topNode j) :=
        (adj_wNode_iff hj hpar).2 (Or.inr (Or.inl rfl))
      rw [edgeGeographyWins_iff]
      refine ⟨aNode j (!b), hadj_ta', mem_vertices_of_adj hadj_ta', by
        simp only [List.mem_cons, not_or]
        refine ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide), ?_, (hunp (!b)).1⟩
        intro h; rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
        · simp only [aNode_eq_pair, Nat.pair_eq_pair, true_and] at hb; cases b <;> simp at hb
        · exact pair_ne_of_ne (by decide) ha, ?_⟩
      rw [edgeGeographyWins_of_unique_move hadj_aw' (mem_vertices_of_adj hadj_aw') (by
        simp only [List.mem_cons, not_or]
        refine ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide), ?_,
          sym2_ne_of_tags (by decide), (hunp (!b)).2.1⟩
        intro h; rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
        · simp only [aNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; cases b <;> simp at ha
        · exact pair_ne_of_ne (by decide) ha)
        (fun v hv hnv => by
          rw [adj_aNode_iff hj hpar] at hv
          rcases hv with rfl | rfl
          · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnv
          · rfl)]
      rw [not_not]
      refine edgeGeographyWins_of_adj_dead hadj_wt' (mem_vertices_of_adj hadj_wt') ?_ ?_
      · simp only [List.mem_cons, not_or]
        refine ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide), ?_,
          sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
          by rw [Sym2.eq_swap]; exact (hunp (!b)).2.2.1⟩
        intro h; rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨_, hb⟩
        · simp only [wNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; cases b <;> simp at ha
        · exact pair_ne_of_ne (by decide) hb
      · intro x hx
        rw [adj_topNode_iff (le_of_lt hj)] at hx
        rcases hx with ⟨hpos, ⟨hp', rfl⟩ | ⟨hp', rfl⟩⟩ | ⟨-, -, b', rfl | rfl⟩ | ⟨-, hp', _⟩ |
          ⟨he, _⟩
        · have := ((hV.1 (j - 1) (by omega)).1 hp').2.2.2.1
          rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this)))))
        · have := ((hV.1 (j - 1) (by omega)).2.1 hp').2
          rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this)))))
        · by_cases hb' : b' = b
          · subst hb'
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
          · have : b' = !b := by cases b <;> cases b' <;> simp at hb' ⊢
            subst this
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · by_cases hb' : b' = b
          · subst hb'
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (by rw [Sym2.eq_swap]; exact List.mem_cons_self)))
          · have : b' = !b := by cases b <;> cases b' <;> simp at hb' ⊢
            subst this
            rw [Sym2.eq_swap]; exact List.mem_cons_self
        · omega
        · omega
    · -- Subcase 1b: normal `wNode j b → cNode j b`
      have hadj_cu : (formulaGraph xs ψ).toSimpleGraph.Adj (cNode j b) (u1Node j b 0) :=
        (adj_cNode_iff hj hpar).2 (Or.inr rfl)
      rw [edgeGeographyWins_iff]
      refine ⟨u1Node j b 0, hadj_cu, mem_vertices_of_adj hadj_cu, by
        simp only [List.mem_cons, not_or]
        exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
          sym2_ne_of_tags (by decide), ((hbr b).2.2.1 hpar).2⟩, ?_⟩
      exact hfrom_u1 b
        [s(cNode j b, u1Node j b 0), s(wNode j b, cNode j b),
         s(aNode j b, wNode j b), s(topNode j, aNode j b)]
        (by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            rcases he with rfl | rfl | rfl | rfl <;> simp [j])
        (by simp [j]) (by simp [j])
        (Or.inl ⟨by simp [j], by simp [j],
          by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
             exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
               sym2_ne_of_tags (by decide),
               fun h => by rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
                           · exact pair_ne_of_ne (by decide) hb
                           · exact pair_ne_of_ne (by decide) ha⟩⟩)
        (by
          refine ⟨?_, ?_, ?_⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            refine ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
              sym2_ne_of_tags (by decide), ?_⟩
            intro h; rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
            · simp only [aNode_eq_pair, Nat.pair_eq_pair, true_and] at hb; cases b <;> simp at hb
            · exact pair_ne_of_ne (by decide) ha
          · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            refine ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide), ?_,
              sym2_ne_of_tags (by decide)⟩
            intro h; rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
            · simp only [aNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; cases b <;> simp at ha
            · exact pair_ne_of_ne (by decide) ha
          · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            refine ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
              sym2_ne_of_tags (by decide), ?_⟩
            intro h; rcases pair_sym2_eq h with ⟨_, hb⟩ | ⟨ha, _⟩
            · exact pair_ne_of_ne (by decide) hb
            · exact pair_ne_of_ne (by decide) ha)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            refine ⟨sym2_ne_of_tags (by decide), ?_,
              sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩
            intro h; rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
            · simp only [wNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; cases b <;> simp at ha
            · exact pair_ne_of_ne (by decide) ha)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            refine ⟨?_, sym2_ne_of_tags (by decide),
              sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide)⟩
            intro h; rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
            · simp only [cNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; cases b <;> simp at ha
            · exact pair_ne_of_ne (by decide) ha)
  · -- Case 2: chord `topNode j → wNode j b`! P2 plays `wNode j b → aNode j b`, forcing P1 back to
    -- `topNode j`, then P2 plays `topNode j → aNode j (!b) → wNode j (!b) → topNode j`, killing P1!
    have hadj_wa : (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j b) (aNode j b) :=
      (adj_wNode_iff hj hpar).2 (Or.inl rfl)
    have hadj_at : (formulaGraph xs ψ).toSimpleGraph.Adj (aNode j b) (topNode j) :=
      (adj_aNode_iff hj hpar).2 (Or.inl rfl)
    have hadj_ta' : (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) (aNode j (!b)) :=
      (adj_aNode_iff hj hpar).2 (Or.inl rfl) |>.symm
    have hadj_aw' : (formulaGraph xs ψ).toSimpleGraph.Adj (aNode j (!b)) (wNode j (!b)) :=
      (adj_aNode_iff hj hpar).2 (Or.inr rfl)
    have hadj_wt' : (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j (!b)) (topNode j) :=
      (adj_wNode_iff hj hpar).2 (Or.inr (Or.inl rfl))
    rw [edgeGeographyWins_iff]
    refine ⟨aNode j b, hadj_wa, mem_vertices_of_adj hadj_wa, by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide), by rw [Sym2.eq_swap]; exact (hunp b).2.1⟩, ?_⟩
    rw [edgeGeographyWins_of_unique_move hadj_at (mem_vertices_of_adj hadj_at) (by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
        by rw [Sym2.eq_swap]; exact (hunp b).1⟩)
      (fun u hu hnu => by
        rw [adj_aNode_iff hj hpar] at hu
        rcases hu with rfl | rfl
        · rfl
        · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnu)]
    rw [not_not, edgeGeographyWins_iff]
    refine ⟨aNode j (!b), hadj_ta', mem_vertices_of_adj hadj_ta', by
      simp only [List.mem_cons, not_or]
      refine ⟨?_, sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide), (hunp (!b)).1⟩
      intro h; rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact pair_ne_of_ne (by decide) ha
      · simp only [aNode_eq_pair, Nat.pair_eq_pair, true_and] at hb; cases b <;> simp at hb, ?_⟩
    rw [edgeGeographyWins_of_unique_move hadj_aw' (mem_vertices_of_adj hadj_aw') (by
      simp only [List.mem_cons, not_or]
      refine ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide), ?_,
        sym2_ne_of_tags (by decide), (hunp (!b)).2.1⟩
      intro h; rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · exact pair_ne_of_ne (by decide) ha
      · simp only [aNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; cases b <;> simp at ha)
      (fun u hu hnu => by
        rw [adj_aNode_iff hj hpar] at hu
        rcases hu with rfl | rfl
        · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnu
        · rfl)]
    rw [not_not]
    refine edgeGeographyWins_of_adj_dead hadj_wt' (mem_vertices_of_adj hadj_wt') ?_ ?_
    · simp only [List.mem_cons, not_or]
      refine ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
        sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide), ?_,
        by rw [Sym2.eq_swap]; exact (hunp (!b)).2.2.1⟩
      intro h; rcases pair_sym2_eq h with ⟨ha, _⟩ | ⟨ha, _⟩
      · exact pair_ne_of_ne (by decide) ha
      · simp only [wNode_eq_pair, Nat.pair_eq_pair, true_and] at ha; cases b <;> simp at ha
    · intro x hx
      rw [adj_topNode_iff (le_of_lt hj)] at hx
      rcases hx with ⟨hpos, ⟨hp', rfl⟩ | ⟨hp', rfl⟩⟩ | ⟨-, -, b', rfl | rfl⟩ | ⟨-, hp', _⟩ |
        ⟨he, _⟩
      · have := ((hV.1 (j - 1) (by omega)).1 hp').2.2.2.1
        rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this)))))
      · have := ((hV.1 (j - 1) (by omega)).2.1 hp').2
        rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this)))))
      · by_cases hb' : b' = b
        · subst hb'
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (by rw [Sym2.eq_swap]; exact List.mem_cons_self)))
        · have : b' = !b := by cases b <;> cases b' <;> simp at hb' ⊢
          subst this
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · by_cases hb' : b' = b
        · subst hb'
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
        · have : b' = !b := by cases b <;> cases b' <;> simp at hb' ⊢
          subst this
          rw [Sym2.eq_swap]; exact List.mem_cons_self
      · omega
      · omega
  · omega
  · omega

end UndirectedEdgeGeography

end Cslib.Complexity
