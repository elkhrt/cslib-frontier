/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Problems.ThreeMinBisectionDefs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.List.GetD

/-!
# Regularity and Forward Soundness of Cubic Torus Gadget

Proves that `torusReductionGraph x.graph` is a well-formed 3-regular simple graph and that every
bisection of `x` lifts to a bisection of `⟨torusReductionGraph x.graph, 2 * x.bound⟩`.

## Main results

* `CslibFrontier.Complexity.MinBisection.torusReductionGraph_wf_and_3reg`: well-formedness &
  3-regularity.
* `CslibFrontier.Complexity.MinBisection.torusReductionGraph_forward`: forward bisection
  preservation.
-/

public section

namespace CslibFrontier.Complexity.MinBisection

open Cslib.Complexity

private theorem getD_mem_of_lt {l : List ℕ} {i : ℕ} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

private theorem idxOf_getElem_of_nodup {l : List ℕ} (hnd : l.Nodup) (i : ℕ) (hi : i < l.length) :
    l.idxOf l[i] = i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    cases i with
    | zero => simp
    | succ i' =>
      have hi' : i' < t.length := by simpa using hi
      have hne : a ≠ t[i'] := fun h => hnd.1 (h ▸ List.getElem_mem hi')
      simp only [List.getElem_cons_succ, List.idxOf_cons_ne _ hne, ih hnd.2 i' hi']

/-- Well-formedness and 3-regularity of `torusReductionGraph x.graph`. -/
theorem torusReductionGraph_wf_and_3reg (x : MinBisectionInstance) :
    (torusReductionGraph x.graph).vertices.Nodup ∧
      (∀ e ∈ (torusReductionGraph x.graph).edges,
        e.1 ∈ (torusReductionGraph x.graph).vertices ∧
          e.2 ∈ (torusReductionGraph x.graph).vertices) ∧
      (∀ v : {v // v ∈ (torusReductionGraph x.graph).vertices},
        (torusReductionGraph x.graph).induced.degree v = 3) := by
  classical
  set V := x.graph.distinctVertices
  set n := V.length
  set K := 4 * n * n + 8
  have hK_ge : 8 ≤ K := by omega
  have hK_pos : 0 < K := by omega
  let nbrs := fun u =>
    (List.range n).filter fun v => x.graph.adjBool (V.getD u 0) (V.getD v 0)
  let internalEdges := (List.range n).flatMap fun u => torusGadgetEdges K u (nbrs u).length
  let crossEdges := (List.range n).flatMap fun u =>
    ((List.range n).filter fun v =>
      decide (u < v) && x.graph.adjBool (V.getD u 0) (V.getD v 0)).flatMap fun v =>
        let i := (nbrs u).idxOf v
        let j := (nbrs v).idxOf u
        [(torusVid K u i i 0, torusVid K v j j 0),
         (torusVid K u i i 1, torusVid K v j j 1)]
  set G' : Graph := ⟨List.range (4 * K * K * n), internalEdges ++ crossEdges⟩
  have hV_nd : V.Nodup := Graph.nodup_distinctVertices x.graph
  have hV_inj : ∀ {i j}, i < n → j < n → V.getD i 0 = V.getD j 0 → i = j :=
    fun {i j} hi hj h => by
      have h1 : V[i] = V[j] := by
        rw [List.getD_eq_getElem _ 0 hi, List.getD_eq_getElem _ 0 hj] at h; exact h
      exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hV_nd)
        (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h1)
  have hnbrs_len : ∀ u < n, (nbrs u).length < K := fun u _ => by
    have h1 : (nbrs u).length ≤ (List.range n).length := List.length_filter_le _ _
    rw [List.length_range] at h1; dsimp only [K]; nlinarith
  have hnbrs_nd : ∀ u, (nbrs u).Nodup := fun u => List.nodup_range.filter _
  have hmem_nbrs : ∀ u v, v ∈ nbrs u ↔
    v < n ∧ x.graph.toSimpleGraph.Adj (V.getD u 0) (V.getD v 0) :=
    fun u v => by simp [nbrs, Graph.adjBool_eq_true_iff]
  have hidx_lt : ∀ u v, u < n → v < n → x.graph.toSimpleGraph.Adj (V.getD u 0) (V.getD v 0) →
      (nbrs u).idxOf v < (nbrs u).length := fun u v _ hv hadj =>
    List.idxOf_lt_length_of_mem ((hmem_nbrs u v).mpr ⟨hv, hadj⟩)
  have hidx_inj : ∀ u v1 v2, v1 ∈ nbrs u → v2 ∈ nbrs u →
      (nbrs u).idxOf v1 = (nbrs u).idxOf v2 → v1 = v2 := fun u v1 v2 h1 _ heq =>
    (List.idxOf_inj h1).mp heq
  have hG'_verts : G'.vertices = List.range (4 * K * K * n) := rfl
  have hG'_eq : torusReductionGraph x.graph = G' := rfl
  rw [hG'_eq]
  have hG'_wf : G'.vertices.Nodup ∧ (∀ e ∈ G'.edges, e.1 ∈ G'.vertices ∧
    e.2 ∈ G'.vertices) := by
    refine ⟨List.nodup_range, ?_⟩
    intro e he
    simp only [G', List.mem_append, List.mem_range] at he ⊢
    rcases he with hi | hc
    · obtain ⟨u, hu, heu⟩ := List.mem_flatMap.mp hi
      rw [List.mem_range] at hu
      obtain ⟨r, hr, her⟩ := List.mem_flatMap.mp heu
      obtain ⟨c, hc, hec⟩ := List.mem_flatMap.mp her
      rw [List.mem_range] at hr hc
      unfold torusCellEdges at hec
      split_ifs at hec <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hec <;>
        rcases hec with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨torusVid_lt hu hr hc (by omega),
               torusVid_lt hu (by first | exact hr | exact Nat.mod_lt _ hK_pos)
                 (by first | exact hc | exact Nat.mod_lt _ hK_pos) (by omega)⟩
    · obtain ⟨u, hu, heu⟩ := List.mem_flatMap.mp hc
      rw [List.mem_range] at hu
      obtain ⟨v, hv, hev⟩ := List.mem_flatMap.mp heu
      simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
        Graph.adjBool_eq_true_iff] at hv
      have hi := (hidx_lt u v hu hv.1 hv.2.2).trans (hnbrs_len u hu)
      have hj := (hidx_lt v u hv.1 hu hv.2.2.symm).trans (hnbrs_len v hv.1)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
      rcases hev with rfl | rfl <;>
        exact ⟨torusVid_lt hu hi hi (by omega), torusVid_lt hv.1 hj hj (by omega)⟩
  -- Prove G' is 3-regular!
  have hG'_3reg : ∀ v : {v // v ∈ G'.vertices}, G'.induced.degree v = 3 := by
    intro ⟨w, hw⟩
    rw [hG'_verts, List.mem_range] at hw
    -- Decode w = torusVid K u r c t
    set t := w % 4
    set q1 := w / 4
    set c := q1 % K
    set q2 := q1 / K
    set r := q2 % K
    set u := q2 / K
    have ht : t < 4 := Nat.mod_lt _ (by omega)
    have hc : c < K := Nat.mod_lt _ hK_pos
    have hr : r < K := Nat.mod_lt _ hK_pos
    have hu : u < n := by
      have hq1 : q1 < K * K * n := Nat.div_lt_of_lt_mul (by nlinarith)
      have hq2 : q2 < K * n :=
        Nat.div_lt_of_lt_mul (show q1 < K * (K * n) by nlinarith)
      exact Nat.div_lt_of_lt_mul hq2
    have hw_eq : w = torusVid K u r c t := by
      unfold torusVid
      have h1 : w = q1 * 4 + t := by dsimp only [q1, t]; omega
      have h2 : q1 = q2 * K + c := by
        have := Nat.div_add_mod q1 K; rw [Nat.mul_comm] at this; dsimp only [q2, c]; omega
      have h3 : q2 = u * K + r := by
        have := Nat.div_add_mod q2 K; rw [Nat.mul_comm] at this; dsimp only [u, r]; omega
      nlinarith
    -- Compute exact 3-element neighbor set of w
    have hmem_int : ∀ x1 x2, (x1, x2) ∈ internalEdges ↔
        ∃ u0 < n, ∃ r0 < K, ∃ c0 < K,
          ((x1 = torusVid K u0 r0 c0 0 ∧ x2 = torusVid K u0 r0 c0 2) ∨
           (x1 = torusVid K u0 r0 c0 2 ∧ x2 = torusVid K u0 r0 ((c0 + 1) % K) 0) ∨
           (x1 = torusVid K u0 r0 c0 1 ∧ x2 = torusVid K u0 r0 c0 3) ∨
           (x1 = torusVid K u0 r0 c0 3 ∧ x2 = torusVid K u0 ((r0 + 1) % K) c0 1) ∨
           (x1 = torusVid K u0 r0 c0 2 ∧ x2 = torusVid K u0 r0 c0 3) ∨
           (¬(r0 = c0 ∧ r0 < (nbrs u0).length) ∧
             x1 = torusVid K u0 r0 c0 0 ∧ x2 = torusVid K u0 r0 c0 1)) := by
      intro x1 x2
      simp only [internalEdges, torusGadgetEdges, torusCellEdges, List.mem_flatMap, List.mem_range]
      constructor
      · rintro ⟨u0, hu0, r0, hr0, c0, hc0, h⟩
        refine ⟨u0, hu0, r0, hr0, c0, hc0, ?_⟩
        split_ifs at h with hport
        · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
          rcases h with h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and] at hport
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
          rcases h with h | h | h | h | h | h
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨fun ⟨ha, hb⟩ => hport ha hb, h⟩))))
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · rintro ⟨u0, hu0, r0, hr0, c0, hc0, h⟩
        refine ⟨u0, hu0, r0, hr0, c0, hc0, ?_⟩
        split_ifs with hport
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hport
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
          rcases h with h | h | h | h | h | ⟨hno, _⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
          · exact absurd hport hno
        · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
          rcases h with h | h | h | h | h | ⟨_, h⟩
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
          · exact Or.inl h
    have hmem_cross : ∀ x1 x2, (x1, x2) ∈ crossEdges ↔
        ∃ u0 < n, ∃ v0 < n, u0 < v0 ∧
          x.graph.toSimpleGraph.Adj (V.getD u0 0) (V.getD v0 0) ∧
          ((x1 = torusVid K u0 ((nbrs u0).idxOf v0) ((nbrs u0).idxOf v0) 0 ∧
            x2 = torusVid K v0 ((nbrs v0).idxOf u0) ((nbrs v0).idxOf u0) 0) ∨
           (x1 = torusVid K u0 ((nbrs u0).idxOf v0) ((nbrs u0).idxOf v0) 1 ∧
            x2 = torusVid K v0 ((nbrs v0).idxOf u0) ((nbrs v0).idxOf u0) 1)) := by
      intro x1 x2
      simp only [crossEdges, List.mem_flatMap, List.mem_filter, List.mem_range,
        Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff,
        List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      constructor
      · rintro ⟨u0, hu0, v0, ⟨hv0, huv, hadj⟩, h⟩
        exact ⟨u0, hu0, v0, hv0, huv, hadj, h⟩
      · rintro ⟨u0, hu0, v0, hv0, huv, hadj, h⟩
        exact ⟨u0, hu0, v0, ⟨hv0, huv, hadj⟩, h⟩
    -- Prove `G'.induced.degree ⟨w, hw⟩ = 3` by identifying the exact 3 neighbors for each `t
    -- ∈ {0,1,2,3}`!
    have hdeg_three : ∀ (z1 z2 z3 : ℕ), z1 < 4 * K * K * n → z2 < 4 * K * K * n →
        z3 < 4 * K * K * n → z1 ≠ z2 → z1 ≠ z3 → z2 ≠ z3 →
        (∀ z, z < 4 * K * K * n → (G'.toSimpleGraph.Adj w z ↔ z = z1 ∨ z = z2 ∨ z = z3)) →
        G'.induced.degree ⟨w, List.mem_range.mpr hw⟩ = 3 := by
      intro z1 z2 z3 hz1 hz2 hz3 h12 h13 h23 hiff
      have hset : G'.induced.neighborFinset ⟨w, List.mem_range.mpr hw⟩ =
          {⟨z1, List.mem_range.mpr hz1⟩, ⟨z2, List.mem_range.mpr hz2⟩,
           ⟨z3, List.mem_range.mpr hz3⟩} := by
        ext ⟨z, hz⟩
        simp only [SimpleGraph.mem_neighborFinset, Graph.induced_adj, Finset.mem_insert,
          Finset.mem_singleton, Subtype.mk.injEq]
        exact hiff z (List.mem_range.mp hz)
      rw [SimpleGraph.degree, hset, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · intro h; simp only [Finset.mem_singleton, Subtype.mk.injEq] at h; exact h23 h
      · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq] at h
        rcases h with h | h
        · exact h12 h
        · exact h13 h
    -- Case split on `t = 0, 1, 2, 3`
    have ht4 : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases ht4 with ht0 | ht1 | ht2 | ht3
    · -- t = 0 (vertex a_{r, c})
      have hw0 : w = torusVid K u r c 0 := ht0 ▸ hw_eq
      set cPrev := (c + K - 1) % K
      have hcPrev : cPrev < K := Nat.mod_lt _ hK_pos
      have hcPrev_next : (cPrev + 1) % K = c := by
        change ((c + K - 1) % K + 1) % K = c
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show c + K - 1 + 1 = c + K by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hc]
      have hcPrev_ne : cPrev ≠ c := by
        intro h; have := congrArg (· % K) (show cPrev + 1 = c + 1 by omega)
        rw [hcPrev_next] at this
        have h1 : (c + 1) % K = c := by
          have hc1 : (c + 1) % K = c := by simpa [Nat.mod_eq_of_lt hc] using this.symm
          exact hc1
        by_cases hlast : c + 1 = K
        · rw [hlast, Nat.mod_self] at h1; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
      by_cases hport : r = c ∧ r < (nbrs u).length
      · -- Port vertex a_{r, r}: neighbors are c_{r,r}, c_{r, cPrev}, and partner a_{v, j, j}
        set v := (nbrs u).getD r 0
        have hv_mem : v ∈ nbrs u := getD_mem_of_lt hport.2
        have hv_lt : v < n := ((hmem_nbrs u v).mp hv_mem).1
        have huv_adj : x.graph.toSimpleGraph.Adj (V.getD u 0) (V.getD v 0) :=
          ((hmem_nbrs u v).mp hv_mem).2
        have huv_ne : u ≠ v := fun h => huv_adj.ne (by rw [h])
        have hidx_r : (nbrs u).idxOf v = r := by
          have hnd := hnbrs_nd u
          have hget : (nbrs u)[r]'(hport.2) = v := List.getD_eq_getElem _ 0 hport.2 |>.symm
          have hidx := idxOf_getElem_of_nodup hnd r hport.2
          simpa [hget] using hidx
        set j := (nbrs v).idxOf u
        have hj_lt : j < K := (hidx_lt v u hv_lt hu huv_adj.symm).trans (hnbrs_len v hv_lt)
        refine hdeg_three (torusVid K u r c 2) (torusVid K u r cPrev 2) (torusVid K v j j 0)
          (torusVid_lt hu hr hc (by omega)) (torusVid_lt hu hr hcPrev (by omega))
          (torusVid_lt hv_lt hj_lt hj_lt (by omega))
          (fun h =>
            hcPrev_ne (torusVid_injective hK_pos hr hc (by omega) hr hcPrev (by omega)
              h).2.2.1.symm)
          (fun h => huv_ne (torusVid_injective hK_pos hr hc (by omega) hj_lt hj_lt (by omega) h).1)
          (fun h =>
            huv_ne (torusVid_injective hK_pos hr hcPrev (by omega) hj_lt hj_lt (by omega) h).1)
          (fun z hz => ?_)
        rw [hw0, Graph.toSimpleGraph_adj]
        constructor
        · rintro ⟨hne, hmem⟩
          simp only [G', List.mem_append] at hmem
          rcases hmem with (hint | hcr) | (hint | hcr)
          · rw [hmem_int] at hint
            obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
            rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨hno,
              h1, rfl⟩
            · obtain ⟨rfl, rfl, rfl, _⟩ :=
              torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1
              exact Or.inl rfl
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · obtain ⟨rfl, rfl, rfl, _⟩ :=
              torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1
              exact absurd hport hno
          · rw [hmem_cross] at hcr
            obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩ := hcr
            · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
              obtain ⟨rfl, hr_eq, _, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1
              have hv_eq : v0 = v := by
                rw [← hidx_r] at hr_eq
                exact hidx_inj u v0 v ((hmem_nbrs u v0).mpr ⟨hv0, hadj0⟩) hv_mem hr_eq.symm
              subst hv_eq; exact Or.inr (Or.inr rfl)
            · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
              have := (torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1).2.2.2;
                  omega
          · rw [hmem_int] at hint
            obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
            rcases h with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨_, rfl,
              h2⟩
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · obtain ⟨rfl, rfl, hc_eq, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega) hr0 (Nat.mod_lt _ hK_pos)
                  (by omega) h2
              have hc0_eq : c0 = cPrev := by
                have := congrArg (fun a => (a + K - 1) % K) hc_eq
                rw [show (c0 + 1) % K + K - 1 = (c0 + 1) % K + (K - 1) by omega,
                    Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
                    show c0 + 1 + (K - 1) = c0 + K by omega, Nat.add_mod_right,
                    Nat.mod_eq_of_lt hc0] at this
                exact this.symm
              subst hc0_eq; exact Or.inr (Or.inl rfl)
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega)
              (Nat.mod_lt _ hK_pos) hc0 (by omega) h2).2.2.2; omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
          · rw [hmem_cross] at hcr
            obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩ := hcr
            · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
              obtain ⟨rfl, hr_eq, _, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2
              have hv_eq : u0 = v := by
                rw [← hidx_r] at hr_eq
                exact hidx_inj u u0 v ((hmem_nbrs u u0).mpr ⟨hu0,
                  hadj0.symm⟩) hv_mem hr_eq.symm
              subst hv_eq; exact Or.inr (Or.inr rfl)
            · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
              have := (torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2).2.2.2;
                  omega
        · rintro (rfl | rfl | rfl)
          · refine ⟨fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega,
              Or.inl (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
                Or.inl ⟨rfl, rfl⟩⟩))⟩
          · refine ⟨fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hr hcPrev (by omega) h).2.2.2; omega,
              Or.inr (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, cPrev, hcPrev,
                Or.inr (Or.inl ⟨rfl, by rw [hcPrev_next]⟩)⟩))⟩
          · refine ⟨fun h =>
            huv_ne (torusVid_injective hK_pos hr hc (by omega) hj_lt hj_lt (by omega) h).1, ?_⟩
            rcases Nat.lt_or_gt_of_ne huv_ne with hlt | hgt
            · exact Or.inl (List.mem_append_right _ ((hmem_cross _ _).mpr
                ⟨u, hu, v, hv_lt, hlt, huv_adj, Or.inl ⟨by rw [hidx_r, hport.1], rfl⟩⟩))
            · exact Or.inr (List.mem_append_right _ ((hmem_cross _ _).mpr
                ⟨v, hv_lt, u, hu, hgt, huv_adj.symm, Or.inl ⟨rfl, by rw [hidx_r, hport.1]⟩⟩))
      · -- Non-port vertex a_{r, c}: neighbors are c_{r,c}, c_{r, cPrev}, b_{r,c}
        refine hdeg_three (torusVid K u r c 2) (torusVid K u r cPrev 2) (torusVid K u r c 1)
          (torusVid_lt hu hr hc (by omega)) (torusVid_lt hu hr hcPrev (by omega))
          (torusVid_lt hu hr hc (by omega))
          (fun h =>
            hcPrev_ne (torusVid_injective hK_pos hr hc (by omega) hr hcPrev (by omega)
              h).2.2.1.symm)
          (fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega)
          (fun h => by have :=
            (torusVid_injective hK_pos hr hcPrev (by omega) hr hc (by omega) h).2.2.2; omega)
          (fun z hz => ?_)
        rw [hw0, Graph.toSimpleGraph_adj]
        constructor
        · rintro ⟨hne, hmem⟩
          simp only [G', List.mem_append] at hmem
          rcases hmem with (hint | hcr) | (hint | hcr)
          · rw [hmem_int] at hint
            obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
            rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨_, h1,
              rfl⟩
            · obtain ⟨rfl, rfl, rfl, _⟩ :=
              torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1
              exact Or.inl rfl
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · obtain ⟨rfl, rfl, rfl, _⟩ :=
              torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1
              exact Or.inr (Or.inr rfl)
          · rw [hmem_cross] at hcr
            obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩ := hcr
            · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
              obtain ⟨rfl, hr_eq, hc_eq, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1
              exact absurd ⟨hr_eq.trans hc_eq.symm, hr_eq ▸ hidx_lt u v0 hu hv0 hadj0⟩ hport
            · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
              have := (torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1).2.2.2;
                  omega
          · rw [hmem_int] at hint
            obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
            rcases h with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨_, rfl,
              h2⟩
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · obtain ⟨rfl, rfl, hc_eq, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega) hr0 (Nat.mod_lt _ hK_pos)
                  (by omega) h2
              have hc0_eq : c0 = cPrev := by
                have := congrArg (fun a => (a + K - 1) % K) hc_eq
                rw [show (c0 + 1) % K + K - 1 = (c0 + 1) % K + (K - 1) by omega,
                    Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
                    show c0 + 1 + (K - 1) = c0 + K by omega, Nat.add_mod_right,
                    Nat.mod_eq_of_lt hc0] at this
                exact this.symm
              subst hc0_eq; exact Or.inr (Or.inl rfl)
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega)
              (Nat.mod_lt _ hK_pos) hc0 (by omega) h2).2.2.2; omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
          · rw [hmem_cross] at hcr
            obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩ := hcr
            · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
              obtain ⟨rfl, hr_eq, hc_eq, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2
              exact absurd ⟨hr_eq.trans hc_eq.symm, hr_eq ▸ hidx_lt u u0 hu hu0 hadj0.symm⟩ hport
            · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
              have := (torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2).2.2.2;
                  omega
        · rintro (rfl | rfl | rfl)
          · refine ⟨fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega,
              Or.inl (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
                Or.inl ⟨rfl, rfl⟩⟩))⟩
          · refine ⟨fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hr hcPrev (by omega) h).2.2.2; omega,
              Or.inr (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, cPrev, hcPrev,
                Or.inr (Or.inl ⟨rfl, by rw [hcPrev_next]⟩)⟩))⟩
          · refine ⟨fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega,
              Or.inl (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hport, rfl, rfl⟩))))⟩))⟩
    · -- t = 1 (vertex b_{r, c})
      have hw1 : w = torusVid K u r c 1 := ht1 ▸ hw_eq
      set rPrev := (r + K - 1) % K
      have hrPrev : rPrev < K := Nat.mod_lt _ hK_pos
      have hrPrev_next : (rPrev + 1) % K = r := by
        change ((r + K - 1) % K + 1) % K = r
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show r + K - 1 + 1 = r + K by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hr]
      have hrPrev_ne : rPrev ≠ r := by
        intro h; have := congrArg (· % K) (show rPrev + 1 = r + 1 by omega)
        rw [hrPrev_next] at this
        have h1 : (r + 1) % K = r := by simpa [Nat.mod_eq_of_lt hr] using this.symm
        by_cases hlast : r + 1 = K
        · rw [hlast, Nat.mod_self] at h1; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
      by_cases hport : r = c ∧ r < (nbrs u).length
      · set v := (nbrs u).getD r 0
        have hv_mem : v ∈ nbrs u := getD_mem_of_lt hport.2
        have hv_lt : v < n := ((hmem_nbrs u v).mp hv_mem).1
        have huv_adj : x.graph.toSimpleGraph.Adj (V.getD u 0) (V.getD v 0) :=
          ((hmem_nbrs u v).mp hv_mem).2
        have huv_ne : u ≠ v := fun h => huv_adj.ne (by rw [h])
        have hidx_r : (nbrs u).idxOf v = r := by
          have hget : (nbrs u)[r]'(hport.2) = v := (List.getD_eq_getElem _ 0 hport.2).symm
          simpa [hget] using idxOf_getElem_of_nodup (hnbrs_nd u) r hport.2
        set j := (nbrs v).idxOf u
        have hj_lt : j < K := (hidx_lt v u hv_lt hu huv_adj.symm).trans (hnbrs_len v hv_lt)
        refine hdeg_three (torusVid K u r c 3) (torusVid K u rPrev c 3) (torusVid K v j j 1)
          (torusVid_lt hu hr hc (by omega)) (torusVid_lt hu hrPrev hc (by omega))
          (torusVid_lt hv_lt hj_lt hj_lt (by omega))
          (fun h =>
            hrPrev_ne (torusVid_injective hK_pos hr hc (by omega) hrPrev hc (by omega) h).2.1.symm)
          (fun h => huv_ne (torusVid_injective hK_pos hr hc (by omega) hj_lt hj_lt (by omega) h).1)
          (fun h =>
            huv_ne (torusVid_injective hK_pos hrPrev hc (by omega) hj_lt hj_lt (by omega) h).1)
          (fun z hz => ?_)
        rw [hw1, Graph.toSimpleGraph_adj]
        constructor
        · rintro ⟨hne, hmem⟩
          simp only [G', List.mem_append] at hmem
          rcases hmem with (hint | hcr) | (hint | hcr)
          · rw [hmem_int] at hint
            obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
            rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨_, h1,
              rfl⟩
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · obtain ⟨rfl, rfl, rfl, _⟩ :=
              torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1
              exact Or.inl rfl
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
          · rw [hmem_cross] at hcr
            obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩ := hcr
            · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
              have := (torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1).2.2.2;
                  omega
            · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
              obtain ⟨rfl, hr_eq, _, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1
              have hv_eq : v0 = v := by
                rw [← hidx_r] at hr_eq
                exact hidx_inj u v0 v ((hmem_nbrs u v0).mpr ⟨hv0, hadj0⟩) hv_mem hr_eq.symm
              subst hv_eq; exact Or.inr (Or.inr rfl)
          · rw [hmem_int] at hint
            obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
            rcases h with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨hno,
              rfl, h2⟩
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 (Nat.mod_lt _ hK_pos)
              (by omega) h2).2.2.2; omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · obtain ⟨rfl, hr_eq, rfl, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega)
                  (Nat.mod_lt _ hK_pos) hc0 (by omega) h2
              have hr0_eq : r0 = rPrev := by
                have := congrArg (fun a => (a + K - 1) % K) hr_eq
                rw [show (r0 + 1) % K + K - 1 = (r0 + 1) % K + (K - 1) by omega,
                    Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
                    show r0 + 1 + (K - 1) = r0 + K by omega, Nat.add_mod_right,
                    Nat.mod_eq_of_lt hr0] at this
                exact this.symm
              subst hr0_eq; exact Or.inr (Or.inl rfl)
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · obtain ⟨rfl, rfl, rfl, _⟩ :=
              torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2
              exact absurd hport hno
          · rw [hmem_cross] at hcr
            obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩ := hcr
            · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
              have := (torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2).2.2.2;
                  omega
            · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
              obtain ⟨rfl, hr_eq, _, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2
              have hv_eq : u0 = v := by
                rw [← hidx_r] at hr_eq
                exact hidx_inj u u0 v ((hmem_nbrs u u0).mpr ⟨hu0,
                  hadj0.symm⟩) hv_mem hr_eq.symm
              subst hv_eq; exact Or.inr (Or.inr rfl)
        · rintro (rfl | rfl | rfl)
          · refine ⟨fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega,
              Or.inl (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
                Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))⟩
          · refine ⟨fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hrPrev hc (by omega) h).2.2.2; omega,
              Or.inr (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, rPrev, hrPrev, c, hc,
                Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [hrPrev_next]⟩)))⟩))⟩
          · refine ⟨fun h =>
            huv_ne (torusVid_injective hK_pos hr hc (by omega) hj_lt hj_lt (by omega) h).1, ?_⟩
            rcases Nat.lt_or_gt_of_ne huv_ne with hlt | hgt
            · exact Or.inl (List.mem_append_right _ ((hmem_cross _ _).mpr
                ⟨u, hu, v, hv_lt, hlt, huv_adj, Or.inr ⟨by rw [hidx_r, hport.1], rfl⟩⟩))
            · exact Or.inr (List.mem_append_right _ ((hmem_cross _ _).mpr
                ⟨v, hv_lt, u, hu, hgt, huv_adj.symm, Or.inr ⟨rfl, by rw [hidx_r, hport.1]⟩⟩))
      · refine hdeg_three (torusVid K u r c 3) (torusVid K u rPrev c 3) (torusVid K u r c 0)
          (torusVid_lt hu hr hc (by omega)) (torusVid_lt hu hrPrev hc (by omega))
          (torusVid_lt hu hr hc (by omega))
          (fun h =>
            hrPrev_ne (torusVid_injective hK_pos hr hc (by omega) hrPrev hc (by omega) h).2.1.symm)
          (fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega)
          (fun h => by have :=
            (torusVid_injective hK_pos hrPrev hc (by omega) hr hc (by omega) h).2.2.2; omega)
          (fun z hz => ?_)
        rw [hw1, Graph.toSimpleGraph_adj]
        constructor
        · rintro ⟨hne, hmem⟩
          simp only [G', List.mem_append] at hmem
          rcases hmem with (hint | hcr) | (hint | hcr)
          · rw [hmem_int] at hint
            obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
            rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨_, h1,
              rfl⟩
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · obtain ⟨rfl, rfl, rfl, _⟩ :=
              torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1
              exact Or.inl rfl
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2;
              omega
          · rw [hmem_cross] at hcr
            obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩ := hcr
            · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
              have := (torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1).2.2.2;
                  omega
            · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
              obtain ⟨rfl, hr_eq, hc_eq, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1
              exact absurd ⟨hr_eq.trans hc_eq.symm, hr_eq ▸ hidx_lt u v0 hu hv0 hadj0⟩ hport
          · rw [hmem_int] at hint
            obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
            rcases h with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨_, rfl,
              h2⟩
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 (Nat.mod_lt _ hK_pos)
              (by omega) h2).2.2.2; omega
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · obtain ⟨rfl, hr_eq, rfl, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega)
                  (Nat.mod_lt _ hK_pos) hc0 (by omega) h2
              have hr0_eq : r0 = rPrev := by
                have := congrArg (fun a => (a + K - 1) % K) hr_eq
                rw [show (r0 + 1) % K + K - 1 = (r0 + 1) % K + (K - 1) by omega,
                    Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
                    show r0 + 1 + (K - 1) = r0 + K by omega, Nat.add_mod_right,
                    Nat.mod_eq_of_lt hr0] at this
                exact this.symm
              subst hr0_eq; exact Or.inr (Or.inl rfl)
            · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2;
              omega
            · obtain ⟨rfl, rfl, rfl, _⟩ :=
              torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2
              exact Or.inr (Or.inr rfl)
          · rw [hmem_cross] at hcr
            obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩ := hcr
            · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
              have := (torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2).2.2.2;
                  omega
            · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
              obtain ⟨rfl, hr_eq, hc_eq, _⟩ :=
                torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2
              exact absurd ⟨hr_eq.trans hc_eq.symm, hr_eq ▸ hidx_lt u u0 hu hu0 hadj0.symm⟩ hport
        · rintro (rfl | rfl | rfl)
          · refine ⟨fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega,
              Or.inl (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
                Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))⟩
          · refine ⟨fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hrPrev hc (by omega) h).2.2.2; omega,
              Or.inr (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, rPrev, hrPrev, c, hc,
                Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [hrPrev_next]⟩)))⟩))⟩
          · refine ⟨fun h => by have :=
            (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega,
              Or.inr (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hport, rfl, rfl⟩))))⟩))⟩
    · -- t = 2 (vertex c_{r, c}): neighbors a_{r,c}, a_{r,(c+1)%K}, d_{r,c}
      have hw2 : w = torusVid K u r c 2 := ht2 ▸ hw_eq
      set cNext := (c + 1) % K
      have hcNext : cNext < K := Nat.mod_lt _ hK_pos
      have hcNext_ne : cNext ≠ c := by
        intro h; by_cases hlast : c + 1 = K
        · rw [show cNext = 0 by simp [cNext, hlast]] at h; omega
        · rw [show cNext = c + 1 from Nat.mod_eq_of_lt (by omega)] at h; omega
      refine hdeg_three (torusVid K u r c 0) (torusVid K u r cNext 0) (torusVid K u r c 3)
        (torusVid_lt hu hr hc (by omega)) (torusVid_lt hu hr hcNext (by omega))
        (torusVid_lt hu hr hc (by omega))
        (fun h =>
          hcNext_ne (torusVid_injective hK_pos hr hc (by omega) hr hcNext (by omega) h).2.2.1.symm)
        (fun h => by have :=
          (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega)
        (fun h => by have :=
          (torusVid_injective hK_pos hr hcNext (by omega) hr hc (by omega) h).2.2.2; omega)
        (fun z hz => ?_)
      rw [hw2, Graph.toSimpleGraph_adj]
      constructor
      · rintro ⟨hne, hmem⟩
        simp only [G', List.mem_append] at hmem
        rcases hmem with (hint | hcr) | (hint | hcr)
        · rw [hmem_int] at hint
          obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
          rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨_, h1,
            rfl⟩
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2; omega
          · obtain ⟨rfl, rfl, rfl, _⟩ :=
            torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1
            exact Or.inr (Or.inl rfl)
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2; omega
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2; omega
          · obtain ⟨rfl, rfl, rfl, _⟩ :=
            torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1
            exact Or.inr (Or.inr rfl)
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2; omega
        · rw [hmem_cross] at hcr
          obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩ := hcr
          · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
            have := (torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1).2.2.2; omega
          · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
            have := (torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1).2.2.2; omega
        · rw [hmem_int] at hint
          obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
          rcases h with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨_, rfl,
            h2⟩
          · obtain ⟨rfl, rfl, rfl, _⟩ :=
            torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2
            exact Or.inl rfl
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 (Nat.mod_lt _ hK_pos)
            (by omega) h2).2.2.2; omega
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2; omega
          · have := (torusVid_injective hK_pos hr hc (by omega)
            (Nat.mod_lt _ hK_pos) hc0 (by omega) h2).2.2.2; omega
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2; omega
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2; omega
        · rw [hmem_cross] at hcr
          obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩ := hcr
          · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
            have := (torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2).2.2.2; omega
          · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
            have := (torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2).2.2.2; omega
      · rintro (rfl | rfl | rfl)
        · refine ⟨fun h => by have :=
          (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega,
            Or.inr (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
              Or.inl ⟨rfl, rfl⟩⟩))⟩
        · refine ⟨fun h => by have :=
          (torusVid_injective hK_pos hr hc (by omega) hr hcNext (by omega) h).2.2.2; omega,
            Or.inl (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
              Or.inr (Or.inl ⟨rfl, rfl⟩)⟩))⟩
        · refine ⟨fun h => by have :=
          (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega,
            Or.inl (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩))⟩
    · -- t = 3 (vertex d_{r, c}): neighbors b_{r,c}, b_{(r+1)%K, c}, c_{r,c}
      have hw3 : w = torusVid K u r c 3 := ht3 ▸ hw_eq
      set rNext := (r + 1) % K
      have hrNext : rNext < K := Nat.mod_lt _ hK_pos
      have hrNext_ne : rNext ≠ r := by
        intro h; by_cases hlast : r + 1 = K
        · rw [show rNext = 0 by simp [rNext, hlast]] at h; omega
        · rw [show rNext = r + 1 from Nat.mod_eq_of_lt (by omega)] at h; omega
      refine hdeg_three (torusVid K u r c 1) (torusVid K u rNext c 1) (torusVid K u r c 2)
        (torusVid_lt hu hr hc (by omega)) (torusVid_lt hu hrNext hc (by omega))
        (torusVid_lt hu hr hc (by omega))
        (fun h =>
          hrNext_ne (torusVid_injective hK_pos hr hc (by omega) hrNext hc (by omega) h).2.1.symm)
        (fun h => by have :=
          (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega)
        (fun h => by have :=
          (torusVid_injective hK_pos hrNext hc (by omega) hr hc (by omega) h).2.2.2; omega)
        (fun z hz => ?_)
      rw [hw3, Graph.toSimpleGraph_adj]
      constructor
      · rintro ⟨hne, hmem⟩
        simp only [G', List.mem_append] at hmem
        rcases hmem with (hint | hcr) | (hint | hcr)
        · rw [hmem_int] at hint
          obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
          rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨_, h1,
            rfl⟩
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2; omega
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2; omega
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2; omega
          · obtain ⟨rfl, rfl, rfl, _⟩ :=
            torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1
            exact Or.inr (Or.inl rfl)
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2; omega
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h1).2.2.2; omega
        · rw [hmem_cross] at hcr
          obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩ := hcr
          · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
            have := (torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1).2.2.2; omega
          · have hi0 := (hidx_lt u0 v0 hu0 hv0 hadj0).trans (hnbrs_len u0 hu0)
            have := (torusVid_injective hK_pos hr hc (by omega) hi0 hi0 (by omega) h1).2.2.2; omega
        · rw [hmem_int] at hint
          obtain ⟨u0, hu0, r0, hr0, c0, hc0, h⟩ := hint
          rcases h with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨_, rfl,
            h2⟩
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2; omega
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 (Nat.mod_lt _ hK_pos)
            (by omega) h2).2.2.2; omega
          · obtain ⟨rfl, rfl, rfl, _⟩ :=
            torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2
            exact Or.inl rfl
          · have := (torusVid_injective hK_pos hr hc (by omega)
            (Nat.mod_lt _ hK_pos) hc0 (by omega) h2).2.2.2; omega
          · obtain ⟨rfl, rfl, rfl, _⟩ :=
            torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2
            exact Or.inr (Or.inr rfl)
          · have := (torusVid_injective hK_pos hr hc (by omega) hr0 hc0 (by omega) h2).2.2.2; omega
        · rw [hmem_cross] at hcr
          obtain ⟨u0, hu0, v0, hv0, huv0, hadj0, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩ := hcr
          · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
            have := (torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2).2.2.2; omega
          · have hj0 := (hidx_lt v0 u0 hv0 hu0 hadj0.symm).trans (hnbrs_len v0 hv0)
            have := (torusVid_injective hK_pos hr hc (by omega) hj0 hj0 (by omega) h2).2.2.2; omega
      · rintro (rfl | rfl | rfl)
        · refine ⟨fun h => by have :=
          (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega,
            Or.inr (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
              Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))⟩
        · refine ⟨fun h => by have :=
          (torusVid_injective hK_pos hr hc (by omega) hrNext hc (by omega) h).2.2.2; omega,
            Or.inl (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
              Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩))⟩
        · refine ⟨fun h => by have :=
          (torusVid_injective hK_pos hr hc (by omega) hr hc (by omega) h).2.2.2; omega,
            Or.inr (List.mem_append_left _ ((hmem_int _ _).mpr ⟨u, hu, r, hr, c, hc,
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩))⟩
  exact ⟨hG'_wf.1, hG'_wf.2, hG'_3reg⟩

/-- Forward soundness of `torusReductionGraph`: a bisection of `x` lifts to a bisection of
`⟨torusReductionGraph x.graph, 2 * x.bound⟩`. -/
theorem torusReductionGraph_forward (x : MinBisectionInstance) (hG_mem : x ∈ MinBisection) :
    ⟨torusReductionGraph x.graph, 2 * x.bound⟩ ∈ ThreeMinBisection := by
  classical
  set V := x.graph.distinctVertices
  set n := V.length
  set K := 4 * n * n + 8
  have hK_ge : 8 ≤ K := by omega
  have hK_pos : 0 < K := by omega
  let nbrs := fun u =>
    (List.range n).filter fun v => x.graph.adjBool (V.getD u 0) (V.getD v 0)
  let internalEdges := (List.range n).flatMap fun u => torusGadgetEdges K u (nbrs u).length
  let crossEdges := (List.range n).flatMap fun u =>
    ((List.range n).filter fun v =>
      decide (u < v) && x.graph.adjBool (V.getD u 0) (V.getD v 0)).flatMap fun v =>
        let i := (nbrs u).idxOf v
        let j := (nbrs v).idxOf u
        [(torusVid K u i i 0, torusVid K v j j 0),
         (torusVid K u i i 1, torusVid K v j j 1)]
  set G' : Graph := ⟨List.range (4 * K * K * n), internalEdges ++ crossEdges⟩
  have hV_nd : V.Nodup := Graph.nodup_distinctVertices x.graph
  have hV_inj : ∀ {i j}, i < n → j < n → V.getD i 0 = V.getD j 0 → i = j :=
    fun {i j} hi hj h => by
      have h1 : V[i] = V[j] := by
        rw [List.getD_eq_getElem _ 0 hi, List.getD_eq_getElem _ 0 hj] at h; exact h
      exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hV_nd)
        (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h1)
  have hnbrs_len : ∀ u < n, (nbrs u).length < K := fun u _ => by
    have h1 : (nbrs u).length ≤ (List.range n).length := List.length_filter_le _ _
    rw [List.length_range] at h1; dsimp only [K]; nlinarith
  have hnbrs_nd : ∀ u, (nbrs u).Nodup := fun u => List.nodup_range.filter _
  have hmem_nbrs : ∀ u v, v ∈ nbrs u ↔
    v < n ∧ x.graph.toSimpleGraph.Adj (V.getD u 0) (V.getD v 0) :=
    fun u v => by simp [nbrs, Graph.adjBool_eq_true_iff]
  have hidx_lt : ∀ u v, u < n → v < n → x.graph.toSimpleGraph.Adj (V.getD u 0) (V.getD v 0) →
      (nbrs u).idxOf v < (nbrs u).length := fun u v _ hv hadj =>
    List.idxOf_lt_length_of_mem ((hmem_nbrs u v).mpr ⟨hv, hadj⟩)
  have hidx_inj : ∀ u v1 v2, v1 ∈ nbrs u → v2 ∈ nbrs u →
      (nbrs u).idxOf v1 = (nbrs u).idxOf v2 → v1 = v2 := fun u v1 v2 h1 _ heq =>
    (List.idxOf_inj h1).mp heq
  have hG'_verts : G'.vertices = List.range (4 * K * K * n) := rfl
  have hG'_eq : torusReductionGraph x.graph = G' := rfl
  rw [hG'_eq]
  have ⟨hG'_wf1, hG'_wf2, hG'_3reg⟩ := torusReductionGraph_wf_and_3reg x
  have hG'_wf : G'.vertices.Nodup ∧ (∀ e ∈ G'.edges, e.1 ∈ G'.vertices ∧ e.2 ∈ G'.vertices) :=
    ⟨hG'_wf1, hG'_wf2⟩
  refine ⟨hG'_wf.1, hG'_wf.2, hG'_3reg, ?_⟩
  obtain ⟨T, hTsub, hTcard, hTcut⟩ := (mem_MinBisection_iff x).mp hG_mem
  let Tidx : Finset ℕ := (Finset.range n).filter fun u => V.getD u 0 ∈ T
  have hTidx_card : Tidx.card = T.card := by
    have hbij : Tidx.image (fun u => V.getD u 0) = T := by
      ext v; simp only [Tidx, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      refine ⟨fun ⟨_, ⟨_, h⟩, heq⟩ => heq ▸ h, fun hv => ?_⟩
      obtain ⟨u, hu, rfl⟩ :=
        List.mem_iff_getElem.mp (Graph.mem_distinctVertices.mpr (hTsub v hv))
      exact ⟨u, ⟨hu, by rw [List.getD_eq_getElem _ 0 hu]; exact hv⟩,
        List.getD_eq_getElem _ 0 hu⟩
    rw [← hbij, Finset.card_image_of_injOn fun u1 hu1 u2 hu2 h =>
      hV_inj (Finset.mem_range.mp (Finset.mem_filter.mp hu1).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hu2).1) h]
  let S' : Finset ℕ := Tidx.biUnion fun u =>
    (Finset.range (4 * K * K)).image fun m => u * (4 * K * K) + m
  have hS'_sub : ∀ w ∈ S', w ∈ G'.vertices := by
    intro w hw
    obtain ⟨u, hu, m, hm, rfl⟩ := by
      simpa only [S', Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] using hw
    have hu' : u < n := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    rw [hG'_verts, List.mem_range]
    have := Nat.mul_le_mul_right (4 * K * K) (Nat.succ_le_of_lt hu'); nlinarith
  have hS'_card : 2 * S'.card = G'.distinctVertices.length := by
    have hG'_len : G'.distinctVertices.length = 4 * K * K * n := by
      rw [Graph.length_distinctVertices, List.toFinset_card_of_nodup hG'_wf.1, hG'_verts,
        List.length_range]
    have hdisj : Set.PairwiseDisjoint (↑Tidx) fun u =>
        (Finset.range (4 * K * K)).image fun m => u * (4 * K * K) + m := by
      intro u1 _ u2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]; intro w hw1 hw2
      obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hw1
      obtain ⟨m2, hm2, heq⟩ := Finset.mem_image.mp hw2
      rw [Finset.mem_range] at hm1 hm2
      have hpos : 0 < 4 * K * K := by nlinarith
      have hq := congrArg (· / (4 * K * K)) heq
      rw [Nat.mul_comm u1 _, Nat.mul_comm u2 _, Nat.mul_add_div hpos, Nat.mul_add_div hpos,
        Nat.div_eq_of_lt hm1, Nat.div_eq_of_lt hm2] at hq
      exact hne (by omega)
    rw [Finset.card_biUnion hdisj]
    have hper : ∀ u ∈ Tidx, ((Finset.range (4 * K * K)).image fun m => u * (4 * K * K) +
      m).card = 4 * K * K := fun u _ => by
      rw [Finset.card_image_of_injective _ (add_right_injective _), Finset.card_range]
    rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul, hG'_len, hTidx_card]
    have hTn : 2 * T.card = n := by dsimp only [n, V]; exact hTcard
    rw [← hTn]; ring
  have hS'_mem_iff : ∀ u < n, ∀ r < K, ∀ c < K, ∀ t < 4,
      torusVid K u r c t ∈ S' ↔ u ∈ Tidx := by
    intro u hu r hr c hc t ht
    simp only [S', Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨u', hu', m, hm, heq⟩
      have h1 : torusVid K u r c t = u * (4 * K * K) + ((r * K + c) * 4 + t) := by
        unfold torusVid; ring
      have hm1 : (r * K + c) * 4 + t < 4 * K * K := by
        have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hr); nlinarith
      rw [h1] at heq
      have hpos : 0 < 4 * K * K := by nlinarith
      have hq := congrArg (· / (4 * K * K)) heq
      rw [Nat.mul_comm u' _, Nat.mul_comm u _, Nat.mul_add_div hpos, Nat.mul_add_div hpos,
        Nat.div_eq_of_lt hm, Nat.div_eq_of_lt hm1] at hq
      exact (show u' = u by omega) ▸ hu'
    · intro huT
      refine ⟨u, huT, (r * K + c) * 4 + t, ?_, ?_⟩
      · have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hr); nlinarith
      · unfold torusVid; ring
  -- No internal edge crosses `S'`, and each edge `{u, v}` crossing `T` contributes 2
  -- cross-edges!
  have hS'_cut : (G'.induced.interedges (S'.subtype (· ∈ G'.vertices))
      (S'.subtype (· ∈ G'.vertices))ᶜ).card ≤ 2 * x.bound := by
    -- Build the exact list of `2 * cut_G(T)` crossing pairs in `G'`!
    let pairs := (List.range n).flatMap fun u =>
      ((List.range n).filter fun v =>
        decide (u ∈ Tidx) && decide (v ∉ Tidx) && x.graph.adjBool (V.getD u 0)
          (V.getD v 0)).flatMap fun v =>
          let i := (nbrs u).idxOf v
          let j := (nbrs v).idxOf u
          [(torusVid K u i i 0, torusVid K v j j 0),
           (torusVid K u i i 1, torusVid K v j j 1)]
    have hsub_p : ∀ p : ℕ × ℕ,
        p.1 ∈ G'.vertices ∧ p.2 ∈ G'.vertices ∧ G'.toSimpleGraph.Adj p.1 p.2 ∧ p.1 ∈ S' ∧
          p.2 ∉ S' →
        p ∈ pairs := by
      rintro ⟨w1, w2⟩ ⟨hw1, hw2, hadj, hw1S, hw2S⟩
      rw [Graph.toSimpleGraph_adj] at hadj
      obtain ⟨hne, hmem⟩ := hadj
      have hno_int : ∀ a b, (a, b) ∈ internalEdges → (a ∈ S' ↔ b ∈ S') := by
        intro a b hab
        obtain ⟨u, hu, heu⟩ := List.mem_flatMap.mp hab
        rw [List.mem_range] at hu
        obtain ⟨r, hr, her⟩ := List.mem_flatMap.mp heu
        obtain ⟨c, hc, h⟩ := List.mem_flatMap.mp her
        rw [List.mem_range] at hr hc
        unfold torusCellEdges at h
        split_ifs at h
        · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp only [hS'_mem_iff u hu r hr c hc 0 (by omega),
              hS'_mem_iff u hu r hr c hc 1 (by omega),
              hS'_mem_iff u hu r hr c hc 2 (by omega),
              hS'_mem_iff u hu r hr c hc 3 (by omega),
              hS'_mem_iff u hu r hr ((c + 1) % K) (Nat.mod_lt _ hK_pos) 0 (by omega),
              hS'_mem_iff u hu ((r + 1) % K) (Nat.mod_lt _ hK_pos) c hc 1 (by omega), iff_self]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
              ⟨rfl, rfl⟩ <;>
            simp only [hS'_mem_iff u hu r hr c hc 0 (by omega),
              hS'_mem_iff u hu r hr c hc 1 (by omega),
              hS'_mem_iff u hu r hr c hc 2 (by omega),
              hS'_mem_iff u hu r hr c hc 3 (by omega),
              hS'_mem_iff u hu r hr ((c + 1) % K) (Nat.mod_lt _ hK_pos) 0 (by omega),
              hS'_mem_iff u hu ((r + 1) % K) (Nat.mod_lt _ hK_pos) c hc 1 (by omega), iff_self]
      have hcross_mem : (w1, w2) ∈ crossEdges ∨ (w2, w1) ∈ crossEdges := by
        simp only [G', List.mem_append] at hmem
        rcases hmem with (hi | hc) | (hi | hc)
        · exact absurd ((hno_int w1 w2 hi).mp hw1S) hw2S
        · exact Or.inl hc
        · exact absurd ((hno_int w2 w1 hi).mpr hw1S) hw2S
        · exact Or.inr hc
      simp only [pairs, List.mem_flatMap, List.mem_filter, List.mem_range,
        Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff,
        List.mem_cons, List.not_mem_nil, or_false]
      rcases hcross_mem with hc | hc
      · obtain ⟨u, hu, hu_m⟩ := List.mem_flatMap.mp hc
        rw [List.mem_range] at hu
        obtain ⟨v, hv, hv_m⟩ := List.mem_flatMap.mp hu_m
        simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
          Graph.adjBool_eq_true_iff, List.mem_cons, List.not_mem_nil, or_false,
            Prod.mk.injEq] at hv hv_m
        have hi := (hidx_lt u v hu hv.1 hv.2.2).trans (hnbrs_len u hu)
        have hj := (hidx_lt v u hv.1 hu hv.2.2.symm).trans (hnbrs_len v hv.1)
        rcases hv_m with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨u, hu, v, ⟨hv.1, ⟨(hS'_mem_iff u hu _ hi _ hi 0 (by omega)).mp hw1S,
            fun h => hw2S ((hS'_mem_iff v hv.1 _ hj _ hj 0 (by omega)).mpr h)⟩, hv.2.2⟩,
              Or.inl rfl⟩
        · exact ⟨u, hu, v, ⟨hv.1, ⟨(hS'_mem_iff u hu _ hi _ hi 1 (by omega)).mp hw1S,
            fun h => hw2S ((hS'_mem_iff v hv.1 _ hj _ hj 1 (by omega)).mpr h)⟩, hv.2.2⟩,
              Or.inr rfl⟩
      · obtain ⟨u, hu, hu_m⟩ := List.mem_flatMap.mp hc
        rw [List.mem_range] at hu
        obtain ⟨v, hv, hv_m⟩ := List.mem_flatMap.mp hu_m
        simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
          Graph.adjBool_eq_true_iff, List.mem_cons, List.not_mem_nil, or_false,
            Prod.mk.injEq] at hv hv_m
        have hi := (hidx_lt u v hu hv.1 hv.2.2).trans (hnbrs_len u hu)
        have hj := (hidx_lt v u hv.1 hu hv.2.2.symm).trans (hnbrs_len v hv.1)
        rcases hv_m with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨v, hv.1, u, ⟨hu, ⟨(hS'_mem_iff v hv.1 _ hj _ hj 0 (by omega)).mp hw1S,
            fun h => hw2S ((hS'_mem_iff u hu _ hi _ hi 0 (by omega)).mpr h)⟩, hv.2.2.symm⟩,
              Or.inl rfl⟩
        · exact ⟨v, hv.1, u, ⟨hu, ⟨(hS'_mem_iff v hv.1 _ hj _ hj 1 (by omega)).mp hw1S,
            fun h => hw2S ((hS'_mem_iff u hu _ hi _ hi 1 (by omega)).mpr h)⟩, hv.2.2.symm⟩,
              Or.inr rfl⟩
    have hcard_le : (G'.induced.interedges (S'.subtype (· ∈ G'.vertices))
        (S'.subtype (· ∈ G'.vertices))ᶜ).card ≤ pairs.length := by
      rw [← Finset.card_map ((Function.Embedding.subtype (· ∈ G'.vertices)).prodMap
        (Function.Embedding.subtype (· ∈ G'.vertices)))]
      refine (Finset.card_le_card fun p hp => ?_).trans (List.toFinset_card_le pairs)
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_map.mp hp
      rw [SimpleGraph.mem_interedges_iff, Finset.mem_compl, Finset.mem_subtype,
        Finset.mem_subtype, Graph.induced_adj] at hab
      exact List.mem_toFinset.mpr (hsub_p (a.1, b.1) ⟨a.2, b.2, hab.2.2, hab.1, hab.2.1⟩)
    have hpairs_len : pairs.length = 2 * (x.graph.induced.interedges
        (T.subtype (· ∈ x.graph.vertices)) (T.subtype (· ∈ x.graph.vertices))ᶜ).card := by
      -- Count pairs = 2 * (# ordered crossing pairs (u, v) in G)
      let gPairs := (List.range n).flatMap fun u =>
        ((List.range n).filter fun v =>
          decide (u ∈ Tidx) && decide (v ∉ Tidx) && x.graph.adjBool (V.getD u 0)
            (V.getD v 0)).map fun v => (u, v)
      have hlen2 : pairs.length = 2 * gPairs.length := by
        simp only [pairs, gPairs, List.length_flatMap, List.length_map]
        have h1 : ∀ u, (((List.range n).filter fun v =>
              decide (u ∈ Tidx) && decide (v ∉ Tidx) && x.graph.adjBool (V.getD u 0)
                (V.getD v 0)).map fun _ => 2).sum =
            2 * ((List.range n).filter fun v =>
              decide (u ∈ Tidx) && decide (v ∉ Tidx) && x.graph.adjBool (V.getD u 0)
                (V.getD v 0)).length := fun u => by
          have hsum_c : ∀ (l : List ℕ), (l.map fun _ => 2).sum = 2 * l.length := by
            intro l; induction l with
            | nil => simp
            | cons _ t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
          exact hsum_c _
        have h2 : (List.range n).map (fun u =>
            (((List.range n).filter fun v =>
              decide (u ∈ Tidx) && decide (v ∉ Tidx) && x.graph.adjBool (V.getD u 0)
                (V.getD v 0)).map fun _ => 2).sum) =
            (List.range n).map (fun u =>
              2 * ((List.range n).filter fun v =>
                decide (u ∈ Tidx) && decide (v ∉ Tidx) && x.graph.adjBool (V.getD u 0)
                  (V.getD v 0)).length) :=
          List.map_congr_left fun u _ => h1 u
        simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
        rw [h2]
        clear h1 h2
        have hmul_sum : ∀ (l : List ℕ) (f : ℕ → ℕ), (l.map fun a => 2 * f a).sum =
            2 * (l.map f).sum := by
          intro l f; induction l with
          | nil => simp
          | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]
        exact hmul_sum (List.range n) _
      rw [hlen2]
      congr 1
      -- `gPairs.length = (x.graph.induced.interedges T Tᶜ).card`
      have hgnd : (gPairs.map fun e => (V.getD e.1 0, V.getD e.2 0)).Nodup := by
        have hnd0 : gPairs.Nodup := by
          rw [List.nodup_flatMap]
          refine ⟨fun u _ => (List.nodup_range.filter _).map fun _ _ h => (Prod.mk.inj h).2,
            List.nodup_range.pairwise_of_forall_ne fun u1 _ u2 _ hne p hp1 hp2 => ?_⟩
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp1
          obtain ⟨_, _, h2⟩ := List.mem_map.mp hp2
          exact hne (Prod.mk.inj h2).1.symm
        refine hnd0.map_on fun e1 he1 e2 he2 h => ?_
        simp only [gPairs, List.mem_flatMap, List.mem_map, List.mem_filter,
          List.mem_range] at he1 he2
        obtain ⟨u1, hu1, v1, ⟨hv1, _⟩, rfl⟩ := he1
        obtain ⟨u2, hu2, v2, ⟨hv2, _⟩, rfl⟩ := he2
        exact Prod.ext (hV_inj hu1 hu2 (Prod.mk.inj h).1) (hV_inj hv1 hv2 (Prod.mk.inj h).2)
      have hT_iff : ∀ u < n, u ∈ Tidx ↔ V.getD u 0 ∈ T := fun u hu => by simp [Tidx, hu]
      rw [← List.length_map (fun e => (V.getD e.1 0, V.getD e.2 0))]
      refine (SimpleMaxCut.card_interedges_eq_length x.graph T hgnd fun ⟨a, b⟩ => ?_).symm
      simp only [List.mem_map, gPairs, List.mem_flatMap, List.mem_filter, List.mem_range,
        Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff]
      constructor
      · rintro ⟨⟨u, v⟩, ⟨u', hu', v', ⟨hv', ⟨huT, hvT⟩, hadj⟩, heq⟩, hmap⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmap
        exact ⟨Graph.mem_distinctVertices.mp (getD_mem_of_lt hu'),
          Graph.mem_distinctVertices.mp (getD_mem_of_lt hv'), hadj,
          (hT_iff u' hu').mp huT, fun h => hvT ((hT_iff v' hv').mpr h)⟩
      · rintro ⟨ha, hb, hadj, haT, hbT⟩
        obtain ⟨u, hu, rfl⟩ := List.mem_iff_getElem.mp (Graph.mem_distinctVertices.mpr ha)
        obtain ⟨v, hv, rfl⟩ := List.mem_iff_getElem.mp (Graph.mem_distinctVertices.mpr hb)
        have hgu : V.getD u 0 = V[u] := List.getD_eq_getElem _ 0 hu
        have hgv : V.getD v 0 = V[v] := List.getD_eq_getElem _ 0 hv
        rw [← hgu] at hadj haT; rw [← hgv] at hadj hbT
        exact ⟨(u, v), ⟨u, hu, v, ⟨hv, ⟨(hT_iff u hu).mpr haT,
          fun h => hbT ((hT_iff v hv).mp h)⟩, hadj⟩, rfl⟩,
          by rw [hgu, hgv]⟩
    omega
  rw [mem_MinBisection_iff]
  exact ⟨S', hS'_sub, hS'_card, hS'_cut⟩

end CslibFrontier.Complexity.MinBisection
