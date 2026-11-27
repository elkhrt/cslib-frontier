/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import CslibFrontier.Computability.Complexity.Problems.ThreeMinBisectionGadget
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.List.GetD

/-!
# NP-Completeness of Cubic Minimum Bisection (`ThreeMinBisection`)

Completes the reduction `toThreeMinBisection` from `MinBisection` to `ThreeMinBisection` by
proving backward soundness (any bisection of the cubic torus-gadget graph of width `≤ 2k` induces
a bisection of the original graph of width `≤ k`) and concluding `ThreeMinBisection_npComplete`.

## Main results

* `CslibFrontier.Complexity.MinBisection.torusReductionGraph_backward`: backward soundness.
* `CslibFrontier.Complexity.MinBisection.toThreeMinBisection_mem_iff`: reduction correctness.
* `CslibFrontier.Complexity.ThreeMinBisection_npComplete`: `NPComplete encMinBisection
  ThreeMinBisection`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

namespace MinBisection

private theorem getD_mem_of_lt {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

private theorem ne_succ_mod {a K : ℕ} (hK : 2 ≤ K) (ha : a < K)
    (h : a = (a + 1) % K) : False := by
  by_cases ha1 : a + 1 < K
  · rw [Nat.mod_eq_of_lt ha1] at h; omega
  · have : a + 1 = K := by omega
    rw [this, Nat.mod_self] at h; omega

private theorem torusVid_div (K u r c t : ℕ)
    (hr : r < K) (hc : c < K) (ht : t < 4) :
    torusVid K u r c t / (4 * K * K) = u := by
  have hm : (r * K + c) * 4 + t < 4 * K * K := by
    have : r * K + c < K * K := by
      have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hr); nlinarith
    nlinarith
  have heq : torusVid K u r c t = (4 * K * K) * u + ((r * K + c) * 4 + t) := by
    dsimp only [torusVid]; ring
  rw [heq, Nat.mul_add_div (by nlinarith), Nat.div_eq_of_lt hm, add_zero]

private def torusIntList (K : ℕ) (isInA : ℕ → ℕ → Bool) (u : ℕ) : List (ℕ × ℕ) :=
  ((List.range K).flatMap fun r =>
    ((List.range K).filter fun c =>
      isInA u (torusVid K u r c 0) != isInA u (torusVid K u r c 2)).map
      (fun c => (torusVid K u r c 0, torusVid K u r c 2)) ++
    ((List.range K).filter fun c =>
      isInA u (torusVid K u r c 2) != isInA u (torusVid K u r ((c + 1) % K) 0)).map
      (fun c => (torusVid K u r c 2, torusVid K u r ((c + 1) % K) 0))) ++
  ((List.range K).flatMap fun c =>
    ((List.range K).filter fun r =>
      isInA u (torusVid K u r c 1) != isInA u (torusVid K u r c 3)).map
      (fun r => (torusVid K u r c 1, torusVid K u r c 3)) ++
    ((List.range K).filter fun r =>
      isInA u (torusVid K u r c 3) != isInA u (torusVid K u ((r + 1) % K) c 1)).map
      (fun r => (torusVid K u r c 3, torusVid K u ((r + 1) % K) c 1))) ++
  (((List.range K).flatMap fun r => (List.range K).map fun c => (r, c)).filter fun p =>
    isInA u (torusVid K u p.1 p.2 2) != isInA u (torusVid K u p.1 p.2 3)).map
    (fun p => (torusVid K u p.1 p.2 2, torusVid K u p.1 p.2 3))

private theorem torusIntList_div_eq (K : ℕ) (hK_pos : 0 < K) (isInA : ℕ → ℕ → Bool)
    (u : ℕ) (p : ℕ × ℕ) (hp : p ∈ torusIntList K isInA u) :
    p.1 / (4 * K * K) = u ∧ p.2 / (4 * K * K) = u := by
  simp only [torusIntList, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_range] at hp
  rcases hp with ((⟨r, hr, ⟨c, ⟨hc, _⟩, rfl⟩ | ⟨c, ⟨hc, _⟩, rfl⟩⟩) |
      ⟨c, hc, ⟨r, ⟨hr, _⟩, rfl⟩ | ⟨r, ⟨hr, _⟩, rfl⟩⟩) |
      ⟨⟨r, c⟩, ⟨⟨r', hr, c', hc, heq⟩, _⟩, rfl⟩
  · exact ⟨torusVid_div K u r c 0 hr hc (by omega),
      torusVid_div K u r c 2 hr hc (by omega)⟩
  · exact ⟨torusVid_div K u r c 2 hr hc (by omega),
      torusVid_div K u r ((c + 1) % K) 0 hr (Nat.mod_lt _ hK_pos) (by omega)⟩
  · exact ⟨torusVid_div K u r c 1 hr hc (by omega),
      torusVid_div K u r c 3 hr hc (by omega)⟩
  · exact ⟨torusVid_div K u r c 3 hr hc (by omega),
      torusVid_div K u ((r + 1) % K) c 1 (Nat.mod_lt _ hK_pos) hc (by omega)⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨torusVid_div K u r' c' 2 hr hc (by omega),
      torusVid_div K u r' c' 3 hr hc (by omega)⟩

private theorem torusIntList_nodup (K : ℕ) (hK_pos : 0 < K) (n : ℕ) (isInA : ℕ → ℕ → Bool) :
    ((List.range n).flatMap (torusIntList K isInA)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · have hnd_row : ((List.range K).flatMap fun r =>
        ((List.range K).filter fun c =>
          isInA u (torusVid K u r c 0) != isInA u (torusVid K u r c 2)).map
          (fun c => (torusVid K u r c 0, torusVid K u r c 2)) ++
        ((List.range K).filter fun c =>
          isInA u (torusVid K u r c 2) != isInA u (torusVid K u r ((c + 1) % K) 0)).map
          (fun c => (torusVid K u r c 2, torusVid K u r ((c + 1) % K) 0))).Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun r hr => ?_, ?_⟩
      · rw [List.mem_range] at hr
        rw [List.nodup_append]
        refine ⟨(List.nodup_range.filter _).map_on fun c1 hc1 c2 hc2 h =>
            (torusVid_injective hK_pos hr (List.mem_range.mp (List.mem_filter.mp hc1).1)
              (by omega)
              hr (List.mem_range.mp (List.mem_filter.mp hc2).1) (by omega)
                (Prod.mk.inj h).1).2.2.1,
          (List.nodup_range.filter _).map_on fun c1 hc1 c2 hc2 h =>
            (torusVid_injective hK_pos hr (List.mem_range.mp (List.mem_filter.mp hc1).1)
              (by omega)
              hr (List.mem_range.mp (List.mem_filter.mp hc2).1) (by omega)
                (Prod.mk.inj h).1).2.2.1,
          fun p hp q hq heq => by
            subst heq
            obtain ⟨c1, hc1, rfl⟩ := List.mem_map.mp hp
            obtain ⟨c2, hc2, h2⟩ := List.mem_map.mp hq
            have h1 := torusVid_injective hK_pos hr (List.mem_range.mp (List.mem_filter.mp
              hc2).1) (by omega)
              hr (List.mem_range.mp (List.mem_filter.mp hc1).1) (by omega)
                (Prod.mk.inj h2).1
            exact absurd h1.2.2.2 (by decide)⟩
      · refine List.nodup_range.pairwise_of_forall_ne fun r1 hr1 r2 hr2 hne => ?_
        intro p hp1 hp2
        rw [List.mem_range] at hr1 hr2
        simp only [List.mem_append, List.mem_map, List.mem_filter,
          List.mem_range] at hp1 hp2
        rcases hp1 with ⟨c1, ⟨hc1, _⟩, rfl⟩ | ⟨c1, ⟨hc1, _⟩, rfl⟩ <;>
          rcases hp2 with ⟨c2, ⟨hc2, _⟩, h2⟩ | ⟨c2, ⟨hc2, _⟩, h2⟩ <;>
          exact hne (torusVid_injective hK_pos hr2 hc2 (by omega) hr1 hc1 (by omega)
            (Prod.mk.inj h2).1).2.1.symm
    have hnd_col : ((List.range K).flatMap fun c =>
        ((List.range K).filter fun r =>
          isInA u (torusVid K u r c 1) != isInA u (torusVid K u r c 3)).map
          (fun r => (torusVid K u r c 1, torusVid K u r c 3)) ++
        ((List.range K).filter fun r =>
          isInA u (torusVid K u r c 3) != isInA u (torusVid K u ((r + 1) % K) c 1)).map
          (fun r => (torusVid K u r c 3, torusVid K u ((r + 1) % K) c 1))).Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun c hc => ?_, ?_⟩
      · rw [List.mem_range] at hc
        rw [List.nodup_append]
        refine ⟨(List.nodup_range.filter _).map_on fun r1 hr1 r2 hr2 h =>
            (torusVid_injective hK_pos (List.mem_range.mp (List.mem_filter.mp hr1).1) hc
              (by omega)
              (List.mem_range.mp (List.mem_filter.mp hr2).1) hc (by omega)
                (Prod.mk.inj h).1).2.1,
          (List.nodup_range.filter _).map_on fun r1 hr1 r2 hr2 h =>
            (torusVid_injective hK_pos (List.mem_range.mp (List.mem_filter.mp hr1).1) hc
              (by omega)
              (List.mem_range.mp (List.mem_filter.mp hr2).1) hc (by omega)
                (Prod.mk.inj h).1).2.1,
          fun p hp q hq heq => by
            subst heq
            obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hp
            obtain ⟨r2, hr2, h2⟩ := List.mem_map.mp hq
            have h1 := torusVid_injective hK_pos (List.mem_range.mp (List.mem_filter.mp
              hr2).1) hc (by omega)
              (List.mem_range.mp (List.mem_filter.mp hr1).1) hc (by omega)
                (Prod.mk.inj h2).1
            exact absurd h1.2.2.2 (by decide)⟩
      · refine List.nodup_range.pairwise_of_forall_ne fun c1 hc1 c2 hc2 hne => ?_
        intro p hp1 hp2
        rw [List.mem_range] at hc1 hc2
        simp only [List.mem_append, List.mem_map, List.mem_filter,
          List.mem_range] at hp1 hp2
        rcases hp1 with ⟨r1, ⟨hr1, _⟩, rfl⟩ | ⟨r1, ⟨hr1, _⟩, rfl⟩ <;>
          rcases hp2 with ⟨r2, ⟨hr2, _⟩, h2⟩ | ⟨r2, ⟨hr2, _⟩, h2⟩ <;>
          exact hne (torusVid_injective hK_pos hr2 hc2 (by omega) hr1 hc1 (by omega)
            (Prod.mk.inj h2).1).2.2.1.symm
    have hnd_cd : ((((List.range K).flatMap fun r => (List.range K).map fun c => (r, c)).filter
        fun p => isInA u (torusVid K u p.1 p.2 2) != isInA u (torusVid K u p.1 p.2 3)).map
        (fun p => (torusVid K u p.1 p.2 2, torusVid K u p.1 p.2 3))).Nodup := by
      refine (List.Nodup.filter _ (List.nodup_flatMap.mpr ⟨fun r _ =>
        List.nodup_range.map (fun _ _ h => (Prod.mk.inj h).2),
        List.nodup_range.pairwise_of_forall_ne fun r1 _ r2 _ hne p h1 h2 => by
          obtain ⟨_, _, h1⟩ := List.mem_map.mp h1
          obtain ⟨_, _, h2⟩ := List.mem_map.mp h2
          exact hne ((Prod.mk.inj h1).1.trans (Prod.mk.inj h2).1.symm)⟩)).map_on ?_
      intro p1 hp1 p2 hp2 h
      simp only [List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range] at hp1 hp2
      obtain ⟨⟨r1, hr1, c1, hc1, rfl⟩, _⟩ := hp1
      obtain ⟨⟨r2, hr2, c2, hc2, rfl⟩, _⟩ := hp2
      have hi := torusVid_injective hK_pos hr1 hc1 (by omega) hr2 hc2 (by omega) (Prod.mk.inj h).1
      exact Prod.ext hi.2.1 hi.2.2.1
    dsimp only [torusIntList]
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hnd_row, hnd_col, ?_⟩, hnd_cd, ?_⟩
    · intro p hp q hq heq; subst heq
      simp only [List.mem_flatMap, List.mem_append, List.mem_map, List.mem_filter,
        List.mem_range] at hp hq
      obtain ⟨r1, hr1, ⟨c1, ⟨hc1, _⟩, rfl⟩ | ⟨c1, ⟨hc1, _⟩, rfl⟩⟩ := hp <;>
        obtain ⟨c2, hc2, ⟨r2, ⟨hr2, _⟩, h2⟩ | ⟨r2, ⟨hr2, _⟩, h2⟩⟩ := hq <;>
        (have := (torusVid_injective hK_pos hr2 hc2 (by omega) hr1 hc1 (by omega)
          (Prod.mk.inj h2).1).2.2.2; omega)
    · intro p hp q hq heq; subst heq
      simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
        List.mem_range] at hp hq
      obtain ⟨⟨r2, c2⟩, ⟨⟨r2', hr2, c2', hc2, heq2⟩, _⟩, h2⟩ := hq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq2
      rcases hp with ⟨r1, hr1, ⟨c1, ⟨hc1, _⟩, rfl⟩ | ⟨c1, ⟨hc1, _⟩, rfl⟩⟩ |
          ⟨c1, hc1, ⟨r1, ⟨hr1, _⟩, rfl⟩ | ⟨r1, ⟨hr1, _⟩, rfl⟩⟩
      · have := (torusVid_injective hK_pos hr2 hc2 (by omega) hr1 hc1 (by omega)
          (Prod.mk.inj h2).1).2.2.2; omega
      · have := (torusVid_injective hK_pos hr2 hc2 (by omega) hr1 (Nat.mod_lt _ hK_pos)
          (by omega) (Prod.mk.inj h2).2).2.2.2; omega
      · have := (torusVid_injective hK_pos hr2 hc2 (by omega) hr1 hc1 (by omega)
          (Prod.mk.inj h2).1).2.2.2; omega
      · have := (torusVid_injective hK_pos hr2 hc2 (by omega) hr1 hc1 (by omega)
          (Prod.mk.inj h2).1).2.2.2; omega
  · refine List.nodup_range.pairwise_of_forall_ne fun u1 _ u2 _ hne p hp1 hp2 => ?_
    exact hne ((torusIntList_div_eq K hK_pos isInA u1 p hp1).1.symm.trans
      (torusIntList_div_eq K hK_pos isInA u2 p hp2).1)

private def torusPairDir (K n : ℕ) (e : ℕ × ℕ) : Prop :=
  (∃ u < n, ∃ r < K, ∃ c < K,
    (e = (torusVid K u r c 0, torusVid K u r c 2)) ∨
    (e = (torusVid K u r c 2, torusVid K u r ((c + 1) % K) 0)) ∨
    (e = (torusVid K u r c 1, torusVid K u r c 3)) ∨
    (e = (torusVid K u r c 3, torusVid K u ((r + 1) % K) c 1)) ∨
    (e = (torusVid K u r c 2, torusVid K u r c 3))) ∨
  (∃ u < n, ∃ v < n, u < v ∧ ∃ i < K, ∃ j < K,
    (e = (torusVid K u i i 0, torusVid K v j j 0)) ∨
    (e = (torusVid K u i i 1, torusVid K v j j 1)))

private theorem torus_pair_no_reverse {K n : ℕ} (hK_ge : 8 ≤ K) (hK_pos : 0 < K)
    {p q : ℕ × ℕ} (hp : torusPairDir K n p) (hq : torusPairDir K n q)
    (h1 : p.1 = q.2) (h2 : p.2 = q.1) : False := by
  rcases hp with ⟨u1, hu1, r1, hr1, c1, hc1, hp1⟩ | ⟨u1, hu1, v1, hv1, huv1,
    i1, hi1, j1, hj1, hp1⟩ <;>
    rcases hq with ⟨u2, hu2, r2, hr2, c2, hc2, hq1⟩ | ⟨u2, hu2, v2, hv2,
      huv2, i2, hi2, j2, hj2, hq1⟩
  · rcases hp1 with rfl | rfl | rfl | rfl | rfl <;> rcases hq1 with rfl | rfl | rfl | rfl
      | rfl
    all_goals
      dsimp only at h1 h2
      have ha :=
        torusVid_injective hK_pos hr1 hc1 (by omega)
        (by first | exact hr2 | exact Nat.mod_lt _ hK_pos)
        (by first | exact hc2 | exact Nat.mod_lt _ hK_pos) (by omega) h1
      have hb :=
        torusVid_injective hK_pos (by first | exact hr1 | exact Nat.mod_lt _ hK_pos)
        (by first | exact hc1 | exact Nat.mod_lt _ hK_pos) (by omega)
        hr2 hc2 (by omega) h2
      try omega
    · exact ne_succ_mod (by omega) hc2 (hb.2.2.1.symm.trans ha.2.2.1)
    · exact ne_succ_mod (by omega) hc1 (ha.2.2.1.trans hb.2.2.1.symm)
    · exact ne_succ_mod (by omega) hr2 (hb.2.1.symm.trans ha.2.1)
    · exact ne_succ_mod (by omega) hr1 (ha.2.1.trans hb.2.1.symm)
  · rcases hp1 with rfl | rfl | rfl | rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      (dsimp only at h1 h2;
       have ha :=
         torusVid_injective hK_pos hr1 hc1
           (by omega) hj2 hj2 (by omega) h1;
       have hb :=
         torusVid_injective hK_pos (by first | exact hr1 | exact Nat.mod_lt _ hK_pos)
         (by first | exact hc1 | exact Nat.mod_lt _ hK_pos)
           (by omega) hi2 hi2 (by omega) h2;
       omega)
  · rcases hp1 with rfl | rfl <;> rcases hq1 with rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only at h1 h2;
       have ha := torusVid_injective hK_pos hi1 hi1 (by omega)
         (by first | exact hr2 | exact Nat.mod_lt _ hK_pos)
         (by first | exact hc2 | exact Nat.mod_lt _ hK_pos) (by omega) h1;
       have hb := torusVid_injective hK_pos hj1 hj1 (by omega)
         hr2 hc2 (by omega) h2;
       omega)
  · rcases hp1 with rfl | rfl <;> rcases hq1 with rfl | rfl <;>
      (dsimp only at h1 h2;
       have ha := torusVid_injective hK_pos hi1 hi1 (by omega) hj2 hj2 (by omega) h1;
       have hb := torusVid_injective hK_pos hj1 hj1 (by omega) hi2 hi2 (by omega) h2;
       omega)

/-- Backward soundness of `torusReductionGraph`: any bisection of width `≤ 2 * x.bound` on
`torusReductionGraph x.graph` induces a bisection of `x.graph` of width `≤ x.bound`. -/
theorem torusReductionGraph_backward (x : MinBisectionInstance)
    (hbig : ¬ (x.graph.distinctVertices.length * x.graph.distinctVertices.length ≤ x.bound))
    (hmem : ⟨torusReductionGraph x.graph, 2 * x.bound⟩ ∈ ThreeMinBisection) :
    x ∈ MinBisection := by
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
  rw [hG'_eq] at hmem
  have ⟨hG'_wf1, hG'_wf2, hG'_3reg⟩ := torusReductionGraph_wf_and_3reg x
  have hG'_wf : G'.vertices.Nodup ∧ (∀ e ∈ G'.edges, e.1 ∈ G'.vertices ∧ e.2 ∈ G'.vertices) :=
    ⟨hG'_wf1, hG'_wf2⟩
  rcases hmem with ⟨_, _, _, hS'_mem⟩
  obtain ⟨S', hS'sub, hS'card, hS'cut⟩ := (mem_MinBisection_iff _).mp hS'_mem
  have hG'_len : G'.distinctVertices.length = 4 * K * K * n := by
    rw [Graph.length_distinctVertices, List.toFinset_card_of_nodup hG'_wf.1, hG'_verts,
      List.length_range]
  have hS'card_eq : S'.card = 2 * K * K * n := by
    rw [hG'_len] at hS'card; linarith
  have hS'lt : ∀ w ∈ S', w < 4 * K * K * n := fun w hw => by
    simpa [G'] using hS'sub w hw
  -- Define gadget vertex sets and minority sets
  let Hu (u : ℕ) : Finset ℕ :=
    (Finset.range (4 * K * K)).image fun m => u * (4 * K * K) + m
  have hHu_mem : ∀ u < n, ∀ r < K, ∀ c < K, ∀ t < 4, torusVid K u r c t ∈ Hu u := by
    intro u _ r hr c hc t ht
    simp only [Hu, Finset.mem_image, Finset.mem_range, torusVid]
    refine ⟨(r * K + c) * 4 + t, ?_, ?_⟩
    · have h1 : r * K + c < K * K := by
        have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hr); nlinarith
      nlinarith
    · ring
  have hHu_card : ∀ u, (Hu u).card = 4 * K * K := fun u => by
    rw [Finset.card_image_of_injective _ (add_right_injective _), Finset.card_range]
  -- Gadget internal cut and minority size
  let Su (u : ℕ) : Finset ℕ := S' ∩ Hu u
  let Au (u : ℕ) : Finset ℕ := if (Su u).card ≤ 2 * K * K then Su u else Hu u \ Su u
  have hAu_le : ∀ u, (Au u).card ≤ 2 * K * K := fun u => by
    dsimp only [Au]; split_ifs with h
    · exact h
    · have h4 : 4 * K * K = 2 * (2 * K * K) := by ring
      rw [Finset.card_sdiff_of_subset Finset.inter_subset_right, hHu_card, h4]
      dsimp only [Su] at h; omega
  -- Internal cut of gadget u: count unordered pairs crossing Au u inside Hu u
  -- Specifically, count crossing row edges + crossing col edges + crossing (c,d) edges
  let isInA (u w : ℕ) : Bool := decide (w ∈ Au u)
  let rowCut (u r : ℕ) : ℕ :=
    ((List.range K).filter fun c =>
      isInA u (torusVid K u r c 0) != isInA u (torusVid K u r c 2)).length +
    ((List.range K).filter fun c =>
      isInA u (torusVid K u r c 2) != isInA u (torusVid K u r ((c + 1) % K) 0)).length
  let colCut (u c : ℕ) : ℕ :=
    ((List.range K).filter fun r =>
      isInA u (torusVid K u r c 1) != isInA u (torusVid K u r c 3)).length +
    ((List.range K).filter fun r =>
      isInA u (torusVid K u r c 3) != isInA u (torusVid K u ((r + 1) % K) c 1)).length
  let cdCut (u : ℕ) : ℕ :=
    (((List.range K).flatMap fun r => (List.range K).map fun c => (r, c)).filter fun p =>
      isInA u (torusVid K u p.1 p.2 2) != isInA u (torusVid K u p.1 p.2 3)).length
  let intCut (u : ℕ) : ℕ :=
    ((List.range K).map (rowCut u)).sum + ((List.range K).map (colCut u)).sum + cdCut u
  -- Every edge counted in `intCut u` is a distinct crossing edge of `G'` inside `Hu u`!
  -- And every cross-edge crossing `S'` is disjoint from all `intCut u`!
  -- First, check that `isInA u` agrees with `decide (· ∈ S')` up to complement on `Hu u`
  have hisInA_xor : ∀ u < n, ∀ w1 ∈ Hu u, ∀ w2 ∈ Hu u,
      (isInA u w1 != isInA u w2) = (decide (w1 ∈ S') != decide (w2 ∈ S')) := by
    intro u _ w1 hw1 w2 hw2
    simp only [isInA, Au]
    split_ifs with h
    · simp [Su, hw1, hw2]
    · have h1 : (w1 ∈ Hu u \ Su u) ↔ w1 ∉ S' := by simp [Su, hw1]
      have h2 : (w2 ∈ Hu u \ Su u) ↔ w2 ∉ S' := by simp [Su, hw2]
      by_cases hs1 : w1 ∈ S' <;> by_cases hs2 : w2 ∈ S' <;> simp [h1, h2, hs1, hs2]
  -- Sum of `intCut u` + crossing cross-edges ≤ cut of `S'` in `G'` ≤ 2 * x.bound
  have hcross_pairs_bound :
      let crossCut :=
        (((List.range n).flatMap fun u =>
          ((List.range n).filter fun v =>
            decide (u < v) && x.graph.adjBool (V.getD u 0) (V.getD v 0)).flatMap fun v =>
            let i := (nbrs u).idxOf v
            let j := (nbrs v).idxOf u
            [(torusVid K u i i 0, torusVid K v j j 0),
             (torusVid K u i i 1, torusVid K v j j 1)]).filter fun e =>
          decide (e.1 ∈ S') != decide (e.2 ∈ S')).length
      ((List.range n).map intCut).sum + crossCut ≤
        (G'.induced.interedges (S'.subtype (· ∈ G'.vertices))
          (S'.subtype (· ∈ G'.vertices))ᶜ).card := by
    intro crossCut
    -- Build a duplicate-free list of oriented crossing pairs `(w1, w2)` in `G'` with `w1 ∈
    -- S', w2 ∉ S'`
    let orient (e : ℕ × ℕ) : ℕ × ℕ := if e.1 ∈ S' then e else (e.2, e.1)
    let intListOf := torusIntList K isInA
    let crossList := (crossEdges.filter fun e => decide (e.1 ∈ S') != decide (e.2 ∈ S'))
    let allPairs := (((List.range n).flatMap intListOf) ++ crossList).map orient
    have hlen_int : ∀ u, (intListOf u).length = intCut u := fun u => by
      simp only [intListOf, torusIntList, intCut, rowCut, colCut, cdCut, List.length_append,
        List.length_flatMap, List.length_map]
    have hlen_all : allPairs.length = ((List.range n).map intCut).sum + crossCut := by
      simp only [allPairs, List.length_map, List.length_append, List.length_flatMap,
        hlen_int]; rfl
    rw [← hlen_all]
    -- Show allPairs maps injectively into G'.induced.interedges S' S'ᶜ
    have hsub_inter : ∀ p ∈ allPairs,
        p.1 ∈ G'.vertices ∧ p.2 ∈ G'.vertices ∧ G'.toSimpleGraph.Adj p.1 p.2 ∧
          p.1 ∈ S' ∧ p.2 ∉ S' := by
      intro p hp
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
      have he_edge : e.1 ∈ G'.vertices ∧ e.2 ∈ G'.vertices ∧
          G'.toSimpleGraph.Adj e.1 e.2 ∧
            (decide (e.1 ∈ S') != decide (e.2 ∈ S')) = true := by
        rw [List.mem_append] at he
        rcases he with hi | hc
        · obtain ⟨u, hu, heu⟩ := List.mem_flatMap.mp hi
          rw [List.mem_range] at hu
          have hsub_int : ∀ a b, (a, b) ∈ intListOf u →
              (a, b) ∈ internalEdges ∧ a ∈ Hu u ∧ b ∈ Hu u ∧
                (isInA u a != isInA u b) = true := by
            intro a b hab
            simp only [intListOf, torusIntList, List.mem_append, List.mem_flatMap, List.mem_map,
              List.mem_filter, List.mem_range, Prod.mk.injEq] at hab
            rcases hab with ((⟨r, hr, (⟨c, ⟨hc, htr⟩, rfl, rfl⟩ | ⟨c, ⟨hc, htr⟩, rfl,
              rfl⟩)⟩) |
                ⟨c, hc, (⟨r, ⟨hr, htr⟩, rfl, rfl⟩ | ⟨r, ⟨hr, htr⟩, rfl, rfl⟩)⟩) |
                ⟨⟨r, c⟩, ⟨⟨r', hr, c', hc, heq⟩, htr⟩, rfl, rfl⟩
            · exact ⟨List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu,
                List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
                  List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, by
                    unfold torusCellEdges; split_ifs <;> simp⟩⟩⟩,
                hHu_mem u hu r hr c hc 0 (by omega), hHu_mem u hu r hr c hc 2 (by omega), htr⟩
            · exact ⟨List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu,
                List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
                  List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, by
                    unfold torusCellEdges; split_ifs <;> simp⟩⟩⟩,
                hHu_mem u hu r hr c hc 2 (by omega),
                hHu_mem u hu r hr ((c + 1) % K) (Nat.mod_lt _ hK_pos) 0 (by omega), htr⟩
            · exact ⟨List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu,
                List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
                  List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, by
                    unfold torusCellEdges; split_ifs <;> simp⟩⟩⟩,
                hHu_mem u hu r hr c hc 1 (by omega), hHu_mem u hu r hr c hc 3 (by omega), htr⟩
            · exact ⟨List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu,
                List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
                  List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, by
                    unfold torusCellEdges; split_ifs <;> simp⟩⟩⟩,
                hHu_mem u hu r hr c hc 3 (by omega),
                hHu_mem u hu ((r + 1) % K) (Nat.mod_lt _ hK_pos) c hc 1 (by omega), htr⟩
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
              exact ⟨List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu,
                List.mem_flatMap.mpr ⟨r', List.mem_range.mpr hr,
                  List.mem_flatMap.mpr ⟨c', List.mem_range.mpr hc, by
                    unfold torusCellEdges; split_ifs <;> simp⟩⟩⟩,
                hHu_mem u hu r' hr c' hc 2 (by omega),
                hHu_mem u hu r' hr c' hc 3 (by omega), htr⟩
          obtain ⟨hmem_e, haH, hbH, htr⟩ := hsub_int e.1 e.2 heu
          have hne_e : e.1 ≠ e.2 := by
            intro h; rw [h] at htr; simp at htr
          have heG := hG'_wf.2 e (List.mem_append_left _ hmem_e)
          refine ⟨heG.1, heG.2, (Graph.toSimpleGraph_adj).mpr ⟨hne_e,
            Or.inl (List.mem_append_left _ hmem_e)⟩, ?_⟩
          rwa [← hisInA_xor u hu e.1 haH e.2 hbH]
        · rw [List.mem_filter] at hc
          have heG := hG'_wf.2 e (List.mem_append_right _ hc.1)
          have hne_e : e.1 ≠ e.2 := fun h => by have := hc.2; rw [h] at this; simp at this
          exact ⟨heG.1, heG.2, (Graph.toSimpleGraph_adj).mpr ⟨hne_e,
            Or.inl (List.mem_append_right _ hc.1)⟩, hc.2⟩
      dsimp only [orient]
      split_ifs with h1
      · refine ⟨he_edge.1, he_edge.2.1, he_edge.2.2.1, h1, ?_⟩
        intro h2; have := he_edge.2.2.2; simp [h1, h2] at this
      · refine ⟨he_edge.2.1, he_edge.1, he_edge.2.2.1.symm, ?_, h1⟩
        have := he_edge.2.2.2; simp only [h1, decide_false, Bool.false_bne,
          decide_eq_true_eq] at this; exact this
    -- Check `allPairs.Nodup` (no two distinct entries produce the same unordered pair)
    have hnd_all : allPairs.Nodup := by
      -- Every entry of `((List.range n).flatMap intListOf) ++ crossList` has a distinct
      -- unordered pair `{e.1, e.2}`
      -- characterized by `(min_type, indices)`!
      have hkey_inj : ∀ (p q : ℕ × ℕ), p ∈ ((List.range n).flatMap intListOf) ++ crossList →
          q ∈ ((List.range n).flatMap intListOf) ++ crossList →
          (p = q ∨ (p.1 = q.2 ∧ p.2 = q.1)) → p = q := by
        intro p q hp hq hor
        rcases hor with rfl | ⟨h1, h2⟩
        · rfl
        · exfalso
          have hdir : ∀ e ∈ ((List.range n).flatMap intListOf) ++ crossList,
              torusPairDir K n e := by
            intro e he
            rw [List.mem_append] at he
            rcases he with hi | hc
            · left
              obtain ⟨u, hu, heu⟩ := List.mem_flatMap.mp hi
              rw [List.mem_range] at hu
              simp only [intListOf, torusIntList, List.mem_append, List.mem_flatMap, List.mem_map,
                List.mem_filter, List.mem_range] at heu
              rcases heu with ((⟨r, hr, (⟨c, ⟨hc, _⟩, rfl⟩ | ⟨c, ⟨hc, _⟩, rfl⟩)⟩) |
                  ⟨c, hc, (⟨r, ⟨hr, _⟩, rfl⟩ | ⟨r, ⟨hr, _⟩, rfl⟩)⟩) |
                  ⟨⟨r, c⟩, ⟨⟨r', hr, c', hc, heq⟩, _⟩, rfl⟩
              · exact ⟨u, hu, r, hr, c, hc, Or.inl rfl⟩
              · exact ⟨u, hu, r, hr, c, hc, Or.inr (Or.inl rfl)⟩
              · exact ⟨u, hu, r, hr, c, hc, Or.inr (Or.inr (Or.inl rfl))⟩
              · exact ⟨u, hu, r, hr, c, hc, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
                exact ⟨u, hu, r', hr, c', hc, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
            · right
              obtain ⟨u, hu, heu⟩ := List.mem_flatMap.mp (List.mem_filter.mp hc).1
              rw [List.mem_range] at hu
              obtain ⟨v, hv, hev⟩ := List.mem_flatMap.mp heu
              simp only [List.mem_filter, List.mem_range, Bool.and_eq_true,
                decide_eq_true_eq,
                Graph.adjBool_eq_true_iff] at hv
              have hi := (hidx_lt u v hu hv.1 hv.2.2).trans (hnbrs_len u hu)
              have hj := (hidx_lt v u hv.1 hu hv.2.2.symm).trans (hnbrs_len v hv.1)
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
              exact ⟨u, hu, v, hv.1, hv.2.1, _, hi, _, hj, hev⟩
          exact torus_pair_no_reverse hK_ge hK_pos (hdir p hp) (hdir q hq) h1 h2
      have hnd_raw : (((List.range n).flatMap intListOf) ++ crossList).Nodup := by
        rw [List.nodup_append]
        refine ⟨torusIntList_nodup K hK_pos n isInA, ?_, ?_⟩
        · refine List.Nodup.filter _ ?_
          rw [List.nodup_flatMap]
          refine ⟨fun u hu => ?_, ?_⟩
          · rw [List.mem_range] at hu
            rw [List.nodup_flatMap]
            refine ⟨fun v hv => ?_, ?_⟩
            · simp only [List.mem_filter, List.mem_range, Bool.and_eq_true,
              decide_eq_true_eq,
                Graph.adjBool_eq_true_iff] at hv
              have hi := (hidx_lt u v hu hv.1 hv.2.2).trans (hnbrs_len u hu)
              have hj := (hidx_lt v u hv.1 hu hv.2.2.symm).trans (hnbrs_len v hv.1)
              simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
                List.nodup_nil, Prod.mk.injEq, and_true]
              intro h; have :=
                (torusVid_injective hK_pos hi hi (by omega) hi hi (by omega) h.1).2.2.2; omega
            · refine (List.nodup_range.filter _).pairwise_of_forall_ne fun v1 hv1 v2 hv2 hne => ?_
              intro p hp1 hp2
              simp only [List.mem_filter, List.mem_range, Bool.and_eq_true,
                decide_eq_true_eq,
                Graph.adjBool_eq_true_iff] at hv1 hv2
              have hj1 := (hidx_lt v1 u hv1.1 hu hv1.2.2.symm).trans (hnbrs_len v1 hv1.1)
              have hj2 := (hidx_lt v2 u hv2.1 hu hv2.2.2.symm).trans (hnbrs_len v2 hv2.1)
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hp1 hp2
              rcases hp1 with rfl | rfl <;> rcases hp2 with h2 | h2
              · exact hne (torusVid_injective hK_pos hj1 hj1 (by omega) hj2 hj2 (by omega)
                  (Prod.mk.inj h2).2).1
              · have := (torusVid_injective hK_pos hj1 hj1 (by omega) hj2 hj2 (by omega)
                  (Prod.mk.inj h2).2).2.2.2; omega
              · have := (torusVid_injective hK_pos hj1 hj1 (by omega) hj2 hj2 (by omega)
                  (Prod.mk.inj h2).2).2.2.2; omega
              · exact hne (torusVid_injective hK_pos hj1 hj1 (by omega) hj2 hj2 (by omega)
                  (Prod.mk.inj h2).2).1
          · refine List.nodup_range.pairwise_of_forall_ne fun u1 hu1 u2 hu2 hne => ?_
            intro p hp1 hp2
            rw [List.mem_range] at hu1 hu2
            simp only [List.mem_flatMap, List.mem_filter, List.mem_range, Bool.and_eq_true,
              decide_eq_true_eq, Graph.adjBool_eq_true_iff, List.mem_cons, List.not_mem_nil,
                or_false] at hp1 hp2
            obtain ⟨v1, ⟨hv1, huv1, hadj1⟩, rfl | rfl⟩ := hp1 <;>
              obtain ⟨v2, ⟨hv2, huv2, hadj2⟩, h2 | h2⟩ := hp2 <;>
              (have hi1 := (hidx_lt u1 v1 hu1 hv1 hadj1).trans (hnbrs_len u1 hu1);
               have hi2 := (hidx_lt u2 v2 hu2 hv2 hadj2).trans (hnbrs_len u2 hu2);
               exact hne (torusVid_injective hK_pos hi1 hi1 (by omega) hi2 hi2 (by omega)
                 (Prod.mk.inj h2).1).1)
        · intro p hp q hq heq; subst heq
          obtain ⟨u1, hu1, hp1⟩ := List.mem_flatMap.mp hp
          have hdiv := torusIntList_div_eq K hK_pos isInA u1 p hp1
          obtain ⟨u2, hu2, hq1⟩ := List.mem_flatMap.mp (List.mem_filter.mp hq).1
          rw [List.mem_range] at hu2
          obtain ⟨v2, hv2, hq2⟩ := List.mem_flatMap.mp hq1
          simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
            Graph.adjBool_eq_true_iff] at hv2
          have hi2 := (hidx_lt u2 v2 hu2 hv2.1 hv2.2.2).trans (hnbrs_len u2 hu2)
          have hj2 := (hidx_lt v2 u2 hv2.1 hu2 hv2.2.2.symm).trans (hnbrs_len v2 hv2.1)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq2
          rcases hq2 with rfl | rfl
          · have h1 := torusVid_div K u2 _ _ 0 hi2 hi2 (by omega)
            have h2 := torusVid_div K v2 _ _ 0 hj2 hj2 (by omega)
            dsimp only at hdiv; omega
          · have h1 := torusVid_div K u2 _ _ 1 hi2 hi2 (by omega)
            have h2 := torusVid_div K v2 _ _ 1 hj2 hj2 (by omega)
            dsimp only at hdiv; omega
      refine hnd_raw.map_on fun p hp q hq hor => hkey_inj p q hp hq ?_
      dsimp only [orient] at hor
      split_ifs at hor with h1 h2
      · exact Or.inl hor
      · exact Or.inr (Prod.mk.inj hor)
      · exact Or.inr ⟨(Prod.mk.inj hor).2, (Prod.mk.inj hor).1⟩
      · exact Or.inl (Prod.ext (Prod.mk.inj hor).2 (Prod.mk.inj hor).1)
    rw [← List.toFinset_card_of_nodup hnd_all,
        ← Finset.card_map ((Function.Embedding.subtype (· ∈ G'.vertices)).prodMap
          (Function.Embedding.subtype (· ∈ G'.vertices)))]
    refine Finset.card_le_card fun p hp => ?_
    rcases p with ⟨w1, w2⟩
    have hmem := List.mem_toFinset.mp hp
    obtain ⟨hw1, hw2, hadj, hw1S, hw2S⟩ := hsub_inter (w1, w2) hmem
    exact Finset.mem_map.mpr ⟨(⟨w1, hw1⟩, ⟨w2, hw2⟩),
      by simp [SimpleGraph.interedges, Rel.mem_interedges_iff, hw1S, hw2S, hadj], rfl⟩
  -- Now apply our clean row/col/cd analysis to EVERY gadget u < n!
  have hsum_int_lt : ((List.range n).map intCut).sum < K / 2 := by
    have h1 := hcross_pairs_bound
    have h2 := hS'cut
    dsimp only at h1 h2
    have h4nn : 4 * n * n = 4 * (n * n) := by ring
    have : ((List.range n).map intCut).sum ≤ 2 * x.bound := by omega
    omega
  have hAu_analysis : ∀ u < n, (Au u).card ≤ K * intCut u ∧
      (((Finset.range (nbrs u).length).filter fun i => isInA u (torusVid K u i i 0) =
        true).card +
       ((Finset.range (nbrs u).length).filter fun i => isInA u (torusVid K u i i 1) =
         true).card ≤ intCut u) := fun u hu => by
    have hint_lt : intCut u < K / 2 := by
      have hle : intCut u ≤ ((List.range n).map intCut).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩)
      omega
    have hAu_sub : ∀ w ∈ Au u, w ∈ Hu u := fun w hw => by
      dsimp only [Au] at hw; split_ifs at hw
      · exact (Finset.mem_inter.mp hw).2
      · exact (Finset.mem_sdiff.mp hw).1
    have hcd_eq : cdCut u =
        ((List.range K).flatMap fun r => (List.range K).filter fun c =>
          isInA u (torusVid K u r c 2) != isInA u (torusVid K u r c 3)).length := by
      simp only [cdCut, List.filter_flatMap, List.filter_map, List.length_flatMap,
        List.length_map, Function.comp_def]
    have hres := torus_gadget_minority_bounds hK_ge (hnbrs_len u hu) (Au u) hAu_sub (hAu_le u)
      (by dsimp only; dsimp only [intCut] at hint_lt; rwa [← hcd_eq])
    dsimp only at hres
    dsimp only [intCut]
    rw [← hcd_eq] at hres
    exact hres
  -- Define majority side `T_idx` in `{0, ..., n-1}`
  let Tidx : Finset ℕ := (Finset.range n).filter fun u => 2 * K * K < (Su u).card
  -- Prove `2 * Tidx.card = n` using `∑_u |Au u| < K² / 2 < 4 K²`!
  have hT_card : 2 * Tidx.card = n := by
    have hS'_part : S'.card = ∑ u ∈ Finset.range n, (Su u).card := by
      have hU : S' = (Finset.range n).biUnion Su := by
        ext w
        simp only [Finset.mem_biUnion, Finset.mem_range, Su, Finset.mem_inter, Hu,
          Finset.mem_image, Finset.mem_range]
        constructor
        · intro hw
          have hlt := hS'lt w hw
          refine ⟨w / (4 * K * K), ?_, hw, w % (4 * K * K), Nat.mod_lt _ (by nlinarith), ?_⟩
          · have : w < (4 * K * K) * n := by linarith
            exact Nat.div_lt_of_lt_mul this
          · have := Nat.div_add_mod w (4 * K * K); linarith
        · rintro ⟨_, _, hw, _⟩; exact hw
      have hdisj : Set.PairwiseDisjoint (↑(Finset.range n)) Su := by
        intro u1 _ u2 _ hne
        change Disjoint (Su u1) (Su u2)
        rw [Finset.disjoint_left]; intro w hw1 hw2
        obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hw1).2
        obtain ⟨m2, hm2, heq⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hw2).2
        rw [Finset.mem_range] at hm1 hm2
        have hpos : 0 < 4 * K * K := by nlinarith
        have hq := congrArg (· / (4 * K * K)) heq
        rw [Nat.mul_comm u1 _, Nat.mul_comm u2 _, Nat.mul_add_div hpos,
          Nat.mul_add_div hpos,
          Nat.div_eq_of_lt hm1, Nat.div_eq_of_lt hm2] at hq
        exact hne (by omega)
      conv_lhs => rw [hU]
      rw [Finset.card_biUnion hdisj]
    have hsum_A : ∑ u ∈ Finset.range n, (Au u).card < K * K := by
      calc
        ∑ u ∈ Finset.range n, (Au u).card
            ≤ ∑ u ∈ Finset.range n, K * intCut u :=
          Finset.sum_le_sum fun u hu => (hAu_analysis u (Finset.mem_range.mp hu)).1
        _ = K * ∑ u ∈ Finset.range n, intCut u := by rw [Finset.mul_sum]
        _ = K * ((List.range n).map intCut).sum := by rw [sum_range_eq_list_sum]
        _ < K * K := by
          have : ((List.range n).map intCut).sum < K := by omega
          exact Nat.mul_lt_mul_of_pos_left this hK_pos
    -- Express `S'.card` via `Tidx`:
    have hsplit_S : ∑ u ∈ Finset.range n, (Su u).card + ∑ u ∈ Tidx, (Au u).card =
        4 * K * K * Tidx.card +
          ∑ u ∈ (Finset.range n).filter (fun u => ¬ 2 * K * K < (Su u).card),
            (Au u).card := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n)
        (fun u => 2 * K * K < (Su u).card)]
      have hT_eq : (Finset.range n).filter (fun u => 2 * K * K < (Su u).card) = Tidx := rfl
      rw [hT_eq]
      have h1 : ∀ u ∈ Tidx, (Su u).card + (Au u).card = 4 * K * K := by
        intro u hu
        have hgt : ¬ (Su u).card ≤ 2 * K * K := by
          have := (Finset.mem_filter.mp hu).2; omega
        simp only [Au, hgt, ↓reduceIte]
        have := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_right (s₁ :=
          S') (s₂ := Hu u))
        rw [hHu_card, add_comm] at this
        exact this
      have h2 : ∀ u ∈ (Finset.range n).filter (fun u => ¬ 2 * K * K < (Su u).card),
          (Su u).card = (Au u).card := by
        intro u hu
        have hle : (Su u).card ≤ 2 * K * K := by
          have := (Finset.mem_filter.mp hu).2; omega
        simp [Au, hle]
      have hsum1 : ∑ u ∈ Tidx, (Su u).card + ∑ u ∈ Tidx, (Au u).card =
        4 * K * K * Tidx.card := by
        rw [← Finset.sum_add_distrib, Finset.sum_congr rfl h1, Finset.sum_const,
          smul_eq_mul, mul_comm]
      have hsum2 := Finset.sum_congr rfl h2
      omega
    have hA_T_le : ∑ u ∈ Tidx, (Au u).card ≤ ∑ u ∈ Finset.range n, (Au u).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hA_Tc_le : ∑ u ∈ (Finset.range n).filter (fun u => ¬ 2 * K * K < (Su u).card),
      (Au u).card ≤
        ∑ u ∈ Finset.range n, (Au u).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    rw [← hS'_part, hS'card_eq] at hsplit_S
    -- `|4 K² * |Tidx| - 2 K² * n| < K²`, so `2 * |Tidx| = n`!
    have hdiff1 : 4 * K * K * Tidx.card < 2 * K * K * n + K * K := by omega
    have hdiff2 : 2 * K * K * n < 4 * K * K * Tidx.card + K * K := by omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle1 : 2 * Tidx.card + 1 ≤ n := hlt
      have hm1 := Nat.mul_le_mul_left (2 * K * K) hle1
      have heq1 : 2 * K * K * (2 * Tidx.card + 1) = 4 * K * K * Tidx.card + 2 * K * K := by ring
      have h2KK : 2 * K * K = 2 * (K * K) := by ring
      have hKK : 0 < K * K := Nat.mul_pos hK_pos hK_pos
      omega
    · have hle2 : n + 1 ≤ 2 * Tidx.card := hgt
      have hm2 := Nat.mul_le_mul_left (2 * K * K) hle2
      have heq2 : 2 * K * K * (n + 1) = 2 * K * K * n + 2 * K * K := by ring
      have heq3 : 2 * K * K * (2 * Tidx.card) = 4 * K * K * Tidx.card := by ring
      have h2KK : 2 * K * K = 2 * (K * K) := by ring
      have hKK : 0 < K * K := Nat.mul_pos hK_pos hK_pos
      omega
  -- Finally, prove `2 * |cut_G(T)| ≤ |crossCut| + ∑_u |A_u ∩ P_u| ≤ 2 * x.bound`!
  let T : Finset ℕ := Tidx.image fun u => V.getD u 0
  have hT_sub : ∀ v ∈ T, v ∈ x.graph.vertices := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    have hu' : u < n := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    exact Graph.mem_distinctVertices.mp (getD_mem_of_lt hu')
  have hT_card_eq : T.card = Tidx.card := by
    refine Finset.card_image_of_injOn fun u1 hu1 u2 hu2 h => ?_
    exact hV_inj (Finset.mem_range.mp (Finset.mem_filter.mp hu1).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hu2).1) h
  have hT_iff : ∀ u < n, V.getD u 0 ∈ T ↔ u ∈ Tidx := by
    intro u hu
    simp only [T, Finset.mem_image]
    exact ⟨fun ⟨u', hu',
      h⟩ => hV_inj (Finset.mem_range.mp (Finset.mem_filter.mp hu').1) hu h ▸ hu',
      fun huT => ⟨u, huT, rfl⟩⟩
  -- Count crossing edges of G for T:
  let Gcross := ((List.range n).flatMap fun u =>
    ((List.range n).filter fun v =>
      decide (u < v) && x.graph.adjBool (V.getD u 0) (V.getD v 0)).map fun v => (u,
        v)).filter fun e =>
    decide (e.1 ∈ Tidx) != decide (e.2 ∈ Tidx)
  have hGcross_eq : (x.graph.induced.interedges (T.subtype (· ∈ x.graph.vertices))
      (T.subtype (· ∈ x.graph.vertices))ᶜ).card = Gcross.length := by
    -- Biject with Gcross via `e ↦ if e.1 ∈ Tidx then (V.getD e.1 0, V.getD e.2 0) else
    -- (V.getD e.2 0, V.getD e.1 0)`
    let mapE (e : ℕ × ℕ) : ℕ × ℕ :=
      if e.1 ∈ Tidx then (V.getD e.1 0, V.getD e.2 0) else (V.getD e.2 0, V.getD e.1 0)
    have hnd_Gc : (Gcross.map mapE).Nodup := by
      have hnd0 : Gcross.Nodup := by
        refine List.Nodup.filter _ ?_
        rw [List.nodup_flatMap]
        refine ⟨fun u _ => (List.nodup_range.filter _).map fun _ _ h => (Prod.mk.inj h).2,
          List.nodup_range.pairwise_of_forall_ne fun u1 _ u2 _ hne p hp1 hp2 => ?_⟩
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp1
        obtain ⟨_, _, h2⟩ := List.mem_map.mp hp2
        exact hne (Prod.mk.inj h2).1.symm
      refine hnd0.map_on fun e1 he1 e2 he2 h => ?_
      have hlt1 : e1.1 < n ∧ e1.2 < n ∧ e1.1 < e1.2 := by
        simp only [Gcross, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range,
          Bool.and_eq_true, decide_eq_true_eq] at he1
        obtain ⟨⟨u, hu, v, ⟨hv, huv, _⟩, rfl⟩, _⟩ := he1
        exact ⟨hu, hv, huv⟩
      have hlt2 : e2.1 < n ∧ e2.2 < n ∧ e2.1 < e2.2 := by
        simp only [Gcross, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range,
          Bool.and_eq_true, decide_eq_true_eq] at he2
        obtain ⟨⟨u, hu, v, ⟨hv, huv, _⟩, rfl⟩, _⟩ := he2
        exact ⟨hu, hv, huv⟩
      dsimp only [mapE] at h
      split_ifs at h with h1 h2
      · exact Prod.ext (hV_inj hlt1.1 hlt2.1 (Prod.mk.inj h).1)
          (hV_inj hlt1.2.1 hlt2.2.1 (Prod.mk.inj h).2)
      · have := hV_inj hlt1.1 hlt2.2.1 (Prod.mk.inj h).1
        have := hV_inj hlt1.2.1 hlt2.1 (Prod.mk.inj h).2
        omega
      · have := hV_inj hlt1.2.1 hlt2.1 (Prod.mk.inj h).1
        have := hV_inj hlt1.1 hlt2.2.1 (Prod.mk.inj h).2
        omega
      · exact Prod.ext (hV_inj hlt1.1 hlt2.1 (Prod.mk.inj h).2)
          (hV_inj hlt1.2.1 hlt2.2.1 (Prod.mk.inj h).1)
    rw [← List.length_map mapE]
    refine SimpleMaxCut.card_interedges_eq_length x.graph T hnd_Gc fun ⟨a, b⟩ => ?_
    simp only [List.mem_map, Gcross, List.mem_filter, List.mem_flatMap, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff]
    constructor
    · rintro ⟨⟨u, v⟩, ⟨⟨u', hu', v', ⟨hv', huv', hadj'⟩, heq⟩, htr⟩, hmap⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      dsimp only [mapE] at hmap
      split_ifs at hmap with huT
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmap
        have hvT : v' ∉ Tidx := fun h => by simp [huT, h] at htr
        exact ⟨Graph.mem_distinctVertices.mp (getD_mem_of_lt hu'),
          Graph.mem_distinctVertices.mp (getD_mem_of_lt hv'), hadj',
          (hT_iff u' hu').mpr huT, fun h => hvT ((hT_iff v' hv').mp h)⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmap
        have hvT : v' ∈ Tidx := by
          simp only [huT, decide_false, Bool.false_bne, decide_eq_true_eq] at htr; exact htr
        exact ⟨Graph.mem_distinctVertices.mp (getD_mem_of_lt hv'),
          Graph.mem_distinctVertices.mp (getD_mem_of_lt hu'), hadj'.symm,
          (hT_iff v' hv').mpr hvT, fun h => huT ((hT_iff u' hu').mp h)⟩
    · rintro ⟨ha, hb, hadj, haT, hbT⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_iff_getElem.mp (Graph.mem_distinctVertices.mpr ha)
      obtain ⟨v, hv, rfl⟩ := List.mem_iff_getElem.mp (Graph.mem_distinctVertices.mpr hb)
      have hgu : V.getD u 0 = V[u] := List.getD_eq_getElem _ 0 hu
      have hgv : V.getD v 0 = V[v] := List.getD_eq_getElem _ 0 hv
      rw [← hgu] at hadj haT; rw [← hgv] at hadj hbT
      have huT : u ∈ Tidx := (hT_iff u hu).mp haT
      have hvT : v ∉ Tidx := fun h => hbT ((hT_iff v hv).mpr h)
      have hne : u ≠ v := fun h => hvT (h ▸ huT)
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨(u, v), ⟨⟨u, hu, v, ⟨hv, hlt, hadj⟩, rfl⟩, by simp [huT, hvT]⟩,
          by dsimp only [mapE]; simp only [huT, ↓reduceIte, hgu, hgv]; rfl⟩
      · exact ⟨(v, u), ⟨⟨v, hv, u, ⟨hu, hgt, hadj.symm⟩, rfl⟩, by simp [huT, hvT]⟩,
          by dsimp only [mapE]; simp only [hvT, ↓reduceIte, hgu, hgv]; rfl⟩
  -- For every `e = (u, v) ∈ Gcross`, its 2 cross-edges are either in `crossCut` OR hit a
  -- port in `Au u` or `Au v`!
  have h2Gcross : 2 * Gcross.length ≤
      ((crossEdges.filter fun e => decide (e.1 ∈ S') != decide (e.2 ∈ S')).length) +
      ((List.range n).map intCut).sum := by
    -- Map each `(e, t) ∈ Gcross × {0, 1}` either to `crossCut` (if crossing) or to `(u, i,
    -- t)` / `(v, j, t)` in `Au`!
    let portA : Finset (ℕ × ℕ × ℕ) :=
      (Finset.range n).biUnion fun u =>
        (((Finset.range (nbrs u).length).filter fun i => isInA u (torusVid K u i i 0) =
          true).image (fun i => (u, i, 0))) ∪
        (((Finset.range (nbrs u).length).filter fun i => isInA u (torusVid K u i i 1) =
          true).image (fun i => (u, i, 1)))
    have hportA_card : portA.card ≤ ((List.range n).map intCut).sum := by
      rw [← sum_range_eq_list_sum]
      refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun u hu => ?_)
      refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).1),
          Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).1)]
      exact (hAu_analysis u (Finset.mem_range.mp hu)).2
    let GcPair : Finset ((ℕ × ℕ) × ℕ) := Gcross.toFinset ×ˢ ({0, 1} : Finset ℕ)
    have hGc_nd : Gcross.Nodup := by
      refine List.Nodup.filter _ ?_
      rw [List.nodup_flatMap]
      refine ⟨fun u _ => (List.nodup_range.filter _).map fun _ _ h => (Prod.mk.inj h).2,
        List.nodup_range.pairwise_of_forall_ne fun u1 _ u2 _ hne p hp1 hp2 => ?_⟩
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp1
      obtain ⟨_, _, h2⟩ := List.mem_map.mp hp2
      exact hne (Prod.mk.inj h2).1.symm
    have hGcPair_card : GcPair.card = 2 * Gcross.length := by
      rw [Finset.card_product, List.toFinset_card_of_nodup hGc_nd,
        Finset.card_pair (by decide), mul_comm]
    -- Split GcPair into those whose cross-edge IS in S'-cut vs those NOT in S'-cut!
    let ceOf (p : (ℕ × ℕ) × ℕ) : ℕ × ℕ :=
      (torusVid K p.1.1 ((nbrs p.1.1).idxOf p.1.2) ((nbrs p.1.1).idxOf p.1.2) p.2,
       torusVid K p.1.2 ((nbrs p.1.2).idxOf p.1.1) ((nbrs p.1.2).idxOf p.1.1) p.2)
    let good := GcPair.filter fun p => decide ((ceOf p).1 ∈ S') != decide ((ceOf p).2 ∈ S')
    let bad := GcPair.filter fun p => ¬ (decide ((ceOf p).1 ∈ S') != decide ((ceOf p).2 ∈ S')) =
      true
    have hsplit_Gc : good.card + bad.card = 2 * Gcross.length := by
      rw [← hGcPair_card]; exact Finset.card_filter_add_card_filter_not _
    have hGcPair_mem : ∀ p ∈ GcPair,
        p.1.1 < n ∧ p.1.2 < n ∧ p.1.1 < p.1.2 ∧
        x.graph.toSimpleGraph.Adj (V.getD p.1.1 0) (V.getD p.1.2 0) ∧
        (decide (p.1.1 ∈ Tidx) != decide (p.1.2 ∈ Tidx)) = true ∧
        (p.2 = 0 ∨ p.2 = 1) := by
      intro p hp
      obtain ⟨he, ht⟩ := Finset.mem_product.mp hp
      rw [List.mem_toFinset] at he
      simp only [Gcross, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range,
        Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff] at he
      obtain ⟨⟨u, hu, v, ⟨hv, huv, hadj⟩, heq⟩, htr⟩ := he
      rcases p with ⟨⟨a, b⟩, t⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      exact ⟨hu, hv, huv, hadj, htr, ht⟩
    have hgood_le : good.card ≤
        (crossEdges.filter fun e => decide (e.1 ∈ S') != decide (e.2 ∈ S')).length := by
      have hce_inj : Set.InjOn ceOf ↑good := by
        intro p1 hp1 p2 hp2 hce
        obtain ⟨hu1, hv1, _, hadj1, _, ht1⟩ := hGcPair_mem p1 (Finset.mem_filter.mp hp1).1
        obtain ⟨hu2, hv2, _, hadj2, _, ht2⟩ := hGcPair_mem p2 (Finset.mem_filter.mp hp2).1
        have hi1 := (hidx_lt _ _ hu1 hv1 hadj1).trans (hnbrs_len _ hu1)
        have hj1 := (hidx_lt _ _ hv1 hu1 hadj1.symm).trans (hnbrs_len _ hv1)
        have hi2 := (hidx_lt _ _ hu2 hv2 hadj2).trans (hnbrs_len _ hu2)
        have hj2 := (hidx_lt _ _ hv2 hu2 hadj2.symm).trans (hnbrs_len _ hv2)
        have h1 := torusVid_injective hK_pos hi1 hi1 (by omega) hi2 hi2 (by omega)
          (Prod.mk.inj hce).1
        have h2 := torusVid_injective hK_pos hj1 hj1 (by omega) hj2 hj2 (by omega)
          (Prod.mk.inj hce).2
        rcases p1 with ⟨⟨u1, v1⟩, t1⟩; rcases p2 with ⟨⟨u2, v2⟩, t2⟩
        dsimp only at h1 h2; rw [h1.1, h2.1, h1.2.2.2]
      have hce_sub : good.image ceOf ⊆
          (crossEdges.filter fun e => decide (e.1 ∈ S') != decide (e.2 ∈ S')).toFinset := by
        intro e he
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨hpG, hpcross⟩ := Finset.mem_filter.mp hp
        obtain ⟨hu, hv, huv, hadj, _, ht⟩ := hGcPair_mem p hpG
        rw [List.mem_toFinset, List.mem_filter]
        refine ⟨?_, hpcross⟩
        refine List.mem_flatMap.mpr ⟨p.1.1, List.mem_range.mpr hu,
          List.mem_flatMap.mpr ⟨p.1.2, ?_, ?_⟩⟩
        · simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
            Graph.adjBool_eq_true_iff]
          exact ⟨hv, huv, hadj⟩
        · rcases ht with h0 | h1
          · simp [ceOf, h0]
          · simp [ceOf, h1]
      calc
        good.card = (good.image ceOf).card := (Finset.card_image_of_injOn hce_inj).symm
        _ ≤ (crossEdges.filter fun e => decide (e.1 ∈ S') != decide (e.2 ∈ S')).toFinset.card :=
          Finset.card_le_card hce_sub
        _ ≤ (crossEdges.filter fun e => decide (e.1 ∈ S') != decide (e.2 ∈ S')).length :=
          List.toFinset_card_le _
    have hbad_le : bad.card ≤ ((List.range n).map intCut).sum := by
      let f (p : (ℕ × ℕ) × ℕ) : ℕ × ℕ × ℕ :=
        if isInA p.1.1 (ceOf p).1 then (p.1.1, (nbrs p.1.1).idxOf p.1.2, p.2)
        else (p.1.2, (nbrs p.1.2).idxOf p.1.1, p.2)
      have hf_sub : bad.image f ⊆ portA := by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨hpG, hpbad⟩ := Finset.mem_filter.mp hp
        obtain ⟨hu, hv, huv, hadj, htr, ht⟩ := hGcPair_mem p hpG
        have hi_lt : (nbrs p.1.1).idxOf p.1.2 < (nbrs p.1.1).length :=
          hidx_lt _ _ hu hv hadj
        have hj_lt : (nbrs p.1.2).idxOf p.1.1 < (nbrs p.1.2).length :=
          hidx_lt _ _ hv hu hadj.symm
        have hiK : (nbrs p.1.1).idxOf p.1.2 < K := hi_lt.trans (hnbrs_len _ hu)
        have hjK : (nbrs p.1.2).idxOf p.1.1 < K := hj_lt.trans (hnbrs_len _ hv)
        have hmem1 : (ceOf p).1 ∈ Hu p.1.1 := hHu_mem _ hu _ hiK _ hiK p.2 (by omega)
        have hmem2 : (ceOf p).2 ∈ Hu p.1.2 := hHu_mem _ hv _ hjK _ hjK p.2 (by omega)
        have hsame : (ceOf p).1 ∈ S' ↔ (ceOf p).2 ∈ S' := by
          by_cases h1 : (ceOf p).1 ∈ S' <;> by_cases h2 : (ceOf p).2 ∈ S' <;>
            simp [h1, h2] at hpbad ⊢
        have hor : isInA p.1.1 (ceOf p).1 = true ∨ isInA p.1.2 (ceOf p).2 = true := by
          have hiff1 : isInA p.1.1 (ceOf p).1 = true ↔
              (if p.1.1 ∈ Tidx then (ceOf p).1 ∉ S' else (ceOf p).1 ∈ S') := by
            simp only [isInA, Au, decide_eq_true_eq, Tidx, Finset.mem_filter,
              Finset.mem_range, hu, true_and]
            by_cases hgt : 2 * K * K < (Su p.1.1).card
            · have hle : ¬ (Su p.1.1).card ≤ 2 * K * K := by omega
              simp [hle, hgt, Su, hmem1]
            · have hle : (Su p.1.1).card ≤ 2 * K * K := by omega
              simp [hle, hgt, Su, hmem1]
          have hiff2 : isInA p.1.2 (ceOf p).2 = true ↔
              (if p.1.2 ∈ Tidx then (ceOf p).2 ∉ S' else (ceOf p).2 ∈ S') := by
            simp only [isInA, Au, decide_eq_true_eq, Tidx, Finset.mem_filter,
              Finset.mem_range, hv, true_and]
            by_cases hgt : 2 * K * K < (Su p.1.2).card
            · have hle : ¬ (Su p.1.2).card ≤ 2 * K * K := by omega
              simp [hle, hgt, Su, hmem2]
            · have hle : (Su p.1.2).card ≤ 2 * K * K := by omega
              simp [hle, hgt, Su, hmem2]
          by_cases h1 : p.1.1 ∈ Tidx <;> by_cases h2 : p.1.2 ∈ Tidx <;> simp [h1, h2] at htr
          · by_cases hs : (ceOf p).1 ∈ S'
            · right; exact hiff2.mpr (by simp [h2, hsame.mp hs])
            · left; exact hiff1.mpr (by simp [h1, hs])
          · by_cases hs : (ceOf p).1 ∈ S'
            · left; exact hiff1.mpr (by simp [h1, hs])
            · right; exact hiff2.mpr (by
                simp only [h2, ↓reduceIte]; exact fun hc => hs (hsame.mpr hc))
        dsimp only [f]
        split_ifs with hA1
        · simp only [portA, Finset.mem_biUnion, Finset.mem_range, Finset.mem_union,
          Finset.mem_image,
            Finset.mem_filter]
          refine ⟨p.1.1, hu, ?_⟩
          rcases ht with h0 | h1
          · left; exact ⟨_, ⟨hi_lt, by simpa [ceOf, h0] using hA1⟩, by simp [h0]⟩
          · right; exact ⟨_, ⟨hi_lt, by simpa [ceOf, h1] using hA1⟩, by simp [h1]⟩
        · have hA2 : isInA p.1.2 (ceOf p).2 = true := hor.resolve_left hA1
          simp only [portA, Finset.mem_biUnion, Finset.mem_range, Finset.mem_union,
            Finset.mem_image,
            Finset.mem_filter]
          refine ⟨p.1.2, hv, ?_⟩
          rcases ht with h0 | h1
          · left; exact ⟨_, ⟨hj_lt, by simpa [ceOf, h0] using hA2⟩, by simp [h0]⟩
          · right; exact ⟨_, ⟨hj_lt, by simpa [ceOf, h1] using hA2⟩, by simp [h1]⟩
      have hf_inj : Set.InjOn f ↑bad := by
        intro p1 hp1 p2 hp2 hfeq
        obtain ⟨hu1, hv1, huv1, hadj1, _, _⟩ := hGcPair_mem p1 (Finset.mem_filter.mp hp1).1
        obtain ⟨hu2, hv2, huv2, hadj2, _, _⟩ := hGcPair_mem p2 (Finset.mem_filter.mp hp2).1
        have hm1 : p1.1.2 ∈ nbrs p1.1.1 := (hmem_nbrs _ _).mpr ⟨hv1, hadj1⟩
        have hm1' : p1.1.1 ∈ nbrs p1.1.2 := (hmem_nbrs _ _).mpr ⟨hu1, hadj1.symm⟩
        have hm2 : p2.1.2 ∈ nbrs p2.1.1 := (hmem_nbrs _ _).mpr ⟨hv2, hadj2⟩
        have hm2' : p2.1.1 ∈ nbrs p2.1.2 := (hmem_nbrs _ _).mpr ⟨hu2, hadj2.symm⟩
        rcases p1 with ⟨⟨u1, v1⟩, t1⟩; rcases p2 with ⟨⟨u2, v2⟩, t2⟩
        dsimp only [f] at hfeq
        dsimp only at huv1 huv2 hm1 hm1' hm2 hm2'
        split_ifs at hfeq with h1 h2
        · simp only [Prod.mk.injEq] at hfeq
          obtain ⟨rfl, hi, rfl⟩ := hfeq
          exact Prod.ext (Prod.ext rfl (hidx_inj _ _ _ hm1 hm2 hi)) rfl
        · simp only [Prod.mk.injEq] at hfeq
          obtain ⟨huv, hi, _⟩ := hfeq; subst huv
          have := hidx_inj _ _ _ hm1 hm2' hi; omega
        · simp only [Prod.mk.injEq] at hfeq
          obtain ⟨huv, hi, _⟩ := hfeq; subst huv
          have := hidx_inj _ _ _ hm1' hm2 hi; omega
        · simp only [Prod.mk.injEq] at hfeq
          obtain ⟨rfl, hi, rfl⟩ := hfeq
          exact Prod.ext (Prod.ext (hidx_inj _ _ _ hm1' hm2' hi) rfl) rfl
      calc
        bad.card = (bad.image f).card := (Finset.card_image_of_injOn hf_inj).symm
        _ ≤ portA.card := Finset.card_le_card hf_sub
        _ ≤ ((List.range n).map intCut).sum := hportA_card
    omega
  -- Conclude `x ∈ MinBisection`
  rw [mem_MinBisection_iff]
  refine ⟨T, hT_sub, by rw [hT_card_eq, hT_card], ?_⟩
  rw [hGcross_eq]
  have h1 := hcross_pairs_bound
  have h2 := hS'cut
  dsimp only [crossEdges] at h2Gcross
  dsimp only at h1 h2
  omega

/-- Correctness of `toThreeMinBisection` (both directions + 3-regularity). -/
theorem toThreeMinBisection_mem_iff (x : MinBisectionInstance) :
    toThreeMinBisection x ∈ ThreeMinBisection ↔ x ∈ MinBisection := by
  classical
  unfold toThreeMinBisection
  dsimp only
  set V := x.graph.distinctVertices
  set n := V.length
  by_cases hn0 : n = 0
  · simp only [hn0, beq_self_eq_true, ↓reduceIte]
    refine ⟨fun _ => ?_, fun _ => threeYesInstance_mem⟩
    rw [mem_MinBisection_iff]
    refine ⟨∅, fun _ h => by simp at h, by dsimp only [n, V] at hn0; simp [hn0],
      by
        have hsub : (∅ : Finset ℕ).subtype (· ∈ x.graph.vertices) = ∅ := by
          ext ⟨v, hv⟩; simp
        rw [hsub]
        simp [SimpleGraph.interedges, Rel.interedges]⟩
  · have hn0b : (n == 0) = false := beq_false_of_ne hn0
    by_cases heven : n % 2 = 0
    · have hevenb : (n % 2 == 0) = true := beq_iff_eq.mpr heven
      by_cases hbig : n * n ≤ x.bound
      · simp only [hn0b, hevenb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hbig, decide_true]
        refine ⟨fun _ => ?_, fun _ => threeYesInstance_mem⟩
        rw [mem_MinBisection_iff]
        let half := (List.range (n / 2)).map (fun i => V.getD i 0)
        have hV_nd : V.Nodup := Graph.nodup_distinctVertices x.graph
        have hhalf_nd : half.Nodup := by
          refine List.nodup_range.map_on fun i hi j hj h => ?_
          rw [List.mem_range] at hi hj
          have h1 : V[i] = V[j] := by
            rw [List.getD_eq_getElem _ 0 (by omega : i < n),
                List.getD_eq_getElem _ 0 (by omega : j < n)] at h; exact h
          exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hV_nd)
            (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) h1)
        refine ⟨half.toFinset, fun v hv => ?_, ?_, ?_⟩
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
          rw [List.mem_range] at hi
          exact Graph.mem_distinctVertices.mp (getD_mem_of_lt (by dsimp only [n, V] at hi; omega))
        · rw [List.toFinset_card_of_nodup hhalf_nd, List.length_map, List.length_range]
          dsimp only [n, V] at heven ⊢; omega
        · have hle : (x.graph.induced.interedges
              (half.toFinset.subtype (· ∈ x.graph.vertices))
              (half.toFinset.subtype (· ∈ x.graph.vertices))ᶜ).card ≤ n * n := by
            have hsub : x.graph.induced.interedges
                (half.toFinset.subtype (· ∈ x.graph.vertices))
                (half.toFinset.subtype (· ∈ x.graph.vertices))ᶜ ⊆ Finset.univ ×ˢ Finset.univ :=
              fun _ _ => by simp
            have := Finset.card_le_card hsub
            rw [Finset.card_product, Finset.card_univ, Graph.card_vertexSubtype,
              ← Graph.length_distinctVertices] at this
            exact this
          omega
      · have hred : (if (n == 0) = true then threeYesInstance
          else if (!(n % 2 == 0)) = true then threeNoInstance
          else if decide (n * n ≤ x.bound) = true then threeYesInstance
          else ⟨⟨List.range (4 * (4 * n * n + 8) * (4 * n * n + 8) * n),
            ((List.range n).flatMap fun u => torusGadgetEdges (4 * n * n + 8) u
              ((List.range n).filter fun v =>
                x.graph.adjBool (V.getD u 0) (V.getD v 0)).length)
            ++ ((List.range n).flatMap fun u =>
              ((List.range n).filter fun v =>
                decide (u < v) && x.graph.adjBool (V.getD u 0) (V.getD v 0)).flatMap
                fun v =>
                  let nbrs := fun w => (List.range n).filter fun z =>
                    x.graph.adjBool (V.getD w 0) (V.getD z 0)
                  let i := (nbrs u).idxOf v
                  let j := (nbrs v).idxOf u
                  [(torusVid (4 * n * n + 8) u i i 0,
                    torusVid (4 * n * n + 8) v j j 0),
                   (torusVid (4 * n * n + 8) u i i 1,
                    torusVid (4 * n * n + 8) v j j 1)])⟩,
            2 * x.bound⟩) = ⟨torusReductionGraph x.graph, 2 * x.bound⟩ := by
          simp only [hn0b, hevenb, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            decide_eq_false hbig, torusReductionGraph]
          dsimp only [n, V]
        rw [hred]
        exact ⟨torusReductionGraph_backward x hbig, torusReductionGraph_forward x⟩
    · have hodd : (n % 2 == 0) = false := beq_false_of_ne heven
      simp only [hn0b, hodd, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun h => absurd h threeNoInstance_notMem, fun h => ?_⟩
      obtain ⟨S, _, hcard, _⟩ := (mem_MinBisection_iff x).mp h
      dsimp only [n, V] at heven; omega

theorem polyTimeReducible_MinBisection_ThreeMinBisection :
    PolyTimeReducible encMinBisection encMinBisection MinBisection ThreeMinBisection :=
  ⟨toThreeMinBisection, computableInPolyTime_toThreeMinBisection,
    fun x => (toThreeMinBisection_mem_iff x).symm⟩

end MinBisection

/-- Cubic Minimum Bisection (`ThreeMinBisection`) is `NP`-complete. -/
theorem ThreeMinBisection_npComplete : NPComplete encMinBisection ThreeMinBisection :=
  ⟨MinBisection.threeMinBisection_mem_NP,
    MinBisection_npComplete.2.trans MinBisection.polyTimeReducible_MinBisection_ThreeMinBisection⟩

end CslibFrontier.Complexity
