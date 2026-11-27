/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.AnyEndpoints
public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.Undirected
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Undirected Hamiltonian Path Without Fixed Endpoints

Complements `Cslib.Complexity.DirHamPathAny` (`AnyEndpoints.lean`) and fixed-endpoint undirected
`Cslib.Complexity.HamPath` (`Undirected.lean`) with undirected Hamiltonian path between unspecified
endpoints (`Cslib.Complexity.HamPathAny`). Shifting all vertex labels by `2` and attaching two
degree-`1` pendant vertices `0 — s + 2` and `t + 2 — 1` (with the `s = t` edge case handled
directly) reduces `HamPath` to `HamPathAny` in polynomial time.

## Main definitions

* `Cslib.Complexity.HamPathAny`: finite undirected graphs admitting a Hamiltonian path between some
  pair of endpoints.
* `Cslib.Complexity.HamPathAny.verifier`: polynomial-time verifier.
* `Cslib.Complexity.HamPath.toAny`: polynomial-time reduction from `HamPath` to `HamPathAny`.

## Main results

* `Cslib.Complexity.HamPathAny.mem_NP`: `HamPathAny ∈ NP encGraph`.
* `Cslib.Complexity.polyTimeReducible_HamPath_HamPathAny`: `HamPath ≤ₚ HamPathAny`.
* `Cslib.Complexity.HamPathAny_npHard`, `Cslib.Complexity.HamPathAny_npComplete`: `HamPathAny` is
  `NP`-hard and `NP`-complete.
-/

public section

namespace Cslib.Complexity

open Function Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Undirected graphs (given by vertex and edge lists) admitting a simple path through all declared
vertices between some unspecified endpoints. Empty graphs are excluded. -/
@[expose] def HamPathAny : Set Graph :=
  {G | ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ G.vertices) ∧ p ≠ [] ∧
    p.IsChain G.toSimpleGraph.Adj}

/-- `G ∈ HamPathAny` iff `⟨G, s, t⟩ ∈ HamPath` for some endpoints `s, t`. -/
theorem mem_HamPathAny_iff {G : Graph} :
    G ∈ HamPathAny ↔ ∃ s t : ℕ, (⟨G, s, t⟩ : PathInstance) ∈ HamPath := by
  simp_rw [mem_HamPath_iff]
  constructor
  · rintro ⟨p, hnd, hcov, hne, hch⟩
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨a, _, _, hnd, hcov, rfl, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hch⟩
  · rintro ⟨s, t, p, hnd, hcov, hs, -, hch⟩
    exact ⟨p, hnd, hcov, by rintro rfl; simp at hs, hch⟩

/-- Polynomial-time certificate verifier for `HamPathAny`. -/
def HamPathAny.verifier : Graph × List Bool → Bool :=
  Graph.verifyOrdering (fun G => G.vertices) fun G p =>
    decide (p ≠ []) && Graph.chainBool G.adjBool p

/-- `HamPathAny.verifier` verifies `HamPathAny` with quadratic witness length bound. -/
theorem HamPathAny.isVerifier : IsVerifier encGraph (Polynomial.X ^ 2) verifier HamPathAny :=
  Graph.isVerifier_verifyOrdering
    (P := fun (G : Graph) p => p ≠ [] ∧ p.IsChain G.toSimpleGraph.Adj)
    Graph.length_vertices_le_encGraph fun G p => by
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        Graph.chainBool_eq_true_iff (Graph.adjBool_eq_true_iff G)]

/-- `HamPathAny.verifier` runs in polynomial time. -/
theorem HamPathAny.computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encGraph encBits) encBool := by
  have hproj : ComputableInPolyTime
      (fun q : ((Graph × List ℕ) × ℕ) × ℕ => ((q.1.1.1, q.1.2), q.2))
      (encPair (encPair (encPair encGraph (encList encNat)) encNat) encNat)
      (encPair (encPair encGraph encNat) encNat) := by
    fun_prop
  unfold verifier
  refine Graph.computableInPolyTime_verifyOrdering (by unfold encGraph; fun_prop)
    (bool_and' ?_ (Graph.computableInPolyTime_chainBool
      (Graph.computableInPolyTime_adjBool.comp hproj) (snd _ _)))
  simpa only [Function.comp_def, _root_.decide_not] using
    bool_not.comp ((snd _ _).decide_eq' (const []))

/-- `HamPathAny` lies in `NP`. -/
theorem HamPathAny.mem_NP : HamPathAny ∈ NP encGraph :=
  ⟨Polynomial.X ^ 2, verifier, computableInPolyTime_verifier, isVerifier⟩

private theorem exists_adj_of_mem_internal {R : ℕ → ℕ → Prop} :
    ∀ {p : List ℕ}, p.IsChain R → ∀ {x}, x ∈ p.tail.dropLast → ∃ y z, R y x ∧ R x z
  | [], _, _, hx => by simp at hx
  | [_], _, _, hx => by simp at hx
  | [_, _], _, _, hx => by simp at hx
  | a :: b :: c :: l, h, x, hx => by
    rw [List.isChain_cons_cons] at h
    have hbc := (List.isChain_cons_cons.mp h.2).1
    simp only [List.tail_cons, List.dropLast_cons_of_ne_nil (List.cons_ne_nil c l),
      List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨a, c, h.1, hbc⟩
    · exact exists_adj_of_mem_internal h.2 hx

/-- Two-pendant-vertex polynomial-time reduction from fixed-endpoint `HamPath` to `HamPathAny`. -/
def HamPath.toAny (x : PathInstance) : Graph :=
  if x.source = x.target then
    if x.graph.distinctVertices = [x.source] then ⟨[0], []⟩
    else ⟨[0, 1], []⟩
  else
    DirHamPath.toAny x

private theorem adj_dirToAny_zero_iff {x : PathInstance} {w : ℕ} :
    (DirHamPath.toAny x).toSimpleGraph.Adj 0 w ↔ w = x.source + 2 := by
  rw [Graph.toSimpleGraph_adj]
  simp only [DirHamPath.toAny, List.mem_cons, Prod.mk.injEq, List.mem_map]
  constructor
  · rintro ⟨_, (⟨-, hw⟩ | ⟨h, -⟩ | ⟨_, -, h, -⟩) | (⟨h, -⟩ | ⟨-, h⟩ | ⟨_, -, -, h⟩)⟩ <;> omega
  · rintro rfl; exact ⟨by omega, Or.inl (Or.inl ⟨trivial, rfl⟩)⟩

private theorem adj_dirToAny_one_iff {x : PathInstance} {w : ℕ} :
    (DirHamPath.toAny x).toSimpleGraph.Adj 1 w ↔ w = x.target + 2 := by
  rw [Graph.toSimpleGraph_adj]
  simp only [DirHamPath.toAny, List.mem_cons, Prod.mk.injEq, List.mem_map]
  constructor
  · rintro ⟨_, (⟨h, -⟩ | ⟨h, -⟩ | ⟨_, -, h, -⟩) | (⟨-, h⟩ | ⟨hw, -⟩ | ⟨_, -, -, h⟩)⟩ <;> omega
  · rintro rfl; exact ⟨by omega, Or.inr (Or.inr (Or.inl ⟨rfl, trivial⟩))⟩

private theorem adj_dirToAny_shift_iff {x : PathInstance} {a b : ℕ} :
    (DirHamPath.toAny x).toSimpleGraph.Adj (a + 2) (b + 2) ↔
      x.graph.toSimpleGraph.Adj a b := by
  rw [Graph.toSimpleGraph_adj, Graph.toSimpleGraph_adj]
  simp only [DirHamPath.toAny, List.mem_cons, Prod.mk.injEq, List.mem_map]
  constructor
  · rintro ⟨_, (⟨h, -⟩ | ⟨-, h⟩ | ⟨⟨u, v⟩, he, hu, hv⟩) |
      (⟨h, -⟩ | ⟨-, h⟩ | ⟨⟨u, v⟩, he, hu, hv⟩)⟩ <;> try omega
    · obtain rfl : u = a := by omega
      obtain rfl : v = b := by omega
      exact ⟨by omega, Or.inl he⟩
    · obtain rfl : u = b := by omega
      obtain rfl : v = a := by omega
      exact ⟨by omega, Or.inr he⟩
  · rintro ⟨hne, he | he⟩
    · exact ⟨by omega, Or.inl (Or.inr (Or.inr ⟨(a, b), he, rfl, rfl⟩))⟩
    · exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨(b, a), he, rfl, rfl⟩))⟩

/-- `HamPath.toAny x ∈ HamPathAny ↔ x ∈ HamPath`. -/
theorem HamPath.toAny_mem_iff (x : PathInstance) :
    HamPath.toAny x ∈ HamPathAny ↔ x ∈ HamPath := by
  obtain ⟨G, s, t⟩ := x
  rw [mem_HamPath_iff]
  unfold HamPath.toAny
  dsimp only
  by_cases hst : s = t
  · subst hst
    rw [ite_eq_left_iff.mpr fun h => (h rfl).elim]
    by_cases hsingle : G.distinctVertices = [s]
    · rw [ite_eq_left_iff.mpr fun h => (h hsingle).elim]
      have hmem : ∀ v, v ∈ G.vertices ↔ v = s := fun v => by
        rw [← Graph.mem_distinctVertices, hsingle, List.mem_singleton]
      refine ⟨fun _ => ⟨[s], List.nodup_singleton s, fun v => by simp [hmem v],
        rfl, rfl, List.isChain_singleton s⟩,
        fun _ => ⟨[0], List.nodup_singleton 0, by simp, List.cons_ne_nil _ _,
          List.isChain_singleton 0⟩⟩
    · rw [ite_eq_right_iff.mpr fun h => (hsingle h).elim]
      constructor
      · rintro ⟨p, _, hcov, hne, hch⟩
        have h0 : 0 ∈ p := (hcov 0).2 (by simp)
        have h1 : 1 ∈ p := (hcov 1).2 (by simp)
        rcases p with _ | ⟨a, _ | ⟨b, l⟩⟩
        · exact absurd rfl hne
        · simp at h0 h1; omega
        · have hab := (List.isChain_cons_cons.mp hch).1
          rw [Graph.toSimpleGraph_adj] at hab; simp at hab
      · rintro ⟨p, hnd, hcov, hs, ht, -⟩
        rcases p with _ | ⟨a, _ | ⟨b, l⟩⟩
        · simp at hs
        · simp only [List.head?_cons, Option.some.injEq] at hs
          subst hs
          have hall : ∀ v ∈ G.distinctVertices, v = a := fun v hv => by
            simpa using (hcov v).2 (Graph.mem_distinctVertices.1 hv)
          have hne_d : G.distinctVertices ≠ [] := by
            intro h
            have : a ∈ G.distinctVertices := Graph.mem_distinctVertices.2 ((hcov a).1 (by simp))
            simp [h] at this
          rcases hd : G.distinctVertices with _ | ⟨u, _ | ⟨w, ws⟩⟩
          · exact (hne_d hd).elim
          · exact (hsingle (hd.trans (by rw [hall u (by simp [hd])]))).elim
          · have hu : u = a := hall u (by simp [hd])
            have hw : w = a := hall w (by simp [hd])
            have hnd_d := G.nodup_distinctVertices
            rw [hd, hu, hw] at hnd_d; simp at hnd_d
        · simp only [List.head?_cons, Option.some.injEq] at hs
          subst hs
          have hlast : (b :: l).getLast (List.cons_ne_nil _ _) = a := by
            rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _),
              Option.some.injEq] at ht
            exact ht
          exact ((List.nodup_cons.1 hnd).1 (hlast ▸ List.getLast_mem (List.cons_ne_nil b l))).elim
  · rw [ite_eq_right_iff.mpr fun h => (hst h).elim]
    have hshift : Injective (· + 2 : ℕ → ℕ) := fun _ _ h => by dsimp at h; omega
    constructor
    · rintro ⟨p, hnd, hcov, hne, hch⟩
      have hno_int_0 : 0 ∉ p.tail.dropLast := fun h0 => by
        obtain ⟨k, hk, hget⟩ := List.getElem_of_mem h0
        have hk' : k + 2 < p.length := by
          simp only [List.length_dropLast, List.length_tail] at hk; omega
        have hp_k1 : p[k + 1]'(by omega) = 0 := by
          simpa [List.getElem_dropLast, List.getElem_tail] using hget
        have hprev : p[k]'(by omega) = s + 2 := by
          have h1 := List.isChain_iff_getElem.1 hch k (by omega)
          rw [hp_k1] at h1
          exact adj_dirToAny_zero_iff.1 h1.symm
        have hnext : p[k + 2]'hk' = s + 2 := by
          have h2 := List.isChain_iff_getElem.1 hch (k + 1) (by omega)
          rw [hp_k1] at h2
          exact adj_dirToAny_zero_iff.1 h2
        have := (List.Nodup.getElem_inj_iff hnd).1 (hprev.trans hnext.symm); omega
      have hno_int_1 : 1 ∉ p.tail.dropLast := fun h1 => by
        obtain ⟨k, hk, hget⟩ := List.getElem_of_mem h1
        have hk' : k + 2 < p.length := by
          simp only [List.length_dropLast, List.length_tail] at hk; omega
        have hp_k1 : p[k + 1]'(by omega) = 1 := by
          simpa [List.getElem_dropLast, List.getElem_tail] using hget
        have hprev : p[k]'(by omega) = t + 2 := by
          have h1 := List.isChain_iff_getElem.1 hch k (by omega)
          rw [hp_k1] at h1
          exact adj_dirToAny_one_iff.1 h1.symm
        have hnext : p[k + 2]'hk' = t + 2 := by
          have h2 := List.isChain_iff_getElem.1 hch (k + 1) (by omega)
          rw [hp_k1] at h2
          exact adj_dirToAny_one_iff.1 h2
        have := (List.Nodup.getElem_inj_iff hnd).1 (hprev.trans hnext.symm); omega
      have hendpt : ∀ u ∈ p, u ∉ p.tail.dropLast → u = p.head hne ∨ u = p.getLast hne := by
        intro u hu hni
        rcases p with _ | ⟨a, rest⟩
        · exact absurd rfl hne
        rcases List.mem_cons.1 hu with rfl | hrest
        · exact Or.inl rfl
        · have hrne : rest ≠ [] := List.ne_nil_of_mem hrest
          rw [← List.dropLast_append_getLast hrne, List.mem_append, List.mem_singleton] at hrest
          rcases hrest with hdl | rfl
          · exact absurd hdl hni
          · exact Or.inr (List.getLast_cons hrne).symm
      have extract : ∀ q : List ℕ, q.Nodup →
          (∀ v, v ∈ q ↔ v ∈ (DirHamPath.toAny ⟨G, s, t⟩).vertices) →
          (hq : q ≠ []) → q.IsChain (DirHamPath.toAny ⟨G, s, t⟩).toSimpleGraph.Adj →
          q.head hq = 0 → q.getLast hq = 1 →
          ∃ r : List ℕ, r.Nodup ∧ (∀ v, v ∈ r ↔ v ∈ G.vertices) ∧
            r.head? = some s ∧ r.getLast? = some t ∧ r.IsChain G.toSimpleGraph.Adj := by
        intro q hqnd hqcov hqne hqch hq0 hq1
        rcases q with _ | ⟨a, rest⟩
        · exact absurd rfl hqne
        simp only [List.head_cons] at hq0; subst hq0
        have hrne : rest ≠ [] := by rintro rfl; simp at hq1
        have hrlast : rest.getLast hrne = 1 := by simpa [List.getLast_cons hrne] using hq1
        let m := rest.dropLast
        have hrest_eq : rest = m ++ [1] := by
          rw [← hrlast]; exact (List.dropLast_append_getLast hrne).symm
        rw [hrest_eq] at hqnd hqcov hqch
        have hqnd' := hqnd
        rw [List.nodup_cons, List.mem_append, not_or, List.nodup_append] at hqnd'
        have hm2 : ∀ v ∈ m, 2 ≤ v := fun v hv => by
          have hv0 : v ≠ 0 := by rintro rfl; exact hqnd'.1.1 hv
          have hv1 : v ≠ 1 := by rintro rfl; exact hqnd'.2.2.2 1 hv 1 (by simp) rfl
          omega
        let r := m.map (· - 2)
        have hm_eq : m = r.map (· + 2) := by
          simpa [r, List.map_map, Function.comp_def] using
            List.map_congr_left fun v hv => (Nat.sub_add_cancel (hm2 v hv)).symm
        rw [hm_eq] at hqnd' hqcov hqch
        have hr_ne : r ≠ [] := fun hr0 => by
          rw [hr0] at hqch
          simp only [List.map_nil, List.nil_append, List.isChain_cons_cons] at hqch
          have := adj_dirToAny_zero_iff.1 hqch.1; omega
        rw [← List.singleton_append, ← List.append_assoc, List.isChain_append,
          List.isChain_append] at hqch
        obtain ⟨⟨-, hmid, hfirst⟩, -, hlast⟩ := hqch
        refine ⟨r, (List.nodup_map_iff hshift).1 hqnd'.2.1, fun v => ?_, ?_, ?_, ?_⟩
        · have hc := hqcov (v + 2)
          simp only [DirHamPath.toAny, List.mem_cons, List.mem_append, List.mem_map,
            hshift.eq_iff, exists_eq_right] at hc
          simpa [show v + 2 ≠ 0 by omega, show v + 2 ≠ 1 by omega] using hc
        · obtain ⟨u, us, hru⟩ := List.exists_cons_of_ne_nil hr_ne
          rw [hru] at hfirst ⊢
          have hf := adj_dirToAny_zero_iff.1 (hfirst 0 (by simp) (u + 2) (by simp))
          dsimp at hf; simp; omega
        · have hl := adj_dirToAny_one_iff.1
            (hlast (r.getLast hr_ne + 2) (by
              rw [Option.mem_def, List.getLast?_append_of_ne_nil _ (by simpa using hr_ne),
                List.getLast?_map, List.getLast?_eq_some_getLast hr_ne]; rfl) 1 (by simp)).symm
          dsimp at hl
          rw [List.getLast?_eq_some_getLast hr_ne, Option.some.injEq]; omega
        · rw [List.isChain_map] at hmid
          exact hmid.imp fun _ _ h => adj_dirToAny_shift_iff.1 h
      have h0m : 0 ∈ p := (hcov 0).2 (by simp [DirHamPath.toAny])
      have h1m : 1 ∈ p := (hcov 1).2 (by simp [DirHamPath.toAny])
      rcases hendpt 0 h0m hno_int_0 with h0h | h0l <;>
        rcases hendpt 1 h1m hno_int_1 with h1h | h1l
      · omega
      · exact extract p hnd hcov hne hch h0h.symm h1l.symm
      · have hrne : p.reverse ≠ [] := by simpa using hne
        exact extract p.reverse (List.nodup_reverse.2 hnd) (by simpa using hcov) hrne
          (List.isChain_reverse.2 (hch.imp fun _ _ h => h.symm))
          (by rw [List.head_reverse]; exact h0l.symm)
          (by rw [List.getLast_reverse]; exact h1h.symm)
      · omega
    · rintro ⟨q, hnd, hcov, hs, ht, hch⟩
      have hq : q ≠ [] := by rintro rfl; simp at hs
      refine ⟨0 :: (q.map (· + 2) ++ [1]), ?_, fun v => ?_, List.cons_ne_nil _ _, ?_⟩
      · refine List.nodup_cons.2 ⟨?_, List.nodup_append.2
          ⟨(List.nodup_map_iff hshift).2 hnd, List.nodup_singleton 1, ?_⟩⟩
        · rw [List.mem_append, List.mem_singleton, List.mem_map]
          rintro (⟨_, _, h⟩ | h) <;> omega
        · intro a ha b hb
          obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha
          rw [List.mem_singleton] at hb; omega
      · simp only [DirHamPath.toAny, List.mem_cons, List.mem_append, List.mem_map, hcov,
          List.not_mem_nil, or_false]
        exact or_congr_right or_comm
      · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hq
        simp only [List.head?_cons, Option.some.injEq] at hs; subst hs
        rw [← List.singleton_append, ← List.append_assoc, List.isChain_append, List.isChain_append]
        refine ⟨⟨List.isChain_singleton 0, ?_, ?_⟩, List.isChain_singleton 1, ?_⟩
        · rw [List.isChain_map]; exact hch.imp fun _ _ h => adj_dirToAny_shift_iff.2 h
        · intro u hu v hv
          simp only [List.getLast?_singleton, List.map_cons, List.head?_cons, Option.mem_def,
            Option.some.injEq] at hu hv
          subst hu hv; exact adj_dirToAny_zero_iff.2 rfl
        · intro u hu v hv
          rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_map, ht] at hu
          simp only [Option.map_some, List.head?_cons, Option.mem_def, Option.some.injEq] at hu hv
          subst hu hv
          exact (adj_dirToAny_one_iff.2 rfl).symm

/-- `HamPath.toAny` runs in polynomial time. -/
theorem HamPath.computableInPolyTime_toAny :
    ComputableInPolyTime HamPath.toAny encPathInstance encGraph := by
  have hc1 : ComputableInPolyTime (fun x : PathInstance => decide (x.source = x.target))
      encPathInstance encBool := by fun_prop
  have hsingle : ComputableInPolyTime (fun x : PathInstance => [x.source])
      encPathInstance (encList encNat) := by fun_prop
  have hdist : ComputableInPolyTime (fun x : PathInstance => x.graph.distinctVertices)
      encPathInstance (encList encNat) := by fun_prop
  have hc2 : ComputableInPolyTime
      (fun x : PathInstance => decide (x.graph.distinctVertices = [x.source]))
      encPathInstance encBool := hdist.decide_eq' hsingle
  exact (ite' hc1 (ite' hc2 (const ⟨[0], []⟩) (const ⟨[0, 1], []⟩))
    DirHamPath.computableInPolyTime_toAny).of_enc_eq fun x =>
      congrArg encGraph (by simp only [HamPath.toAny, decide_eq_true_eq])

/-- `HamPath` reduces in polynomial time to `HamPathAny`. -/
theorem polyTimeReducible_HamPath_HamPathAny :
    PolyTimeReducible encPathInstance encGraph HamPath HamPathAny :=
  ⟨HamPath.toAny, HamPath.computableInPolyTime_toAny, fun x => (HamPath.toAny_mem_iff x).symm⟩

/-- **Undirected Hamiltonian path without fixed endpoints is `NP`-hard.** -/
theorem HamPathAny_npHard : NPHard encGraph HamPathAny :=
  HamPath_npHard.trans polyTimeReducible_HamPath_HamPathAny

/-- **Undirected Hamiltonian path without fixed endpoints is `NP`-complete.** -/
theorem HamPathAny_npComplete : NPComplete encGraph HamPathAny :=
  ⟨HamPathAny.mem_NP, HamPathAny_npHard⟩

end Cslib.Complexity
