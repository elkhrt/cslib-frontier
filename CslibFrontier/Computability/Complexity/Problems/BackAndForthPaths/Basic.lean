/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Problems.Graph.DirectedCycle
public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian

import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Tactic.EncLen

/-!
# Back-and-Forth Paths (`BFP`) — Definition and `NP` Membership

Defines the Back-and-Forth Paths problem (`Cslib.Complexity.BFP`) on directed graphs (two openly
vertex-disjoint directed paths `s → t` and `t → s` between distinct vertices `s ≠ t`), proves its
equivalence with simple directed cycles through both terminals (`mem_BFP_iff_exists_isDirCycle`),
and proves `BFP ∈ NP encPathInstance` (`BFP_mem_NP`).

## Main definitions

* `Cslib.Complexity.IsDirPath`: simple directed path from `s` to `t` in a `Graph`.
* `Cslib.Complexity.BFP`: the Back-and-Forth Paths decision problem on `PathInstance`.

## Main results

* `Cslib.Complexity.mem_BFP_iff_exists_isDirCycle`: equivalence with directed cycles through both
  terminals.
* `Cslib.Complexity.BFP_mem_NP`: `BFP ∈ NP encPathInstance`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- `p` is a simple directed path from `s` to `t` in the directed graph `G`: a duplicate-free
nonempty list of declared vertices starting at `s`, ending at `t`, with consecutive arcs in
`G.edges`. -/
@[expose] def IsDirPath (G : Graph) (s t : ℕ) (p : List ℕ) : Prop :=
  p.Nodup ∧ (∀ v ∈ p, v ∈ G.vertices) ∧ p.head? = some s ∧ p.getLast? = some t ∧
    p.IsChain fun u v ↦ (u, v) ∈ G.edges

/-- **Back-and-Forth Paths (`BFP`)**: directed graphs with two distinct vertices `s, t` admitting
two openly disjoint directed paths, one from `s` to `t` and one from `t` to `s`. -/
@[expose] def BFP : Set PathInstance :=
  {x | x.source ≠ x.target ∧
    ∃ p q : List ℕ, IsDirPath x.graph x.source x.target p ∧
      IsDirPath x.graph x.target x.source q ∧
      ∀ v : ℕ, v ∈ p → v ∈ q → v = x.source ∨ v = x.target}

private lemma exists_rotated_cons {q : List ℕ} {s : ℕ} (hs : s ∈ q) :
    ∃ rest : List ℕ, (q : Cycle ℕ) = (s :: rest : List ℕ) ∧ (s :: rest).Nodup = q.Nodup ∧
      ∀ v, v ∈ s :: rest ↔ v ∈ q := by
  have hlt : q.idxOf s < q.length := List.idxOf_lt_length_iff.mpr hs
  have hrot : q.rotate (q.idxOf s) = s :: (q.drop (q.idxOf s + 1) ++ q.take (q.idxOf s)) := by
    rw [List.rotate_eq_drop_append_take hlt.le, List.drop_eq_getElem_cons hlt,
      List.getElem_idxOf hlt, List.cons_append]
  refine ⟨q.drop (q.idxOf s + 1) ++ q.take (q.idxOf s), ?_, ?_, fun v ↦ ?_⟩
  · rw [← hrot]; exact Cycle.coe_eq_coe.mpr ⟨_, rfl⟩
  · rw [← hrot]; exact propext List.nodup_rotate
  · rw [← hrot]; exact List.mem_rotate

/-- A `PathInstance` belongs to `BFP` if and only if `source ≠ target` and the digraph contains a
simple directed cycle passing through both `source` and `target`. -/
theorem mem_BFP_iff_exists_isDirCycle {x : PathInstance} :
    x ∈ BFP ↔ x.source ≠ x.target ∧
      ∃ c : List ℕ, x.graph.IsDirCycle c ∧ x.source ∈ c ∧ x.target ∈ c := by
  constructor
  · rintro ⟨hst, p, q, hp, hq, hdisj⟩
    rcases hp with ⟨hp_nd, hp_V, hp_hd, hp_lst, hp_ch⟩
    rcases hq with ⟨hq_nd, hq_V, hq_hd, hq_lst, hq_ch⟩
    have hp_ne : p ≠ [] := by rintro rfl; simp at hp_hd
    have hq_ne : q ≠ [] := by rintro rfl; simp at hq_hd
    have hp_eq : p = p.dropLast ++ [x.target] := by
      conv_lhs => rw [← List.dropLast_append_getLast hp_ne]
      rw [List.getLast?_eq_some_getLast hp_ne] at hp_lst
      rw [Option.some.inj hp_lst]
    have hq_eq : q = q.dropLast ++ [x.source] := by
      conv_lhs => rw [← List.dropLast_append_getLast hq_ne]
      rw [List.getLast?_eq_some_getLast hq_ne] at hq_lst
      rw [Option.some.inj hq_lst]
    have hp_dl_ne : p.dropLast ≠ [] := by
      intro h
      rw [h, List.nil_append] at hp_eq
      rw [hp_eq] at hp_hd
      exact hst (Option.some.inj hp_hd).symm
    have hq_dl_ne : q.dropLast ≠ [] := by
      intro h
      rw [h, List.nil_append] at hq_eq
      rw [hq_eq] at hq_hd
      exact hst (Option.some.inj hq_hd)
    have hpd_nd : p.dropLast.Nodup := (hp_eq ▸ hp_nd).of_append_left
    have hqd_nd : q.dropLast.Nodup := (hq_eq ▸ hq_nd).of_append_left
    have ht_not_pd : x.target ∉ p.dropLast := by
      have hnd := hp_eq ▸ hp_nd
      rw [List.nodup_append] at hnd
      intro ht; exact hnd.2.2 x.target ht x.target (List.mem_singleton_self _) rfl
    have hs_not_qd : x.source ∉ q.dropLast := by
      have hnd := hq_eq ▸ hq_nd
      rw [List.nodup_append] at hnd
      intro hs; exact hnd.2.2 x.source hs x.source (List.mem_singleton_self _) rfl
    have hs_pd : x.source ∈ p.dropLast := by
      have hs_p : x.source ∈ p := List.mem_of_head? hp_hd
      rw [hp_eq, List.mem_append, List.mem_singleton] at hs_p
      exact hs_p.resolve_right hst
    have ht_qd : x.target ∈ q.dropLast := by
      have ht_q : x.target ∈ q := List.mem_of_head? hq_hd
      rw [hq_eq, List.mem_append, List.mem_singleton] at ht_q
      exact ht_q.resolve_right hst.symm
    let c : List ℕ := p.dropLast ++ q.dropLast
    refine ⟨hst, c, ⟨by simp [c, hp_dl_ne], ?_, ?_, ?_⟩,
      List.mem_append_left _ hs_pd, List.mem_append_right _ ht_qd⟩
    · rw [List.nodup_append]
      refine ⟨hpd_nd, hqd_nd, fun v hv₁ w hv₂ hvw ↦ ?_⟩
      subst hvw
      have hvp : v ∈ p := hp_eq ▸ List.mem_append_left _ hv₁
      have hvq : v ∈ q := hq_eq ▸ List.mem_append_left _ hv₂
      rcases hdisj v hvp hvq with rfl | rfl
      · exact hs_not_qd hv₂
      · exact ht_not_pd hv₁
    · intro v hv
      rcases List.mem_append.mp hv with hv₁ | hv₂
      · exact hp_V v (hp_eq ▸ List.mem_append_left _ hv₁)
      · exact hq_V v (hq_eq ▸ List.mem_append_left _ hv₂)
    · rw [Cycle.chain_coe_iff_isChain_append_take_one]
      have htake : c.take 1 = [x.source] := by
        cases hpd : p.dropLast with
        | nil => exact absurd hpd hp_dl_ne
        | cons a l =>
          have ha : a = x.source := by
            have : (a :: l ++ [x.target]).head? = some x.source := by
              rw [← hpd, ← hp_eq]; exact hp_hd
            simpa using this
          simp [c, hpd, ha]
      have hconcat : c ++ [x.source] = p.dropLast ++ q := by
        dsimp only [c]; rw [List.append_assoc, ← hq_eq]
      rw [htake, hconcat]
      have hp_dl_ch : p.dropLast.IsChain (fun u v ↦ (u, v) ∈ x.graph.edges) :=
        (List.isChain_append.mp (hp_eq ▸ hp_ch)).1
      refine List.isChain_append.mpr ⟨hp_dl_ch, hq_ch, fun u hu v hv ↦ ?_⟩
      have hlast_p := (List.isChain_append.mp (hp_eq ▸ hp_ch)).2.2 u hu x.target rfl
      rw [hq_hd] at hv
      rw [Option.mem_def, Option.some.injEq] at hv
      exact hv ▸ hlast_p
  · rintro ⟨hst, c, ⟨hc_ne, hc_nd, hc_V, hc_ch⟩, hs_c, ht_c⟩
    obtain ⟨rest, hc_eq, hnd_eq, hmem_eq⟩ := exists_rotated_cons hs_c
    have hnd' : (x.source :: rest).Nodup := hnd_eq ▸ hc_nd
    rw [hc_eq, Cycle.chain_coe_cons] at hc_ch
    have ht_rest : x.target ∈ rest := by
      have := (hmem_eq x.target).mpr ht_c
      exact (List.mem_cons.mp this).resolve_left hst.symm
    obtain ⟨r₁, r₂, rfl⟩ := List.append_of_mem ht_rest
    let p : List ℕ := x.source :: r₁ ++ [x.target]
    let q : List ℕ := x.target :: r₂ ++ [x.source]
    have hch_all : (x.source :: (r₁ ++ x.target :: r₂) ++ [x.source]).IsChain
        (fun u v ↦ (u, v) ∈ x.graph.edges) := hc_ch
    have hsplit_eq : x.source :: (r₁ ++ x.target :: r₂) ++ [x.source] =
        (x.source :: r₁) ++ (x.target :: r₂ ++ [x.source]) := by
      simp [List.append_assoc]
    rw [hsplit_eq] at hch_all
    have hch_parts := List.isChain_append.mp hch_all
    have hp_ch : p.IsChain (fun u v ↦ (u, v) ∈ x.graph.edges) := by
      refine List.isChain_append.mpr ⟨hch_parts.1, List.IsChain.singleton _, fun u hu v hv ↦ ?_⟩
      have hlast := hch_parts.2.2 u hu x.target rfl
      rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
      exact hv ▸ hlast
    have hq_ch : q.IsChain (fun u v ↦ (u, v) ∈ x.graph.edges) := hch_parts.2.1
    have hp_nd : p.Nodup := by
      have hsub : p.Sublist (x.source :: (r₁ ++ x.target :: r₂)) := by
        simp [p]
      exact hnd'.sublist hsub
    have hq_nd : q.Nodup := by
      have hnd_tail : (x.target :: r₂).Nodup :=
        (List.nodup_append.mp (List.nodup_cons.mp hnd').2).2.1
      have hs_not : x.source ∉ x.target :: r₂ := fun h ↦
        (List.nodup_cons.mp hnd').1 (List.mem_append_right r₁ h)
      rw [show q = (x.target :: r₂) ++ [x.source] from rfl, List.nodup_append]
      exact ⟨hnd_tail, List.nodup_singleton _, fun u hu v hv huv ↦ by
        simp only [List.mem_singleton] at hv; subst hv; subst huv; exact hs_not hu⟩
    refine ⟨hst, p, q,
      ⟨hp_nd, fun v hv ↦ hc_V v ((hmem_eq v).mp ?_), rfl,
        by exact List.getLast?_concat, hp_ch⟩,
      ⟨hq_nd, fun v hv ↦ hc_V v ((hmem_eq v).mp ?_), rfl,
        by exact List.getLast?_concat, hq_ch⟩,
      fun v hvp hvq ↦ ?_⟩
    · simp only [p, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hv ⊢
      tauto
    · simp only [q, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hv ⊢
      tauto
    · by_contra hne
      push Not at hne
      have hv_r1 : v ∈ r₁ := by
        simp only [p, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hvp
        rcases hvp with rfl | h | rfl
        · exact absurd rfl hne.1
        · exact h
        · exact absurd rfl hne.2
      have hv_r2 : v ∈ r₂ := by
        simp only [q, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hvq
        rcases hvq with rfl | h | rfl
        · exact absurd rfl hne.2
        · exact h
        · exact absurd rfl hne.1
      have hnd_mid := List.nodup_append.mp (List.nodup_cons.mp hnd').2
      exact hnd_mid.2.2 v hv_r1 v (List.mem_cons_of_mem _ hv_r2) rfl

/-- Encoding length of a duplicate-free sublist of `V` is bounded by the encoding length of `V`. -/
theorem length_encList_le_of_nodup_subset {c V : List ℕ}
    (hc : c.Nodup) (hsub : ∀ v ∈ c, v ∈ V) :
    (encList encNat c).length ≤ (encList encNat V).length := by
  have hlen : ∀ l : List ℕ, (encList encNat l).length =
      (l.map fun a ↦ (frame (encNat a)).length).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [encList_cons, ih]
  rw [hlen c, hlen V]
  have hsp : c.Subperm V := hc.subperm hsub
  obtain ⟨l', hl'perm, hl'sub⟩ := List.subperm_iff.mp hsp
  have h1 : (l'.map fun a ↦ (frame (encNat a)).length).sum =
      (V.map fun a ↦ (frame (encNat a)).length).sum := (hl'perm.map _).sum_eq
  rw [← h1]
  exact List.Sublist.sum_le_sum (hl'sub.map _) (fun _ _ ↦ Nat.zero_le _)

private def bfpCheck (q : PathInstance × List ℕ) : Bool :=
  let x := q.1
  let c := q.2
  decide (x.source ≠ x.target) &&
    decide (c ≠ []) &&
    (c.zipIdx.all fun e ↦ decide (c.idxOf e.1 = e.2)) &&
    (c.all fun v ↦ x.graph.vertices.any fun u ↦ decide (u = v)) &&
    (c.any fun v ↦ decide (v = x.source)) &&
    (c.any fun v ↦ decide (v = x.target)) &&
    Graph.cycleChainBool x.graph.arcBool c

private lemma bfpCheck_eq_true_iff (x : PathInstance) (c : List ℕ) :
    bfpCheck (x, c) = true ↔
      x.source ≠ x.target ∧ x.graph.IsDirCycle c ∧ x.source ∈ c ∧ x.target ∈ c := by
  have hnodup : (∀ e ∈ c.zipIdx, c.idxOf e.1 = e.2) ↔ c.Nodup := by
    constructor
    · intro h
      rw [List.nodup_iff_injective_get]
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [List.get_eq_getElem] at hij
      have hi' := h (c[i], i) (List.mem_zipIdx_iff_getElem?.mpr (by simp))
      have hj' := h (c[j], j) (List.mem_zipIdx_iff_getElem?.mpr (by simp))
      rw [hij] at hi'
      exact Fin.ext (hi'.symm.trans hj')
    · intro hnd e he
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
      rw [← heq, hnd.idxOf_getElem]
  simp only [bfpCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    hnodup, Graph.cycleChainBool_eq_true_iff (Graph.arcBool_eq_true_iff x.graph),
    Graph.IsDirCycle]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨hst, hne⟩, hnd⟩, hV⟩, hs⟩, ht⟩, hch⟩
    refine ⟨hst, ⟨hne, hnd, fun v hv ↦ ?_, hch⟩, ?_, ?_⟩
    · obtain ⟨u, hu, rfl⟩ := hV v hv; exact hu
    · obtain ⟨v, hv, rfl⟩ := hs; exact hv
    · obtain ⟨v, hv, rfl⟩ := ht; exact hv
  · rintro ⟨hst, ⟨hne, hnd, hV, hch⟩, hs, ht⟩
    exact ⟨⟨⟨⟨⟨⟨hst, hne⟩, hnd⟩, fun v hv ↦ ⟨v, hV v hv, rfl⟩⟩, ⟨x.source, hs, rfl⟩⟩,
      ⟨x.target, ht, rfl⟩⟩, hch⟩

/-- `BFP` belongs to `NP`. -/
theorem BFP_mem_NP : BFP ∈ NP encPathInstance := by
  have hcheck : ComputableInPolyTime bfpCheck
      (encPair encPathInstance (encList encNat)) encBool := by
    have hnotnil : ComputableInPolyTime (fun q : PathInstance × List ℕ ↦ decide (q.2 ≠ []))
        (encPair encPathInstance (encList encNat)) encBool := by
      simpa only [Function.comp_def, _root_.decide_not] using
        bool_not.comp ((snd _ _).decide_eq' (const []))
    have hnd : ComputableInPolyTime
        (fun q : PathInstance × List ℕ ↦ q.2.zipIdx.all fun e ↦ decide (q.2.idxOf e.1 = e.2))
        (encPair encPathInstance (encList encNat)) encBool := by
      fun_prop
    have hcyc : ComputableInPolyTime
        (fun q : PathInstance × List ℕ ↦ Graph.cycleChainBool q.1.graph.arcBool q.2)
        (encPair encPathInstance (encList encNat)) encBool :=
      Graph.computableInPolyTime_cycleChainBool
        (Graph.computableInPolyTime_arcBool.comp (show ComputableInPolyTime
          (fun q : ((PathInstance × List ℕ) × ℕ) × ℕ ↦ ((q.1.1.1.graph, q.1.2), q.2)) _ _ by
          fun_prop))
        (snd _ _)
    unfold bfpCheck
    exact bool_and' (bool_and' (bool_and' (bool_and' (bool_and' (bool_and'
      (by fun_prop) hnotnil) hnd) (by fun_prop)) (by fun_prop)) (by fun_prop)) hcyc
  have hset : BFP = {x : PathInstance | ∃ c : List ℕ, bfpCheck (x, c) = true} := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_BFP_iff_exists_isDirCycle, bfpCheck_eq_true_iff,
      exists_and_left]
  rw [hset]
  refine mem_NP_of_witness (p := Polynomial.X) (Decoder.list Decoder.nat) hcheck
    (fun _ _ ↦ Iff.rfl) fun x c hc ↦ ⟨c, hc, ?_⟩
  obtain ⟨_, ⟨_, hnd, hV, _⟩, _, _⟩ := (bfpCheck_eq_true_iff x c).mp hc
  rw [Polynomial.eval_X]
  refine (length_encList_le_of_nodup_subset hnd hV).trans ?_
  have h1 := length_le_encPair_left (encList encNat) (encList (encPair encNat encNat))
    (x.graph.vertices, x.graph.edges)
  have h2 := encPathInstance_graph_length_le x
  simpa [encGraph_apply] using h1.trans h2

end Cslib.Complexity
