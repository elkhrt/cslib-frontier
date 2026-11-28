/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Ramsey.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

/-!
# Multicolor Ramsey Numbers of Complete Graphs

For a finite palette of `c` colors and target clique sizes `t : Fin c → ℕ`, the off-diagonal
multicolor Ramsey number `CslibFrontier.SimpleGraph.offDiagRamsey t` is the least `N : ℕ` such
that every `Fin c`-edge-labeling of the complete graph on `Fin N` admits some color `i : Fin c`
and a subset `S : Finset (Fin N)` forming a monochromatic `(t i)`-clique in `C.labelGraph i`.
Specializing to constant target size `t = fun _ ↦ n` gives the symmetric `c`-color Ramsey number
`CslibFrontier.SimpleGraph.multicolorRamsey c n` ($R^c(n)$), which agrees with the two-color
Ramsey number `SimpleGraph.ramseyNumber n n` when `c = 2`.

## Main definitions

* `CslibFrontier.SimpleGraph.offDiagRamsey`: off-diagonal multicolor Ramsey number
  $R(t_0, \dots, t_{c-1})$.
* `CslibFrontier.SimpleGraph.multicolorRamsey`: symmetric `c`-color Ramsey number $R^c(n)$.

## Main results

* `CslibFrontier.SimpleGraph.exists_isNClique_labelGraph_of_pow_le`: multicolor pigeonhole
  Erdős–Szekeres bound guaranteeing a monochromatic `(t i)`-clique in any subset of cardinality at
  least $c^{\sum_i (t_i - 1)}$ for $c \ge 2$.
* `CslibFrontier.SimpleGraph.offDiagRamsey_le_card_iff`,
  `CslibFrontier.SimpleGraph.multicolorRamsey_le_card_iff`: finite-type characterizations via
  `TopEdgeLabeling V (Fin c)`.
* `CslibFrontier.SimpleGraph.multicolorRamsey_two_eq_ramseyNumber`: agreement $R^2(n) = R(n, n)$
  with `SimpleGraph.ramseyNumber`.
* `CslibFrontier.SimpleGraph.multicolorRamsey_le_pow_mul_pred`,
  `CslibFrontier.SimpleGraph.multicolorRamsey_le_pow_mul_sub_one`: exponential upper bounds
  $R^c(n) \le c^{c(n - 1)} \le c^{c n - 1}$ for $c \ge 2$.
* `CslibFrontier.SimpleGraph.multicolorRamsey_two_three`: exact evaluation $R^2(3) = 6$.
-/

public section

namespace CslibFrontier.SimpleGraph

open Finset _root_.SimpleGraph

section OffDiag

variable {V W : Type*}

private lemma exists_isNClique_pullback {c : ℕ} {t : Fin c → ℕ} {C : TopEdgeLabeling W (Fin c)}
    (f : V ↪ W)
    (h : ∃ (i : Fin c) (S : Finset V), ((TopEdgeLabeling.pullback C f).labelGraph i).IsNClique
      (t i) S) :
    ∃ (i : Fin c) (S : Finset W), (C.labelGraph i).IsNClique (t i) S := by
  classical
  obtain ⟨i, S, hcl, hcard⟩ := h
  refine ⟨i, S.map f, ⟨?_, by rw [card_map, hcard]⟩⟩
  rw [coe_map, IsClique, f.injective.injOn.pairwise_image]
  intro x hx y hy hne
  have hadj := hcl hx hy hne
  rw [EdgeLabeling.labelGraph_adj] at hadj
  dsimp only [Function.onFun]
  rw [EdgeLabeling.labelGraph_adj]
  obtain ⟨hxy, hget⟩ := hadj
  rw [TopEdgeLabeling.pullback, EdgeLabeling.pullback_apply] at hget
  refine ⟨by simpa using f.injective.ne hne, ?_⟩
  convert hget using 2
  ext
  simp

private lemma sum_card_colorFilter_eq_card_erase {c : ℕ}
    (C : TopEdgeLabeling V (Fin c)) [DecidableEq V] {s : Finset V} {v : V} (hv : v ∈ s) :
    (∑ i : Fin c, #((s.erase v).filter fun w ↦ (C.labelGraph i).Adj v w)) = #s - 1 := by
  have hbiUnion :
      univ.biUnion (fun i : Fin c ↦ (s.erase v).filter fun w ↦ (C.labelGraph i).Adj v w) =
        s.erase v := by
    ext w
    simp only [mem_biUnion, mem_univ, true_and, mem_filter, TopEdgeLabeling.labelGraph_adj]
    refine ⟨fun ⟨_, hw, _⟩ ↦ hw, fun hw ↦ ?_⟩
    have hvw : v ≠ w := (mem_erase.mp hw).1.symm
    exact ⟨C.get v w hvw, hw, hvw, rfl⟩
  have hdisj :
      ((univ : Finset (Fin c)) : Set (Fin c)).PairwiseDisjoint
        (fun i : Fin c ↦ (s.erase v).filter fun w ↦ (C.labelGraph i).Adj v w) := by
    intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w hwi hwj
    have hi := (TopEdgeLabeling.labelGraph_adj v w).mp (mem_filter.mp hwi).2
    have hj := (TopEdgeLabeling.labelGraph_adj v w).mp (mem_filter.mp hwj).2
    obtain ⟨_, hgi⟩ := hi
    obtain ⟨_, hgj⟩ := hj
    exact hij (hgi.symm.trans hgj)
  rw [← card_biUnion hdisj, hbiUnion, card_erase_of_mem hv]

private lemma exists_isNClique_aux {c : ℕ} (hc : 2 ≤ c) :
    ∀ (M : ℕ) {V : Type*} (C : TopEdgeLabeling V (Fin c)) (t : Fin c → ℕ)
      (s : Finset V), (∑ i : Fin c, (t i - 1)) = M → c ^ M ≤ #s →
      ∃ (i : Fin c) (S : Finset V), S ⊆ s ∧ (C.labelGraph i).IsNClique (t i) S
  | 0, V, C, t, s, hM, hs => by
    classical
    let hi0 : Fin c := ⟨0, by omega⟩
    have ht0 : t hi0 - 1 = 0 :=
      Nat.eq_zero_of_le_zero
        ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ hi0)).trans hM.le)
    rcases Nat.eq_zero_or_pos (t hi0) with hz | hpos
    · exact ⟨hi0, ∅, empty_subset s, by simp [hz]⟩
    · have ht1 : t hi0 = 1 := by omega
      obtain ⟨v, hv⟩ : s.Nonempty := card_pos.mp (by simpa using hs)
      exact ⟨hi0, {v}, singleton_subset_iff.mpr hv, by simp [ht1]⟩
  | M + 1, V, C, t, s, hM, hs => by
    classical
    by_cases hle1 : ∃ i : Fin c, t i ≤ 1
    · obtain ⟨i, hi⟩ := hle1
      rcases Nat.eq_zero_or_pos (t i) with hz | hpos
      · exact ⟨i, ∅, empty_subset s, by simp [hz]⟩
      · have ht1 : t i = 1 := by omega
        have hcpos : 0 < c ^ (M + 1) := Nat.pow_pos (by omega)
        obtain ⟨v, hv⟩ : s.Nonempty := card_pos.mp (lt_of_lt_of_le hcpos hs)
        exact ⟨i, {v}, singleton_subset_iff.mpr hv, by simp [ht1]⟩
    · push Not at hle1
      have hcpos : 0 < c ^ (M + 1) := Nat.pow_pos (by omega)
      obtain ⟨v, hv⟩ : s.Nonempty := card_pos.mp (lt_of_lt_of_le hcpos hs)
      let part : Fin c → Finset V := fun i ↦
        (s.erase v).filter fun w ↦ (C.labelGraph i).Adj v w
      have hsum_part : (∑ i : Fin c, #(part i)) = #s - 1 :=
        sum_card_colorFilter_eq_card_erase C hv
      have hex_color : ∃ i : Fin c, c ^ M ≤ #(part i) := by
        by_contra hall
        push Not at hall
        have hle_each : ∀ i ∈ (univ : Finset (Fin c)), #(part i) ≤ c ^ M - 1 :=
          fun i _ ↦ Nat.le_sub_one_of_lt (hall i)
        have hsum_le : (∑ i : Fin c, #(part i)) ≤ c * (c ^ M - 1) := by
          simpa using Finset.sum_le_card_nsmul univ (fun i ↦ #(part i)) (c ^ M - 1) hle_each
        have hcle : c ≤ c ^ (M + 1) := Nat.le_self_pow (by omega) c
        have hmul : c * (c ^ M - 1) = c ^ (M + 1) - c := by
          rw [Nat.mul_sub_one, pow_succ']
        rw [hsum_part, hmul] at hsum_le
        omega
      obtain ⟨i₀, hi₀⟩ := hex_color
      let t' : Fin c → ℕ := Function.update t i₀ (t i₀ - 1)
      have ht'_sum : (∑ j : Fin c, (t' j - 1)) = M := by
        have h2 : 2 ≤ t i₀ := hle1 i₀
        have hsplit1 := add_sum_erase univ (fun j ↦ t' j - 1) (mem_univ i₀)
        have hsplit2 := add_sum_erase univ (fun j ↦ t j - 1) (mem_univ i₀)
        have herase :
            ∑ j ∈ univ.erase i₀, (t' j - 1) = ∑ j ∈ univ.erase i₀, (t j - 1) := by
          refine sum_congr rfl fun j hj ↦ ?_
          simp [t', (mem_erase.mp hj).1]
        have hi₀_val : t' i₀ - 1 = (t i₀ - 1) - 1 := by simp [t']
        omega
      obtain ⟨j, S, hS_sub, hS_cl⟩ := exists_isNClique_aux hc M C t' (part i₀) ht'_sum hi₀
      have hpart_sub : part i₀ ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
      by_cases hji : j = i₀
      · subst hji
        have hti₀ : t' j = t j - 1 := by simp [t']
        rw [hti₀] at hS_cl
        have hv_adj : ∀ w ∈ S, (C.labelGraph j).Adj v w :=
          fun w hw ↦ (mem_filter.mp (hS_sub hw)).2
        have hcl_ins : (C.labelGraph j).IsNClique (t j - 1 + 1) (insert v S) :=
          hS_cl.insert hv_adj
        have h2 : 2 ≤ t j := hle1 j
        rw [Nat.sub_add_cancel (by omega)] at hcl_ins
        exact ⟨j, insert v S, insert_subset hv (hS_sub.trans hpart_sub), hcl_ins⟩
      · have htj : t' j = t j := by simp [t', hji]
        rw [htj] at hS_cl
        exact ⟨j, S, hS_sub.trans hpart_sub, hS_cl⟩

/-- **Multicolor Erdős–Szekeres bound**: for `2 ≤ c`, any subset `s` of cardinality at least
$c^{\sum_i (t_i - 1)}$ in a `Fin c`-edge-labeled complete graph contains a monochromatic
`(t i)`-clique for some color `i : Fin c`. -/
theorem exists_isNClique_labelGraph_of_pow_le {c : ℕ} (hc : 2 ≤ c)
    (C : TopEdgeLabeling V (Fin c)) (t : Fin c → ℕ) {s : Finset V}
    (hs : c ^ (∑ i : Fin c, (t i - 1)) ≤ #s) :
    ∃ (i : Fin c) (S : Finset V), S ⊆ s ∧ (C.labelGraph i).IsNClique (t i) S :=
  exists_isNClique_aux hc (∑ i : Fin c, (t i - 1)) C t s rfl hs

private lemma offDiagRamsey_set_nonempty {c : ℕ} (t : Fin c → ℕ) :
    {N : ℕ | ∀ C : TopEdgeLabeling (Fin N) (Fin c),
      ∃ (i : Fin c) (S : Finset (Fin N)), (C.labelGraph i).IsNClique (t i) S}.Nonempty := by
  rcases c with _ | _ | c'
  · refine ⟨2, fun C ↦ ?_⟩
    have hedge : ((0 : Fin 2) ≠ (1 : Fin 2)) := by decide
    exact Fin.elim0 (C.get 0 1 hedge)
  · refine ⟨t 0, fun C ↦ ⟨0, univ, ?_⟩⟩
    refine ⟨fun x _ y _ hne ↦ ?_, by simp⟩
    rw [TopEdgeLabeling.labelGraph_adj]
    exact ⟨hne, Fin.ext (by omega)⟩
  · refine ⟨(c' + 2) ^ (∑ i : Fin (c' + 2), (t i - 1)), fun C ↦ ?_⟩
    obtain ⟨i, S, _, hcl⟩ :=
      exists_isNClique_labelGraph_of_pow_le (by omega) C t (s := univ) (by simp)
    exact ⟨i, S, hcl⟩

/-- The **off-diagonal multicolor Ramsey number** $R(t_0, \dots, t_{c-1})$: the least `N : ℕ`
such that every `Fin c`-edge-labeling of `⊤ : SimpleGraph (Fin N)` admits a color `i : Fin c`
and a monochromatic `(t i)`-clique. -/
noncomputable def offDiagRamsey {c : ℕ} (t : Fin c → ℕ) : ℕ :=
  sInf {N : ℕ | ∀ C : TopEdgeLabeling (Fin N) (Fin c),
    ∃ (i : Fin c) (S : Finset (Fin N)), (C.labelGraph i).IsNClique (t i) S}

/-- Characterization of `offDiagRamsey t ≤ Fintype.card V` on any finite vertex type `V`. -/
theorem offDiagRamsey_le_card_iff {c : ℕ} {t : Fin c → ℕ} [Fintype V] :
    offDiagRamsey t ≤ Fintype.card V ↔
      ∀ C : TopEdgeLabeling V (Fin c),
        ∃ (i : Fin c) (S : Finset V), (C.labelGraph i).IsNClique (t i) S := by
  refine ⟨fun h C ↦ ?_, fun h ↦ Nat.sInf_le fun C ↦ ?_⟩
  · let emb : Fin (offDiagRamsey t) ↪ V :=
      (Fin.castLEEmb h).trans (Fintype.equivFin V).symm.toEmbedding
    exact exists_isNClique_pullback emb (Nat.sInf_mem (offDiagRamsey_set_nonempty t) _)
  · exact exists_isNClique_pullback (Fintype.equivFin V).toEmbedding (h _)

/-- Exponential upper bound $R(t_0, \dots, t_{c-1}) \le c^{\sum_i (t_i - 1)}$ for `2 ≤ c`. -/
theorem offDiagRamsey_le_pow_sum_pred {c : ℕ} (hc : 2 ≤ c) (t : Fin c → ℕ) :
    offDiagRamsey t ≤ c ^ (∑ i : Fin c, (t i - 1)) := by
  rw [← Fintype.card_fin (c ^ (∑ i : Fin c, (t i - 1))), offDiagRamsey_le_card_iff]
  intro C
  obtain ⟨i, S, _, hcl⟩ :=
    exists_isNClique_labelGraph_of_pow_le hc C t (s := univ) (by simp)
  exact ⟨i, S, hcl⟩

end OffDiag

section Symmetric

variable {V : Type*}

/-- The **symmetric `c`-color Ramsey number** $R^c(n)$, equal to
`offDiagRamsey (fun _ : Fin c ↦ n)`. -/
noncomputable def multicolorRamsey (c n : ℕ) : ℕ :=
  offDiagRamsey (fun _ : Fin c ↦ n)

/-- Characterization of `multicolorRamsey c n ≤ Fintype.card V` on any finite vertex type `V`. -/
theorem multicolorRamsey_le_card_iff {c n : ℕ} [Fintype V] :
    multicolorRamsey c n ≤ Fintype.card V ↔
      ∀ C : TopEdgeLabeling V (Fin c),
        ∃ (i : Fin c) (S : Finset V), (C.labelGraph i).IsNClique n S :=
  offDiagRamsey_le_card_iff

/-- Every `Fin c`-edge-labeling on a finite vertex type `V` with
`multicolorRamsey c n ≤ Fintype.card V` has a monochromatic `n`-clique. -/
theorem exists_monochromatic_isNClique {c n : ℕ} [Fintype V]
    (h : multicolorRamsey c n ≤ Fintype.card V) (C : TopEdgeLabeling V (Fin c)) :
    ∃ (i : Fin c) (S : Finset V), (C.labelGraph i).IsNClique n S :=
  multicolorRamsey_le_card_iff.mp h C

/-- Negated characterization `Fintype.card V < multicolorRamsey c n`. -/
theorem card_lt_multicolorRamsey_iff {c n : ℕ} [Fintype V] :
    Fintype.card V < multicolorRamsey c n ↔
      ∃ C : TopEdgeLabeling V (Fin c), ∀ i : Fin c, (C.labelGraph i).CliqueFree n := by
  simp only [← not_le, multicolorRamsey_le_card_iff, not_forall, not_exists, CliqueFree]

/-- Agreement of the two-color symmetric multicolor Ramsey number with
`SimpleGraph.ramseyNumber n n`. -/
theorem multicolorRamsey_two_eq_ramseyNumber (n : ℕ) :
    multicolorRamsey 2 n = _root_.SimpleGraph.ramseyNumber n n := by
  classical
  refine le_antisymm ?_ ?_
  · rw [← Fintype.card_fin (_root_.SimpleGraph.ramseyNumber n n), multicolorRamsey_le_card_iff]
    intro C
    have h := (_root_.SimpleGraph.ramseyNumber_le_card_iff (V := Fin
      (_root_.SimpleGraph.ramseyNumber n n))).mp (Fintype.card_fin _).symm.le (C.labelGraph 0)
    rcases h with ⟨S, hcl⟩ | ⟨S, hind⟩
    · exact ⟨0, S, hcl⟩
    · refine ⟨1, S, ?_⟩
      have hcompl : (C.labelGraph 0)ᶜ = C.labelGraph 1 := by
        ext u v
        simp only [compl_adj, TopEdgeLabeling.labelGraph_adj]
        refine ⟨fun ⟨hne, h0⟩ ↦ ⟨hne, ?_⟩, fun ⟨hne, h1⟩ ↦ ⟨hne, fun ⟨_, h0⟩ ↦ ?_⟩⟩
        · have hne0 : C.get u v hne ≠ 0 := fun h ↦ h0 ⟨hne, h⟩
          have hlt := (C.get u v hne).isLt
          exact Fin.ext (by have := Fin.val_ne_of_ne hne0; dsimp at this; omega)
        · have : (1 : Fin 2) = 0 := h1.symm.trans h0
          contradiction
      rw [← hcompl]
      exact (isNClique_compl (C.labelGraph 0)).mpr hind
  · rw [← Fintype.card_fin (multicolorRamsey 2 n), _root_.SimpleGraph.ramseyNumber_le_card_iff]
    intro G
    let C : TopEdgeLabeling (Fin (multicolorRamsey 2 n)) (Fin 2) :=
      EdgeLabeling.mk (fun x y _ ↦ if G.Adj x y then 0 else 1)
        (fun x y _ ↦ by simp [G.adj_comm])
    obtain ⟨i, S, hcl⟩ := exists_monochromatic_isNClique (Fintype.card_fin _).symm.le C
    fin_cases i
    · refine Or.inl ⟨S, ?_⟩
      have heq : C.labelGraph 0 = G := by
        ext u v
        simp only [TopEdgeLabeling.labelGraph_adj, C, EdgeLabeling.get_mk]
        refine ⟨fun ⟨_, h⟩ ↦ ?_, fun h ↦ ⟨h.ne, by simp [h]⟩⟩
        split_ifs at h with hadj
        · exact hadj
        · contradiction
      dsimp only at hcl
      exact heq ▸ hcl
    · refine Or.inr ⟨S, ?_⟩
      have heq : C.labelGraph 1 = Gᶜ := by
        ext u v
        simp only [TopEdgeLabeling.labelGraph_adj, compl_adj, C, EdgeLabeling.get_mk]
        refine ⟨fun ⟨hne, h⟩ ↦ ⟨hne, ?_⟩, fun ⟨hne, hnadj⟩ ↦ ⟨hne, by simp [hnadj]⟩⟩
        split_ifs at h with hadj
        · contradiction
        · exact hadj
      dsimp only at hcl
      exact (isNClique_compl G).mp (heq ▸ hcl)

/-- For `0` colors, `multicolorRamsey 0 n = 2`. -/
@[simp]
theorem multicolorRamsey_zero_left (n : ℕ) : multicolorRamsey 0 n = 2 := by
  refine le_antisymm ?_ ?_
  · rw [← Fintype.card_fin 2, multicolorRamsey_le_card_iff]
    intro C
    exact Fin.elim0 (C.get 0 1 (by decide))
  · by_contra hlt
    push Not at hlt
    have h1 : multicolorRamsey 0 n ≤ Fintype.card (Fin 1) := by simpa using Nat.lt_succ_iff.mp hlt
    obtain ⟨i, -⟩ := multicolorRamsey_le_card_iff.mp h1 (fun ⟨_, he⟩ ↦ False.elim (by simp at he))
    exact Fin.elim0 i

/-- For `1` color, `multicolorRamsey 1 n = n`. -/
@[simp]
theorem multicolorRamsey_one_left (n : ℕ) : multicolorRamsey 1 n = n := by
  refine le_antisymm ?_ ?_
  · rw [← Fintype.card_fin n, multicolorRamsey_le_card_iff]
    refine fun C ↦ ⟨0, univ, ⟨fun x _ y _ hne ↦ ?_, by simp⟩⟩
    rw [TopEdgeLabeling.labelGraph_adj]
    exact ⟨hne, Subsingleton.elim _ _⟩
  · by_contra hlt
    push Not at hlt
    have hself : multicolorRamsey 1 n ≤ Fintype.card (Fin (multicolorRamsey 1 n)) :=
      (Fintype.card_fin _).symm.le
    obtain ⟨_, S, _, hcard⟩ :=
      (multicolorRamsey_le_card_iff (c := 1) (n := n)).mp hself default
    have hle : #S ≤ multicolorRamsey 1 n := (card_le_univ S).trans_eq (Fintype.card_fin _)
    omega

/-- For `1 ≤ c`, `multicolorRamsey c 0 = 0`. -/
@[simp]
theorem multicolorRamsey_zero_right {c : ℕ} (hc : 1 ≤ c) : multicolorRamsey c 0 = 0 := by
  refine Nat.eq_zero_of_le_zero ?_
  rw [← Fintype.card_fin 0, multicolorRamsey_le_card_iff]
  exact fun _ ↦ ⟨⟨0, hc⟩, ∅, by simp⟩

/-- For `1 ≤ c`, `multicolorRamsey c 1 = 1`. -/
@[simp]
theorem multicolorRamsey_one_right {c : ℕ} (hc : 1 ≤ c) : multicolorRamsey c 1 = 1 := by
  refine le_antisymm ?_ ?_
  · rw [← Fintype.card_fin 1, multicolorRamsey_le_card_iff]
    exact fun _ ↦ ⟨⟨0, hc⟩, {0}, by simp⟩
  · by_contra hlt
    have h0 : multicolorRamsey c 1 ≤ Fintype.card (Fin 0) := by omega
    obtain ⟨_, S, _, hcard⟩ := multicolorRamsey_le_card_iff.mp h0 (fun _ ↦ ⟨0, hc⟩)
    have := card_le_univ S
    simp_all

/-- For every `c`, `multicolorRamsey c 2 = 2`. -/
@[simp]
theorem multicolorRamsey_two_right (c : ℕ) : multicolorRamsey c 2 = 2 := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exact multicolorRamsey_zero_left 2
  · refine le_antisymm ?_ ?_
    · rw [← Fintype.card_fin 2, multicolorRamsey_le_card_iff]
      intro C
      have h01 : (0 : Fin 2) ≠ 1 := by decide
      have hadj10 : (⊤ : SimpleGraph (Fin 2)).Adj 1 0 := by decide
      refine ⟨C.get 0 1 h01, {0, 1}, ⟨?_, by decide⟩⟩
      intro x hx y hy hne
      rw [TopEdgeLabeling.labelGraph_adj]
      refine ⟨hne, ?_⟩
      fin_cases x <;> fin_cases y
      · exact absurd rfl hne
      · rfl
      · exact EdgeLabeling.get_comm (0 : Fin 2) 1 hadj10
      · exact absurd rfl hne
    · by_contra hlt
      have h1 : multicolorRamsey c 2 ≤ Fintype.card (Fin 1) := by
        rw [Fintype.card_fin]
        omega
      obtain ⟨_, S, _, hcard⟩ :=
        multicolorRamsey_le_card_iff.mp h1 (fun _ ↦ ⟨0, hc⟩)
      have := (card_le_univ S).trans_eq (Fintype.card_fin 1)
      omega

/-- Lower bound `n ≤ multicolorRamsey c n` whenever `1 ≤ c`. -/
theorem le_multicolorRamsey {c n : ℕ} (hc : 1 ≤ c) : n ≤ multicolorRamsey c n := by
  let defaultC : TopEdgeLabeling (Fin (multicolorRamsey c n)) (Fin c) := fun _ ↦ ⟨0, hc⟩
  have hself : multicolorRamsey c n ≤ Fintype.card (Fin (multicolorRamsey c n)) :=
    (Fintype.card_fin _).symm.le
  obtain ⟨_, S, _, hcard⟩ :=
    (multicolorRamsey_le_card_iff (c := c) (n := n)).mp hself defaultC
  calc
    n = #S := hcard.symm
    _ ≤ #(univ : Finset (Fin (multicolorRamsey c n))) := card_le_univ S
    _ = multicolorRamsey c n := Fintype.card_fin _

/-- Monotonicity of `multicolorRamsey c n` in the target clique size `n`. -/
@[gcongr]
theorem multicolorRamsey_mono_right {c m n : ℕ} (hmn : m ≤ n) :
    multicolorRamsey c m ≤ multicolorRamsey c n := by
  rw [← Fintype.card_fin (multicolorRamsey c n), multicolorRamsey_le_card_iff]
  intro C
  have hself : multicolorRamsey c n ≤ Fintype.card (Fin (multicolorRamsey c n)) :=
    (Fintype.card_fin _).symm.le
  obtain ⟨i, S, hcl, hcard⟩ :=
    (multicolorRamsey_le_card_iff (c := c) (n := n)).mp hself C
  obtain ⟨T, hTS, hTcard⟩ := exists_subset_card_eq (hmn.trans_eq hcard.symm)
  exact ⟨i, T, hcl.subset hTS, hTcard⟩

/-- Monotonicity of `multicolorRamsey c n` in the color count `c` for `1 ≤ c₁ ≤ c₂`. -/
theorem multicolorRamsey_mono_left {c₁ c₂ n : ℕ} (hc₁ : 1 ≤ c₁) (hle : c₁ ≤ c₂) :
    multicolorRamsey c₁ n ≤ multicolorRamsey c₂ n := by
  rcases n with _ | n
  · simp [hc₁, hc₁.trans hle]
  · rw [← Fintype.card_fin (multicolorRamsey c₂ (n + 1)), multicolorRamsey_le_card_iff]
    intro C
    let C' : TopEdgeLabeling (Fin (multicolorRamsey c₂ (n + 1))) (Fin c₂) :=
      C.compRight (Fin.castLE hle)
    have hself :
        multicolorRamsey c₂ (n + 1) ≤ Fintype.card (Fin (multicolorRamsey c₂ (n + 1))) :=
      (Fintype.card_fin _).symm.le
    obtain ⟨j, S, hcl, hcard⟩ :=
      (multicolorRamsey_le_card_iff (c := c₂) (n := n + 1)).mp hself C'
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨v, _⟩ := card_pos.mp (by omega : 0 < #S)
      exact ⟨⟨0, hc₁⟩, {v}, by simp⟩
    · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < #S)
      have hadj := hcl hx hy hxy
      rw [TopEdgeLabeling.labelGraph_adj] at hadj
      obtain ⟨_, hget⟩ := hadj
      rw [EdgeLabeling.compRight_get] at hget
      let i₀ : Fin c₁ := C.get x y hxy
      have hj_eq : j = Fin.castLE hle i₀ := hget.symm
      refine ⟨i₀, S, ⟨?_, hcard⟩⟩
      intro u hu w hw huw
      have hadj' := hcl hu hw huw
      rw [TopEdgeLabeling.labelGraph_adj] at hadj' ⊢
      obtain ⟨_, hg'⟩ := hadj'
      rw [EdgeLabeling.compRight_get, hj_eq] at hg'
      exact ⟨huw, (Fin.castLE_injective hle) hg'⟩

/-- Sharp exponential upper bound $R^c(n) \le c^{c(n - 1)}$ for `2 ≤ c`. -/
theorem multicolorRamsey_le_pow_mul_pred {c : ℕ} (hc : 2 ≤ c) (n : ℕ) :
    multicolorRamsey c n ≤ c ^ (c * (n - 1)) := by
  simpa [multicolorRamsey] using offDiagRamsey_le_pow_sum_pred hc (fun _ : Fin c ↦ n)

/-- Classical multicolor Ramsey upper bound $R^c(n) \le c^{c n - 1}$ for `2 ≤ c` and all `n : ℕ`. -/
theorem multicolorRamsey_le_pow_mul_sub_one {c : ℕ} (hc : 2 ≤ c) (n : ℕ) :
    multicolorRamsey c n ≤ c ^ (c * n - 1) := by
  rcases n with _ | n
  · simp [show 1 ≤ c by omega]
  · refine (multicolorRamsey_le_pow_mul_pred hc (n + 1)).trans ?_
    refine Nat.pow_le_pow_right (by omega) ?_
    rw [Nat.add_sub_cancel, Nat.mul_succ]
    omega

private def pentagonColoring : TopEdgeLabeling (Fin 5) (Fin 2) :=
  EdgeLabeling.mk
    (fun x y _ ↦ if y = x + 1 ∨ x = y + 1 then 1 else 0)
    (fun x y _ ↦ by
      by_cases h : x = y + 1 ∨ y = x + 1
      · have h' : y = x + 1 ∨ x = y + 1 := h.symm
        simp [h, h']
      · have h' : ¬ (y = x + 1 ∨ x = y + 1) := fun hc ↦ h hc.symm
        simp [h, h'])

private lemma pentagonColoring_cliqueFree (i : Fin 2) :
    (pentagonColoring.labelGraph i).CliqueFree 3 := by
  intro S ⟨hcl, hcard⟩
  have hsub : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      (if y = x + 1 ∨ x = y + 1 then (1 : Fin 2) else 0) = i := by
    intro x hx y hy hne
    have hadj := hcl hx hy hne
    rw [TopEdgeLabeling.labelGraph_adj] at hadj
    obtain ⟨_, hget⟩ := hadj
    simpa [pentagonColoring, EdgeLabeling.get_mk] using hget
  revert S
  decide +revert

/-- Exact evaluation $R^2(3) = 6$, witnessing sharpness of the two-color case via the pentagon
coloring on `Fin 5` together with the $K_6$ pigeonhole bound. -/
theorem multicolorRamsey_two_three : multicolorRamsey 2 3 = 6 := by
  refine le_antisymm ?_ ?_
  · rw [← Fintype.card_fin 6, multicolorRamsey_le_card_iff]
    intro C
    let deg1 : Finset (Fin 6) :=
      (univ.erase 0).filter fun w ↦ (C.labelGraph 1).Adj 0 w
    let deg0 : Finset (Fin 6) :=
      (univ.erase 0).filter fun w ↦ (C.labelGraph 0).Adj 0 w
    have hsum : #deg0 + #deg1 = 5 := by
      have h := sum_card_colorFilter_eq_card_erase C (mem_univ (0 : Fin 6))
      rw [Fin.sum_univ_two] at h
      exact h
    have hex3 : 3 ≤ #deg0 ∨ 3 ≤ #deg1 := by omega
    have step : ∀ (c0 c1 : Fin 2), c0 ≠ c1 →
        3 ≤ #((univ.erase (0 : Fin 6)).filter fun w ↦ (C.labelGraph c0).Adj 0 w) →
        ∃ (i : Fin 2) (S : Finset (Fin 6)), (C.labelGraph i).IsNClique 3 S := by
      intro c0 c1 hne hcard3
      set N := (univ.erase (0 : Fin 6)).filter fun w ↦ (C.labelGraph c0).Adj 0 w
      by_cases hedge : ∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ (C.labelGraph c0).Adj x y
      · obtain ⟨x, hx, y, hy, hxy, hadj⟩ := hedge
        have h0x : (0 : Fin 6) ≠ x := (mem_erase.mp (mem_filter.mp hx).1).1.symm
        have h0y : (0 : Fin 6) ≠ y := (mem_erase.mp (mem_filter.mp hy).1).1.symm
        refine ⟨c0, {0, x, y}, ⟨?_, ?_⟩⟩
        · intro u hu v hv huv
          simp only [mem_coe, mem_insert, mem_singleton] at hu hv
          rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
          · exact absurd rfl huv
          · exact (mem_filter.mp hx).2
          · exact (mem_filter.mp hy).2
          · exact ((mem_filter.mp hx).2).symm
          · exact absurd rfl huv
          · exact hadj
          · exact ((mem_filter.mp hy).2).symm
          · exact hadj.symm
          · exact absurd rfl huv
        · rw [card_insert_of_notMem (by simp [h0x, h0y]),
            card_insert_of_notMem (by simp [hxy]), card_singleton]
      · push Not at hedge
        obtain ⟨T, hTN, hTcard⟩ := exists_subset_card_eq hcard3
        refine ⟨c1, T, ⟨?_, hTcard⟩⟩
        intro x hx y hy hxy
        have hnot0 := hedge x (hTN hx) y (hTN hy) hxy
        rw [TopEdgeLabeling.labelGraph_adj] at hnot0 ⊢
        refine ⟨hxy, ?_⟩
        have hval : C.get x y hxy ≠ c0 := fun heq ↦ hnot0 ⟨hxy, heq⟩
        have hlt2 := (C.get x y hxy).isLt
        have hc0 := c0.isLt
        have hc1 := c1.isLt
        have hne_val : c0.val ≠ c1.val := Fin.val_ne_of_ne hne
        have hget_ne : (C.get x y hxy).val ≠ c0.val := Fin.val_ne_of_ne hval
        exact Fin.ext (by omega)
    rcases hex3 with h0 | h1
    · exact step 0 1 (by decide) h0
    · exact step 1 0 (by decide) h1
  · have hlt : Fintype.card (Fin 5) < multicolorRamsey 2 3 :=
      card_lt_multicolorRamsey_iff.mpr ⟨pentagonColoring, pentagonColoring_cliqueFree⟩
    rw [Fintype.card_fin] at hlt
    exact Nat.succ_le_of_lt hlt

end Symmetric

end CslibFrontier.SimpleGraph
