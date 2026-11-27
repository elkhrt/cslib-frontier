module

public import CslibFrontier.Computability.Complexity.Problems.UndirectedEdgeGeography.Diamond
import CslibFrontier.Computability.Complexity.Classes.Space.GeneralizedGeography.Reduction
import CslibFrontier.Computability.Complexity.Classes.Space.TQBF.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Foundations.Data.List.Counting

/-!
# Undirected Edge Geography is `PSPACE`-complete

Completes the `PSPACE`-hardness and `PSPACE`-completeness proofs for Undirected Edge Geography
(`Cslib.Complexity.UndirectedEdgeGeography`) via the polynomial-time many-one reduction
`Cslib.Complexity.UndirectedEdgeGeography.reduce` from alternating prenex CNF `TQBF`
(`Cslib.Complexity.TQBFCNF`).

## Main results

* `Cslib.Complexity.UndirectedEdgeGeography.uegWins_formulaGraph`: Player 1 wins on
  `formulaGraph xs ψ` from `topNode 0` iff the alternating existential/universal game on `(xs, ψ)`
  is won by the existential player.
* `Cslib.Complexity.UndirectedEdgeGeography.reduce_mem_iff`: correctness of the reduction.
* `Cslib.Complexity.UndirectedEdgeGeography.computableInPolyTime_reduce`: the reduction is
  computable in polynomial time.
* `Cslib.Complexity.polyTimeReducible_TQBFCNF_UndirectedEdgeGeography`: `TQBFCNF ≤ₚ UEG`.
* `Cslib.Complexity.UndirectedEdgeGeography_pspaceHard`: `UndirectedEdgeGeography` is
  `PSPACE`-hard.
* `Cslib.Complexity.UndirectedEdgeGeography_pspaceComplete`: `UndirectedEdgeGeography` is
  `PSPACE`-complete.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

namespace UndirectedEdgeGeography

/-! ### Phase 2: end of the variable-gadget chain (`topNode xs.length`) -/

private theorem lastIdx_lt_of_mem {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) :
    GeneralizedGeography.lastIdx xs x < xs.length := by
  by_contra hge
  have hup : ∀ (l : List ℕ) (bs : List Bool) (σ : ℕ → Bool), l.length = bs.length →
      (∀ b ∈ bs, b = true) → ∀ v, (v ∈ l ∨ σ v = true) → QBF.updates σ l bs v = true := by
    intro l
    induction l with
    | nil =>
      intro bs σ hlen _ v hv
      cases bs with
      | nil => simpa [QBF.updates] using hv
      | cons _ _ => simp at hlen
    | cons a t ih =>
      intro bs σ hlen hall v hv
      cases bs with
      | nil => simp at hlen
      | cons b bs' =>
        refine ih bs' _ (by simpa using hlen)
          (fun y hy => hall y (List.mem_cons_of_mem _ hy)) v ?_
        rcases hv with hv | hv
        · rcases List.mem_cons.1 hv with rfl | hvt
          · right; simp [Function.update, hall b List.mem_cons_self]
          · exact Or.inl hvt
        · by_cases hva : v = a
          · right; simp [Function.update, hva, hall b List.mem_cons_self]
          · right; simp [Function.update, hva, hv]
  have h1 := GeneralizedGeography.updates_eq_getD_lastIdx (fun _ => false) xs
    (List.replicate xs.length true) (List.length_replicate ..) x hx
  have ht := hup xs (List.replicate xs.length true) (fun _ => false)
    (List.length_replicate ..).symm (fun b hb => List.eq_of_mem_replicate hb) x (Or.inl hx)
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
    Option.getD_none] at ht
  exact Bool.noConfusion ht

private theorem wins_topNode_length_of_true {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    (hz : z.length = xs.length) (hvars : ∀ c ∈ ψ, ∀ l ∈ c, l.1 ∈ xs)
    (heval : ψ.eval (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) = true) :
    EdgeGeographyWins (formulaGraph xs ψ) (normalUsed xs ψ z) (topNode xs.length) := by
  have hnormV := validUsed_normalUsed xs ψ z
  have hadj_tc : (formulaGraph xs ψ).toSimpleGraph.Adj (topNode xs.length) chooserNode :=
    (adj_chooserNode_iff).2 (Or.inl rfl) |>.symm
  rw [edgeGeographyWins_iff]
  refine ⟨chooserNode, hadj_tc, mem_vertices_of_adj hadj_tc,
    by rw [Sym2.eq_swap]; exact chooser_edge_not_mem_validUsed hnormV _, ?_⟩
  rw [not_edgeGeographyWins_iff]
  intro w hadj _ hnot
  rw [adj_chooserNode_iff] at hadj
  rcases hadj with rfl | ⟨i, hi, rfl⟩
  · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnot
  · have hcl : Clause.eval (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) ψ[i] =
        true := (CNF.eval_eq_true_iff _ _).1 heval _ (List.getElem_mem hi)
    obtain ⟨⟨x, b⟩, hlmem, hleval⟩ := (Clause.eval_eq_true_iff _ _).1 hcl
    have hx : x ∈ xs := hvars _ (List.getElem_mem hi) (x, b) hlmem
    set j := GeneralizedGeography.lastIdx xs x
    have hj_xs : j < xs.length := lastIdx_lt_of_mem hx
    have hj_z : j < z.length := hz ▸ hj_xs
    have hzb : z[j] = b := by
      dsimp only at hleval
      rwa [List.getD_eq_getElem _ _ hj_z] at hleval
    have hi_occ : i ∈ occClauses xs ψ j b :=
      mem_occClauses_iff.2 ⟨hi, (x, b), hlmem, hx, rfl, rfl⟩
    obtain ⟨k, hk, hki⟩ := List.getElem_of_mem hi_occ
    have hadj_cu : (formulaGraph xs ψ).toSimpleGraph.Adj (clauseNode i) (u1Node j b k) :=
      (adj_clauseNode_iff hi).2 (Or.inr ⟨j, hj_xs, b, k, hk, hki, Or.inl rfl⟩)
    refine edgeGeographyWins_of_adj_dead hadj_cu (mem_vertices_of_adj hadj_cu) ?_ ?_
    · simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide), sym2_ne_of_tags (by decide),
        clause_edge_not_mem_normalUsed⟩
    · intro u hu
      have hk_seg : k < segCount xs ψ j b := lt_of_lt_of_le hk (length_occClauses_le_segCount ..)
      rw [adj_u1Node_iff hj_xs hk_seg] at hu
      have hj_entry := hnormV.1 j hj_z
      rw [hzb] at hj_entry
      rcases hu with ⟨rfl, ⟨hpar, rfl⟩ | ⟨hpar, rfl⟩⟩ | ⟨hkpos, rfl⟩ | rfl | ⟨_, rfl⟩
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (by rw [Sym2.eq_swap]; exact (hj_entry.1 hpar).2.1)))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (by rw [Sym2.eq_swap]; exact (hj_entry.2.1 hpar).1)))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (by
            rw [Sym2.eq_swap]
            have := (hj_entry.2.2.1 (k - 1) (by omega)).2
            rwa [Nat.sub_add_cancel (by omega)] at this)))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (by
            rcases hj_entry.2.2.2.2 k hk_seg with ⟨hm, _⟩ | ⟨_, hcl1, _⟩
            · exact hm
            · exact absurd hcl1 clause_edge_not_mem_normalUsed)))
      · rw [hki, Sym2.eq_swap]; exact List.mem_cons_self

private theorem loses_topNode_length_of_false {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {used : List (Sym2 ℕ)} (hV : ValidUsed xs ψ z used)
    (hz : z.length = xs.length)
    (heval : ψ.eval (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) = false) :
    ¬ EdgeGeographyWins (formulaGraph xs ψ) used (topNode xs.length) := by
  rw [not_edgeGeographyWins_iff]
  intro w hadj _ hnot
  rw [adj_topNode_iff le_rfl] at hadj
  rcases hadj with ⟨hpos, ⟨hpar, rfl⟩ | ⟨hpar, rfl⟩⟩ | ⟨hlt, _⟩ | ⟨hlt, _⟩ | ⟨-, rfl⟩
  · have h := ((hV.1 (xs.length - 1) (by omega)).1 hpar).2.2.2.1
    rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at h
    exact absurd h hnot
  · have h := ((hV.1 (xs.length - 1) (by omega)).2.1 hpar).2
    rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at h
    exact absurd h hnot
  · omega
  · omega
  · have hne_all : ¬ ∀ c ∈ ψ,
        Clause.eval (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) c = true := by
      intro hall; rw [(CNF.eval_eq_true_iff _ _).2 hall] at heval; exact Bool.noConfusion heval
    push Not at hne_all
    obtain ⟨c, hc, hceval⟩ := hne_all
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hci_false :
        Clause.eval (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) ψ[i] = false := by
      cases h : Clause.eval _ ψ[i] <;> simp_all
    have hadj_cc : (formulaGraph xs ψ).toSimpleGraph.Adj chooserNode (clauseNode i) :=
      (adj_chooserNode_iff).2 (Or.inr ⟨i, hi, rfl⟩)
    rw [edgeGeographyWins_iff]
    refine ⟨clauseNode i, hadj_cc, mem_vertices_of_adj hadj_cc, by
      simp only [List.mem_cons, not_or]
      exact ⟨sym2_ne_of_tags (by decide), chooser_edge_not_mem_validUsed hV _⟩, ?_⟩
    rw [not_edgeGeographyWins_iff]
    intro u hadj_u _ hnot_u
    rw [adj_clauseNode_iff hi] at hadj_u
    rcases hadj_u with rfl | ⟨j, hj_xs, b, k, hk, hki, rfl | rfl⟩
    · exact absurd (by rw [Sym2.eq_swap]; exact List.mem_cons_self) hnot_u
    · have hj_z : j < z.length := hz ▸ hj_xs
      have hb_ne : b ≠ z[j] := by
        intro heq
        obtain ⟨_, l, hl, _, hlj, hlb⟩ := mem_occClauses_iff.1 (hki ▸ List.getElem_mem hk)
        have hltrue :
            (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) l.1 = l.2 := by
          dsimp only
          rw [hlj, List.getD_eq_getElem _ _ hj_z, ← heq, ← hlb]
        have := (Clause.eval_eq_true_iff
          (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) ψ[i]).2 ⟨l, hl, hltrue⟩
        rw [this] at hci_false; exact Bool.noConfusion hci_false
      have hb_eq : b = !z[j] := by cases b <;> cases hzj : z[j] <;> simp_all
      subst hb_eq
      have hbr := validUsed_not_mem_branch hV (j := j) (b := !z[j]) (fun _ => by simp)
      have hk_seg : k < segCount xs ψ j (!z[j]) :=
        lt_of_lt_of_le hk (length_occClauses_le_segCount ..)
      have hnot3 : ∀ {e : Sym2 ℕ},
          e ≠ s(clauseNode i, u1Node j (!z[j]) k) →
          e ≠ s(chooserNode, clauseNode i) →
          e ≠ s(topNode xs.length, chooserNode) → e ∉ used →
          e ∉ s(clauseNode i, u1Node j (!z[j]) k) :: s(chooserNode, clauseNode i) ::
              s(topNode xs.length, chooserNode) :: used := by
        intro e h1 h2 h3 h4; simp [List.mem_cons, h1, h2, h3, h4]
      refine wins_backwalk_u1 hj_xs k hk_seg _ ?_ ?_ ?_
      · intro hpar
        obtain ⟨hwc, hcu, hcases⟩ := validUsed_even_backwalk_hyp hV hj_z hj_xs hpar
        refine ⟨hnot3 (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) hwc,
          hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) hcu, ?_⟩
        rcases hcases with ⟨hta, haw, htop⟩
        refine ⟨hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) hta,
          hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) haw, ?_⟩
        rcases htop with ⟨htw, hdead⟩ | ⟨htw_b, hta', haw', hdead, htop_dead⟩
        · left
          refine ⟨hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (sym2_ne_of_tags (by decide)) htw, fun v hv => ?_⟩
          simp only [List.mem_cons]
          rcases List.mem_cons.1 (hdead v hv) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
        · right
          refine ⟨hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (sym2_ne_of_tags (by decide)) htw_b,
            hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (sym2_ne_of_tags (by decide)) hta',
            hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (sym2_ne_of_tags (by decide)) haw', fun v hv => ?_, fun v hv => ?_⟩
          · simp only [List.mem_cons]
            rcases List.mem_cons.1 (hdead v hv) with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
          · rcases htop_dead v hv with h | h | hd
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · right; right; simp only [List.mem_cons]
              rcases List.mem_cons.1 hd with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · intro hpar
        refine ⟨hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) (hbr.2.2.2 hpar), fun v hv => ?_⟩
        simp only [List.mem_cons]
        rcases List.mem_cons.1 (validUsed_dead_topNode_odd hV hj_z (le_of_eq hz) hpar v hv) with
          h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · intro t _
        obtain ⟨h1, h2, h3, h4⟩ := hbr.1 t
        refine ⟨hnot3 (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) h3,
          hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) h4,
          hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) h1,
          hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) h2⟩
    · have hj_z : j < z.length := hz ▸ hj_xs
      have hb_ne : b ≠ z[j] := by
        intro heq
        obtain ⟨_, l, hl, _, hlj, hlb⟩ := mem_occClauses_iff.1 (hki ▸ List.getElem_mem hk)
        have hltrue :
            (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) l.1 = l.2 := by
          dsimp only
          rw [hlj, List.getD_eq_getElem _ _ hj_z, ← heq, ← hlb]
        have := (Clause.eval_eq_true_iff
          (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) ψ[i]).2 ⟨l, hl, hltrue⟩
        rw [this] at hci_false; exact Bool.noConfusion hci_false
      have hb_eq : b = !z[j] := by cases b <;> cases hzj : z[j] <;> simp_all
      subst hb_eq
      have hbr := validUsed_not_mem_branch hV (j := j) (b := !z[j]) (fun _ => by simp)
      have hk_seg : k < segCount xs ψ j (!z[j]) :=
        lt_of_lt_of_le hk (length_occClauses_le_segCount ..)
      have hnot3 : ∀ {e : Sym2 ℕ},
          e ≠ s(clauseNode i, u2Node j (!z[j]) k) →
          e ≠ s(chooserNode, clauseNode i) →
          e ≠ s(topNode xs.length, chooserNode) → e ∉ used →
          e ∉ s(clauseNode i, u2Node j (!z[j]) k) :: s(chooserNode, clauseNode i) ::
              s(topNode xs.length, chooserNode) :: used := by
        intro e h1 h2 h3 h4; simp [List.mem_cons, h1, h2, h3, h4]
      refine wins_backwalk_u2 hj_xs k hk_seg _ ?_ ?_ ?_ ?_
      · intro hpar
        obtain ⟨hwc, hcu, hcases⟩ := validUsed_even_backwalk_hyp hV hj_z hj_xs hpar
        refine ⟨hnot3 (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) hwc,
          hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) hcu, ?_⟩
        rcases hcases with ⟨hta, haw, htop⟩
        refine ⟨hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) hta,
          hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) haw, ?_⟩
        rcases htop with ⟨htw, hdead⟩ | ⟨htw_b, hta', haw', hdead, htop_dead⟩
        · left
          refine ⟨hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (sym2_ne_of_tags (by decide)) htw, fun v hv => ?_⟩
          simp only [List.mem_cons]
          rcases List.mem_cons.1 (hdead v hv) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
        · right
          refine ⟨hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (sym2_ne_of_tags (by decide)) htw_b,
            hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (sym2_ne_of_tags (by decide)) hta',
            hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
              (sym2_ne_of_tags (by decide)) haw', fun v hv => ?_, fun v hv => ?_⟩
          · simp only [List.mem_cons]
            rcases List.mem_cons.1 (hdead v hv) with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
          · rcases htop_dead v hv with h | h | hd
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · right; right; simp only [List.mem_cons]
              rcases List.mem_cons.1 hd with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · intro hpar
        refine ⟨hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) (hbr.2.2.2 hpar), fun v hv => ?_⟩
        simp only [List.mem_cons]
        rcases List.mem_cons.1 (validUsed_dead_topNode_odd hV hj_z (le_of_eq hz) hpar v hv) with
          h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · intro t _
        obtain ⟨h1, h2, -, -⟩ := hbr.1 t
        exact ⟨hnot3 (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) h1,
          hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) h2⟩
      · intro t _
        obtain ⟨-, -, h3, h4⟩ := hbr.1 t
        exact ⟨hnot3 (sym2_ne_of_tags (by decide))
          (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) h3,
          hnot3 (sym2_ne_of_tags (by decide)) (sym2_ne_of_tags (by decide))
            (sym2_ne_of_tags (by decide)) h4⟩

private theorem cross_odd_wins {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    (hj : z.length < xs.length) (hpar : z.length % 2 = 1)
    (hnext : ∀ b : Bool, EdgeGeographyWins (formulaGraph xs ψ) (normalUsed xs ψ (z ++ [b]))
      (topNode (z.length + 1))) :
    ¬ EdgeGeographyWins (formulaGraph xs ψ) (normalUsed xs ψ z) (topNode z.length) := by
  set j := z.length
  have hV := validUsed_normalUsed xs ψ z
  rw [not_edgeGeographyWins_iff]
  intro w hadj _ hnot
  rw [adj_topNode_iff (le_of_lt hj)] at hadj
  rcases hadj with ⟨hpos, ⟨hpar', rfl⟩ | ⟨hpar', rfl⟩⟩ | ⟨-, hpar', _⟩ | ⟨-, -, b, rfl⟩ | ⟨heq, _⟩
  · have := ((hV.1 (j - 1) (by omega)).1 hpar').2.2.2.1
    rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this; exact absurd this hnot
  · omega
  · omega
  · have hbr := validUsed_not_mem_branch hV (j := j) (b := b) (fun h => by omega)
    have hbr' := validUsed_not_mem_branch hV (j := j) (b := !b) (fun h => by omega)
    have hunp := validUsed_not_mem_unplayed hV b
    refine walk_branch_wins hj (segCount xs ψ j b) 0 (one_le_segCount _ _ _ _)
      (zero_add _) _ ?_ ?_ ?_ ?_
    · intro t _ _
      exact ⟨by
          simp only [List.mem_cons, not_or]; exact ⟨sym2_ne_of_tags (by decide), (hbr.1 t).1⟩,
        by
          simp only [List.mem_cons, not_or]; exact ⟨sym2_ne_of_tags (by decide), (hbr.1 t).2.1⟩⟩
    · intro t _ _
      exact ⟨by
          simp only [List.mem_cons, not_or]; exact ⟨sym2_ne_of_tags (by decide), (hbr.1 t).2.2.1⟩,
        by
          simp only [List.mem_cons, not_or]; exact ⟨sym2_ne_of_tags (by decide), (hbr.1 t).2.2.2⟩⟩
    · simp only [List.mem_cons, not_or]; exact ⟨sym2_ne_of_tags (by decide), hbr.2.1⟩
    · intro used' hused'
      have hused'_nb : ∀ e, e ∈ used' ↔ e ∈ normalUsed xs ψ z ∨ e ∈ normalBranchEdges xs ψ j b := by
        intro e
        rw [hused']
        simp only [List.mem_cons, normalBranchEdges_eq_append, hpar, Nat.reduceBEq,
          Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_flatMap, List.mem_range,
          List.not_mem_nil, or_false]
        constructor
        · rintro ((rfl | h) | ⟨t, _, ht, h⟩ | ⟨t, _, ht, h⟩ | rfl)
          · exact Or.inr (Or.inl (Or.inl (Or.inl rfl)))
          · exact Or.inl h
          · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨t, ht, h⟩)))
          · exact Or.inr (Or.inl (Or.inr ⟨t, ht, h⟩))
          · exact Or.inr (Or.inr rfl)
        · rintro (h | ((rfl | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | rfl)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr (Or.inl ⟨t, Nat.zero_le _, ht, h⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨t, Nat.zero_le _, ht, h⟩))
          · exact Or.inr (Or.inr (Or.inr rfl))
      rw [not_edgeGeographyWins_iff]
      intro v hadj_v _ hnot_v
      rw [adj_botNode_iff hj] at hadj_v
      rcases hadj_v with ⟨b', rfl⟩ | ⟨hpar', _⟩ | ⟨-, rfl⟩
      · by_cases hb' : b' = b
        · subst hb'
          exact absurd ((hused'_nb _).2 (Or.inr (by simp [normalBranchEdges_eq_append]))) hnot_v
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
          refine wins_backwalk_u2 hj (segCount xs ψ j (!b) - 1) hk_last _ (fun h => by omega)
            ?_ ?_ ?_
          · intro _
            refine ⟨hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.1)
                (sym2_ne_of_tags (by decide)).symm (hbr'.2.2.2 hpar),
              fun u hu => ?_⟩
            rw [adj_topNode_iff (le_of_lt hj)] at hu
            rcases hu with ⟨hpos, ⟨hp', rfl⟩ | ⟨hp', rfl⟩⟩ | ⟨-, hp', _⟩ | ⟨-, -, b'', rfl⟩ | ⟨he,
              _⟩
            · have := ((hV.1 (j - 1) (by omega)).1 hp').2.2.2.1
              rw [Nat.sub_add_cancel (by omega), Sym2.eq_swap] at this
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((hused'_nb _).2 (Or.inl this)))
            · omega
            · omega
            · by_cases hb'' : b'' = b
              · subst hb''
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  ((hused'_nb _).2 (Or.inr (by simp [normalBranchEdges_eq_append, hpar]))))
              · have : b'' = !b := by cases b <;> cases b'' <;> simp_all
                subst this; exact List.mem_cons_self
            · omega
          · intro t _
            exact ⟨hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.1 t)
                (sym2_ne_of_tags (by decide)).symm (hbr'.1 t).1,
              hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.2.1 t)
                (sym2_ne_of_tags (by decide)).symm (hbr'.1 t).2.1⟩
          · intro t _
            exact ⟨hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.2.2.1 t)
                (sym2_ne_of_tags (by decide)).symm (hbr'.1 t).2.2.1,
              hnot_u' (fun _ _ => normalBranchEdges_idx.2.2.2.2.2.2.2.2.2.1 t)
                (sym2_ne_of_tags (by decide)).symm (hbr'.1 t).2.2.2⟩
      · omega
      · refine (edgeGeographyWins_congr ?_ _).2 (hnext b)
        intro e
        rw [mem_normalUsed_append]
        have hbr_j : e ∈ bridgeEdges z.length ↔ e = s(botNode j, topNode (j + 1)) := by
          simp [hpar, j]
        dsimp only [j] at hused'_nb hbr_j ⊢
        simp only [List.mem_cons, hused'_nb, hbr_j]
        constructor
        · rintro (rfl | h | h)
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rintro (h | h | rfl)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact Or.inl rfl
  · omega

/-- Crossing an odd diamond (`j = z.length < xs.length`, `j % 2 = 1`): if for SOME `b` and every
`ValidUsed (z ++ [b]) used'`, Player 1 loses at `topNode (j + 1)`, then Player 2 WINS at `topNode j`
from any `ValidUsed z used`. -/
private theorem cross_odd_loses {xs : List ℕ} {ψ : CNF ℕ} {z : List Bool}
    {used : List (Sym2 ℕ)} (hV : ValidUsed xs ψ z used)
    (hj : z.length < xs.length) (hpar : z.length % 2 = 1) {b : Bool}
    (hnext : ∀ used' : List (Sym2 ℕ),
      ValidUsed xs ψ (z ++ [b]) used' →
      ¬ EdgeGeographyWins (formulaGraph xs ψ) used' (topNode (z.length + 1))) :
    EdgeGeographyWins (formulaGraph xs ψ) used (topNode z.length) := by
  set j := z.length
  have hbr := validUsed_not_mem_branch hV (j := j) (b := b) (fun h => by omega)
  have hunp := validUsed_not_mem_unplayed hV b
  have hadj_tu : (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) (u1Node j b 0) :=
    (adj_topNode_iff (le_of_lt hj)).2 (Or.inr (Or.inr (Or.inl ⟨hj, hpar, b, rfl⟩)))
  rw [edgeGeographyWins_iff]
  refine ⟨u1Node j b 0, hadj_tu, mem_vertices_of_adj hadj_tu, hbr.2.2.2 hpar, ?_⟩
  refine walk_branch_loses hj (segCount xs ψ j b) 0 (one_le_segCount _ _ _ _) (zero_add _) _
    (fun _ h => by omega) (fun _ h => by omega) ?_ ?_ ?_
    (fun _ => ⟨fun h => by omega, fun _ => List.mem_cons_self⟩) ?_
  · intro t _ _
    exact ⟨by simp only [List.mem_cons, not_or]; exact ⟨sym2_ne_of_tags (by decide), (hbr.1 t).1⟩,
      by simp only [List.mem_cons, not_or]; exact ⟨sym2_ne_of_tags (by decide), (hbr.1 t).2.1⟩,
      fun ht => ⟨by
          simp only [List.mem_cons, not_or]
          exact ⟨sym2_ne_of_tags (by decide), (hunp.2.2.2.2.2.2 t ht).1⟩,
        by
          simp only [List.mem_cons, not_or]
          exact ⟨sym2_ne_of_tags (by decide), (hunp.2.2.2.2.2.2 t ht).2⟩⟩⟩
  · intro t _ _
    exact ⟨by
        simp only [List.mem_cons, not_or]; exact ⟨sym2_ne_of_tags (by decide), (hbr.1 t).2.2.1⟩,
      by
        simp only [List.mem_cons, not_or]; exact ⟨sym2_ne_of_tags (by decide), (hbr.1 t).2.2.2⟩⟩
  · simp only [List.mem_cons, not_or]; exact ⟨sym2_ne_of_tags (by decide), hbr.2.1⟩
  · intro used' hsub' hconn' hbot' hseg' hmem'
    have hadj_bt : (formulaGraph xs ψ).toSimpleGraph.Adj (botNode j) (topNode (j + 1)) :=
      (adj_botNode_iff hj).2 (Or.inr (Or.inr ⟨hpar, rfl⟩))
    have hnot_bt' : s(botNode j, topNode (j + 1)) ∉ used' := by
      intro hm
      rcases hmem' _ hm with h | ⟨t, _, _, h | h | ⟨_, h | h⟩⟩ | ⟨t, _, _, h | h⟩ | h
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact sym2_ne_of_tags (by decide) h
        · exact hunp.2.2.2.2.2.1 h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
      · exact sym2_ne_of_tags (by decide) h
    rw [edgeGeographyWins_iff]
    refine ⟨topNode (j + 1), hadj_bt, mem_vertices_of_adj hadj_bt, hnot_bt', ?_⟩
    refine hnext _ (validUsed_extend hV
      (fun e he => List.mem_cons_of_mem _ (hsub' e (List.mem_cons_of_mem _ he)))
      (fun e he => ?_) (fun h => by omega)
      (fun _ => ⟨List.mem_cons_of_mem _ (hsub' _ List.mem_cons_self), List.mem_cons_self⟩)
      (fun k hk => ⟨List.mem_cons_of_mem _ (hconn' k hk).1, List.mem_cons_of_mem _ (hconn' k hk).2⟩)
      (List.mem_cons_of_mem _ hbot')
      (fun k hk => (hseg' k hk).imp
        (fun ⟨a, c⟩ => ⟨List.mem_cons_of_mem _ a, List.mem_cons_of_mem _ c⟩)
        (fun ⟨hko, a, c⟩ => ⟨hko, List.mem_cons_of_mem _ a, List.mem_cons_of_mem _ c⟩)))
    simp only [List.mem_cons] at he
    rcases he with rfl | he'
    · exact Or.inr (Or.inr (Or.inl (by simp [hpar, j])))
    · rcases hmem' e he' with h | ⟨t, _, ht, h | h | ⟨hto, h | h⟩⟩ | ⟨t, _, ht, h | h⟩ | rfl
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inr (Or.inl (by simp [normalBranchEdges_eq_append, hpar, j]))
        · exact Or.inl h
      · exact Or.inr (Or.inl (by
          simp only [normalBranchEdges_eq_append, List.mem_append, List.mem_flatMap, List.mem_range,
            List.mem_cons]
          exact Or.inl (Or.inl (Or.inr ⟨t, ht, Or.inl h⟩))))
      · exact Or.inr (Or.inl (by
          simp only [normalBranchEdges_eq_append, List.mem_append, List.mem_flatMap, List.mem_range,
            List.mem_cons]
          exact Or.inl (Or.inl (Or.inr ⟨t, ht, Or.inr (Or.inl h)⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, hto, Or.inl h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, hto, Or.inr h⟩)))
      · exact Or.inr (Or.inl (by
          simp only [normalBranchEdges_eq_append, List.mem_append, List.mem_flatMap, List.mem_range,
            List.mem_cons]
          exact Or.inl (Or.inr ⟨t, ht, Or.inl h⟩)))
      · exact Or.inr (Or.inl (by
          simp only [normalBranchEdges_eq_append, List.mem_append, List.mem_flatMap, List.mem_range,
            List.mem_cons]
          exact Or.inl (Or.inr ⟨t, ht, Or.inr (Or.inl h)⟩)))
      · exact Or.inr (Or.inl (by simp [normalBranchEdges_eq_append, j]))

/-! ### Induction over the alternating quantifier prefix -/

private theorem uegWins_topNode_both {xs : List ℕ} {ψ : CNF ℕ}
    (heven : Even xs.length) (hvars : ∀ c ∈ ψ, ∀ l ∈ c, l.1 ∈ xs) :
    ∀ (k : ℕ) (z : List Bool), z.length + k = xs.length →
      let alt := Alternation (z.length % 2 == 0) (List.replicate k 1)
        fun bs => ψ.eval (fun x => (z ++ bs).getD (GeneralizedGeography.lastIdx xs x) false) = true
      (alt →
        if z.length % 2 = 0 then
          EdgeGeographyWins (formulaGraph xs ψ) (normalUsed xs ψ z) (topNode z.length)
        else
          ¬ EdgeGeographyWins (formulaGraph xs ψ) (normalUsed xs ψ z) (topNode z.length)) ∧
      (¬ alt → ∀ used, ValidUsed xs ψ z used →
        if z.length % 2 = 0 then
          ¬ EdgeGeographyWins (formulaGraph xs ψ) used (topNode z.length)
        else
          EdgeGeographyWins (formulaGraph xs ψ) used (topNode z.length))
  | 0, z, hz => by
    have hz' : z.length = xs.length := by omega
    obtain ⟨m, hm⟩ := heven
    have hpar : z.length % 2 = 0 := by omega
    simp only [List.replicate_zero, hpar, ↓reduceIte, alternation_nil, List.append_nil]
    rw [hz']
    constructor
    · exact wins_topNode_length_of_true hz' hvars
    · intro hne used hV
      have hf : ψ.eval (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) = false := by
        cases h : ψ.eval _ <;> simp_all
      exact loses_topNode_length_of_false hV hz' hf
  | k + 1, z, hz => by
    have hlt : z.length < xs.length := by omega
    have ih (b : Bool) := uegWins_topNode_both heven hvars k (z ++ [b])
      (by simp only [List.length_append, List.length_singleton]; omega)
    simp only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append] at ih
    rw [List.replicate_succ]
    rcases Nat.mod_two_eq_zero_or_one z.length with h | h
    · have h1 : (z.length + 1) % 2 = 1 := by omega
      simp only [h, beq_self_eq_true, ↓reduceIte, h1, Nat.reduceBEq,
        alternation_true_one_cons] at ih ⊢
      constructor
      · rintro ⟨b, hb⟩
        exact cross_even_wins hlt h ((ih b).1 hb)
      · intro hall used hV
        push Not at hall
        exact cross_even_loses hV hlt h fun b used' hV' => (ih b).2 (hall b) used' hV'
    · have h0 : (z.length + 1) % 2 = 0 := by omega
      simp only [h, Nat.reduceBEq, ↓reduceIte, h0, beq_self_eq_true,
        alternation_false_one_cons] at ih ⊢
      constructor
      · intro hall
        exact cross_odd_wins hlt h fun b => (ih b).1 (hall b)
      · intro hne used hV
        push Not at hne
        obtain ⟨b, hb⟩ := hne
        exact cross_odd_loses hV hlt h (fun used' hV' => (ih b).2 hb used' hV')

/-- **Game-formula equivalence**: Player 1 wins Undirected Edge Geography on `(formulaGraph xs ψ,
topNode 0)` iff the alternating existential/universal game on `(xs, ψ)` is won by the existential
player. -/
theorem uegWins_formulaGraph {xs : List ℕ} {ψ : CNF ℕ} (heven : Even xs.length)
    (hvars : ∀ c ∈ ψ, ∀ l ∈ c, l.1 ∈ xs) :
    EdgeGeographyWins (formulaGraph xs ψ) [] (topNode 0) ↔
      Alternation true (List.replicate xs.length 1)
        fun z => ψ.eval (fun x => z.getD (GeneralizedGeography.lastIdx xs x) false) = true := by
  have hboth := uegWins_topNode_both heven hvars xs.length [] (by simp)
  simp only [List.length_nil, Nat.zero_mod, beq_self_eq_true, ↓reduceIte, List.nil_append,
    normalUsed_eq_flatMap, List.zipIdx_nil, List.flatMap_nil] at hboth
  exact ⟨fun hw => by_contra fun hn => hboth.2 hn [] (validUsed_normalUsed xs ψ []) hw, hboth.1⟩

/-- **Correctness of the reduction**: `reduce x ∈ UndirectedEdgeGeography ↔ x ∈ TQBFCNF`. -/
theorem reduce_mem_iff (x : PrenexCNF) :
    reduce x ∈ UndirectedEdgeGeography ↔ x ∈ TQBFCNF := by
  obtain ⟨ps, ψ⟩ := x
  dsimp only [reduce_eq_ite]
  split_ifs with hall
  · have hvars : ∀ c ∈ ψ, ∀ l ∈ c, l.1 ∈ QBF.roundVars ps := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hall
    have hclosed := (QBF.closed_rounds_ofCNF_iff ps ψ).2 hvars
    have heven : Even (QBF.roundVars ps).length := ⟨ps.length, by rw [QBF.length_roundVars]; ring⟩
    rw [mem_UndirectedEdgeGeography, and_iff_right (topNode_mem_vertices _ _),
      uegWins_formulaGraph heven hvars, mk_mem_TQBFCNF,
      mem_TQBF_iff_of_closed hclosed (fun _ => false),
      QBF.eval_rounds_eq_true_iff, ← QBF.length_roundVars]
    refine alternation_congr_of_length fun z hz => ?_
    rw [sum_replicate_one] at hz
    rw [QBF.eval_ofCNF]
    refine Eq.congr_left (CNF.eval_congr fun v hv => ?_)
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
    obtain ⟨c, hc, hlc⟩ := List.mem_flatten.1 hl
    exact (GeneralizedGeography.updates_eq_getD_lastIdx _ _ z hz l.1 (hvars c hc l hlc)).symm
  · refine iff_of_false ?_ fun h => hall ?_
    · rw [mem_UndirectedEdgeGeography, edgeGeographyWins_iff]
      rintro ⟨_, ⟨w, hadj, _⟩⟩
      simp [Graph.toSimpleGraph_adj] at hadj
    · rw [mk_mem_TQBFCNF] at h
      simpa only [List.all_eq_true, decide_eq_true_eq] using
        (QBF.closed_rounds_ofCNF_iff ps ψ).1 h.1

/-! ### Polynomial-time computability of the reduction -/

section PolyTime

open ComputableInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

private theorem computableInPolyTime_occClauses {xs : γ → List ℕ} {ψ : γ → CNF ℕ}
    {j : γ → ℕ} {b : γ → Bool}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hψ : ComputableInPolyTime ψ encIn encCNF)
    (hj : ComputableInPolyTime j encIn encUnary)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => occClauses (xs x) (ψ x) (j x) (b x)) encIn
      (encList encUnary) := by
  simp only [occClauses_eq_filter]
  simp only [List.decide_mem_eq_any]
  fun_prop

attribute [local fun_prop] computableInPolyTime_occClauses

private theorem computableInPolyTime_segCount {xs : γ → List ℕ} {ψ : γ → CNF ℕ}
    {j : γ → ℕ} {b : γ → Bool}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hψ : ComputableInPolyTime ψ encIn encCNF)
    (hj : ComputableInPolyTime j encIn encUnary)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => segCount (xs x) (ψ x) (j x) (b x)) encIn encUnary := by
  simp only [segCount_eq_max]
  have : (fun x => max 1 (occClauses (xs x) (ψ x) (j x) (b x)).length) =
      fun x => if decide (1 ≤ (occClauses (xs x) (ψ x) (j x) (b x)).length) then
        (occClauses (xs x) (ψ x) (j x) (b x)).length else 1 := by
    funext x; by_cases h : 1 ≤ (occClauses (xs x) (ψ x) (j x) (b x)).length <;> simp [h]; omega
  rw [this]; fun_prop

attribute [local fun_prop] computableInPolyTime_segCount

private theorem computableInPolyTime_node1 {tag : ℕ} {j : γ → ℕ}
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => Nat.pair tag (j x)) encIn encNat :=
  unary_to_binary.comp (show ComputableInPolyTime (fun x => Nat.pair tag (j x)) _ _ by fun_prop)

private theorem computableInPolyTime_node2 {tag : ℕ} {j : γ → ℕ} {b : γ → Bool}
    (hj : ComputableInPolyTime j encIn encUnary) (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => Nat.pair tag (Nat.pair (j x) (b x).toNat)) encIn encNat :=
  unary_to_binary.comp (show ComputableInPolyTime
    (fun x => Nat.pair tag (Nat.pair (j x) (b x).toNat)) _ _ by fun_prop)

private theorem computableInPolyTime_node3 {tag : ℕ} {j : γ → ℕ} {b : γ → Bool} {k : γ → ℕ}
    (hj : ComputableInPolyTime j encIn encUnary) (hb : ComputableInPolyTime b encIn encBool)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun x => Nat.pair tag (Nat.pair (j x) (Nat.pair (b x).toNat (k x))))
      encIn encNat :=
  unary_to_binary.comp (show ComputableInPolyTime
    (fun x => Nat.pair tag (Nat.pair (j x) (Nat.pair (b x).toNat (k x)))) _ _ by fun_prop)

attribute [local fun_prop] computableInPolyTime_node1 computableInPolyTime_node2
  computableInPolyTime_node3

private theorem computableInPolyTime_branchEdges {xs : γ → List ℕ} {ψ : γ → CNF ℕ}
    {j : γ → ℕ} {b : γ → Bool}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hψ : ComputableInPolyTime ψ encIn encCNF)
    (hj : ComputableInPolyTime j encIn encUnary)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => branchEdges (xs x) (ψ x) (j x) (b x)) encIn
      (encList (encPair encNat encNat)) := by
  simp only [branchEdges_eq_append, u1Node_eq_pair, mNode_eq_pair, u2Node_eq_pair,
    vNode_eq_pair, botNode_eq_pair, clauseNode_eq_pair]
  have hseg := computableInPolyTime_segCount hxs hψ hj hb
  have hocc := computableInPolyTime_occClauses hxs hψ hj hb
  have h1 : ComputableInPolyTime
      (fun x => (List.range (segCount (xs x) (ψ x) (j x) (b x))).flatMap fun k =>
        [(Nat.pair 6 (Nat.pair (j x) (Nat.pair (b x).toNat k)),
          Nat.pair 7 (Nat.pair (j x) (Nat.pair (b x).toNat k))),
         (Nat.pair 7 (Nat.pair (j x) (Nat.pair (b x).toNat k)),
          Nat.pair 8 (Nat.pair (j x) (Nat.pair (b x).toNat k)))])
      encIn (encList (encPair encNat encNat)) := by fun_prop
  have h2 : ComputableInPolyTime
      (fun x => (List.range (segCount (xs x) (ψ x) (j x) (b x) - 1)).flatMap fun k =>
        [(Nat.pair 8 (Nat.pair (j x) (Nat.pair (b x).toNat k)),
          Nat.pair 9 (Nat.pair (j x) (Nat.pair (b x).toNat k))),
         (Nat.pair 9 (Nat.pair (j x) (Nat.pair (b x).toNat k)),
          Nat.pair 6 (Nat.pair (j x) (Nat.pair (b x).toNat (k + 1))))])
      encIn (encList (encPair encNat encNat)) := by fun_prop
  have h3 : ComputableInPolyTime
      (fun x => (Nat.pair 8 (Nat.pair (j x) (Nat.pair (b x).toNat
          (segCount (xs x) (ψ x) (j x) (b x) - 1))), Nat.pair 1 (j x)))
      encIn (encPair encNat encNat) := by fun_prop
  have h4 : ComputableInPolyTime
      (fun x => (List.range (occClauses (xs x) (ψ x) (j x) (b x)).length).flatMap fun k =>
        let i := (occClauses (xs x) (ψ x) (j x) (b x)).getD k 0
        [(Nat.pair 11 i, Nat.pair 6 (Nat.pair (j x) (Nat.pair (b x).toNat k))),
         (Nat.pair 11 i, Nat.pair 8 (Nat.pair (j x) (Nat.pair (b x).toNat k)))])
      encIn (encList (encPair encNat encNat)) := by fun_prop
  exact (listAppend _).comp
    (((listAppend _).comp
      (((listAppend _).comp (h1.prod h2)).prod
        ((ComputableInPolyTime.cons _).comp (h3.prod (const []))))).prod h4)

attribute [local fun_prop] computableInPolyTime_branchEdges

private theorem computableInPolyTime_diamondEdges {xs : γ → List ℕ} {ψ : γ → CNF ℕ} {j : γ → ℕ}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hψ : ComputableInPolyTime ψ encIn encCNF)
    (hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => diamondEdges (xs x) (ψ x) (j x)) encIn
      (encList (encPair encNat encNat)) := by
  simp only [diamondEdges_eq_ite, topNode_eq_pair, botNode_eq_pair, midNode_eq_pair,
    aNode_eq_pair, wNode_eq_pair, cNode_eq_pair, u1Node_eq_pair]
  have hcond : ComputableInPolyTime (fun x => j x % 2 == 0) encIn encBool :=
    ComputableInPolyTime.beq (unary_mod' hj (const 2)) (const 0)
  have heven : ComputableInPolyTime
      (fun x => ([false, true].flatMap fun b =>
          [(Nat.pair 0 (j x), Nat.pair 3 (Nat.pair (j x) b.toNat)),
           (Nat.pair 3 (Nat.pair (j x) b.toNat), Nat.pair 4 (Nat.pair (j x) b.toNat)),
           (Nat.pair 0 (j x), Nat.pair 4 (Nat.pair (j x) b.toNat)),
           (Nat.pair 4 (Nat.pair (j x) b.toNat), Nat.pair 5 (Nat.pair (j x) b.toNat)),
           (Nat.pair 5 (Nat.pair (j x) b.toNat), Nat.pair 6 (Nat.pair (j x) (Nat.pair b.toNat 0)))]
            ++ branchEdges (xs x) (ψ x) (j x) b) ++
        [(Nat.pair 1 (j x), Nat.pair 2 (j x)), (Nat.pair 2 (j x), Nat.pair 0 (j x + 1))])
      encIn (encList (encPair encNat encNat)) := by fun_prop
  have hodd : ComputableInPolyTime
      (fun x => ([false, true].flatMap fun b =>
          (Nat.pair 0 (j x), Nat.pair 6 (Nat.pair (j x) (Nat.pair b.toNat 0))) ::
            branchEdges (xs x) (ψ x) (j x) b) ++
        [(Nat.pair 1 (j x), Nat.pair 0 (j x + 1))])
      encIn (encList (encPair encNat encNat)) := by fun_prop
  exact hcond.ite' heven hodd

attribute [local fun_prop] computableInPolyTime_diamondEdges

/-- **The reduction is polynomial-time.** -/
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce encPrenexCNF encUndirectedEdgeGeography := by
  have hrounds : ComputableInPolyTime (fun x : PrenexCNF => QBF.roundVars x.rounds)
      encPrenexCNF (encList encNat) := by
    unfold QBF.roundVars; fun_prop
  have hmat : ComputableInPolyTime (fun x : PrenexCNF => x.matrix) encPrenexCNF encCNF :=
    encPrenexCNF_matrix_polyTime id'
  have hall : ComputableInPolyTime
      (fun x : PrenexCNF =>
        x.matrix.all fun c => c.all fun l => decide (l.1 ∈ QBF.roundVars x.rounds))
      encPrenexCNF encBool := by
    have h : ComputableInPolyTime
        (fun x : PrenexCNF =>
          x.matrix.all fun c => c.all fun l => (QBF.roundVars x.rounds).any fun u => u == l.1)
        encPrenexCNF encBool :=
      allWithInput hmat (allWithInput (snd _ _)
        (anyWithInput (hrounds.comp ((fst _ _).comp (fst _ _)))
          (ComputableInPolyTime.beq (snd _ _) ((fst _ _).comp ((snd _ _).comp (fst _ _))))))
    exact h.of_enc_eq fun x => congrArg encBool (by simp only [List.decide_mem_eq_any]; congr 1)
  have hgraph : ComputableInPolyTime
      (fun x : PrenexCNF =>
        (⟨formulaGraph (QBF.roundVars x.rounds) x.matrix, topNode 0⟩ :
          UndirectedEdgeGeographyInstance))
      encPrenexCNF encUndirectedEdgeGeography := by
    have hlenR : ComputableInPolyTime (fun x : PrenexCNF => (QBF.roundVars x.rounds).length)
        encPrenexCNF encUnary := (length_list _).comp hrounds
    have hlenM : ComputableInPolyTime (fun x : PrenexCNF => x.matrix.length)
        encPrenexCNF encUnary := (length_list _).comp hmat
    have hedges : ComputableInPolyTime
        (fun x : PrenexCNF => formulaEdges (QBF.roundVars x.rounds) x.matrix)
        encPrenexCNF (encList (encPair encNat encNat)) := by
      simp only [formulaEdges_eq_append, topNode_eq_pair, chooserNode_eq_pair, clauseNode_eq_pair]
      have hd : ComputableInPolyTime
          (fun x : PrenexCNF =>
            (List.range (QBF.roundVars x.rounds).length).flatMap
              (diamondEdges (QBF.roundVars x.rounds) x.matrix))
          encPrenexCNF (encList (encPair encNat encNat)) :=
        flatMapWithInput (range.comp hlenR)
          (computableInPolyTime_diamondEdges (hrounds.comp (fst _ _)) (hmat.comp (fst _ _))
            (snd _ _))
      have hmid : ComputableInPolyTime
          (fun x : PrenexCNF => (Nat.pair 0 (QBF.roundVars x.rounds).length, Nat.pair 10 0))
          encPrenexCNF (encPair encNat encNat) :=
        (computableInPolyTime_node1 hlenR).prod (const (Nat.pair 10 0))
      have hcls : ComputableInPolyTime
          (fun x : PrenexCNF =>
            (List.range x.matrix.length).map fun i => (Nat.pair 10 0, Nat.pair 11 i))
          encPrenexCNF (encList (encPair encNat encNat)) :=
        mapWithInput (range.comp hlenM)
          ((const (Nat.pair 10 0)).prod (computableInPolyTime_node1 (snd _ _)))
      exact (listAppend _).comp (hd.prod ((ComputableInPolyTime.cons _).comp (hmid.prod hcls)))
    have hverts : ComputableInPolyTime
        (fun x : PrenexCNF =>
          topNode 0 :: (formulaEdges (QBF.roundVars x.rounds) x.matrix).flatMap fun e => [e.1, e.2])
        encPrenexCNF (encList encNat) := by
      fun_prop
    exact encUndirectedEdgeGeography_mk_polyTime (encGraph_mk_polyTime hverts hedges)
      (const (topNode 0))
  change ComputableInPolyTime (fun x => reduce x) _ _
  simp only [reduce_eq_ite]
  exact hall.ite' hgraph (const (⟨⟨[0], []⟩, 0⟩ : UndirectedEdgeGeographyInstance))

end PolyTime

end UndirectedEdgeGeography

open UndirectedEdgeGeography

/-- **`TQBFCNF` reduces in polynomial time to Undirected Edge Geography**
.
-/
theorem polyTimeReducible_TQBFCNF_UndirectedEdgeGeography :
    PolyTimeReducible encPrenexCNF encUndirectedEdgeGeography TQBFCNF UndirectedEdgeGeography :=
  ⟨reduce, computableInPolyTime_reduce, fun x => (reduce_mem_iff x).symm⟩

/-- **Undirected Edge Geography is `PSPACE`-hard**. -/
theorem UndirectedEdgeGeography_pspaceHard :
    PSPACEHard encUndirectedEdgeGeography UndirectedEdgeGeography :=
  TQBFCNF_pspaceHard.trans polyTimeReducible_TQBFCNF_UndirectedEdgeGeography

/-- **Undirected Edge Geography is `PSPACE`-complete**. -/
theorem UndirectedEdgeGeography_pspaceComplete :
    PSPACEComplete encUndirectedEdgeGeography UndirectedEdgeGeography :=
  ⟨UndirectedEdgeGeography_mem_PSPACE, UndirectedEdgeGeography_pspaceHard⟩

end Cslib.Complexity
