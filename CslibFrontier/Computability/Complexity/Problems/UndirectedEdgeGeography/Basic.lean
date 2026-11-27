module

public import CslibFrontier.Computability.Complexity.Classes.Alternation.TQBF
public import CslibFrontier.Computability.Complexity.Classes.Space.GeneralizedGeography.Membership
public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Data.Sym.Sym2
import CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Tactic.EncLen

/-!
# Undirected Edge Geography

**Undirected Edge Geography** (UEG) is played on a finite undirected graph
(`Cslib.Complexity.Graph` interpreted via `Cslib.Complexity.Graph.toSimpleGraph`) with a token on a
declared starting vertex. Two players alternately move the token along an incident undirected edge
to a declared vertex, deleting the traversed edge after each move; the first player unable to move
loses. Unlike vertex geography, vertices may be revisited as long as unused incident edges remain.

Every move consumes a previously unused undirected edge of the graph, so plays terminate in at most
`|G.edges|` moves, and the winner is characterized by backward induction (`edgeGeographyWins_iff`).
Because a play has at most `|G.edges|` moves and each move is verified in polynomial time,
Undirected Edge Geography lies in `PSPACE` via `Cslib.Complexity.IsGameVerifier.mem_PSPACE`.

## Main definitions

* `Cslib.Complexity.UndirectedEdgeGeography.edgeSet`: the finite set of undirected edges
  connecting declared vertices of a `Cslib.Complexity.Graph`.
* `Cslib.Complexity.UndirectedEdgeGeography.EdgeGeographyWins`: backward-induction winning
  predicate for the player to move.
* `Cslib.Complexity.UndirectedEdgeGeographyInstance`: instance `(graph, start)` of Undirected
  Edge Geography.
* `Cslib.Complexity.encUndirectedEdgeGeography`: polynomial-time binary encoding of
  `UndirectedEdgeGeographyInstance`.
* `Cslib.Complexity.UndirectedEdgeGeography`: the set of instances on which the first player has
  a winning strategy.

## Main results

* `Cslib.Complexity.UndirectedEdgeGeography.edgeGeographyWins_iff`: backward induction
  characterization of winning positions.
* `Cslib.Complexity.UndirectedEdgeGeography.edgeGeographyWins_congr`: invariance under
  coextensive used-edge lists.
* `Cslib.Complexity.UndirectedEdgeGeography_mem_PSPACE`: Undirected Edge Geography belongs to
  `PSPACE`.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Turing.MultiTapeTM

namespace UndirectedEdgeGeography

/-- The undirected edges of `G` as unordered pairs `Sym2 ℕ`, collected from `G.edges`. -/
@[expose]
def edgeFinset (G : Graph) : Finset (Sym2 ℕ) :=
  (G.edges.map fun e => s(e.1, e.2)).toFinset

/-- A legal undirected edge move `(v, w)` belongs to `edgeFinset G`. -/
theorem sym2_mem_edgeFinset_of_adj {G : Graph} {v w : ℕ} (h : G.toSimpleGraph.Adj v w) :
    s(v, w) ∈ edgeFinset G := by
  rw [Graph.toSimpleGraph_adj] at h
  simp only [edgeFinset, List.mem_toFinset, List.mem_map]
  rcases h.2 with hvw | hwv
  · exact ⟨(v, w), hvw, rfl⟩
  · exact ⟨(w, v), hwv, Sym2.eq_swap⟩

/-- Consuming a previously unused undirected edge strictly decreases the number of remaining
undirected edges. -/
theorem card_edgeFinset_sdiff_cons_lt {G : Graph} {used : List (Sym2 ℕ)} {v w : ℕ}
    (hadj : G.toSimpleGraph.Adj v w) (hused : s(v, w) ∉ used) :
    (edgeFinset G \ (s(v, w) :: used).toFinset).card <
      (edgeFinset G \ used.toFinset).card := by
  rw [List.toFinset_cons, Finset.sdiff_insert]
  exact Finset.card_erase_lt_of_mem
    (Finset.mem_sdiff.2 ⟨sym2_mem_edgeFinset_of_adj hadj,
      fun h => hused (List.mem_toFinset.1 h)⟩)

/-- **Undirected Edge Geography**: with the token at `v` and undirected edges `used` already
traversed, the player to move wins when there is a declared neighbor `w` along an unused
undirected edge `s(v, w)` from which the opponent does not win. -/
@[expose]
def EdgeGeographyWins (G : Graph) (used : List (Sym2 ℕ)) (v : ℕ) : Prop :=
  ∃ w, ∃ _ : G.toSimpleGraph.Adj v w ∧ w ∈ G.vertices ∧ s(v, w) ∉ used,
    ¬EdgeGeographyWins G (s(v, w) :: used) w
termination_by (edgeFinset G \ used.toFinset).card
decreasing_by rename_i h; exact card_edgeFinset_sdiff_cons_lt h.1 h.2.2

/-- **Backward induction of Undirected Edge Geography.** -/
theorem edgeGeographyWins_iff {G : Graph} {used : List (Sym2 ℕ)} {v : ℕ} :
    EdgeGeographyWins G used v ↔
      ∃ w, G.toSimpleGraph.Adj v w ∧ w ∈ G.vertices ∧ s(v, w) ∉ used ∧
        ¬EdgeGeographyWins G (s(v, w) :: used) w := by
  rw [EdgeGeographyWins]
  simp only [exists_prop, and_assoc]

/-- The player to move loses iff every legal move leads to a winning position for the opponent. -/
theorem not_edgeGeographyWins_iff {G : Graph} {used : List (Sym2 ℕ)} {v : ℕ} :
    ¬EdgeGeographyWins G used v ↔
      ∀ w, G.toSimpleGraph.Adj v w → w ∈ G.vertices → s(v, w) ∉ used →
        EdgeGeographyWins G (s(v, w) :: used) w := by
  rw [edgeGeographyWins_iff]
  simp only [not_exists, not_and, not_not]

/-- Only the set of traversed undirected edges matters. -/
theorem edgeGeographyWins_congr {G : Graph} {used used' : List (Sym2 ℕ)}
    (h : ∀ e, e ∈ used ↔ e ∈ used') (v : ℕ) :
    EdgeGeographyWins G used v ↔ EdgeGeographyWins G used' v := by
  fun_induction EdgeGeographyWins G used v generalizing used' with
  | case1 used v ih =>
    have hcons (e : Sym2 ℕ) (u : Sym2 ℕ) : u ∈ e :: used ↔ u ∈ e :: used' := by
      simp only [List.mem_cons, h]
    rw [EdgeGeographyWins]
    refine exists_congr fun w => ⟨fun ⟨hc, hl⟩ => ?_, fun ⟨hc, hl⟩ => ?_⟩
    · exact ⟨⟨hc.1, hc.2.1, (not_congr (h _)).1 hc.2.2⟩, (ih w hc (hcons _)).not.1 hl⟩
    · have hc' : G.toSimpleGraph.Adj v w ∧ w ∈ G.vertices ∧ s(v, w) ∉ used :=
        ⟨hc.1, hc.2.1, (not_congr (h _)).2 hc.2.2⟩
      exact ⟨hc', (ih w hc' (hcons _)).not.2 hl⟩

/-- A graph has at most `G.edges.length` remaining unused undirected edges. -/
theorem card_edgeFinset_sdiff_le (G : Graph) (used : List (Sym2 ℕ)) :
    (edgeFinset G \ used.toFinset).card ≤ G.edges.length := by
  calc (edgeFinset G \ used.toFinset).card
      ≤ (edgeFinset G).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ (G.edges.map fun e => s(e.1, e.2)).length := List.toFinset_card_le _
    _ = G.edges.length := List.length_map _

end UndirectedEdgeGeography

/-- An instance `(graph, start)` of **Undirected Edge Geography**. -/
@[ext]
structure UndirectedEdgeGeographyInstance where
  /-- The undirected graph on which the game is played. -/
  graph : Graph
  /-- The starting vertex of the token. -/
  start : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `UndirectedEdgeGeographyInstance` as `(graph, start)`. -/
enc_structure encUndirectedEdgeGeography : UndirectedEdgeGeographyInstance where
  graph : encGraph,
  start : encNat

attribute [fun_prop] encUndirectedEdgeGeography_graph_polyTime
  encUndirectedEdgeGeography_start_polyTime encUndirectedEdgeGeography_mk_polyTime

/-- **Undirected Edge Geography**: instances `(G, d)` with `d ∈ G.vertices` on which the first
player has a winning strategy. -/
@[expose]
def UndirectedEdgeGeography : Set UndirectedEdgeGeographyInstance :=
  {x | x.start ∈ x.graph.vertices ∧
    UndirectedEdgeGeography.EdgeGeographyWins x.graph [] x.start}

/-- Membership characterization for `UndirectedEdgeGeography`. -/
theorem mem_UndirectedEdgeGeography {x : UndirectedEdgeGeographyInstance} :
    x ∈ UndirectedEdgeGeography ↔
      x.start ∈ x.graph.vertices ∧
        UndirectedEdgeGeography.EdgeGeographyWins x.graph [] x.start :=
  Iff.rfl

/-- On a graph without edges, the first player has no legal move and loses. -/
theorem notMem_UndirectedEdgeGeography_of_nil {V : List ℕ} {s : ℕ} :
    (⟨⟨V, []⟩, s⟩ : UndirectedEdgeGeographyInstance) ∉ UndirectedEdgeGeography := by
  rw [mem_UndirectedEdgeGeography, UndirectedEdgeGeography.edgeGeographyWins_iff]
  simp [Graph.toSimpleGraph_adj]

namespace UndirectedEdgeGeography

open ComputableInPolyTime GeneralizedGeography

/-- Directed-pair representation of used undirected edges: `s(v, w)` is used iff `(v, w)` or
`(w, v)` lies in `used`. -/
@[expose]
def usedSym2 (used : List (ℕ × ℕ)) : List (Sym2 ℕ) :=
  used.map fun e => s(e.1, e.2)

theorem mem_usedSym2_iff {used : List (ℕ × ℕ)} {v w : ℕ} :
    s(v, w) ∈ usedSym2 used ↔ (v, w) ∈ used ∨ (w, v) ∈ used := by
  simp only [usedSym2, List.mem_map, Sym2.eq_iff, Prod.exists]
  constructor
  · rintro ⟨a, b, hmem, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl hmem
    · exact Or.inr hmem
  · rintro (h | h)
    · exact ⟨v, w, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨w, v, h, Or.inr ⟨rfl, rfl⟩⟩

/-- The undirected edge at index `i` (directed from `v` if `dir = false`, or reversed if
`dir = true`). A move of index `j < 2 * G.edges.length` selects edge `j / 2` in orientation
`j % 2 == 1`. -/
@[expose]
def edgeTarget (G : Graph) (_v j : ℕ) : ℕ :=
  let e := arc G (j / 2)
  if j % 2 == 0 then e.2 else e.1

/-- The undirected edge move of index `j` is legal from `v` given traversed directed pairs
`used`. -/
@[expose]
def legalMove (G : Graph) (used : List (ℕ × ℕ)) (v j : ℕ) : Bool :=
  let e := arc G (j / 2)
  let src := if j % 2 == 0 then e.1 else e.2
  let dst := if j % 2 == 0 then e.2 else e.1
  decide (j / 2 < G.edges.length) && decide (src = v) && decide (dst ≠ v) &&
    decide (dst ∈ G.vertices) && !decide ((v, dst) ∈ used) && !decide ((dst, v) ∈ used)

theorem legalMove_eq_true_iff {G : Graph} {used : List (ℕ × ℕ)} {v j : ℕ} :
    legalMove G used v j = true ↔
      ∃ h : j / 2 < G.edges.length,
        let e := G.edges[j / 2]
        let src := if j % 2 == 0 then e.1 else e.2
        let dst := if j % 2 == 0 then e.2 else e.1
        src = v ∧ dst ≠ v ∧ dst ∈ G.vertices ∧ s(v, dst) ∉ usedSym2 used := by
  simp only [legalMove, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, mem_usedSym2_iff, not_or, and_assoc]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    simpa only [arc, List.getD_eq_getElem _ _ hi] using h
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    simpa only [arc, List.getD_eq_getElem _ _ hi] using h

private def moveIndicator (B j : ℕ) : List Bool :=
  List.replicate j false ++ true :: List.replicate (B - j - 1) false

private theorem length_moveIndicator {B j : ℕ} (h : j < B) :
    (moveIndicator B j).length = B := by
  simp only [moveIndicator, List.length_append, List.length_replicate, List.length_cons]
  omega

private theorem choice_moveIndicator (B j : ℕ) : choice (moveIndicator B j) = j := by
  rw [choice, moveIndicator, List.idxOf_append_of_notMem (by simp), List.idxOf_cons_self]
  simp

/-- Legal move indices correspond 1-to-1 with legal undirected edge moves in `EdgeGeographyWins`. -/
theorem exists_legalMove_iff {G : Graph} {used : List (ℕ × ℕ)} {v : ℕ} {R : ℕ → Prop} :
    (∃ x : List Bool, x.length = 2 * G.edges.length ∧
        legalMove G used v (choice x) = true ∧ R (edgeTarget G v (choice x))) ↔
      ∃ w, G.toSimpleGraph.Adj v w ∧ w ∈ G.vertices ∧ s(v, w) ∉ usedSym2 used ∧ R w := by
  constructor
  · rintro ⟨x, -, hleg, hR⟩
    obtain ⟨hi, hsrc, hne, hmem, hnot⟩ := legalMove_eq_true_iff.1 hleg
    have harc : arc G (choice x / 2) = G.edges[choice x / 2] :=
      List.getD_eq_getElem _ _ hi
    refine ⟨edgeTarget G v (choice x), ?_, ?_, ?_, hR⟩
    · rw [Graph.toSimpleGraph_adj]
      dsimp only [edgeTarget]
      rw [harc]
      refine ⟨hne.symm, ?_⟩
      split_ifs at hsrc ⊢ with hmod
      · left; rw [← hsrc]; exact List.getElem_mem hi
      · right; rw [← hsrc]; exact List.getElem_mem hi
    · dsimp only [edgeTarget]; rw [harc]; exact hmem
    · dsimp only [edgeTarget]; rw [harc]; exact hnot
  · rintro ⟨w, hadj, hw, hnot, hR⟩
    rw [Graph.toSimpleGraph_adj] at hadj
    obtain ⟨hne, hedge⟩ := hadj
    rcases hedge with hvw | hwv
    · obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hvw
      refine ⟨moveIndicator (2 * G.edges.length) (2 * i), length_moveIndicator (by omega), ?_, ?_⟩
      · rw [choice_moveIndicator]
        refine legalMove_eq_true_iff.2 ⟨by omega, ?_⟩
        simp only [show 2 * i / 2 = i by omega, show 2 * i % 2 = 0 by omega,
          beq_self_eq_true, ↓reduceIte, hei]
        exact ⟨trivial, hne.symm, hw, hnot⟩
      · rw [choice_moveIndicator]
        dsimp only [edgeTarget, arc]
        rw [show 2 * i / 2 = i by omega, show 2 * i % 2 = 0 by omega,
          List.getD_eq_getElem _ _ hi, hei]
        exact hR
    · obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hwv
      refine ⟨moveIndicator (2 * G.edges.length) (2 * i + 1),
        length_moveIndicator (by omega), ?_, ?_⟩
      · rw [choice_moveIndicator]
        refine legalMove_eq_true_iff.2 ⟨by omega, ?_⟩
        simp only [show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega,
          Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, hei]
        exact ⟨trivial, hne.symm, hw, hnot⟩
      · rw [choice_moveIndicator]
        dsimp only [edgeTarget, arc]
        rw [show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega,
          List.getD_eq_getElem _ _ hi, hei]
        exact hR

/-- Universal counterpart of `exists_legalMove_iff`. -/
theorem forall_legalMove_iff {G : Graph} {used : List (ℕ × ℕ)} {v : ℕ} {R : ℕ → Prop} :
    (∀ y : List Bool, y.length = 2 * G.edges.length →
        legalMove G used v (choice y) = true → R (edgeTarget G v (choice y))) ↔
      ∀ w, G.toSimpleGraph.Adj v w → w ∈ G.vertices → s(v, w) ∉ usedSym2 used → R w := by
  have h := not_iff_not.mpr
    (exists_legalMove_iff (G := G) (used := used) (v := v) (R := fun w => ¬R w))
  simpa only [not_exists, not_and, Classical.not_not] using h

/-- A play state during replay: optional winner, whose turn (`true` = first player), list of used
directed edges, and current vertex. -/
abbrev EdgePlay : Type := Option Bool × Bool × List (ℕ × ℕ) × ℕ

/-- Transition for one move represented by `bits`. -/
@[expose]
def nextMove (G : Graph) (first : Bool) (used : List (ℕ × ℕ)) (v : ℕ) (bits : List Bool) :
    EdgePlay :=
  if legalMove G used v (choice bits) then
    let w := edgeTarget G v (choice bits)
    (none, !first, (v, w) :: used, w)
  else (some !first, first, used, v)

/-- Transition for one block of `2 * B` single-bit moves. -/
@[expose]
def stepBlock (G : Graph) (B : ℕ) (st : EdgePlay) (block : List Bool) : EdgePlay :=
  if st.1.isSome then st
  else nextMove G st.2.1 st.2.2.1 st.2.2.2 (moverBits B st.2.1 block)

private theorem foldl_stepBlock_some (G : Graph) (B : ℕ) (b : Bool)
    (rest : Bool × List (ℕ × ℕ) × ℕ) :
    ∀ bs : List (List Bool), bs.foldl (stepBlock G B) (some b, rest) = (some b, rest)
  | [] => rfl
  | _ :: bs => by
    rw [List.foldl_cons, stepBlock, ite_eq_left (show (some b).isSome = true from rfl)]
    exact foldl_stepBlock_some G B b rest bs

private theorem moverBits_take_eq (B : ℕ) (first : Bool) (z : List Bool) :
    moverBits B first (z.take (2 * B)) = moverBits B first z := by
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt (by split <;> omega)]

private theorem blocks_succ_eq (B R : ℕ) (z : List Bool) :
    blocks B (R + 1) z = z.take (2 * B) :: blocks B R (z.drop (2 * B)) := by
  simp only [blocks, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero,
    List.drop_zero]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply, List.drop_drop, Nat.succ_eq_add_one]
  congr 2
  ring

/-- **Game equivalence for Undirected Edge Geography**: replaying `r` blocks of `2 * B` moves
(`B = 2 * G.edges.length`) matches `EdgeGeographyWins` whenever fewer than `r` edges remain. -/
theorem alternation_foldl_stepBlock (G : Graph) :
    ∀ (r : ℕ) (first : Bool) (used : List (ℕ × ℕ)) (v : ℕ),
      (edgeFinset G \ (usedSym2 used).toFinset).card < r →
      (Alternation true (List.replicate (2 * (2 * G.edges.length) * r) 1)
          (fun z => ((blocks (2 * G.edges.length) r z).foldl
            (stepBlock G (2 * G.edges.length)) (none, first, used, v)).1.getD false = true) ↔
        if first then EdgeGeographyWins G (usedSym2 used) v
        else ¬EdgeGeographyWins G (usedSym2 used) v)
  | 0, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | r + 1, first, used, v, hr => by
    set B := 2 * G.edges.length
    have hsplit : List.replicate (2 * B * (r + 1)) 1 =
        List.replicate (2 * B) 1 ++ List.replicate (2 * B * r) 1 := by
      rw [← List.replicate_add]
      congr 1
      ring
    rw [hsplit]
    have hstep : ∀ z : List Bool,
        ((blocks B (r + 1) z).foldl (stepBlock G B) (none, first, used, v)).1.getD false =
          ((blocks B r (z.drop (2 * B))).foldl (stepBlock G B)
            (nextMove G first used v (moverBits B first z))).1.getD false := fun z => by
      rw [blocks_succ_eq, List.foldl_cons, stepBlock,
        ite_eq_right (show (none : Option Bool).isSome ≠ true from Bool.false_ne_true),
        moverBits_take_eq]
    simp only [hstep]
    have hlt_of_legal : ∀ (bits : List Bool), legalMove G used v (choice bits) = true →
        (edgeFinset G \ (usedSym2 ((v, edgeTarget G v (choice bits)) :: used)).toFinset).card
          < r := fun bits hleg => by
      obtain ⟨hi, hsrc, hne, _, hnot⟩ := legalMove_eq_true_iff.1 hleg
      have harc : arc G (choice bits / 2) = G.edges[choice bits / 2] :=
        List.getD_eq_getElem _ _ hi
      have hadj : G.toSimpleGraph.Adj v (edgeTarget G v (choice bits)) := by
        rw [Graph.toSimpleGraph_adj]
        dsimp only [edgeTarget]; rw [harc]
        refine ⟨hne.symm, ?_⟩
        split_ifs at hsrc ⊢ with hmod
        · left; rw [← hsrc]; exact List.getElem_mem hi
        · right; rw [← hsrc]; exact List.getElem_mem hi
      have hnot' : s(v, edgeTarget G v (choice bits)) ∉ usedSym2 used := by
        dsimp only [edgeTarget]; rw [harc]; exact hnot
      have hdec := card_edgeFinset_sdiff_cons_lt hadj hnot'
      have hcons : usedSym2 ((v, edgeTarget G v (choice bits)) :: used) =
          s(v, edgeTarget G v (choice bits)) :: usedSym2 used := rfl
      rw [hcons]
      omega
    cases first
    · rw [alternation_moverBits_false (F := fun y rest =>
        ((blocks B r rest).foldl (stepBlock G B)
          (nextMove G false used v y)).1.getD false = true)]
      simp only [Bool.false_eq_true, ↓reduceIte, not_edgeGeographyWins_iff]
      rw [← forall_legalMove_iff]
      refine forall_congr' fun y => forall_congr' fun _ => ?_
      unfold nextMove
      split_ifs with hleg
      · simp only [Bool.not_false, hleg, true_imp_iff]
        have ih := alternation_foldl_stepBlock G r true ((v, edgeTarget G v (choice y)) :: used)
          (edgeTarget G v (choice y)) (hlt_of_legal y hleg)
        simpa only [↓reduceIte, B, usedSym2, List.map_cons] using ih
      · simp [foldl_stepBlock_some, alternation_const, hleg]
    · rw [alternation_moverBits_true (F := fun x rest =>
        ((blocks B r rest).foldl (stepBlock G B)
          (nextMove G true used v x)).1.getD false = true)]
      simp only [↓reduceIte]
      rw [edgeGeographyWins_iff, ← exists_legalMove_iff]
      refine exists_congr fun x => and_congr_right fun _ => ?_
      unfold nextMove
      split_ifs with hleg
      · simp only [Bool.not_true, hleg, true_and]
        have ih := alternation_foldl_stepBlock G r false ((v, edgeTarget G v (choice x)) :: used)
          (edgeTarget G v (choice x)) (hlt_of_legal x hleg)
        simpa only [Bool.false_eq_true, ↓reduceIte, B, usedSym2, List.map_cons] using ih
      · simp [foldl_stepBlock_some, alternation_const, hleg]

/-- Polynomial-time game verifier for Undirected Edge Geography. -/
@[expose]
def verifier (x : UndirectedEdgeGeographyInstance × List Bool) : Bool :=
  let G := x.1.graph
  let B := 2 * G.edges.length
  let R := G.edges.length + 1
  decide (x.1.start ∈ G.vertices) &&
    ((blocks B R x.2).foldl (stepBlock G B) (none, true, [], x.1.start)).1.getD false

private theorem blocks_take_eq (B R : ℕ) (z : List Bool) :
    blocks B R (z.take (2 * B * R)) = blocks B R z := by
  refine List.map_congr_left fun r hr => ?_
  rw [List.mem_range] at hr
  rw [List.drop_take, List.take_take]
  congr 1
  have : 2 * B * r + 2 * B ≤ 2 * B * R := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hr
  omega

/-- `verifier` is a game verifier for `UndirectedEdgeGeography` with quadratic round bound. -/
theorem isGameVerifier_verifier :
    IsGameVerifier encUndirectedEdgeGeography (Polynomial.C 2 * (Polynomial.X + 1) ^ 2)
      verifier UndirectedEdgeGeography := by
  intro x
  set G := x.graph
  set B := 2 * G.edges.length
  set R := G.edges.length + 1
  have hlen : G.edges.length ≤ (encUndirectedEdgeGeography x).length := by
    have h₁ := length_le_length_encList (encPair encNat encNat) x.graph.edges
    have h₂ := length_le_encPair_left encGraph encNat (x.graph, x.start)
    rw [← encUndirectedEdgeGeography_apply] at h₂
    dsimp only [G]
    enc_len [encGraph_apply] at h₁ h₂
  have hle : 2 * B * R ≤ 2 * ((Polynomial.C 2 * (Polynomial.X + 1) ^ 2 : Polynomial ℕ).eval
      (encUndirectedEdgeGeography x).length) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, B, R]
    nlinarith
  rw [mem_UndirectedEdgeGeography, ← Nat.add_sub_cancel' hle, List.replicate_add]
  by_cases hstart : x.start ∈ G.vertices
  · have hver : ∀ z : List Bool, verifier (x, z) = true ↔
        ((blocks B R z).foldl (stepBlock G B)
          (none, true, [], x.start)).1.getD false = true := fun z => by
      simp only [verifier, hstart, decide_true, Bool.true_and, G, B, R]
    rw [alternation_append_iff (fun z => by
      rw [sum_replicate_one, hver, hver, blocks_take_eq])]
    simp only [hver]
    have hr : (edgeFinset G \ (usedSym2 []).toFinset).card < R := by
      have := card_edgeFinset_sdiff_le G []
      simp only [R, usedSym2, List.map_nil] at this ⊢; omega
    have hmain := alternation_foldl_stepBlock G R true [] x.start hr
    simp only [↓reduceIte, usedSym2, List.map_nil] at hmain
    exact ⟨fun ⟨_, hw⟩ => hmain.2 hw, fun hw => ⟨hstart, hmain.1 hw⟩⟩
  · have hver : ∀ z : List Bool, verifier (x, z) = false := fun z => by
      simp [verifier, hstart, G]
    simp only [hver, Bool.false_eq_true, alternation_const, iff_false, not_and]
    intro h; exact absurd h hstart

section PolyTime

private abbrev encEdgePlay : EdgePlay ↪ List Bool :=
  encPair (encOption encBool)
    (encPair encBool (encPair (encList (encPair encNat encNat)) encNat))

private theorem computableInPolyTime_nextMove :
    ComputableInPolyTime
      (fun p : (Graph × EdgePlay) × List Bool =>
        nextMove p.1.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2)
      (encPair (encPair encGraph encEdgePlay) (encList encBool)) encEdgePlay := by
  let encQ := encPair (encPair encGraph encEdgePlay) (encList encBool)
  have hG : ComputableInPolyTime (fun p : (Graph × EdgePlay) × List Bool => p.1.1)
      encQ encGraph := by fun_prop
  have hV : ComputableInPolyTime (fun p : (Graph × EdgePlay) × List Bool => p.1.1.vertices)
      encQ (encList encNat) := by fun_prop
  have hE : ComputableInPolyTime (fun p : (Graph × EdgePlay) × List Bool => p.1.1.edges)
      encQ (encList (encPair encNat encNat)) := by fun_prop
  have hfirst : ComputableInPolyTime (fun p : (Graph × EdgePlay) × List Bool => p.1.2.2.1)
      encQ encBool := by fun_prop
  have hused : ComputableInPolyTime (fun p : (Graph × EdgePlay) × List Bool => p.1.2.2.2.1)
      encQ (encList (encPair encNat encNat)) := by fun_prop
  have hv : ComputableInPolyTime (fun p : (Graph × EdgePlay) × List Bool => p.1.2.2.2.2)
      encQ encNat := by fun_prop
  have hj : ComputableInPolyTime (fun p : (Graph × EdgePlay) × List Bool => choice p.2)
      encQ encUnary := idxOfWithInput (snd _ _) (const true)
  have hdivmod : ComputableInPolyTime
      (fun p : (Graph × EdgePlay) × List Bool => (choice p.2 / 2, choice p.2 % 2 == 0))
      encQ (encPair encUnary encBool) := by
    have hstep : ComputableInPolyTime
        (fun st : (((Graph × EdgePlay) × List Bool) × (ℕ × Bool)) × ℕ =>
          (if st.1.2.2 then st.1.2.1 else st.1.2.1 + 1, !st.1.2.2))
        (encPair (encPair encQ (encPair encUnary encBool)) encUnary)
        (encPair encUnary encBool) := by
      have hfst : ComputableInPolyTime
          (fun st : (((Graph × EdgePlay) × List Bool) × (ℕ × Bool)) × ℕ => st.1.2.1)
          (encPair (encPair encQ (encPair encUnary encBool)) encUnary) encUnary :=
        (fst _ _).comp ((snd _ _).comp (fst _ _))
      have hsnd : ComputableInPolyTime
          (fun st : (((Graph × EdgePlay) × List Bool) × (ℕ × Bool)) × ℕ => st.1.2.2)
          (encPair (encPair encQ (encPair encUnary encBool)) encUnary) encBool :=
        (snd _ _).comp ((snd _ _).comp (fst _ _))
      have h1 : ComputableInPolyTime
          (fun st : (((Graph × EdgePlay) × List Bool) × (ℕ × Bool)) × ℕ =>
            if st.1.2.2 then st.1.2.1 else st.1.2.1 + 1)
          (encPair (encPair encQ (encPair encUnary encBool)) encUnary) encUnary :=
        ite' hsnd hfst (unary_add.comp (hfst.prod (const 1)))
      have h2 : ComputableInPolyTime
          (fun st : (((Graph × EdgePlay) × List Bool) × (ℕ × Bool)) × ℕ => !st.1.2.2)
          (encPair (encPair encQ (encPair encUnary encBool)) encUnary) encBool :=
        bool_not.comp hsnd
      exact h1.prod h2
    have hfold := foldlWithInput_of_bounded_growth
      (encA := encUnary) (encL := encList encUnary)
      (step := fun (_ : (Graph × EdgePlay) × List Bool) (st : ℕ × Bool) (_ : ℕ) =>
        (if st.2 then st.1 else st.1 + 1, !st.2))
      (const (0, true)) ⟨range.comp hj, hstep, inferInstance, inferInstance⟩
      (growth := fun _ => 2) ⟨PolyBounded.const 2, fun _ st _ _ => by
        obtain ⟨q, b⟩ := st
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> enc_len⟩
    have hspec : ∀ n : ℕ, (List.range n).foldl
        (fun (st : ℕ × Bool) (_ : ℕ) => (if st.2 then st.1 else st.1 + 1, !st.2)) (0, true) =
          (n / 2, n % 2 == 0) := by
      intro n
      induction n with
      | zero => rfl
      | succ k ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
        rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · have h1 : (m + m) / 2 = m := by omega
          have h2 : (m + m) % 2 = 0 := by omega
          have h3 : (m + m + 1) / 2 = m := by omega
          have h4 : (m + m + 1) % 2 = 1 := by omega
          simp [h1, h2, h3, h4]
        · have h1 : (2 * m + 1) / 2 = m := by omega
          have h2 : (2 * m + 1) % 2 = 1 := by omega
          have h3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          have h4 : (2 * m + 1 + 1) % 2 = 0 := by omega
          simp [h1, h2, h3, h4]
    exact hfold.of_enc_eq fun p => congrArg (encPair encUnary encBool) (hspec (choice p.2)).symm
  have hj2 : ComputableInPolyTime (fun p : (Graph × EdgePlay) × List Bool => choice p.2 / 2)
      encQ encUnary := (fst _ _).comp hdivmod
  have hmod : ComputableInPolyTime
      (fun p : (Graph × EdgePlay) × List Bool => (choice p.2 % 2 == 0)) encQ encBool :=
    (snd _ _).comp hdivmod
  have hN : ComputableInPolyTime (fun p : (Graph × EdgePlay) × List Bool => p.1.1.edges.length)
      encQ encUnary := (length_list _).comp hE
  have harc : ComputableInPolyTime
      (fun p : (Graph × EdgePlay) × List Bool => arc p.1.1 (choice p.2 / 2)) encQ
      (encPair encNat encNat) := (listGetD (0, 0)).comp (hE.prod hj2)
  have hsrc : ComputableInPolyTime
      (fun p : (Graph × EdgePlay) × List Bool =>
        if choice p.2 % 2 == 0 then (arc p.1.1 (choice p.2 / 2)).1
        else (arc p.1.1 (choice p.2 / 2)).2) encQ encNat :=
    ite' hmod ((fst _ _).comp harc) ((snd _ _).comp harc)
  have hdst : ComputableInPolyTime
      (fun p : (Graph × EdgePlay) × List Bool => edgeTarget p.1.1 p.1.2.2.2.2 (choice p.2))
      encQ encNat :=
    ite' hmod ((snd _ _).comp harc) ((fst _ _).comp harc)
  have hmemV : ComputableInPolyTime
      (fun p : (Graph × EdgePlay) × List Bool =>
        decide (edgeTarget p.1.1 p.1.2.2.2.2 (choice p.2) ∈ p.1.1.vertices)) encQ encBool := by
    simp only [List.decide_mem_eq_any]
    exact anyWithInput hV (decide_eq' (snd _ _) (hdst.comp (fst _ _)))
  have hmemU1 : ComputableInPolyTime
      (fun p : (Graph × EdgePlay) × List Bool =>
        decide ((p.1.2.2.2.2, edgeTarget p.1.1 p.1.2.2.2.2 (choice p.2)) ∈ p.1.2.2.2.1))
      encQ encBool := by
    simp only [List.decide_mem_eq_any]
    exact anyWithInput hused (decide_eq' (snd _ _) ((hv.prod hdst).comp (fst _ _)))
  have hmemU2 : ComputableInPolyTime
      (fun p : (Graph × EdgePlay) × List Bool =>
        decide ((edgeTarget p.1.1 p.1.2.2.2.2 (choice p.2), p.1.2.2.2.2) ∈ p.1.2.2.2.1))
      encQ encBool := by
    simp only [List.decide_mem_eq_any]
    exact anyWithInput hused (decide_eq' (snd _ _) ((hdst.prod hv).comp (fst _ _)))
  have hlegal : ComputableInPolyTime
      (fun p : (Graph × EdgePlay) × List Bool =>
        legalMove p.1.1 p.1.2.2.2.1 p.1.2.2.2.2 (choice p.2)) encQ encBool := by
    unfold legalMove
    have hlt := (unary_lt.comp (hj2.prod hN))
    have hsrceq := decide_eq' hsrc hv
    have hdne := bool_not.comp (decide_eq' hdst hv)
    have hdstne : ComputableInPolyTime
        (fun p : (Graph × EdgePlay) × List Bool =>
          decide (edgeTarget p.1.1 p.1.2.2.2.2 (choice p.2) ≠ p.1.2.2.2.2)) encQ encBool :=
      hdne.of_enc_eq fun p => congrArg encBool (by simp [edgeTarget])
    have h1 := bool_and.comp (hlt.prod hsrceq)
    have h2 := bool_and.comp (h1.prod hdstne)
    have h3 := bool_and.comp (h2.prod hmemV)
    have h4 := bool_and.comp (h3.prod (bool_not.comp hmemU1))
    have h5 := bool_and.comp (h4.prod (bool_not.comp hmemU2))
    exact h5.of_enc_eq fun p => congrArg encBool (by simp [edgeTarget])
  unfold nextMove
  exact ite' hlegal
    ((const none).prod ((bool_not.comp hfirst).prod ((cons' (hv.prod hdst) hused).prod hdst)))
    (((optionSome encBool).comp (bool_not.comp hfirst)).prod (hfirst.prod (hused.prod hv)))

private theorem length_encNat_le_of_mem_edges {G : Graph} {e : ℕ × ℕ} (he : e ∈ G.edges) :
    (encNat e.1).length ≤ (encGraph G).length ∧ (encNat e.2).length ≤ (encGraph G).length := by
  have h₁ := sum_length_le_length_encList (encPair encNat encNat) G.edges
  have h₂ := List.le_sum_of_mem (List.mem_map_of_mem (f := fun a =>
    (encPair encNat encNat a).length) he)
  have h₃ := length_le_encPair_left encNat encNat e
  have h₄ := length_le_encPair_right encNat encNat e
  constructor <;> enc_len [encGraph_apply] at h₁ h₂ h₃ h₄ ⊢

private theorem length_encEdgePlay_stepBlock_le (G : Graph) (B : ℕ) (st : EdgePlay)
    (block : List Bool) :
    (encEdgePlay (stepBlock G B st block)).length ≤
      (encEdgePlay st).length + 12 * (encGraph G).length + 12 := by
  obtain ⟨o, first, used, v⟩ := st
  unfold stepBlock
  split_ifs with ho
  · omega
  · have ho' : o = none := by cases o <;> simp_all
    subst ho'
    unfold nextMove
    split_ifs with hl
    · obtain ⟨hi, hsrc, -, -, -⟩ := legalMove_eq_true_iff.1 hl
      dsimp only at hi hsrc
      have hmem := List.getElem_mem hi
      obtain ⟨h1, h2⟩ := length_encNat_le_of_mem_edges hmem
      have harc : arc G (choice (moverBits B first block) / 2) =
          G.edges[choice (moverBits B first block) / 2] :=
        List.getD_eq_getElem _ _ hi
      have hdst_le : (encNat (edgeTarget G v (choice (moverBits B first block)))).length ≤
          (encGraph G).length := by
        dsimp only [edgeTarget]; rw [harc]; split_ifs <;> assumption
      have hv_le : (encNat v).length ≤ (encGraph G).length := by
        rw [← hsrc]; split_ifs <;> assumption
      enc_len [encList_cons] at hdst_le hv_le ⊢
    · enc_len

private abbrev encVerifierIn : UndirectedEdgeGeographyInstance × List Bool ↪ List Bool :=
  encPair encUndirectedEdgeGeography encBits

private abbrev encStepIn :
    (((UndirectedEdgeGeographyInstance × List Bool) × EdgePlay) × List Bool) ↪ List Bool :=
  encPair (encPair encVerifierIn encEdgePlay) encBits

/-- **The UEG game verifier is computable in polynomial time.** -/
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encUndirectedEdgeGeography encBits) encBool := by
  have hG : ComputableInPolyTime
      (fun x : UndirectedEdgeGeographyInstance × List Bool => x.1.graph)
      encVerifierIn encGraph := by fun_prop
  have hV : ComputableInPolyTime
      (fun x : UndirectedEdgeGeographyInstance × List Bool => x.1.graph.vertices)
      encVerifierIn (encList encNat) := by fun_prop
  have hE : ComputableInPolyTime
      (fun x : UndirectedEdgeGeographyInstance × List Bool => x.1.graph.edges)
      encVerifierIn (encList (encPair encNat encNat)) := by fun_prop
  have hstart : ComputableInPolyTime
      (fun x : UndirectedEdgeGeographyInstance × List Bool => x.1.start)
      encVerifierIn encNat := by fun_prop
  have hlenE : ComputableInPolyTime
      (fun x : UndirectedEdgeGeographyInstance × List Bool => x.1.graph.edges.length)
      encVerifierIn encUnary := (length_list _).comp hE
  have hB : ComputableInPolyTime
      (fun x : UndirectedEdgeGeographyInstance × List Bool => 2 * x.1.graph.edges.length)
      encVerifierIn encUnary := unary_mul.comp ((const 2).prod hlenE)
  have hR : ComputableInPolyTime
      (fun x : UndirectedEdgeGeographyInstance × List Bool => x.1.graph.edges.length + 1)
      encVerifierIn encUnary := unary_add.comp (hlenE.prod (const 1))
  have hblocks : ComputableInPolyTime
      (fun x : UndirectedEdgeGeographyInstance × List Bool =>
        blocks (2 * x.1.graph.edges.length) (x.1.graph.edges.length + 1) x.2)
      encVerifierIn (encList encBits) := by
    have h2B : ComputableInPolyTime
        (fun p : (UndirectedEdgeGeographyInstance × List Bool) × ℕ =>
          2 * (2 * p.1.1.graph.edges.length))
        (encPair encVerifierIn encUnary) encUnary :=
      unary_mul.comp ((const 2).prod (hB.comp (fst _ _)))
    unfold blocks
    exact mapWithInput (range.comp hR) (bitsTakeWithInput (bitsDropWithInput
      ((snd _ _).comp (fst _ _)) (unary_mul.comp (h2B.prod (snd _ _)))) h2B)
  have hinit : ComputableInPolyTime
      (fun x : UndirectedEdgeGeographyInstance × List Bool =>
        ((none, true, [], x.1.start) : EdgePlay))
      encVerifierIn encEdgePlay := by fun_prop
  have hstep : ComputableInPolyTime
      (fun p : (((UndirectedEdgeGeographyInstance × List Bool) × EdgePlay) × List Bool) =>
        stepBlock p.1.1.1.graph (2 * p.1.1.1.graph.edges.length) p.1.2 p.2)
      encStepIn encEdgePlay := by
    have hst : ComputableInPolyTime
        (fun p : (((UndirectedEdgeGeographyInstance × List Bool) × EdgePlay) × List Bool) =>
          p.1.2) encStepIn encEdgePlay := by fun_prop
    have hX : ComputableInPolyTime
        (fun p : (((UndirectedEdgeGeographyInstance × List Bool) × EdgePlay) × List Bool) =>
          p.1.1) encStepIn encVerifierIn := by fun_prop
    have hbits : ComputableInPolyTime
        (fun p : (((UndirectedEdgeGeographyInstance × List Bool) × EdgePlay) × List Bool) =>
          moverBits (2 * p.1.1.1.graph.edges.length) p.1.2.2.1 p.2)
        encStepIn (encList encBool) :=
      computableInPolyTime_moverBits (hB.comp hX) (by fun_prop) (snd _ _)
    have hpair : ComputableInPolyTime
        (fun p : (((UndirectedEdgeGeographyInstance × List Bool) × EdgePlay) × List Bool) =>
          ((p.1.1.1.graph, p.1.2),
            moverBits (2 * p.1.1.1.graph.edges.length) p.1.2.2.1 p.2))
        encStepIn (encPair (encPair encGraph encEdgePlay) (encList encBool)) :=
      ((hG.comp hX).prod hst).prod hbits
    have hnext : ComputableInPolyTime
        (fun p : (((UndirectedEdgeGeographyInstance × List Bool) × EdgePlay) × List Bool) =>
          nextMove p.1.1.1.graph p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2
            (moverBits (2 * p.1.1.1.graph.edges.length) p.1.2.2.1 p.2))
        encStepIn encEdgePlay := by
      have h := computableInPolyTime_nextMove.comp hpair
      simp only [Function.comp_def] at h
      exact h
    have hsome : ComputableInPolyTime
        (fun p : (((UndirectedEdgeGeographyInstance × List Bool) × EdgePlay) × List Bool) =>
          p.1.2.1.isSome) encStepIn encBool := optionIsSome ((fst _ _).comp hst)
    unfold stepBlock
    exact ite' hsome hst hnext
  have hfold := foldlWithInput_of_bounded_growth (encA := encBits) (encL := encList encBits)
    (step := fun x : UndirectedEdgeGeographyInstance × List Bool =>
      stepBlock x.1.graph (2 * x.1.graph.edges.length))
    hinit ⟨hblocks, hstep, inferInstance, inferInstance⟩
    (growth := fun x => 12 * (encVerifierIn x).length + 12)
    ⟨((PolyBounded.const 12).mul .self).add (.const 12),
      fun x st b _ => (length_encEdgePlay_stepBlock_le _ _ st b).trans (by
        have h1 := length_le_encPair_left encUndirectedEdgeGeography encBits x
        have h2 := length_le_encPair_left encGraph encNat (x.1.graph, x.1.start)
        rw [← encUndirectedEdgeGeography_apply] at h2
        dsimp only [encVerifierIn] at h1 h2 ⊢
        omega)⟩
  have hstartMem : ComputableInPolyTime
      (fun x : UndirectedEdgeGeographyInstance × List Bool =>
        decide (x.1.start ∈ x.1.graph.vertices))
      encVerifierIn encBool := by
    simp only [List.decide_mem_eq_any]
    exact anyWithInput hV (decide_eq' (snd _ _) (hstart.comp (fst _ _)))
  unfold verifier
  exact bool_and.comp (hstartMem.prod (optionGetDWithInput ((fst _ _).comp hfold) (const false)))

end PolyTime

end UndirectedEdgeGeography

/-- **Undirected Edge Geography is in `PSPACE`** [Fraenkel, Scheinerman, and Ullman ]. -/
theorem UndirectedEdgeGeography_mem_PSPACE :
    UndirectedEdgeGeography ∈ PSPACE encUndirectedEdgeGeography :=
  UndirectedEdgeGeography.isGameVerifier_verifier.mem_PSPACE
    UndirectedEdgeGeography.computableInPolyTime_verifier

end Cslib.Complexity
