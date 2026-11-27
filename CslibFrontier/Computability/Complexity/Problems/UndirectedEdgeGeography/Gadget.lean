module

public import CslibFrontier.Computability.Complexity.Problems.UndirectedEdgeGeography.Basic
public import CslibFrontier.Computability.Complexity.Classes.Space.GeneralizedGeography.Reduction
public import CslibFrontier.Computability.Complexity.Classes.Space.TQBF.Prenex

/-!
# Variable-Gadget Graph for Undirected Edge Geography

Constructs the Fraenkel–Scheinerman–Ullman undirected graph
`Cslib.Complexity.UndirectedEdgeGeography.formulaGraph` from an alternating prenex CNF
instance `(xs, ψ)`, together with exact neighbor characterizations for all twelve disjoint
`Nat.pair`-tagged vertex families.

## Main definitions

* `Cslib.Complexity.UndirectedEdgeGeography.topNode`, `botNode`, `midNode`, `aNode`, `wNode`,
  `cNode`, `u1Node`, `mNode`, `u2Node`, `vNode`, `chooserNode`, `clauseNode`: disjoint vertex
  encodings.
* `Cslib.Complexity.UndirectedEdgeGeography.occClauses`, `segCount`, `branchEdges`,
  `diamondEdges`, `formulaEdges`, `formulaGraph`: the undirected reduction graph.
* `Cslib.Complexity.UndirectedEdgeGeography.reduce`: the reduction map from `PrenexCNF` to
  `UndirectedEdgeGeographyInstance`.

## Main results

* `Cslib.Complexity.UndirectedEdgeGeography.adj_aNode_iff`, `adj_cNode_iff`, `adj_wNode_iff`,
  `adj_midNode_iff`, `adj_mNode_iff`, `adj_vNode_iff`, `adj_u1Node_iff`, `adj_u2Node_iff`,
  `adj_botNode_iff`, `adj_topNode_iff`, `adj_chooserNode_iff`, `adj_clauseNode_iff`,
  `pair_sym2_eq`: exact neighbor characterizations and pair-equality helpers for `formulaGraph`.
-/

public section

namespace Cslib.Complexity

open Cslib.Complexity Cslib.Logic.PL

namespace UndirectedEdgeGeography

/-! ### Node encoding and graph construction -/

/-- Top vertex of variable gadget `j`. -/
@[expose] def topNode (j : ℕ) : ℕ := Nat.pair 0 j

/-- Bottom vertex of variable gadget `j`. -/
@[expose] def botNode (j : ℕ) : ℕ := Nat.pair 1 j

/-- Bridge midpoint after an even variable gadget `j`. -/
@[expose] def midNode (j : ℕ) : ℕ := Nat.pair 2 j

/-- Entry vertex `a(j, b)` on branch `b` of an even variable gadget `j`. -/
@[expose] def aNode (j : ℕ) (b : Bool) : ℕ := Nat.pair 3 (Nat.pair j b.toNat)

/-- Chord vertex `w(j, b)` on branch `b` of an even variable gadget `j`. -/
@[expose] def wNode (j : ℕ) (b : Bool) : ℕ := Nat.pair 4 (Nat.pair j b.toNat)

/-- Connector vertex `c(j, b)` on branch `b` of an even variable gadget `j`. -/
@[expose] def cNode (j : ℕ) (b : Bool) : ℕ := Nat.pair 5 (Nat.pair j b.toNat)

/-- First literal-segment vertex `u₁(j, b, k)`. -/
@[expose] def u1Node (j : ℕ) (b : Bool) (k : ℕ) : ℕ :=
  Nat.pair 6 (Nat.pair j (Nat.pair b.toNat k))

/-- Middle literal-segment vertex `m(j, b, k)`. -/
@[expose] def mNode (j : ℕ) (b : Bool) (k : ℕ) : ℕ :=
  Nat.pair 7 (Nat.pair j (Nat.pair b.toNat k))

/-- Second literal-segment vertex `u₂(j, b, k)`. -/
@[expose] def u2Node (j : ℕ) (b : Bool) (k : ℕ) : ℕ :=
  Nat.pair 8 (Nat.pair j (Nat.pair b.toNat k))

/-- Inter-segment connector vertex `v(j, b, k)`. -/
@[expose] def vNode (j : ℕ) (b : Bool) (k : ℕ) : ℕ :=
  Nat.pair 9 (Nat.pair j (Nat.pair b.toNat k))

/-- Clause-chooser vertex after the last variable gadget. -/
@[expose] def chooserNode : ℕ := Nat.pair 10 0

/-- Clause vertex for clause index `i`. -/
@[expose] def clauseNode (i : ℕ) : ℕ := Nat.pair 11 i

theorem topNode_eq_pair (j : ℕ) : topNode j = Nat.pair 0 j := rfl
theorem botNode_eq_pair (j : ℕ) : botNode j = Nat.pair 1 j := rfl
theorem midNode_eq_pair (j : ℕ) : midNode j = Nat.pair 2 j := rfl
theorem aNode_eq_pair (j : ℕ) (b : Bool) : aNode j b = Nat.pair 3 (Nat.pair j b.toNat) := rfl
theorem wNode_eq_pair (j : ℕ) (b : Bool) : wNode j b = Nat.pair 4 (Nat.pair j b.toNat) := rfl
theorem cNode_eq_pair (j : ℕ) (b : Bool) : cNode j b = Nat.pair 5 (Nat.pair j b.toNat) := rfl
theorem u1Node_eq_pair (j : ℕ) (b : Bool) (k : ℕ) :
    u1Node j b k = Nat.pair 6 (Nat.pair j (Nat.pair b.toNat k)) := rfl
theorem mNode_eq_pair (j : ℕ) (b : Bool) (k : ℕ) :
    mNode j b k = Nat.pair 7 (Nat.pair j (Nat.pair b.toNat k)) := rfl
theorem u2Node_eq_pair (j : ℕ) (b : Bool) (k : ℕ) :
    u2Node j b k = Nat.pair 8 (Nat.pair j (Nat.pair b.toNat k)) := rfl
theorem vNode_eq_pair (j : ℕ) (b : Bool) (k : ℕ) :
    vNode j b k = Nat.pair 9 (Nat.pair j (Nat.pair b.toNat k)) := rfl
theorem chooserNode_eq_pair : chooserNode = Nat.pair 10 0 := rfl
theorem clauseNode_eq_pair (i : ℕ) : clauseNode i = Nat.pair 11 i := rfl

@[simp] theorem topNode_inj {j₁ j₂ : ℕ} : topNode j₁ = topNode j₂ ↔ j₁ = j₂ := by
  simp [topNode]
@[simp] theorem botNode_inj {j₁ j₂ : ℕ} : botNode j₁ = botNode j₂ ↔ j₁ = j₂ := by
  simp [botNode]
@[simp] theorem midNode_inj {j₁ j₂ : ℕ} : midNode j₁ = midNode j₂ ↔ j₁ = j₂ := by
  simp [midNode]
@[simp] theorem clauseNode_inj {i₁ i₂ : ℕ} : clauseNode i₁ = clauseNode i₂ ↔ i₁ = i₂ := by
  simp [clauseNode]

/-- Clause indices `i < ψ.length` in which literal `(j, b)` (with `j = lastIdx xs v`) occurs. -/
@[expose]
def occClauses (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) : List ℕ :=
  (List.range ψ.length).filter fun i =>
    (ψ.getD i []).any fun l =>
      decide (l.1 ∈ xs) && decide (GeneralizedGeography.lastIdx xs l.1 = j) && (l.2 == b)

/-- Number of segments on branch `(j, b)` (always at least `1`). -/
@[expose]
def segCount (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) : ℕ :=
  max 1 (occClauses xs ψ j b).length

theorem one_le_segCount (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) :
    1 ≤ segCount xs ψ j b :=
  Nat.le_max_left 1 _

theorem length_occClauses_le_segCount (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) :
    (occClauses xs ψ j b).length ≤ segCount xs ψ j b :=
  Nat.le_max_right 1 _

theorem nodup_occClauses (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) :
    (occClauses xs ψ j b).Nodup :=
  (List.nodup_range).filter _

theorem mem_occClauses_iff {xs : List ℕ} {ψ : CNF ℕ} {j i : ℕ} {b : Bool} :
    i ∈ occClauses xs ψ j b ↔
      ∃ h : i < ψ.length, ∃ l ∈ ψ[i],
        l.1 ∈ xs ∧ GeneralizedGeography.lastIdx xs l.1 = j ∧ l.2 = b := by
  simp only [occClauses, List.mem_filter, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨hi, l, hl, ⟨hlx, hlj⟩, hlb⟩
    rw [List.getD_eq_getElem _ _ hi] at hl
    exact ⟨hi, l, hl, hlx, hlj, hlb⟩
  · rintro ⟨hi, l, hl, hlx, hlj, hlb⟩
    refine ⟨hi, l, ?_, ⟨hlx, hlj⟩, hlb⟩
    rw [List.getD_eq_getElem _ _ hi]
    exact hl

/-- Undirected edges along branch `b` of variable gadget `j` (internal segments + clause edges). -/
@[expose]
def branchEdges (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) : List (ℕ × ℕ) :=
  let occ := occClauses xs ψ j b
  let r := segCount xs ψ j b
  ((List.range r).flatMap fun k => [(u1Node j b k, mNode j b k), (mNode j b k, u2Node j b k)]) ++
  ((List.range (r - 1)).flatMap fun k =>
      [(u2Node j b k, vNode j b k), (vNode j b k, u1Node j b (k + 1))]) ++
  [(u2Node j b (r - 1), botNode j)] ++
  ((List.range occ.length).flatMap fun k =>
      let i := occ.getD k 0
      [(clauseNode i, u1Node j b k), (clauseNode i, u2Node j b k)])

/-- Undirected edges of variable gadget `j`. -/
@[expose]
def diamondEdges (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) : List (ℕ × ℕ) :=
  if j % 2 == 0 then
    ([false, true].flatMap fun b =>
      [(topNode j, aNode j b), (aNode j b, wNode j b), (topNode j, wNode j b),
        (wNode j b, cNode j b), (cNode j b, u1Node j b 0)] ++ branchEdges xs ψ j b) ++
    [(botNode j, midNode j), (midNode j, topNode (j + 1))]
  else
    ([false, true].flatMap fun b =>
      (topNode j, u1Node j b 0) :: branchEdges xs ψ j b) ++
    [(botNode j, topNode (j + 1))]

/-- All edges of the UEG reduction graph for `(xs, ψ)`. -/
@[expose]
def formulaEdges (xs : List ℕ) (ψ : CNF ℕ) : List (ℕ × ℕ) :=
  (List.range xs.length).flatMap (diamondEdges xs ψ) ++
  (topNode xs.length, chooserNode) ::
    ((List.range ψ.length).map fun i => (chooserNode, clauseNode i))

/-- The UEG reduction graph for quantified variables `xs` and CNF matrix `ψ`. -/
@[expose]
def formulaGraph (xs : List ℕ) (ψ : CNF ℕ) : Graph :=
  ⟨topNode 0 :: (formulaEdges xs ψ).flatMap fun e => [e.1, e.2], formulaEdges xs ψ⟩

/-- The polynomial-time reduction from `TQBFCNF` to `UndirectedEdgeGeography`. -/
@[expose]
def reduce (x : PrenexCNF) : UndirectedEdgeGeographyInstance :=
  if x.matrix.all (fun c => c.all fun l => decide (l.1 ∈ QBF.roundVars x.rounds)) then
    ⟨formulaGraph (QBF.roundVars x.rounds) x.matrix, topNode 0⟩
  else ⟨⟨[0], []⟩, 0⟩

theorem occClauses_eq_filter (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) :
    occClauses xs ψ j b =
      (List.range ψ.length).filter fun i =>
        (ψ.getD i []).any fun l =>
          decide (l.1 ∈ xs) && decide (GeneralizedGeography.lastIdx xs l.1 = j) && (l.2 == b) :=
  rfl

theorem segCount_eq_max (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) :
    segCount xs ψ j b = max 1 (occClauses xs ψ j b).length := rfl

theorem branchEdges_eq_append (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) (b : Bool) :
    branchEdges xs ψ j b =
      ((List.range (segCount xs ψ j b)).flatMap fun k =>
          [(u1Node j b k, mNode j b k), (mNode j b k, u2Node j b k)]) ++
      ((List.range (segCount xs ψ j b - 1)).flatMap fun k =>
          [(u2Node j b k, vNode j b k), (vNode j b k, u1Node j b (k + 1))]) ++
      [(u2Node j b (segCount xs ψ j b - 1), botNode j)] ++
      ((List.range (occClauses xs ψ j b).length).flatMap fun k =>
          let i := (occClauses xs ψ j b).getD k 0
          [(clauseNode i, u1Node j b k), (clauseNode i, u2Node j b k)]) := rfl

theorem diamondEdges_eq_ite (xs : List ℕ) (ψ : CNF ℕ) (j : ℕ) :
    diamondEdges xs ψ j =
      if j % 2 == 0 then
        ([false, true].flatMap fun b =>
          [(topNode j, aNode j b), (aNode j b, wNode j b), (topNode j, wNode j b),
            (wNode j b, cNode j b), (cNode j b, u1Node j b 0)] ++ branchEdges xs ψ j b) ++
        [(botNode j, midNode j), (midNode j, topNode (j + 1))]
      else
        ([false, true].flatMap fun b =>
          (topNode j, u1Node j b 0) :: branchEdges xs ψ j b) ++
        [(botNode j, topNode (j + 1))] := rfl

theorem formulaEdges_eq_append (xs : List ℕ) (ψ : CNF ℕ) :
    formulaEdges xs ψ =
      (List.range xs.length).flatMap (diamondEdges xs ψ) ++
      (topNode xs.length, chooserNode) ::
        ((List.range ψ.length).map fun i => (chooserNode, clauseNode i)) := rfl

theorem reduce_eq_ite (x : PrenexCNF) :
    reduce x =
      if x.matrix.all (fun c => c.all fun l => decide (l.1 ∈ QBF.roundVars x.rounds)) then
        ⟨formulaGraph (QBF.roundVars x.rounds) x.matrix, topNode 0⟩
      else ⟨⟨[0], []⟩, 0⟩ := rfl

/-! ### Exact edge-set and adjacency characterization -/

theorem mem_vertices_of_mem_edges {xs : List ℕ} {ψ : CNF ℕ} {u v : ℕ}
    (h : (u, v) ∈ formulaEdges xs ψ) :
    u ∈ (formulaGraph xs ψ).vertices ∧ v ∈ (formulaGraph xs ψ).vertices := by
  simp only [formulaGraph, List.mem_cons, List.mem_flatMap, Prod.exists]
  exact ⟨Or.inr ⟨u, v, h, by simp⟩, Or.inr ⟨u, v, h, by simp⟩⟩

theorem mem_vertices_of_adj {xs : List ℕ} {ψ : CNF ℕ} {u v : ℕ}
    (h : (formulaGraph xs ψ).toSimpleGraph.Adj u v) :
    v ∈ (formulaGraph xs ψ).vertices := by
  rw [Graph.toSimpleGraph_adj] at h
  rcases h.2 with h1 | h2
  · exact (mem_vertices_of_mem_edges h1).2
  · exact (mem_vertices_of_mem_edges h2).1

theorem topNode_mem_vertices (xs : List ℕ) (ψ : CNF ℕ) :
    topNode 0 ∈ (formulaGraph xs ψ).vertices :=
  List.mem_cons_self

theorem mem_branchEdges_iff {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {b : Bool} {p q : ℕ} :
    (p, q) ∈ branchEdges xs ψ j b ↔
      (∃ k < segCount xs ψ j b,
        (p = u1Node j b k ∧ q = mNode j b k) ∨ (p = mNode j b k ∧ q = u2Node j b k)) ∨
      (∃ k < segCount xs ψ j b - 1,
        (p = u2Node j b k ∧ q = vNode j b k) ∨ (p = vNode j b k ∧ q = u1Node j b (k + 1))) ∨
      (p = u2Node j b (segCount xs ψ j b - 1) ∧ q = botNode j) ∨
      (∃ k, ∃ h : k < (occClauses xs ψ j b).length,
        let i := (occClauses xs ψ j b)[k]
        (p = clauseNode i ∧ q = u1Node j b k) ∨ (p = clauseNode i ∧ q = u2Node j b k)) := by
  simp only [branchEdges, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq]
  constructor
  · rintro (((⟨k, hk, h⟩ | ⟨k, hk, h⟩) | h) | ⟨k, hk, h⟩)
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr (Or.inl ⟨k, hk, h⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr ⟨k, hk, ?_⟩))
      simpa only [List.getD_eq_getElem _ _ hk] using h
  · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩ | h | ⟨k, hk, h⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨k, hk, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨k, hk, h⟩))
    · exact Or.inl (Or.inr h)
    · refine Or.inr ⟨k, hk, ?_⟩
      simpa only [List.getD_eq_getElem _ _ hk] using h

theorem sym2_mem_formulaEdges_iff {xs : List ℕ} {ψ : CNF ℕ} {e : Sym2 ℕ} :
    (∃ u v, e = s(u, v) ∧ (u, v) ∈ formulaEdges xs ψ) ↔
      (∃ j < xs.length, j % 2 = 0 ∧
        ((∃ b : Bool,
            e = s(topNode j, aNode j b) ∨ e = s(aNode j b, wNode j b) ∨
            e = s(topNode j, wNode j b) ∨ e = s(wNode j b, cNode j b) ∨
            e = s(cNode j b, u1Node j b 0) ∨
            (∃ p q, e = s(p, q) ∧ (p, q) ∈ branchEdges xs ψ j b)) ∨
          e = s(botNode j, midNode j) ∨ e = s(midNode j, topNode (j + 1)))) ∨
      (∃ j < xs.length, j % 2 = 1 ∧
        ((∃ b : Bool,
            e = s(topNode j, u1Node j b 0) ∨
            (∃ p q, e = s(p, q) ∧ (p, q) ∈ branchEdges xs ψ j b)) ∨
          e = s(botNode j, topNode (j + 1)))) ∨
      e = s(topNode xs.length, chooserNode) ∨
      (∃ i < ψ.length, e = s(chooserNode, clauseNode i)) := by
  simp only [formulaEdges, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨u, v, rfl, ⟨j, hj, h⟩ | h⟩
    · unfold diamondEdges at h
      by_cases hpar : j % 2 = 0
      · simp only [hpar, beq_self_eq_true, ↓reduceIte, List.mem_append, List.mem_flatMap,
          List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        left
        refine ⟨j, hj, hpar, ?_⟩
        rcases h with ⟨b, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
          hb⟩ |
          (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact Or.inl ⟨b, Or.inl rfl⟩
        · exact Or.inl ⟨b, Or.inr (Or.inl rfl)⟩
        · exact Or.inl ⟨b, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact Or.inl ⟨b, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
        · exact Or.inl ⟨b, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
        · exact Or.inl ⟨b, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, v, rfl, hb⟩))))⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · have hpar1 : j % 2 = 1 := by omega
        simp only [hpar1, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, List.mem_append,
          List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        right; left
        refine ⟨j, hj, hpar1, ?_⟩
        rcases h with ⟨b, _, ⟨rfl, rfl⟩ | hb⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨b, Or.inl rfl⟩
        · exact Or.inl ⟨b, Or.inr ⟨u, v, rfl, hb⟩⟩
        · exact Or.inr rfl
    · rcases h with ⟨rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩))
  · rintro (⟨j, hj, hpar, h⟩ | ⟨j, hj, hpar, h⟩ | rfl | ⟨i, hi, rfl⟩)
    · rcases h with ⟨b, h⟩ | h | h
      · rcases h with rfl | rfl | rfl | rfl | rfl | ⟨p, q, rfl, hpq⟩
        · exact ⟨_, _, rfl, Or.inl ⟨j, hj, by cases b <;> simp [diamondEdges, hpar]⟩⟩
        · exact ⟨_, _, rfl, Or.inl ⟨j, hj, by cases b <;> simp [diamondEdges, hpar]⟩⟩
        · exact ⟨_, _, rfl, Or.inl ⟨j, hj, by cases b <;> simp [diamondEdges, hpar]⟩⟩
        · exact ⟨_, _, rfl, Or.inl ⟨j, hj, by cases b <;> simp [diamondEdges, hpar]⟩⟩
        · exact ⟨_, _, rfl, Or.inl ⟨j, hj, by cases b <;> simp [diamondEdges, hpar]⟩⟩
        · refine ⟨p, q, rfl, Or.inl ⟨j, hj, ?_⟩⟩
          simp only [diamondEdges, hpar, beq_self_eq_true, ↓reduceIte, List.mem_append,
            List.mem_flatMap]
          exact Or.inl ⟨b, by simp, Or.inr hpq⟩
      · exact ⟨_, _, h, Or.inl ⟨j, hj, by simp [diamondEdges, hpar]⟩⟩
      · exact ⟨_, _, h, Or.inl ⟨j, hj, by simp [diamondEdges, hpar]⟩⟩
    · rcases h with ⟨b, h⟩ | h
      · rcases h with rfl | ⟨p, q, rfl, hpq⟩
        · exact ⟨_, _, rfl, Or.inl ⟨j, hj, by cases b <;> simp [diamondEdges, hpar]⟩⟩
        · refine ⟨p, q, rfl, Or.inl ⟨j, hj, ?_⟩⟩
          simp only [diamondEdges, hpar, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
            List.mem_append, List.mem_flatMap, List.mem_cons]
          exact Or.inl ⟨b, by simp, Or.inr hpq⟩
      · exact ⟨_, _, h, Or.inl ⟨j, hj, by simp [diamondEdges, hpar]⟩⟩
    · exact ⟨_, _, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, _, rfl, Or.inr (Or.inr ⟨i, hi, rfl, rfl⟩)⟩

/-- Helper characterizing adjacency in `formulaGraph xs ψ` via `Sym2`. -/
theorem adj_formulaGraph_iff {xs : List ℕ} {ψ : CNF ℕ} {u v : ℕ} :
    (formulaGraph xs ψ).toSimpleGraph.Adj u v ↔
      u ≠ v ∧ (∃ p q, s(u, v) = s(p, q) ∧ (p, q) ∈ formulaEdges xs ψ) := by
  rw [Graph.toSimpleGraph_adj]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro (h | h)
    · exact ⟨u, v, rfl, h⟩
    · exact ⟨v, u, Sym2.eq_swap, h⟩
  · rintro ⟨p, q, heq, hpq⟩
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hpq
    · exact Or.inr hpq

/-- Distinctness helper for our 12 disjoint `Nat.pair` tags. -/
private theorem bool_toNat_inj {b₁ b₂ : Bool} (h : b₁.toNat = b₂.toNat) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> simp_all

theorem pair_ne_of_ne {a b x y : ℕ} (h : a ≠ x) : Nat.pair a b ≠ Nat.pair x y := by
  intro heq
  exact h ((Nat.pair_eq_pair.1 heq).1)

/-- Equality characterization for `Sym2` pairs. -/
theorem pair_sym2_eq {x y a b : ℕ} (h : s(x, y) = s(a, b)) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) :=
  Sym2.eq_iff.1 h

/-- Disjoint-tag elimination for `Sym2` pairs: if `a`'s tag differs from both `c` and `d`, then
`s(Nat.pair a b, w) ≠ s(Nat.pair c x, Nat.pair d y)`. -/
theorem sym2_ne_of_tag {a b w c x d y : ℕ} (hc : a ≠ c) (hd : a ≠ d) :
    s(Nat.pair a b, w) ≠ s(Nat.pair c x, Nat.pair d y) := by
  intro h
  rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact pair_ne_of_ne hc h1
  · exact pair_ne_of_ne hd h1

/-- Disjoint-tag elimination for `branchEdges` when `t ∉ {1, 6, 7, 8, 9, 11}`. -/
theorem sym2_ne_branchEdges_of_tag {xs : List ℕ} {ψ : CNF ℕ} {t arg w j p q : ℕ}
    {bb : Bool} (h1 : t ≠ 1) (h6 : t ≠ 6) (h7 : t ≠ 7) (h8 : t ≠ 8) (h9 : t ≠ 9)
    (h11 : t ≠ 11) (hpq : (p, q) ∈ branchEdges xs ψ j bb) :
    s(Nat.pair t arg, w) ≠ s(p, q) := by
  rw [mem_branchEdges_iff] at hpq
  rcases hpq with ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
    ⟨rfl, rfl⟩ | ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact sym2_ne_of_tag h6 h7
  · exact sym2_ne_of_tag h7 h8
  · exact sym2_ne_of_tag h8 h9
  · exact sym2_ne_of_tag h9 h6
  · exact sym2_ne_of_tag h8 h1
  · exact sym2_ne_of_tag h11 h6
  · exact sym2_ne_of_tag h11 h8

/-- In `formulaGraph xs ψ`, any two endpoints of a listed edge are distinct. -/
theorem fst_ne_snd_of_mem_formulaEdges {xs : List ℕ} {ψ : CNF ℕ} {u v : ℕ}
    (h : (u, v) ∈ formulaEdges xs ψ) : u ≠ v := by
  have hs : ∃ p q, s(u, v) = s(p, q) ∧ (p, q) ∈ formulaEdges xs ψ := ⟨u, v, rfl, h⟩
  rw [sym2_mem_formulaEdges_iff] at hs
  have hbranch : ∀ j b p q, (p, q) ∈ branchEdges xs ψ j b → p ≠ q := by
    intro j b p q hbr
    rw [mem_branchEdges_iff] at hbr
    rcases hbr with ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨rfl, rfl⟩ | ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      exact pair_ne_of_ne (by decide)
  rcases hs with ⟨j, _, _, ⟨b, h⟩ | h | h⟩ | ⟨j, _, _, ⟨b, h⟩ | h⟩ | h | ⟨i, _, h⟩
  · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
    · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)
    · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)
    · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)
    · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)
    · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)
    · rcases pair_sym2_eq heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hbranch j b _ _ hpq
      · exact (hbranch j b _ _ hpq).symm
  · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)
  · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)
  · rcases h with h | ⟨p, q, heq, hpq⟩
    · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)
    · rcases pair_sym2_eq heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hbranch j b _ _ hpq
      · exact (hbranch j b _ _ hpq).symm
  · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)
  · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)
  · rcases pair_sym2_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact pair_ne_of_ne (by decide)

/-- Convenient adjacency constructor from `Sym2` membership in `formulaEdges`. -/
theorem adj_of_sym2_mem {xs : List ℕ} {ψ : CNF ℕ} {u v : ℕ}
    (h : ∃ p q, s(u, v) = s(p, q) ∧ (p, q) ∈ formulaEdges xs ψ) :
    (formulaGraph xs ψ).toSimpleGraph.Adj u v := by
  obtain ⟨p, q, heq, hpq⟩ := h
  have hne := fst_ne_snd_of_mem_formulaEdges hpq
  rcases pair_sym2_eq heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (Graph.toSimpleGraph_adj).2 ⟨hne, Or.inl hpq⟩
  · exact ((Graph.toSimpleGraph_adj).2 ⟨hne, Or.inl hpq⟩).symm

/-- Adjacency helper for edges lying inside `branchEdges`. -/
theorem adj_of_branchEdges {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {b : Bool} {u v p q : ℕ}
    (hj : j < xs.length) (heq : s(u, v) = s(p, q)) (hpq : (p, q) ∈ branchEdges xs ψ j b) :
    (formulaGraph xs ψ).toSimpleGraph.Adj u v := by
  rcases Nat.mod_two_eq_zero_or_one j with hpar | hpar
  · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
      Or.inl ⟨b, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, q, heq, hpq⟩))))⟩⟩))
  · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inr (Or.inl ⟨j, hj, hpar,
      Or.inl ⟨b, Or.inr ⟨p, q, heq, hpq⟩⟩⟩)))

/-! ### Exact neighbor lists of each node family -/

theorem adj_aNode_iff {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {b : Bool} {w : ℕ}
    (hj : j < xs.length) (hpar : j % 2 = 0) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (aNode j b) w ↔ w = topNode j ∨ w = wNode j b := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    rcases h with ⟨j', _, _, ⟨b', h⟩ | h | h⟩ | ⟨j', _, _, ⟨b', h⟩ | h⟩ | h | ⟨i, _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [aNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb'⟩ := h1; obtain rfl := bool_toNat_inj hb'; exact Or.inl rfl
      · rcases pair_sym2_eq h with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [aNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb'⟩ := h1; obtain rfl := bool_toNat_inj hb'; exact Or.inr rfl
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · rintro (rfl | rfl)
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inl ⟨b, Or.inl Sym2.eq_swap⟩⟩))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inl ⟨b, Or.inr (Or.inl rfl)⟩⟩))

theorem adj_cNode_iff {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {b : Bool} {w : ℕ}
    (hj : j < xs.length) (hpar : j % 2 = 0) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (cNode j b) w ↔ w = wNode j b ∨ w = u1Node j b 0 := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    rcases h with ⟨j', _, _, ⟨b', h⟩ | h | h⟩ | ⟨j', _, _, ⟨b', h⟩ | h⟩ | h | ⟨i, _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [cNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb'⟩ := h1; obtain rfl := bool_toNat_inj hb'; exact Or.inl rfl
      · rcases pair_sym2_eq h with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [cNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb'⟩ := h1; obtain rfl := bool_toNat_inj hb'; exact Or.inr rfl
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · rintro (rfl | rfl)
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inl ⟨b, Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap)))⟩⟩))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inl ⟨b, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩⟩))

theorem adj_wNode_iff {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {b : Bool} {w : ℕ}
    (hj : j < xs.length) (hpar : j % 2 = 0) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (wNode j b) w ↔
      w = aNode j b ∨ w = topNode j ∨ w = cNode j b := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    rcases h with ⟨j', _, _, ⟨b', h⟩ | h | h⟩ | ⟨j', _, _, ⟨b', h⟩ | h⟩ | h | ⟨i, _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [wNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb'⟩ := h1; obtain rfl := bool_toNat_inj hb'; exact Or.inl rfl
      · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [wNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb'⟩ := h1; obtain rfl := bool_toNat_inj hb'; exact Or.inr (Or.inl rfl)
      · rcases pair_sym2_eq h with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [wNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb'⟩ := h1; obtain rfl := bool_toNat_inj hb'; exact Or.inr (Or.inr rfl)
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · rintro (rfl | rfl | rfl)
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inl ⟨b, Or.inr (Or.inl Sym2.eq_swap)⟩⟩))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inl ⟨b, Or.inr (Or.inr (Or.inl Sym2.eq_swap))⟩⟩))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inl ⟨b, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩⟩))

theorem adj_midNode_iff {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {w : ℕ}
    (hj : j < xs.length) (hpar : j % 2 = 0) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (midNode j) w ↔
      w = botNode j ∨ w = topNode (j + 1) := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    rcases h with ⟨j', _, _, ⟨b', h⟩ | h | h⟩ | ⟨j', _, _, ⟨b', h⟩ | h⟩ | h | ⟨i, _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
      · exact absurd h1 (pair_ne_of_ne (by decide))
      · simp only [midNode, Nat.pair_eq_pair, true_and] at h1; subst h1; exact Or.inl rfl
    · rcases pair_sym2_eq h with ⟨h1, rfl⟩ | ⟨h1, _⟩
      · simp only [midNode, Nat.pair_eq_pair, true_and] at h1; subst h1; exact Or.inr rfl
      · exact absurd h1 (pair_ne_of_ne (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · rintro (rfl | rfl)
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inr (Or.inl Sym2.eq_swap)⟩))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inr (Or.inr rfl)⟩))

theorem adj_mNode_iff {xs : List ℕ} {ψ : CNF ℕ} {j k : ℕ} {b : Bool} {w : ℕ}
    (hj : j < xs.length) (hk : k < segCount xs ψ j b) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (mNode j b k) w ↔
      w = u1Node j b k ∨ w = u2Node j b k := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    have hbr : ∀ j' b' p q, (p, q) ∈ branchEdges xs ψ j' b' →
        s(mNode j b k, w) = s(p, q) → w = u1Node j b k ∨ w = u2Node j b k := by
      intro j' b' p q hpq heq
      rw [mem_branchEdges_iff] at hpq
      rcases hpq with ⟨k', _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k', _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨rfl, rfl⟩ | ⟨k', _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · rcases pair_sym2_eq heq with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [mNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inl rfl
      · rcases pair_sym2_eq heq with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [mNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inr rfl
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
    rcases h with ⟨j', _, _, ⟨b', h⟩ | h | h⟩ | ⟨j', _, _, ⟨b', h⟩ | h⟩ | h | ⟨i, _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact hbr j' b' p q hpq heq
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact hbr j' b' p q hpq heq
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · rintro (rfl | rfl)
    · exact adj_of_branchEdges hj Sym2.eq_swap
        (mem_branchEdges_iff.2 (Or.inl ⟨k, hk, Or.inl ⟨rfl, rfl⟩⟩))
    · exact adj_of_branchEdges hj rfl
        (mem_branchEdges_iff.2 (Or.inl ⟨k, hk, Or.inr ⟨rfl, rfl⟩⟩))

theorem adj_vNode_iff {xs : List ℕ} {ψ : CNF ℕ} {j k : ℕ} {b : Bool} {w : ℕ}
    (hj : j < xs.length) (hk : k < segCount xs ψ j b - 1) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (vNode j b k) w ↔
      w = u2Node j b k ∨ w = u1Node j b (k + 1) := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    have hbr : ∀ j' b' p q, (p, q) ∈ branchEdges xs ψ j' b' →
        s(vNode j b k, w) = s(p, q) → w = u2Node j b k ∨ w = u1Node j b (k + 1) := by
      intro j' b' p q hpq heq
      rw [mem_branchEdges_iff] at hpq
      rcases hpq with ⟨k', _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k', _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨rfl, rfl⟩ | ⟨k', _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq heq with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [vNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inl rfl
      · rcases pair_sym2_eq heq with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [vNode, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inr rfl
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
    rcases h with ⟨j', _, _, ⟨b', h⟩ | h | h⟩ | ⟨j', _, _, ⟨b', h⟩ | h⟩ | h | ⟨i, _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact hbr j' b' p q hpq heq
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact hbr j' b' p q hpq heq
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · rintro (rfl | rfl)
    · exact adj_of_branchEdges hj Sym2.eq_swap
        (mem_branchEdges_iff.2 (Or.inr (Or.inl ⟨k, hk, Or.inl ⟨rfl, rfl⟩⟩)))
    · exact adj_of_branchEdges hj rfl
        (mem_branchEdges_iff.2 (Or.inr (Or.inl ⟨k, hk, Or.inr ⟨rfl, rfl⟩⟩)))

theorem adj_u1Node_iff {xs : List ℕ} {ψ : CNF ℕ} {j k : ℕ} {b : Bool} {w : ℕ}
    (hj : j < xs.length) (hk : k < segCount xs ψ j b) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (u1Node j b k) w ↔
      (k = 0 ∧ ((j % 2 = 0 ∧ w = cNode j b) ∨ (j % 2 = 1 ∧ w = topNode j))) ∨
      (0 < k ∧ w = vNode j b (k - 1)) ∨
      w = mNode j b k ∨
      (∃ h : k < (occClauses xs ψ j b).length, w = clauseNode ((occClauses xs ψ j b)[k])) := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    have hbr : ∀ j' b' p q, (p, q) ∈ branchEdges xs ψ j' b' →
        s(u1Node j b k, w) = s(p, q) →
        (0 < k ∧ w = vNode j b (k - 1)) ∨ w = mNode j b k ∨
        (∃ h : k < (occClauses xs ψ j b).length, w = clauseNode ((occClauses xs ψ j b)[k])) := by
      intro j' b' p q hpq heq
      rw [mem_branchEdges_iff] at hpq
      rcases hpq with ⟨k', _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k', _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨rfl, rfl⟩ | ⟨k', hk', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · rcases pair_sym2_eq heq with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [u1Node, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inr (Or.inl rfl)
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq heq with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [u1Node, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inl ⟨by omega, by simp⟩
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq heq with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [u1Node, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inr (Or.inr ⟨hk', rfl⟩)
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
    rcases h with ⟨j', _, hpar', ⟨b', h⟩ | h | h⟩ | ⟨j', _, hpar', ⟨b', h⟩ | h⟩ | h | ⟨i, _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [u1Node, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inl ⟨rfl, Or.inl ⟨hpar', rfl⟩⟩
      · exact Or.inr (hbr j' b' p q hpq heq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [u1Node, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inl ⟨rfl, Or.inr ⟨hpar', rfl⟩⟩
      · exact Or.inr (hbr j' b' p q hpq heq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · rintro (⟨rfl, ⟨hpar, rfl⟩ | ⟨hpar, rfl⟩⟩ | ⟨hkpos, rfl⟩ | rfl | ⟨hkocc, rfl⟩)
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inl ⟨b, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap))))⟩⟩))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inr (Or.inl ⟨j, hj, hpar,
        Or.inl ⟨b, Or.inl Sym2.eq_swap⟩⟩)))
    · have hmem : (vNode j b (k - 1), u1Node j b k) ∈ branchEdges xs ψ j b := by
        have := mem_branchEdges_iff (xs := xs) (ψ := ψ) (j := j) (b := b)
          (p := vNode j b (k - 1)) (q := u1Node j b (k - 1 + 1)) |>.2
          (Or.inr (Or.inl ⟨k - 1, by omega, Or.inr ⟨rfl, rfl⟩⟩))
        rwa [Nat.sub_add_cancel (by omega)] at this
      exact adj_of_branchEdges hj Sym2.eq_swap hmem
    · exact adj_of_branchEdges hj rfl
        (mem_branchEdges_iff.2 (Or.inl ⟨k, hk, Or.inl ⟨rfl, rfl⟩⟩))
    · exact adj_of_branchEdges hj Sym2.eq_swap
        (mem_branchEdges_iff.2 (Or.inr (Or.inr (Or.inr ⟨k, hkocc, Or.inl ⟨rfl, rfl⟩⟩))))

theorem adj_u2Node_iff {xs : List ℕ} {ψ : CNF ℕ} {j k : ℕ} {b : Bool} {w : ℕ}
    (hj : j < xs.length) (hk : k < segCount xs ψ j b) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (u2Node j b k) w ↔
      w = mNode j b k ∨
      (k < segCount xs ψ j b - 1 ∧ w = vNode j b k) ∨
      (k = segCount xs ψ j b - 1 ∧ w = botNode j) ∨
      (∃ h : k < (occClauses xs ψ j b).length, w = clauseNode ((occClauses xs ψ j b)[k])) := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    have hbr : ∀ j' b' p q, (p, q) ∈ branchEdges xs ψ j' b' →
        s(u2Node j b k, w) = s(p, q) →
        w = mNode j b k ∨ (k < segCount xs ψ j b - 1 ∧ w = vNode j b k) ∨
        (k = segCount xs ψ j b - 1 ∧ w = botNode j) ∨
        (∃ h : k < (occClauses xs ψ j b).length, w = clauseNode ((occClauses xs ψ j b)[k])) := by
      intro j' b' p q hpq heq
      rw [mem_branchEdges_iff] at hpq
      rcases hpq with ⟨k', _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k', hk', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨rfl, rfl⟩ | ⟨k', hk', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq heq with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [u2Node, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inl rfl
      · rcases pair_sym2_eq heq with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [u2Node, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inr (Or.inl ⟨hk', rfl⟩)
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq heq with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [u2Node, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq heq with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [u2Node, Nat.pair_eq_pair, true_and] at h1
          obtain ⟨rfl, hb', rfl⟩ := h1; obtain rfl := bool_toNat_inj hb'
          exact Or.inr (Or.inr (Or.inr ⟨hk', rfl⟩))
    rcases h with ⟨j', _, _, ⟨b', h⟩ | h | h⟩ | ⟨j', _, _, ⟨b', h⟩ | h⟩ | h | ⟨i, _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact hbr j' b' p q hpq heq
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact hbr j' b' p q hpq heq
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · rintro (rfl | ⟨hk', rfl⟩ | ⟨rfl, rfl⟩ | ⟨hkocc, rfl⟩)
    · exact adj_of_branchEdges hj Sym2.eq_swap
        (mem_branchEdges_iff.2 (Or.inl ⟨k, hk, Or.inr ⟨rfl, rfl⟩⟩))
    · exact adj_of_branchEdges hj rfl
        (mem_branchEdges_iff.2 (Or.inr (Or.inl ⟨k, hk', Or.inl ⟨rfl, rfl⟩⟩)))
    · exact adj_of_branchEdges hj rfl (mem_branchEdges_iff.2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · exact adj_of_branchEdges hj Sym2.eq_swap
        (mem_branchEdges_iff.2 (Or.inr (Or.inr (Or.inr ⟨k, hkocc, Or.inr ⟨rfl, rfl⟩⟩))))

theorem adj_botNode_iff {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {w : ℕ} (hj : j < xs.length) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (botNode j) w ↔
      (∃ b : Bool, w = u2Node j b (segCount xs ψ j b - 1)) ∨
      (j % 2 = 0 ∧ w = midNode j) ∨ (j % 2 = 1 ∧ w = topNode (j + 1)) := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    have hbr : ∀ j' b' p q, (p, q) ∈ branchEdges xs ψ j' b' →
        s(botNode j, w) = s(p, q) → ∃ b : Bool, w = u2Node j b (segCount xs ψ j b - 1) := by
      intro j' b' p q hpq heq
      rw [mem_branchEdges_iff] at hpq
      rcases hpq with ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨rfl, rfl⟩ | ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq heq with ⟨h1, _⟩ | ⟨h1, rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
        · simp only [botNode, Nat.pair_eq_pair, true_and] at h1; subst h1; exact ⟨b', rfl⟩
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
    rcases h with ⟨j', _, hpar', ⟨b', h⟩ | h | h⟩ | ⟨j', _, hpar', ⟨b', h⟩ | h⟩ | h | ⟨i, _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact Or.inl (hbr j' b' p q hpq heq)
    · rcases pair_sym2_eq h with ⟨h1, rfl⟩ | ⟨h1, _⟩
      · simp only [botNode, Nat.pair_eq_pair, true_and] at h1; subst h1
        exact Or.inr (Or.inl ⟨hpar', rfl⟩)
      · exact absurd h1 (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact Or.inl (hbr j' b' p q hpq heq)
    · rcases pair_sym2_eq h with ⟨h1, rfl⟩ | ⟨h1, _⟩
      · simp only [botNode, Nat.pair_eq_pair, true_and] at h1; subst h1
        exact Or.inr (Or.inr ⟨hpar', rfl⟩)
      · exact absurd h1 (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · rintro (⟨b, rfl⟩ | ⟨hpar, rfl⟩ | ⟨hpar, rfl⟩)
    · exact adj_of_branchEdges hj Sym2.eq_swap
        (mem_branchEdges_iff.2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hj, hpar,
        Or.inr (Or.inl rfl)⟩))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inr (Or.inl ⟨j, hj, hpar,
        Or.inr rfl⟩)))

theorem adj_topNode_iff {xs : List ℕ} {ψ : CNF ℕ} {j : ℕ} {w : ℕ} (hj : j ≤ xs.length) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (topNode j) w ↔
      (0 < j ∧ (((j - 1) % 2 = 0 ∧ w = midNode (j - 1)) ∨
        ((j - 1) % 2 = 1 ∧ w = botNode (j - 1)))) ∨
      (j < xs.length ∧ j % 2 = 0 ∧ ∃ b : Bool, w = aNode j b ∨ w = wNode j b) ∨
      (j < xs.length ∧ j % 2 = 1 ∧ ∃ b : Bool, w = u1Node j b 0) ∨
      (j = xs.length ∧ w = chooserNode) := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    rcases h with ⟨j', hj', hpar', ⟨b', h⟩ | h | h⟩ | ⟨j', hj', hpar', ⟨b', h⟩ | h⟩ | h | ⟨i, _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · rcases pair_sym2_eq h with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [topNode, Nat.pair_eq_pair, true_and] at h1; subst h1
          exact Or.inr (Or.inl ⟨hj', hpar', b', Or.inl rfl⟩)
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq h with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [topNode, Nat.pair_eq_pair, true_and] at h1; subst h1
          exact Or.inr (Or.inl ⟨hj', hpar', b', Or.inr rfl⟩)
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
      · exact absurd h1 (pair_ne_of_ne (by decide))
      · simp only [topNode, Nat.pair_eq_pair, true_and] at h1; subst h1
        exact Or.inl ⟨by omega, Or.inl ⟨by simpa using hpar', by simp⟩⟩
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · rcases pair_sym2_eq h with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [topNode, Nat.pair_eq_pair, true_and] at h1; subst h1
          exact Or.inr (Or.inr (Or.inl ⟨hj', hpar', b', rfl⟩))
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
      · exact absurd h1 (pair_ne_of_ne (by decide))
      · simp only [topNode, Nat.pair_eq_pair, true_and] at h1; subst h1
        exact Or.inl ⟨by omega, Or.inr ⟨by simpa using hpar', by simp⟩⟩
    · rcases pair_sym2_eq h with ⟨h1, rfl⟩ | ⟨h1, _⟩
      · simp only [topNode, Nat.pair_eq_pair, true_and] at h1; subst h1
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact absurd h1 (pair_ne_of_ne (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
  · rintro (⟨hpos, ⟨hpar, rfl⟩ | ⟨hpar, rfl⟩⟩ | ⟨hlt, hpar, b, rfl | rfl⟩ | ⟨hlt, hpar, b, rfl⟩ |
      ⟨rfl, rfl⟩)
    · have h := adj_of_sym2_mem (sym2_mem_formulaEdges_iff (xs := xs) (ψ := ψ) |>.2
        (Or.inl ⟨j - 1, by omega, hpar, Or.inr (Or.inr Sym2.eq_swap)⟩))
      rwa [Nat.sub_add_cancel (by omega)] at h
    · have h := adj_of_sym2_mem (sym2_mem_formulaEdges_iff (xs := xs) (ψ := ψ) |>.2
        (Or.inr (Or.inl ⟨j - 1, by omega, hpar, Or.inr Sym2.eq_swap⟩)))
      rwa [Nat.sub_add_cancel (by omega)] at h
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hlt, hpar,
        Or.inl ⟨b, Or.inl rfl⟩⟩))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inl ⟨j, hlt, hpar,
        Or.inl ⟨b, Or.inr (Or.inr (Or.inl rfl))⟩⟩))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inr (Or.inl ⟨j, hlt, hpar,
        Or.inl ⟨b, Or.inl rfl⟩⟩)))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inr (Or.inr (Or.inl rfl))))

theorem adj_chooserNode_iff {xs : List ℕ} {ψ : CNF ℕ} {w : ℕ} :
    (formulaGraph xs ψ).toSimpleGraph.Adj chooserNode w ↔
      w = topNode xs.length ∨ ∃ i < ψ.length, w = clauseNode i := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    rcases h with ⟨j', _, _, ⟨b', h⟩ | h | h⟩ | ⟨j', _, _, ⟨b', h⟩ | h⟩ | h | ⟨i, hi, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_branchEdges_of_tag (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) hpq)
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
      · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact Or.inl rfl
    · rcases pair_sym2_eq h with ⟨_, rfl⟩ | ⟨h1, _⟩
      · exact Or.inr ⟨i, hi, rfl⟩
      · exact absurd h1 (pair_ne_of_ne (by decide))
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2 (Or.inr (Or.inr (Or.inl Sym2.eq_swap))))
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2
        (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩))))

theorem adj_clauseNode_iff {xs : List ℕ} {ψ : CNF ℕ} {i : ℕ} {w : ℕ} (hi : i < ψ.length) :
    (formulaGraph xs ψ).toSimpleGraph.Adj (clauseNode i) w ↔
      w = chooserNode ∨
      ∃ j < xs.length, ∃ b : Bool, ∃ k, ∃ hk : k < (occClauses xs ψ j b).length,
        (occClauses xs ψ j b)[k] = i ∧ (w = u1Node j b k ∨ w = u2Node j b k) := by
  constructor
  · intro hadj
    obtain ⟨-, h⟩ := adj_formulaGraph_iff.1 hadj
    rw [sym2_mem_formulaEdges_iff] at h
    have hbr : ∀ j' b' p q, (p, q) ∈ branchEdges xs ψ j' b' →
        s(clauseNode i, w) = s(p, q) →
        ∃ k, ∃ hk : k < (occClauses xs ψ j' b').length,
          (occClauses xs ψ j' b')[k] = i ∧ (w = u1Node j' b' k ∨ w = u2Node j' b' k) := by
      intro j' b' p q hpq heq
      rw [mem_branchEdges_iff] at hpq
      rcases hpq with ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨rfl, rfl⟩ | ⟨k, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd heq (sym2_ne_of_tag (by decide) (by decide))
      · rcases pair_sym2_eq heq with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [clauseNode, Nat.pair_eq_pair, true_and] at h1
          exact ⟨k, hk, h1.symm, Or.inl rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
      · rcases pair_sym2_eq heq with ⟨h1, rfl⟩ | ⟨h1, _⟩
        · simp only [clauseNode, Nat.pair_eq_pair, true_and] at h1
          exact ⟨k, hk, h1.symm, Or.inr rfl⟩
        · exact absurd h1 (pair_ne_of_ne (by decide))
    rcases h with ⟨j', hj', _, ⟨b', h⟩ | h | h⟩ | ⟨j', hj', _, ⟨b', h⟩ | h⟩ | h | ⟨i', _, h⟩
    · rcases h with h | h | h | h | h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · obtain ⟨k, hk, hki, hw⟩ := hbr j' b' p q hpq heq
        exact Or.inr ⟨j', hj', b', k, hk, hki, hw⟩
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases h with h | ⟨p, q, heq, hpq⟩
      · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
      · obtain ⟨k, hk, hki, hw⟩ := hbr j' b' p q hpq heq
        exact Or.inr ⟨j', hj', b', k, hk, hki, hw⟩
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · exact absurd h (sym2_ne_of_tag (by decide) (by decide))
    · rcases pair_sym2_eq h with ⟨h1, _⟩ | ⟨h1, rfl⟩
      · exact absurd h1 (pair_ne_of_ne (by decide))
      · exact Or.inl rfl
  · rintro (rfl | ⟨j, hj, b, k, hk, hki, rfl | rfl⟩)
    · exact adj_of_sym2_mem (sym2_mem_formulaEdges_iff.2
        (Or.inr (Or.inr (Or.inr ⟨i, hi, Sym2.eq_swap⟩))))
    · have hmem : (clauseNode i, u1Node j b k) ∈ branchEdges xs ψ j b := by
        rw [← hki]
        exact mem_branchEdges_iff.2 (Or.inr (Or.inr (Or.inr ⟨k, hk, Or.inl ⟨rfl, rfl⟩⟩)))
      exact adj_of_branchEdges hj rfl hmem
    · have hmem : (clauseNode i, u2Node j b k) ∈ branchEdges xs ψ j b := by
        rw [← hki]
        exact mem_branchEdges_iff.2 (Or.inr (Or.inr (Or.inr ⟨k, hk, Or.inr ⟨rfl, rfl⟩⟩)))
      exact adj_of_branchEdges hj rfl hmem

end UndirectedEdgeGeography

end Cslib.Complexity
