/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime

import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Fortune–Hopcroft–Wyllie 14-Vertex Switch Gadget for `SAT ≤_p BFP`

This module constructs the 14-vertex interlocking switch gadget and the polynomial-time reduction
`BackAndForthPaths.toBFP : CNF ℕ → PathInstance`
under standard Lean axioms.
-/

public section

namespace Cslib.Complexity.BackAndForthPaths

open Cslib.Complexity Cslib.Logic.PL
open Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Node encoding and 14-vertex switch gadget -/

/-- Port codes `0..13` of the 14-vertex interlocking switch gadget. -/
abbrev swC : ℕ := 0
/-- Port `B` (top entry for `P₂`). -/
abbrev swB : ℕ := 1
/-- Port `A` (bottom exit for `P₁`). -/
abbrev swA : ℕ := 2
/-- Port `D` (bottom exit for `P₂`). -/
abbrev swD : ℕ := 3
/-- Port `Lin` (left-wing entry). -/
abbrev swLin : ℕ := 4
/-- Port `Lout` (left-wing exit). -/
abbrev swLout : ℕ := 5
/-- Port `Rin` (right-wing entry). -/
abbrev swRin : ℕ := 6
/-- Port `Rout` (right-wing exit). -/
abbrev swRout : ℕ := 7
/-- Internal vertex `U`. -/
abbrev swU : ℕ := 8
/-- Internal vertex `V`. -/
abbrev swV : ℕ := 9
/-- Internal vertex `X`. -/
abbrev swX : ℕ := 10
/-- Internal vertex `X2`. -/
abbrev swX2 : ℕ := 11
/-- Internal vertex `Y`. -/
abbrev swY : ℕ := 12
/-- Internal vertex `Y2`. -/
abbrev swY2 : ℕ := 13

/-- Terminal `s₁`. -/
abbrev s1Node : ℕ := 0
/-- Terminal `t₁`. -/
abbrev t1Node : ℕ := 1
/-- Terminal `s₂`. -/
abbrev s2Node : ℕ := 2
/-- Terminal `t₂`. -/
abbrev t2Node : ℕ := 3

/-- Variable chain vertex `X_i`. -/
@[expose] def varNode (i : ℕ) : ℕ := 4 * (i + 1)

/-- Clause chain vertex `C_j`. -/
@[expose] def clauseNode (j : ℕ) : ℕ := 4 * (j + 1) + 1

/-- Vertex `r` (`0 ≤ r < 14`) inside switch `k`. -/
@[expose] def swNode (k r : ℕ) : ℕ := 4 * (14 * k + r + 1) + 2

/-- The 18 internal arcs of switch `k`. -/
@[expose] def switchArcs (k : ℕ) : List (ℕ × ℕ) :=
  [ (swNode k swC, swNode k swX), (swNode k swC, swNode k swY),
    (swNode k swB, swNode k swU), (swNode k swB, swNode k swV),
    (swNode k swLin, swNode k swY2), (swNode k swRin, swNode k swX2),
    (swNode k swY2, swNode k swY), (swNode k swY2, swNode k swD),
    (swNode k swY, swNode k swLout), (swNode k swY, swNode k swV),
    (swNode k swX2, swNode k swX), (swNode k swX2, swNode k swD),
    (swNode k swX, swNode k swRout), (swNode k swX, swNode k swU),
    (swNode k swU, swNode k swY2), (swNode k swU, swNode k swA),
    (swNode k swV, swNode k swX2), (swNode k swV, swNode k swA) ]

/-- Arcs threading `src` through the left wings of switches `ks` to `dst`. -/
@[expose] def chainArcs (src dst : ℕ) (ks : List ℕ) : List (ℕ × ℕ) :=
  if ks.isEmpty then [(src, dst)]
  else
    (src, swNode (ks.headD 0) swLin) ::
      ((List.range (ks.length - 1)).map fun i ↦
        (swNode (ks.getD i 0) swLout, swNode (ks.getD (i + 1) 0) swLin)) ++
      [(swNode (ks.getD (ks.length - 1) 0) swLout, dst)]

/-- Flattened literal occurrences `(clauseIdx, varIdx, polarity)` of `φ`. -/
@[expose] def litList (φ : CNF ℕ) : List ((ℕ × ℕ) × Bool) :=
  φ.zipIdx.flatMap fun c ↦ c.1.map fun l ↦ ((c.2, φ.vars.idxOf l.1), l.2)

/-- Literal indices in `litList φ` belonging to variable index `i` with polarity `≠ val`. -/
@[expose] def varOccs (φ : CNF ℕ) (i : ℕ) (val : Bool) : List ℕ :=
  (List.range (litList φ).length).filter fun k ↦
    let lit := (litList φ).getD k ((0, 0), false)
    decide (lit.1.2 = i ∧ lit.2 ≠ val)

/-- Vertex list of the FHW reduction digraph for `φ`. -/
@[expose] def bfpVertices (φ : CNF ℕ) : List ℕ :=
  let N := φ.vars.length
  let M := φ.length
  let K := (litList φ).length
  [s1Node, t1Node, s2Node, t2Node] ++
    ((List.range (N + 1)).map varNode) ++
    ((List.range (M + 1)).map clauseNode) ++
    ((List.range K).flatMap fun k ↦ (List.range 14).map fun r ↦ swNode k r)

/-- Arc list of the FHW reduction digraph for `φ`. -/
@[expose] def bfpEdges (φ : CNF ℕ) : List (ℕ × ℕ) :=
  let N := φ.vars.length
  let M := φ.length
  let lits := litList φ
  let K := lits.length
  ((List.range K).flatMap switchArcs) ++
  (if K = 0 then [(s2Node, t2Node)]
   else [(s2Node, swNode 0 swB), (swNode (K - 1) swD, t2Node), (swNode 0 swA, t1Node)] ++
     ((List.range (K - 1)).flatMap fun k ↦
       [(swNode k swD, swNode (k + 1) swB), (swNode (k + 1) swA, swNode k swC)])) ++
  ((List.range N).flatMap fun i ↦
    chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i true) ++
    chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i false)) ++
  ((List.range K).flatMap fun k ↦
    let j := (lits.getD k ((0, 0), false)).1.1
    [(clauseNode j, swNode k swRin), (swNode k swRout, clauseNode (j + 1))]) ++
  [(s1Node, varNode 0), (varNode N, clauseNode 0),
    (clauseNode M, if K = 0 then t1Node else swNode (K - 1) swC),
    (t1Node, s2Node), (t2Node, s1Node)]

/-- The FHW reduction from `SAT` to `BFP`: constructs `⟨G(φ), t1Node, t2Node⟩`. -/
@[expose] def toBFP (φ : CNF ℕ) : PathInstance :=
  ⟨⟨bfpVertices φ, bfpEdges φ⟩, t1Node, t2Node⟩

theorem toBFP_source (φ : CNF ℕ) : (toBFP φ).source = t1Node := rfl
theorem toBFP_target (φ : CNF ℕ) : (toBFP φ).target = t2Node := rfl
theorem toBFP_graph_vertices (φ : CNF ℕ) : (toBFP φ).graph.vertices = bfpVertices φ := rfl
theorem toBFP_graph_edges (φ : CNF ℕ) : (toBFP φ).graph.edges = bfpEdges φ := rfl

theorem mem_litList_of_mem_clause {φ : CNF ℕ} {j : ℕ} (hj : j < φ.length)
    {l : Literal ℕ} (hl : l ∈ φ[j]) : ((j, φ.vars.idxOf l.1), l.2) ∈ litList φ :=
  List.mem_flatMap.mpr ⟨(φ[j], j),
    List.mem_zipIdx_iff_getElem?.mpr (by simp), List.mem_map.mpr ⟨l, hl, rfl⟩⟩

theorem mem_chainArcs_nil (src dst : ℕ) : (src, dst) ∈ chainArcs src dst [] := by
  simp [chainArcs]

theorem mem_chainArcs_cons_iff {src dst k₀ : ℕ} {rest : List ℕ} {u v : ℕ} :
    (u, v) ∈ chainArcs src dst (k₀ :: rest) ↔
      (u = src ∧ v = swNode k₀ swLin) ∨
      (∃ i < (k₀ :: rest).length - 1,
        u = swNode ((k₀ :: rest).getD i 0) swLout ∧
          v = swNode ((k₀ :: rest).getD (i + 1) 0) swLin) ∨
      (u = swNode ((k₀ :: rest).getD ((k₀ :: rest).length - 1) 0) swLout ∧ v = dst) := by
  unfold chainArcs
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append,
    List.mem_cons, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq,
    List.headD_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | ⟨i, hi, hu, hv⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨i, hi, hu.symm, hv.symm⟩)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨i, hi, hu, hv⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨i, hi, hu.symm, hv.symm⟩)
    · exact Or.inr (Or.inr h)

theorem mem_bfpVertices_term (φ : CNF ℕ) :
    s1Node ∈ bfpVertices φ ∧ t1Node ∈ bfpVertices φ ∧
      s2Node ∈ bfpVertices φ ∧ t2Node ∈ bfpVertices φ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold bfpVertices <;>
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (by simp)))

theorem mem_bfpVertices_varNode {φ : CNF ℕ} {i : ℕ} (hi : i ≤ φ.vars.length) :
    varNode i ∈ bfpVertices φ := by
  unfold bfpVertices
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)))

theorem mem_bfpVertices_clauseNode {φ : CNF ℕ} {j : ℕ} (hj : j ≤ φ.length) :
    clauseNode j ∈ bfpVertices φ := by
  unfold bfpVertices
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩))

theorem mem_bfpVertices_swNode {φ : CNF ℕ} {k r : ℕ} (hk : k < (litList φ).length) (hr : r < 14) :
    swNode k r ∈ bfpVertices φ := by
  unfold bfpVertices
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
    List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩⟩)

theorem mem_bfpEdges_switchArcs {φ : CNF ℕ} {k : ℕ} (hk : k < (litList φ).length)
    {e : ℕ × ℕ} (he : e ∈ switchArcs k) : e ∈ bfpEdges φ := by
  unfold bfpEdges
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, he⟩))))

theorem mem_bfpEdges_varChain {φ : CNF ℕ} {i : ℕ} (hi : i < φ.vars.length) (val : Bool)
    {e : ℕ × ℕ} (he : e ∈ chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i val)) :
    e ∈ bfpEdges φ := by
  unfold bfpEdges
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩)))
  cases val
  · exact List.mem_append_right _ he
  · exact List.mem_append_left _ he

theorem mem_bfpEdges_clause {φ : CNF ℕ} {k : ℕ} (hk : k < (litList φ).length) :
    (clauseNode ((litList φ).getD k ((0, 0), false)).1.1, swNode k swRin) ∈ bfpEdges φ ∧
    (swNode k swRout, clauseNode (((litList φ).getD k ((0, 0), false)).1.1 + 1)) ∈ bfpEdges φ := by
  constructor <;> unfold bfpEdges <;>
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, by simp⟩))

theorem mem_bfpEdges_stack_nil {φ : CNF ℕ} (hK : (litList φ).length = 0) :
    (s2Node, t2Node) ∈ bfpEdges φ := by
  unfold bfpEdges
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ ?_)))
  simp [hK]

theorem mem_bfpEdges_stack_head {φ : CNF ℕ} (hK : (litList φ).length ≠ 0) :
    (s2Node, swNode 0 swB) ∈ bfpEdges φ ∧
    (swNode ((litList φ).length - 1) swD, t2Node) ∈ bfpEdges φ ∧
    (swNode 0 swA, t1Node) ∈ bfpEdges φ := by
  have hmem : ∀ e ∈ [(s2Node, swNode 0 swB), (swNode ((litList φ).length - 1) swD, t2Node),
      (swNode 0 swA, t1Node)], e ∈ bfpEdges φ := by
    intro e he
    unfold bfpEdges
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ ?_)))
    simp only [hK, ↓reduceIte, List.mem_append]
    exact Or.inl he
  exact ⟨hmem _ (by simp), hmem _ (by simp), hmem _ (by simp)⟩

theorem mem_bfpEdges_stack_mid {φ : CNF ℕ} {k : ℕ} (hk : k + 1 < (litList φ).length) :
    (swNode k swD, swNode (k + 1) swB) ∈ bfpEdges φ ∧
    (swNode (k + 1) swA, swNode k swC) ∈ bfpEdges φ := by
  have hK : (litList φ).length ≠ 0 := by omega
  have hmem : ∀ e ∈ [(swNode k swD, swNode (k + 1) swB), (swNode (k + 1) swA, swNode k swC)],
      e ∈ bfpEdges φ := by
    intro e he
    unfold bfpEdges
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ ?_)))
    simp only [hK, ↓reduceIte, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inr ⟨k, by omega, he⟩
  exact ⟨hmem _ (by simp), hmem _ (by simp)⟩

theorem mem_bfpEdges_terminals (φ : CNF ℕ) :
    (s1Node, varNode 0) ∈ bfpEdges φ ∧
    (varNode φ.vars.length, clauseNode 0) ∈ bfpEdges φ ∧
    (clauseNode φ.length,
      if (litList φ).length = 0 then t1Node else swNode ((litList φ).length - 1) swC) ∈
      bfpEdges φ ∧
    (t1Node, s2Node) ∈ bfpEdges φ ∧
    (t2Node, s1Node) ∈ bfpEdges φ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (unfold bfpEdges; exact List.mem_append_right _ (by simp))

/-! ### 2. Disjointness, adjacency in lists, and neighbor lemmas -/

theorem swNode_inj {k₁ r₁ k₂ r₂ : ℕ} (hr₁ : r₁ < 14) (hr₂ : r₂ < 14)
    (h : swNode k₁ r₁ = swNode k₂ r₂) : k₁ = k₂ ∧ r₁ = r₂ := by
  unfold swNode at h; omega

theorem varNode_inj {i₁ i₂ : ℕ} (h : varNode i₁ = varNode i₂) : i₁ = i₂ := by
  unfold varNode at h; omega

theorem clauseNode_inj {j₁ j₂ : ℕ} (h : clauseNode j₁ = clauseNode j₂) : j₁ = j₂ := by
  unfold clauseNode at h; omega

theorem varNode_ne_term (i : ℕ) :
    varNode i ≠ s1Node ∧ varNode i ≠ t1Node ∧ varNode i ≠ s2Node ∧ varNode i ≠ t2Node := by
  unfold varNode; dsimp only [s1Node, t1Node, s2Node, t2Node]; omega

theorem clauseNode_ne_term (j : ℕ) :
    clauseNode j ≠ s1Node ∧ clauseNode j ≠ t1Node ∧
      clauseNode j ≠ s2Node ∧ clauseNode j ≠ t2Node := by
  unfold clauseNode; dsimp only [s1Node, t1Node, s2Node, t2Node]; omega

theorem swNode_ne_term (k r : ℕ) :
    swNode k r ≠ s1Node ∧ swNode k r ≠ t1Node ∧ swNode k r ≠ s2Node ∧ swNode k r ≠ t2Node := by
  unfold swNode; dsimp only [s1Node, t1Node, s2Node, t2Node]; omega

theorem varNode_ne_clauseNode (i j : ℕ) : varNode i ≠ clauseNode j := by
  unfold varNode clauseNode; omega

theorem varNode_ne_swNode (i k r : ℕ) : varNode i ≠ swNode k r := by
  unfold varNode swNode; omega

theorem clauseNode_ne_swNode (j k r : ℕ) : clauseNode j ≠ swNode k r := by
  unfold clauseNode swNode; omega

theorem mem_switchArcs_iff {k u v : ℕ} :
    (u, v) ∈ switchArcs k ↔
      (u = swNode k swC ∧ v = swNode k swX) ∨ (u = swNode k swC ∧ v = swNode k swY) ∨
      (u = swNode k swB ∧ v = swNode k swU) ∨ (u = swNode k swB ∧ v = swNode k swV) ∨
      (u = swNode k swLin ∧ v = swNode k swY2) ∨ (u = swNode k swRin ∧ v = swNode k swX2) ∨
      (u = swNode k swY2 ∧ v = swNode k swY) ∨ (u = swNode k swY2 ∧ v = swNode k swD) ∨
      (u = swNode k swY ∧ v = swNode k swLout) ∨ (u = swNode k swY ∧ v = swNode k swV) ∨
      (u = swNode k swX2 ∧ v = swNode k swX) ∨ (u = swNode k swX2 ∧ v = swNode k swD) ∨
      (u = swNode k swX ∧ v = swNode k swRout) ∨ (u = swNode k swX ∧ v = swNode k swU) ∨
      (u = swNode k swU ∧ v = swNode k swY2) ∨ (u = swNode k swU ∧ v = swNode k swA) ∨
      (u = swNode k swV ∧ v = swNode k swX2) ∨ (u = swNode k swV ∧ v = swNode k swA) := by
  simp [switchArcs]

theorem mem_chainArcs_cases {src dst : ℕ} {ks : List ℕ} {u v : ℕ}
    (h : (u, v) ∈ chainArcs src dst ks) :
    (ks = [] ∧ u = src ∧ v = dst) ∨
    (∃ k, k ∈ ks ∧ u = src ∧ v = swNode k swLin) ∨
    (∃ k₁ k₂, k₁ ∈ ks ∧ k₂ ∈ ks ∧ u = swNode k₁ swLout ∧ v = swNode k₂ swLin) ∨
    (∃ k, k ∈ ks ∧ u = swNode k swLout ∧ v = dst) := by
  unfold chainArcs at h
  cases hks : ks with
  | nil =>
    simp only [hks, List.isEmpty_nil, ↓reduceIte, List.mem_singleton, Prod.mk.injEq] at h
    exact Or.inl ⟨rfl, h⟩
  | cons k₀ rest =>
    rw [hks] at h
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
      Prod.mk.injEq, List.headD_cons, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨i, hi, hu, hv⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨k₀, List.mem_cons_self, rfl, rfl⟩)
    · have hi1 : i < (k₀ :: rest).length := by omega
      have hi2 : i + 1 < (k₀ :: rest).length := by omega
      refine Or.inr (Or.inr (Or.inl ⟨(k₀ :: rest).getD i 0, (k₀ :: rest).getD (i + 1) 0, ?_, ?_,
        hu.symm, hv.symm⟩))
      · rw [List.getD_eq_getElem _ _ hi1]; exact List.getElem_mem hi1
      · rw [List.getD_eq_getElem _ _ hi2]; exact List.getElem_mem hi2
    · have hlast : (k₀ :: rest).length - 1 < (k₀ :: rest).length := by simp
      refine Or.inr (Or.inr (Or.inr ⟨(k₀ :: rest).getD ((k₀ :: rest).length - 1) 0, ?_, rfl, rfl⟩))
      rw [List.getD_eq_getElem _ _ hlast]; exact List.getElem_mem hlast

/-- Immediate adjacency of `(w, u)` inside a list `p`: `w` is followed directly by `u`. -/
@[expose] def IsAdjInList (p : List ℕ) (w u : ℕ) : Prop :=
  ∃ i : ℕ, ∃ h : i + 1 < p.length, p[i]'(by omega) = w ∧ p[i + 1]'h = u

theorem isAdjInList_mem_left {p : List ℕ} {w u : ℕ} (h : IsAdjInList p w u) : w ∈ p := by
  rcases h with ⟨i, hi, rfl, _⟩; exact List.getElem_mem _

theorem isAdjInList_mem_right {p : List ℕ} {w u : ℕ} (h : IsAdjInList p w u) : u ∈ p := by
  rcases h with ⟨i, hi, _, rfl⟩; exact List.getElem_mem _

theorem isAdjInList_succ_unique {p : List ℕ} (hnd : p.Nodup) {a b c : ℕ}
    (h1 : IsAdjInList p a b) (h2 : IsAdjInList p a c) : b = c := by
  rcases h1 with ⟨i, hi, hi_eq, hb⟩
  rcases h2 with ⟨j, hj, hj_eq, hc⟩
  have hij : (⟨i, by omega⟩ : Fin p.length) = ⟨j, by omega⟩ :=
    (List.nodup_iff_injective_getElem.mp hnd) (hi_eq.trans hj_eq.symm)
  have hij' : i = j := congrArg Fin.val hij
  subst hij'; exact hb.symm.trans hc

theorem exists_pred_in_path {E : ℕ → ℕ → Prop} {p : List ℕ}
    (hch : p.IsChain E) {u : ℕ} (hu : u ∈ p) (hhead : p.head? ≠ some u) :
    ∃ w : ℕ, IsAdjInList p w u ∧ E w u := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
  cases k with
  | zero =>
    exfalso; apply hhead
    cases p with
    | nil => simp at hk
    | cons a l => rfl
  | succ i =>
    refine ⟨p[i]'(by omega), ⟨i, hk, rfl, rfl⟩, ?_⟩
    exact (List.isChain_iff_getElem.mp hch) i hk

theorem exists_succ_in_path {E : ℕ → ℕ → Prop} {p : List ℕ}
    (hch : p.IsChain E) {u : ℕ} (hu : u ∈ p) (hlast : p.getLast? ≠ some u) :
    ∃ w : ℕ, IsAdjInList p u w ∧ E u w := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
  have hk1 : k + 1 < p.length := by
    by_contra hge
    have hkeq : k = p.length - 1 := by omega
    apply hlast
    have hne : p ≠ [] := by intro h; subst h; simp at hk
    rw [List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem]
    congr 1
    simp [hkeq]
  exact ⟨p[k + 1]'hk1, ⟨k, hk1, rfl, rfl⟩, (List.isChain_iff_getElem.mp hch) k hk1⟩

theorem litList_getD_eq {φ : CNF ℕ} {k : ℕ} (hk : k < (litList φ).length) :
    ∃ (j : ℕ) (hj : j < φ.length) (l : Literal ℕ), l ∈ φ[j] ∧
      (litList φ).getD k ((0, 0), false) = ((j, φ.vars.idxOf l.1), l.2) := by
  have hmem : (litList φ)[k] ∈ litList φ := List.getElem_mem hk
  rw [List.getD_eq_getElem _ _ hk]
  unfold litList at hmem
  simp only [List.mem_flatMap, List.mem_map] at hmem
  obtain ⟨⟨c, j⟩, hcj, l, hl, heq⟩ := hmem
  obtain ⟨hj, hc_eq⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hcj)
  exact ⟨j, hj, l, hc_eq ▸ hl, heq.symm⟩

theorem mem_varOccs_iff {φ : CNF ℕ} {i k : ℕ} {val : Bool} :
    k ∈ varOccs φ i val ↔ k < (litList φ).length ∧
      ((litList φ).getD k ((0, 0), false)).1.2 = i ∧
      ((litList φ).getD k ((0, 0), false)).2 ≠ val := by
  simp [varOccs]

theorem bfpEdges_cases {φ : CNF ℕ} {u v : ℕ} (h : (u, v) ∈ bfpEdges φ) :
    (∃ k < (litList φ).length, (u, v) ∈ switchArcs k) ∨
    ((litList φ).length = 0 ∧ u = s2Node ∧ v = t2Node) ∨
    (0 < (litList φ).length ∧ u = s2Node ∧ v = swNode 0 swB) ∨
    (0 < (litList φ).length ∧ u = swNode ((litList φ).length - 1) swD ∧ v = t2Node) ∨
    (0 < (litList φ).length ∧ u = swNode 0 swA ∧ v = t1Node) ∨
    (∃ k, k + 1 < (litList φ).length ∧ u = swNode k swD ∧ v = swNode (k + 1) swB) ∨
    (∃ k, k + 1 < (litList φ).length ∧ u = swNode (k + 1) swA ∧ v = swNode k swC) ∨
    (∃ i < φ.vars.length,
      (u, v) ∈ chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i true) ∨
      (u, v) ∈ chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i false)) ∨
    (∃ k < (litList φ).length,
      let j := ((litList φ).getD k ((0, 0), false)).1.1
      (u = clauseNode j ∧ v = swNode k swRin) ∨
      (u = swNode k swRout ∧ v = clauseNode (j + 1))) ∨
    (u = s1Node ∧ v = varNode 0) ∨
    (u = varNode φ.vars.length ∧ v = clauseNode 0) ∨
    (u = clauseNode φ.length ∧
      v = if (litList φ).length = 0 then t1Node else swNode ((litList φ).length - 1) swC) ∨
    (u = t1Node ∧ v = s2Node) ∨
    (u = t2Node ∧ v = s1Node) := by
  unfold bfpEdges at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ((((⟨k, hk, hsw⟩ | hstack) | ⟨i, hi, hch⟩) | ⟨k, hk, hcl⟩) | hterm)
  · exact Or.inl ⟨k, hk, hsw⟩
  · by_cases hK : (litList φ).length = 0
    · simp only [hK, ↓reduceIte, List.mem_singleton, Prod.mk.injEq] at hstack
      exact Or.inr (Or.inl ⟨hK, hstack⟩)
    · have hKpos : 0 < (litList φ).length := Nat.pos_of_ne_zero hK
      simp only [hK, ↓reduceIte, List.mem_append, List.mem_cons,
        List.mem_flatMap, List.mem_range, Prod.mk.injEq, List.not_mem_nil, or_false] at hstack
      rcases hstack with (h1 | h2 | h3) | ⟨k, hk, h4 | h5⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hKpos, h1⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hKpos, h2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hKpos, h3⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, by omega, h4⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, by omega, h5⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, hch⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨k, hk, hcl⟩))))))))
  · rcases hterm with h1 | h2 | h3 | h4 | h5
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h1)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h2))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl h3)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl h4))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr h5))))))))))))

theorem in_swInternal {φ : CNF ℕ} {k r u : ℕ} (hr : r < 14)
    (hnot : r ≠ swB ∧ r ≠ swLin ∧ r ≠ swRin ∧ r ≠ swC)
    (h : (u, swNode k r) ∈ bfpEdges φ) : (u, swNode k r) ∈ switchArcs k := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, _, hv⟩ | ⟨k', _, _, hv⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', _, ⟨_, hv⟩ | ⟨_, hv⟩⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩
  · have hk : k' = k := by
      rw [mem_switchArcs_iff] at hsw
      rcases hsw with ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
        ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
        ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ <;>
        exact (swNode_inj hr (by decide) hv).1.symm
    exact hk ▸ hsw
  · exfalso; exact (swNode_ne_term k r).2.2.2 h.2.2
  · exfalso; exact hnot.1 (swNode_inj hr (by decide) h.2.2).2
  · exfalso; exact (swNode_ne_term k r).2.2.2 h.2.2
  · exfalso; exact (swNode_ne_term k r).2.1 h.2.2
  · exfalso; exact hnot.1 (swNode_inj hr (by decide) hv).2
  · exfalso; exact hnot.2.2.2 (swNode_inj hr (by decide) hv).2
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact varNode_ne_swNode _ _ _ hv.symm
    · exact hnot.2.1 (swNode_inj hr (by decide) hv).2
    · exact hnot.2.1 (swNode_inj hr (by decide) hv).2
    · exact varNode_ne_swNode _ _ _ hv.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact varNode_ne_swNode _ _ _ hv.symm
    · exact hnot.2.1 (swNode_inj hr (by decide) hv).2
    · exact hnot.2.1 (swNode_inj hr (by decide) hv).2
    · exact varNode_ne_swNode _ _ _ hv.symm
  · exfalso; exact hnot.2.2.1 (swNode_inj hr (by decide) hv).2
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv.symm
  · exfalso; exact varNode_ne_swNode _ _ _ hv.symm
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv.symm
  · exfalso; split_ifs at hv
    · exact (swNode_ne_term k r).2.1 hv
    · exact hnot.2.2.2 (swNode_inj hr (by decide) hv).2
  · exfalso; exact (swNode_ne_term k r).2.2.1 hv
  · exfalso; exact (swNode_ne_term k r).1 hv

theorem out_swInternal {φ : CNF ℕ} {k r v : ℕ} (hr : r < 14)
    (hnot : r ≠ swA ∧ r ≠ swD ∧ r ≠ swLout ∧ r ≠ swRout)
    (h : (swNode k r, v) ∈ bfpEdges φ) : (swNode k r, v) ∈ switchArcs k := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, hu, _⟩ | ⟨k', _, hu, _⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', _, ⟨hu, _⟩ | ⟨hu, _⟩⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩
  · have hk : k' = k := by
      rw [mem_switchArcs_iff] at hsw
      rcases hsw with ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ |
        ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ |
        ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ <;>
        exact (swNode_inj hr (by decide) hu).1.symm
    exact hk ▸ hsw
  · exfalso; exact (swNode_ne_term k r).2.2.1 h.2.1
  · exfalso; exact (swNode_ne_term k r).2.2.1 h.2.1
  · exfalso; exact hnot.2.1 (swNode_inj hr (by decide) h.2.1).2
  · exfalso; exact hnot.1 (swNode_inj hr (by decide) h.2.1).2
  · exfalso; exact hnot.2.1 (swNode_inj hr (by decide) hu).2
  · exfalso; exact hnot.1 (swNode_inj hr (by decide) hu).2
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, hu, _⟩ | ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ |
      ⟨_, _, hu, _⟩
    · exact varNode_ne_swNode _ _ _ hu.symm
    · exact varNode_ne_swNode _ _ _ hu.symm
    · exact hnot.2.2.1 (swNode_inj hr (by decide) hu).2
    · exact hnot.2.2.1 (swNode_inj hr (by decide) hu).2
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, hu, _⟩ | ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ |
      ⟨_, _, hu, _⟩
    · exact varNode_ne_swNode _ _ _ hu.symm
    · exact varNode_ne_swNode _ _ _ hu.symm
    · exact hnot.2.2.1 (swNode_inj hr (by decide) hu).2
    · exact hnot.2.2.1 (swNode_inj hr (by decide) hu).2
  · exfalso; exact clauseNode_ne_swNode _ _ _ hu.symm
  · exfalso; exact hnot.2.2.2 (swNode_inj hr (by decide) hu).2
  · exfalso; exact (swNode_ne_term k r).1 hu
  · exfalso; exact varNode_ne_swNode _ _ _ hu.symm
  · exfalso; exact clauseNode_ne_swNode _ _ _ hu.symm
  · exfalso; exact (swNode_ne_term k r).2.1 hu
  · exfalso; exact (swNode_ne_term k r).2.2.2 hu

private def switchPortArcs : List (ℕ × ℕ) :=
  [ (swC, swX), (swC, swY), (swB, swU), (swB, swV), (swLin, swY2), (swRin, swX2),
    (swY2, swY), (swY2, swD), (swY, swLout), (swY, swV), (swX2, swX), (swX2, swD),
    (swX, swRout), (swX, swU), (swU, swY2), (swU, swA), (swV, swX2), (swV, swA) ]

private lemma in_sw_mem {φ : CNF ℕ} {k r u : ℕ} (hr : r < 14)
    (hnot : r ≠ swB ∧ r ≠ swLin ∧ r ≠ swRin ∧ r ≠ swC)
    (h : (u, swNode k r) ∈ bfpEdges φ) :
    u ∈ (switchPortArcs.filter fun p ↦ p.2 == r).map fun p ↦ swNode k p.1 := by
  have hsw := in_swInternal hr hnot h
  have hmap : switchArcs k = switchPortArcs.map fun p ↦ (swNode k p.1, swNode k p.2) := rfl
  rw [hmap, List.mem_map] at hsw
  obtain ⟨p, hp, hp_eq⟩ := hsw
  have hp_lt : p.1 < 14 ∧ p.2 < 14 := by
    simp only [switchPortArcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h1 := congrArg Prod.fst hp_eq
  have h2 := (swNode_inj hp_lt.2 hr (congrArg Prod.snd hp_eq)).2
  exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, beq_iff_eq.mpr h2⟩, h1⟩

private lemma out_sw_mem {φ : CNF ℕ} {k r v : ℕ} (hr : r < 14)
    (hnot : r ≠ swA ∧ r ≠ swD ∧ r ≠ swLout ∧ r ≠ swRout)
    (h : (swNode k r, v) ∈ bfpEdges φ) :
    v ∈ (switchPortArcs.filter fun p ↦ p.1 == r).map fun p ↦ swNode k p.2 := by
  have hsw := out_swInternal hr hnot h
  have hmap : switchArcs k = switchPortArcs.map fun p ↦ (swNode k p.1, swNode k p.2) := rfl
  rw [hmap, List.mem_map] at hsw
  obtain ⟨p, hp, hp_eq⟩ := hsw
  have hp_lt : p.1 < 14 ∧ p.2 < 14 := by
    simp only [switchPortArcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h1 := (swNode_inj hp_lt.1 hr (congrArg Prod.fst hp_eq)).2
  have h2 := congrArg Prod.snd hp_eq
  exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, beq_iff_eq.mpr h1⟩, h2⟩

theorem in_swA {φ : CNF ℕ} {k u : ℕ} (h : (u, swNode k swA) ∈ bfpEdges φ) :
    u = swNode k swU ∨ u = swNode k swV := by
  simpa [switchPortArcs] using in_sw_mem (by decide) (by decide) h

theorem out_swB {φ : CNF ℕ} {k v : ℕ} (h : (swNode k swB, v) ∈ bfpEdges φ) :
    v = swNode k swU ∨ v = swNode k swV := by
  simpa [switchPortArcs] using out_sw_mem (by decide) (by decide) h

theorem in_swU {φ : CNF ℕ} {k u : ℕ} (h : (u, swNode k swU) ∈ bfpEdges φ) :
    u = swNode k swB ∨ u = swNode k swX := by
  simpa [switchPortArcs] using in_sw_mem (by decide) (by decide) h

theorem in_swV {φ : CNF ℕ} {k u : ℕ} (h : (u, swNode k swV) ∈ bfpEdges φ) :
    u = swNode k swB ∨ u = swNode k swY := by
  simpa [switchPortArcs] using in_sw_mem (by decide) (by decide) h

theorem out_swU {φ : CNF ℕ} {k v : ℕ} (h : (swNode k swU, v) ∈ bfpEdges φ) :
    v = swNode k swY2 ∨ v = swNode k swA := by
  simpa [switchPortArcs] using out_sw_mem (by decide) (by decide) h

theorem out_swV {φ : CNF ℕ} {k v : ℕ} (h : (swNode k swV, v) ∈ bfpEdges φ) :
    v = swNode k swX2 ∨ v = swNode k swA := by
  simpa [switchPortArcs] using out_sw_mem (by decide) (by decide) h

theorem in_swX {φ : CNF ℕ} {k u : ℕ} (h : (u, swNode k swX) ∈ bfpEdges φ) :
    u = swNode k swC ∨ u = swNode k swX2 := by
  simpa [switchPortArcs] using in_sw_mem (by decide) (by decide) h

theorem in_swY {φ : CNF ℕ} {k u : ℕ} (h : (u, swNode k swY) ∈ bfpEdges φ) :
    u = swNode k swC ∨ u = swNode k swY2 := by
  simpa [switchPortArcs] using in_sw_mem (by decide) (by decide) h

theorem out_swX2 {φ : CNF ℕ} {k v : ℕ} (h : (swNode k swX2, v) ∈ bfpEdges φ) :
    v = swNode k swX ∨ v = swNode k swD := by
  simpa [switchPortArcs] using out_sw_mem (by decide) (by decide) h

theorem out_swY2 {φ : CNF ℕ} {k v : ℕ} (h : (swNode k swY2, v) ∈ bfpEdges φ) :
    v = swNode k swY ∨ v = swNode k swD := by
  simpa [switchPortArcs] using out_sw_mem (by decide) (by decide) h

theorem in_swX2 {φ : CNF ℕ} {k u : ℕ} (h : (u, swNode k swX2) ∈ bfpEdges φ) :
    u = swNode k swRin ∨ u = swNode k swV := by
  simpa [switchPortArcs] using in_sw_mem (by decide) (by decide) h

theorem in_swY2 {φ : CNF ℕ} {k u : ℕ} (h : (u, swNode k swY2) ∈ bfpEdges φ) :
    u = swNode k swLin ∨ u = swNode k swU := by
  simpa [switchPortArcs] using in_sw_mem (by decide) (by decide) h

theorem in_swRout {φ : CNF ℕ} {k u : ℕ} (h : (u, swNode k swRout) ∈ bfpEdges φ) :
    u = swNode k swX := by
  simpa [switchPortArcs] using in_sw_mem (by decide) (by decide) h

theorem in_swLout {φ : CNF ℕ} {k u : ℕ} (h : (u, swNode k swLout) ∈ bfpEdges φ) :
    u = swNode k swY := by
  simpa [switchPortArcs] using in_sw_mem (by decide) (by decide) h

theorem in_t1Node {φ : CNF ℕ} {u : ℕ} (h : (u, t1Node) ∈ bfpEdges φ) :
    ((litList φ).length = 0 ∧ u = clauseNode φ.length) ∨
    (0 < (litList φ).length ∧ u = swNode 0 swA) := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, _, hv⟩ | ⟨k', _, _, hv⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', _, ⟨_, hv⟩ | ⟨_, hv⟩⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨hu, hv⟩ | ⟨_, hv⟩ | ⟨_,
      hv⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ <;>
      exact (swNode_ne_term _ _).2.1 hv.symm
  · exfalso; exact absurd h.2.2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.1 h.2.2.symm
  · exfalso; exact absurd h.2.2 (by decide)
  · exact Or.inr ⟨h.1, h.2.1⟩
  · exfalso; exact (swNode_ne_term _ _).2.1 hv.symm
  · exfalso; exact (swNode_ne_term _ _).2.1 hv.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact (varNode_ne_term _).2.1 hv.symm
    · exact (swNode_ne_term _ _).2.1 hv.symm
    · exact (swNode_ne_term _ _).2.1 hv.symm
    · exact (varNode_ne_term _).2.1 hv.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact (varNode_ne_term _).2.1 hv.symm
    · exact (swNode_ne_term _ _).2.1 hv.symm
    · exact (swNode_ne_term _ _).2.1 hv.symm
    · exact (varNode_ne_term _).2.1 hv.symm
  · exfalso; exact (swNode_ne_term _ _).2.1 hv.symm
  · exfalso; exact (clauseNode_ne_term _).2.1 hv.symm
  · exfalso; exact (varNode_ne_term _).2.1 hv.symm
  · exfalso; exact (clauseNode_ne_term _).2.1 hv.symm
  · split_ifs at hv with hK
    · exact Or.inl ⟨hK, hu⟩
    · exfalso; exact (swNode_ne_term _ _).2.1 hv.symm
  · exfalso; dsimp only [s1Node, t1Node, s2Node, t2Node] at *; omega
  · exfalso; dsimp only [s1Node, t1Node, s2Node, t2Node] at *; omega

theorem out_s2Node {φ : CNF ℕ} {v : ℕ} (h : (s2Node, v) ∈ bfpEdges φ) :
    ((litList φ).length = 0 ∧ v = t2Node) ∨
    (0 < (litList φ).length ∧ v = swNode 0 swB) := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, hu, _⟩ | ⟨k', _, hu, _⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', _, ⟨hu, _⟩ | ⟨hu, _⟩⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ |
      ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ |
      ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ <;>
      exact (swNode_ne_term _ _).2.2.1 hu.symm
  · exact Or.inl ⟨h.1, h.2.2⟩
  · exact Or.inr ⟨h.1, h.2.2⟩
  · exfalso; exact (swNode_ne_term _ _).2.2.1 h.2.1.symm
  · exfalso; exact (swNode_ne_term _ _).2.2.1 h.2.1.symm
  · exfalso; exact (swNode_ne_term _ _).2.2.1 hu.symm
  · exfalso; exact (swNode_ne_term _ _).2.2.1 hu.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, hu, _⟩ | ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ |
      ⟨_, _, hu, _⟩
    · exact (varNode_ne_term _).2.2.1 hu.symm
    · exact (varNode_ne_term _).2.2.1 hu.symm
    · exact (swNode_ne_term _ _).2.2.1 hu.symm
    · exact (swNode_ne_term _ _).2.2.1 hu.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, hu, _⟩ | ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ |
      ⟨_, _, hu, _⟩
    · exact (varNode_ne_term _).2.2.1 hu.symm
    · exact (varNode_ne_term _).2.2.1 hu.symm
    · exact (swNode_ne_term _ _).2.2.1 hu.symm
    · exact (swNode_ne_term _ _).2.2.1 hu.symm
  · exfalso; exact (clauseNode_ne_term _).2.2.1 hu.symm
  · exfalso; exact (swNode_ne_term _ _).2.2.1 hu.symm
  · exfalso; dsimp only [s1Node, t1Node, s2Node, t2Node] at *; omega
  · exfalso; exact (varNode_ne_term _).2.2.1 hu.symm
  · exfalso; exact (clauseNode_ne_term _).2.2.1 hu.symm
  · exfalso; dsimp only [s1Node, t1Node, s2Node, t2Node] at *; omega
  · exfalso; dsimp only [s1Node, t1Node, s2Node, t2Node] at *; omega

theorem out_t1Node {φ : CNF ℕ} {v : ℕ} (h : (t1Node, v) ∈ bfpEdges φ) : v = s2Node := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, hu, _⟩ | ⟨k', _, hu, _⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', _, ⟨hu, _⟩ | ⟨hu, _⟩⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨_, hv⟩ | ⟨hu, _⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ |
      ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ |
      ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ <;>
      exact (swNode_ne_term _ _).2.1 hu.symm
  · exfalso; exact absurd h.2.1 (by decide)
  · exfalso; exact absurd h.2.1 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.1 h.2.1.symm
  · exfalso; exact (swNode_ne_term _ _).2.1 h.2.1.symm
  · exfalso; exact (swNode_ne_term _ _).2.1 hu.symm
  · exfalso; exact (swNode_ne_term _ _).2.1 hu.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, hu, _⟩ | ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ |
      ⟨_, _, hu, _⟩
    · exact (varNode_ne_term _).2.1 hu.symm
    · exact (varNode_ne_term _).2.1 hu.symm
    · exact (swNode_ne_term _ _).2.1 hu.symm
    · exact (swNode_ne_term _ _).2.1 hu.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, hu, _⟩ | ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ |
      ⟨_, _, hu, _⟩
    · exact (varNode_ne_term _).2.1 hu.symm
    · exact (varNode_ne_term _).2.1 hu.symm
    · exact (swNode_ne_term _ _).2.1 hu.symm
    · exact (swNode_ne_term _ _).2.1 hu.symm
  · exfalso; exact (clauseNode_ne_term _).2.1 hu.symm
  · exfalso; exact (swNode_ne_term _ _).2.1 hu.symm
  · exfalso; dsimp only [s1Node, t1Node, s2Node, t2Node] at *; omega
  · exfalso; exact (varNode_ne_term _).2.1 hu.symm
  · exfalso; exact (clauseNode_ne_term _).2.1 hu.symm
  · exact hv
  · exfalso; dsimp only [s1Node, t1Node, s2Node, t2Node] at *; omega

theorem out_t2Node {φ : CNF ℕ} {v : ℕ} (h : (t2Node, v) ∈ bfpEdges φ) : v = s1Node := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, hu, _⟩ | ⟨k', _, hu, _⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', _, ⟨hu, _⟩ | ⟨hu, _⟩⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨_, hv⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ |
      ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ |
      ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ <;>
      exact (swNode_ne_term _ _).2.2.2 hu.symm
  · exfalso; exact absurd h.2.1 (by decide)
  · exfalso; exact absurd h.2.1 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.2.2 h.2.1.symm
  · exfalso; exact (swNode_ne_term _ _).2.2.2 h.2.1.symm
  · exfalso; exact (swNode_ne_term _ _).2.2.2 hu.symm
  · exfalso; exact (swNode_ne_term _ _).2.2.2 hu.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, hu, _⟩ | ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ |
      ⟨_, _, hu, _⟩
    · exact (varNode_ne_term _).2.2.2 hu.symm
    · exact (varNode_ne_term _).2.2.2 hu.symm
    · exact (swNode_ne_term _ _).2.2.2 hu.symm
    · exact (swNode_ne_term _ _).2.2.2 hu.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, hu, _⟩ | ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ |
      ⟨_, _, hu, _⟩
    · exact (varNode_ne_term _).2.2.2 hu.symm
    · exact (varNode_ne_term _).2.2.2 hu.symm
    · exact (swNode_ne_term _ _).2.2.2 hu.symm
    · exact (swNode_ne_term _ _).2.2.2 hu.symm
  · exfalso; exact (clauseNode_ne_term _).2.2.2 hu.symm
  · exfalso; exact (swNode_ne_term _ _).2.2.2 hu.symm
  · exfalso; dsimp only [s1Node, t1Node, s2Node, t2Node] at *; omega
  · exfalso; exact (varNode_ne_term _).2.2.2 hu.symm
  · exfalso; exact (clauseNode_ne_term _).2.2.2 hu.symm
  · exfalso; dsimp only [s1Node, t1Node, s2Node, t2Node] at *; omega
  · exact hv

theorem in_swC {φ : CNF ℕ} {k u : ℕ} (hk : k < (litList φ).length)
    (h : (u, swNode k swC) ∈ bfpEdges φ) :
    (k + 1 < (litList φ).length ∧ u = swNode (k + 1) swA) ∨
    (k + 1 = (litList φ).length ∧ u = clauseNode φ.length) := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, _, hv⟩ | ⟨k', hk', hu, hv⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', _, ⟨_, hv⟩ | ⟨_, hv⟩⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨hu, hv⟩ | ⟨_, hv⟩ | ⟨_,
      hv⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ <;>
      exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.2.2 h.2.2
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) h.2.2).2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.2.2 h.2.2
  · exfalso; exact (swNode_ne_term _ _).2.1 h.2.2
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · have hkk := (swNode_inj (by decide) (by decide) hv).1
    subst hkk
    exact Or.inl ⟨hk', hu⟩
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact varNode_ne_swNode _ _ _ hv.symm
    · exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
    · exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
    · exact varNode_ne_swNode _ _ _ hv.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact varNode_ne_swNode _ _ _ hv.symm
    · exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
    · exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
    · exact varNode_ne_swNode _ _ _ hv.symm
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv.symm
  · exfalso; exact varNode_ne_swNode _ _ _ hv.symm
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv.symm
  · split_ifs at hv with hK
    · exfalso; exact (swNode_ne_term _ _).2.1 hv
    · have hkk := (swNode_inj (by decide) (by decide) hv).1
      exact Or.inr ⟨by omega, hu⟩
  · exfalso; exact (swNode_ne_term _ _).2.2.1 hv
  · exfalso; exact (swNode_ne_term _ _).1 hv

theorem out_swD {φ : CNF ℕ} {k v : ℕ} (hk : k < (litList φ).length)
    (h : (swNode k swD, v) ∈ bfpEdges φ) :
    (k + 1 < (litList φ).length ∧ v = swNode (k + 1) swB) ∨
    (k + 1 = (litList φ).length ∧ v = t2Node) := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', hk', hu, hv⟩ | ⟨k', _, hu, _⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', _, ⟨hu, _⟩ | ⟨hu, _⟩⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ |
      ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ |
      ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ <;>
      exact absurd (swNode_inj (by decide) (by decide) hu).2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.2.1 h.2.1
  · exfalso; exact (swNode_ne_term _ _).2.2.1 h.2.1
  · have hkk := (swNode_inj (by decide) (by decide) h.2.1).1
    exact Or.inr ⟨by omega, h.2.2⟩
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) h.2.1).2 (by decide)
  · have hkk := (swNode_inj (by decide) (by decide) hu).1
    subst hkk
    exact Or.inl ⟨hk', hv⟩
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) hu).2 (by decide)
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, hu, _⟩ | ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ |
      ⟨_, _, hu, _⟩
    · exact varNode_ne_swNode _ _ _ hu.symm
    · exact varNode_ne_swNode _ _ _ hu.symm
    · exact absurd (swNode_inj (by decide) (by decide) hu).2 (by decide)
    · exact absurd (swNode_inj (by decide) (by decide) hu).2 (by decide)
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, hu, _⟩ | ⟨_, _, hu, _⟩ | ⟨_, _, _, _, hu, _⟩ |
      ⟨_, _, hu, _⟩
    · exact varNode_ne_swNode _ _ _ hu.symm
    · exact varNode_ne_swNode _ _ _ hu.symm
    · exact absurd (swNode_inj (by decide) (by decide) hu).2 (by decide)
    · exact absurd (swNode_inj (by decide) (by decide) hu).2 (by decide)
  · exfalso; exact clauseNode_ne_swNode _ _ _ hu.symm
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) hu).2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).1 hu
  · exfalso; exact varNode_ne_swNode _ _ _ hu.symm
  · exfalso; exact clauseNode_ne_swNode _ _ _ hu.symm
  · exfalso; exact (swNode_ne_term _ _).2.1 hu
  · exfalso; exact (swNode_ne_term _ _).2.2.2 hu

theorem in_clauseNode_succ {φ : CNF ℕ} {j u : ℕ}
    (h : (u, clauseNode (j + 1)) ∈ bfpEdges φ) :
    ∃ k < (litList φ).length,
      ((litList φ).getD k ((0, 0), false)).1.1 = j ∧ u = swNode k swRout := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, _, hv⟩ | ⟨k', _, _, hv⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', hk', ⟨_, hv⟩ | ⟨hu, hv⟩⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_,
      hv⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ <;>
      exact clauseNode_ne_swNode _ _ _ hv
  · exfalso; exact (clauseNode_ne_term _).2.2.2 h.2.2
  · exfalso; exact clauseNode_ne_swNode _ _ _ h.2.2
  · exfalso; exact (clauseNode_ne_term _).2.2.2 h.2.2
  · exfalso; exact (clauseNode_ne_term _).2.1 h.2.2
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact varNode_ne_clauseNode _ _ hv.symm
    · exact clauseNode_ne_swNode _ _ _ hv
    · exact clauseNode_ne_swNode _ _ _ hv
    · exact varNode_ne_clauseNode _ _ hv.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact varNode_ne_clauseNode _ _ hv.symm
    · exact clauseNode_ne_swNode _ _ _ hv
    · exact clauseNode_ne_swNode _ _ _ hv
    · exact varNode_ne_clauseNode _ _ hv.symm
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv
  · have hj := clauseNode_inj hv; exact ⟨k', hk', by omega, hu⟩
  · exfalso; exact varNode_ne_clauseNode _ _ hv.symm
  · exfalso; have := clauseNode_inj hv; omega
  · exfalso; split_ifs at hv
    · exact (clauseNode_ne_term _).2.1 hv
    · exact clauseNode_ne_swNode _ _ _ hv
  · exfalso; exact (clauseNode_ne_term _).2.2.1 hv
  · exfalso; exact (clauseNode_ne_term _).1 hv

theorem in_clauseNode_zero {φ : CNF ℕ} {u : ℕ} (h : (u, clauseNode 0) ∈ bfpEdges φ) :
    u = varNode φ.vars.length := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, _, hv⟩ | ⟨k', _, _, hv⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', _, ⟨_, hv⟩ | ⟨_, hv⟩⟩ | ⟨_, hv⟩ | ⟨hu, _⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ <;>
      exact clauseNode_ne_swNode _ _ _ hv
  · exfalso; exact (clauseNode_ne_term _).2.2.2 h.2.2
  · exfalso; exact clauseNode_ne_swNode _ _ _ h.2.2
  · exfalso; exact (clauseNode_ne_term _).2.2.2 h.2.2
  · exfalso; exact (clauseNode_ne_term _).2.1 h.2.2
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact varNode_ne_clauseNode _ _ hv.symm
    · exact clauseNode_ne_swNode _ _ _ hv
    · exact clauseNode_ne_swNode _ _ _ hv
    · exact varNode_ne_clauseNode _ _ hv.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact varNode_ne_clauseNode _ _ hv.symm
    · exact clauseNode_ne_swNode _ _ _ hv
    · exact clauseNode_ne_swNode _ _ _ hv
    · exact varNode_ne_clauseNode _ _ hv.symm
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv
  · exfalso; have := clauseNode_inj hv; omega
  · exfalso; exact varNode_ne_clauseNode _ _ hv.symm
  · exact hu
  · exfalso; split_ifs at hv
    · exact (clauseNode_ne_term _).2.1 hv
    · exact clauseNode_ne_swNode _ _ _ hv
  · exfalso; exact (clauseNode_ne_term _).2.2.1 hv
  · exfalso; exact (clauseNode_ne_term _).1 hv

theorem in_swRin {φ : CNF ℕ} {k u : ℕ}
    (h : (u, swNode k swRin) ∈ bfpEdges φ) :
    u = clauseNode ((litList φ).getD k ((0, 0), false)).1.1 := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, _, hv⟩ | ⟨k', _, _, hv⟩ |
    ⟨i, _, hch | hch⟩ | ⟨k', _, ⟨hu, hv⟩ | ⟨_, hv⟩⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_,
      hv⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ <;>
      exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.2.2 h.2.2
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) h.2.2).2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.2.2 h.2.2
  · exfalso; exact (swNode_ne_term _ _).2.1 h.2.2
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact varNode_ne_swNode _ _ _ hv.symm
    · exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
    · exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
    · exact varNode_ne_swNode _ _ _ hv.symm
  · exfalso; rcases mem_chainArcs_cases hch with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
      ⟨_, _, _, hv⟩
    · exact varNode_ne_swNode _ _ _ hv.symm
    · exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
    · exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
    · exact varNode_ne_swNode _ _ _ hv.symm
  · have hkk := (swNode_inj (by decide) (by decide) hv).1
    subst hkk; exact hu
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv.symm
  · exfalso; exact varNode_ne_swNode _ _ _ hv.symm
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv.symm
  · exfalso; split_ifs at hv
    · exact (swNode_ne_term _ _).2.1 hv
    · exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.2.1 hv
  · exfalso; exact (swNode_ne_term _ _).1 hv

theorem in_varNode_succ {φ : CNF ℕ} {i u : ℕ}
    (h : (u, varNode (i + 1)) ∈ bfpEdges φ) :
    (u, varNode (i + 1)) ∈ chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i true) ∨
    (u, varNode (i + 1)) ∈ chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i false) := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, _, hv⟩ | ⟨k', _, _, hv⟩ |
    ⟨i', _, hch⟩ | ⟨k', _, ⟨_, hv⟩ | ⟨_, hv⟩⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ <;>
      exact varNode_ne_swNode _ _ _ hv
  · exfalso; exact (varNode_ne_term _).2.2.2 h.2.2
  · exfalso; exact varNode_ne_swNode _ _ _ h.2.2
  · exfalso; exact (varNode_ne_term _).2.2.2 h.2.2
  · exfalso; exact (varNode_ne_term _).2.1 h.2.2
  · exfalso; exact varNode_ne_swNode _ _ _ hv
  · exfalso; exact varNode_ne_swNode _ _ _ hv
  · have hi : i' = i := by
      rcases hch with h1 | h1 <;>
        rcases mem_chainArcs_cases h1 with ⟨_, _, hv⟩ | ⟨_, _, _, hv⟩ | ⟨_, _, _, _, _, hv⟩ |
          ⟨_, _, _, hv⟩
      · have := varNode_inj hv; omega
      · exact absurd hv (varNode_ne_swNode _ _ _)
      · exact absurd hv (varNode_ne_swNode _ _ _)
      · have := varNode_inj hv; omega
      · have := varNode_inj hv; omega
      · exact absurd hv (varNode_ne_swNode _ _ _)
      · exact absurd hv (varNode_ne_swNode _ _ _)
      · have := varNode_inj hv; omega
    exact hi ▸ hch
  · exfalso; exact varNode_ne_swNode _ _ _ hv
  · exfalso; exact varNode_ne_clauseNode _ _ hv
  · exfalso; have := varNode_inj hv; omega
  · exfalso; exact varNode_ne_clauseNode _ _ hv
  · exfalso; split_ifs at hv
    · exact (varNode_ne_term _).2.1 hv
    · exact varNode_ne_swNode _ _ _ hv
  · exfalso; exact (varNode_ne_term _).2.2.1 hv
  · exfalso; exact (varNode_ne_term _).1 hv

theorem in_swLin {φ : CNF ℕ} {k u : ℕ} (h : (u, swNode k swLin) ∈ bfpEdges φ) :
    ∃ i < φ.vars.length,
      (u, swNode k swLin) ∈ chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i true) ∨
      (u, swNode k swLin) ∈ chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i false) := by
  rcases bfpEdges_cases h with ⟨k', _, hsw⟩ | h | h | h | h | ⟨k', _, _, hv⟩ | ⟨k', _, _, hv⟩ |
    ⟨i, hi, hch⟩ | ⟨k', _, ⟨_, hv⟩ | ⟨_, hv⟩⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩
  · rw [mem_switchArcs_iff] at hsw
    exfalso
    rcases hsw with ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ |
      ⟨_, hv⟩ | ⟨_, hv⟩ | ⟨_, hv⟩ <;>
      exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.2.2 h.2.2
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) h.2.2).2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.2.2 h.2.2
  · exfalso; exact (swNode_ne_term _ _).2.1 h.2.2
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exact ⟨i, hi, hch⟩
  · exfalso; exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv.symm
  · exfalso; exact varNode_ne_swNode _ _ _ hv.symm
  · exfalso; exact clauseNode_ne_swNode _ _ _ hv.symm
  · exfalso; split_ifs at hv
    · exact (swNode_ne_term _ _).2.1 hv
    · exact absurd (swNode_inj (by decide) (by decide) hv).2 (by decide)
  · exfalso; exact (swNode_ne_term _ _).2.2.1 hv
  · exfalso; exact (swNode_ne_term _ _).1 hv

/-! ### 3. Polynomial-time computability of `toBFP` -/

private lemma computableInPolyTime_varNode :
    ComputableInPolyTime varNode encUnary encNat := by
  unfold varNode
  exact unary_to_binary.comp (by fun_prop)

private lemma computableInPolyTime_clauseNode :
    ComputableInPolyTime clauseNode encUnary encNat := by
  unfold clauseNode
  exact unary_to_binary.comp (by fun_prop)

private lemma computableInPolyTime_swNode :
    ComputableInPolyTime (fun p : ℕ × ℕ ↦ swNode p.1 p.2) (encPair encUnary encUnary) encNat := by
  unfold swNode
  exact unary_to_binary.comp (by fun_prop)

private lemma computableInPolyTime_swNode' {α : Type} {encIn : α ↪ List Bool} {k r : α → ℕ}
    (hk : ComputableInPolyTime k encIn encUnary) (hr : ComputableInPolyTime r encIn encUnary) :
    ComputableInPolyTime (fun x ↦ swNode (k x) (r x)) encIn encNat :=
  computableInPolyTime_swNode.comp (hk.prod hr)

private lemma computableInPolyTime_switchArcs :
    ComputableInPolyTime switchArcs encUnary (encList (encPair encNat encNat)) := by
  unfold switchArcs
  have hmk (r₁ r₂ : ℕ) :
      ComputableInPolyTime (fun k : ℕ ↦ (swNode k r₁, swNode k r₂)) encUnary
        (encPair encNat encNat) :=
    (computableInPolyTime_swNode' id' (const r₁)).prod
      (computableInPolyTime_swNode' id' (const r₂))
  repeat' apply (cons _).comp ((hmk _ _).prod _)
  exact const []

private lemma computableInPolyTime_chainArcs :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × List ℕ ↦ chainArcs p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) (encList encUnary)) (encList (encPair encNat encNat)) := by
  unfold chainArcs
  have h1 : ComputableInPolyTime (fun p : (ℕ × ℕ) × List ℕ ↦ [(p.1.1, p.1.2)])
      (encPair (encPair encNat encNat) (encList encUnary)) (encList (encPair encNat encNat)) := by
    fun_prop
  have hmid : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List ℕ ↦
        (List.range (p.2.length - 1)).map fun i ↦
          (swNode (p.2.getD i 0) swLout, swNode (p.2.getD (i + 1) 0) swLin))
      (encPair (encPair encNat encNat) (encList encUnary)) (encList (encPair encNat encNat)) := by
    refine mapWithInput (by fun_prop) ?_
    refine (computableInPolyTime_swNode' ?_ (const swLout)).prod
      (computableInPolyTime_swNode' ?_ (const swLin))
    · fun_prop
    · exact listGetDWithInput (by fun_prop) (unary_add' (by fun_prop) (const 1)) 0
  have h2 : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List ℕ ↦
        (p.1.1, swNode (p.2.headD 0) swLin) ::
          ((List.range (p.2.length - 1)).map fun i ↦
            (swNode (p.2.getD i 0) swLout, swNode (p.2.getD (i + 1) 0) swLin)) ++
          [(swNode (p.2.getD (p.2.length - 1) 0) swLout, p.1.2)])
      (encPair (encPair encNat encNat) (encList encUnary)) (encList (encPair encNat encNat)) := by
    have hhead : ComputableInPolyTime
        (fun p : (ℕ × ℕ) × List ℕ ↦ (p.1.1, swNode (p.2.headD 0) swLin))
        (encPair (encPair encNat encNat) (encList encUnary)) (encPair encNat encNat) :=
      ((fst (encPair encNat encNat) (encList encUnary)).fst').prod
        (computableInPolyTime_swNode' (by fun_prop) (const swLin))
    have hlast : ComputableInPolyTime
        (fun p : (ℕ × ℕ) × List ℕ ↦ [(swNode (p.2.getD (p.2.length - 1) 0) swLout, p.1.2)])
        (encPair (encPair encNat encNat) (encList encUnary)) (encList (encPair encNat encNat)) :=
      cons' ((computableInPolyTime_swNode'
        (listGetDWithInput (snd (encPair encNat encNat) (encList encUnary))
          (unary_sub' (length_list encUnary |>.comp
            (snd (encPair encNat encNat) (encList encUnary))) (const 1)) 0)
        (const swLout)).prod ((fst (encPair encNat encNat) (encList encUnary)).snd'))
        (const [])
    exact listAppend' (cons' hhead hmid) hlast
  exact (listIsEmpty' encUnary |>.comp (snd (encPair encNat encNat) (encList encUnary))).ite' h1 h2

private lemma computableInPolyTime_litList :
    ComputableInPolyTime litList encCNF
      (encList (encPair (encPair encUnary encUnary) encBool)) := by
  unfold litList encCNF
  have hvars : ComputableInPolyTime (CNF.vars (V := ℕ))
      (encList (encList (encPair encNat encBool))) (encList encNat) :=
    SAT.computableInPolyTime_vars
  refine flatMapWithInput (by fun_prop) ?_
  refine mapWithInput (by fun_prop) ?_
  have hidx : ComputableInPolyTime
      (fun p : (CNF ℕ × (Clause ℕ × ℕ)) × Literal ℕ ↦ p.1.1.vars.idxOf p.2.1)
      (encPair (encPair (encList (encList (encPair encNat encBool)))
        (encPair (encList (encPair encNat encBool)) encUnary)) (encPair encNat encBool))
      encUnary :=
    idxOfWithInput (hvars.comp (by fun_prop)) (by fun_prop)
  exact ((by fun_prop :
    ComputableInPolyTime (fun p : (CNF ℕ × (Clause ℕ × ℕ)) × Literal ℕ ↦ p.1.2.2)
    _ encUnary).prod hidx).prod (by fun_prop)

private lemma computableInPolyTime_varOccs :
    ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × Bool ↦ varOccs p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF encUnary) encBool) (encList encUnary) := by
  unfold varOccs
  have hlits : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × Bool ↦ litList p.1.1)
      (encPair (encPair encCNF encUnary) encBool)
      (encList (encPair (encPair encUnary encUnary) encBool)) :=
    computableInPolyTime_litList.comp (by fun_prop)
  refine filterWithInput (range.comp (length_list _ |>.comp hlits)) ?_
  have hlit : ComputableInPolyTime
      (fun q : ((CNF ℕ × ℕ) × Bool) × ℕ ↦ (litList q.1.1.1).getD q.2 ((0, 0), false))
      (encPair (encPair (encPair encCNF encUnary) encBool) encUnary)
      (encPair (encPair encUnary encUnary) encBool) :=
    listGetDWithInput (hlits.comp (fst _ _)) (snd _ _) ((0, 0), false)
  have hpred : ComputableInPolyTime
      (fun q : ((CNF ℕ × ℕ) × Bool) × ℕ ↦
        let lit := (litList q.1.1.1).getD q.2 ((0, 0), false)
        (lit.1.2 == q.1.1.2) && !(lit.2 == q.1.2))
      (encPair (encPair (encPair encCNF encUnary) encBool) encUnary) encBool :=
    bool_and' (unary_beq (hlit.fst'.snd') (by fun_prop))
      (bool_not.comp (ComputableInPolyTime.beq (hlit.snd') (by fun_prop)))
  exact hpred.of_enc_eq fun q ↦ congrArg encBool (by rw [Bool.eq_iff_iff]; simp [beq_iff_eq])

private lemma computableInPolyTime_bfpVertices :
    ComputableInPolyTime bfpVertices encCNF (encList encNat) := by
  unfold bfpVertices
  have hN : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.vars.length) encCNF encUnary :=
    SAT.computableInPolyTime_vars_length id'
  have hM : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.length) encCNF encUnary :=
    SAT.computableInPolyTime_length id'
  have hK : ComputableInPolyTime (fun φ : CNF ℕ ↦ (litList φ).length) encCNF encUnary :=
    (length_list _).comp computableInPolyTime_litList
  have hV : ComputableInPolyTime (fun φ : CNF ℕ ↦ (List.range (φ.vars.length + 1)).map varNode)
      encCNF (encList encNat) :=
    mapWithInput (range.comp (unary_add' hN (const 1)))
      (computableInPolyTime_varNode.comp (snd _ _))
  have hC : ComputableInPolyTime (fun φ : CNF ℕ ↦ (List.range (φ.length + 1)).map clauseNode)
      encCNF (encList encNat) :=
    mapWithInput (range.comp (unary_add' hM (const 1)))
      (computableInPolyTime_clauseNode.comp (snd _ _))
  have hS : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range (litList φ).length).flatMap fun k ↦
        (List.range 14).map fun r ↦ swNode k r)
      encCNF (encList encNat) :=
    flatMapWithInput (range.comp hK)
      (mapWithInput (encA := encUnary) (const (List.range 14))
        (computableInPolyTime_swNode'
          ((fst (encPair encCNF encUnary) encUnary).snd')
          (snd (encPair encCNF encUnary) encUnary)))
  exact listAppend' (listAppend' (listAppend' (const [s1Node, t1Node, s2Node, t2Node]) hV) hC) hS

private lemma computableInPolyTime_bfpEdges :
    ComputableInPolyTime bfpEdges encCNF (encList (encPair encNat encNat)) := by
  unfold bfpEdges
  have hN : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.vars.length) encCNF encUnary :=
    SAT.computableInPolyTime_vars_length id'
  have hM : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.length) encCNF encUnary :=
    SAT.computableInPolyTime_length id'
  have hK : ComputableInPolyTime (fun φ : CNF ℕ ↦ (litList φ).length) encCNF encUnary :=
    (length_list _).comp computableInPolyTime_litList
  have hK0 : ComputableInPolyTime (fun φ : CNF ℕ ↦ decide ((litList φ).length = 0))
      encCNF encBool :=
    (unary_beq hK (const 0)).of_enc_eq fun φ ↦ congrArg encBool (by rw [Bool.eq_iff_iff]; simp)
  have h1 : ComputableInPolyTime
      (fun φ : CNF ℕ ↦ (List.range (litList φ).length).flatMap switchArcs)
      encCNF (encList (encPair encNat encNat)) :=
    flatMapWithInput (range.comp hK) (computableInPolyTime_switchArcs.comp (snd encCNF encUnary))
  have h2 : ComputableInPolyTime
      (fun φ : CNF ℕ ↦
        if (litList φ).length = 0 then [(s2Node, t2Node)]
        else [(s2Node, swNode 0 swB), (swNode ((litList φ).length - 1) swD, t2Node),
            (swNode 0 swA, t1Node)] ++
          ((List.range ((litList φ).length - 1)).flatMap fun k ↦
            [(swNode k swD, swNode (k + 1) swB), (swNode (k + 1) swA, swNode k swC)]))
      encCNF (encList (encPair encNat encNat)) := by
    have hpre : ComputableInPolyTime
        (fun φ : CNF ℕ ↦
          [(s2Node, swNode 0 swB), (swNode ((litList φ).length - 1) swD, t2Node),
            (swNode 0 swA, t1Node)])
        encCNF (encList (encPair encNat encNat)) :=
      cons' (const (s2Node, swNode 0 swB))
        (cons' ((computableInPolyTime_swNode' (unary_sub' hK (const 1)) (const swD)).prod
          (const t2Node)) (const [(swNode 0 swA, t1Node)]))
    have hstk : ComputableInPolyTime
        (fun φ : CNF ℕ ↦
          (List.range ((litList φ).length - 1)).flatMap fun k ↦
            [(swNode k swD, swNode (k + 1) swB), (swNode (k + 1) swA, swNode k swC)])
        encCNF (encList (encPair encNat encNat)) := by
      refine flatMapWithInput (range.comp (unary_sub' hK (const 1))) ?_
      have ha := (computableInPolyTime_swNode' (snd encCNF encUnary) (const swD)).prod
        (computableInPolyTime_swNode' (unary_add' (snd encCNF encUnary) (const 1)) (const swB))
      have hb := (computableInPolyTime_swNode'
        (unary_add' (snd encCNF encUnary) (const 1)) (const swA)).prod
        (computableInPolyTime_swNode' (snd encCNF encUnary) (const swC))
      exact cons' ha (cons' hb (const []))
    exact (hK0.ite' (const [(s2Node, t2Node)]) (listAppend' hpre hstk)).of_enc_eq
      fun φ ↦ by by_cases h : (litList φ).length = 0 <;> simp [h]
  have h3 : ComputableInPolyTime
      (fun φ : CNF ℕ ↦
        (List.range φ.vars.length).flatMap fun i ↦
          chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i true) ++
          chainArcs (varNode i) (varNode (i + 1)) (varOccs φ i false))
      encCNF (encList (encPair encNat encNat)) := by
    refine flatMapWithInput (range.comp hN) ?_
    have hvi : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ varNode p.2)
        (encPair encCNF encUnary) encNat := computableInPolyTime_varNode.comp (snd encCNF encUnary)
    have hvi1 : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ varNode (p.2 + 1))
        (encPair encCNF encUnary) encNat :=
      computableInPolyTime_varNode.comp (unary_add' (snd encCNF encUnary) (const 1))
    have ht := computableInPolyTime_chainArcs.comp
      ((hvi.prod hvi1).prod (computableInPolyTime_varOccs.comp (id'.prod (const true))))
    have hf := computableInPolyTime_chainArcs.comp
      ((hvi.prod hvi1).prod (computableInPolyTime_varOccs.comp (id'.prod (const false))))
    exact listAppend' ht hf
  have h4 : ComputableInPolyTime
      (fun φ : CNF ℕ ↦
        (List.range (litList φ).length).flatMap fun k ↦
          let j := ((litList φ).getD k ((0, 0), false)).1.1
          [(clauseNode j, swNode k swRin), (swNode k swRout, clauseNode (j + 1))])
      encCNF (encList (encPair encNat encNat)) := by
    refine flatMapWithInput (range.comp hK) ?_
    have hj : ComputableInPolyTime
        (fun p : CNF ℕ × ℕ ↦ ((litList p.1).getD p.2 ((0, 0), false)).1.1)
        (encPair encCNF encUnary) encUnary :=
      (listGetDWithInput (computableInPolyTime_litList.comp (fst encCNF encUnary))
        (snd encCNF encUnary) ((0, 0), false)).fst'.fst'
    have ha := (computableInPolyTime_clauseNode.comp hj).prod
      (computableInPolyTime_swNode' (snd encCNF encUnary) (const swRin))
    have hb := (computableInPolyTime_swNode' (snd encCNF encUnary) (const swRout)).prod
      (computableInPolyTime_clauseNode.comp (unary_add' hj (const 1)))
    exact cons' ha (cons' hb (const []))
  have h5 : ComputableInPolyTime
      (fun φ : CNF ℕ ↦
        [(s1Node, varNode 0), (varNode φ.vars.length, clauseNode 0),
          (clauseNode φ.length,
            if (litList φ).length = 0 then t1Node else swNode ((litList φ).length - 1) swC),
          (t1Node, s2Node), (t2Node, s1Node)])
      encCNF (encList (encPair encNat encNat)) := by
    have hlast : ComputableInPolyTime
        (fun φ : CNF ℕ ↦
          if (litList φ).length = 0 then t1Node else swNode ((litList φ).length - 1) swC)
        encCNF encNat :=
      (hK0.ite' (const t1Node)
        (computableInPolyTime_swNode' (unary_sub' hK (const 1)) (const swC))).of_enc_eq
        fun φ ↦ by by_cases h : (litList φ).length = 0 <;> simp [h]
    exact cons' (const (s1Node, varNode 0))
      (cons' ((computableInPolyTime_varNode.comp hN).prod (const (clauseNode 0)))
        (cons' ((computableInPolyTime_clauseNode.comp hM).prod hlast)
          (const [(t1Node, s2Node), (t2Node, s1Node)])))
  exact listAppend' (listAppend' (listAppend' (listAppend' h1 h2) h3) h4) h5

/-- Polynomial-time computability of `toBFP`. -/
@[fun_prop]
theorem computableInPolyTime_toBFP :
    ComputableInPolyTime toBFP encCNF encPathInstance := by
  unfold toBFP
  exact encPathInstance_mk_polyTime
    (encGraph_mk_polyTime computableInPolyTime_bfpVertices computableInPolyTime_bfpEdges)
    (const t1Node) (const t2Node)

end Cslib.Complexity.BackAndForthPaths
