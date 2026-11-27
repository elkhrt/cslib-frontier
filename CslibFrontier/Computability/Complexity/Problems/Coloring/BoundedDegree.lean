/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.CountingExponents
public import CslibFrontier.Computability.Complexity.Problems.Coloring
public import Mathlib.Combinatorics.SimpleGraph.Finite
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma

/-!
# Bounded-Degree 3-Coloring and `#3-Coloring`: NP-Completeness and Fine-Grained Hardness

Develops `SharpKColoring`, `SharpThreeColoring`, `DegreeFourThreeColoring`, and
`SharpDegreeFourThreeColoring`, proving `NP`-completeness (`DegreeFourThreeColoring_npComplete`),
scaled-parsimonious `SAT`/degree-`4` reductions (`SAT.toCountThreeColoring`,
`ThreeColoring.toDegreeFour`), and unconditional subexponential runtime transfers and `ETH` /
`SharpETH` `2 ^ Ω(n)` lower bounds on maximum-degree-`4` graphs.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing Turing.MultiTapeTM ComputableInPolyTime
open scoped Finset

private theorem getD_eq_getElem {α : Type*} (l : List α) (d : α) {i : ℕ} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
private theorem getD_idxOf {α : Type*} [BEq α] [LawfulBEq α] {l : List α} {x : α} (hx : x ∈ l)
    (d : α) : l.getD (l.idxOf x) d = x := by
  have h := List.idxOf_lt_length_iff.mpr hx; rw [getD_eq_getElem l d h, List.getElem_idxOf h]
private theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a List.mem_cons_self; have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    nlinarith
private theorem computableInPolyTime_tagPair (tag : ℕ) {γ : Type} {enc : γ ↪ List Bool}
    {a b : γ → ℕ} (ha : ComputableInPolyTime a enc encUnary)
    (hb : ComputableInPolyTime b enc encUnary) :
    ComputableInPolyTime (fun x => Nat.pair tag (Nat.pair (a x) (b x))) enc encNat :=
  unary_to_binary.comp (unary_pair.comp ((const tag).prod (unary_pair.comp (ha.prod hb))))

/-- Number of distinct declared vertices of an encoded graph `G`. -/
@[expose] def Graph.numVertices (G : Graph) : ℕ := G.distinctVertices.length
theorem Graph.numVertices_eq_card (G : Graph) :
    G.numVertices = Fintype.card {v // v ∈ G.vertices} := by
  rw [Graph.numVertices, Graph.card_vertexSubtype, Graph.length_distinctVertices]
theorem Graph.numVertices_le_length_vertices (G : Graph) :
    G.numVertices ≤ G.vertices.length := by
  rw [Graph.numVertices, Graph.length_distinctVertices]; exact List.toFinset_card_le G.vertices
/-- **`#k-Coloring`**: the number of proper `k`-colorings of `G.induced`. -/
@[expose] def SharpKColoring (k : ℕ) (G : Graph) : ℕ :=
  (Finset.univ.filter fun c : Fin G.distinctVertices.length → Fin k =>
    ∀ i j : Fin G.distinctVertices.length,
      G.induced.Adj (G.vertexEquiv i) (G.vertexEquiv j) → c i ≠ c j).card
/-- **`#3-Coloring`**: the number of proper `3`-colorings of `G.induced`. -/
abbrev SharpThreeColoring : Graph → ℕ := SharpKColoring 3
/-- Bijection between `G.induced.Coloring (Fin k)` and the filtered table of `SharpKColoring`. -/
def coloringEquiv (k : ℕ) (G : Graph) :
    G.induced.Coloring (Fin k) ≃
      {c : Fin G.distinctVertices.length → Fin k //
        ∀ i j : Fin G.distinctVertices.length,
          G.induced.Adj (G.vertexEquiv i) (G.vertexEquiv j) → c i ≠ c j} where
  toFun C := ⟨fun i => C (G.vertexEquiv i), fun _ _ hadj => C.valid hadj⟩
  invFun c := SimpleGraph.Coloring.mk (fun v => c.1 (G.vertexEquiv.symm v)) fun {_ _} hadj =>
    c.2 _ _ (by simpa using hadj)
  left_inv C := DFunLike.ext _ _ fun v => congrArg C (G.vertexEquiv.apply_symm_apply v)
  right_inv c := Subtype.ext (funext fun i => congrArg c.1 (G.vertexEquiv.symm_apply_apply i))
theorem sharpKColoring_eq_fintype_card {k : ℕ} {G : Graph} {α : Type*} [Fintype α]
    (e : α ≃ G.induced.Coloring (Fin k)) : SharpKColoring k G = Fintype.card α := by
  rw [SharpKColoring, ← Fintype.card_subtype]
  exact Fintype.card_congr ((coloringEquiv k G).symm.trans e.symm)
theorem mem_KColoring_iff_pos_SharpKColoring {k : ℕ} {G : Graph} :
    G ∈ KColoring k ↔ 0 < SharpKColoring k G := by
  rw [KColoring, Set.mem_ofPred_eq, SimpleGraph.Colorable, SharpKColoring, Finset.card_pos,
    Finset.filter_nonempty_iff]
  exact ⟨fun ⟨C⟩ => ⟨(coloringEquiv k G C).1, Finset.mem_univ _, (coloringEquiv k G C).2⟩,
    fun ⟨c, _, hc⟩ => ⟨(coloringEquiv k G).symm ⟨c, hc⟩⟩⟩
theorem sharpKColoring_le_pow_numVertices (k : ℕ) (G : Graph) :
    SharpKColoring k G ≤ k ^ G.numVertices :=
  (Finset.card_filter_le _ _).trans (by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Graph.numVertices, le_rfl])
/-- Executable test checking whether every distinct declared vertex of `G` has degree at most `d`
in `G.induced`. -/
def maxDegreeLeBool (d : ℕ) (G : Graph) : Bool :=
  G.distinctVertices.all fun u => decide ((G.distinctVertices.countP fun v => G.adjBool u v) ≤ d)
theorem maxDegreeLeBool_eq_true_iff (d : ℕ) (G : Graph) :
    maxDegreeLeBool d G = true ↔ G.induced.maxDegree ≤ d := by
  simp only [maxDegreeLeBool, List.all_eq_true, decide_eq_true_eq]
  have hcount : ∀ u : {v // v ∈ G.vertices},
      (G.distinctVertices.countP fun v => G.adjBool u.1 v) = G.induced.degree u := fun u => by
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
      (G.nodup_distinctVertices.filter _), ← SimpleGraph.card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun x hx => ⟨x, Graph.mem_distinctVertices.mp
        (List.mem_of_mem_filter (List.mem_toFinset.mp hx))⟩)
      (fun x hx => ?_) (fun _ _ _ _ h => Subtype.mk.inj h) fun w hw => ?_
    · rw [SimpleGraph.mem_neighborFinset, Graph.induced_adj, ← Graph.adjBool_eq_true_iff]
      exact (List.mem_filter.mp (List.mem_toFinset.mp hx)).2
    · rw [SimpleGraph.mem_neighborFinset, Graph.induced_adj, ← Graph.adjBool_eq_true_iff] at hw
      exact ⟨w.1, List.mem_toFinset.mpr (List.mem_filter.mpr
        ⟨Graph.mem_distinctVertices.mpr w.2, hw⟩), rfl⟩
  exact ⟨fun hall => G.induced.maxDegree_le_of_forall_degree_le d fun u =>
      hcount u ▸ hall u.1 (Graph.mem_distinctVertices.mpr u.2),
    fun hmax u hu => (hcount ⟨u, Graph.mem_distinctVertices.mp hu⟩).symm ▸
      (G.induced.degree_le_maxDegree _).trans hmax⟩
@[fun_prop]
theorem computableInPolyTime_maxDegreeLeBool (d : ℕ) :
    ComputableInPolyTime (maxDegreeLeBool d) encGraph encBool := by
  have hV := Graph.computableInPolyTime_distinctVertices
  unfold maxDegreeLeBool
  exact allWithInput hV (unary_le' (countPWithInput (hV.comp (fst _ _)) (by fun_prop)) (const d))
/-- **`3-Coloring` on graphs of maximum degree at most `4`**. -/
def DegreeFourThreeColoring : Set Graph := {G | G.induced.maxDegree ≤ 4 ∧ G ∈ ThreeColoring}
/-- **`#3-Coloring` guarded to graphs of maximum degree at most `4`**. -/
@[expose] def SharpDegreeFourThreeColoring (G : Graph) : ℕ :=
  if maxDegreeLeBool 4 G then SharpThreeColoring G else 0
theorem mem_DegreeFourThreeColoring_iff_pos {G : Graph} :
    G ∈ DegreeFourThreeColoring ↔ 0 < SharpDegreeFourThreeColoring G := by
  simp only [DegreeFourThreeColoring, Set.mem_ofPred_eq, SharpDegreeFourThreeColoring,
    ← maxDegreeLeBool_eq_true_iff]; split_ifs with h <;> simp [h,
      mem_KColoring_iff_pos_SharpKColoring]
theorem sharpDegreeFourThreeColoring_of_maxDegree_le {G : Graph} (h : G.induced.maxDegree ≤ 4) :
    SharpDegreeFourThreeColoring G = SharpThreeColoring G := by
  simp only [SharpDegreeFourThreeColoring, (maxDegreeLeBool_eq_true_iff 4 G).mpr h, ↓reduceIte]

theorem polyBounded_length_encNat_SharpDegreeFourThreeColoring :
    PolyBounded (fun G : Graph => (encGraph G).length)
      (fun G => (encNat (SharpDegreeFourThreeColoring G)).length) := by
  refine PolyBounded.of_forall_le 3 1 fun G => ?_
  have hle : SharpDegreeFourThreeColoring G ≤ 2 ^ (2 * G.numVertices) := by
    rw [show 2 ^ (2 * G.numVertices) = 4 ^ G.numVertices by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← Nat.pow_mul]]
    unfold SharpDegreeFourThreeColoring; split_ifs
    · exact (sharpKColoring_le_pow_numVertices 3 G).trans (Nat.pow_le_pow_left (by decide) _)
    · exact Nat.zero_le _
  have h1 := (length_encNat_mono hle).trans_eq (length_encNat_two_pow _); rw [pow_one]
  have h2 := G.numVertices_le_length_vertices.trans G.length_vertices_le_encGraph; omega

private theorem any_take_succ {α : Type*} (l : List α) (p : α → Bool) {j : ℕ} (hj : j < l.length) :
    (l.take (j + 1)).any p = ((l.take j).any p || p l[j]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.any_append]
  simp only [Option.toList_some, List.any_cons, List.any_nil, Bool.or_false]

private def fin3Perms : List (Fin 3 × Fin 3 × Fin 3) :=
  [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
private def validNAE (a₀ a₁ a₂ : Fin 3) (u : Fin 3 × Fin 3 × Fin 3) : Bool :=
  decide (u.1 ≠ u.2.1 ∧ u.2.1 ≠ u.2.2 ∧ u.2.2 ≠ u.1 ∧ u.1 ≠ a₀ ∧ u.2.1 ≠ a₁ ∧ u.2.2 ≠ a₂)
private def naeChoice (a₀ a₁ a₂ : Fin 3) (b : Bool) : Fin 3 × Fin 3 × Fin 3 :=
  (fin3Perms.filter (validNAE a₀ a₁ a₂)).getD (if b then 1 else 0) (0, 1, 2)
private def naeBit (a₀ a₁ a₂ : Fin 3) (u : Fin 3 × Fin 3 × Fin 3) : Bool :=
  decide (u = naeChoice a₀ a₁ a₂ true)

private theorem naeChoice_valid (a₀ a₁ a₂ : Fin 3) (b : Bool) (h : ¬(a₀ = a₁ ∧ a₁ = a₂)) :
    validNAE a₀ a₁ a₂ (naeChoice a₀ a₁ a₂ b) = true := by revert a₀ a₁ a₂ b; decide
private theorem naeBit_naeChoice (a₀ a₁ a₂ : Fin 3) (b : Bool) (h : ¬(a₀ = a₁ ∧ a₁ = a₂)) :
    naeBit a₀ a₁ a₂ (naeChoice a₀ a₁ a₂ b) = b := by revert a₀ a₁ a₂ b; decide
private theorem naeChoice_naeBit (a₀ a₁ a₂ : Fin 3) (u : Fin 3 × Fin 3 × Fin 3)
    (h : validNAE a₀ a₁ a₂ u = true) :
    ¬(a₀ = a₁ ∧ a₁ = a₂) ∧ naeChoice a₀ a₁ a₂ (naeBit a₀ a₁ a₂ u) = u := by
  revert a₀ a₁ a₂ u; decide
private theorem orGate_not_mono (cT cF : Fin 3) (hTF : cT ≠ cF) (bx by_ : Bool) :
    let x := if bx then cT else cF; let y := if by_ then cT else cF
    let nz := if (bx || by_) then cF else cT
    ¬(x = y ∧ y = nz) ∧ ¬(x = nz ∧ nz = cT) ∧ ¬(y = nz ∧ nz = cT) := by
  revert cT cF bx by_; decide
private theorem lit_forced (cT cF cB v1 v0 : Fin 3) (b : Bool)
    (hTF : cT ≠ cF) (hFB : cF ≠ cB) (hBT : cB ≠ cT) (h10 : v1 ≠ v0) (h1B : v1 ≠ cB)
    (h0B : v0 ≠ cB) : (if b then v1 else v0) = if decide (v1 = cT) == b then cT else cF := by
  revert cT cF cB v1 v0 b; decide
private theorem fin3_eq_of_ne_two (cT cF cB v : Fin 3)
    (hTF : cT ≠ cF) (hFB : cF ≠ cB) (hBT : cB ≠ cT) (hT : v ≠ cT) (hB : v ≠ cB) : v = cF := by
  revert cT cF cB v; decide
private theorem stage_forced (cT cF cB z nz : Fin 3) (bx by_ : Bool)
    (hTF : cT ≠ cF) (hFB : cF ≠ cB) (hBT : cB ≠ cT) (hznz : z ≠ nz) (hzB : z ≠ cB) (hnzB : nz ≠ cB)
    (ht0 : ¬((if bx then cT else cF) = (if by_ then cT else cF) ∧ (if by_ then cT else cF) = nz))
    (ht1 : ¬((if bx then cT else cF) = nz ∧ nz = cT))
    (ht2 : ¬((if by_ then cT else cF) = nz ∧ nz = cT)) :
    z = (if (bx || by_) then cT else cF) ∧ nz = (if (bx || by_) then cF else cT) := by
  revert cT cF cB z nz bx by_; decide
private def otherPair : Fin 3 → Bool → Fin 3 × Fin 3
  | ⟨0, _⟩, false => (1, 2) | ⟨0, _⟩, true => (2, 1)
  | ⟨1, _⟩, false => (0, 2) | ⟨1, _⟩, true => (2, 0)
  | _, false => (0, 1) | _, true => (1, 0)
private theorem otherPair_valid (c : Fin 3) (b : Bool) :
    (otherPair c b).1 ≠ (otherPair c b).2 ∧ (otherPair c b).1 ≠ c ∧ (otherPair c b).2 ≠ c ∧
      decide ((otherPair c b).2 < (otherPair c b).1) = b := by revert c b; decide
private theorem h5_forced (a b c₁ c₂ p : Fin 3)
    (hab : a ≠ b) (hc₁a : c₁ ≠ a) (hc₁b : c₁ ≠ b)
    (hc₂a : c₂ ≠ a) (hc₂b : c₂ ≠ b) (hpa : p ≠ a) (hpb : p ≠ b) :
    c₂ = c₁ ∧ p = c₁ ∧ otherPair c₁ (decide (b < a)) = (a, b) := by revert a b c₁ c₂ p; decide

/-! ### Scaled-parsimonious `SAT` to `#3-Coloring` reduction (`SAT.toCountThreeColoring`) -/

namespace SAT

def cPalVertex (c : ℕ) : ℕ := Nat.pair 0 c
def cLitIdxVertex (k b : ℕ) : ℕ := Nat.pair 1 (Nat.pair k b)
def cLitVertex (φ : CNF ℕ) (l : Literal ℕ) : ℕ :=
  cLitIdxVertex (φ.distinctVars.idxOf l.1) l.2.toNat
def cOutVertex (i j : ℕ) : ℕ := Nat.pair 2 (Nat.pair i j)
def cNotOutVertex (i j : ℕ) : ℕ := Nat.pair 3 (Nat.pair i j)
def cTriVertex (i j t r : ℕ) : ℕ := Nat.pair 4 (Nat.pair i (Nat.pair j (Nat.pair t r)))
def cTriEdges (i j t a₀ a₁ a₂ : ℕ) : List (ℕ × ℕ) :=
  [(cTriVertex i j t 0, cTriVertex i j t 1), (cTriVertex i j t 1, cTriVertex i j t 2),
    (cTriVertex i j t 2, cTriVertex i j t 0), (cTriVertex i j t 0, a₀),
    (cTriVertex i j t 1, a₁), (cTriVertex i j t 2, a₂)]
def cStageEdges (φ : CNF ℕ) (i j : ℕ) (l : Literal ℕ) : List (ℕ × ℕ) :=
  [(cOutVertex i (j + 1), cNotOutVertex i j), (cOutVertex i (j + 1), cPalVertex 2),
    (cNotOutVertex i j, cPalVertex 2)] ++
    cTriEdges i j 0 (cOutVertex i j) (cLitVertex φ l) (cNotOutVertex i j) ++
    cTriEdges i j 1 (cOutVertex i j) (cNotOutVertex i j) (cPalVertex 0) ++
    cTriEdges i j 2 (cLitVertex φ l) (cNotOutVertex i j) (cPalVertex 0)
def cClauseEdges (φ : CNF ℕ) (i : ℕ) (c : Clause ℕ) : List (ℕ × ℕ) :=
  [(cOutVertex i 0, cPalVertex 0), (cOutVertex i 0, cPalVertex 2),
    (cOutVertex i c.length, cPalVertex 1), (cOutVertex i c.length, cPalVertex 2)] ++
    c.zipIdx.flatMap fun l => cStageEdges φ i l.2 l.1
def cVarEdges (k : ℕ) : List (ℕ × ℕ) :=
  [(cLitIdxVertex k 1, cLitIdxVertex k 0), (cLitIdxVertex k 1, cPalVertex 2),
    (cLitIdxVertex k 0, cPalVertex 2)]
def countColoringEdges (φ : CNF ℕ) : List (ℕ × ℕ) :=
  [(cPalVertex 0, cPalVertex 1), (cPalVertex 1, cPalVertex 2), (cPalVertex 2, cPalVertex 0)] ++
    (List.range φ.distinctVars.length).flatMap cVarEdges ++
    φ.zipIdx.flatMap fun c => cClauseEdges φ c.2 c.1
private def stageVertices (i : ℕ) (l : Literal ℕ × ℕ) : List ℕ :=
  [cOutVertex i (l.2 + 1), cNotOutVertex i l.2,
    cTriVertex i l.2 0 0, cTriVertex i l.2 0 1, cTriVertex i l.2 0 2,
    cTriVertex i l.2 1 0, cTriVertex i l.2 1 1, cTriVertex i l.2 1 2,
    cTriVertex i l.2 2 0, cTriVertex i l.2 2 1, cTriVertex i l.2 2 2]
def countColoringVertices (φ : CNF ℕ) : List ℕ :=
  [cPalVertex 0, cPalVertex 1, cPalVertex 2] ++
    ((List.range φ.distinctVars.length).flatMap fun k => [cLitIdxVertex k 1, cLitIdxVertex k 0]) ++
    φ.zipIdx.flatMap fun c => [cOutVertex c.2 0] ++ c.1.zipIdx.flatMap (stageVertices c.2)

/-- **Scaled-parsimonious `SAT`-to-`#3-Coloring` gadget graph**. -/
def toCountThreeColoring (φ : CNF ℕ) : Graph := ⟨countColoringVertices φ, countColoringEdges φ⟩

private theorem mem_countColoringVertices_iff {φ : CNF ℕ} {v : ℕ} :
    v ∈ countColoringVertices φ ↔
      (∃ c < 3, v = cPalVertex c) ∨ (∃ k < φ.distinctVars.length, ∃ b < 2, v = cLitIdxVertex k b) ∨
      (∃ (i : ℕ) (hi : i < φ.length), ∃ j ≤ (φ[i]'hi).length, v = cOutVertex i j) ∨
      (∃ (i : ℕ) (hi : i < φ.length), ∃ j < (φ[i]'hi).length, v = cNotOutVertex i j) ∨
      (∃ (i : ℕ) (hi : i < φ.length), ∃ j < (φ[i]'hi).length,
        ∃ t < 3, ∃ r < 3, v = cTriVertex i j t r) := by
  simp only [countColoringVertices, stageVertices, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_flatMap, List.mem_range, List.mem_zipIdx_iff_getElem?]
  refine ⟨?_, ?_⟩
  · rintro (htop | ⟨⟨cl, i⟩, hi, rfl | ⟨⟨l, j⟩, hj, hrest⟩⟩)
    · rcases htop with (rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩
      exacts [Or.inl ⟨0, by omega, rfl⟩, Or.inl ⟨1, by omega, rfl⟩, Or.inl ⟨2, by omega, rfl⟩,
        Or.inr (Or.inl ⟨k, hk, 1, by omega, rfl⟩), Or.inr (Or.inl ⟨k, hk, 0, by omega, rfl⟩)]
    · dsimp only at hi; obtain ⟨hilt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
      exact Or.inr (Or.inr (Or.inl ⟨i, hilt, 0, Nat.zero_le _, rfl⟩))
    · dsimp only at hi hj hrest; obtain ⟨hilt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
      obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hj
      rcases hrest with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact Or.inr (Or.inr (Or.inl ⟨i, hilt, j + 1, hjlt, rfl⟩))
        | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hilt, j, hjlt, rfl⟩)))
        | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hilt, j, hjlt, _, by omega, _, by omega, rfl⟩)))
  · rintro (⟨c, hc, rfl⟩ | ⟨k, hk, b, hb, rfl⟩ | ⟨i, hi, j, hj, rfl⟩ |
      ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, t, ht, r, hr, rfl⟩)
    · interval_cases c <;> simp
    · interval_cases b <;> [exact Or.inl (Or.inr ⟨k, hk, Or.inr rfl⟩);
        exact Or.inl (Or.inr ⟨k, hk, Or.inl rfl⟩)]
    · refine Or.inr ⟨(φ[i], i), by simp [hi], ?_⟩
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      exacts [Or.inl rfl, Or.inr ⟨(φ[i][j - 1], j - 1),
        by simp [show j - 1 < φ[i].length by omega], Or.inl (by rw [Nat.sub_add_cancel hjpos])⟩]
    · exact Or.inr ⟨(φ[i], i), by simp [hi], Or.inr ⟨(φ[i][j], j), by simp [hj],
        Or.inr (Or.inl rfl)⟩⟩
    · refine Or.inr ⟨(φ[i], i), by simp [hi], Or.inr ⟨(φ[i][j], j), by simp [hj], ?_⟩⟩
      interval_cases t <;> interval_cases r <;> simp

private theorem cPal_mem {φ : CNF ℕ} {c : ℕ} (hc : c < 3) :
    cPalVertex c ∈ (toCountThreeColoring φ).vertices :=
  mem_countColoringVertices_iff.mpr (Or.inl ⟨c, hc, rfl⟩)
private theorem cLit_mem {φ : CNF ℕ} {k b : ℕ} (hk : k < φ.distinctVars.length) (hb : b < 2) :
    cLitIdxVertex k b ∈ (toCountThreeColoring φ).vertices :=
  mem_countColoringVertices_iff.mpr (Or.inr (Or.inl ⟨k, hk, b, hb, rfl⟩))
private theorem cOut_mem {φ : CNF ℕ} {i j : ℕ} (hi : i < φ.length) (hj : j ≤ φ[i].length) :
    cOutVertex i j ∈ (toCountThreeColoring φ).vertices :=
  mem_countColoringVertices_iff.mpr (Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, rfl⟩)))
private theorem cNot_mem {φ : CNF ℕ} {i j : ℕ} (hi : i < φ.length) (hj : j < φ[i].length) :
    cNotOutVertex i j ∈ (toCountThreeColoring φ).vertices :=
  mem_countColoringVertices_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, rfl⟩))))
private theorem cTri_mem {φ : CNF ℕ} {i j t r : ℕ} (hi : i < φ.length) (hj : j < φ[i].length)
    (ht : t < 3) (hr : r < 3) : cTriVertex i j t r ∈ (toCountThreeColoring φ).vertices :=
  mem_countColoringVertices_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, t, ht, r, hr,
    rfl⟩))))

private theorem ne_of_mem_countColoringEdges {φ : CNF ℕ} {e : ℕ × ℕ}
    (he : e ∈ countColoringEdges φ) : e.1 ≠ e.2 := by
  simp only [countColoringEdges, cVarEdges, cClauseEdges, cStageEdges, cTriEdges,
    List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he_top | ⟨⟨cl, i⟩, -, he_cl | ⟨⟨l, j⟩, -, he'⟩⟩
  · rcases he_top with (rfl | rfl | rfl) | ⟨k, -, rfl | rfl | rfl⟩ <;>
      simp [cPalVertex, cLitIdxVertex, Nat.pair_eq_pair]
  · rcases he_cl with rfl | rfl | rfl | rfl <;> simp [cOutVertex, cPalVertex, Nat.pair_eq_pair]
  · rcases he' with (((rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      dsimp only [cPalVertex, cLitVertex, cLitIdxVertex, cOutVertex, cNotOutVertex, cTriVertex] <;>
      intro h <;> have := Nat.pair_eq_pair.mp h <;> try { exact absurd this.1 (by decide) } <;>
      have := Nat.pair_eq_pair.mp this.2 <;> have := Nat.pair_eq_pair.mp this.2 <;>
      have := Nat.pair_eq_pair.mp this.2 <;> omega

private theorem adj_of_mem_countColoringEdges {φ : CNF ℕ} {u v : ℕ}
    (he : (u, v) ∈ countColoringEdges φ) : (toCountThreeColoring φ).toSimpleGraph.Adj u v := by
  rw [toCountThreeColoring, Graph.toSimpleGraph_adj]
  exact ⟨ne_of_mem_countColoringEdges he, Or.inl he⟩

private abbrev PalPerm :=
  {p : Fin 3 × Fin 3 × Fin 3 // p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.2.2 ≠ p.1}
private abbrev SatAssign (φ : CNF ℕ) :=
  {τ : φ.vars.toFinset → Bool // φ.eval (φ.extendAssignment τ) = true}
private abbrev OccIdx (φ : CNF ℕ) := Σ i : Fin φ.length, Fin φ[i.val].length
private theorem card_occIdx (φ : CNF ℕ) : Fintype.card (OccIdx φ) = φ.vars.length := by
  rw [Fintype.card_sigma]; simp only [Fintype.card_fin]
  induction φ with
  | nil => simp [CNF.vars]
  | cons c cs ih =>
    simp only [List.length_cons]; rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ, ih,
      CNF.vars, List.flatten_cons, List.map_append, List.length_append, List.length_map]
private def getOccBits {φ : CNF ℕ} (bits : OccIdx φ → Bool × Bool × Bool) (i j : ℕ) :
    Bool × Bool × Bool :=
  if hi : i < φ.length then
    if hj : j < φ[i].length then bits ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ else (false, false, false)
  else (false, false, false)
private theorem getOccBits_of_lt {φ : CNF ℕ} {bits : OccIdx φ → Bool × Bool × Bool}
    {i j : ℕ} (hi : i < φ.length) (hj : j < φ[i].length) :
    getOccBits bits i j = bits ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := by simp [getOccBits, hi, hj]

private def countGadgetColor (φ : CNF ℕ) (p : PalPerm) (τ : φ.vars.toFinset → Bool)
    (bits : OccIdx φ → Bool × Bool × Bool) (n : ℕ) : Fin 3 :=
  let cT := p.1.1; let cF := p.1.2.1; let cB := p.1.2.2; let σ := φ.extendAssignment τ
  match n.unpair.1 with
  | 0 => match n.unpair.2 with | 0 => cT | 1 => cF | _ => cB
  | 1 => if σ (φ.distinctVars.getD n.unpair.2.unpair.1 0) == decide (n.unpair.2.unpair.2 = 1)
         then cT else cF
  | 2 => if ((φ.getD n.unpair.2.unpair.1 []).take n.unpair.2.unpair.2).any (Literal.eval σ) then cT
         else cF
  | 3 => if ((φ.getD n.unpair.2.unpair.1 []).take (n.unpair.2.unpair.2 + 1)).any (Literal.eval σ)
         then cF else cT
  | _ =>
    let i := n.unpair.2.unpair.1; let j := n.unpair.2.unpair.2.unpair.1
    let t := n.unpair.2.unpair.2.unpair.2.unpair.1; let r := n.unpair.2.unpair.2.unpair.2.unpair.2
    let cl := φ.getD i []; let b3 := getOccBits bits i j
    let xCol := if (cl.take j).any (Literal.eval σ) then cT else cF
    let yCol := if Literal.eval σ (cl.getD j (0, false)) then cT else cF
    let nzCol := if (cl.take (j + 1)).any (Literal.eval σ) then cF else cT
    let triple := match t with
      | 0 => naeChoice xCol yCol nzCol b3.1 | 1 => naeChoice xCol nzCol cT b3.2.1
      | _ => naeChoice yCol nzCol cT b3.2.2
    match r with | 0 => triple.1 | 1 => triple.2.1 | _ => triple.2.2

private theorem countGadgetColor_ne_of_cTriEdges {φ : CNF ℕ} (p : PalPerm)
    (τ : φ.vars.toFinset → Bool) (bits : OccIdx φ → Bool × Bool × Bool)
    {i j t a₀ a₁ a₂ : ℕ} (triple : Fin 3 × Fin 3 × Fin 3)
    (htr : ∀ r < 3, countGadgetColor φ p τ bits (cTriVertex i j t r) =
      match r with | 0 => triple.1 | 1 => triple.2.1 | _ => triple.2.2)
    (hv : validNAE (countGadgetColor φ p τ bits a₀) (countGadgetColor φ p τ bits a₁)
      (countGadgetColor φ p τ bits a₂) triple = true) {e : ℕ × ℕ}
    (he : e ∈ cTriEdges i j t a₀ a₁ a₂) :
    countGadgetColor φ p τ bits e.1 ≠ countGadgetColor φ p τ bits e.2 := by
  simp only [validNAE, decide_eq_true_eq] at hv
  have h0 := htr 0 (by omega); have h1 := htr 1 (by omega); have h2 := htr 2 (by omega)
  simp only [cTriEdges, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0 ▸ h1 ▸ hv.1, h1 ▸ h2 ▸ hv.2.1, h2 ▸ h0 ▸ hv.2.2.1,
    h0 ▸ hv.2.2.2.1, h1 ▸ hv.2.2.2.2.1, h2 ▸ hv.2.2.2.2.2]

private theorem countGadgetColor_ne_of_edge {φ : CNF ℕ} (p : PalPerm) (τ : SatAssign φ)
    (bits : OccIdx φ → Bool × Bool × Bool) {e : ℕ × ℕ} (he : e ∈ countColoringEdges φ) :
    countGadgetColor φ p τ.1 bits e.1 ≠ countGadgetColor φ p τ.1 bits e.2 := by
  obtain ⟨hTF, hFB, hBT⟩ := p.2
  simp only [countColoringEdges, List.mem_append, List.mem_flatMap, List.mem_range] at he
  rcases he with (he | ⟨k, -, he⟩) | ⟨⟨cl, i⟩, hi, he⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp [countGadgetColor, cPalVertex, hTF, hFB, hBT]
  · simp only [cVarEdges, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp only [countGadgetColor, cLitIdxVertex, cPalVertex, Nat.unpair_pair] <;>
      cases φ.extendAssignment τ.1 (φ.distinctVars.getD k 0) <;> simp [hTF, hTF.symm, hFB, hBT.symm]
  · dsimp only at he
    have hmem_i := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hi)
    dsimp only at hmem_i; obtain ⟨hilt, rfl⟩ := hmem_i
    have hget_cl : φ.getD i [] = φ[i] := getD_eq_getElem φ [] hilt
    have hsat_cl : φ[i].any (Literal.eval (φ.extendAssignment τ.1)) = true :=
      (CNF.eval_eq_true_iff _ _).mp τ.2 φ[i] (List.getElem_mem hilt)
    simp only [cClauseEdges, List.mem_append, List.mem_flatMap] at he
    rcases he with he | ⟨⟨l, j⟩, hj, he⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;>
        simp only [countGadgetColor, cOutVertex, cPalVertex, Nat.unpair_pair, hget_cl,
          List.take_zero, List.any_nil, Bool.false_eq_true, List.take_length, hsat_cl, ↓reduceIte]
      exacts [hTF.symm, hFB, hTF, hBT.symm]
    · dsimp only at he
      have hmem_j := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hj)
      dsimp only at hmem_j; obtain ⟨hjlt, rfl⟩ := hmem_j
      have hget_l : φ[i].getD j (0, false) = φ[i][j] := getD_eq_getElem φ[i] (0, false) hjlt
      have hlv : φ[i][j].1 ∈ φ.distinctVars := CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr
        ⟨φ[i], List.getElem_mem hilt, φ[i][j].2, List.getElem_mem hjlt⟩)
      have hlit_col : countGadgetColor φ p τ.1 bits (cLitVertex φ φ[i][j]) =
          if Literal.eval (φ.extendAssignment τ.1) φ[i][j] then p.1.1 else p.1.2.1 := by
        simp only [countGadgetColor, cLitVertex, cLitIdxVertex, Nat.unpair_pair, getD_idxOf hlv 0]
        obtain ⟨x, b⟩ := φ[i][j]; rw [Literal.eval_mk]; cases b <;> rfl
      have htake_succ := any_take_succ φ[i] (Literal.eval (φ.extendAssignment τ.1)) hjlt
      let bx := (φ[i].take j).any (Literal.eval (φ.extendAssignment τ.1))
      let by_ := Literal.eval (φ.extendAssignment τ.1) φ[i][j]
      have hnm := orGate_not_mono p.1.1 p.1.2.1 hTF bx by_; let b3 := bits ⟨⟨i, hilt⟩, ⟨j, hjlt⟩⟩
      have hout_col : countGadgetColor φ p τ.1 bits (cOutVertex i j) =
          if bx then p.1.1 else p.1.2.1 := by
        simp only [countGadgetColor, cOutVertex, Nat.unpair_pair, hget_cl]; rfl
      have hnz_col : countGadgetColor φ p τ.1 bits (cNotOutVertex i j) =
          if (bx || by_) then p.1.2.1 else p.1.1 := by
        simp only [countGadgetColor, cNotOutVertex, Nat.unpair_pair, hget_cl, htake_succ]; rfl
      have hpal0_col : countGadgetColor φ p τ.1 bits (cPalVertex 0) = p.1.1 := by
        simp only [countGadgetColor, cPalVertex, Nat.unpair_pair]
      simp only [cStageEdges, List.mem_append] at he
      rcases he with ((he_base | he0) | he1) | he2
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he_base
        rcases he_base with rfl | rfl | rfl <;>
          simp only [countGadgetColor, cOutVertex, cNotOutVertex, cPalVertex, Nat.unpair_pair,
            hget_cl] <;>
          cases (φ[i].take (j + 1)).any (Literal.eval (φ.extendAssignment τ.1)) <;>
          simp [hTF, hTF.symm, hFB, hBT.symm]
      · refine countGadgetColor_ne_of_cTriEdges p τ.1 bits
          (naeChoice (if bx then p.1.1 else p.1.2.1) (if by_ then p.1.1 else p.1.2.1)
            (if (bx || by_) then p.1.2.1 else p.1.1) b3.1) (fun r hr => ?_)
          (hout_col.symm ▸ hlit_col.symm ▸ hnz_col.symm ▸ naeChoice_valid _ _ _ _ hnm.1) he0
        interval_cases r <;> { simp only [countGadgetColor, cTriVertex, Nat.unpair_pair,
          hget_cl, hget_l, htake_succ, getOccBits_of_lt hilt hjlt]; rfl }
      · refine countGadgetColor_ne_of_cTriEdges p τ.1 bits
          (naeChoice (if bx then p.1.1 else p.1.2.1)
            (if (bx || by_) then p.1.2.1 else p.1.1) p.1.1 b3.2.1) (fun r hr => ?_)
          (hout_col.symm ▸ hnz_col.symm ▸ hpal0_col.symm ▸ naeChoice_valid _ _ _ _ hnm.2.1) he1
        interval_cases r <;> { simp only [countGadgetColor, cTriVertex, Nat.unpair_pair,
          hget_cl, htake_succ, getOccBits_of_lt hilt hjlt]; rfl }
      · refine countGadgetColor_ne_of_cTriEdges p τ.1 bits
          (naeChoice (if by_ then p.1.1 else p.1.2.1)
            (if (bx || by_) then p.1.2.1 else p.1.1) p.1.1 b3.2.2) (fun r hr => ?_)
          (hlit_col.symm ▸ hnz_col.symm ▸ hpal0_col.symm ▸ naeChoice_valid _ _ _ _ hnm.2.2) he2
        interval_cases r <;> { simp only [countGadgetColor, cTriVertex, Nat.unpair_pair,
          hget_cl, hget_l, htake_succ, getOccBits_of_lt hilt hjlt]; rfl }

private def decTau {φ : CNF ℕ} (C : (toCountThreeColoring φ).induced.Coloring (Fin 3)) :
    φ.vars.toFinset → Bool := fun x =>
  decide (C ⟨cLitIdxVertex (φ.distinctVars.idxOf x.1) 1, cLit_mem
    (List.idxOf_lt_length_iff.mpr (CNF.mem_distinctVars.mpr (List.mem_toFinset.mp x.2)))
    (by omega)⟩ = C ⟨cPalVertex 0, cPal_mem (by omega)⟩)
private def decTri {φ : CNF ℕ} (C : (toCountThreeColoring φ).induced.Coloring (Fin 3))
    {i j : ℕ} (hi : i < φ.length) (hj : j < φ[i].length) (t : ℕ) (ht : t < 3) :
    Fin 3 × Fin 3 × Fin 3 :=
  (C ⟨cTriVertex i j t 0, cTri_mem hi hj ht (by omega)⟩,
   C ⟨cTriVertex i j t 1, cTri_mem hi hj ht (by omega)⟩,
   C ⟨cTriVertex i j t 2, cTri_mem hi hj ht (by omega)⟩)

private theorem decode_countThreeColoring {φ : CNF ℕ}
    (C : (toCountThreeColoring φ).induced.Coloring (Fin 3)) :
    let cT := C ⟨cPalVertex 0, cPal_mem (by omega)⟩; let cF := C ⟨cPalVertex 1, cPal_mem (by omega)⟩
    let cB := C ⟨cPalVertex 2, cPal_mem (by omega)⟩; let σ := φ.extendAssignment (decTau C)
    (cT ≠ cF ∧ cF ≠ cB ∧ cB ≠ cT) ∧ φ.eval σ = true ∧
    (∀ k (hk : k < φ.distinctVars.length) b (hb : b < 2),
      C ⟨cLitIdxVertex k b, cLit_mem hk hb⟩ =
        if σ (φ.distinctVars.getD k 0) == decide (b = 1) then cT else cF) ∧
    (∀ (i : ℕ) (hi : i < φ.length) j (hj : j ≤ φ[i].length),
      C ⟨cOutVertex i j, cOut_mem hi hj⟩ = if (φ[i].take j).any (Literal.eval σ) then cT else cF) ∧
    (∀ (i : ℕ) (hi : i < φ.length) j (hj : j < φ[i].length), C ⟨cNotOutVertex i j, cNot_mem hi hj⟩ =
      if (φ[i].take (j + 1)).any (Literal.eval σ) then cF else cT) ∧
    (∀ (i : ℕ) (hi : i < φ.length) j (hj : j < φ[i].length),
      let xCol := if (φ[i].take j).any (Literal.eval σ) then cT else cF
      let yCol := if Literal.eval σ φ[i][j] then cT else cF
      let nzCol := if (φ[i].take (j + 1)).any (Literal.eval σ) then cF else cT
      naeChoice xCol yCol nzCol (naeBit xCol yCol nzCol (decTri C hi hj 0 (by omega))) =
        decTri C hi hj 0 (by omega) ∧
      naeChoice xCol nzCol cT (naeBit xCol nzCol cT (decTri C hi hj 1 (by omega))) =
        decTri C hi hj 1 (by omega) ∧
      naeChoice yCol nzCol cT (naeBit yCol nzCol cT (decTri C hi hj 2 (by omega))) =
        decTri C hi hj 2 (by omega)) := by
  have hedge_valid : ∀ {u v : ℕ}
      (hu : u ∈ (toCountThreeColoring φ).vertices) (hv : v ∈ (toCountThreeColoring φ).vertices),
      (u, v) ∈ countColoringEdges φ → C ⟨u, hu⟩ ≠ C ⟨v, hv⟩ := fun hu hv he =>
    C.valid (adj_of_mem_countColoringEdges he)
  dsimp only
  let cT := C ⟨cPalVertex 0, cPal_mem (by omega)⟩; let cF := C ⟨cPalVertex 1, cPal_mem (by omega)⟩
  let cB := C ⟨cPalVertex 2, cPal_mem (by omega)⟩
  have hTF : cT ≠ cF := hedge_valid _ _ (by simp [countColoringEdges])
  have hFB : cF ≠ cB := hedge_valid _ _ (by simp [countColoringEdges])
  have hBT : cB ≠ cT := hedge_valid _ _ (by simp [countColoringEdges])
  let τ := decTau C; let σ := φ.extendAssignment τ
  have hvar_sub : ∀ {k} (hk : k < φ.distinctVars.length),
      cVarEdges k ⊆ countColoringEdges φ := fun {k} hk _ he =>
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
      he⟩))
  have hcl_sub : ∀ {i} (hi : i < φ.length), cClauseEdges φ i φ[i] ⊆ countColoringEdges φ :=
    fun {i} hi _ he => List.mem_append_right _
      (List.mem_flatMap.mpr ⟨(φ[i], i), List.mem_zipIdx_iff_getElem?.mpr (by simp [hi]), he⟩)
  have hst_sub : ∀ {i j} (hi : i < φ.length) (hj : j < φ[i].length),
      cStageEdges φ i j φ[i][j] ⊆ countColoringEdges φ := fun {i j} hi hj _ he =>
    hcl_sub hi (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨(φ[i][j], j), List.mem_zipIdx_iff_getElem?.mpr (by simp [hj]), he⟩))
  have hlit_eq : ∀ k (hk : k < φ.distinctVars.length) b (hb : b < 2),
      C ⟨cLitIdxVertex k b, cLit_mem hk hb⟩ =
        if σ (φ.distinctVars.getD k 0) == decide (b = 1) then cT else cF := fun k hk b hb => by
    have hx_mem : φ.distinctVars[k] ∈ φ.vars := CNF.mem_distinctVars.mp (List.getElem_mem hk)
    have hσ : σ (φ.distinctVars.getD k 0) =
        decide (C ⟨cLitIdxVertex k 1, cLit_mem hk (by omega)⟩ = cT) := by
      dsimp only [σ]; rw [getD_eq_getElem _ _ hk, CNF.extendAssignment_of_mem τ hx_mem]
      simp only [τ, decTau, φ.nodup_distinctVars.idxOf_getElem k hk]; rfl
    rw [hσ, ← lit_forced cT cF cB (C ⟨cLitIdxVertex k 1, cLit_mem hk (by omega)⟩)
      (C ⟨cLitIdxVertex k 0, cLit_mem hk (by omega)⟩) (decide (b = 1)) hTF hFB hBT
      (hedge_valid _ _ (hvar_sub hk (by simp [cVarEdges])))
      (hedge_valid _ _ (hvar_sub hk (by simp [cVarEdges])))
      (hedge_valid _ _ (hvar_sub hk (by simp [cVarEdges])))]
    interval_cases b <;> rfl
  have hlit_ij {i j} (hi : i < φ.length) (hj : j < φ[i].length) :
      cLitVertex φ φ[i][j] ∈ (toCountThreeColoring φ).vertices :=
    cLit_mem (List.idxOf_lt_length_iff.mpr (CNF.mem_distinctVars.mpr
      (CNF.mem_vars.mpr ⟨φ[i], List.getElem_mem hi, φ[i][j].2, List.getElem_mem hj⟩)))
      (by cases φ[i][j].2 <;> decide)
  have hy_lit : ∀ {i j} (hi : i < φ.length) (hj : j < φ[i].length),
      C ⟨cLitVertex φ φ[i][j], hlit_ij hi hj⟩ =
        if Literal.eval σ φ[i][j] then cT else cF := fun {i j} hi hj => by
    have hlv : φ[i][j].1 ∈ φ.distinctVars := CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr
      ⟨φ[i], List.getElem_mem hi, φ[i][j].2, List.getElem_mem hj⟩)
    dsimp only [cLitVertex]
    rw [hlit_eq _ (List.idxOf_lt_length_iff.mpr hlv) _ (by cases φ[i][j].2 <;> decide),
      getD_idxOf hlv 0]; obtain ⟨x, b⟩ := φ[i][j]; rw [Literal.eval_mk]; cases b <;> rfl
  have hnae : ∀ {i j a₀ a₁ a₂ : ℕ} (hi : i < φ.length) (hj : j < φ[i].length) (t : ℕ) (ht : t < 3)
      (ha₀ : a₀ ∈ (toCountThreeColoring φ).vertices)
      (ha₁ : a₁ ∈ (toCountThreeColoring φ).vertices) (ha₂ : a₂ ∈ (toCountThreeColoring φ).vertices),
      cTriEdges i j t a₀ a₁ a₂ ⊆ countColoringEdges φ →
      ¬(C ⟨a₀, ha₀⟩ = C ⟨a₁, ha₁⟩ ∧ C ⟨a₁, ha₁⟩ = C ⟨a₂, ha₂⟩) ∧
        naeChoice (C ⟨a₀, ha₀⟩) (C ⟨a₁, ha₁⟩) (C ⟨a₂, ha₂⟩)
          (naeBit (C ⟨a₀, ha₀⟩) (C ⟨a₁, ha₁⟩) (C ⟨a₂, ha₂⟩) (decTri C hi hj t ht)) =
          decTri C hi hj t ht := fun hi hj t ht ha₀ ha₁ ha₂ hsub =>
    naeChoice_naeBit _ _ _ _ (decide_eq_true
      ⟨hedge_valid (cTri_mem hi hj ht (by omega)) _ (hsub (by simp [cTriEdges])),
       hedge_valid (cTri_mem hi hj ht (by omega)) _ (hsub (by simp [cTriEdges])),
       hedge_valid (cTri_mem hi hj ht (by omega)) _ (hsub (by simp [cTriEdges])),
       hedge_valid _ ha₀ (hsub (by simp [cTriEdges])),
       hedge_valid _ ha₁ (hsub (by simp [cTriEdges])),
       hedge_valid _ ha₂ (hsub (by simp [cTriEdges]))⟩)
  have hstages {i j} (hi : i < φ.length) (hj : j < φ[i].length) :=
    And.intro (hnae hi hj 0 (by omega) (cOut_mem hi hj.le) (hlit_ij hi hj) (cNot_mem hi hj)
      fun _ he => hst_sub hi hj
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ he))))
      (And.intro (hnae hi hj 1 (by omega) (cOut_mem hi hj.le) (cNot_mem hi hj)
        (cPal_mem (by omega)) fun _ he => hst_sub hi hj
          (List.mem_append_left _ (List.mem_append_right _ he)))
        (hnae hi hj 2 (by omega) (hlit_ij hi hj) (cNot_mem hi hj) (cPal_mem (by omega))
          fun _ he => hst_sub hi hj (List.mem_append_right _ he)))
  have hout_not : ∀ (i : ℕ) (hi : i < φ.length),
      (∀ j (hj : j ≤ φ[i].length), C ⟨cOutVertex i j, cOut_mem hi hj⟩ =
        if (φ[i].take j).any (Literal.eval σ) then cT else cF) ∧
      (∀ j (hj : j < φ[i].length), C ⟨cNotOutVertex i j, cNot_mem hi hj⟩ =
        if (φ[i].take (j + 1)).any (Literal.eval σ) then cF else cT) := fun i hi => by
    have hstep : ∀ j (hj : j ≤ φ[i].length), C ⟨cOutVertex i j, cOut_mem hi hj⟩ =
        if (φ[i].take j).any (Literal.eval σ) then cT else cF := by
      intro j; induction j with
      | zero =>
        intro _; simp only [List.take_zero, List.any_nil, Bool.false_eq_true, ↓reduceIte]
        exact fin3_eq_of_ne_two cT cF cB _ hTF hFB hBT
          (hedge_valid _ _ (hcl_sub hi (by simp [cClauseEdges])))
          (hedge_valid _ _ (hcl_sub hi (by simp [cClauseEdges])))
      | succ j ih =>
        intro hj; have hjlt : j < φ[i].length := hj
        obtain ⟨⟨ht0, -⟩, ⟨ht1, -⟩, ⟨ht2, -⟩⟩ := hstages hi hjlt
        rw [ih hjlt.le, hy_lit hi hjlt] at ht0
        rw [ih hjlt.le] at ht1; rw [hy_lit hi hjlt] at ht2
        rw [any_take_succ φ[i] (Literal.eval σ) hjlt]
        exact (stage_forced cT cF cB _ _ _ _ hTF hFB hBT
          (hedge_valid _ _ (hst_sub hi hjlt (by simp [cStageEdges])))
          (hedge_valid _ _ (hst_sub hi hjlt (by simp [cStageEdges])))
          (hedge_valid _ _ (hst_sub hi hjlt (by simp [cStageEdges]))) ht0 ht1 ht2).1
    refine ⟨hstep, fun j hj => ?_⟩
    obtain ⟨⟨ht0, -⟩, ⟨ht1, -⟩, ⟨ht2, -⟩⟩ := hstages hi hj
    rw [hstep j hj.le, hy_lit hi hj] at ht0; rw [hstep j hj.le] at ht1; rw [hy_lit hi hj] at ht2
    rw [any_take_succ φ[i] (Literal.eval σ) hj]
    exact (stage_forced cT cF cB _ _ _ _ hTF hFB hBT
      (hedge_valid (cOut_mem hi hj) _ (hst_sub hi hj (by simp [cStageEdges])))
      (hedge_valid (cOut_mem hi hj) _ (hst_sub hi hj (by simp [cStageEdges])))
      (hedge_valid _ _ (hst_sub hi hj (by simp [cStageEdges]))) ht0 ht1 ht2).2
  have hsat : φ.eval σ = true := by
    rw [CNF.eval_eq_true_iff]; intro cl hcl; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
    have hout_end := (hout_not i hi).1 φ[i].length le_rfl; rw [List.take_length] at hout_end
    have hendF := hedge_valid (cOut_mem hi le_rfl) (@cPal_mem φ 1 (by omega))
      (hcl_sub hi (by simp [cClauseEdges]))
    rw [hout_end] at hendF; cases h : φ[i].any (Literal.eval σ)
    exacts [absurd rfl (h ▸ hendF), by simpa [Clause.eval] using h]
  refine ⟨⟨hTF, hFB, hBT⟩, hsat, hlit_eq, fun i hi => (hout_not i hi).1,
    fun i hi => (hout_not i hi).2, fun i hi j hj => ?_⟩
  obtain ⟨⟨-, h0⟩, ⟨-, h1⟩, ⟨-, h2⟩⟩ := hstages hi hj
  simp only [(hout_not i hi).1 j hj.le, hy_lit hi hj, (hout_not i hi).2 j hj] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

private theorem nonempty_countThreeColoringEquiv (φ : CNF ℕ) :
    Nonempty ((PalPerm × SatAssign φ × (OccIdx φ → Bool × Bool × Bool)) ≃
      (toCountThreeColoring φ).induced.Coloring (Fin 3)) := by
  let mkCol (p : PalPerm) (τ : SatAssign φ) (bits : OccIdx φ → Bool × Bool × Bool) :
      (toCountThreeColoring φ).induced.Coloring (Fin 3) :=
    SimpleGraph.Coloring.mk (fun v => countGadgetColor φ p τ.1 bits v.1) fun {_ _} huv =>
      ((Graph.toSimpleGraph_adj.mp (Graph.induced_adj.mp huv)).2).elim
        (countGadgetColor_ne_of_edge p τ bits)
        fun h => (countGadgetColor_ne_of_edge p τ bits h).symm
  refine ⟨{ toFun := fun ⟨p, τ, bits⟩ => mkCol p τ bits
            invFun := fun C =>
              let hd := decode_countThreeColoring C; let σ := φ.extendAssignment (decTau C)
              let cT := C ⟨cPalVertex 0, cPal_mem (by omega)⟩
              let cF := C ⟨cPalVertex 1, cPal_mem (by omega)⟩
              (⟨(cT, cF, C ⟨cPalVertex 2, cPal_mem (by omega)⟩), hd.1⟩, ⟨decTau C, hd.2.1⟩,
                fun ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ =>
                  let xCol := if (φ[i].take j).any (Literal.eval σ) then cT else cF
                  let yCol := if Literal.eval σ φ[i][j] then cT else cF
                  let nzCol := if (φ[i].take (j + 1)).any (Literal.eval σ) then cF else cT
                  (naeBit xCol yCol nzCol (decTri C hi hj 0 (by omega)),
                   naeBit xCol nzCol cT (decTri C hi hj 1 (by omega)),
                   naeBit yCol nzCol cT (decTri C hi hj 2 (by omega))))
            left_inv := ?_, right_inv := ?_ }⟩
  · rintro ⟨p, τ, bits⟩; obtain ⟨hTF, hFB, hBT⟩ := p.2
    have hp0 : countGadgetColor φ p τ.1 bits (cPalVertex 0) = p.1.1 := by
      simp [countGadgetColor, cPalVertex]
    have hp1 : countGadgetColor φ p τ.1 bits (cPalVertex 1) = p.1.2.1 := by
      simp [countGadgetColor, cPalVertex]
    have hp2 : countGadgetColor φ p τ.1 bits (cPalVertex 2) = p.1.2.2 := by
      simp [countGadgetColor, cPalVertex]
    have hτ_eq : decTau (mkCol p τ bits) = τ.1 := by
      funext ⟨x, hx⟩; have hxv : x ∈ φ.vars := List.mem_toFinset.mp hx
      dsimp only [decTau, mkCol, SimpleGraph.Coloring.mk]; simp only [RelHom.coeFn_mk, hp0]
      simp only [countGadgetColor, cLitIdxVertex, Nat.unpair_pair,
        getD_idxOf (CNF.mem_distinctVars.mpr hxv) 0, CNF.extendAssignment_of_mem τ.1 hxv]
      cases τ.1 ⟨x, hx⟩ <;> [simp [hTF.symm]; simp]
    refine Prod.ext (Subtype.ext (Prod.ext hp0 (Prod.ext hp1 hp2)))
      (Prod.ext (Subtype.ext hτ_eq) ?_)
    funext ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; dsimp only; rw [hτ_eq]
    dsimp only [decTri, mkCol, SimpleGraph.Coloring.mk]
    have hget_cl : φ.getD i [] = φ[i] := getD_eq_getElem φ [] hi
    have hget_l : φ[i].getD j (0, false) = φ[i][j] := getD_eq_getElem φ[i] (0, false) hj
    have htake_succ := any_take_succ φ[i] (Literal.eval (φ.extendAssignment τ.1)) hj
    let bx := (φ[i].take j).any (Literal.eval (φ.extendAssignment τ.1))
    let by_ := Literal.eval (φ.extendAssignment τ.1) φ[i][j]
    let b3 := bits ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; have hnm := orGate_not_mono p.1.1 p.1.2.1 hTF bx by_
    let xCol := if bx then p.1.1 else p.1.2.1; let yCol := if by_ then p.1.1 else p.1.2.1
    let nzCol := if (bx || by_) then p.1.2.1 else p.1.1
    have htri : ∀ t, (countGadgetColor φ p τ.1 bits (cTriVertex i j t 0),
        countGadgetColor φ p τ.1 bits (cTriVertex i j t 1),
        countGadgetColor φ p τ.1 bits (cTriVertex i j t 2)) =
          match t with
          | 0 => naeChoice xCol yCol nzCol b3.1 | 1 => naeChoice xCol nzCol p.1.1 b3.2.1
          | _ => naeChoice yCol nzCol p.1.1 b3.2.2 := fun t => by
      rcases t with _ | _ | _ <;> refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
        { simp only [countGadgetColor, cTriVertex, Nat.unpair_pair, hget_cl, hget_l,
            htake_succ, getOccBits_of_lt hi hj]; rfl }
    simp only [RelHom.coeFn_mk, hp0, hp1, htake_succ, htri 0, htri 1, htri 2]
    exact Prod.ext (naeBit_naeChoice xCol yCol nzCol b3.1 hnm.1)
      (Prod.ext (naeBit_naeChoice xCol nzCol p.1.1 b3.2.1 hnm.2.1)
        (naeBit_naeChoice yCol nzCol p.1.1 b3.2.2 hnm.2.2))
  · intro C; obtain ⟨hpal, hsat, hlit_eq, hout_eq, hnot_eq, htri_eq⟩ := decode_countThreeColoring C
    apply DFunLike.ext; rintro ⟨v, hv⟩; dsimp only [mkCol, SimpleGraph.Coloring.mk, RelHom.coeFn_mk]
    rcases mem_countColoringVertices_iff.mp hv with
      ⟨c, hc, rfl⟩ | ⟨k, hk, b, hb, rfl⟩ | ⟨i, hi, j, hj, rfl⟩ |
      ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, t, ht, r, hr, rfl⟩
    · interval_cases c <;> simp only [countGadgetColor, cPalVertex, Nat.unpair_pair]
    · simp only [countGadgetColor, cLitIdxVertex, Nat.unpair_pair]; exact (hlit_eq k hk b hb).symm
    · simp only [countGadgetColor, cOutVertex, Nat.unpair_pair, getD_eq_getElem φ [] hi,
        (hout_eq i hi j hj).symm]
    · simp only [countGadgetColor, cNotOutVertex, Nat.unpair_pair, getD_eq_getElem φ [] hi,
        (hnot_eq i hi j hj).symm]
    · obtain ⟨h0, h1, h2⟩ := htri_eq i hi j hj
      simp only [countGadgetColor, cTriVertex, Nat.unpair_pair, getD_eq_getElem φ [] hi,
        getD_eq_getElem φ[i] (0, false) hj, getOccBits_of_lt hi hj]
      interval_cases t <;> interval_cases r
      exacts [congrArg Prod.fst h0, congrArg (Prod.fst ∘ Prod.snd) h0,
        congrArg (Prod.snd ∘ Prod.snd) h0, congrArg Prod.fst h1,
        congrArg (Prod.fst ∘ Prod.snd) h1, congrArg (Prod.snd ∘ Prod.snd) h1,
        congrArg Prod.fst h2, congrArg (Prod.fst ∘ Prod.snd) h2,
        congrArg (Prod.snd ∘ Prod.snd) h2]

/-- **Exact `#3-Coloring` count of `SAT.toCountThreeColoring`**. -/
theorem sharpThreeColoring_toCountThreeColoring (φ : CNF ℕ) :
    SharpThreeColoring (toCountThreeColoring φ) = 6 * 8 ^ φ.vars.length * SharpSAT φ := by
  obtain ⟨e⟩ := nonempty_countThreeColoringEquiv φ
  have hpal : Fintype.card PalPerm = 6 := by decide
  have hsat : Fintype.card (SatAssign φ) = SharpSAT φ := by
    rw [SharpSAT, CNF.modelCount, Fintype.card_subtype]
  rw [SharpThreeColoring, sharpKColoring_eq_fintype_card e, Fintype.card_prod, Fintype.card_prod,
    hpal, hsat, Fintype.card_fun, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_bool, card_occIdx]; ring

theorem toCountThreeColoring_mem_iff (φ : CNF ℕ) :
    toCountThreeColoring φ ∈ ThreeColoring ↔ φ ∈ SAT := by
  rw [ThreeColoring, mem_KColoring_iff_pos_SharpKColoring, SharpSAT.mem_SAT_iff]
  change 0 < SharpThreeColoring (toCountThreeColoring φ) ↔ 0 < SharpSAT φ
  rw [sharpThreeColoring_toCountThreeColoring]
  exact ⟨Nat.pos_of_mul_pos_left, Nat.mul_pos (by positivity)⟩

private theorem computableInPolyTime_cLitIdxVertex {γ : Type} {enc : γ ↪ List Bool} {k b : γ → ℕ}
    (hk : ComputableInPolyTime k enc encUnary) (hb : ComputableInPolyTime b enc encUnary) :
    ComputableInPolyTime (fun x => cLitIdxVertex (k x) (b x)) enc encNat :=
  computableInPolyTime_tagPair 1 hk hb
private theorem computableInPolyTime_cOutVertex {γ : Type} {enc : γ ↪ List Bool} {i j : γ → ℕ}
    (hi : ComputableInPolyTime i enc encUnary) (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun x => cOutVertex (i x) (j x)) enc encNat :=
  computableInPolyTime_tagPair 2 hi hj
private theorem computableInPolyTime_cNotOutVertex {γ : Type} {enc : γ ↪ List Bool} {i j : γ → ℕ}
    (hi : ComputableInPolyTime i enc encUnary) (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun x => cNotOutVertex (i x) (j x)) enc encNat :=
  computableInPolyTime_tagPair 3 hi hj
private theorem computableInPolyTime_cLitVertex {γ : Type} {enc : γ ↪ List Bool}
    {φ : γ → CNF ℕ} {l : γ → Literal ℕ} (hφ : ComputableInPolyTime φ enc encCNF)
    (hl : ComputableInPolyTime l enc (encPair encNat encBool)) :
    ComputableInPolyTime (fun x => cLitVertex (φ x) (l x)) enc encNat := by
  have hdvars : ComputableInPolyTime (CNF.distinctVars (V := ℕ)) encCNF (encList encNat) := by
    fun_prop
  exact computableInPolyTime_cLitIdxVertex (idxOfWithInput (hdvars.comp hφ) hl.fst')
    ((of_finite Bool.toNat).comp hl.snd')
private theorem computableInPolyTime_cTriVertex {γ : Type} {enc : γ ↪ List Bool}
    {i j t r : γ → ℕ} (hi : ComputableInPolyTime i enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) (ht : ComputableInPolyTime t enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary) :
    ComputableInPolyTime (fun x => cTriVertex (i x) (j x) (t x) (r x)) enc encNat :=
  unary_to_binary.comp (unary_pair.comp ((const 4).prod (unary_pair.comp (hi.prod
    (unary_pair.comp (hj.prod (unary_pair.comp (ht.prod hr))))))))
attribute [local fun_prop] computableInPolyTime_cLitIdxVertex computableInPolyTime_cLitVertex
  computableInPolyTime_cOutVertex computableInPolyTime_cNotOutVertex
  computableInPolyTime_cTriVertex

private theorem computableInPolyTime_zipClauses :
    ComputableInPolyTime (List.zipIdx (α := Clause ℕ)) encCNF
      (encList (encPair (encList (encPair encNat encBool)) encUnary)) := by unfold encCNF; fun_prop
private theorem computableInPolyTime_countColoringEdges :
    ComputableInPolyTime countColoringEdges encCNF (encList (encPair encNat encNat)) := by
  have hd : ComputableInPolyTime (fun φ : CNF ℕ => List.range φ.distinctVars.length)
      encCNF (encList encUnary) := by fun_prop
  unfold countColoringEdges
  exact listAppend' (listAppend' (const _) (flatMapWithInput hd (by unfold cVarEdges; fun_prop)))
    (flatMapWithInput computableInPolyTime_zipClauses (by
      unfold cClauseEdges; exact listAppend' (by fun_prop)
        (flatMapWithInput (by fun_prop) (by unfold cStageEdges cTriEdges; fun_prop))))
private theorem computableInPolyTime_countColoringVertices :
    ComputableInPolyTime countColoringVertices encCNF (encList encNat) := by
  have hd : ComputableInPolyTime (fun φ : CNF ℕ => List.range φ.distinctVars.length)
      encCNF (encList encUnary) := by fun_prop
  unfold countColoringVertices
  exact listAppend' (listAppend' (const _) (flatMapWithInput hd (by fun_prop)))
    (flatMapWithInput computableInPolyTime_zipClauses (listAppend' (by fun_prop)
      (flatMapWithInput (by fun_prop) (by unfold stageVertices; fun_prop))))
attribute [local fun_prop] computableInPolyTime_countColoringEdges
  computableInPolyTime_countColoringVertices
/-- `SAT.toCountThreeColoring` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toCountThreeColoring :
    ComputableInPolyTime toCountThreeColoring encCNF encGraph := by
  unfold toCountThreeColoring; fun_prop

theorem length_toCountThreeColoring_le {k : ℕ} {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    (toCountThreeColoring φ).vertices.length ≤ (13 * k + 1) * φ.length + 3 ∧
      (toCountThreeColoring φ).edges.length ≤ (24 * k + 4) * φ.length + 3 := by
  have hzip : ∀ c ∈ φ.zipIdx, c.1.length ≤ k := fun c hc =>
    let ⟨hi, hcl⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hc)
    hcl ▸ hφ _ (List.getElem_mem hi)
  have hnvars := CNF.length_distinctVars φ ▸ CNF.numVars_le_mul_length hφ
  have hV₁ := (List.length_range (n := φ.distinctVars.length)) ▸ length_flatMap_le
    (List.range φ.distinctVars.length) (fun i => [cLitIdxVertex i 1, cLitIdxVertex i 0]) 2
    fun _ _ => by simp
  have hV₂ := (List.length_zipIdx (l := φ)) ▸ length_flatMap_le φ.zipIdx
    (fun c => [cOutVertex c.2 0] ++ c.1.zipIdx.flatMap (stageVertices c.2)) (11 * k + 1)
    fun c hc => by
      have := (List.length_zipIdx (l := c.1)) ▸ length_flatMap_le c.1.zipIdx (stageVertices c.2) 11
        fun _ _ => by simp [stageVertices]
      have := hzip c hc
      simp only [List.length_append, List.length_cons, List.length_nil]; nlinarith
  have hE₁ := (List.length_range (n := φ.distinctVars.length)) ▸
    length_flatMap_le (List.range φ.distinctVars.length) cVarEdges 3 fun _ _ => by simp [cVarEdges]
  have hE₂ := (List.length_zipIdx (l := φ)) ▸ length_flatMap_le φ.zipIdx
    (fun c => cClauseEdges φ c.2 c.1) (21 * k + 4) fun c hc => by
      have := (List.length_zipIdx (l := c.1)) ▸ length_flatMap_le c.1.zipIdx
        (fun l => cStageEdges φ c.2 l.2 l.1) 21 fun _ _ => by simp [cStageEdges, cTriEdges]
      have := hzip c hc; simp only [cClauseEdges, List.length_append, List.length_cons,
        List.length_nil]; nlinarith
  refine ⟨?_, ?_⟩ <;> { simp only [toCountThreeColoring, countColoringVertices, countColoringEdges,
    List.length_append, List.length_cons, List.length_nil]; nlinarith }

end SAT

/-! ### Degree-`≤ 4` vertex-splitting reduction (`ThreeColoring.toDegreeFour`) -/

namespace ThreeColoring

def allIndexPairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range n).map fun j => (i, j)
def canonicalEdges (G : Graph) : List (ℕ × ℕ) :=
  (allIndexPairs G.distinctVertices.length).filter fun p =>
    decide (p.1 < p.2) && G.adjBool (G.distinctVertices.getD p.1 0) (G.distinctVertices.getD p.2 0)
def incEdges (E : List (ℕ × ℕ)) (i : ℕ) : List ℕ :=
  (List.range E.length).filter fun k => ((E.getD k (0, 0)).1 == i) || ((E.getD k (0, 0)).2 == i)
def chainVertex (i t : ℕ) : ℕ := Nat.pair 0 (Nat.pair i t)
def auxAVertex (i t : ℕ) : ℕ := Nat.pair 1 (Nat.pair i t)
def auxBVertex (i t : ℕ) : ℕ := Nat.pair 2 (Nat.pair i t)
def portVertex (i t : ℕ) : ℕ := Nat.pair 3 (Nat.pair i t)
def diamondEdges (i t : ℕ) : List (ℕ × ℕ) :=
  [(auxAVertex i t, auxBVertex i t), (chainVertex i t, auxAVertex i t),
    (chainVertex i t, auxBVertex i t), (chainVertex i (t + 1), auxAVertex i t),
    (chainVertex i (t + 1), auxBVertex i t), (portVertex i t, auxAVertex i t),
    (portVertex i t, auxBVertex i t)]
def degreeFourVertices (G : Graph) : List ℕ :=
  let E := canonicalEdges G
  (List.range G.distinctVertices.length).flatMap fun i =>
    [chainVertex i 0] ++ (List.range (incEdges E i).length).flatMap fun t =>
      [chainVertex i (t + 1), auxAVertex i t, auxBVertex i t, portVertex i t]
def degreeFourEdges (G : Graph) : List (ℕ × ℕ) :=
  let E := canonicalEdges G
  ((List.range G.distinctVertices.length).flatMap fun i =>
      (List.range (incEdges E i).length).flatMap fun t => diamondEdges i t) ++
    (List.range E.length).map fun k =>
      let e := E.getD k (0, 0)
      (portVertex e.1 ((incEdges E e.1).idxOf k), portVertex e.2 ((incEdges E e.2).idxOf k))

/-- **Degree-`≤ 4` vertex-splitting reduction** for `3-Coloring` and `#3-Coloring`. -/
def toDegreeFour (G : Graph) : Graph := ⟨degreeFourVertices G, degreeFourEdges G⟩

private theorem nodup_canonicalEdges (G : Graph) : (canonicalEdges G).Nodup :=
  List.Nodup.filter _ (List.nodup_flatMap.mpr
    ⟨fun i _ => List.nodup_range.map (Prod.mk_right_injective i),
     List.nodup_range.pairwise_of_forall_ne fun _ _ _ _ hij => by
       dsimp only [Function.onFun]; refine List.disjoint_left.mpr fun _ h1 h2 => ?_
       obtain ⟨_, -, rfl⟩ := List.mem_map.mp h1; obtain ⟨_, -, heq⟩ := List.mem_map.mp h2
       exact hij (congrArg Prod.fst heq).symm⟩)

private theorem mem_canonicalEdges_iff {G : Graph} {p : ℕ × ℕ} :
    p ∈ canonicalEdges G ↔ p.1 < p.2 ∧ p.2 < G.distinctVertices.length ∧
      G.toSimpleGraph.Adj (G.distinctVertices.getD p.1 0) (G.distinctVertices.getD p.2 0) := by
  obtain ⟨i, j⟩ := p
  simp only [canonicalEdges, allIndexPairs, List.mem_filter, List.mem_flatMap, List.mem_range,
    List.mem_map, Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff]
  exact ⟨fun ⟨⟨_, _, _, hb, rfl, rfl⟩, hlt, hadj⟩ => ⟨hlt, hb, hadj⟩,
    fun ⟨hlt, hj, hadj⟩ => ⟨⟨i, by omega, j, hj, rfl, rfl⟩, hlt, hadj⟩⟩

theorem length_canonicalEdges_le (G : Graph) : (canonicalEdges G).length ≤ G.edges.length := by
  have hex : ∀ p : {p // p ∈ canonicalEdges G}, ∃ idx : Fin G.edges.length,
      G.edges[idx.val] = (G.distinctVertices.getD p.1.1 0, G.distinctVertices.getD p.1.2 0) ∨
        G.edges[idx.val] = (G.distinctVertices.getD p.1.2 0, G.distinctVertices.getD p.1.1 0) := by
    rintro ⟨⟨i, j⟩, hp⟩
    rcases (Graph.toSimpleGraph_adj.mp (mem_canonicalEdges_iff.mp hp).2.2).2 with h | h <;>
      obtain ⟨k, hk, heq⟩ := List.getElem_of_mem h
    exacts [⟨⟨k, hk⟩, Or.inl heq⟩, ⟨⟨k, hk⟩, Or.inr heq⟩]
  choose f hf using hex
  have hinj : Function.Injective f := by
    rintro ⟨⟨i₁, j₁⟩, hp₁⟩ ⟨⟨i₂, j₂⟩, hp₂⟩ hfeq
    obtain ⟨hlt₁, hj₁, -⟩ := mem_canonicalEdges_iff.mp hp₁
    obtain ⟨hlt₂, hj₂, -⟩ := mem_canonicalEdges_iff.mp hp₂
    have hi₁ := hlt₁.trans hj₁; have hi₂ := hlt₂.trans hj₂
    have h₁ := hfeq ▸ hf ⟨(i₁, j₁), hp₁⟩; have h₂ := hf ⟨(i₂, j₂), hp₂⟩
    simp only [getD_eq_getElem _ _ hi₁, getD_eq_getElem _ _ hj₁] at h₁
    simp only [getD_eq_getElem _ _ hi₂, getD_eq_getElem _ _ hj₂] at h₂
    have hinjV {a b} (ha : a < G.distinctVertices.length) (hb : b < G.distinctVertices.length)
        (h : G.distinctVertices[a] = G.distinctVertices[b]) : a = b :=
      Fin.mk.inj ((List.nodup_iff_injective_get.mp G.nodup_distinctVertices)
        (a₁ := ⟨_, ha⟩) (a₂ := ⟨_, hb⟩) h)
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
      obtain ⟨hA, hB⟩ := Prod.mk.inj (h₁.symm.trans h₂)
    exacts [Subtype.ext (Prod.ext (hinjV hi₁ hi₂ hA) (hinjV hj₁ hj₂ hB)),
      by have := hinjV hi₁ hj₂ hA; have := hinjV hj₁ hi₂ hB; omega,
      by have := hinjV hj₁ hi₂ hA; have := hinjV hi₁ hj₂ hB; omega,
      Subtype.ext (Prod.ext (hinjV hi₁ hi₂ hB) (hinjV hj₁ hj₂ hA))]
  have hcard := Fintype.card_le_of_injective f hinj
  rwa [Fintype.card_fin, Fintype.card_congr (Equiv.subtypeEquivRight fun _ =>
    List.mem_toFinset.symm), Fintype.card_coe,
    List.toFinset_card_of_nodup (nodup_canonicalEdges G)] at hcard

private theorem mem_incEdges_iff {E : List (ℕ × ℕ)} {i k : ℕ} :
    k ∈ incEdges E i ↔ k < E.length ∧ ((E.getD k (0, 0)).1 = i ∨ (E.getD k (0, 0)).2 = i) := by
  simp only [incEdges, List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq]
private theorem sum_length_incEdges_canonicalEdges (G : Graph) :
    (∑ i : Fin G.distinctVertices.length, (incEdges (canonicalEdges G) i.val).length) =
      2 * (canonicalEdges G).length := by
  set E := canonicalEdges G; set n := G.distinctVertices.length
  have hlen (i : Fin n) : (incEdges E i.val).length =
      ((Finset.univ : Finset (Fin E.length)).filter fun k =>
        E[k.val].1 = i.val ∨ E[k.val].2 = i.val).card := by
    have hnd : (incEdges E i.val).Nodup := List.nodup_range.filter _
    rw [← List.toFinset_card_of_nodup hnd]
    refine Finset.card_bij (fun k hk =>
        ⟨k, List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hk)).1⟩)
      (fun k hk => ?_) (fun _ _ _ _ h => Fin.mk.inj h) fun k hk =>
      ⟨k.val, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr k.isLt, by
        rw [getD_eq_getElem _ _ k.isLt]
        simpa only [Bool.or_eq_true, beq_iff_eq] using (Finset.mem_filter.mp hk).2⟩), rfl⟩
    obtain ⟨h1, h2⟩ := List.mem_filter.mp (List.mem_toFinset.mp hk)
    rw [getD_eq_getElem _ _ (List.mem_range.mp h1)] at h2
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.or_eq_true, beq_iff_eq] using h2
  simp_rw [hlen, Finset.card_filter]; rw [Finset.sum_comm]
  have htwo (k : Fin E.length) :
      (∑ i : Fin n, if E[k.val].1 = i.val ∨ E[k.val].2 = i.val then 1 else 0) = 2 := by
    obtain ⟨hlt, hj⟩ := mem_canonicalEdges_iff.mp (List.getElem_mem k.isLt)
    have hpair : (Finset.univ.filter fun i : Fin n => E[k.val].1 = i.val ∨ E[k.val].2 = i.val) =
        {⟨E[k.val].1, hlt.trans hj.1⟩, ⟨E[k.val].2, hj.1⟩} := by
      ext i; simp [Fin.ext_iff, eq_comm]
    rw [← Finset.card_filter, hpair, Finset.card_pair fun h => by have := Fin.mk.inj h; omega]
  simp only [htwo, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

private theorem mem_degreeFourVertices_iff {G : Graph} {v : ℕ} :
    v ∈ degreeFourVertices G ↔
      let E := canonicalEdges G
      (∃ i < G.distinctVertices.length, ∃ t ≤ (incEdges E i).length, v = chainVertex i t) ∨
      (∃ i < G.distinctVertices.length, ∃ t < (incEdges E i).length, v = auxAVertex i t) ∨
      (∃ i < G.distinctVertices.length, ∃ t < (incEdges E i).length, v = auxBVertex i t) ∨
      (∃ i < G.distinctVertices.length, ∃ t < (incEdges E i).length, v = portVertex i t) := by
  dsimp only [degreeFourVertices]; set E := canonicalEdges G
  simp only [List.mem_flatMap, List.mem_range, List.mem_append, List.mem_cons, List.mem_nil_iff,
    or_false]
  refine ⟨fun ⟨i, hi, h⟩ => ?_, fun h => ?_⟩
  · rcases h with rfl | ⟨t, ht, rfl | rfl | rfl | rfl⟩
    exacts [Or.inl ⟨i, hi, 0, Nat.zero_le _, rfl⟩, Or.inl ⟨i, hi, t + 1, ht, rfl⟩,
      Or.inr (Or.inl ⟨i, hi, t, ht, rfl⟩), Or.inr (Or.inr (Or.inl ⟨i, hi, t, ht, rfl⟩)),
      Or.inr (Or.inr (Or.inr ⟨i, hi, t, ht, rfl⟩))]
  · rcases h with ⟨i, hi, t, ht, rfl⟩ | ⟨i, hi, t, ht, rfl⟩ | ⟨i, hi, t, ht, rfl⟩ |
      ⟨i, hi, t, ht, rfl⟩
    · rcases Nat.eq_zero_or_pos t with rfl | htpos
      exacts [⟨i, hi, Or.inl rfl⟩,
        ⟨i, hi, Or.inr ⟨t - 1, by omega, Or.inl (by rw [Nat.sub_add_cancel htpos])⟩⟩]
    exacts [⟨i, hi, Or.inr ⟨t, ht, Or.inr (Or.inl rfl)⟩⟩,
      ⟨i, hi, Or.inr ⟨t, ht, Or.inr (Or.inr (Or.inl rfl))⟩⟩,
      ⟨i, hi, Or.inr ⟨t, ht, Or.inr (Or.inr (Or.inr rfl))⟩⟩]

theorem length_degreeFourVertices (G : Graph) :
    (toDegreeFour G).vertices.length =
      G.distinctVertices.length + 8 * (canonicalEdges G).length := by
  dsimp only [toDegreeFour, degreeFourVertices]; set E := canonicalEdges G
  have hinner (i : ℕ) : ([chainVertex i 0] ++ (List.range (incEdges E i).length).flatMap fun t =>
      [chainVertex i (t + 1), auxAVertex i t, auxBVertex i t, portVertex i t]).length =
      1 + 4 * (incEdges E i).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_flatMap,
      List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]; ring
  rw [List.length_flatMap, ← List.map_coe_finRange_eq_range, List.map_map,
    List.map_congr_left fun i _ => hinner i.val, ← Fin.sum_univ_def, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, ← Finset.mul_sum,
    sum_length_incEdges_canonicalEdges]; ring

theorem numVertices_toDegreeFour_le (G : Graph) :
    (toDegreeFour G).numVertices ≤ G.numVertices + 8 * G.edges.length :=
  ((toDegreeFour G).numVertices_le_length_vertices.trans_eq (length_degreeFourVertices G)).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 8 (length_canonicalEdges_le G)) _)

private def candidateNeighbors (G : Graph) (u : ℕ) : List ℕ :=
  let E := canonicalEdges G; let i := u.unpair.2.unpair.1; let t := u.unpair.2.unpair.2
  match u.unpair.1 with
  | 0 => [auxAVertex i t, auxBVertex i t] ++
         if t = 0 then [] else [auxAVertex i (t - 1), auxBVertex i (t - 1)]
  | 1 => [auxBVertex i t, chainVertex i t, chainVertex i (t + 1), portVertex i t]
  | 2 => [auxAVertex i t, chainVertex i t, chainVertex i (t + 1), portVertex i t]
  | 3 =>
    let k := (incEdges E i).getD t 0; let e := E.getD k (0, 0)
    [auxAVertex i t, auxBVertex i t,
      if i = e.1 then portVertex e.2 ((incEdges E e.2).idxOf k)
      else portVertex e.1 ((incEdges E e.1).idxOf k)]
  | _ => []

private theorem length_candidateNeighbors_le (G : Graph) (u : ℕ) :
    (candidateNeighbors G u).length ≤ 4 := by
  dsimp only [candidateNeighbors]
  rcases u.unpair.1 with _ | _ | _ | _ | _ <;> [(split_ifs <;> simp); simp; simp; simp; simp]

private theorem mem_candidateNeighbors_of_edge {G : Graph} {u w : ℕ}
    (h : (u, w) ∈ degreeFourEdges G ∨ (w, u) ∈ degreeFourEdges G) :
    w ∈ candidateNeighbors G u := by
  have hboth : ∀ {a b}, (a, b) ∈ degreeFourEdges G →
      b ∈ candidateNeighbors G a ∧ a ∈ candidateNeighbors G b := fun {a b} hab => by
    dsimp only [degreeFourEdges] at hab; set E := canonicalEdges G
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map] at hab
    rcases hab with ⟨i, -, t, -, hd⟩ | ⟨k, hk, heq⟩
    · simp only [diamondEdges, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hd
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [candidateNeighbors, chainVertex, auxAVertex, auxBVertex, portVertex]
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq.symm
      have hget : E.getD k (0, 0) = E[k] := getD_eq_getElem _ _ hk
      obtain ⟨hlt, -⟩ := mem_canonicalEdges_iff.mp (List.getElem_mem hk)
      have hne12 : (E.getD k (0, 0)).1 ≠ (E.getD k (0, 0)).2 := by rw [hget]; omega
      have hidx1 := getD_idxOf ((mem_incEdges_iff (E := E)).mpr ⟨hk, Or.inl rfl⟩) 0
      have hidx2 := getD_idxOf ((mem_incEdges_iff (E := E)).mpr ⟨hk, Or.inr rfl⟩) 0
      dsimp only [E] at hidx1 hidx2 hne12 ⊢
      exact ⟨by simp only [candidateNeighbors, portVertex, Nat.unpair_pair, hidx1, ↓reduceIte,
        List.mem_cons, true_or, or_true],
        by simp only [candidateNeighbors, portVertex, Nat.unpair_pair, hidx2, hne12.symm,
          ↓reduceIte, List.mem_cons, true_or, or_true]⟩
  exact h.elim (fun h1 => (hboth h1).1) (fun h2 => (hboth h2).2)

/-- **Every vertex of `toDegreeFour G` has degree at most `4`**. -/
theorem maxDegree_toDegreeFour_le (G : Graph) : (toDegreeFour G).induced.maxDegree ≤ 4 := by
  refine (toDegreeFour G).induced.maxDegree_le_of_forall_degree_le 4 fun u => ?_
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : ((toDegreeFour G).induced.neighborFinset u).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
      (candidateNeighbors G u.1).toFinset := fun w hw => by
    obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
    rw [SimpleGraph.mem_neighborFinset, Graph.induced_adj, Graph.toSimpleGraph_adj] at hw'
    exact List.mem_toFinset.mpr (mem_candidateNeighbors_of_edge hw'.2)
  exact ((Finset.card_map _).symm.trans_le (Finset.card_le_card hsub)).trans
    ((List.toFinset_card_le _).trans (length_candidateNeighbors_le G u.1))

private abbrev DiamondIdx (G : Graph) :=
  Σ i : Fin G.distinctVertices.length, Fin (incEdges (canonicalEdges G) i.val).length
private def getBaseColor (G : Graph) (C₀ : G.induced.Coloring (Fin 3)) (i : ℕ) : Fin 3 :=
  if hi : i < G.distinctVertices.length then C₀ (G.vertexEquiv ⟨i, hi⟩) else 0
private theorem getBaseColor_of_lt {G : Graph} {C₀ : G.induced.Coloring (Fin 3)}
    {i : ℕ} (hi : i < G.distinctVertices.length) :
    getBaseColor G C₀ i = C₀ (G.vertexEquiv ⟨i, hi⟩) := by simp [getBaseColor, hi]
private def getDiamondBit (G : Graph) (bits : DiamondIdx G → Bool) (i t : ℕ) : Bool :=
  if hi : i < G.distinctVertices.length then
    if ht : t < (incEdges (canonicalEdges G) i).length then bits ⟨⟨i, hi⟩, ⟨t, ht⟩⟩ else false
  else false
private theorem getDiamondBit_of_lt {G : Graph} {bits : DiamondIdx G → Bool}
    {i t : ℕ} (hi : i < G.distinctVertices.length)
    (ht : t < (incEdges (canonicalEdges G) i).length) :
    getDiamondBit G bits i t = bits ⟨⟨i, hi⟩, ⟨t, ht⟩⟩ := by simp [getDiamondBit, hi, ht]
private def degreeFourColorFn (G : Graph) (C₀ : G.induced.Coloring (Fin 3))
    (bits : DiamondIdx G → Bool) (u : ℕ) : Fin 3 :=
  let base := getBaseColor G C₀ u.unpair.2.unpair.1
  let bit := getDiamondBit G bits u.unpair.2.unpair.1 u.unpair.2.unpair.2
  match u.unpair.1 with
  | 0 => base | 1 => (otherPair base bit).1 | 2 => (otherPair base bit).2 | _ => base

private theorem degreeFourColorFn_ne_of_edge {G : Graph} (C₀ : G.induced.Coloring (Fin 3))
    (bits : DiamondIdx G → Bool) {e : ℕ × ℕ} (he : e ∈ degreeFourEdges G) :
    degreeFourColorFn G C₀ bits e.1 ≠ degreeFourColorFn G C₀ bits e.2 := by
  dsimp only [degreeFourEdges] at he; set E := canonicalEdges G
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map] at he
  rcases he with ⟨i, hi, t, ht, hd⟩ | ⟨k, hk, heq⟩
  · have hv := otherPair_valid (C₀ (G.vertexEquiv ⟨i, hi⟩)) (bits ⟨⟨i, hi⟩, ⟨t, ht⟩⟩)
    simp only [diamondEdges, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [degreeFourColorFn, chainVertex, auxAVertex, auxBVertex, portVertex,
        Nat.unpair_pair, getBaseColor_of_lt hi, getDiamondBit_of_lt hi ht]
    · exact hv.1
    all_goals first | exact hv.2.1.symm | exact hv.2.2.1.symm
  · obtain ⟨rfl⟩ := heq.symm; obtain ⟨hlt, hj, hadj⟩ :=
    mem_canonicalEdges_iff.mp (List.getElem_mem hk)
    have hi1 : E[k].1 < G.distinctVertices.length := hlt.trans hj
    have hadj_ind : G.induced.Adj (G.vertexEquiv ⟨E[k].1, hi1⟩) (G.vertexEquiv ⟨E[k].2, hj⟩) := by
      rw [Graph.induced_adj, Graph.vertexEquiv_apply, Graph.vertexEquiv_apply]; exact hadj
    simp only [degreeFourColorFn, portVertex, Nat.unpair_pair, getD_eq_getElem _ _ hk,
      getBaseColor_of_lt hi1, getBaseColor_of_lt hj]; exact C₀.valid hadj_ind

private theorem chain_mem {G : Graph} {i t : ℕ} (hi : i < G.distinctVertices.length)
    (ht : t ≤ (incEdges (canonicalEdges G) i).length) :
    chainVertex i t ∈ (toDegreeFour G).vertices :=
  mem_degreeFourVertices_iff.mpr (Or.inl ⟨i, hi, t, ht, rfl⟩)
private theorem auxA_mem {G : Graph} {i t : ℕ} (hi : i < G.distinctVertices.length)
    (ht : t < (incEdges (canonicalEdges G) i).length) :
    auxAVertex i t ∈ (toDegreeFour G).vertices :=
  mem_degreeFourVertices_iff.mpr (Or.inr (Or.inl ⟨i, hi, t, ht, rfl⟩))
private theorem auxB_mem {G : Graph} {i t : ℕ} (hi : i < G.distinctVertices.length)
    (ht : t < (incEdges (canonicalEdges G) i).length) :
    auxBVertex i t ∈ (toDegreeFour G).vertices :=
  mem_degreeFourVertices_iff.mpr (Or.inr (Or.inr (Or.inl ⟨i, hi, t, ht, rfl⟩)))
private theorem port_mem {G : Graph} {i t : ℕ} (hi : i < G.distinctVertices.length)
    (ht : t < (incEdges (canonicalEdges G) i).length) :
    portVertex i t ∈ (toDegreeFour G).vertices :=
  mem_degreeFourVertices_iff.mpr (Or.inr (Or.inr (Or.inr ⟨i, hi, t, ht, rfl⟩)))

private theorem toDegreeFourColoringEquiv_aux {G : Graph}
    (C : (toDegreeFour G).induced.Coloring (Fin 3)) :
    (∀ i (hi : i < G.distinctVertices.length) t (ht : t ≤ (incEdges (canonicalEdges G) i).length),
      C ⟨chainVertex i t, chain_mem hi ht⟩ = C ⟨chainVertex i 0, chain_mem hi (Nat.zero_le _)⟩) ∧
    (∀ i (hi : i < G.distinctVertices.length) t (ht : t < (incEdges (canonicalEdges G) i).length),
      C ⟨portVertex i t, port_mem hi ht⟩ = C ⟨chainVertex i 0, chain_mem hi (Nat.zero_le _)⟩ ∧
      otherPair (C ⟨chainVertex i 0, chain_mem hi (Nat.zero_le _)⟩)
        (decide (C ⟨auxBVertex i t, auxB_mem hi ht⟩ < C ⟨auxAVertex i t, auxA_mem hi ht⟩)) =
        (C ⟨auxAVertex i t, auxA_mem hi ht⟩, C ⟨auxBVertex i t, auxB_mem hi ht⟩)) := by
  set E := canonicalEdges G
  have hstep : ∀ i (hi : i < G.distinctVertices.length) t (ht : t < (incEdges E i).length),
      C ⟨chainVertex i (t + 1), chain_mem hi ht⟩ = C ⟨chainVertex i t, chain_mem hi ht.le⟩ ∧
      C ⟨portVertex i t, port_mem hi ht⟩ = C ⟨chainVertex i t, chain_mem hi ht.le⟩ ∧
      otherPair (C ⟨chainVertex i t, chain_mem hi ht.le⟩)
        (decide (C ⟨auxBVertex i t, auxB_mem hi ht⟩ < C ⟨auxAVertex i t, auxA_mem hi ht⟩)) =
        (C ⟨auxAVertex i t, auxA_mem hi ht⟩, C ⟨auxBVertex i t, auxB_mem hi ht⟩) :=
    fun i hi t ht => by
      have hdv : ∀ {u v} (hu : u ∈ (toDegreeFour G).vertices) (hv : v ∈ (toDegreeFour G).vertices),
          u ≠ v → (u, v) ∈ diamondEdges i t → C ⟨u, hu⟩ ≠ C ⟨v, hv⟩ := fun hu hv hne hm =>
        C.valid ⟨hne, Or.inl (List.mem_append_left _ (List.mem_flatMap.mpr ⟨i,
          List.mem_range.mpr hi, List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, hm⟩⟩))⟩
      exact h5_forced _ _ _ _ _
        (hdv _ _ (by simp [auxAVertex, auxBVertex]) (by simp [diamondEdges]))
        (hdv _ _ (by simp [chainVertex, auxAVertex]) (by simp [diamondEdges]))
        (hdv _ _ (by simp [chainVertex, auxBVertex]) (by simp [diamondEdges]))
        (hdv _ _ (by simp [chainVertex, auxAVertex]) (by simp [diamondEdges]))
        (hdv _ _ (by simp [chainVertex, auxBVertex]) (by simp [diamondEdges]))
        (hdv _ _ (by simp [portVertex, auxAVertex]) (by simp [diamondEdges]))
        (hdv _ _ (by simp [portVertex, auxBVertex]) (by simp [diamondEdges]))
  have hch : ∀ i (hi : i < G.distinctVertices.length) t (ht : t ≤ (incEdges E i).length),
      C ⟨chainVertex i t, chain_mem hi ht⟩ =
        C ⟨chainVertex i 0, chain_mem hi (Nat.zero_le _)⟩ := fun i hi t => by
    induction t with
    | zero => intro _; rfl
    | succ t ih => intro ht; exact (hstep i hi t ht).1.trans (ih (Nat.le_of_succ_le ht))
  exact ⟨hch, fun i hi t ht =>
    let ⟨_, hp1, hp2⟩ := hstep i hi t ht; (hch i hi t ht.le) ▸ ⟨hp1, hp2⟩⟩

private theorem nonempty_toDegreeFourColoringEquiv (G : Graph) :
    Nonempty ((G.induced.Coloring (Fin 3) × (DiamondIdx G → Bool)) ≃
      (toDegreeFour G).induced.Coloring (Fin 3)) := by
  set E := canonicalEdges G
  have hedge_valid : ∀ (C : (toDegreeFour G).induced.Coloring (Fin 3)) {u v : ℕ}
      (hu : u ∈ (toDegreeFour G).vertices) (hv : v ∈ (toDegreeFour G).vertices),
      u ≠ v → (u, v) ∈ degreeFourEdges G → C ⟨u, hu⟩ ≠ C ⟨v, hv⟩ := fun C _ _ _ _ hne he =>
    C.valid ⟨hne, Or.inl he⟩
  have hbase_valid : ∀ (C : (toDegreeFour G).induced.Coloring (Fin 3))
      {u v : {x // x ∈ G.vertices}}, G.induced.Adj u v →
      C ⟨chainVertex (G.vertexEquiv.symm u).val 0,
          chain_mem (G.vertexEquiv.symm u).isLt (Nat.zero_le _)⟩ ≠
        C ⟨chainVertex (G.vertexEquiv.symm v).val 0,
          chain_mem (G.vertexEquiv.symm v).isLt (Nat.zero_le _)⟩ := by
    intro C u v hadj
    let iu := G.vertexEquiv.symm u; let iv := G.vertexEquiv.symm v
    have huv_ne : iu ≠ iv := fun h => G.induced.loopless.irrefl u
      ((G.vertexEquiv.symm.injective h) ▸ hadj)
    have hlt_or : ∀ (a b : Fin G.distinctVertices.length), a.val < b.val →
        G.induced.Adj (G.vertexEquiv a) (G.vertexEquiv b) →
        C ⟨chainVertex a.val 0, chain_mem a.isLt (Nat.zero_le _)⟩ ≠
          C ⟨chainVertex b.val 0, chain_mem b.isLt (Nat.zero_le _)⟩ := by
      intro a b hab hadj'
      rw [Graph.induced_adj, Graph.vertexEquiv_apply, Graph.vertexEquiv_apply] at hadj'
      obtain ⟨k, hk, heqk⟩ := List.getElem_of_mem
        ((mem_canonicalEdges_iff (G := G) (p := (a.val, b.val))).mpr ⟨hab, b.isLt, hadj'⟩)
      have hgetk : E.getD k (0, 0) = (a.val, b.val) := (getD_eq_getElem _ _ hk).trans heqk
      have hta := List.idxOf_lt_length_iff.mpr
        ((mem_incEdges_iff (E := E) (i := a.val)).mpr ⟨hk, Or.inl (by rw [hgetk])⟩)
      have htb := List.idxOf_lt_length_iff.mpr
        ((mem_incEdges_iff (E := E) (i := b.val)).mpr ⟨hk, Or.inr (by rw [hgetk])⟩)
      have hext_mem : (portVertex a.val ((incEdges E a.val).idxOf k),
          portVertex b.val ((incEdges E b.val).idxOf k)) ∈ degreeFourEdges G :=
        List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk,
          by rw [show canonicalEdges G = E from rfl, hgetk]⟩)
      have hp_ne := hedge_valid C (port_mem a.isLt hta) (port_mem b.isLt htb)
        (by simp [portVertex, Nat.pair_eq_pair]; omega) hext_mem
      obtain ⟨_, hauxC⟩ := toDegreeFourColoringEquiv_aux C
      rwa [(hauxC a.val a.isLt _ hta).1, (hauxC b.val b.isLt _ htb).1] at hp_ne
    have hu_eq : G.vertexEquiv iu = u := G.vertexEquiv.apply_symm_apply u
    have hv_eq : G.vertexEquiv iv = v := G.vertexEquiv.apply_symm_apply v
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne huv_ne) with hlt | hgt
    · exact hlt_or iu iv hlt (by rw [hu_eq, hv_eq]; exact hadj)
    · exact (hlt_or iv iu hgt (by rw [hv_eq, hu_eq]; exact hadj.symm)).symm
  refine ⟨{ toFun := fun ⟨C₀, bits⟩ =>
              SimpleGraph.Coloring.mk (fun v => degreeFourColorFn G C₀ bits v.1) fun {_ _} huv =>
                ((Graph.toSimpleGraph_adj.mp (Graph.induced_adj.mp huv)).2).elim
                  (degreeFourColorFn_ne_of_edge C₀ bits)
                  fun h => (degreeFourColorFn_ne_of_edge C₀ bits h).symm
            invFun := fun C =>
              (SimpleGraph.Coloring.mk (fun u => C ⟨chainVertex (G.vertexEquiv.symm u).val 0,
                  chain_mem (G.vertexEquiv.symm u).isLt (Nat.zero_le _)⟩)
                  (fun {_ _} => hbase_valid C),
               fun ⟨⟨i, hi⟩, ⟨t, ht⟩⟩ => decide (C ⟨auxBVertex i t, auxB_mem hi ht⟩ <
                 C ⟨auxAVertex i t, auxA_mem hi ht⟩))
            left_inv := fun ⟨C₀, bits⟩ => Prod.ext (DFunLike.ext _ _ fun u => by
                dsimp only [SimpleGraph.Coloring.mk]
                simp only [RelHom.coeFn_mk, degreeFourColorFn, chainVertex, Nat.unpair_pair,
                  getBaseColor_of_lt (G.vertexEquiv.symm u).isLt, Fin.eta, Equiv.apply_symm_apply])
              (funext fun ⟨⟨i, hi⟩, ⟨t, ht⟩⟩ => by
                dsimp only [SimpleGraph.Coloring.mk]
                simp only [RelHom.coeFn_mk, degreeFourColorFn, auxAVertex, auxBVertex,
                  Nat.unpair_pair, getBaseColor_of_lt hi, getDiamondBit_of_lt hi ht]
                exact (otherPair_valid (C₀ (G.vertexEquiv ⟨i, hi⟩))
                  (bits ⟨⟨i, hi⟩, ⟨t, ht⟩⟩)).2.2.2)
            right_inv := fun C => by
              obtain ⟨hch, hpp⟩ := toDegreeFourColoringEquiv_aux C
              apply DFunLike.ext; rintro ⟨v, hv⟩; dsimp only [SimpleGraph.Coloring.mk]
              rcases mem_degreeFourVertices_iff.mp hv with
                ⟨i, hi, t, ht, rfl⟩ | ⟨i, hi, t, ht, rfl⟩ | ⟨i, hi, t, ht, rfl⟩ |
                ⟨i, hi, t, ht, rfl⟩
              · simp only [degreeFourColorFn, chainVertex, Nat.unpair_pair, getBaseColor_of_lt hi,
                  RelHom.coeFn_mk, Equiv.symm_apply_apply]; exact (hch i hi t ht).symm
              · simp only [degreeFourColorFn, auxAVertex, Nat.unpair_pair, getBaseColor_of_lt hi,
                  getDiamondBit_of_lt hi ht, RelHom.coeFn_mk, Equiv.symm_apply_apply]
                exact congrArg Prod.fst (hpp i hi t ht).2
              · simp only [degreeFourColorFn, auxBVertex, Nat.unpair_pair, getBaseColor_of_lt hi,
                  getDiamondBit_of_lt hi ht, RelHom.coeFn_mk, Equiv.symm_apply_apply]
                exact congrArg Prod.snd (hpp i hi t ht).2
              · simp only [degreeFourColorFn, portVertex, Nat.unpair_pair, getBaseColor_of_lt hi,
                  RelHom.coeFn_mk, Equiv.symm_apply_apply]; exact (hpp i hi t ht).1.symm }⟩

/-- **Exact `#3-Coloring` count of `ThreeColoring.toDegreeFour`**. -/
theorem sharpThreeColoring_toDegreeFour (G : Graph) :
    SharpThreeColoring (toDegreeFour G) =
      2 ^ (2 * (canonicalEdges G).length) * SharpThreeColoring G := by
  obtain ⟨ed⟩ := nonempty_toDegreeFourColoringEquiv G
  let e := (Equiv.prodCongrLeft fun _ => (coloringEquiv 3 G).symm).trans ed
  rw [show SharpThreeColoring (toDegreeFour G) = Fintype.card _ from
      sharpKColoring_eq_fintype_card e,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_sigma]
  simp only [Fintype.card_fin, sum_length_incEdges_canonicalEdges]
  rw [SharpThreeColoring, SharpKColoring, ← Fintype.card_subtype, Nat.mul_comm]

/-- `toDegreeFour G` is `3`-colorable iff `G` is `3`-colorable. -/
theorem toDegreeFour_mem_iff (G : Graph) :
    toDegreeFour G ∈ ThreeColoring ↔ G ∈ ThreeColoring := by
  rw [ThreeColoring, mem_KColoring_iff_pos_SharpKColoring, mem_KColoring_iff_pos_SharpKColoring]
  change 0 < SharpThreeColoring (toDegreeFour G) ↔ 0 < SharpThreeColoring G
  rw [sharpThreeColoring_toDegreeFour]
  have hpos : 0 < 2 ^ (2 * (canonicalEdges G).length) := by positivity
  exact ⟨fun h => Nat.pos_of_mul_pos_left h, fun h => Nat.mul_pos hpos h⟩

theorem toDegreeFour_mem_DegreeFourThreeColoring_iff (G : Graph) :
    toDegreeFour G ∈ DegreeFourThreeColoring ↔ G ∈ ThreeColoring := by
  simp only [DegreeFourThreeColoring, Set.mem_ofPred_eq, maxDegree_toDegreeFour_le, true_and,
    toDegreeFour_mem_iff]

private theorem computableInPolyTime_chainVertex {γ : Type} {enc : γ ↪ List Bool} {i t : γ → ℕ}
    (hi : ComputableInPolyTime i enc encUnary) (ht : ComputableInPolyTime t enc encUnary) :
    ComputableInPolyTime (fun x => chainVertex (i x) (t x)) enc encNat :=
  computableInPolyTime_tagPair 0 hi ht
private theorem computableInPolyTime_auxAVertex {γ : Type} {enc : γ ↪ List Bool} {i t : γ → ℕ}
    (hi : ComputableInPolyTime i enc encUnary) (ht : ComputableInPolyTime t enc encUnary) :
    ComputableInPolyTime (fun x => auxAVertex (i x) (t x)) enc encNat :=
  computableInPolyTime_tagPair 1 hi ht
private theorem computableInPolyTime_auxBVertex {γ : Type} {enc : γ ↪ List Bool} {i t : γ → ℕ}
    (hi : ComputableInPolyTime i enc encUnary) (ht : ComputableInPolyTime t enc encUnary) :
    ComputableInPolyTime (fun x => auxBVertex (i x) (t x)) enc encNat :=
  computableInPolyTime_tagPair 2 hi ht
private theorem computableInPolyTime_portVertex {γ : Type} {enc : γ ↪ List Bool} {i t : γ → ℕ}
    (hi : ComputableInPolyTime i enc encUnary) (ht : ComputableInPolyTime t enc encUnary) :
    ComputableInPolyTime (fun x => portVertex (i x) (t x)) enc encNat :=
  computableInPolyTime_tagPair 3 hi ht

attribute [local fun_prop] computableInPolyTime_chainVertex computableInPolyTime_auxAVertex
  computableInPolyTime_auxBVertex computableInPolyTime_portVertex
@[fun_prop]
theorem computableInPolyTime_canonicalEdges :
    ComputableInPolyTime canonicalEdges encGraph (encList (encPair encUnary encUnary)) := by
  have hall : ComputableInPolyTime allIndexPairs encUnary
      (encList (encPair encUnary encUnary)) := by
    unfold allIndexPairs; exact flatMapWithInput (by fun_prop)
      (mapWithInput (by fun_prop) (by fun_prop))
  have hpairs := hall.comp ((length encNat).comp Graph.computableInPolyTime_distinctVertices)
  unfold canonicalEdges
  exact filterWithInput hpairs (bool_and' (unary_lt' (by fun_prop) (by fun_prop))
    (Graph.computableInPolyTime_adjBool_comp (fst encGraph (encPair encUnary encUnary))
      (by fun_prop) (by fun_prop)))
private theorem computableInPolyTime_incEdges :
    ComputableInPolyTime (fun p : List (ℕ × ℕ) × ℕ => incEdges p.1 p.2)
      (encPair (encList (encPair encUnary encUnary)) encUnary) (encList encUnary) := by
  have hlen : ComputableInPolyTime (fun p : List (ℕ × ℕ) × ℕ => List.range p.1.length)
      (encPair (encList (encPair encUnary encUnary)) encUnary) (encList encUnary) := by fun_prop
  have hget : ComputableInPolyTime (fun q : (List (ℕ × ℕ) × ℕ) × ℕ => q.1.1.getD q.2 (0, 0))
      (encPair (encPair (encList (encPair encUnary encUnary)) encUnary) encUnary)
      (encPair encUnary encUnary) := by fun_prop
  unfold incEdges; exact filterWithInput hlen (bool_or.comp
    ((unary_beq hget.fst' (fst _ _).snd').prod (unary_beq hget.snd' (fst _ _).snd')))
private theorem computableInPolyTime_incRange :
    ComputableInPolyTime (fun p : Graph × ℕ =>
        List.range (incEdges (canonicalEdges p.1) p.2).length)
      (encPair encGraph encUnary) (encList encUnary) := by
  have hpair := (computableInPolyTime_canonicalEdges.comp (fst encGraph encUnary)).prod
    (snd encGraph encUnary)
  have hinc := computableInPolyTime_incEdges.comp hpair
  have hlen := (length encUnary).comp hinc
  exact unary_range' hlen
private theorem computableInPolyTime_degreeFourVertices :
    ComputableInPolyTime degreeFourVertices encGraph (encList encNat) := by
  have hn : ComputableInPolyTime (fun G : Graph => List.range G.distinctVertices.length)
      encGraph (encList encUnary) := by fun_prop
  have hstep : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ =>
        [chainVertex q.1.2 (q.2 + 1), auxAVertex q.1.2 q.2,
          auxBVertex q.1.2 q.2, portVertex q.1.2 q.2])
      (encPair (encPair encGraph encUnary) encUnary) (encList encNat) := by fun_prop
  unfold degreeFourVertices; exact flatMapWithInput hn
    (listAppend' (by fun_prop) (flatMapWithInput computableInPolyTime_incRange hstep))
private theorem computableInPolyTime_degreeFourEdges :
    ComputableInPolyTime degreeFourEdges encGraph (encList (encPair encNat encNat)) := by
  have hn : ComputableInPolyTime (fun G : Graph => List.range G.distinctVertices.length)
      encGraph (encList encUnary) := by fun_prop
  have hdiam : ComputableInPolyTime (fun q : (Graph × ℕ) × ℕ => diamondEdges q.1.2 q.2)
      (encPair (encPair encGraph encUnary) encUnary) (encList (encPair encNat encNat)) := by
    unfold diamondEdges; fun_prop
  have hE := computableInPolyTime_canonicalEdges
  have heGet : ComputableInPolyTime (fun q : Graph × ℕ => (canonicalEdges q.1).getD q.2 (0, 0))
      (encPair encGraph encUnary) (encPair encUnary encUnary) := by fun_prop
  have hp1 := (hE.comp (fst encGraph encUnary)).prod heGet.fst'
  have hidx1 := idxOfWithInput (computableInPolyTime_incEdges.comp hp1) (snd encGraph encUnary)
  have hp2 := (hE.comp (fst encGraph encUnary)).prod heGet.snd'
  have hidx2 := idxOfWithInput (computableInPolyTime_incEdges.comp hp2) (snd encGraph encUnary)
  have hext := (computableInPolyTime_portVertex heGet.fst' hidx1).prod
    (computableInPolyTime_portVertex heGet.snd' hidx2)
  unfold degreeFourEdges; exact listAppend'
    (flatMapWithInput hn (flatMapWithInput computableInPolyTime_incRange hdiam))
    (mapWithInput (unary_range' ((length (encPair encUnary encUnary)).comp hE)) hext)
attribute [local fun_prop] computableInPolyTime_degreeFourVertices
  computableInPolyTime_degreeFourEdges
/-- `ThreeColoring.toDegreeFour` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toDegreeFour :
    ComputableInPolyTime toDegreeFour encGraph encGraph := by unfold toDegreeFour; fun_prop

end ThreeColoring

/-! ### NP-Completeness, Unconditional Runtime Transfers, and `ETH` / `SharpETH` Lower Bounds -/

/-- **`DegreeFourThreeColoring` is `NP`-complete**. -/
theorem DegreeFourThreeColoring_npComplete : NPComplete encGraph DegreeFourThreeColoring := by
  have hNP : DegreeFourThreeColoring ∈ NP encGraph := by
    have heq : DegreeFourThreeColoring =
        {G : Graph | maxDegreeLeBool 4 G = true} ∩ ThreeColoring := by
      ext G; simp [DegreeFourThreeColoring, maxDegreeLeBool_eq_true_iff]
    obtain ⟨p, v, hv, hver⟩ := KColoring.mem_NP 3
    refine ⟨p, fun x => maxDegreeLeBool 4 x.1 && v x,
      bool_and' ((computableInPolyTime_maxDegreeLeBool 4).comp (fst _ _)) hv, fun G => ?_⟩
    rw [heq, Set.mem_inter_iff, Set.mem_ofPred_eq]; simp only [Bool.and_eq_true]
    exact ⟨fun ⟨hdeg, hcol⟩ => let ⟨w, hwlen, hw⟩ := (hver G).mp hcol; ⟨w, hwlen, hdeg, hw⟩,
      fun ⟨w, hwlen, hdeg, hw⟩ => ⟨hdeg, (hver G).mpr ⟨w, hwlen, hw⟩⟩⟩
  exact ⟨hNP, ThreeColoring_npHard.trans ⟨ThreeColoring.toDegreeFour,
    ThreeColoring.computableInPolyTime_toDegreeFour,
    fun G => (ThreeColoring.toDegreeFour_mem_DegreeFourThreeColoring_iff G).symm⟩⟩

def toDegreeFourCountColoring (φ : CNF ℕ) : Graph :=
  ThreeColoring.toDegreeFour (SAT.toCountThreeColoring φ)
@[fun_prop]
theorem computableInPolyTime_toDegreeFourCountColoring :
    ComputableInPolyTime toDegreeFourCountColoring encCNF encGraph :=
  ThreeColoring.computableInPolyTime_toDegreeFour.comp SAT.computableInPolyTime_toCountThreeColoring
theorem toDegreeFourCountColoring_mem_iff (φ : CNF ℕ) :
    toDegreeFourCountColoring φ ∈ DegreeFourThreeColoring ↔ φ ∈ SAT := by
  rw [toDegreeFourCountColoring, ThreeColoring.toDegreeFour_mem_DegreeFourThreeColoring_iff,
    SAT.toCountThreeColoring_mem_iff]
theorem numVertices_toDegreeFourCountColoring_le {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (toDegreeFourCountColoring φ).numVertices ≤ 648 * φ.length + 27 := by
  obtain ⟨hV, hE⟩ := SAT.length_toCountThreeColoring_le hφ
  have h1 := ThreeColoring.numVertices_toDegreeFour_le (SAT.toCountThreeColoring φ)
  have h2 := (SAT.toCountThreeColoring φ).numVertices_le_length_vertices
  dsimp only [toDegreeFourCountColoring]; omega
theorem sharpDegreeFourThreeColoring_toDegreeFourCountColoring (φ : CNF ℕ) :
    SharpDegreeFourThreeColoring (toDegreeFourCountColoring φ) =
      (6 * 2 ^ (3 * φ.vars.length +
        2 * (ThreeColoring.canonicalEdges (SAT.toCountThreeColoring φ)).length)) * SharpSAT φ := by
  rw [toDegreeFourCountColoring,
    sharpDegreeFourThreeColoring_of_maxDegree_le (ThreeColoring.maxDegree_toDegreeFour_le _),
    ThreeColoring.sharpThreeColoring_toDegreeFour, SAT.sharpThreeColoring_toCountThreeColoring,
    show (8 : ℕ) ^ φ.vars.length = 2 ^ (3 * φ.vars.length) by
      rw [show (8 : ℕ) = 2 ^ 3 by decide, ← Nat.pow_mul], Nat.pow_add]; ring

private def threeSATGraph (φ : CNF ℕ) : Graph :=
  if φ.all (fun c => decide (c.length ≤ 3)) then toDegreeFourCountColoring φ
  else toDegreeFourCountColoring [[]]
private theorem computableInPolyTime_threeSATGraph :
    ComputableInPolyTime threeSATGraph encCNF encGraph :=
  ComputableInPolyTime.ite' (computableInPolyTime_all_length_le 3)
    computableInPolyTime_toDegreeFourCountColoring (const _)
private theorem numVertices_threeSATGraph_le (φ : CNF ℕ) :
    (threeSATGraph φ).numVertices ≤ 675 * φ.length + 675 := by
  dsimp only [threeSATGraph]; split_ifs with hw
  · simp only [List.all_eq_true, decide_eq_true_eq] at hw
    have := numVertices_toDegreeFourCountColoring_le hw; omega
  · have := numVertices_toDegreeFourCountColoring_le (φ := [[]]) (by simp); simp at this; omega
theorem DecidableInExpTime.threeSAT_length_of_degreeFourThreeColoring {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime DegreeFourThreeColoring encGraph Graph.numVertices δ) :
    DecidableInExpTime ThreeSAT encCNF List.length (675 * δ) := by
  refine h.of_reduction computableInPolyTime_threeSATGraph (fun φ => ?_) (c := 675)
    numVertices_threeSATGraph_le hδ
  dsimp only [threeSATGraph]; split_ifs with hw
  · simp only [List.all_eq_true, decide_eq_true_eq] at hw
    rw [toDegreeFourCountColoring_mem_iff]; exact ⟨fun h' => h'.2, fun h' => ⟨hw, h'⟩⟩
  · simp only [List.all_eq_true, decide_eq_true_eq] at hw
    rw [toDegreeFourCountColoring_mem_iff, mem_SAT]
    exact ⟨fun h' => (hw h'.1).elim, fun ⟨_, hσ⟩ => by simp at hσ⟩
/-- **Unconditional decision runtime transfer (`ThreeSAT` in `CNF.numVars`)**. -/
theorem DecidableInSubexpTime.threeSAT_of_degreeFourThreeColoring
    (h : DecidableInSubexpTime DegreeFourThreeColoring encGraph Graph.numVertices) :
    DecidableInSubexpTime ThreeSAT encCNF CNF.numVars := by
  have hlen : DecidableInSubexpTime ThreeSAT encCNF List.length := fun δ hδ =>
    ((h (δ / 676) (by positivity)).threeSAT_length_of_degreeFourThreeColoring (by positivity)).mono
      (by linarith)
  rw [← KSAT_three] at hlen ⊢; exact fun δ hδ => hlen.numVars_of_length δ hδ
/-- **ETH lower bound for `DegreeFourThreeColoring`**. -/
theorem ETH.not_decidableInSubexpTime_degreeFourThreeColoring (hETH : ETH) :
    ∃ β : ℝ, 0 < β ∧ ¬DecidableInExpTime DegreeFourThreeColoring encGraph Graph.numVertices β := by
  by_contra h; push Not at h
  exact ETH_iff_not_decidableInSubexpTime.mp hETH
    (DecidableInSubexpTime.threeSAT_of_degreeFourThreeColoring h)
private def countScaleFactor (φ : CNF ℕ) : ℕ :=
  6 * 2 ^ (3 * φ.vars.length +
    2 * (ThreeColoring.canonicalEdges (SAT.toCountThreeColoring φ)).length)
private theorem computableInPolyTime_countScaleFactor :
    ComputableInPolyTime countScaleFactor encCNF encNat := by
  have hv : ComputableInPolyTime (CNF.vars (V := ℕ)) encCNF (encList encNat) := by
    unfold encCNF; fun_prop
  have hf := binary_mul' (const 6) (binary_two_pow.comp
    (unary_add' (unary_mul' (const 3) ((length encNat).comp hv))
      (unary_mul' (const 2) ((length (encPair encUnary encUnary)).comp
        (ThreeColoring.computableInPolyTime_canonicalEdges.comp
          SAT.computableInPolyTime_toCountThreeColoring)))))
  convert hf using 1
  funext φ; simp only [Function.comp_apply, countScaleFactor]

theorem ComputableInExpTime.sharpThreeSAT_length_of_sharpDegreeFourThreeColoring {δ : ℝ}
    (hδ : 0 ≤ δ)
    (h : ComputableInExpTime SharpDegreeFourThreeColoring encGraph encNat Graph.numVertices δ) :
    ComputableInExpTime SharpThreeSAT encCNF encNat List.length (675 * δ) := by
  obtain ⟨e, hcompO⟩ := h.of_reduction computableInPolyTime_threeSATGraph
    numVertices_threeSATGraph_le hδ
  obtain ⟨t₁, c₁, hcomp_inO, ht₁⟩ := hcompO.exists_computableInO
  have hpost_poly : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ =>
        if p.1.all (fun c => decide (c.length ≤ 3)) then p.2 / countScaleFactor p.1 else 0)
      (encPair encCNF encNat) encNat :=
    ComputableInPolyTime.ite' ((computableInPolyTime_all_length_le 3).comp (fst encCNF encNat))
      (binary_div.comp ((snd encCNF encNat).prod
        (computableInPolyTime_countScaleFactor.comp (fst encCNF encNat)))) (const 0)
  obtain ⟨d, _, hpost_deg⟩ := hpost_poly.exists_degree
  obtain ⟨p_b, q_b, hp_b⟩ := (polyBounded_length_encNat_SharpDegreeFourThreeColoring.comp
    computableInPolyTime_threeSATGraph.polyBounded_length).exists_le
  have hid_inO : ComputableInO (fun φ : CNF ℕ => φ) encCNF encCNF
      (fun φ => (encCNF φ).length) (fun φ => (encCNF φ).length) := ComputableInO.of_eq fun _ => rfl
  have hfull_inO' := hpost_deg.inO.comp (hid_inO.prod hcomp_inO)
  have hfun_eq : (fun φ : CNF ℕ =>
      if φ.all (fun c => decide (c.length ≤ 3)) then
        SharpDegreeFourThreeColoring (threeSATGraph φ) / countScaleFactor φ
      else 0) = SharpThreeSAT := by
    funext φ; dsimp only [SharpThreeSAT, threeSATGraph]; split_ifs with hw
    · rw [sharpDegreeFourThreeColoring_toDegreeFourCountColoring]
      exact Nat.mul_div_right _ (by positivity)
    · rfl
  set E : ℕ := e + (q_b + 1) * d + 1
  refine ComputableInExpTime.of_computableInO (hfull_inO'.of_enc_eq fun φ =>
      congrArg encNat (congrFun hfun_eq φ).symm)
    (2 * c₁ + 2 + (3 + p_b) ^ d) E fun φ => ?_
  set L := (encCNF φ).length
  set X : ℝ := (2 : ℝ) ^ (675 * δ * φ.length) * ((L : ℝ) + 1) ^ E
  have hX0 : 0 ≤ X := by positivity
  have ht₁' : (t₁ φ : ℝ) ≤ 2 * (c₁ : ℝ) * X := by
    have h := le_two_mul_mul_of_le_mul_add (ht₁ φ)
      (two_rpow_mul_pow_le_two_rpow_mul_pow le_rfl (by omega : e ≤ E))
      (one_le_two_rpow_mul_pow (by positivity))
    dsimp only [L, X] at h ⊢; push_cast at h; exact h
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (675 * δ * φ.length) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hL_rpow : (L : ℝ) ≤ X :=
    (show (L : ℝ) ≤ ((L : ℝ) + 1) ^ E from mod_cast (Nat.le_succ L).trans
      (Nat.le_self_pow (by omega) _)).trans (le_mul_of_one_le_left (by positivity) h2)
  have hpair_len : (encPair encCNF encNat
      (φ, SharpDegreeFourThreeColoring (threeSATGraph φ))).length + 1 ≤
      (3 + p_b) * (L + 1) ^ (q_b + 1) := by
    have hb := hp_b φ; rw [length_encPair]
    have hL1 : L + 1 ≤ (L + 1) ^ (q_b + 1) := Nat.le_self_pow (by omega) _
    have hq1 : (L + 1) ^ q_b ≤ (L + 1) ^ (q_b + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_succ q_b)
    nlinarith
  have hpair_pow : (((encPair encCNF encNat
      (φ, SharpDegreeFourThreeColoring (threeSATGraph φ))).length + 1 : ℕ) : ℝ) ^ d ≤
      ((3 + p_b) ^ d : ℕ) * ((L : ℝ) + 1) ^ E := mod_cast
    ((Nat.pow_le_pow_left hpair_len d).trans_eq (by rw [Nat.mul_pow, ← Nat.pow_mul])).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos L) (by omega)))
  have hpair_rpow : (((encPair encCNF encNat
      (φ, SharpDegreeFourThreeColoring (threeSATGraph φ))).length + 1 : ℕ) : ℝ) ^ d ≤
      ((3 + p_b) ^ d : ℕ) * X :=
    hpair_pow.trans (by
      dsimp only [X]; rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (Nat.cast_nonneg _) h2)
        (by positivity))
  change (((L + t₁ φ) + ((encPair encCNF encNat
      (φ, SharpDegreeFourThreeColoring (threeSATGraph φ))).length + 1) ^ d : ℕ) : ℝ) ≤
    ((2 * c₁ + 2 + (3 + p_b) ^ d : ℕ) : ℝ) * X
  push_cast at hpair_rpow ⊢
  linarith only [ht₁', hL_rpow, hpair_rpow, hX0]

/-- **Unconditional counting runtime transfer (`SharpThreeSAT` in `CNF.numVars`)**. -/
theorem ComputableInSubexpTime.sharpThreeSAT_of_sharpDegreeFourThreeColoring
    (h : ComputableInSubexpTime SharpDegreeFourThreeColoring encGraph encNat Graph.numVertices) :
    ComputableInSubexpTime SharpThreeSAT encCNF encNat CNF.numVars := by
  have hlen : ComputableInSubexpTime SharpThreeSAT encCNF encNat List.length := fun δ hδ =>
    ((h (δ / 676) (by positivity)).sharpThreeSAT_length_of_sharpDegreeFourThreeColoring
      (by positivity)).mono (by linarith)
  rw [← SharpKSAT_three] at hlen ⊢; exact hlen.SharpKSAT_numVars_of_length

/-- **`#ETH` lower bound for `SharpDegreeFourThreeColoring`**. -/
theorem SharpETH.not_computableInSubexpTime_sharpDegreeFourThreeColoring (hSharpETH : SharpETH) :
    ∃ β : ℝ, 0 < β ∧
      ¬ComputableInExpTime SharpDegreeFourThreeColoring encGraph encNat Graph.numVertices β := by
  by_contra h; push Not at h
  exact SharpETH_iff_not_computableInSubexpTime.mp hSharpETH
    (ComputableInSubexpTime.sharpThreeSAT_of_sharpDegreeFourThreeColoring h)

end Cslib.Complexity
