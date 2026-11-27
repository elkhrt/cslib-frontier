/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Papers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Problems.UGraph
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Complexity Foundations for Edge Coloring of Regular Graphs

This module provides polynomial-time query primitives (`ugraphOrder`, `ugraphAdjBool`,
`ugraphDegree`) for adjacency-matrix undirected graph instances (`Cslib.Complexity.UGraphInstance`),
defines proper `k`-edge-colorability (`IsProperEdgeColoring`, `IsEdgeColorable` via line-graph
vertex colorability) and the general and `k`-regular `k`-edge-coloring decision problems, proves
`NP` membership for all `k : ℕ`, proves deterministic polynomial-time (`P`) decidability for
`k ∈ {0, 1}`, and constructs explicit Class 1 and Class 2 nonempty `k`-regular graph families for
every `k ≥ 3`.

All declarations in this module are proved under standard Lean axioms using only `Mathlib` and
`CslibFrontier`.

## Main definitions

* `CslibFrontier.Complexity.ugraphOrder`, `CslibFrontier.Complexity.ugraphAdjBool`,
  `CslibFrontier.Complexity.ugraphDegree`: polynomial-time vertex count, adjacency query, and
  vertex degree on `Cslib.Complexity.UGraphInstance`.
* `CslibFrontier.Complexity.IsProperEdgeColoring`, `CslibFrontier.Complexity.IsEdgeColorable`:
  proper edge coloring and `k`-edge-colorability (`G.lineGraph.Colorable k`).
* `CslibFrontier.Complexity.IsNonemptyRegular`, `CslibFrontier.Complexity.encRegularUGraph`:
  nonempty `k`-regular instance predicate and subtype encoding.
* `CslibFrontier.Complexity.edgeColorableUGraph`, `CslibFrontier.Complexity.regularEdgeColoring`,
  `CslibFrontier.Complexity.restrictedRegularEdgeColoring`: edge-coloring decision languages.
* `CslibFrontier.Complexity.completeBipartiteRegularUGraph`,
  `CslibFrontier.Complexity.classTwoRegularUGraph`: explicit Class 1 (`k ≥ 1`) and Class 2 (`k ≥ 3`)
  nonempty `k`-regular graph families.

## Main results

* `CslibFrontier.Complexity.computableInPolyTime_ugraphOrder`,
  `CslibFrontier.Complexity.computableInPolyTime_ugraphAdjBool_comp`,
  `CslibFrontier.Complexity.computableInPolyTime_ugraphDegree_comp`: `@[fun_prop]` polynomial-time
  rules for `UGraphInstance` queries.
* `CslibFrontier.Complexity.isNonemptyRegular_mem_P`: recognizing nonempty `k`-regular graphs is in
  `P`.
* `CslibFrontier.Complexity.edgeColorableUGraph_mem_NP`,
  `CslibFrontier.Complexity.regularEdgeColoring_mem_NP`,
  `CslibFrontier.Complexity.restrictedRegularEdgeColoring_mem_NP`: `NP` membership for all `k : ℕ`.
* `CslibFrontier.Complexity.regularEdgeColoring_zero_mem_P`,
  `CslibFrontier.Complexity.regularEdgeColoring_one_mem_P`: polynomial-time decidability for
  `k = 0, 1`.
* `CslibFrontier.Complexity.exists_mem_and_notMem_regularEdgeColoring`,
  `CslibFrontier.Complexity.exists_mem_and_notMem_restrictedRegularEdgeColoring`: Class 1 and
  Class 2 realizability for every `k ≥ 3`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Decidability of adjacency in `G.graph` for `G : UGraphInstance`, scoped to
`CslibFrontier.Complexity`. -/
scoped instance instDecidableRelUGraphAdj (G : UGraphInstance) : DecidableRel G.graph.Adj :=
  fun a b ↦ inferInstanceAs (Decidable (G.adj a b = true))

section EdgeColoring

/-- A function `c : G.edgeSet → α` is a proper edge coloring if distinct edges sharing a common
endpoint receive distinct colors. -/
def IsProperEdgeColoring {V α : Type*} (G : _root_.SimpleGraph V) (c : G.edgeSet → α) : Prop :=
  ∀ (v w₁ w₂ : V) (h₁ : G.Adj v w₁) (h₂ : G.Adj v w₂),
    c ⟨s(v, w₁), h₁⟩ = c ⟨s(v, w₂), h₂⟩ → w₁ = w₂

/-- Pull back a proper edge coloring along an injective graph homomorphism. -/
theorem IsProperEdgeColoring.pullback_of_injective {V W α : Type*} {G : _root_.SimpleGraph V}
    {H : _root_.SimpleGraph W} {c : H.edgeSet → α} (hc : IsProperEdgeColoring H c) (f : G →g H)
    (hfinj : Function.Injective f) :
    IsProperEdgeColoring G (fun e ↦ c (f.mapEdgeSet e)) :=
  fun v w₁ w₂ h₁ h₂ heq ↦ hfinj (hc (f v) (f w₁) (f w₂) (f.map_adj h₁) (f.map_adj h₂) heq)

/-- A simple graph `G` is `k`-edge-colorable if its line graph is `k`-vertex-colorable. -/
def IsEdgeColorable {V : Type*} (G : _root_.SimpleGraph V) (k : ℕ) : Prop :=
  G.lineGraph.Colorable k

/-- `IsEdgeColorable G 0` holds iff `G = ⊥`. -/
theorem isEdgeColorable_zero_iff {V : Type*} {G : _root_.SimpleGraph V} :
    IsEdgeColorable G 0 ↔ G = ⊥ := by
  constructor
  · rintro ⟨C⟩
    ext u v
    simp only [_root_.SimpleGraph.bot_adj, iff_false]
    intro hadj
    exact Fin.elim0 (C ⟨s(u, v), hadj⟩)
  · rintro rfl
    refine ⟨_root_.SimpleGraph.Coloring.mk
      (fun e ↦ False.elim (by have h := e.2; simp at h))
      fun {e₁ _} _ ↦ False.elim (by have h := e₁.2; simp at h)⟩

/-- Equivalence between line-graph `k`-colorability and existence of a `Fin k`-valued proper edge
coloring. -/
theorem isEdgeColorable_iff_exists_isProperEdgeColoring {V : Type*} {G : _root_.SimpleGraph V}
    {k : ℕ} :
    IsEdgeColorable G k ↔ ∃ c : G.edgeSet → Fin k, IsProperEdgeColoring G c := by
  constructor
  · rintro ⟨C⟩
    refine ⟨C, fun v w₁ w₂ h₁ h₂ heq ↦ ?_⟩
    by_contra hne
    have hsne : (⟨s(v, w₁), h₁⟩ : G.edgeSet) ≠ ⟨s(v, w₂), h₂⟩ := by
      intro hs
      rcases Sym2.eq_iff.mp (congrArg Subtype.val hs) with ⟨_, hw⟩ | ⟨hvw, _⟩
      · exact hne hw
      · exact G.loopless.irrefl v (hvw ▸ h₂)
    have hadj : G.lineGraph.Adj ⟨s(v, w₁), h₁⟩ ⟨s(v, w₂), h₂⟩ :=
      _root_.SimpleGraph.lineGraph_adj_iff_exists.mpr
        ⟨hsne, v, Sym2.mem_mk_left v w₁, Sym2.mem_mk_left v w₂⟩
    exact C.valid hadj heq
  · rintro ⟨c, hc⟩
    refine ⟨_root_.SimpleGraph.Coloring.mk c fun {e₁ e₂} hadj heq ↦ ?_⟩
    obtain ⟨hne, v, hv₁, hv₂⟩ := _root_.SimpleGraph.lineGraph_adj_iff_exists.mp hadj
    have hex : ∀ (e : G.edgeSet), v ∈ (e : Sym2 V) →
        ∃ (w : V) (h : G.Adj v w), e = ⟨s(v, w), h⟩ := by
      rintro ⟨s, hs⟩ hv
      induction s using Sym2.ind with
      | _ a b =>
        have hab : G.Adj a b := G.mem_edgeSet.mp hs
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact ⟨b, hab, rfl⟩
        · exact ⟨a, hab.symm, Subtype.ext Sym2.eq_swap⟩
    obtain ⟨w₁, h₁, rfl⟩ := hex e₁ hv₁
    obtain ⟨w₂, h₂, rfl⟩ := hex e₂ hv₂
    have hw : w₁ = w₂ := hc v w₁ w₂ h₁ h₂ heq
    subst hw
    exact hne rfl

/-- Matching bound: each color class of a proper edge coloring has size at most `|V| / 2`, so
`|E(G)| ≤ |α| * (|V| / 2)`. -/
theorem IsProperEdgeColoring.card_edgeFinset_le {V α : Type*} [Fintype V] [Fintype α]
    [DecidableEq V] {G : _root_.SimpleGraph V} [DecidableRel G.Adj] {c : G.edgeSet → α}
    (hc : IsProperEdgeColoring G c) :
    G.edgeFinset.card ≤ Fintype.card α * (Fintype.card V / 2) := by
  classical
  have hfiber : ∀ col : α,
      (Finset.univ.filter fun e : G.edgeSet ↦ c e = col).card ≤ Fintype.card V / 2 := by
    intro col
    let F := Finset.univ.filter fun e : G.edgeSet ↦ c e = col
    let inc : Finset V := Finset.univ.filter fun v : V ↦ ∃ e ∈ F, v ∈ (e : Sym2 V)
    have hsum : ∑ v ∈ inc, (F.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)).card = 2 * F.card := by
      have hswap : ∑ v ∈ inc, (F.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)).card =
          ∑ e ∈ F, (inc.filter fun v ↦ v ∈ (e : Sym2 V)).card := by
        simp_rw [Finset.card_filter]
        exact Finset.sum_comm
      rw [hswap]
      have hconst : ∑ e ∈ F, (inc.filter fun v ↦ v ∈ (e : Sym2 V)).card = ∑ _e ∈ F, 2 := by
        refine Finset.sum_congr rfl fun e he ↦ ?_
        rcases e with ⟨s, hs⟩
        induction s using Sym2.ind with
        | _ u w =>
          have huw : u ≠ w := G.ne_of_adj (G.mem_edgeSet.mp hs)
          have hset : (inc.filter fun v ↦ v ∈ (s(u, w) : Sym2 V)) = {u, w} := by
            ext v
            simp only [Finset.mem_filter, inc, Finset.mem_univ, true_and, Sym2.mem_iff,
              Finset.mem_insert, Finset.mem_singleton]
            refine ⟨And.right, fun hvw ↦ ⟨⟨⟨s(u, w), hs⟩, he, Sym2.mem_iff.mpr hvw⟩, hvw⟩⟩
          rw [hset, Finset.card_pair huw]
      rw [hconst, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have hle_one : ∀ v ∈ inc, (F.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)).card ≤ 1 := by
      intro v _
      refine Finset.card_le_one.mpr fun e₁ he₁ e₂ he₂ ↦ ?_
      dsimp only [F] at he₁ he₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
      have hex : ∀ (e : G.edgeSet), v ∈ (e : Sym2 V) →
          ∃ (w : V) (h : G.Adj v w), e = ⟨s(v, w), h⟩ := by
        rintro ⟨s, hs⟩ hv
        induction s using Sym2.ind with
        | _ a b =>
          have hab : G.Adj a b := G.mem_edgeSet.mp hs
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact ⟨b, hab, rfl⟩
          · exact ⟨a, hab.symm, Subtype.ext Sym2.eq_swap⟩
      obtain ⟨w₁, h₁, rfl⟩ := hex e₁ he₁.2
      obtain ⟨w₂, h₂, rfl⟩ := hex e₂ he₂.2
      have hw : w₁ = w₂ := hc v w₁ w₂ h₁ h₂ (he₁.1.trans he₂.1.symm)
      subst hw
      rfl
    have h2 : 2 * F.card ≤ Fintype.card V := by
      calc 2 * F.card = ∑ v ∈ inc, (F.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)).card :=
            hsum.symm
        _ ≤ ∑ _ ∈ inc, 1 := Finset.sum_le_sum hle_one
        _ = inc.card := by simp
        _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card V := Finset.card_univ
    dsimp only [F] at h2
    omega
  have htot : (Finset.univ : Finset G.edgeSet).card =
      ∑ col : α, (Finset.univ.filter fun e : G.edgeSet ↦ c e = col).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext e
      simp
    · intro a _ b _ hab
      exact Finset.disjoint_left.mpr fun e ha hb ↦ hab ((Finset.mem_filter.mp ha).2.symm.trans
        (Finset.mem_filter.mp hb).2)
  rw [← Fintype.card_coe G.edgeFinset]
  have heq_card : Fintype.card G.edgeFinset = (Finset.univ : Finset G.edgeSet).card := by
    rw [Finset.card_univ]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ ↦ G.mem_edgeFinset)
  rw [heq_card, htot]
  calc ∑ col : α, (Finset.univ.filter fun e : G.edgeSet ↦ c e = col).card
      ≤ ∑ _ : α, (Fintype.card V / 2) := Finset.sum_le_sum fun col _ ↦ hfiber col
    _ = Fintype.card α * (Fintype.card V / 2) := by simp

/-- Every nonempty `k`-regular `k`-edge-colorable finite graph (`1 ≤ k`) has an even number of
vertices. -/
theorem even_card_of_isRegularOfDegree_of_isEdgeColorable {V : Type*} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hreg : G.IsRegularOfDegree k) (hk : 1 ≤ k) (hcol : IsEdgeColorable G k) :
    Even (Fintype.card V) := by
  obtain ⟨c, hc⟩ := isEdgeColorable_iff_exists_isProperEdgeColoring.mp hcol
  have hle := hc.card_edgeFinset_le
  rw [Fintype.card_fin] at hle
  have hsum : Fintype.card V * k = 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    have : ∑ v : V, G.degree v = ∑ _ : V, k := Finset.sum_congr rfl fun v _ ↦ hreg v
    rw [this, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h2 : Fintype.card V * k ≤ k * (2 * (Fintype.card V / 2)) := by
    calc Fintype.card V * k = 2 * G.edgeFinset.card := hsum
      _ ≤ 2 * (k * (Fintype.card V / 2)) := Nat.mul_le_mul_left 2 hle
      _ = k * (2 * (Fintype.card V / 2)) := by ring
  rw [Nat.mul_comm (Fintype.card V) k] at h2
  have hdiv : Fintype.card V ≤ 2 * (Fintype.card V / 2) := Nat.le_of_mul_le_mul_left h2 hk
  have hdiv2 : 2 * (Fintype.card V / 2) ≤ Fintype.card V := Nat.mul_div_le _ _
  exact ⟨Fintype.card V / 2, by omega⟩

end EdgeColoring

section UGraphPolyTime

/-- Number of vertices `G.n` of an undirected graph instance `G`. -/
def ugraphOrder (G : UGraphInstance) : ℕ := G.n

@[simp]
theorem ugraphOrder_eq (G : UGraphInstance) : ugraphOrder G = G.n := by rfl

private lemma countP_quad_eq_self (n : ℕ) :
    ((List.range (n + 1 + n * n)).countP fun k ↦ decide (k * k + k + 2 ≤ n + 1 + n * n)) = n := by
  have hiff : ∀ k : ℕ, (k * k + k + 2 ≤ n + 1 + n * n) ↔ k < n := fun k ↦ by
    constructor
    · intro hle
      by_contra hge
      have hnk : n ≤ k := Nat.le_of_not_lt hge
      have hsq : n * n ≤ k * k := Nat.mul_le_mul hnk hnk
      omega
    · intro hlt
      have hk1 : k + 1 ≤ n := hlt
      nlinarith
  rw [List.countP_eq_length_filter]
  have hfilt : ((List.range (n + 1 + n * n)).filter fun k ↦
      decide (k * k + k + 2 ≤ n + 1 + n * n)) = List.range n := by
    have hrng : List.range (n + 1 + n * n) =
        List.range n ++ (List.range (1 + n * n)).map (n + ·) := by
      rw [show n + 1 + n * n = n + (1 + n * n) by omega, List.range_add]
    rw [hrng, List.filter_append]
    have hleft : ((List.range n).filter fun k ↦ decide (k * k + k + 2 ≤ n + 1 + n * n)) =
        List.range n :=
      List.filter_eq_self.mpr fun k hk ↦ decide_eq_true ((hiff k).mpr (List.mem_range.mp hk))
    have hright : (((List.range (1 + n * n)).map (n + ·)).filter fun k ↦
        decide (k * k + k + 2 ≤ n + 1 + n * n)) = [] :=
      List.filter_eq_nil_iff.mpr fun k hk hdec ↦ by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hk
        have hlt := (hiff (n + j)).mp (of_decide_eq_true hdec)
        omega
    rw [hleft, hright, List.append_nil]
  rw [hfilt, List.length_range]

/-- Computing the vertex count `ugraphOrder G = G.n` from `encUGraph G` is polynomial-time in unary.
-/
@[fun_prop]
theorem computableInPolyTime_ugraphOrder :
    ComputableInPolyTime ugraphOrder encUGraph encUnary := by
  have hraw : ComputableInPolyTime
      (fun G : UGraphInstance ↦
        (List.range (encUGraph G).length).countP fun k ↦
          decide (k * k + k + 2 ≤ (encUGraph G).length))
      encUGraph encUnary := by
    fun_prop
  refine hraw.of_enc_eq fun G ↦ congrArg encUnary ?_
  rw [encUGraph_apply, G.length_encode, countP_quad_eq_self, ugraphOrder]

/-- Compositional `fun_prop` rule for `ugraphOrder`. -/
@[fun_prop]
theorem computableInPolyTime_ugraphOrder_comp {α : Type} {enc : α ↪ List Bool}
    {f : α → UGraphInstance} (hf : ComputableInPolyTime f enc encUGraph) :
    ComputableInPolyTime (fun x ↦ ugraphOrder (f x)) enc encUnary :=
  computableInPolyTime_ugraphOrder.comp hf

/-- Boolean adjacency lookup on natural-number vertex indices (`false` out of bounds). -/
def ugraphAdjBool (G : UGraphInstance) (u v : ℕ) : Bool :=
  G.adjN u v

@[simp]
theorem ugraphAdjBool_eq (G : UGraphInstance) (u v : ℕ) : ugraphAdjBool G u v = G.adjN u v := by
  rfl

/-- `ugraphAdjBool G u v = true` iff `u < G.n`, `v < G.n`, and `G.graph.Adj ⟨u, _⟩ ⟨v, _⟩`. -/
theorem ugraphAdjBool_eq_true_iff (G : UGraphInstance) (u v : ℕ) :
    ugraphAdjBool G u v = true ↔
      ∃ (hu : u < G.n) (hv : v < G.n), G.graph.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  unfold ugraphAdjBool UGraphInstance.adjN
  by_cases h : u < G.n ∧ v < G.n
  · rw [dite_eq_left h]
    exact ⟨fun hadj ↦ ⟨h.1, h.2, hadj⟩, fun ⟨_, _, hadj⟩ ↦ hadj⟩
  · rw [dite_eq_right h]
    exact ⟨Bool.noConfusion, fun ⟨hu, hv, _⟩ ↦ (h ⟨hu, hv⟩).elim⟩

private lemma ugraphAdjBool_eq_getD (G : UGraphInstance) (u v : ℕ) :
    ugraphAdjBool G u v =
      ((decide (u < ugraphOrder G) && decide (v < ugraphOrder G)) &&
        (encUGraph G).getD (ugraphOrder G + 1 + (u * ugraphOrder G + v)) false) := by
  unfold ugraphAdjBool UGraphInstance.adjN ugraphOrder
  by_cases h : u < G.n ∧ v < G.n
  · rw [dite_eq_left h]
    simp only [h.1, h.2, decide_true, Bool.and_self, Bool.true_and, encUGraph_apply,
      List.getD_eq_getElem?_getD, G.getElem?_encode_matrix h.1 h.2, Option.getD_some]
  · rw [dite_eq_right h]
    have hfalse : (decide (u < G.n) && decide (v < G.n)) = false := by
      rw [Bool.and_eq_false_iff]
      by_cases hu : u < G.n
      · right; exact decide_eq_false fun hv ↦ h ⟨hu, hv⟩
      · left; exact decide_eq_false hu
    rw [hfalse, Bool.false_and]

/-- Testing adjacency `ugraphAdjBool (fG x) (fu x) (fv x)` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_ugraphAdjBool_comp {α : Type} {enc : α ↪ List Bool}
    {fG : α → UGraphInstance} {fu fv : α → ℕ}
    (hG : ComputableInPolyTime fG enc encUGraph)
    (hu : ComputableInPolyTime fu enc encUnary)
    (hv : ComputableInPolyTime fv enc encUnary) :
    ComputableInPolyTime (fun x ↦ ugraphAdjBool (fG x) (fu x) (fv x)) enc encBool := by
  have hOrd : ComputableInPolyTime (fun x ↦ ugraphOrder (fG x)) enc encUnary :=
    computableInPolyTime_ugraphOrder_comp hG
  have hBits : ComputableInPolyTime (fun x ↦ encUGraph (fG x)) enc encBits :=
    (of_eq (encIn := encUGraph) (encOut := encBits) fun _ ↦ rfl).comp hG
  have hIdx : ComputableInPolyTime
      (fun x ↦ ugraphOrder (fG x) + 1 + (fu x * ugraphOrder (fG x) + fv x)) enc encUnary := by
    fun_prop
  have hraw : ComputableInPolyTime
      (fun x ↦ (decide (fu x < ugraphOrder (fG x)) && decide (fv x < ugraphOrder (fG x))) &&
        (encUGraph (fG x)).getD
          (ugraphOrder (fG x) + 1 + (fu x * ugraphOrder (fG x) + fv x)) false)
      enc encBool :=
    bool_and' (bool_and' (unary_lt' hu hOrd) (unary_lt' hv hOrd))
      (bitsGetDWithInput hBits hIdx false)
  exact hraw.of_enc_eq fun x ↦ congrArg encBool (ugraphAdjBool_eq_getD (fG x) (fu x) (fv x))

/-- Degree of vertex index `u` in `G` (`0` if `u ≥ G.n`). -/
def ugraphDegree (G : UGraphInstance) (u : ℕ) : ℕ :=
  (List.range (ugraphOrder G)).countP fun v ↦ ugraphAdjBool G u v

/-- Computing vertex degrees in unary is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_ugraphDegree_comp {α : Type} {enc : α ↪ List Bool}
    {fG : α → UGraphInstance} {fu : α → ℕ}
    (hG : ComputableInPolyTime fG enc encUGraph)
    (hu : ComputableInPolyTime fu enc encUnary) :
    ComputableInPolyTime (fun x ↦ ugraphDegree (fG x) (fu x)) enc encUnary := by
  unfold ugraphDegree
  fun_prop

/-- On any vertex `u : Fin G.n`, `ugraphDegree G u.1` equals `G.graph.degree u`. -/
theorem ugraphDegree_eq_degree (G : UGraphInstance) (u : Fin G.n) :
    ugraphDegree G u.1 = G.graph.degree u := by
  unfold ugraphDegree ugraphOrder
  rw [List.countP_eq_length_filter]
  let L := (List.range G.n).filter fun v ↦ ugraphAdjBool G u.1 v
  have hnodup : L.Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hnodup, ← G.graph.card_neighborFinset_eq_degree]
  refine Finset.card_bij
    (fun v hv ↦ ⟨v, List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hv)).1⟩)
    (fun v hv ↦ ?_) (fun _ _ _ _ h ↦ congrArg Fin.val h) (fun w hw ↦ ?_)
  · simp only [L, List.mem_toFinset, List.mem_filter, List.mem_range,
      ugraphAdjBool_eq_true_iff] at hv
    obtain ⟨_, _, hadj⟩ := hv.2
    exact (G.graph.mem_neighborFinset u _).mpr hadj
  · rw [G.graph.mem_neighborFinset] at hw
    refine ⟨w.1, ?_, Fin.eta w w.2⟩
    simp only [L, List.mem_toFinset, List.mem_filter, List.mem_range, ugraphAdjBool_eq_true_iff]
    exact ⟨w.2, u.2, w.2, hw⟩

end UGraphPolyTime

section LanguagesAndNP

/-- Predicate that `G : UGraphInstance` is nonempty (`0 < G.n`) and `k`-regular. -/
def IsNonemptyRegular (k : ℕ) (G : UGraphInstance) : Prop :=
  0 < G.n ∧ G.graph.IsRegularOfDegree k

/-- Explicit conjunction characterization of `IsNonemptyRegular`. -/
theorem isNonemptyRegular_iff {k : ℕ} {G : UGraphInstance} :
    IsNonemptyRegular k G ↔ 0 < G.n ∧ G.graph.IsRegularOfDegree k := by
  rfl

/-- Induced bit-string encoding of the subtype `{G : UGraphInstance // IsNonemptyRegular k G}`. -/
abbrev encRegularUGraph (k : ℕ) : {G : UGraphInstance // IsNonemptyRegular k G} ↪ List Bool :=
  (Function.Embedding.subtype (IsNonemptyRegular k)).trans encUGraph

/-- Executable polynomial-time test for `IsNonemptyRegular k`. -/
def isNonemptyRegularBool (k : ℕ) (G : UGraphInstance) : Bool :=
  decide (0 < ugraphOrder G) &&
    (List.range (ugraphOrder G)).all fun u ↦ decide (ugraphDegree G u = k)

/-- `isNonemptyRegularBool k` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_isNonemptyRegularBool (k : ℕ) :
    ComputableInPolyTime (isNonemptyRegularBool k) encUGraph encBool := by
  unfold isNonemptyRegularBool
  fun_prop

/-- Correctness of `isNonemptyRegularBool`. -/
theorem isNonemptyRegularBool_eq_true_iff (k : ℕ) (G : UGraphInstance) :
    isNonemptyRegularBool k G = true ↔ IsNonemptyRegular k G := by
  simp only [isNonemptyRegularBool, ugraphOrder_eq, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, isNonemptyRegular_iff]
  refine ⟨fun ⟨h0, hall⟩ ↦ ⟨h0, fun u ↦ ?_⟩, fun ⟨h0, hreg⟩ ↦ ⟨h0, fun u hu ↦ ?_⟩⟩
  · rw [← ugraphDegree_eq_degree G u]
    exact hall u.1 u.2
  · rw [ugraphDegree_eq_degree G ⟨u, hu⟩]
    exact hreg ⟨u, hu⟩

/-- Recognizing nonempty `k`-regular undirected graphs lies in `P encUGraph`. -/
theorem isNonemptyRegular_mem_P (k : ℕ) :
    {G : UGraphInstance | IsNonemptyRegular k G} ∈ P encUGraph :=
  ⟨isNonemptyRegularBool k, computableInPolyTime_isNonemptyRegularBool k,
    fun G ↦ (isNonemptyRegularBool_eq_true_iff k G).symm⟩

/-- General `k`-edge-coloring decision problem on `UGraphInstance`. -/
def edgeColorableUGraph (k : ℕ) : Set UGraphInstance :=
  {G | IsEdgeColorable G.graph k}

/-- `k`-edge-coloring decision problem on nonempty `k`-regular `UGraphInstance`s. -/
def regularEdgeColoring (k : ℕ) : Set UGraphInstance :=
  {G | IsNonemptyRegular k G ∧ IsEdgeColorable G.graph k}

/-- `k`-edge-coloring decision problem restricted to
`{G : UGraphInstance // IsNonemptyRegular k G}`. -/
def restrictedRegularEdgeColoring (k : ℕ) :
    Set {G : UGraphInstance // IsNonemptyRegular k G} :=
  {x | IsEdgeColorable x.1.graph k}

/-- Equivalence between `restrictedRegularEdgeColoring k` and `regularEdgeColoring k`. -/
theorem mem_restrictedRegularEdgeColoring_iff_mem {k : ℕ}
    {x : {G : UGraphInstance // IsNonemptyRegular k G}} :
    x ∈ restrictedRegularEdgeColoring k ↔ x.1 ∈ regularEdgeColoring k :=
  ⟨fun hx ↦ ⟨x.2, hx⟩, And.right⟩

/-- Subtype projection reduces `restrictedRegularEdgeColoring k` to `regularEdgeColoring k` in
polynomial time. -/
theorem polyTimeReducible_restrictedRegularEdgeColoring (k : ℕ) :
    PolyTimeReducible (encRegularUGraph k) encUGraph
      (restrictedRegularEdgeColoring k) (regularEdgeColoring k) :=
  ⟨Subtype.val, of_eq fun _ ↦ rfl, fun _ ↦ mem_restrictedRegularEdgeColoring_iff_mem⟩

private lemma getD_append_replicate_false (u : List Bool) (m idx : ℕ) :
    (u ++ List.replicate m false).getD idx false = u.getD idx false := by
  by_cases h : idx < u.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left h,
      List.getD_eq_getElem _ _ h]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_of_not_lt h), List.getElem?_eq_none (Nat.le_of_not_lt h)]
    by_cases h2 : idx - u.length < m
    · simp [h2]
    · rw [List.getElem?_eq_none (by simp; omega)]

private def edgeColoringCheckAt (K : ℕ) (G : UGraphInstance) (bit : ℕ → Bool) : Bool :=
  let N := ugraphOrder G
  ((List.range N).all fun u ↦ (List.range N).all fun v ↦
    !(ugraphAdjBool G u v) ||
      (((List.range K).any fun c ↦ bit ((u * N + v) * K + c)) &&
        ((List.range K).all fun c ↦
          bit ((u * N + v) * K + c) == bit ((v * N + u) * K + c)))) &&
  ((List.range N).all fun u ↦ (List.range N).all fun v₁ ↦ (List.range N).all fun v₂ ↦
    !(decide (v₁ ≠ v₂) && ugraphAdjBool G u v₁ && ugraphAdjBool G u v₂) ||
      ((List.range K).all fun c ↦
        !(bit ((u * N + v₁) * K + c) && bit ((u * N + v₂) * K + c))))

private def edgeColoringVerifier (K : ℕ) (p : UGraphInstance × List Bool) : Bool :=
  edgeColoringCheckAt K p.1 (fun idx ↦ p.2.getD idx false)

private lemma computableInPolyTime_edgeColoringVerifier (K : ℕ) :
    ComputableInPolyTime (edgeColoringVerifier K) (encPair encUGraph encBits) encBool := by
  unfold edgeColoringVerifier edgeColoringCheckAt
  have hK : ∀ {α : Type} {enc : α ↪ List Bool},
      ComputableInPolyTime (fun _ : α ↦ List.range K) enc (encList encUnary) :=
    fun {_ _} ↦ const (List.range K)
  fun_prop

private lemma edgeColorableUGraph_zero_mem_P : edgeColorableUGraph 0 ∈ P encUGraph := by
  refine ⟨fun G ↦ (List.range (ugraphOrder G)).all fun u ↦
      (List.range (ugraphOrder G)).all fun v ↦ !(ugraphAdjBool G u v),
    by fun_prop, fun G ↦ ?_⟩
  simp only [edgeColorableUGraph, Set.mem_ofPred_eq, isEdgeColorable_zero_iff,
    List.all_eq_true, List.mem_range, Bool.not_eq_true', ugraphOrder_eq]
  constructor
  · intro hbot u hu v hv
    rw [Bool.eq_false_iff]
    intro htrue
    obtain ⟨_, _, hadj⟩ := (ugraphAdjBool_eq_true_iff G u v).mp htrue
    rw [hbot] at hadj
    exact hadj
  · intro hall
    ext ⟨u, hu⟩ ⟨v, hv⟩
    simp only [_root_.SimpleGraph.bot_adj, iff_false]
    intro hadj
    have htrue : ugraphAdjBool G u v = true :=
      (ugraphAdjBool_eq_true_iff G u v).mpr ⟨hu, hv, hadj⟩
    exact Bool.noConfusion ((hall u hu v hv).symm.trans htrue)

/-- For every `k : ℕ`, `edgeColorableUGraph k` belongs to `NP encUGraph`. -/
theorem edgeColorableUGraph_mem_NP (k : ℕ) : edgeColorableUGraph k ∈ NP encUGraph := by
  cases k with
  | zero => exact P_subset_NP edgeColorableUGraph_zero_mem_P
  | succ k' =>
    let K := k' + 1
    refine ⟨Polynomial.C K * Polynomial.X, edgeColoringVerifier K,
      computableInPolyTime_edgeColoringVerifier K,
      IsVerifier.of_padding (fun G w _ hV ↦ ?_) (fun G hG ↦ ?_)⟩
    · simp only [edgeColoringVerifier, edgeColoringCheckAt, ugraphOrder_eq, Bool.and_eq_true,
        List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
        beq_iff_eq] at hV
      obtain ⟨hpart1, hpart2⟩ := hV
      rw [edgeColorableUGraph, Set.mem_ofPred_eq, isEdgeColorable_iff_exists_isProperEdgeColoring]
      have hexCol : ∀ (u v : Fin G.n), G.graph.Adj u v →
          ∃ col < K, w.getD ((u.1 * G.n + v.1) * K + col) false = true := fun u v huv ↦ by
        rcases hpart1 u.1 u.2 v.1 v.2 with hfalse | ⟨hex, _⟩
        · have htrue := (ugraphAdjBool_eq_true_iff G u.1 v.1).mpr ⟨u.2, v.2, huv⟩
          exact Bool.noConfusion (hfalse.symm.trans htrue)
        · exact hex
      have hsymm : ∀ (u v : Fin G.n), G.graph.Adj u v → ∀ col < K,
          w.getD ((u.1 * G.n + v.1) * K + col) false =
            w.getD ((v.1 * G.n + u.1) * K + col) false := fun u v huv col hcol ↦ by
        rcases hpart1 u.1 u.2 v.1 v.2 with hfalse | ⟨_, hsym⟩
        · have htrue := (ugraphAdjBool_eq_true_iff G u.1 v.1).mpr ⟨u.2, v.2, huv⟩
          exact Bool.noConfusion (hfalse.symm.trans htrue)
        · exact hsym col hcol
      let pick : G.graph.edgeSet → Fin K := fun e ↦
        let a := e.1.out.1
        let b := e.1.out.2
        have hadj : G.graph.Adj a b := by
          rw [← G.graph.mem_edgeSet, show s(a, b) = e.1 from Quot.out_eq e.1]
          exact e.2
        ⟨(hexCol a b hadj).choose, (hexCol a b hadj).choose_spec.1⟩
      have hpick_bit : ∀ (u v : Fin G.n) (huv : G.graph.Adj u v),
          w.getD ((u.1 * G.n + v.1) * K + (pick ⟨s(u, v), G.graph.mem_edgeSet.mpr huv⟩).1) false =
            true := by
        intro u v huv
        let e : G.graph.edgeSet := ⟨s(u, v), G.graph.mem_edgeSet.mpr huv⟩
        let a := e.1.out.1
        let b := e.1.out.2
        have hadj_ab : G.graph.Adj a b := by
          rw [← G.graph.mem_edgeSet, show s(a, b) = e.1 from Quot.out_eq e.1]
          exact e.2
        have hspec := (hexCol a b hadj_ab).choose_spec.2
        have hcol_lt : (pick e).1 < K := (pick e).2
        rcases Sym2.eq_iff.mp (Quot.out_eq e.1 : s(a, b) = s(u, v)) with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
        · change w.getD ((u.1 * G.n + v.1) * K + (pick e).1) false = true
          rw [← hau, ← hbv]
          exact hspec
        · change w.getD ((u.1 * G.n + v.1) * K + (pick e).1) false = true
          rw [hsymm u v huv (pick e).1 hcol_lt, ← hav, ← hbu]
          exact hspec
      refine ⟨pick, fun u v1 v2 h1 h2 heq ↦ ?_⟩
      by_contra hne
      have hne_val : v1.1 ≠ v2.1 := fun hv ↦ hne (Fin.ext hv)
      have hb1 := hpick_bit u v1 h1
      have hb2 := hpick_bit u v2 h2
      have hlt : (pick ⟨s(u, v1), G.graph.mem_edgeSet.mpr h1⟩).1 < K :=
        (pick ⟨s(u, v1), G.graph.mem_edgeSet.mpr h1⟩).2
      rw [show (pick ⟨s(u, v2), G.graph.mem_edgeSet.mpr h2⟩).1 =
          (pick ⟨s(u, v1), G.graph.mem_edgeSet.mpr h1⟩).1 from
        congrArg Fin.val heq.symm] at hb2
      rcases hpart2 u.1 u.2 v1.1 v1.2 v2.1 v2.2 with hnot | hdiff
      · have ht1 := (ugraphAdjBool_eq_true_iff G u.1 v1.1).mpr ⟨u.2, v1.2, h1⟩
        have ht2 := (ugraphAdjBool_eq_true_iff G u.1 v2.1).mpr ⟨u.2, v2.2, h2⟩
        have htrue : (decide (v1.1 ≠ v2.1) && ugraphAdjBool G u.1 v1.1 &&
            ugraphAdjBool G u.1 v2.1) = true := by
          rw [ht1, ht2]
          simp [hne_val]
        exact Bool.noConfusion (hnot.symm.trans htrue)
      · have hboth := hdiff (pick ⟨s(u, v1), G.graph.mem_edgeSet.mpr h1⟩).1 hlt
        rw [hb1, hb2] at hboth
        exact Bool.noConfusion hboth
    · obtain ⟨c, hc⟩ := isEdgeColorable_iff_exists_isProperEdgeColoring.mp hG
      let g : ℕ → Bool := fun p ↦
        let uv := p / K
        let col := p % K
        let u := uv / G.n
        let v := uv % G.n
        if h : u < G.n ∧ v < G.n then
          if hadj : G.graph.Adj ⟨u, h.1⟩ ⟨v, h.2⟩ then
            decide ((c ⟨s(⟨u, h.1⟩, ⟨v, h.2⟩), G.graph.mem_edgeSet.mpr hadj⟩).1 = col)
          else false
        else false
      let uWord : List Bool := (List.range (G.n * G.n * K)).map g
      have hulen : uWord.length = G.n * G.n * K := by simp [uWord]
      have huget : ∀ {u v col : ℕ} (hu : u < G.n) (hv : v < G.n) (hcol : col < K),
          uWord.getD ((u * G.n + v) * K + col) false =
            if hadj : G.graph.Adj ⟨u, hu⟩ ⟨v, hv⟩ then
              decide ((c ⟨s(⟨u, hu⟩, ⟨v, hv⟩), G.graph.mem_edgeSet.mpr hadj⟩).1 = col)
            else false := by
        intro u v col hu hv hcol
        let idx := (u * G.n + v) * K + col
        have huv_lt : u * G.n + v < G.n * G.n := by
          calc u * G.n + v < u * G.n + G.n := Nat.add_lt_add_left hv _
            _ = (u + 1) * G.n := by rw [Nat.succ_mul]
            _ ≤ G.n * G.n := Nat.mul_le_mul_right G.n hu
        have hidx : idx < G.n * G.n * K := by
          calc (u * G.n + v) * K + col < (u * G.n + v) * K + K := Nat.add_lt_add_left hcol _
            _ = (u * G.n + v + 1) * K := by rw [Nat.succ_mul]
            _ ≤ G.n * G.n * K := Nat.mul_le_mul_right K huv_lt
        have hposK : 0 < K := Nat.succ_pos k'
        have hposG : 0 < G.n := Nat.lt_of_le_of_lt (Nat.zero_le _) hu
        have huv : idx / K = u * G.n + v := by
          dsimp only [idx]
          rw [Nat.mul_comm _ K, Nat.mul_add_div hposK, Nat.div_eq_of_lt hcol]; omega
        have hcol' : idx % K = col := by
          dsimp only [idx]; rw [Nat.mul_comm _ K, Nat.mul_add_mod, Nat.mod_eq_of_lt hcol]
        have hu' : (idx / K) / G.n = u := by
          rw [huv, Nat.mul_comm u G.n, Nat.mul_add_div hposG, Nat.div_eq_of_lt hv]; omega
        have hv' : (idx / K) % G.n = v := by
          rw [huv, Nat.mul_comm u G.n, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
        rw [List.getD_eq_getElem _ _ (hulen ▸ hidx), List.getElem_map, List.getElem_range]
        dsimp only [g]
        dsimp only [idx] at hu' hv' hcol'
        have hcond : ((u * G.n + v) * K + col) / K / G.n < G.n ∧
            ((u * G.n + v) * K + col) / K % G.n < G.n :=
          ⟨by rw [hu']; exact hu, by rw [hv']; exact hv⟩
        rw [dite_eq_left hcond]
        have hfin_u : (⟨((u * G.n + v) * K + col) / K / G.n, hcond.1⟩ : Fin G.n) = ⟨u, hu⟩ :=
          Fin.ext hu'
        have hfin_v : (⟨((u * G.n + v) * K + col) / K % G.n, hcond.2⟩ : Fin G.n) = ⟨v, hv⟩ :=
          Fin.ext hv'
        rw [hfin_u, hfin_v, hcol']
      have hcheck : edgeColoringVerifier K (G, uWord) = true := by
        simp only [edgeColoringVerifier, edgeColoringCheckAt, ugraphOrder_eq, Bool.and_eq_true,
          List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
          beq_iff_eq]
        refine ⟨fun u hu v hv ↦ ?_, fun u hu v1 hv1 v2 hv2 ↦ ?_⟩
        · by_cases hadj : G.graph.Adj ⟨u, hu⟩ ⟨v, hv⟩
          · right
            have hcol := (c ⟨s(⟨u, hu⟩, ⟨v, hv⟩), G.graph.mem_edgeSet.mpr hadj⟩).2
            refine ⟨⟨(c ⟨s(⟨u, hu⟩, ⟨v, hv⟩), G.graph.mem_edgeSet.mpr hadj⟩).1, hcol, ?_⟩,
              fun col hcol' ↦ ?_⟩
            · simp only [huget hu hv hcol, hadj, ↓reduceDIte, decide_true]
            · rw [huget hu hv hcol', huget hv hu hcol']
              simp only [hadj, hadj.symm, ↓reduceDIte]
              exact congrArg (fun e ↦ decide ((c e).1 = col)) (Subtype.ext Sym2.eq_swap)
          · left
            rw [Bool.eq_false_iff]
            intro htrue
            obtain ⟨_, _, hadj'⟩ := (ugraphAdjBool_eq_true_iff G u v).mp htrue
            exact hadj hadj'
        · by_cases hcond : (decide (v1 ≠ v2) && ugraphAdjBool G u v1 &&
              ugraphAdjBool G u v2) = true
          · right
            intro col hcol
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            obtain ⟨⟨hne, ht1⟩, ht2⟩ := hcond
            obtain ⟨_, _, hadj1⟩ := (ugraphAdjBool_eq_true_iff G u v1).mp ht1
            obtain ⟨_, _, hadj2⟩ := (ugraphAdjBool_eq_true_iff G u v2).mp ht2
            rw [huget hu hv1 hcol, huget hu hv2 hcol]
            simp only [hadj1, hadj2, ↓reduceDIte, Bool.and_eq_false_iff, decide_eq_false_iff_not]
            by_contra hboth
            push Not at hboth
            have hveq := hc ⟨u, hu⟩ ⟨v1, hv1⟩ ⟨v2, hv2⟩ hadj1 hadj2
              (Fin.ext (hboth.1.trans hboth.2.symm))
            exact hne (congrArg Fin.val hveq)
          · left
            exact Bool.eq_false_iff.mpr hcond
      refine ⟨uWord, ?_, fun m ↦ ?_⟩
      · simp only [hulen, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          encUGraph_apply, G.length_encode]
        nlinarith
      · have hpad : edgeColoringVerifier K (G, uWord ++ List.replicate m false) =
            edgeColoringVerifier K (G, uWord) :=
          congrArg (edgeColoringCheckAt K G)
            (funext fun idx ↦ getD_append_replicate_false uWord m idx)
        exact hpad.trans hcheck

/-- For every `k : ℕ`, `regularEdgeColoring k` belongs to `NP encUGraph`. -/
theorem regularEdgeColoring_mem_NP (k : ℕ) : regularEdgeColoring k ∈ NP encUGraph :=
  mem_NP_of_guard (computableInPolyTime_isNonemptyRegularBool k) (edgeColorableUGraph_mem_NP k)
    fun G ↦ by simp [regularEdgeColoring, edgeColorableUGraph, isNonemptyRegularBool_eq_true_iff]

/-- Pull back `NP` membership along a subtype embedding. -/
theorem subtype_mem_NP {α : Type} {enc : α ↪ List Bool} {Q : α → Prop} {A : Set α}
    (hA : A ∈ NP enc) :
    {x : {a : α // Q a} | x.1 ∈ A} ∈ NP ((Function.Embedding.subtype Q).trans enc) := by
  obtain ⟨p, V, hV, hVer⟩ := hA
  refine ⟨p, fun xw ↦ V (xw.1.1, xw.2), hV.comp (of_eq fun _ ↦ rfl), fun x ↦ ?_⟩
  exact hVer x.1

/-- For every `k : ℕ`, `restrictedRegularEdgeColoring k` belongs to `NP (encRegularUGraph k)`. -/
theorem restrictedRegularEdgeColoring_mem_NP (k : ℕ) :
    restrictedRegularEdgeColoring k ∈ NP (encRegularUGraph k) :=
  subtype_mem_NP (Q := IsNonemptyRegular k) (edgeColorableUGraph_mem_NP k)

end LanguagesAndNP

section TractableBaseCases

private lemma isEdgeColorable_zero_of_isNonemptyRegular {G : UGraphInstance}
    (hG : IsNonemptyRegular 0 G) : IsEdgeColorable G.graph 0 := by
  rw [isEdgeColorable_zero_iff]
  ext u v
  simp only [_root_.SimpleGraph.bot_adj, iff_false]
  intro hadj
  have hpos : 0 < G.graph.degree u := hadj.degree_pos_left
  have h0 := hG.2 u
  omega

private lemma isEdgeColorable_one_of_isNonemptyRegular {G : UGraphInstance}
    (hG : IsNonemptyRegular 1 G) : IsEdgeColorable G.graph 1 := by
  rw [isEdgeColorable_iff_exists_isProperEdgeColoring]
  refine ⟨fun _ ↦ 0, fun v w₁ w₂ h₁ h₂ _ ↦ ?_⟩
  by_contra hne
  have h2 : 2 ≤ G.graph.degree v := by
    rw [← G.graph.card_neighborFinset_eq_degree]
    exact Finset.one_lt_card.mpr ⟨w₁, (G.graph.mem_neighborFinset v w₁).mpr h₁,
      w₂, (G.graph.mem_neighborFinset v w₂).mpr h₂, hne⟩
  have h1 := hG.2 v
  omega

/-- **Base case `k = 0`**: `regularEdgeColoring 0 ∈ P encUGraph`. -/
theorem regularEdgeColoring_zero_mem_P : regularEdgeColoring 0 ∈ P encUGraph := by
  have heq : regularEdgeColoring 0 = {G : UGraphInstance | IsNonemptyRegular 0 G} :=
    Set.ext fun _ ↦ ⟨And.left, fun h ↦ ⟨h, isEdgeColorable_zero_of_isNonemptyRegular h⟩⟩
  exact heq ▸ isNonemptyRegular_mem_P 0

/-- **Base case `k = 0` (restricted)**: `restrictedRegularEdgeColoring 0 ∈ P (encRegularUGraph 0)`.
-/
theorem restrictedRegularEdgeColoring_zero_mem_P :
    restrictedRegularEdgeColoring 0 ∈ P (encRegularUGraph 0) :=
  (polyTimeReducible_restrictedRegularEdgeColoring 0).mem_P regularEdgeColoring_zero_mem_P

/-- **Base case `k = 1`**: `regularEdgeColoring 1 ∈ P encUGraph`. -/
theorem regularEdgeColoring_one_mem_P : regularEdgeColoring 1 ∈ P encUGraph := by
  have heq : regularEdgeColoring 1 = {G : UGraphInstance | IsNonemptyRegular 1 G} :=
    Set.ext fun _ ↦ ⟨And.left, fun h ↦ ⟨h, isEdgeColorable_one_of_isNonemptyRegular h⟩⟩
  exact heq ▸ isNonemptyRegular_mem_P 1

/-- **Base case `k = 1` (restricted)**: `restrictedRegularEdgeColoring 1 ∈ P (encRegularUGraph 1)`.
-/
theorem restrictedRegularEdgeColoring_one_mem_P :
    restrictedRegularEdgeColoring 1 ∈ P (encRegularUGraph 1) :=
  (polyTimeReducible_restrictedRegularEdgeColoring 1).mem_P regularEdgeColoring_one_mem_P

end TractableBaseCases

section ClassOneAndTwoFamilies

/-- Complete bipartite `k`-regular instance `K_{k,k}` on `k + k` vertices (`k ≥ 1`). -/
def completeBipartiteRegularUGraph (k : ℕ) (_hk : 1 ≤ k) : UGraphInstance where
  n := k + k
  adj a b := decide ((a.1 < k ∧ k ≤ b.1) ∨ (k ≤ a.1 ∧ b.1 < k))
  symm a b := by simp only [decide_eq_decide]; tauto
  loopless a := by simp only [decide_eq_false_iff_not]; omega

private lemma completeBipartiteRegularUGraph_adj (k : ℕ) (hk : 1 ≤ k)
    (a b : Fin (completeBipartiteRegularUGraph k hk).n) :
    (completeBipartiteRegularUGraph k hk).graph.Adj a b ↔
      (a.1 < k ∧ k ≤ b.1) ∨ (k ≤ a.1 ∧ b.1 < k) := by
  change decide ((a.1 < k ∧ k ≤ b.1) ∨ (k ≤ a.1 ∧ b.1 < k)) = true ↔ _
  rw [decide_eq_true_eq]

/-- For every `k ≥ 1`, `completeBipartiteRegularUGraph k hk` is nonempty and `k`-regular. -/
theorem completeBipartiteRegularUGraph_isNonemptyRegular (k : ℕ) (hk : 1 ≤ k) :
    IsNonemptyRegular k (completeBipartiteRegularUGraph k hk) := by
  have hn : (completeBipartiteRegularUGraph k hk).n = k + k := rfl
  refine ⟨by omega, fun u ↦ ?_⟩
  rw [← (completeBipartiteRegularUGraph k hk).graph.card_neighborFinset_eq_degree]
  by_cases hu : u.1 < k
  · let emb : Fin k ↪ Fin (completeBipartiteRegularUGraph k hk).n :=
      ⟨fun j ↦ ⟨k + j.1, by omega⟩, fun j₁ j₂ h ↦ by
        dsimp only at h
        exact Fin.ext (Nat.add_left_cancel (Fin.mk.inj h))⟩
    have hemb : ∀ j : Fin k, (emb j).1 = k + j.1 := fun _ ↦ rfl
    have hset : (completeBipartiteRegularUGraph k hk).graph.neighborFinset u =
        (Finset.univ : Finset (Fin k)).map emb := by
      ext v
      have hv := v.2
      rw [_root_.SimpleGraph.mem_neighborFinset, completeBipartiteRegularUGraph_adj]
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.ext_iff, hemb]
      refine ⟨fun h ↦ ?_, fun ⟨_, hj⟩ ↦ Or.inl ⟨hu, by omega⟩⟩
      rcases h with ⟨_, hkv⟩ | ⟨hku, _⟩
      · exact ⟨⟨v.1 - k, by omega⟩, Nat.add_sub_of_le hkv⟩
      · omega
    rw [hset, Finset.card_map, Finset.card_fin]
  · let emb : Fin k ↪ Fin (completeBipartiteRegularUGraph k hk).n :=
      ⟨fun j ↦ ⟨j.1, by omega⟩, fun j₁ j₂ h ↦ by
        dsimp only at h
        exact Fin.ext (Fin.mk.inj h)⟩
    have hemb : ∀ j : Fin k, (emb j).1 = j.1 := fun _ ↦ rfl
    have hset : (completeBipartiteRegularUGraph k hk).graph.neighborFinset u =
        (Finset.univ : Finset (Fin k)).map emb := by
      ext v
      rw [_root_.SimpleGraph.mem_neighborFinset, completeBipartiteRegularUGraph_adj]
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.ext_iff, hemb]
      refine ⟨fun h ↦ ?_, fun ⟨j, hj⟩ ↦ Or.inr ⟨by omega, by have := j.2; omega⟩⟩
      rcases h with ⟨huk, _⟩ | ⟨_, hvk⟩
      · exact (hu huk).elim
      · exact ⟨⟨v.1, hvk⟩, rfl⟩
    rw [hset, Finset.card_map, Finset.card_fin]

/-- For every `k ≥ 1`, `completeBipartiteRegularUGraph k hk` is Class 1 (`k`-edge-colorable) via
explicit cyclic modular edge coloring. -/
theorem completeBipartiteRegularUGraph_mem (k : ℕ) (hk : 1 ≤ k) :
    completeBipartiteRegularUGraph k hk ∈ regularEdgeColoring k := by
  refine ⟨completeBipartiteRegularUGraph_isNonemptyRegular k hk, ?_⟩
  rw [isEdgeColorable_iff_exists_isProperEdgeColoring]
  have hn : (completeBipartiteRegularUGraph k hk).n = k + k := rfl
  let G := (completeBipartiteRegularUGraph k hk).graph
  let col : G.edgeSet → Fin k := fun e ↦
    ⟨(Sym2.lift ⟨fun a b : Fin (completeBipartiteRegularUGraph k hk).n ↦ a.1 + b.1 - k,
        fun a b ↦ by dsimp only; rw [Nat.add_comm a.1 b.1]⟩ e.1) % k,
      Nat.mod_lt _ hk⟩
  refine ⟨col, fun v w₁ w₂ h₁ h₂ heq ↦ ?_⟩
  have hval : (v.1 + w₁.1 - k) % k = (v.1 + w₂.1 - k) % k := congrArg Fin.val heq
  rw [completeBipartiteRegularUGraph_adj] at h₁ h₂
  have hw₁ : w₁.1 < k + k := hn ▸ w₁.2
  have hw₂ : w₂.1 < k + k := hn ▸ w₂.2
  rcases h₁ with ⟨hv, hkw₁⟩ | ⟨hkv, hlw₁⟩
  · rcases h₂ with ⟨_, hkw₂⟩ | ⟨hkv', _⟩
    · have h1 : v.1 + w₁.1 - k = v.1 + (w₁.1 - k) := by omega
      have h2 : v.1 + w₂.1 - k = v.1 + (w₂.1 - k) := by omega
      rw [h1, h2] at hval
      have hj1 : w₁.1 - k < k := by omega
      have hj2 : w₂.1 - k < k := by omega
      have hdvd : k ∣ (v.1 + (w₁.1 - k)) - (v.1 + (w₂.1 - k)) ∧
          k ∣ (v.1 + (w₂.1 - k)) - (v.1 + (w₁.1 - k)) := by
        rcases le_total (w₁.1 - k) (w₂.1 - k) with hle | hle
        · exact ⟨⟨0, by omega⟩,
            Nat.modEq_iff_dvd' (Nat.add_le_add_left hle v.1) |>.mp hval⟩
        · exact ⟨Nat.modEq_iff_dvd' (Nat.add_le_add_left hle v.1) |>.mp hval.symm,
            ⟨0, by omega⟩⟩
      rcases hdvd with ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩
      have hq1_zero : q1 = 0 := by
        by_contra hne
        have hle1 : 1 * k ≤ q1 * k := Nat.mul_le_mul_right k (Nat.pos_of_ne_zero hne)
        rw [Nat.one_mul, Nat.mul_comm] at hle1
        omega
      have hq2_zero : q2 = 0 := by
        by_contra hne
        have hle2 : 1 * k ≤ q2 * k := Nat.mul_le_mul_right k (Nat.pos_of_ne_zero hne)
        rw [Nat.one_mul, Nat.mul_comm] at hle2
        omega
      subst hq1_zero hq2_zero
      exact Fin.ext (by omega)
    · omega
  · rcases h₂ with ⟨hv', _⟩ | ⟨_, hlw₂⟩
    · omega
    · have h1 : v.1 + w₁.1 - k = (v.1 - k) + w₁.1 := by omega
      have h2 : v.1 + w₂.1 - k = (v.1 - k) + w₂.1 := by omega
      rw [h1, h2] at hval
      have hdvd : k ∣ ((v.1 - k) + w₁.1) - ((v.1 - k) + w₂.1) ∧
          k ∣ ((v.1 - k) + w₂.1) - ((v.1 - k) + w₁.1) := by
        rcases le_total w₁.1 w₂.1 with hle | hle
        · exact ⟨⟨0, by omega⟩,
            Nat.modEq_iff_dvd' (Nat.add_le_add_left hle (v.1 - k)) |>.mp hval⟩
        · exact ⟨Nat.modEq_iff_dvd' (Nat.add_le_add_left hle (v.1 - k)) |>.mp hval.symm,
            ⟨0, by omega⟩⟩
      rcases hdvd with ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩
      have hq1_zero : q1 = 0 := by
        by_contra hne
        have hle1 : 1 * k ≤ q1 * k := Nat.mul_le_mul_right k (Nat.pos_of_ne_zero hne)
        rw [Nat.one_mul, Nat.mul_comm] at hle1
        omega
      have hq2_zero : q2 = 0 := by
        by_contra hne
        have hle2 : 1 * k ≤ q2 * k := Nat.mul_le_mul_right k (Nat.pos_of_ne_zero hne)
        rw [Nat.one_mul, Nat.mul_comm] at hle2
        omega
      subst hq1_zero hq2_zero
      exact Fin.ext (by omega)

private def oddDeletedPair (u v : ℕ) : Prop :=
  (u = 0 ∧ (v = 1 ∨ v = 2)) ∨ (v = 0 ∧ (u = 1 ∨ u = 2)) ∨
    (3 ≤ u ∧ 3 ≤ v ∧ ((u % 2 = 1 ∧ v = u + 1) ∨ (u % 2 = 0 ∧ u = v + 1)))

private instance instDecidableOddDeletedPair (u v : ℕ) : Decidable (oddDeletedPair u v) :=
  inferInstanceAs (Decidable ((u = 0 ∧ (v = 1 ∨ v = 2)) ∨ (v = 0 ∧ (u = 1 ∨ u = 2)) ∨
    (3 ≤ u ∧ 3 ≤ v ∧ ((u % 2 = 1 ∧ v = u + 1) ∨ (u % 2 = 0 ∧ u = v + 1)))))

private lemma oddDeletedPair_symm {u v : ℕ} (h : oddDeletedPair u v) : oddDeletedPair v u := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨hu, hv, hpair⟩
  · exact Or.inr (Or.inl ⟨rfl, h⟩)
  · exact Or.inl ⟨rfl, h⟩
  · refine Or.inr (Or.inr ⟨hv, hu, ?_⟩)
    rcases hpair with ⟨_, hvu⟩ | ⟨_, huv⟩
    · exact Or.inr ⟨by omega, hvu⟩
    · exact Or.inl ⟨by omega, huv⟩

private def oddBaseGraph (k : ℕ) : _root_.SimpleGraph (Fin (k + 2)) where
  Adj u v := u.1 ≠ v.1 ∧ ¬ oddDeletedPair u.1 v.1
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, fun hp ↦ h.2 (oddDeletedPair_symm hp)⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

private local instance instDecidableRelOddBaseGraphAdj (k : ℕ) :
    DecidableRel (oddBaseGraph k).Adj :=
  fun u v ↦ inferInstanceAs (Decidable (u.1 ≠ v.1 ∧ ¬ oddDeletedPair u.1 v.1))

private lemma oddBaseGraph_degree_zero {k : ℕ} (hk : 3 ≤ k) :
    (oddBaseGraph k).degree ⟨0, by omega⟩ = k - 1 := by
  rw [← (oddBaseGraph k).card_neighborFinset_eq_degree]
  let S : Finset (Fin (k + 2)) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hset : (oddBaseGraph k).neighborFinset ⟨0, by omega⟩ = Finset.univ \ S := by
    ext v
    rw [_root_.SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, S, Finset.mem_insert,
      Finset.mem_singleton, oddBaseGraph, oddDeletedPair, Fin.ext_iff]
    omega
  rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hS : S.card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_singleton]
  omega

private lemma oddBaseGraph_degree_pos {k : ℕ} (hk : 3 ≤ k) (hodd : Odd k)
    {u : Fin (k + 2)} (hu : u.1 ≠ 0) :
    (oddBaseGraph k).degree u = k := by
  rw [← (oddBaseGraph k).card_neighborFinset_eq_degree]
  have hodd_nat : k % 2 = 1 := Nat.odd_iff.mp hodd
  rcases Nat.lt_trichotomy u.1 2 with hlt2 | heq2 | hgt2
  · have hu1 : u.1 = 1 := by omega
    let S : Finset (Fin (k + 2)) := {u, ⟨0, by omega⟩}
    have hset : (oddBaseGraph k).neighborFinset u = Finset.univ \ S := by
      ext v
      rw [_root_.SimpleGraph.mem_neighborFinset]
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, S, Finset.mem_insert,
        Finset.mem_singleton, oddBaseGraph, oddDeletedPair, Fin.ext_iff]
      omega
    have hS : S.card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff, hu1]), Finset.card_singleton]
    rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hS]
    omega
  · let S : Finset (Fin (k + 2)) := {u, ⟨0, by omega⟩}
    have hset : (oddBaseGraph k).neighborFinset u = Finset.univ \ S := by
      ext v
      rw [_root_.SimpleGraph.mem_neighborFinset]
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, S, Finset.mem_insert,
        Finset.mem_singleton, oddBaseGraph, oddDeletedPair, Fin.ext_iff]
      omega
    have hS : S.card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff, heq2]), Finset.card_singleton]
    rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hS]
    omega
  · by_cases huodd : u.1 % 2 = 1
    · let S : Finset (Fin (k + 2)) := {u, ⟨u.1 + 1, by omega⟩}
      have hset : (oddBaseGraph k).neighborFinset u = Finset.univ \ S := by
        ext v
        rw [_root_.SimpleGraph.mem_neighborFinset]
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, S, Finset.mem_insert,
          Finset.mem_singleton, oddBaseGraph, oddDeletedPair, Fin.ext_iff]
        omega
      have hS : S.card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_singleton]
      rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, hS]
      omega
    · let S : Finset (Fin (k + 2)) := {u, ⟨u.1 - 1, by omega⟩}
      have hset : (oddBaseGraph k).neighborFinset u = Finset.univ \ S := by
        ext v
        rw [_root_.SimpleGraph.mem_neighborFinset]
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, S, Finset.mem_insert,
          Finset.mem_singleton, oddBaseGraph, oddDeletedPair, Fin.ext_iff]
        omega
      have hS : S.card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega), Finset.card_singleton]
      rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, hS]
      omega

private lemma oddBaseGraph_card_edgeFinset_gt {k : ℕ} (hk : 3 ≤ k) (hodd : Odd k) :
    k * ((k + 2) / 2) < (oddBaseGraph k).edgeFinset.card := by
  have hsum : 2 * (oddBaseGraph k).edgeFinset.card = (k - 1) + (k + 1) * k := by
    rw [← (oddBaseGraph k).sum_degrees_eq_twice_card_edges]
    let z : Fin (k + 2) := ⟨0, by omega⟩
    rw [← Finset.add_sum_erase Finset.univ (fun u ↦ (oddBaseGraph k).degree u) (Finset.mem_univ z),
      oddBaseGraph_degree_zero hk]
    have hconst : ∑ u ∈ Finset.univ.erase z, (oddBaseGraph k).degree u =
        ∑ _ ∈ Finset.univ.erase z, k :=
      Finset.sum_congr rfl fun u hu ↦
        oddBaseGraph_degree_pos hk hodd (fun h0 ↦ (Finset.mem_erase.mp hu).1 (Fin.ext h0))
    rw [hconst, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ z),
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, show k + 2 - 1 = k + 1 by omega]
  have hdiv : 2 * ((k + 2) / 2) = k + 1 := by
    have := Nat.odd_iff.mp hodd
    omega
  by_contra hle
  have hle2 : 2 * (oddBaseGraph k).edgeFinset.card ≤ 2 * (k * ((k + 2) / 2)) :=
    Nat.mul_le_mul_left 2 (not_lt.mp hle)
  have hmul : 2 * (k * ((k + 2) / 2)) = (k + 1) * k := by
    calc 2 * (k * ((k + 2) / 2)) = k * (2 * ((k + 2) / 2)) := by ring
      _ = k * (k + 1) := by rw [hdiv]
      _ = (k + 1) * k := Nat.mul_comm _ _
  omega

private def oddSumGraph (k : ℕ) : _root_.SimpleGraph (Fin (k + 2) ⊕ Fin (k + 2)) where
  Adj x y := match x, y with
    | .inl u, .inl v => (oddBaseGraph k).Adj u v
    | .inr u, .inr v => (oddBaseGraph k).Adj u v
    | .inl u, .inr v => u.1 = 0 ∧ v.1 = 0
    | .inr u, .inl v => u.1 = 0 ∧ v.1 = 0
  symm := ⟨fun x y h ↦ by
    cases x <;> cases y <;> simp only at h ⊢
    exacts [h.symm, ⟨h.2, h.1⟩, ⟨h.2, h.1⟩, h.symm]⟩
  loopless := ⟨fun x h ↦ by cases x <;> exact (oddBaseGraph k).loopless.irrefl _ h⟩

private local instance instDecidableRelOddSumGraphAdj (k : ℕ) :
    DecidableRel (oddSumGraph k).Adj
  | .inl u, .inl v => inferInstanceAs (Decidable ((oddBaseGraph k).Adj u v))
  | .inr u, .inr v => inferInstanceAs (Decidable ((oddBaseGraph k).Adj u v))
  | .inl u, .inr v => inferInstanceAs (Decidable (u.1 = 0 ∧ v.1 = 0))
  | .inr u, .inl v => inferInstanceAs (Decidable (u.1 = 0 ∧ v.1 = 0))

private lemma oddSumGraph_isRegular {k : ℕ} (hk : 3 ≤ k) (hodd : Odd k) :
    (oddSumGraph k).IsRegularOfDegree k := by
  intro x
  rw [← (oddSumGraph k).card_neighborFinset_eq_degree]
  rcases x with u | u
  · by_cases hu : u.1 = 0
    · have hu0 : u = ⟨0, by omega⟩ := Fin.ext hu
      let zR : Fin (k + 2) ⊕ Fin (k + 2) := .inr ⟨0, by omega⟩
      let S₁ : Finset (Fin (k + 2) ⊕ Fin (k + 2)) :=
        ((oddBaseGraph k).neighborFinset u).map ⟨Sum.inl, Sum.inl_injective⟩
      have hset : (oddSumGraph k).neighborFinset (.inl u) = insert zR S₁ := by
        ext y
        rw [_root_.SimpleGraph.mem_neighborFinset]
        rcases y with v | v
        · simp [S₁, zR, oddSumGraph]
        · constructor
          · intro hv
            dsimp only [oddSumGraph] at hv
            exact Finset.mem_insert.mpr (Or.inl (congrArg Sum.inr (Fin.ext hv.2)))
          · intro hy
            rcases Finset.mem_insert.mp hy with heq | hmap
            · exact ⟨hu, congrArg Fin.val (Sum.inr.inj heq)⟩
            · obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hmap
              exact nomatch ha
      rw [hset, Finset.card_insert_of_notMem (by simp [zR, S₁]), Finset.card_map,
        _root_.SimpleGraph.card_neighborFinset_eq_degree, hu0, oddBaseGraph_degree_zero hk]
      omega
    · let S₁ : Finset (Fin (k + 2) ⊕ Fin (k + 2)) :=
        ((oddBaseGraph k).neighborFinset u).map ⟨Sum.inl, Sum.inl_injective⟩
      have hset : (oddSumGraph k).neighborFinset (.inl u) = S₁ := by
        ext y
        rw [_root_.SimpleGraph.mem_neighborFinset]
        rcases y with v | v
        · simp [S₁, oddSumGraph]
        · simp only [S₁, oddSumGraph, Finset.mem_map, Function.Embedding.coeFn_mk, reduceCtorEq]
          exact ⟨fun ⟨h, _⟩ ↦ absurd h hu, fun ⟨_, _, h⟩ ↦ h.elim⟩
      rw [hset, Finset.card_map, _root_.SimpleGraph.card_neighborFinset_eq_degree,
        oddBaseGraph_degree_pos hk hodd hu]
  · by_cases hu : u.1 = 0
    · have hu0 : u = ⟨0, by omega⟩ := Fin.ext hu
      let zL : Fin (k + 2) ⊕ Fin (k + 2) := .inl ⟨0, by omega⟩
      let S₁ : Finset (Fin (k + 2) ⊕ Fin (k + 2)) :=
        ((oddBaseGraph k).neighborFinset u).map ⟨Sum.inr, Sum.inr_injective⟩
      have hset : (oddSumGraph k).neighborFinset (.inr u) = insert zL S₁ := by
        ext y
        rw [_root_.SimpleGraph.mem_neighborFinset]
        rcases y with v | v
        · constructor
          · intro hv
            dsimp only [oddSumGraph] at hv
            exact Finset.mem_insert.mpr (Or.inl (congrArg Sum.inl (Fin.ext hv.2)))
          · intro hy
            rcases Finset.mem_insert.mp hy with heq | hmap
            · exact ⟨hu, congrArg Fin.val (Sum.inl.inj heq)⟩
            · obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hmap
              exact nomatch ha
        · simp [S₁, zL, oddSumGraph]
      rw [hset, Finset.card_insert_of_notMem (by simp [zL, S₁]), Finset.card_map,
        _root_.SimpleGraph.card_neighborFinset_eq_degree, hu0, oddBaseGraph_degree_zero hk]
      omega
    · let S₁ : Finset (Fin (k + 2) ⊕ Fin (k + 2)) :=
        ((oddBaseGraph k).neighborFinset u).map ⟨Sum.inr, Sum.inr_injective⟩
      have hset : (oddSumGraph k).neighborFinset (.inr u) = S₁ := by
        ext y
        rw [_root_.SimpleGraph.mem_neighborFinset]
        rcases y with v | v
        · simp only [S₁, oddSumGraph, Finset.mem_map, Function.Embedding.coeFn_mk, reduceCtorEq]
          exact ⟨fun ⟨h, _⟩ ↦ absurd h hu, fun ⟨_, _, h⟩ ↦ h.elim⟩
        · simp [S₁, oddSumGraph]
      rw [hset, Finset.card_map, _root_.SimpleGraph.card_neighborFinset_eq_degree,
        oddBaseGraph_degree_pos hk hodd hu]

private def oddSumEquiv (k : ℕ) : Fin (k + 2) ⊕ Fin (k + 2) ≃ Fin (2 * (k + 2)) :=
  finSumFinEquiv.trans (finCongr (by omega))

private def oddClassTwoUGraph (k : ℕ) : UGraphInstance where
  n := 2 * (k + 2)
  adj a b := decide ((oddSumGraph k).Adj ((oddSumEquiv k).symm a) ((oddSumEquiv k).symm b))
  symm a b := by
    simp only [decide_eq_decide]
    exact (oddSumGraph k).adj_comm _ _
  loopless a := by
    simp only [decide_eq_false_iff_not]
    exact (oddSumGraph k).loopless.irrefl _

private def evenClassTwoUGraph (k : ℕ) : UGraphInstance where
  n := k + 1
  adj a b := decide (a ≠ b)
  symm a b := by simp [ne_comm]
  loopless a := by simp

/-- Explicit Class 2 nonempty `k`-regular `UGraphInstance` for every `k ≥ 3`. -/
def classTwoRegularUGraph (k : ℕ) (_hk : 3 ≤ k) : UGraphInstance :=
  if k % 2 = 0 then evenClassTwoUGraph k else oddClassTwoUGraph k

private lemma isRegularOfDegree_congr {V W : Type*} [Fintype V] [Fintype W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) {k : ℕ} (h : G.IsRegularOfDegree k) : H.IsRegularOfDegree k := fun w ↦ by
  rw [← H.card_neighborFinset_eq_degree]
  let bij : G.neighborFinset (e.symm w) ≃ H.neighborFinset w :=
    { toFun := fun ⟨v, hv⟩ ↦ ⟨e v, by
        rw [_root_.SimpleGraph.mem_neighborFinset] at hv ⊢
        simpa using e.map_rel_iff.mpr hv⟩
      invFun := fun ⟨u, hu⟩ ↦ ⟨e.symm u, by
        rw [_root_.SimpleGraph.mem_neighborFinset] at hu ⊢
        exact e.symm.map_rel_iff.mpr hu⟩
      left_inv := fun ⟨v, _⟩ ↦ Subtype.ext (e.symm_apply_apply v)
      right_inv := fun ⟨u, _⟩ ↦ Subtype.ext (e.apply_symm_apply u) }
  rw [← Fintype.card_coe (H.neighborFinset w), ← Fintype.card_congr bij,
    Fintype.card_coe, G.card_neighborFinset_eq_degree, h (e.symm w)]

private lemma evenClassTwoUGraph_adj (k : ℕ) (a b : Fin (evenClassTwoUGraph k).n) :
    (evenClassTwoUGraph k).graph.Adj a b ↔ a ≠ b := by
  change decide (a ≠ b) = true ↔ a ≠ b
  rw [decide_eq_true_eq]

/-- For every `k ≥ 3`, `classTwoRegularUGraph k hk` is nonempty and `k`-regular. -/
theorem classTwoRegularUGraph_isNonemptyRegular (k : ℕ) (hk : 3 ≤ k) :
    IsNonemptyRegular k (classTwoRegularUGraph k hk) := by
  by_cases hm : k % 2 = 0
  · rw [classTwoRegularUGraph, ite_eq_left hm]
    have hn : (evenClassTwoUGraph k).n = k + 1 := rfl
    refine ⟨by omega, fun u ↦ ?_⟩
    rw [← (evenClassTwoUGraph k).graph.card_neighborFinset_eq_degree]
    have hset : (evenClassTwoUGraph k).graph.neighborFinset u = Finset.univ.erase u := by
      ext v
      rw [_root_.SimpleGraph.mem_neighborFinset, evenClassTwoUGraph_adj, Finset.mem_erase]
      exact ⟨fun h ↦ ⟨h.symm, Finset.mem_univ v⟩, fun h ↦ h.1.symm⟩
    rw [hset, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin, hn]
    omega
  · rw [classTwoRegularUGraph, ite_eq_right hm]
    have hn : (oddClassTwoUGraph k).n = 2 * (k + 2) := rfl
    have hodd : Odd k := Nat.odd_iff.mpr (by omega)
    refine ⟨by omega, ?_⟩
    let e : oddSumGraph k ≃g (oddClassTwoUGraph k).graph :=
      { toEquiv := oddSumEquiv k
        map_rel_iff' := fun {a b} ↦ by
          change decide ((oddSumGraph k).Adj ((oddSumEquiv k).symm (oddSumEquiv k a))
            ((oddSumEquiv k).symm (oddSumEquiv k b))) = true ↔ (oddSumGraph k).Adj a b
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, decide_eq_true_eq] }
    exact isRegularOfDegree_congr e (oddSumGraph_isRegular hk hodd)

/-- For every `k ≥ 3`, `classTwoRegularUGraph k hk` is not `k`-edge-colorable. -/
theorem classTwoRegularUGraph_notMem (k : ℕ) (hk : 3 ≤ k) :
    classTwoRegularUGraph k hk ∉ regularEdgeColoring k := by
  by_cases hm : k % 2 = 0
  · rw [classTwoRegularUGraph, ite_eq_left hm]
    rintro ⟨hreg, hcol⟩
    have heven := even_card_of_isRegularOfDegree_of_isEdgeColorable hreg.2 (by omega) hcol
    rw [Fintype.card_fin] at heven
    have hmod := Nat.even_iff.mp heven
    dsimp [evenClassTwoUGraph] at hmod
    omega
  · rw [classTwoRegularUGraph, ite_eq_right hm]
    rintro ⟨_, hcol⟩
    have hodd : Odd k := Nat.odd_iff.mpr (by omega)
    obtain ⟨c, hc⟩ := isEdgeColorable_iff_exists_isProperEdgeColoring.mp hcol
    let emb : oddBaseGraph k →g (oddClassTwoUGraph k).graph :=
      { toFun := fun u ↦ oddSumEquiv k (.inl u)
        map_rel' := fun {u v} huv ↦ by
          simp only [UGraphInstance.graph_adj, oddClassTwoUGraph, Equiv.symm_apply_apply,
            decide_eq_true_eq]
          exact huv }
    have hcbase := hc.pullback_of_injective emb
      ((oddSumEquiv k).injective.comp Sum.inl_injective)
    have hle := hcbase.card_edgeFinset_le
    rw [Fintype.card_fin, Fintype.card_fin] at hle
    exact (not_le_of_gt (oddBaseGraph_card_edgeFinset_gt hk hodd)) hle

/-- For every `k ≥ 3`, `regularEdgeColoring k` contains both a Class 1 instance and a Class 2
non-member. -/
theorem exists_mem_and_notMem_regularEdgeColoring (k : ℕ) (hk : 3 ≤ k) :
    ∃ G₁ G₂ : UGraphInstance,
      G₁ ∈ regularEdgeColoring k ∧ G₂ ∉ regularEdgeColoring k :=
  ⟨completeBipartiteRegularUGraph k (by omega), classTwoRegularUGraph k hk,
    completeBipartiteRegularUGraph_mem k (by omega), classTwoRegularUGraph_notMem k hk⟩

/-- For every `k ≥ 3`, `restrictedRegularEdgeColoring k` contains both a Class 1 yes-instance and a
Class 2 no-instance inside `{G : UGraphInstance // IsNonemptyRegular k G}`. -/
theorem exists_mem_and_notMem_restrictedRegularEdgeColoring (k : ℕ) (hk : 3 ≤ k) :
    ∃ x₁ x₂ : {G : UGraphInstance // IsNonemptyRegular k G},
      x₁ ∈ restrictedRegularEdgeColoring k ∧ x₂ ∉ restrictedRegularEdgeColoring k :=
  ⟨⟨completeBipartiteRegularUGraph k (by omega),
      completeBipartiteRegularUGraph_isNonemptyRegular k (by omega)⟩,
    ⟨classTwoRegularUGraph k hk, classTwoRegularUGraph_isNonemptyRegular k hk⟩,
    mem_restrictedRegularEdgeColoring_iff_mem.mpr
      (completeBipartiteRegularUGraph_mem k (by omega)),
    fun h ↦ classTwoRegularUGraph_notMem k hk (mem_restrictedRegularEdgeColoring_iff_mem.mp h)⟩

end ClassOneAndTwoFamilies

end CslibFrontier.Complexity
