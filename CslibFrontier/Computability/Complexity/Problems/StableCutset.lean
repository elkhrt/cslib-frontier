/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Closure
public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Reduction
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stable Cutsets and Minimum-Degree-Constrained Stable Cutsets

This module formalizes the **Stable Cutset** decision problem (`StableCutset`) and its minimum
degree restriction (`StableCutsetMinDeg c`) on binary-encoded graphs (`Cslib.Complexity.Graph`,
`Cslib.Complexity.encGraph`) over multi-tape Turing machines:

* `IsCutset`, `IsStableCutset`, `HasStableCutset`: cutsets and stable (independent) vertex cutsets
  of a simple graph, together with isomorphism invariance (`hasStableCutset_iff_of_iso`).
* `StableCutset`, `StableCutsetMinDeg c`: encoded graph languages on `Cslib.Complexity.Graph`.
* `polyTimeReducible_StableCutset_ThreeSAT`, `StableCutset_mem_NP`, `StableCutsetMinDeg_mem_NP`:
  polynomial-time many-one reduction to `ThreeSAT` and `NP` membership.
* `attachEdgeCliques`, `hasStableCutset_attachEdgeCliques_iff`,
  `polyTimeReducible_StableCutset_StableCutsetMinDeg`: edge-clique attachment construction showing
  `StableCutset ≤_p StableCutsetMinDeg c` for every constant `c > 1`.
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ## Vertex Cutsets and Stable Cutsets on `SimpleGraph` -/

/-- `S : Set V` is a vertex cutset of `G` if `V \ S` partitions into two nonempty disjoint sets `A`
and `B` with no edge of `G` between `A` and `B`. -/
def IsCutset {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ A B : Set V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ Sᶜ = A ∪ B ∧
    ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

/-- `S : Set V` is a stable cutset of `G` if `S` is both an independent set and a vertex cutset. -/
def IsStableCutset {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  G.IsIndepSet S ∧ IsCutset G S

/-- `G` admits a stable cutset if some `S : Set V` is a stable cutset of `G`. -/
def HasStableCutset {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ S : Set V, IsStableCutset G S

theorem not_hasStableCutset_of_subsingleton {V : Type*} [Subsingleton V] (G : SimpleGraph V) :
    ¬ HasStableCutset G := by
  rintro ⟨S, _, A, B, ⟨a, ha⟩, ⟨b, hb⟩, hdisj, _, _⟩
  exact Set.disjoint_left.mp hdisj ha (Subsingleton.elim b a ▸ hb)

private theorem hasStableCutset_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : HasStableCutset G → HasStableCutset H := by
  rintro ⟨S, hS_indep, A, B, ⟨a, ha⟩, ⟨b, hb⟩, hdisj, hunion, hno⟩
  refine ⟨f '' S, ?_, f '' A, f '' B, ⟨f a, a, ha, rfl⟩, ⟨f b, b, hb, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hne hadj
    exact hS_indep hu hv (fun h ↦ hne (congrArg f h)) (f.map_rel_iff.mp hadj)
  · rw [Set.disjoint_left]
    rintro _ ⟨u, huA, rfl⟩ ⟨v, hvB, heq⟩
    exact Set.disjoint_left.mp hdisj huA (f.injective heq ▸ hvB)
  · ext w
    obtain ⟨u, rfl⟩ := f.surjective w
    have hu := Set.ext_iff.mp hunion u
    simp only [Set.mem_compl_iff, Set.mem_image, f.injective.eq_iff, exists_eq_right,
      Set.mem_union] at hu ⊢
    exact hu
  · rintro _ ⟨u, huA, rfl⟩ _ ⟨v, hvB, rfl⟩ hadj
    exact hno u huA v hvB (f.map_rel_iff.mp hadj)

theorem hasStableCutset_iff_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : HasStableCutset G ↔ HasStableCutset H :=
  ⟨hasStableCutset_of_iso e, hasStableCutset_of_iso e.symm⟩

/-! ## Encoded Graph Languages and `NP` Membership -/

/-- The **Stable Cutset** decision problem on binary-encoded graphs `Cslib.Complexity.Graph`. -/
def StableCutset : Set Graph :=
  {G | HasStableCutset G.induced}

@[simp]
theorem mem_StableCutset_iff (G : Graph) :
    G ∈ StableCutset ↔ HasStableCutset G.induced := Iff.rfl

/-- The **Minimum-Degree-Constrained Stable Cutset** decision problem (`δ(G) ≥ c`). -/
def StableCutsetMinDeg (c : ℕ) : Set Graph :=
  {G | c ≤ G.induced.minDegree ∧ G ∈ StableCutset}

@[simp]
theorem mem_StableCutsetMinDeg_iff (c : ℕ) (G : Graph) :
    G ∈ StableCutsetMinDeg c ↔ c ≤ G.induced.minDegree ∧ G ∈ StableCutset := Iff.rfl

private inductive Label3 : Type
  | A | B | S
  deriving DecidableEq

private def Label3.compat : Label3 → Label3 → Bool
  | .A, .B => false
  | .B, .A => false
  | .S, .S => false
  | _, _ => true

private def scsVar (tag i : ℕ) : ℕ := 5 * i + tag

private theorem computableInPolyTime_scsVar (tag : ℕ) {γ : Type} {enc : γ ↪ List Bool}
    {i : γ → ℕ} (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x ↦ scsVar tag (i x)) enc encNat := by
  unfold scsVar
  exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

attribute [local fun_prop] computableInPolyTime_scsVar

private def scsVertexClauses (i : ℕ) : CNF ℕ :=
  [[(scsVar 0 i, true), (scsVar 1 i, true), (scsVar 2 i, true)],
   [(scsVar 0 i, false), (scsVar 1 i, false)],
   [(scsVar 0 i, false), (scsVar 2 i, false)],
   [(scsVar 1 i, false), (scsVar 2 i, false)],
   [(scsVar 3 (i + 1), false), (scsVar 3 i, true), (scsVar 0 i, true)],
   [(scsVar 4 (i + 1), false), (scsVar 4 i, true), (scsVar 1 i, true)]]

private def scsPairClauses (G : Graph) (ui wj : ℕ × ℕ) : CNF ℕ :=
  if G.adjBool ui.1 wj.1 then
    [[(scsVar 0 ui.2, false), (scsVar 1 wj.2, false)],
     [(scsVar 1 ui.2, false), (scsVar 0 wj.2, false)],
     [(scsVar 2 ui.2, false), (scsVar 2 wj.2, false)]]
  else []

/-- Polynomial-time 3-CNF encoding of `StableCutset`. -/
def graphSCSToThreeSAT (G : Graph) : CNF ℕ :=
  let n := G.distinctVertices.length
  let V := G.distinctVertices.zipIdx
  [[(scsVar 3 0, false)], [(scsVar 3 n, true)],
   [(scsVar 4 0, false)], [(scsVar 4 n, true)]] ++
    (V.flatMap fun ui ↦ scsVertexClauses ui.2) ++
    (V.flatMap fun ui ↦ V.flatMap fun wj ↦ scsPairClauses G ui wj)

theorem computableInPolyTime_graphSCSToThreeSAT :
    ComputableInPolyTime graphSCSToThreeSAT encGraph encCNF := by
  have hn : ComputableInPolyTime (fun G : Graph ↦ G.distinctVertices.length) encGraph encUnary :=
    (ComputableInPolyTime.length_list encNat).comp Graph.computableInPolyTime_distinctVertices
  have hV : ComputableInPolyTime (fun G : Graph ↦ G.distinctVertices.zipIdx)
      encGraph (encList (encPair encNat encUnary)) := by
    have hzip : ComputableInPolyTime (List.zipIdx (α := ℕ))
        (encList encNat) (encList (encPair encNat encUnary)) := by fun_prop
    exact hzip.comp Graph.computableInPolyTime_distinctVertices
  have hvtx : ComputableInPolyTime
      (fun p : Graph × (ℕ × ℕ) ↦ scsVertexClauses p.2.2)
      (encPair encGraph (encPair encNat encUnary)) encCNF := by
    unfold scsVertexClauses encCNF; fun_prop
  have hpair : ComputableInPolyTime
      (fun p : (Graph × (ℕ × ℕ)) × (ℕ × ℕ) ↦ scsPairClauses p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph (encPair encNat encUnary)) (encPair encNat encUnary)) encCNF := by
    unfold scsPairClauses encCNF; fun_prop
  have hhead : ComputableInPolyTime
      (fun G : Graph ↦
        ([[ (scsVar 3 0, false) ], [ (scsVar 3 G.distinctVertices.length, true) ],
          [ (scsVar 4 0, false) ], [ (scsVar 4 G.distinctVertices.length, true) ]] : CNF ℕ))
      encGraph encCNF := by
    unfold encCNF; fun_prop
  have inner : ComputableInPolyTime
      (fun p : Graph × (ℕ × ℕ) ↦
        p.1.distinctVertices.zipIdx.flatMap fun wj ↦ scsPairClauses p.1 p.2 wj)
      (encPair encGraph (encPair encNat encUnary)) encCNF :=
    ComputableInPolyTime.flatMapWithInput (hV.comp (ComputableInPolyTime.fst _ _)) hpair
  unfold graphSCSToThreeSAT
  exact ComputableInPolyTime.listAppend'
    (ComputableInPolyTime.listAppend' hhead (ComputableInPolyTime.flatMapWithInput hV hvtx))
    (ComputableInPolyTime.flatMapWithInput hV inner)

private theorem list_getD_eq_getElem {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem computableInPolyTime_unary_add_comp {γ : Type} {enc : γ ↪ List Bool}
    {f g : γ → ℕ} (hf : ComputableInPolyTime f enc encUnary)
    (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun x ↦ f x + g x) enc encUnary :=
  ComputableInPolyTime.unary_add.comp (hf.prod hg)

private theorem computableInPolyTime_unary_mul_comp {γ : Type} {enc : γ ↪ List Bool}
    {f g : γ → ℕ} (hf : ComputableInPolyTime f enc encUnary)
    (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun x ↦ f x * g x) enc encUnary :=
  ComputableInPolyTime.unary_mul.comp (hf.prod hg)

attribute [local fun_prop]
  computableInPolyTime_unary_add_comp computableInPolyTime_unary_mul_comp

/-- `StableCutset` reduces in polynomial time to `ThreeSAT`. -/
theorem polyTimeReducible_StableCutset_ThreeSAT :
    PolyTimeReducible encGraph encCNF StableCutset ThreeSAT := by
  refine ⟨graphSCSToThreeSAT, computableInPolyTime_graphSCSToThreeSAT, fun G ↦ ?_⟩
  change HasStableCutset G.induced ↔
    (∀ c ∈ graphSCSToThreeSAT G, c.length ≤ 3) ∧ (graphSCSToThreeSAT G).Satisfiable
  have hwidth : ∀ c ∈ graphSCSToThreeSAT G, c.length ≤ 3 := by
    intro c hc
    simp only [graphSCSToThreeSAT, List.mem_append, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | ⟨ui, _, hc⟩) | ⟨ui, _, wj, _, hc⟩
    · simp
    · simp
    · simp
    · simp
    · simp only [scsVertexClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · unfold scsPairClauses at hc
      split_ifs at hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp
      · simp at hc
  rw [and_iff_right hwidth]
  let n := G.distinctVertices.length
  let eqv := G.vertexEquiv
  constructor
  · rintro ⟨S, hSindep, A, B, ⟨a, ha⟩, ⟨b, hb⟩, hdisj, hunion, hno⟩
    classical
    let ℓ : {v // v ∈ G.vertices} → Label3 :=
      fun v ↦ if v ∈ S then .S else if v ∈ A then .A else .B
    have haS : a ∉ S := by rw [← Set.mem_compl_iff, hunion]; exact Or.inl ha
    have hbS : b ∉ S := by rw [← Set.mem_compl_iff, hunion]; exact Or.inr hb
    have hbA : b ∉ A := fun h ↦ Set.disjoint_left.mp hdisj h hb
    have hcomp : ∀ {u w : {v // v ∈ G.vertices}}, G.induced.Adj u w →
        (ℓ u).compat (ℓ w) = true := by
      intro u w hadj
      by_cases huS : u ∈ S <;> by_cases hwS : w ∈ S
      · exact (hSindep huS hwS (G.induced.ne_of_adj hadj) hadj).elim
      · simp only [ℓ, huS, hwS, ↓reduceIte]; split_ifs <;> rfl
      · simp only [ℓ, huS, hwS, ↓reduceIte]; split_ifs <;> rfl
      · have huAB : u ∈ A ∪ B := by rw [← hunion, Set.mem_compl_iff]; exact huS
        have hwAB : w ∈ A ∪ B := by rw [← hunion, Set.mem_compl_iff]; exact hwS
        by_cases huA : u ∈ A <;> by_cases hwA : w ∈ A
        · simp [ℓ, huS, hwS, huA, hwA, Label3.compat]
        · exact (hno u huA w (hwAB.resolve_left hwA) hadj).elim
        · exact (hno w hwA u (huAB.resolve_left huA) hadj.symm).elim
        · simp [ℓ, huS, hwS, huA, hwA, Label3.compat]
    let iA : Fin n := eqv.symm a
    let iB : Fin n := eqv.symm b
    let labelAt (i : ℕ) : Label3 := if hi : i < n then ℓ (eqv ⟨i, hi⟩) else .S
    let σ (x : ℕ) : Bool :=
      match x % 5, x / 5 with
      | 0, i => decide (labelAt i = .A)
      | 1, i => decide (labelAt i = .B)
      | 2, i => decide (labelAt i = .S)
      | 3, i => decide (iA.1 < i)
      | _, i => decide (iB.1 < i)
    have hσ0 (i : ℕ) : σ (scsVar 0 i) = decide (labelAt i = .A) := by
      dsimp only [σ, scsVar]
      rw [show (5 * i + 0) % 5 = 0 by omega, show (5 * i + 0) / 5 = i by omega]; rfl
    have hσ1 (i : ℕ) : σ (scsVar 1 i) = decide (labelAt i = .B) := by
      dsimp only [σ, scsVar]
      rw [show (5 * i + 1) % 5 = 1 by omega, show (5 * i + 1) / 5 = i by omega]; rfl
    have hσ2 (i : ℕ) : σ (scsVar 2 i) = decide (labelAt i = .S) := by
      dsimp only [σ, scsVar]
      rw [show (5 * i + 2) % 5 = 2 by omega, show (5 * i + 2) / 5 = i by omega]; rfl
    have hσ3 (i : ℕ) : σ (scsVar 3 i) = decide (iA.1 < i) := by
      dsimp only [σ, scsVar]
      rw [show (5 * i + 3) % 5 = 3 by omega, show (5 * i + 3) / 5 = i by omega]; rfl
    have hσ4 (i : ℕ) : σ (scsVar 4 i) = decide (iB.1 < i) := by
      dsimp only [σ, scsVar]
      rw [show (5 * i + 4) % 5 = 4 by omega, show (5 * i + 4) / 5 = i by omega]; rfl
    refine ⟨σ, (CNF.eval_eq_true_iff _ _).mpr fun c hc ↦ ?_⟩
    simp only [graphSCSToThreeSAT, List.mem_append, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | ⟨⟨u, i⟩, hui, hc⟩) |
      ⟨⟨u, i⟩, hui, ⟨w, j⟩, hwj, hc⟩
    · simp [Clause.eval, Literal.eval, hσ3]
    · simp only [Clause.eval_cons, Literal.eval_mk, beq_true, Clause.eval_nil, Bool.or_false,
        hσ3, decide_eq_true_eq]
      exact iA.2
    · simp [Clause.eval, Literal.eval, hσ4]
    · simp only [Clause.eval_cons, Literal.eval_mk, beq_true, Clause.eval_nil, Bool.or_false,
        hσ4, decide_eq_true_eq]
      exact iB.2
    · have hi : i < n := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hui)).1
      simp only [scsVertexClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · cases hli : labelAt i <;> simp [Clause.eval, Literal.eval, hσ0, hσ1, hσ2, hli]
      · cases hli : labelAt i <;> simp [Clause.eval, Literal.eval, hσ0, hσ1, hli]
      · cases hli : labelAt i <;> simp [Clause.eval, Literal.eval, hσ0, hσ2, hli]
      · cases hli : labelAt i <;> simp [Clause.eval, Literal.eval, hσ1, hσ2, hli]
      · simp only [Clause.eval, Literal.eval, hσ3, hσ0, List.any_cons, List.any_nil,
          Bool.or_false, Bool.or_eq_true, beq_iff_eq, decide_eq_false_iff_not, decide_eq_true_eq]
        by_cases hlt : iA.1 < i + 1
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
          · exact Or.inr (Or.inl hlt')
          · have hfin : (⟨i, hi⟩ : Fin n) = iA := Fin.ext heq.symm
            exact Or.inr (Or.inr (by simp [labelAt, hi, hfin, iA, ℓ, haS, ha]))
        · exact Or.inl hlt
      · simp only [Clause.eval, Literal.eval, hσ4, hσ1, List.any_cons, List.any_nil,
          Bool.or_false, Bool.or_eq_true, beq_iff_eq, decide_eq_false_iff_not, decide_eq_true_eq]
        by_cases hlt : iB.1 < i + 1
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
          · exact Or.inr (Or.inl hlt')
          · have hfin : (⟨i, hi⟩ : Fin n) = iB := Fin.ext heq.symm
            exact Or.inr (Or.inr (by simp [labelAt, hi, hfin, iB, ℓ, hbS, hbA]))
        · exact Or.inl hlt
    · obtain ⟨hi, hu_eq⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hui)
      obtain ⟨hj, hw_eq⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hwj)
      unfold scsPairClauses at hc
      split_ifs at hc with hadjB
      · have hadj_ind : G.induced.Adj (eqv ⟨i, hi⟩) (eqv ⟨j, hj⟩) := by
          rw [Graph.induced_adj, G.vertexEquiv_apply, G.vertexEquiv_apply,
            list_getD_eq_getElem _ _ hi, list_getD_eq_getElem _ _ hj, hu_eq, hw_eq]
          exact (G.adjBool_eq_true_iff u w).mp hadjB
        have hc_ij := hcomp hadj_ind
        have hli : labelAt i = ℓ (eqv ⟨i, hi⟩) := dite_eq_left hi
        have hlj : labelAt j = ℓ (eqv ⟨j, hj⟩) := dite_eq_left hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · simp only [Clause.eval, Literal.eval, List.any_cons, List.any_nil]
          rw [hσ0, hσ1, hli, hlj]
          cases ha' : ℓ (eqv ⟨i, hi⟩) <;> cases hb' : ℓ (eqv ⟨j, hj⟩) <;>
            (rw [ha', hb'] at hc_ij; dsimp only [Label3.compat] at hc_ij; simp_all)
        · simp only [Clause.eval, Literal.eval, List.any_cons, List.any_nil]
          rw [hσ1, hσ0, hli, hlj]
          cases ha' : ℓ (eqv ⟨i, hi⟩) <;> cases hb' : ℓ (eqv ⟨j, hj⟩) <;>
            (rw [ha', hb'] at hc_ij; dsimp only [Label3.compat] at hc_ij; simp_all)
        · simp only [Clause.eval, Literal.eval, List.any_cons, List.any_nil]
          rw [hσ2, hσ2, hli, hlj]
          cases ha' : ℓ (eqv ⟨i, hi⟩) <;> cases hb' : ℓ (eqv ⟨j, hj⟩) <;>
            (rw [ha', hb'] at hc_ij; dsimp only [Label3.compat] at hc_ij; simp_all)
      · simp at hc
  · rintro ⟨σ, hσ⟩
    have heval := (CNF.eval_eq_true_iff _ _).mp hσ
    have hmem_head : ∀ c ∈ ([[ (scsVar 3 0, false) ], [ (scsVar 3 n, true) ],
        [ (scsVar 4 0, false) ], [ (scsVar 4 n, true) ]] : CNF ℕ),
        c.eval σ = true := fun c hc ↦
      heval c (List.mem_append_left _ (List.mem_append_left _ hc))
    have hp0 : σ (scsVar 3 0) = false := by
      simpa [Clause.eval, Literal.eval] using hmem_head [(scsVar 3 0, false)] (by simp)
    have hpn : σ (scsVar 3 n) = true := by
      simpa [Clause.eval, Literal.eval] using hmem_head [(scsVar 3 n, true)] (by simp)
    have hq0 : σ (scsVar 4 0) = false := by
      simpa [Clause.eval, Literal.eval] using hmem_head [(scsVar 4 0, false)] (by simp)
    have hqn : σ (scsVar 4 n) = true := by
      simpa [Clause.eval, Literal.eval] using hmem_head [(scsVar 4 n, true)] (by simp)
    have hvtx : ∀ (i : ℕ) (hi : i < n), ∀ c ∈ scsVertexClauses i, c.eval σ = true := by
      intro i hi c hc
      refine heval c (List.mem_append_left _ (List.mem_append_right _ ?_))
      exact List.mem_flatMap.mpr ⟨(G.distinctVertices[i], i),
        List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi), hc⟩
    have hA_ex : ∃ i : Fin n, σ (scsVar 0 i) = true := by
      by_contra hno; push Not at hno
      have hfalse : ∀ k ≤ n, σ (scsVar 3 k) = false := by
        intro k hk; induction k with
        | zero => exact hp0
        | succ k ih =>
          have hk' : k < n := hk
          have hcl := hvtx k hk' [(scsVar 3 (k + 1), false), (scsVar 3 k, true), (scsVar 0 k, true)]
            (by simp [scsVertexClauses])
          have h0 : σ (scsVar 0 k) = false := Bool.eq_false_iff.mpr (hno ⟨k, hk'⟩)
          have hk0 := ih hk'.le
          simpa [Clause.eval, Literal.eval, hk0, h0] using hcl
      exact Bool.false_ne_true ((hfalse n le_rfl).symm.trans hpn)
    have hB_ex : ∃ i : Fin n, σ (scsVar 1 i) = true := by
      by_contra hno; push Not at hno
      have hfalse : ∀ k ≤ n, σ (scsVar 4 k) = false := by
        intro k hk; induction k with
        | zero => exact hq0
        | succ k ih =>
          have hk' : k < n := hk
          have hcl := hvtx k hk' [(scsVar 4 (k + 1), false), (scsVar 4 k, true), (scsVar 1 k, true)]
            (by simp [scsVertexClauses])
          have h1 : σ (scsVar 1 k) = false := Bool.eq_false_iff.mpr (hno ⟨k, hk'⟩)
          have hk0 := ih hk'.le
          simpa [Clause.eval, Literal.eval, hk0, h1] using hcl
      exact Bool.false_ne_true ((hfalse n le_rfl).symm.trans hqn)
    let labelAt (i : Fin n) : Label3 :=
      if σ (scsVar 0 i) then .A else if σ (scsVar 1 i) then .B else .S
    have hlabel_spec : ∀ i : Fin n,
        (labelAt i = .A → σ (scsVar 0 i) = true) ∧
        (labelAt i = .B → σ (scsVar 1 i) = true) ∧
        (labelAt i = .S → σ (scsVar 2 i) = true) := by
      intro i
      have hcover := hvtx i i.2
        [(scsVar 0 i, true), (scsVar 1 i, true), (scsVar 2 i, true)] (by simp [scsVertexClauses])
      dsimp only [labelAt]
      cases h0 : σ (scsVar 0 i) <;> cases h1 : σ (scsVar 1 i) <;>
        cases h2 : σ (scsVar 2 i) <;> simp_all [Clause.eval, Literal.eval]
    have hnot01 : ∀ i : Fin n, ¬ (σ (scsVar 0 i) = true ∧ σ (scsVar 1 i) = true) := by
      intro i ⟨h0, h1⟩
      have hcl := hvtx i i.2 [(scsVar 0 i, false), (scsVar 1 i, false)] (by simp [scsVertexClauses])
      simp [Clause.eval, Literal.eval, h0, h1] at hcl
    let ℓ : {v // v ∈ G.vertices} → Label3 := fun v ↦ labelAt (eqv.symm v)
    obtain ⟨iA, hiA⟩ := hA_ex
    obtain ⟨iB, hiB⟩ := hB_ex
    have hiB0 : σ (scsVar 0 iB) = false := Bool.eq_false_iff.mpr fun h0 ↦ hnot01 iB ⟨h0, hiB⟩
    have hcomp : ∀ {u w : {v // v ∈ G.vertices}}, G.induced.Adj u w →
        (ℓ u).compat (ℓ w) = true := by
      intro u w hadj
      let i := eqv.symm u; let j := eqv.symm w
      have hu_eq : (u : ℕ) = G.distinctVertices[i.1] := by
        have h := G.vertexEquiv_apply i
        rw [Equiv.apply_symm_apply, list_getD_eq_getElem _ _ i.2] at h; exact h
      have hw_eq : (w : ℕ) = G.distinctVertices[j.1] := by
        have h := G.vertexEquiv_apply j
        rw [Equiv.apply_symm_apply, list_getD_eq_getElem _ _ j.2] at h; exact h
      have hadjB : G.adjBool G.distinctVertices[i.1] G.distinctVertices[j.1] = true := by
        rw [Graph.adjBool_eq_true_iff, ← hu_eq, ← hw_eq]; exact hadj
      have hpair : ∀ c ∈ scsPairClauses G (G.distinctVertices[i.1], i.1)
          (G.distinctVertices[j.1], j.1), c.eval σ = true := fun c hc ↦
        heval c (List.mem_append_right _ (List.mem_flatMap.mpr
          ⟨(G.distinctVertices[i.1], i.1), List.mem_zipIdx_iff_getElem?.mpr (by simp [i.2]),
            List.mem_flatMap.mpr ⟨(G.distinctVertices[j.1], j.1),
              List.mem_zipIdx_iff_getElem?.mpr (by simp [j.2]), hc⟩⟩))
      change (labelAt i).compat (labelAt j) = true
      have hsi := hlabel_spec i; have hsj := hlabel_spec j
      cases hli : labelAt i <;> cases hlj : labelAt j <;> try rfl
      · have h0 := hsi.1 hli; have h1 := hsj.2.1 hlj
        have hcl := hpair [(scsVar 0 i.1, false), (scsVar 1 j.1, false)]
          (by simp [scsPairClauses, hadjB])
        simp [Clause.eval, Literal.eval, h0, h1] at hcl
      · have h1 := hsi.2.1 hli; have h0 := hsj.1 hlj
        have hcl := hpair [(scsVar 1 i.1, false), (scsVar 0 j.1, false)]
          (by simp [scsPairClauses, hadjB])
        simp [Clause.eval, Literal.eval, h1, h0] at hcl
      · have h2i := hsi.2.2 hli; have h2j := hsj.2.2 hlj
        have hcl := hpair [(scsVar 2 i.1, false), (scsVar 2 j.1, false)]
          (by simp [scsPairClauses, hadjB])
        simp [Clause.eval, Literal.eval, h2i, h2j] at hcl
    refine ⟨{v | ℓ v = .S}, ?_, {v | ℓ v = .A}, {v | ℓ v = .B},
      ⟨eqv iA, by simp [ℓ, labelAt, hiA]⟩, ⟨eqv iB, by simp [ℓ, labelAt, hiB0, hiB]⟩,
      Set.disjoint_left.mpr fun v h1 h2 ↦ Label3.noConfusion (h1.symm.trans h2),
      by ext v; simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq];
         cases ℓ v <;> simp,
      fun u hu w hw hadj ↦ ?_⟩
    · intro u hu w hw _ hadj
      have hc := hcomp hadj; rw [hu, hw] at hc; exact Bool.false_ne_true hc
    · have hc := hcomp hadj; rw [hu, hw] at hc; exact Bool.false_ne_true hc

/-- `StableCutset` belongs to `NP` under `Cslib.Complexity.encGraph`. -/
theorem StableCutset_mem_NP : StableCutset ∈ NP encGraph :=
  polyTimeReducible_StableCutset_ThreeSAT.mem_NP ThreeSAT.mem_NP

/-- `StableCutsetMinDeg c` belongs to `NP` for every `c : ℕ`. -/
theorem StableCutsetMinDeg_mem_NP (c : ℕ) : StableCutsetMinDeg c ∈ NP encGraph := by
  let guard (G : Graph) : Bool :=
    let V := G.distinctVertices
    if c = 0 then true
    else decide (1 ≤ V.length) && V.all fun u ↦ decide (c ≤ V.countP fun w ↦ G.adjBool u w)
  have hguard_poly : ComputableInPolyTime guard encGraph encBool := by
    have hV := Graph.computableInPolyTime_distinctVertices
    have hlen := (ComputableInPolyTime.length_list encNat).comp hV
    have hdeg : ComputableInPolyTime
        (fun p : Graph × ℕ ↦ p.1.distinctVertices.countP fun w ↦ p.1.adjBool p.2 w)
        (encPair encGraph encNat) encUnary :=
      ComputableInPolyTime.countPWithInput (hV.comp (ComputableInPolyTime.fst _ _)) (by fun_prop)
    dsimp only [guard]
    split_ifs
    · exact .const true
    · exact ComputableInPolyTime.bool_and' (by fun_prop)
        (ComputableInPolyTime.allWithInput hV (by fun_prop))
  have hguard_iff : ∀ G : Graph, G ∈ StableCutsetMinDeg c ↔ guard G = true ∧ G ∈ StableCutset := by
    intro G
    rw [mem_StableCutsetMinDeg_iff]
    refine and_congr_left' ?_
    dsimp only [guard]
    split_ifs with h0
    · subst h0; simp
    · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      have hdeg_eq : ∀ (u : ℕ) (hu : u ∈ G.distinctVertices),
          (G.distinctVertices.countP fun w ↦ G.adjBool u w) =
            G.induced.degree ⟨u, G.mem_distinctVertices.mp hu⟩ := by
        intro u hu
        let u' : {w // w ∈ G.vertices} := ⟨u, G.mem_distinctVertices.mp hu⟩
        rw [List.countP_eq_length_filter,
          ← List.toFinset_card_of_nodup (G.nodup_distinctVertices.filter _)]
        have hcard_map : (G.induced.neighborFinset u').card =
            ((G.induced.neighborFinset u').map (Function.Embedding.subtype _)).card :=
          (Finset.card_map _).symm
        rw [← SimpleGraph.card_neighborFinset_eq_degree, hcard_map]
        congr 1; ext w
        simp only [List.mem_toFinset, List.mem_filter, G.mem_distinctVertices,
          G.adjBool_eq_true_iff, Finset.mem_map, Function.Embedding.coe_subtype,
          SimpleGraph.mem_neighborFinset, Graph.induced_adj]
        exact ⟨fun ⟨hwV, hadj⟩ ↦ ⟨⟨w, hwV⟩, hadj, rfl⟩,
          fun ⟨⟨w', hw'V⟩, hadj, heq⟩ ↦ by subst heq; exact ⟨hw'V, hadj⟩⟩
      by_cases hV : G.distinctVertices = []
      · have hmd0 : G.induced.minDegree = 0 := by
          have _ : IsEmpty {w // w ∈ G.vertices} :=
            ⟨fun w ↦ List.not_mem_nil (hV ▸ G.mem_distinctVertices.mpr w.2)⟩
          simp [SimpleGraph.minDegree]
        simp [hV, hmd0, h0]
      · have h1 : 1 ≤ G.distinctVertices.length :=
          Nat.pos_iff_ne_zero.mpr (List.length_pos_iff_ne_nil.mpr hV |>.ne')
        simp only [h1, true_and]
        obtain ⟨u₀, hu₀⟩ := List.exists_mem_of_ne_nil G.distinctVertices hV
        have _ : Nonempty {w // w ∈ G.vertices} := ⟨⟨u₀, G.mem_distinctVertices.mp hu₀⟩⟩
        obtain ⟨v_min, hv_min⟩ := G.induced.exists_minimal_degree_vertex
        constructor
        · intro hle u hu
          rw [hdeg_eq u hu]; exact hle.trans (G.induced.minDegree_le_degree _)
        · intro hall
          have hv_DV : v_min.1 ∈ G.distinctVertices := G.mem_distinctVertices.mpr v_min.2
          have := hall v_min.1 hv_DV
          rwa [hdeg_eq v_min.1 hv_DV, ← hv_min] at this
  exact mem_NP_of_guard hguard_poly StableCutset_mem_NP hguard_iff

/-! ## Edge-Clique Attachment and `StableCutset ≤_p StableCutsetMinDeg c` (`c > 1`) -/

/-- Vertex type of the edge-clique attachment graph `G'` attaching a `(c - 1)`-clique to every
edge of `G`. -/
abbrev EdgeCliqueVertex {V : Type*} (G : SimpleGraph V) (c : ℕ) : Type _ :=
  V ⊕ (G.edgeSet × Fin (c - 1))

/-- Edge-clique attachment graph `attachEdgeCliques G c`: for each edge `e = {u, v}` of `G`, attach
a `(c - 1)`-clique adjacent to both `u` and `v`. -/
@[expose] def attachEdgeCliques {V : Type*} (G : SimpleGraph V) (c : ℕ) :
    SimpleGraph (EdgeCliqueVertex G c) where
  Adj x y :=
    match x, y with
    | .inl u, .inl v => G.Adj u v
    | .inl u, .inr (e, _) => u ∈ (e.1 : Sym2 V)
    | .inr (e, _), .inl v => v ∈ (e.1 : Sym2 V)
    | .inr (e₁, i₁), .inr (e₂, i₂) => e₁ = e₂ ∧ i₁ ≠ i₂
  symm := ⟨fun x y h ↦ by
    cases x <;> cases y
    · exact (h : G.Adj _ _).symm
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun x h ↦ by
    cases x
    · exact G.ne_of_adj h rfl
    · exact h.2 rfl⟩

instance instDecidableAdjAttachEdgeCliques {V : Type*} (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (c : ℕ) : DecidableRel (attachEdgeCliques G c).Adj := by
  intro x y; cases x <;> cases y <;> dsimp only [attachEdgeCliques] <;> infer_instance

theorem degree_attachEdgeCliques_inl {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℕ} (hc : 1 ≤ c) (u : V) :
    (attachEdgeCliques G c).degree (.inl u) = c * G.degree u := by
  let incEdges : Finset G.edgeSet := Finset.univ.filter fun e ↦ u ∈ (e.1 : Sym2 V)
  have hcard_inc : incEdges.card = G.degree u := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun (e : G.edgeSet) (he : e ∈ incEdges) ↦
        Sym2.Mem.other ((Finset.mem_filter.mp he).2))
      (fun e he ↦ ?_) (fun e₁ he₁ e₂ he₂ heq ↦ ?_) (fun v hv ↦ ?_)
    · have hmem : u ∈ (e.1 : Sym2 V) := (Finset.mem_filter.mp he).2
      exact (G.mem_neighborFinset u _).mpr
        (G.mem_edgeSet.mp (by rw [Sym2.other_spec hmem]; exact e.2))
    · have hm₁ : u ∈ (e₁.1 : Sym2 V) := (Finset.mem_filter.mp he₁).2
      have hm₂ : u ∈ (e₂.1 : Sym2 V) := (Finset.mem_filter.mp he₂).2
      apply Subtype.ext; rw [← Sym2.other_spec hm₁, ← Sym2.other_spec hm₂, heq]
    · have hadj : G.Adj u v := (G.mem_neighborFinset u v).mp hv
      let e : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr hadj⟩
      have he : e ∈ incEdges := Finset.mem_filter.mpr ⟨Finset.mem_univ e, Sym2.mem_mk_left u v⟩
      refine ⟨e, he, ?_⟩
      have hmem : u ∈ (e.1 : Sym2 V) := (Finset.mem_filter.mp he).2
      rcases Sym2.eq_iff.mp (Sym2.other_spec hmem) with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact h2.trans h1
  have hsplit : (attachEdgeCliques G c).neighborFinset (.inl u) =
      (G.neighborFinset u).map Function.Embedding.inl ∪
        (incEdges ×ˢ (Finset.univ : Finset (Fin (c - 1)))).map Function.Embedding.inr := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x with
    | inl v => dsimp only [attachEdgeCliques]; simp
    | inr p => rcases p with ⟨e, i⟩; dsimp only [attachEdgeCliques, incEdges]; simp
  have hdisj : Disjoint ((G.neighborFinset u).map Function.Embedding.inl)
      ((incEdges ×ˢ (Finset.univ : Finset (Fin (c - 1)))).map Function.Embedding.inr) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    obtain ⟨_, _, rfl⟩ := Finset.mem_map.mp hx1
    obtain ⟨_, _, heq⟩ := Finset.mem_map.mp hx2
    nomatch heq
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hsplit, Finset.card_union_of_disjoint hdisj,
    Finset.card_map, Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    hcard_inc, SimpleGraph.card_neighborFinset_eq_degree]
  have : 1 + (c - 1) = c := by omega
  nlinarith

theorem degree_attachEdgeCliques_inr {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℕ} (hc : 2 ≤ c)
    (e : G.edgeSet) (i : Fin (c - 1)) :
    (attachEdgeCliques G c).degree (.inr (e, i)) = c := by
  rcases e with ⟨s, hs⟩
  induction s using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := G.ne_of_adj (G.mem_edgeSet.mp hs)
    let e₀ : G.edgeSet := ⟨s(u, v), hs⟩
    have hsplit : (attachEdgeCliques G c).neighborFinset (.inr (e₀, i)) =
        ({u, v} : Finset V).map Function.Embedding.inl ∪
          (({e₀} : Finset G.edgeSet) ×ˢ
            ((Finset.univ : Finset (Fin (c - 1))).erase i)).map Function.Embedding.inr := by
      ext x
      rw [SimpleGraph.mem_neighborFinset]
      cases x with
      | inl w => dsimp only [attachEdgeCliques, e₀]; simp
      | inr p =>
        rcases p with ⟨e', j⟩
        dsimp only [attachEdgeCliques]
        constructor
        · rintro ⟨rfl, hij⟩
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_map.mpr
            ⟨(e₀, j), Finset.mem_product.mpr ⟨Finset.mem_singleton_self e₀,
              Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩⟩, rfl⟩))
        · intro hmem
          rcases Finset.mem_union.mp hmem with h1 | h2
          · obtain ⟨_, _, heq⟩ := Finset.mem_map.mp h1; nomatch heq
          · obtain ⟨⟨e₁, j₁⟩, hp, heq⟩ := Finset.mem_map.mp h2
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Sum.inr.inj heq)
            obtain ⟨he₁, hj₁⟩ := Finset.mem_product.mp hp
            exact ⟨(Finset.mem_singleton.mp he₁).symm, (Finset.mem_erase.mp hj₁).1.symm⟩
    have hdisj : Disjoint (({u, v} : Finset V).map Function.Embedding.inl)
        ((({e₀} : Finset G.edgeSet) ×ˢ
          ((Finset.univ : Finset (Fin (c - 1))).erase i)).map Function.Embedding.inr) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      obtain ⟨_, _, rfl⟩ := Finset.mem_map.mp hx1
      obtain ⟨_, _, heq⟩ := Finset.mem_map.mp hx2
      nomatch heq
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hsplit, Finset.card_union_of_disjoint hdisj,
      Finset.card_map, Finset.card_map, Finset.card_product, Finset.card_singleton,
      Finset.card_pair huv, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega

theorem minDegree_attachEdgeCliques_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℕ} (hc : 2 ≤ c) [Nonempty V]
    (hmin : 1 ≤ G.minDegree) : c ≤ (attachEdgeCliques G c).minDegree := by
  have _ : Nonempty (EdgeCliqueVertex G c) := ⟨.inl (Classical.arbitrary V)⟩
  obtain ⟨x_min, hx_min⟩ := (attachEdgeCliques G c).exists_minimal_degree_vertex
  rw [hx_min]
  cases x_min with
  | inl u =>
    rw [degree_attachEdgeCliques_inl G (by omega) u]
    have hdu : 1 ≤ G.degree u := hmin.trans (G.minDegree_le_degree u)
    nlinarith
  | inr p => rw [degree_attachEdgeCliques_inr G hc p.1 p.2]

/-- For every `c : ℕ` and every graph `G`, `attachEdgeCliques G c` admits a stable cutset if and
only if `G` admits a stable cutset. -/
theorem hasStableCutset_attachEdgeCliques_iff {V : Type*} (G : SimpleGraph V) (c : ℕ) :
    HasStableCutset (attachEdgeCliques G c) ↔ HasStableCutset G := by
  constructor
  · rintro ⟨S', hS'indep, A', B', ⟨a', ha'⟩, ⟨b', hb'⟩, hdisj', hunion', hno'⟩
    let S : Set V := {u : V | Sum.inl u ∈ S'}
    let A : Set V := {u : V | Sum.inl u ∈ A'}
    let B : Set V := {u : V | Sum.inl u ∈ B'}
    have hshore_nonempty : ∀ (C' : Set (EdgeCliqueVertex G c)),
        C'.Nonempty → (∀ x ∈ C', ∀ y ∈ (S'ᶜ \ C'), ¬ (attachEdgeCliques G c).Adj x y) →
        ∃ u : V, Sum.inl u ∈ C' := by
      rintro C' ⟨z, hz⟩ hsep
      cases z with
      | inl u => exact ⟨u, hz⟩
      | inr p =>
        rcases p with ⟨⟨e, he⟩, i⟩
        induction e using Sym2.ind with
        | _ u v =>
          have hadj_uv : G.Adj u v := G.mem_edgeSet.mp he
          have hnot_both_S : ¬ (Sum.inl u ∈ S' ∧ Sum.inl v ∈ S') := fun ⟨huS, hvS⟩ ↦
            hS'indep huS hvS (fun h ↦ G.ne_of_adj hadj_uv (Sum.inl.inj h)) hadj_uv
          have hex_nonS : ∃ w : V, w ∈ (s(u, v) : Sym2 V) ∧ Sum.inl w ∉ S' := by
            by_cases huS : Sum.inl u ∈ S'
            · exact ⟨v, Sym2.mem_mk_right u v, fun hvS ↦ hnot_both_S ⟨huS, hvS⟩⟩
            · exact ⟨u, Sym2.mem_mk_left u v, huS⟩
          obtain ⟨w, hw_e, hwnS⟩ := hex_nonS
          refine ⟨w, ?_⟩
          by_contra hwnC
          exact hsep _ hz (Sum.inl w) ⟨hwnS, hwnC⟩ hw_e
    have hA_ne : A.Nonempty := hshore_nonempty A' ⟨a', ha'⟩ fun x hx y hy hadj ↦
      hno' x hx y ((hunion' ▸ hy.1).resolve_left hy.2) hadj
    have hB_ne : B.Nonempty := hshore_nonempty B' ⟨b', hb'⟩ fun x hx y hy hadj ↦
      hno' y ((hunion' ▸ hy.1).resolve_right hy.2) x hx hadj.symm
    refine ⟨S, fun u hu v hv huv hadj ↦ hS'indep hu hv (fun h ↦ huv (Sum.inl.inj h)) hadj,
      A, B, hA_ne, hB_ne,
      Set.disjoint_left.mpr fun u h1 h2 ↦ Set.disjoint_left.mp hdisj' h1 h2,
      by ext u; simpa [S, A, B] using Set.ext_iff.mp hunion' (Sum.inl u),
      fun u hu v hv hadj ↦ hno' (Sum.inl u) hu (Sum.inl v) hv hadj⟩
  · rintro ⟨S, hSindep, A, B, ⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩, hdisj, hunion, hno⟩
    let edgeInA (e : G.edgeSet) : Prop := ∃ w ∈ (e.1 : Sym2 V), w ∈ A
    let S' : Set (EdgeCliqueVertex G c) := {x | ∃ u ∈ S, x = .inl u}
    let A' : Set (EdgeCliqueVertex G c) :=
      {x | (∃ u ∈ A, x = .inl u) ∨ ∃ p : G.edgeSet × Fin (c - 1), edgeInA p.1 ∧ x = .inr p}
    let B' : Set (EdgeCliqueVertex G c) :=
      {x | (∃ u ∈ B, x = .inl u) ∨ ∃ p : G.edgeSet × Fin (c - 1), ¬ edgeInA p.1 ∧ x = .inr p}
    have hedge_no_B : ∀ {e : G.edgeSet}, edgeInA e → ∀ v ∈ (e.1 : Sym2 V), v ∉ B := by
      rintro ⟨s, hs⟩ ⟨w, hws, hwA⟩ v hvs hvB
      induction s using Sym2.ind with
      | _ x y =>
        have hadj_xy : G.Adj x y := G.mem_edgeSet.mp hs
        simp only [Sym2.mem_iff] at hws hvs
        rcases hws with rfl | rfl <;> rcases hvs with rfl | rfl
        · exact Set.disjoint_left.mp hdisj hwA hvB
        · exact hno w hwA v hvB hadj_xy
        · exact hno w hwA v hvB hadj_xy.symm
        · exact Set.disjoint_left.mp hdisj hwA hvB
    refine ⟨S', ?_, A', B', ⟨.inl a₀, Or.inl ⟨a₀, ha₀, rfl⟩⟩, ⟨.inl b₀, Or.inl ⟨b₀, hb₀, rfl⟩⟩,
      ?_, ?_, ?_⟩
    · rintro _ ⟨u, huS, rfl⟩ _ ⟨v, hvS, rfl⟩ hne hadj
      exact hSindep huS hvS (fun h ↦ hne (congrArg Sum.inl h)) hadj
    · rw [Set.disjoint_left]
      rintro x (⟨u, huA, rfl⟩ | ⟨p, hpA, rfl⟩) (⟨v, hvB, heq⟩ | ⟨q, hqB, heq⟩)
      · exact Set.disjoint_left.mp hdisj huA (Sum.inl.inj heq ▸ hvB)
      · nomatch heq
      · nomatch heq
      · exact hqB (Sum.inr.inj heq ▸ hpA)
    · ext x; cases x with
      | inl u =>
        have hu := Set.ext_iff.mp hunion u
        simpa [S', A', B', exists_eq_right'] using hu
      | inr p =>
        constructor
        · intro _
          by_cases hA : edgeInA p.1
          · exact Or.inl (Or.inr ⟨p, hA, rfl⟩)
          · exact Or.inr (Or.inr ⟨p, hA, rfl⟩)
        · rintro _ ⟨_, _, h⟩; nomatch h
    · rintro x hx y hy hadj
      rcases hx with ⟨u, huA, rfl⟩ | ⟨⟨e₁, i₁⟩, he₁A, rfl⟩ <;>
        rcases hy with ⟨v, hvB, rfl⟩ | ⟨⟨e₂, i₂⟩, he₂B, rfl⟩
      · exact hno u huA v hvB hadj
      · exact he₂B ⟨u, hadj, huA⟩
      · exact hedge_no_B he₁A v hadj hvB
      · exact he₂B (hadj.1 ▸ he₁A)

private theorem computableInPolyTime_natRangeList {γ : Type} {enc : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun x ↦ List.range (n x)) enc (encList encNat) := by
  have h := ComputableInPolyTime.mapWithInput (f := fun _ i ↦ i)
    (ComputableInPolyTime.range.comp hn)
    (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))
  simpa using h

private def canonIndexEdges (G : Graph) : List (ℕ × ℕ) :=
  let V := G.distinctVertices
  let n := V.length
  (List.range n).flatMap fun i ↦
    (List.range n).flatMap fun j ↦
      if decide (i < j) && G.adjBool (V.getD i 0) (V.getD j 0) then [(i, j)] else []

private theorem computableInPolyTime_canonIndexEdges :
    ComputableInPolyTime canonIndexEdges encGraph (encList (encPair encUnary encUnary)) := by
  have hV := Graph.computableInPolyTime_distinctVertices
  have hn : ComputableInPolyTime (fun G : Graph ↦ G.distinctVertices.length) encGraph encUnary :=
    (ComputableInPolyTime.length_list encNat).comp hV
  have hr := ComputableInPolyTime.range.comp hn
  have hG2 : ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ ↦ p.1.1)
      (encPair (encPair encGraph encUnary) encUnary) encGraph := by fun_prop
  have hi2 : ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ ↦ p.1.2)
      (encPair (encPair encGraph encUnary) encUnary) encUnary := by fun_prop
  have hj2 : ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ ↦ p.2)
      (encPair (encPair encGraph encUnary) encUnary) encUnary := by fun_prop
  have hvi : ComputableInPolyTime
      (fun p : (Graph × ℕ) × ℕ ↦ p.1.1.distinctVertices.getD p.1.2 0)
      (encPair (encPair encGraph encUnary) encUnary) encNat :=
    (ComputableInPolyTime.listGetD (encA := encNat) (encL := encList encNat) 0).comp
      ((hV.comp hG2).prod hi2)
  have hvj : ComputableInPolyTime
      (fun p : (Graph × ℕ) × ℕ ↦ p.1.1.distinctVertices.getD p.2 0)
      (encPair (encPair encGraph encUnary) encUnary) encNat :=
    (ComputableInPolyTime.listGetD (encA := encNat) (encL := encList encNat) 0).comp
      ((hV.comp hG2).prod hj2)
  have hbody : ComputableInPolyTime
      (fun p : (Graph × ℕ) × ℕ ↦
        if decide (p.1.2 < p.2) &&
            p.1.1.adjBool (p.1.1.distinctVertices.getD p.1.2 0)
              (p.1.1.distinctVertices.getD p.2 0) then
          [(p.1.2, p.2)]
        else ([] : List (ℕ × ℕ)))
      (encPair (encPair encGraph encUnary) encUnary) (encList (encPair encUnary encUnary)) := by
    have hcond : ComputableInPolyTime
        (fun p : (Graph × ℕ) × ℕ ↦ decide (p.1.2 < p.2) &&
          p.1.1.adjBool (p.1.1.distinctVertices.getD p.1.2 0)
            (p.1.1.distinctVertices.getD p.2 0))
        (encPair (encPair encGraph encUnary) encUnary) encBool := by fun_prop
    exact hcond.ite (by fun_prop) (.const [])
  have hinner : ComputableInPolyTime
      (fun p : Graph × ℕ ↦
        (List.range p.1.distinctVertices.length).flatMap fun j ↦
          if decide (p.2 < j) &&
              p.1.adjBool (p.1.distinctVertices.getD p.2 0)
                (p.1.distinctVertices.getD j 0) then
            [(p.2, j)]
          else [])
      (encPair encGraph encUnary) (encList (encPair encUnary encUnary)) :=
    ComputableInPolyTime.flatMapWithInput
      (hr.comp (ComputableInPolyTime.fst encGraph encUnary)) hbody
  unfold canonIndexEdges
  exact ComputableInPolyTime.flatMapWithInput hr hinner

private theorem mem_canonIndexEdges_iff (G : Graph) (p : ℕ × ℕ) :
    p ∈ canonIndexEdges G ↔
      p.1 < p.2 ∧ p.2 < G.distinctVertices.length ∧
        G.adjBool (G.distinctVertices.getD p.1 0) (G.distinctVertices.getD p.2 0) = true := by
  rcases p with ⟨i, j⟩
  simp only [canonIndexEdges, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i', _, j', hj', hm⟩
    split_ifs at hm with hc
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨hc.1, hj', hc.2⟩
    · simp at hm
  · rintro ⟨hij, hj, hadj⟩
    refine ⟨i, by omega, j, hj, ?_⟩
    simp only [hij, hadj, decide_true, Bool.true_and, ↓reduceIte, List.mem_singleton]

private theorem nodup_canonIndexEdges (G : Graph) : (canonIndexEdges G).Nodup := by
  unfold canonIndexEdges
  rw [List.nodup_flatMap]
  refine ⟨fun i _ ↦ List.nodup_flatMap.mpr ⟨fun j _ ↦ by split_ifs <;> simp,
    List.nodup_range.pairwise_of_forall_ne fun j₁ _ j₂ _ hne ↦ List.disjoint_left.mpr
      fun x hx₁ hx₂ ↦ ?_⟩,
    List.nodup_range.pairwise_of_forall_ne fun i₁ _ i₂ _ hne ↦ List.disjoint_left.mpr
      fun x hx₁ hx₂ ↦ ?_⟩
  · dsimp only at hx₁ hx₂
    split_ifs at hx₁ hx₂
    all_goals simp only [List.mem_singleton, List.not_mem_nil] at hx₁ hx₂
    subst hx₁; exact hne (Prod.mk.inj hx₂).2
  · dsimp only at hx₁ hx₂
    rw [List.mem_flatMap] at hx₁ hx₂
    obtain ⟨_, _, hm₁⟩ := hx₁; obtain ⟨_, _, hm₂⟩ := hx₂
    split_ifs at hm₁ hm₂
    all_goals simp only [List.mem_singleton, List.not_mem_nil] at hm₁ hm₂
    subst hm₁; exact hne (Prod.mk.inj hm₂).1

/-- Polynomial-time encoded-graph implementation of edge-clique attachment. -/
def attachEdgeCliquesGraph (c : ℕ) (G : Graph) : Graph :=
  let n := G.distinctVertices.length
  let E := canonIndexEdges G
  let m := E.length
  { vertices := List.range (n + m * (c - 1))
    edges :=
      E.zipIdx.flatMap fun ⟨ij, e⟩ ↦
        [(ij.1, ij.2)] ++
          ((List.range (c - 1)).flatMap fun t ↦
            [(ij.1, n + e * (c - 1) + t), (ij.2, n + e * (c - 1) + t)]) ++
          ((List.range (c - 1)).flatMap fun t₁ ↦
            (List.range (c - 1)).flatMap fun t₂ ↦
              if t₁ < t₂ then [(n + e * (c - 1) + t₁, n + e * (c - 1) + t₂)] else []) }

theorem computableInPolyTime_attachEdgeCliquesGraph (c : ℕ) :
    ComputableInPolyTime (attachEdgeCliquesGraph c) encGraph encGraph := by
  have hV := Graph.computableInPolyTime_distinctVertices
  have hn : ComputableInPolyTime (fun G : Graph ↦ G.distinctVertices.length) encGraph encUnary :=
    (ComputableInPolyTime.length_list encNat).comp hV
  have hE := computableInPolyTime_canonIndexEdges
  have hm : ComputableInPolyTime (fun G : Graph ↦ (canonIndexEdges G).length) encGraph encUnary :=
    (ComputableInPolyTime.length_list (encPair encUnary encUnary)).comp hE
  have hverts := computableInPolyTime_natRangeList
    (n := fun G : Graph ↦ G.distinctVertices.length + (canonIndexEdges G).length * (c - 1))
    (by fun_prop)
  have hEzip : ComputableInPolyTime (fun G : Graph ↦ (canonIndexEdges G).zipIdx) encGraph
      (encList (encPair (encPair encUnary encUnary) encUnary)) := by
    have hzip : ComputableInPolyTime (List.zipIdx (α := ℕ × ℕ))
        (encList (encPair encUnary encUnary))
        (encList (encPair (encPair encUnary encUnary) encUnary)) := by fun_prop
    exact hzip.comp hE
  have hnE := hn.comp (ComputableInPolyTime.fst encGraph
    (encPair (encPair encUnary encUnary) encUnary))
  have hiE : ComputableInPolyTime (fun p : Graph × ((ℕ × ℕ) × ℕ) ↦ p.2.1.1)
      (encPair encGraph (encPair (encPair encUnary encUnary) encUnary)) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hjE : ComputableInPolyTime (fun p : Graph × ((ℕ × ℕ) × ℕ) ↦ p.2.1.2)
      (encPair encGraph (encPair (encPair encUnary encUnary) encUnary)) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have heE : ComputableInPolyTime (fun p : Graph × ((ℕ × ℕ) × ℕ) ↦ p.2.2)
      (encPair encGraph (encPair (encPair encUnary encUnary) encUnary)) encUnary := by fun_prop
  have hhead : ComputableInPolyTime
      (fun p : Graph × ((ℕ × ℕ) × ℕ) ↦ ([(p.2.1.1, p.2.1.2)] : List (ℕ × ℕ)))
      (encPair encGraph (encPair (encPair encUnary encUnary) encUnary))
      (encList (encPair encNat encNat)) := by fun_prop
  have hatt : ComputableInPolyTime
      (fun p : Graph × ((ℕ × ℕ) × ℕ) ↦ (List.range (c - 1)).flatMap fun t ↦
        [(p.2.1.1, p.1.distinctVertices.length + p.2.2 * (c - 1) + t),
         (p.2.1.2, p.1.distinctVertices.length + p.2.2 * (c - 1) + t)])
      (encPair encGraph (encPair (encPair encUnary encUnary) encUnary))
      (encList (encPair encNat encNat)) := by
    refine ComputableInPolyTime.flatMapConst (List.range (c - 1)) fun t _ ↦ ?_
    have hv_t : ComputableInPolyTime
        (fun p : Graph × ((ℕ × ℕ) × ℕ) ↦ p.1.distinctVertices.length + p.2.2 * (c - 1) + t)
        (encPair encGraph (encPair (encPair encUnary encUnary) encUnary)) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    fun_prop
  have hclq : ComputableInPolyTime
      (fun p : Graph × ((ℕ × ℕ) × ℕ) ↦ (List.range (c - 1)).flatMap fun t₁ ↦
        (List.range (c - 1)).flatMap fun t₂ ↦
          if t₁ < t₂ then
            [(p.1.distinctVertices.length + p.2.2 * (c - 1) + t₁,
              p.1.distinctVertices.length + p.2.2 * (c - 1) + t₂)]
          else [])
      (encPair encGraph (encPair (encPair encUnary encUnary) encUnary))
      (encList (encPair encNat encNat)) := by
    refine ComputableInPolyTime.flatMapConst (List.range (c - 1)) fun t₁ _ ↦ ?_
    refine ComputableInPolyTime.flatMapConst (List.range (c - 1)) fun t₂ _ ↦ ?_
    split_ifs
    · have hv1 : ComputableInPolyTime
          (fun p : Graph × ((ℕ × ℕ) × ℕ) ↦ p.1.distinctVertices.length + p.2.2 * (c - 1) + t₁)
          (encPair encGraph (encPair (encPair encUnary encUnary) encUnary)) encNat :=
        ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
      have hv2 : ComputableInPolyTime
          (fun p : Graph × ((ℕ × ℕ) × ℕ) ↦ p.1.distinctVertices.length + p.2.2 * (c - 1) + t₂)
          (encPair encGraph (encPair (encPair encUnary encUnary) encUnary)) encNat :=
        ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
      fun_prop
    · exact .const []
  have hedges : ComputableInPolyTime (fun G : Graph ↦ (attachEdgeCliquesGraph c G).edges)
      encGraph (encList (encPair encNat encNat)) := by
    dsimp only [attachEdgeCliquesGraph]
    exact ComputableInPolyTime.flatMapWithInput hEzip
      (ComputableInPolyTime.listAppend' (ComputableInPolyTime.listAppend' hhead hatt) hclq)
  have : attachEdgeCliquesGraph c = fun G ↦ Graph.mk
      (List.range (G.distinctVertices.length + (canonIndexEdges G).length * (c - 1)))
      (attachEdgeCliquesGraph c G).edges := funext fun _ ↦ rfl
  rw [this]; fun_prop

private noncomputable def attachEdgeCliquesGraphIso (c : ℕ) (G : Graph) :
    (attachEdgeCliquesGraph c G).induced ≃g attachEdgeCliques G.induced c := by
  classical
  let n := G.distinctVertices.length
  let E := canonIndexEdges G
  let m := E.length
  let eqvV : Fin n ≃ {v // v ∈ G.vertices} := G.vertexEquiv
  have hE_edge : ∀ k : Fin m,
      (E[k.1]).1 < (E[k.1]).2 ∧ (E[k.1]).2 < n ∧
        G.induced.Adj (eqvV ⟨(E[k.1]).1,
          ((mem_canonIndexEdges_iff G E[k.1]).mp (List.getElem_mem k.2)).1.trans
            ((mem_canonIndexEdges_iff G E[k.1]).mp (List.getElem_mem k.2)).2.1⟩)
          (eqvV ⟨(E[k.1]).2,
            ((mem_canonIndexEdges_iff G E[k.1]).mp (List.getElem_mem k.2)).2.1⟩) := by
    intro k
    obtain ⟨h12, h2n, hadjB⟩ := (mem_canonIndexEdges_iff G E[k.1]).mp (List.getElem_mem k.2)
    refine ⟨h12, h2n, ?_⟩
    rw [Graph.induced_adj, G.vertexEquiv_apply, G.vertexEquiv_apply]
    exact (G.adjBool_eq_true_iff _ _).mp hadjB
  let edgeOfFin (k : Fin m) : G.induced.edgeSet :=
    ⟨s(eqvV ⟨(E[k.1]).1, (hE_edge k).1.trans (hE_edge k).2.1⟩, eqvV ⟨(E[k.1]).2, (hE_edge k).2.1⟩),
      G.induced.mem_edgeSet.mpr (hE_edge k).2.2⟩
  have hedgeOfFin_bij : Function.Bijective edgeOfFin := by
    have hnodup := nodup_canonIndexEdges G
    refine ⟨fun a b hab ↦ ?_, fun ⟨s, hs⟩ ↦ ?_⟩
    · rcases Sym2.eq_iff.mp (Subtype.ext_iff.mp hab) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 := congrArg Fin.val (eqvV.injective h1)
        have e2 := congrArg Fin.val (eqvV.injective h2)
        exact Fin.ext ((hnodup.getElem_inj_iff (hi := a.2) (hj := b.2)).mp (Prod.ext e1 e2))
      · have e1 := congrArg Fin.val (eqvV.injective h1)
        have e2 := congrArg Fin.val (eqvV.injective h2)
        have ha12 := (hE_edge a).1; have hb12 := (hE_edge b).1
        dsimp only at e1 e2; omega
    · induction s using Sym2.ind with
      | _ u w =>
        have hadj : G.induced.Adj u w := G.induced.mem_edgeSet.mp hs
        let iu := eqvV.symm u; let iw := eqvV.symm w
        have hiu_ne_iw : iu.1 ≠ iw.1 := fun h ↦
          G.induced.ne_of_adj hadj (eqvV.symm.injective (Fin.ext h))
        let i := min iu.1 iw.1; let j := max iu.1 iw.1
        have hij : i < j := by dsimp only [i, j]; omega
        have hjn : j < n := max_lt iu.2 iw.2
        have hadjB : G.adjBool (G.distinctVertices.getD i 0) (G.distinctVertices.getD j 0) =
            true := by
          rw [G.adjBool_eq_true_iff]
          rcases Nat.lt_or_gt_of_ne hiu_ne_iw with hlt | hgt
          · have hu_v := G.vertexEquiv_apply iu; rw [eqvV.apply_symm_apply] at hu_v
            have hw_v := G.vertexEquiv_apply iw; rw [eqvV.apply_symm_apply] at hw_v
            rw [show i = iu.1 from Nat.min_eq_left hlt.le,
              show j = iw.1 from Nat.max_eq_right hlt.le, ← hu_v, ← hw_v]; exact hadj
          · have hu_v := G.vertexEquiv_apply iu; rw [eqvV.apply_symm_apply] at hu_v
            have hw_v := G.vertexEquiv_apply iw; rw [eqvV.apply_symm_apply] at hw_v
            rw [show i = iw.1 from Nat.min_eq_right hgt.le,
              show j = iu.1 from Nat.max_eq_left hgt.le, ← hw_v, ← hu_v]; exact hadj.symm
        have hmemE : (i, j) ∈ E := (mem_canonIndexEdges_iff G (i, j)).mpr ⟨hij, hjn, hadjB⟩
        let idx := E.idxOf (i, j)
        have hidx : idx < m := List.idxOf_lt_length_iff.mpr hmemE
        have hget : E[idx] = (i, j) := List.getElem_idxOf hidx
        refine ⟨⟨idx, hidx⟩, Subtype.ext ?_⟩
        dsimp only [edgeOfFin]
        rcases Nat.lt_or_gt_of_ne hiu_ne_iw with hlt | hgt
        · have e1 : (⟨(E[idx]).1, (hE_edge ⟨idx, hidx⟩).1.trans (hE_edge ⟨idx, hidx⟩).2.1⟩ :
              Fin n) = iu := Fin.ext (by dsimp only; rw [hget]; exact Nat.min_eq_left hlt.le)
          have e2 : (⟨(E[idx]).2, (hE_edge ⟨idx, hidx⟩).2.1⟩ : Fin n) = iw :=
            Fin.ext (by dsimp only; rw [hget]; exact Nat.max_eq_right hlt.le)
          exact congrArg₂ (fun x y ↦ s(x, y))
            ((congrArg eqvV e1).trans (eqvV.apply_symm_apply u))
            ((congrArg eqvV e2).trans (eqvV.apply_symm_apply w))
        · have e1 : (⟨(E[idx]).1, (hE_edge ⟨idx, hidx⟩).1.trans (hE_edge ⟨idx, hidx⟩).2.1⟩ :
              Fin n) = iw := Fin.ext (by dsimp only; rw [hget]; exact Nat.min_eq_right hgt.le)
          have e2 : (⟨(E[idx]).2, (hE_edge ⟨idx, hidx⟩).2.1⟩ : Fin n) = iu :=
            Fin.ext (by dsimp only; rw [hget]; exact Nat.max_eq_left hgt.le)
          exact (congrArg₂ (fun x y ↦ s(x, y))
            ((congrArg eqvV e1).trans (eqvV.apply_symm_apply w))
            ((congrArg eqvV e2).trans (eqvV.apply_symm_apply u))).trans Sym2.eq_swap
  let eqvE : Fin m ≃ G.induced.edgeSet := Equiv.ofBijective edgeOfFin hedgeOfFin_bij
  have hdiv_edge : ∀ (k : ℕ) {t : ℕ}, t < c - 1 → (n + k * (c - 1) + t - n) / (c - 1) = k := by
    intro k t ht
    rw [show n + k * (c - 1) + t - n = t + k * (c - 1) by omega,
      Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_zero_iff.mpr (Or.inr ht), zero_add]
  have hmod_edge : ∀ (k : ℕ) {t : ℕ}, t < c - 1 → (n + k * (c - 1) + t - n) % (c - 1) = t := by
    intro k t ht
    rw [show n + k * (c - 1) + t - n = t + k * (c - 1) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  let toFun (x : {z // z ∈ (attachEdgeCliquesGraph c G).vertices}) :
      EdgeCliqueVertex G.induced c :=
    have hx : x.1 < n + m * (c - 1) := List.mem_range.mp x.2
    if hlt : x.1 < n then .inl (eqvV ⟨x.1, hlt⟩)
    else
      have hc1_pos : 0 < c - 1 := by
        by_contra h0; have hc1 : c - 1 = 0 := by omega
        rw [hc1, Nat.mul_zero, add_zero] at hx; exact hlt hx
      let off := x.1 - n
      .inr (eqvE ⟨off / (c - 1), (Nat.div_lt_iff_lt_mul hc1_pos).mpr (by dsimp only [off]; omega)⟩,
        ⟨off % (c - 1), Nat.mod_lt _ hc1_pos⟩)
  let invFun (y : EdgeCliqueVertex G.induced c) :
      {z // z ∈ (attachEdgeCliquesGraph c G).vertices} :=
    match y with
    | .inl u => ⟨(eqvV.symm u).1, List.mem_range.mpr (Nat.lt_add_right _ (eqvV.symm u).2)⟩
    | .inr (e, t) => ⟨n + (eqvE.symm e).1 * (c - 1) + t.1, List.mem_range.mpr (by
        have he : ((eqvE.symm e).1 + 1) ≤ m := (eqvE.symm e).2; have ht := t.2; nlinarith)⟩
  have hleft_inv : Function.LeftInverse invFun toFun := fun x ↦ by
    apply Subtype.ext
    have hx : x.1 < n + m * (c - 1) := List.mem_range.mp x.2
    dsimp only [toFun, invFun]; split_ifs with hlt
    · simp
    · simp only [Equiv.symm_apply_apply]
      have hdm := Nat.div_add_mod (x.1 - n) (c - 1)
      rw [Nat.mul_comm] at hdm; omega
  have hright_inv : Function.RightInverse invFun toFun := fun y ↦ by
    cases y with
    | inl u =>
      dsimp only [invFun, toFun]; rw [dite_eq_left (eqvV.symm u).2]
      exact congrArg Sum.inl (eqvV.apply_symm_apply u)
    | inr p =>
      rcases p with ⟨e, t⟩; dsimp only [invFun, toFun]; rw [dite_eq_right (by omega)]
      congr 1; apply Prod.ext
      · exact Eq.trans (b := eqvE (eqvE.symm e))
          (congrArg eqvE (Fin.ext (hdiv_edge _ t.2))) (eqvE.apply_symm_apply e)
      · exact Fin.ext (hmod_edge _ t.2)
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := hleft_inv
      right_inv := hright_inv
      map_rel_iff' := by
        intro x y
        obtain ⟨x', rfl⟩ : ∃ x', invFun x' = x := ⟨toFun x, hleft_inv x⟩
        obtain ⟨y', rfl⟩ : ∃ y', invFun y' = y := ⟨toFun y, hleft_inv y⟩
        dsimp only [Equiv.coe_fn_mk]
        rw [hright_inv x', hright_inv y', Graph.induced_adj, Graph.toSimpleGraph_adj]
        have hmem_edges : ∀ a b : ℕ, (a, b) ∈ (attachEdgeCliquesGraph c G).edges ↔
            ∃ (e : Fin m),
              ((a = (E[e.1]).1 ∧ b = (E[e.1]).2) ∨
               (∃ t < c - 1, (a = (E[e.1]).1 ∨ a = (E[e.1]).2) ∧ b = n + e.1 * (c - 1) + t) ∨
               (∃ t₁ t₂ : ℕ, t₁ < t₂ ∧ t₂ < c - 1 ∧
                 a = n + e.1 * (c - 1) + t₁ ∧ b = n + e.1 * (c - 1) + t₂)) := by
          intro a b
          dsimp only [attachEdgeCliquesGraph]
          simp only [List.mem_flatMap, List.mem_append, List.mem_range]
          constructor
          · rintro ⟨⟨ij, e⟩, he_zip, (hab | ⟨t, ht, h12⟩) | ⟨t₁, _, t₂, ht₂, hif⟩⟩
            · obtain ⟨he_lt, hij_eq⟩ := List.getElem?_eq_some_iff.mp
                (List.mem_zipIdx_iff_getElem?.mp he_zip)
              dsimp only at he_lt hij_eq hab
              simp only [List.mem_singleton, Prod.mk.injEq] at hab
              exact ⟨⟨e, he_lt⟩, Or.inl (hij_eq ▸ hab)⟩
            · obtain ⟨he_lt, hij_eq⟩ := List.getElem?_eq_some_iff.mp
                (List.mem_zipIdx_iff_getElem?.mp he_zip)
              dsimp only at he_lt hij_eq h12
              rw [← hij_eq] at h12
              simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h12
              rcases h12 with ⟨ha, hb⟩ | ⟨ha, hb⟩
              · exact ⟨⟨e, he_lt⟩, Or.inr (Or.inl ⟨t, ht, Or.inl ha, hb⟩)⟩
              · exact ⟨⟨e, he_lt⟩, Or.inr (Or.inl ⟨t, ht, Or.inr ha, hb⟩)⟩
            · obtain ⟨he_lt, _⟩ := List.getElem?_eq_some_iff.mp
                (List.mem_zipIdx_iff_getElem?.mp he_zip)
              dsimp only at he_lt hif
              split_ifs at hif with hlt_t
              · simp only [List.mem_singleton, Prod.mk.injEq] at hif
                exact ⟨⟨e, he_lt⟩, Or.inr (Or.inr ⟨t₁, t₂, hlt_t, ht₂, hif.1, hif.2⟩)⟩
              · simp at hif
          · rintro ⟨e, ⟨ha, hb⟩ | ⟨t, ht, ha_or, hb⟩ | ⟨t₁, t₂, h12, ht₂, ha, hb⟩⟩
            · exact ⟨(E[e.1], e.1),
                List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem e.2),
                Or.inl (Or.inl (List.mem_singleton.mpr (Prod.ext ha hb)))⟩
            · refine ⟨(E[e.1], e.1),
                List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem e.2),
                Or.inl (Or.inr ⟨t, ht, ?_⟩)⟩
              dsimp only [n] at hb
              rcases ha_or with ha | ha <;> simp [ha, hb]
            · refine ⟨(E[e.1], e.1),
                List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem e.2),
                Or.inr ⟨t₁, h12.trans ht₂, t₂, ht₂, ?_⟩⟩
              dsimp only [n] at ha hb
              simp [h12, ha, hb]
        have hE_lt_n : ∀ e : Fin m, (E[e.1]).1 < (E[e.1]).2 ∧ (E[e.1]).2 < n :=
          fun e ↦ ⟨(hE_edge e).1, (hE_edge e).2.1⟩
        cases x' with
        | inl u =>
          cases y' with
          | inl v =>
            dsimp only [invFun, attachEdgeCliques]
            constructor
            · intro hadj
              have hne_uv : u ≠ v := G.induced.ne_of_adj hadj
              have hne_idx : (eqvV.symm u).1 ≠ (eqvV.symm v).1 := fun h ↦
                hne_uv (by rw [← eqvV.apply_symm_apply u, ← eqvV.apply_symm_apply v, Fin.ext h])
              let e0 : G.induced.edgeSet := ⟨s(u, v), G.induced.mem_edgeSet.mpr hadj⟩
              let eIdx := eqvE.symm e0
              have hsym := Subtype.ext_iff.mp (eqvE.apply_symm_apply e0)
              dsimp only [edgeOfFin, e0] at hsym
              refine ⟨hne_idx, ?_⟩
              rcases Sym2.eq_iff.mp hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · have i1 := congrArg Fin.val (eqvV.symm_apply_eq.mpr h1.symm).symm
                have i2 := congrArg Fin.val (eqvV.symm_apply_eq.mpr h2.symm).symm
                exact Or.inl ((hmem_edges _ _).mpr ⟨eIdx, Or.inl ⟨i1.symm, i2.symm⟩⟩)
              · have i1 := congrArg Fin.val (eqvV.symm_apply_eq.mpr h1.symm).symm
                have i2 := congrArg Fin.val (eqvV.symm_apply_eq.mpr h2.symm).symm
                exact Or.inr ((hmem_edges _ _).mpr ⟨eIdx, Or.inl ⟨i1.symm, i2.symm⟩⟩)
            · rintro ⟨_, hfwd | hbwd⟩
              · obtain ⟨e, ⟨h1, h2⟩ | ⟨_, _, _, hb⟩ | ⟨_, _, _, _, _, hb⟩⟩ :=
                  (hmem_edges _ _).mp hfwd
                · have hu' : u = eqvV ⟨(E[e.1]).1, by have := hE_lt_n e; omega⟩ := by
                    have hfin : eqvV.symm u = ⟨(E[e.1]).1, by have := hE_lt_n e; omega⟩ :=
                      Fin.ext h1
                    rw [← hfin, eqvV.apply_symm_apply]
                  have hv' : v = eqvV ⟨(E[e.1]).2, (hE_lt_n e).2⟩ := by
                    have hfin : eqvV.symm v = ⟨(E[e.1]).2, (hE_lt_n e).2⟩ := Fin.ext h2
                    rw [← hfin, eqvV.apply_symm_apply]
                  rw [hu', hv']; exact (hE_edge e).2.2
                · have := (eqvV.symm v).2; omega
                · have := (eqvV.symm v).2; omega
              · obtain ⟨e, ⟨h1, h2⟩ | ⟨_, _, _, hb⟩ | ⟨_, _, _, _, _, hb⟩⟩ :=
                  (hmem_edges _ _).mp hbwd
                · have hv' : v = eqvV ⟨(E[e.1]).1, by have := hE_lt_n e; omega⟩ := by
                    have hfin : eqvV.symm v = ⟨(E[e.1]).1, by have := hE_lt_n e; omega⟩ :=
                      Fin.ext h1
                    rw [← hfin, eqvV.apply_symm_apply]
                  have hu' : u = eqvV ⟨(E[e.1]).2, (hE_lt_n e).2⟩ := by
                    have hfin : eqvV.symm u = ⟨(E[e.1]).2, (hE_lt_n e).2⟩ := Fin.ext h2
                    rw [← hfin, eqvV.apply_symm_apply]
                  rw [hu', hv']; exact (hE_edge e).2.2.symm
                · have := (eqvV.symm u).2; omega
                · have := (eqvV.symm u).2; omega
          | inr p =>
            rcases p with ⟨e, t⟩; dsimp only [invFun, attachEdgeCliques]
            have he_eq : e = edgeOfFin (eqvE.symm e) := (eqvE.apply_symm_apply e).symm
            constructor
            · intro hmem
              rw [he_eq] at hmem; dsimp only [edgeOfFin] at hmem; simp only [Sym2.mem_iff] at hmem
              refine ⟨by have := (eqvV.symm u).2; omega, Or.inl ((hmem_edges _ _).mpr
                ⟨eqvE.symm e, Or.inr (Or.inl ⟨t.1, t.2, ?_, rfl⟩)⟩)⟩
              rcases hmem with rfl | rfl
              · exact Or.inl (congrArg Fin.val (eqvV.symm_apply_apply _))
              · exact Or.inr (congrArg Fin.val (eqvV.symm_apply_apply _))
            · rintro ⟨_, hfwd | hbwd⟩
              · obtain ⟨e', ⟨_, h2⟩ | ⟨t', ht', ha_or, hb⟩ | ⟨_, _, _, _, ha, _⟩⟩ :=
                  (hmem_edges _ _).mp hfwd
                · have := (hE_lt_n e').2; omega
                · have d1 := hdiv_edge (eqvE.symm e).1 t.2
                  have d2 := hdiv_edge e'.1 ht'
                  rw [hb] at d1
                  have he'_eq : e' = eqvE.symm e := Fin.ext (d2.symm.trans d1)
                  subst he'_eq; rw [he_eq]; dsimp only [edgeOfFin]; simp only [Sym2.mem_iff]
                  rcases ha_or with h1 | h2
                  · left; rw [← eqvV.apply_symm_apply u]; congr 1; exact Fin.ext h1
                  · right; rw [← eqvV.apply_symm_apply u]; congr 1; exact Fin.ext h2
                · have := (eqvV.symm u).2; omega
              · obtain ⟨e', ⟨_, _⟩ | ⟨_, _, ha_or, _⟩ | ⟨_, _, _, _, _, _⟩⟩ :=
                  (hmem_edges _ _).mp hbwd
                · have := hE_lt_n e'; omega
                · rcases ha_or with ha | ha <;> (have := hE_lt_n e'; omega)
                · have := (eqvV.symm u).2; omega
        | inr p =>
          rcases p with ⟨e, t⟩
          cases y' with
          | inl v =>
            dsimp only [invFun, attachEdgeCliques]
            have he_eq : e = edgeOfFin (eqvE.symm e) := (eqvE.apply_symm_apply e).symm
            constructor
            · intro hmem
              rw [he_eq] at hmem; dsimp only [edgeOfFin] at hmem; simp only [Sym2.mem_iff] at hmem
              refine ⟨by have := (eqvV.symm v).2; omega, Or.inr ((hmem_edges _ _).mpr
                ⟨eqvE.symm e, Or.inr (Or.inl ⟨t.1, t.2, ?_, rfl⟩)⟩)⟩
              rcases hmem with rfl | rfl
              · exact Or.inl (congrArg Fin.val (eqvV.symm_apply_apply _))
              · exact Or.inr (congrArg Fin.val (eqvV.symm_apply_apply _))
            · rintro ⟨_, hfwd | hbwd⟩
              · obtain ⟨e', ⟨_, _⟩ | ⟨_, _, ha_or, _⟩ | ⟨_, _, _, _, _, _⟩⟩ :=
                  (hmem_edges _ _).mp hfwd
                · have := hE_lt_n e'; omega
                · rcases ha_or with ha | ha <;> (have := hE_lt_n e'; omega)
                · have := (eqvV.symm v).2; omega
              · obtain ⟨e', ⟨_, h2⟩ | ⟨t', ht', ha_or, hb⟩ | ⟨_, _, _, _, ha, _⟩⟩ :=
                  (hmem_edges _ _).mp hbwd
                · have := (hE_lt_n e').2; omega
                · have d1 := hdiv_edge (eqvE.symm e).1 t.2
                  have d2 := hdiv_edge e'.1 ht'
                  rw [hb] at d1
                  have he'_eq : e' = eqvE.symm e := Fin.ext (d2.symm.trans d1)
                  subst he'_eq; rw [he_eq]; dsimp only [edgeOfFin]; simp only [Sym2.mem_iff]
                  rcases ha_or with h1 | h2
                  · left; rw [← eqvV.apply_symm_apply v]; congr 1; exact Fin.ext h1
                  · right; rw [← eqvV.apply_symm_apply v]; congr 1; exact Fin.ext h2
                · have := (eqvV.symm v).2; omega
          | inr q =>
            rcases q with ⟨e₂, t₂⟩; dsimp only [invFun, attachEdgeCliques]
            constructor
            · rintro ⟨rfl, ht_ne⟩
              refine ⟨by omega, ?_⟩
              rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne ht_ne) with hlt | hgt
              · exact Or.inl ((hmem_edges _ _).mpr ⟨eqvE.symm e,
                  Or.inr (Or.inr ⟨t.1, t₂.1, hlt, t₂.2, rfl, rfl⟩)⟩)
              · exact Or.inr ((hmem_edges _ _).mpr ⟨eqvE.symm e,
                  Or.inr (Or.inr ⟨t₂.1, t.1, hgt, t.2, rfl, rfl⟩)⟩)
            · rintro ⟨hne_num, hfwd | hbwd⟩
              · obtain ⟨e', ⟨_, _⟩ | ⟨_, _, ha_or, _⟩ | ⟨s₁, s₂, hs12, hs2, ha, hb⟩⟩ :=
                  (hmem_edges _ _).mp hfwd
                · have := hE_lt_n e'; omega
                · rcases ha_or with ha | ha <;> (have := hE_lt_n e'; omega)
                · have d1 := hdiv_edge (eqvE.symm e).1 t.2
                  have d2 := hdiv_edge e'.1 (hs12.trans hs2); rw [ha] at d1
                  have e1 := hdiv_edge (eqvE.symm e₂).1 t₂.2
                  have e2 := hdiv_edge e'.1 hs2; rw [hb] at e1
                  have hee : e = e₂ :=
                    eqvE.symm.injective (Fin.ext ((d1.symm.trans d2).trans (e2.symm.trans e1)))
                  refine ⟨hee, fun htt ↦ ?_⟩; subst hee htt; exact hne_num rfl
              · obtain ⟨e', ⟨_, _⟩ | ⟨_, _, ha_or, _⟩ | ⟨s₁, s₂, hs12, hs2, ha, hb⟩⟩ :=
                  (hmem_edges _ _).mp hbwd
                · have := hE_lt_n e'; omega
                · rcases ha_or with ha | ha <;> (have := hE_lt_n e'; omega)
                · have e1 := hdiv_edge (eqvE.symm e₂).1 t₂.2
                  have e2 := hdiv_edge e'.1 (hs12.trans hs2); rw [ha] at e1
                  have d1 := hdiv_edge (eqvE.symm e).1 t.2
                  have d2 := hdiv_edge e'.1 hs2; rw [hb] at d1
                  have hee : e = e₂ :=
                    eqvE.symm.injective (Fin.ext ((d1.symm.trans d2).trans (e2.symm.trans e1)))
                  refine ⟨hee, fun htt ↦ ?_⟩; subst hee htt; exact hne_num rfl }

private theorem minDegree_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) : G.minDegree = H.minDegree := by
  classical
  have hdeg : ∀ u : V, G.degree u = H.degree (e u) := by
    intro u
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun v _ ↦ e v)
      (fun v hv ↦ (H.mem_neighborFinset _ _).mpr (e.map_rel_iff.mpr
        ((G.mem_neighborFinset _ _).mp hv)))
      (fun _ _ _ _ h ↦ e.injective h)
      (fun w hw ↦ ⟨e.symm w, by
        rw [G.mem_neighborFinset, ← e.map_rel_iff, e.apply_symm_apply]
        exact (H.mem_neighborFinset _ _).mp hw, e.apply_symm_apply w⟩)
  by_cases hV : Nonempty V
  · have _ : Nonempty V := hV
    have _ : Nonempty W := ⟨e (Classical.arbitrary V)⟩
    obtain ⟨u₀, hu₀⟩ := G.exists_minimal_degree_vertex
    obtain ⟨w₀, hw₀⟩ := H.exists_minimal_degree_vertex
    exact le_antisymm
      (by rw [hw₀, ← e.apply_symm_apply w₀, ← hdeg]; exact G.minDegree_le_degree _)
      (by rw [hu₀, hdeg u₀]; exact H.minDegree_le_degree _)
  · have _ : IsEmpty V := not_nonempty_iff.mp hV
    have _ : IsEmpty W := e.symm.isEmpty
    simp [SimpleGraph.minDegree]

private def pathThreeEncoded : Graph :=
  { vertices := [0, 1, 2], edges := [(0, 1), (1, 2)] }

/-- Total polynomial-time many-one reduction from `StableCutset` to `StableCutsetMinDeg c`. -/
def reduceToMinDeg (c : ℕ) (G : Graph) : Graph :=
  let V := G.distinctVertices
  if decide (V.length < 2) then { vertices := [], edges := [] }
  else if V.any fun u ↦ !(V.any fun w ↦ G.adjBool u w) then
    attachEdgeCliquesGraph c pathThreeEncoded
  else attachEdgeCliquesGraph c G

/-- For every constant `c > 1`, `StableCutset` reduces in polynomial time on multi-tape Turing
machines to `StableCutsetMinDeg c`. -/
theorem polyTimeReducible_StableCutset_StableCutsetMinDeg (c : ℕ) (hc : 1 < c) :
    PolyTimeReducible encGraph encGraph StableCutset (StableCutsetMinDeg c) := by
  have hc2 : 2 ≤ c := hc
  have hV := Graph.computableInPolyTime_distinctVertices
  have hlen := (ComputableInPolyTime.length_list encNat).comp hV
  have hiso_bool : ComputableInPolyTime
      (fun G : Graph ↦
        G.distinctVertices.any fun u ↦ !(G.distinctVertices.any fun w ↦ G.adjBool u w))
      encGraph encBool :=
    ComputableInPolyTime.anyWithInput hV (ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.anyWithInput (hV.comp (ComputableInPolyTime.fst _ _)) (by fun_prop)))
  have hred_poly : ComputableInPolyTime (reduceToMinDeg c) encGraph encGraph := by
    unfold reduceToMinDeg
    have hlt2 : ComputableInPolyTime (fun G : Graph ↦ decide (G.distinctVertices.length < 2))
        encGraph encBool := by fun_prop
    exact hlt2.ite (.const ({ vertices := [], edges := [] } : Graph))
      (hiso_bool.ite (.const (attachEdgeCliquesGraph c pathThreeEncoded))
        (computableInPolyTime_attachEdgeCliquesGraph c))
  refine ⟨reduceToMinDeg c, hred_poly, fun G ↦ ?_⟩
  have hattach_spec : ∀ H : Graph,
      2 ≤ H.distinctVertices.length →
      (∀ u ∈ H.distinctVertices, ∃ w ∈ H.distinctVertices, H.adjBool u w = true) →
      (attachEdgeCliquesGraph c H ∈ StableCutsetMinDeg c ↔ H ∈ StableCutset) := by
    intro H hH2 hHno_iso
    rw [mem_StableCutsetMinDeg_iff, mem_StableCutset_iff, mem_StableCutset_iff]
    let iso := attachEdgeCliquesGraphIso c H
    have hscs_iff : HasStableCutset (attachEdgeCliquesGraph c H).induced ↔
      HasStableCutset H.induced :=
      (hasStableCutset_iff_of_iso iso).trans (hasStableCutset_attachEdgeCliques_iff H.induced c)
    have h0_lt : 0 < H.distinctVertices.length := by omega
    have _ : Nonempty {w // w ∈ H.vertices} :=
      ⟨⟨H.distinctVertices[0], H.mem_distinctVertices.mp (List.getElem_mem h0_lt)⟩⟩
    have hmin1 : 1 ≤ H.induced.minDegree := by
      obtain ⟨u_min, hu_min⟩ := H.induced.exists_minimal_degree_vertex
      rw [hu_min, ← SimpleGraph.card_neighborFinset_eq_degree]
      obtain ⟨w, hwDV, hadjB⟩ := hHno_iso u_min.1 (H.mem_distinctVertices.mpr u_min.2)
      exact Finset.card_pos.mpr ⟨⟨w, H.mem_distinctVertices.mp hwDV⟩,
        (H.induced.mem_neighborFinset _ _).mpr ((H.adjBool_eq_true_iff _ _).mp hadjB)⟩
    have hmd_ge : c ≤ (attachEdgeCliquesGraph c H).induced.minDegree := by
      rw [minDegree_of_iso iso]
      exact minDegree_attachEdgeCliques_ge H.induced hc2 hmin1
    exact ⟨fun ⟨_, h⟩ ↦ hscs_iff.mp h, fun h ↦ ⟨hmd_ge, hscs_iff.mpr h⟩⟩
  dsimp only [reduceToMinDeg]
  by_cases hlt2 : G.distinctVertices.length < 2
  · simp only [hlt2, decide_true, ↓reduceIte]
    have hsub : Subsingleton {w // w ∈ G.vertices} := ⟨fun a b ↦ Subtype.ext (by
      have ha := G.mem_distinctVertices.mpr a.2
      have hb := G.mem_distinctVertices.mpr b.2
      rcases h : G.distinctVertices with _ | ⟨x, _ | ⟨y, ys⟩⟩
      · simp [h] at ha
      · simp only [h, List.mem_singleton] at ha hb; exact ha.trans hb.symm
      · simp [h] at hlt2)⟩
    have hnG : G ∉ StableCutset := by
      rw [mem_StableCutset_iff]
      exact @not_hasStableCutset_of_subsingleton _ hsub _
    have hnEmpty : ({ vertices := [], edges := [] } : Graph) ∉ StableCutsetMinDeg c := by
      rintro ⟨hmd, _⟩
      have _ : IsEmpty {w // w ∈ ([] : List ℕ)} := ⟨fun w ↦ List.not_mem_nil w.2⟩
      have : ({ vertices := [], edges := [] } : Graph).induced.minDegree = 0 := by
        simp [SimpleGraph.minDegree]
      omega
    exact iff_of_false hnG hnEmpty
  · simp only [hlt2, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hge2 : 2 ≤ G.distinctVertices.length := by omega
    by_cases hiso : (G.distinctVertices.any fun u ↦
        !(G.distinctVertices.any fun w ↦ G.adjBool u w)) = true
    · rw [ite_eq_left hiso]
      have hG_yes : G ∈ StableCutset := by
        rw [mem_StableCutset_iff]
        simp only [List.any_eq_true, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true] at hiso
        obtain ⟨u, huDV, hno_w'⟩ := hiso
        let u' : {x // x ∈ G.vertices} := ⟨u, G.mem_distinctVertices.mp huDV⟩
        obtain ⟨v, hvDV, hvu⟩ : ∃ v ∈ G.distinctVertices, v ≠ u := by
          rcases h : G.distinctVertices with _ | ⟨a, _ | ⟨b, bs⟩⟩
          · simp [h] at hge2
          · simp [h] at hge2
          · have hnd := G.nodup_distinctVertices; rw [h] at hnd
            have hab : a ≠ b := fun heq ↦ (List.nodup_cons.mp hnd).1 (by simp [heq])
            by_cases hau : a = u
            · exact ⟨b, by simp, fun hbu ↦ hab (hau.trans hbu.symm)⟩
            · exact ⟨a, by simp, hau⟩
        let v' : {x // x ∈ G.vertices} := ⟨v, G.mem_distinctVertices.mp hvDV⟩
        refine ⟨∅, by simp, {u'}, {x | x ≠ u'}, ⟨u', rfl⟩,
          ⟨v', fun h ↦ hvu (congrArg Subtype.val h)⟩,
          Set.disjoint_left.mpr fun _ h1 h2 ↦ h2 h1, by ext x; simp [em], fun a ha b _ hadj ↦ ?_⟩
        rw [Set.mem_singleton_iff] at ha; subst ha
        have hadjB := (G.adjBool_eq_true_iff u b.1).mpr hadj
        rw [hno_w' b.1 (G.mem_distinctVertices.mpr b.2)] at hadjB
        exact Bool.false_ne_true hadjB
      have hP3_yes : attachEdgeCliquesGraph c pathThreeEncoded ∈ StableCutsetMinDeg c := by
        refine (hattach_spec pathThreeEncoded (by decide) ?_).mpr ?_
        · intro u hu
          have hdv : pathThreeEncoded.distinctVertices = [0, 1, 2] := by decide
          rw [hdv] at hu ⊢
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl
          · exact ⟨1, by decide, by decide⟩
          · exact ⟨0, by decide, by decide⟩
          · exact ⟨1, by decide, by decide⟩
        · rw [mem_StableCutset_iff]
          refine ⟨{⟨1, by decide⟩}, ?_, {⟨0, by decide⟩}, {⟨2, by decide⟩},
            ⟨_, rfl⟩, ⟨_, rfl⟩,
            Set.disjoint_singleton.mpr
              (fun h ↦ absurd (congrArg Subtype.val h : (0 : ℕ) = 2) (by decide)),
            ?_, ?_⟩
          · intro a ha b hb hab
            rw [Set.mem_singleton_iff] at ha hb
            exact (hab (ha.trans hb.symm)).elim
          · ext ⟨x, hx⟩
            simp only [pathThreeEncoded, List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl <;> simp [Subtype.ext_iff]
          · intro a ha b hb hadj
            rw [Set.mem_singleton_iff] at ha hb; subst ha hb
            have : ¬ pathThreeEncoded.toSimpleGraph.Adj 0 2 := by
              simp [pathThreeEncoded, Graph.toSimpleGraph_adj]
            exact this hadj
      exact iff_of_true hG_yes hP3_yes
    · rw [ite_eq_right hiso]
      have hno_iso : ∀ u ∈ G.distinctVertices, ∃ w ∈ G.distinctVertices, G.adjBool u w = true := by
        intro u hu; by_contra hno; push Not at hno
        apply hiso; rw [List.any_eq_true]
        refine ⟨u, hu, ?_⟩
        rw [Bool.not_eq_true', List.any_eq_false]
        intro w hw htr; exact hno w hw htr
      exact (hattach_spec G hge2 hno_iso).symm

end CslibFrontier.Complexity
