/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Complexity.Problems.SharpTwoSAT
public import Mathlib.Combinatorics.SimpleGraph.Clique

import CslibFrontier.Computability.Complexity.CookLevin.Counting
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.Polynomial.FiniteDifference
import CslibFrontier.Logics.Propositional.CNF
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Tactic.PolyTime
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Basic

/-!
# `#P`-Completeness of Counting Independent Sets (`#IndependentSet`)

This module formalizes the counting problem `#IndependentSet` (`SharpIndepSet`) on encoded simple
graphs (`Cslib.Complexity.Graph` under `encGraph`), proving under standard Lean axioms that
`SharpIndepSet` belongs to `#P` and is `#P`-complete under polynomial-time counting Turing
reductions (`CountingTuringComplete`), and that a polynomial-time algorithm for `SharpIndepSet`
implies `P = NP`.

## Main definitions

- `CslibFrontier.Complexity.graphDecoder`: polynomial-time total decoder for `encGraph`.
- `CslibFrontier.Complexity.indepFinsets`, `CslibFrontier.Complexity.SharpIndepSet`: the finite set
  and count
  of independent subsets of declared vertices of a graph `G`.
- `CslibFrontier.Complexity.twoSATIndepGraph`: block-clique interpolation graph `G(φ, r)` for a
  `2-CNF`
  formula `φ` at slack parameter `r : ℕ`.

## Main results

- `CslibFrontier.Complexity.mem_indepFinsets_iff`: characterization of `indepFinsets G`.
- `CslibFrontier.Complexity.sharpP_of_distinctVertices_filter`,
  `CslibFrontier.Complexity.SharpIndepSet_mem_SharpP`: `SharpIndepSet ∈ SharpP encGraph`.
- `CslibFrontier.Complexity.countingTuringReducible_SharpTwoSAT_SharpIndepSet`,
  `CslibFrontier.Complexity.countingTuringReducible_SharpSAT_SharpIndepSet`: polynomial-time
  counting
  Turing reductions `#2SAT ≤_T^#P #IndependentSet` and `#SAT ≤_T^#P #IndependentSet`.
- `CslibFrontier.Complexity.SharpIndepSet_countingTuringComplete`: `#P`-completeness of
  `SharpIndepSet`.
- `CslibFrontier.Complexity.countingTuringHard_of_add_offset_SharpIndepSet`: transfer of
  `#P`-hardness
  from `SharpIndepSet` along polynomial-time reductions with `{0, 1}` count offsets.
- `CslibFrontier.Complexity.SharpIndepSet_polyTime_implies_P_eq_NP`: if `SharpIndepSet ∈ FP`, then
  `P = NP`.

## Tags

computational complexity, SharpP, counting complexity, independent set
-/

public section

namespace CslibFrontier.Complexity

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Graph decoder and independent set counts -/

/-- Total polynomial-time decoder for `Cslib.Complexity.encGraph`. -/
def graphDecoder : Decoder encGraph :=
  ((Decoder.list .nat).pair (.list (.pair .nat .nat))).map
    (fun p ↦ ⟨p.1, p.2⟩) (fun G ↦ (G.vertices, G.edges))
    (fun _ ↦ rfl) (fun p ↦ encGraph_apply ⟨p.1, p.2⟩)

/-- The finite set of all independent subsets of declared vertices of `G`. -/
@[expose] def indepFinsets (G : Graph) : Finset (Finset ℕ) :=
  G.distinctVertices.toFinset.powerset.filter fun S ↦
    ∀ u ∈ S, ∀ v ∈ S, G.adjBool u v = false

/-- Membership in `indepFinsets G`: subsets of `G.vertices` that are independent in
`G.toSimpleGraph`. -/
theorem mem_indepFinsets_iff {G : Graph} {S : Finset ℕ} :
    S ∈ indepFinsets G ↔ (∀ v ∈ S, v ∈ G.vertices) ∧ G.toSimpleGraph.IsIndepSet (S : Set ℕ) := by
  simp only [indepFinsets, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff,
    List.mem_toFinset, Graph.mem_distinctVertices, Graph.adjBool_eq_false_iff,
    SimpleGraph.IsIndepSet, Set.Pairwise, Finset.mem_coe]
  refine and_congr_right fun _ ↦ ⟨fun h u hu v hv _ ↦ h u hu v hv, fun h u hu v hv ↦ ?_⟩
  by_cases huv : u = v
  · exact huv ▸ G.toSimpleGraph.loopless.irrefl u
  · exact h hu hv huv

/-- Number of independent subsets of declared vertices of `G` (`#IndependentSet`). -/
def SharpIndepSet (G : Graph) : ℕ :=
  (indepFinsets G).card

/-- The cardinality of `indepFinsets G` is `SharpIndepSet G`. -/
theorem card_indepFinsets (G : Graph) : (indepFinsets G).card = SharpIndepSet G := by rfl

/-! ### Membership in `#P` for subset-counting problems on `distinctVertices` -/

private def canonicalGraphMask (G : Graph) (w : List Bool) : Bool :=
  (List.range w.length).all fun i ↦ !w.getD i false || decide (i < G.distinctVertices.length)

private lemma canonicalGraphMask_eq_true_iff {G : Graph} {w : List Bool} :
    canonicalGraphMask G w = true ↔
      ∀ i < w.length, w.getD i false = true → i < G.distinctVertices.length := by
  simp only [canonicalGraphMask, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq]
  exact forall₂_congr fun i _ ↦ by cases w.getD i false <;> simp

private lemma computableInPolyTime_canonicalGraphMask :
    ComputableInPolyTime (fun p : Graph × List Bool ↦ canonicalGraphMask p.1 p.2)
      (encPair encGraph encBits) encBool := by
  unfold canonicalGraphMask
  have hdvLen : ComputableInPolyTime
      (fun q : (Graph × List Bool) × ℕ ↦ q.1.1.distinctVertices.length)
      (encPair (encPair encGraph encBits) encUnary) encUnary :=
    (ComputableInPolyTime.length encNat).comp
      (Graph.computableInPolyTime_distinctVertices.comp
        (ComputableInPolyTime.fst (encPair encGraph encBits) encUnary).fst')
  refine ComputableInPolyTime.allWithInput (encA := encUnary) (by fun_prop) ?_
  exact ComputableInPolyTime.bool_or.comp
    ((ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.bitsGetDWithInput
        (ComputableInPolyTime.fst (encPair encGraph encBits) encUnary).snd'
        (ComputableInPolyTime.snd (encPair encGraph encBits) encUnary) false)).prod
      (ComputableInPolyTime.unary_lt'
        (ComputableInPolyTime.snd (encPair encGraph encBits) encUnary) hdvLen))

/-- Any graph-subset counting function over `G.distinctVertices` whose subset predicate is decided
in polynomial time on duplicate-free vertex lists belongs to `SharpP encGraph`. -/
theorem sharpP_of_distinctVertices_filter
    (P : Graph → Finset ℕ → Prop) [∀ G, DecidablePred (P G)]
    (check : Graph × List ℕ → Bool)
    (hcheck : ComputableInPolyTime check (encWithEntries encGraph encNat) encBool)
    (hP : ∀ G (l : List ℕ), l.Nodup → (∀ v ∈ l, v ∈ G.distinctVertices) →
      (check (G, l) = true ↔ P G l.toFinset)) :
    (fun G : Graph ↦ (G.distinctVertices.toFinset.powerset.filter (P G)).card) ∈
      SharpP encGraph := by
  let V (x : Graph × List Bool) : Bool :=
    subsetVerifier Graph.distinctVertices check x && canonicalGraphMask x.1 x.2
  have hV : ComputableInPolyTime V (encPair encGraph encBits) encBool :=
    ComputableInPolyTime.bool_and'
      (computableInPolyTime_subsetVerifier Graph.computableInPolyTime_distinctVertices hcheck)
      computableInPolyTime_canonicalGraphMask
  refine ⟨Polynomial.X, V, hV, fun G ↦ ?_⟩
  simp only [Polynomial.eval_X]
  let L := (encGraph G).length
  let dv := G.distinctVertices
  have hdv_le : dv.length ≤ L := G.length_distinctVertices_le
  have hdv_nd : dv.Nodup := G.nodup_distinctVertices
  rw [acceptCount]
  refine Finset.card_bij
    (fun S _ ↦ fun i : Fin L ↦ if h : i.val < dv.length then decide (dv[i.val] ∈ S) else false)
    (fun S hS ↦ ?_) (fun S₁ hS₁ S₂ hS₂ heq ↦ ?_) (fun w hw ↦ ?_)
  · simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ, true_and] at hS ⊢
    let wFn : Fin L → Bool :=
      fun i ↦ if h : i.val < dv.length then decide (dv[i.val] ∈ S) else false
    have hsel_sub : ∀ v ∈ selectDistinct dv (List.ofFn wFn), v ∈ dv :=
      fun _ hv ↦ (mem_selectDistinct.mp hv).1
    have hsel_eq : (selectDistinct dv (List.ofFn wFn)).toFinset = S := by
      ext v
      rw [List.mem_toFinset, mem_selectDistinct]
      constructor
      · rintro ⟨hv, hbit⟩
        have hidx : dv.idxOf v < dv.length := List.idxOf_lt_length_iff.mpr hv
        have hidxL : dv.idxOf v < L := hidx.trans_le hdv_le
        rw [List.getD_ofFn_of_lt wFn hidxL false] at hbit
        simp only [wFn, hidx, ↓reduceDIte, List.getElem_idxOf hidx, decide_eq_true_eq] at hbit
        exact hbit
      · intro hvS
        have hv : v ∈ dv := List.mem_toFinset.mp (hS.1 hvS)
        have hidx : dv.idxOf v < dv.length := List.idxOf_lt_length_iff.mpr hv
        have hidxL : dv.idxOf v < L := hidx.trans_le hdv_le
        refine ⟨hv, ?_⟩
        rw [List.getD_ofFn_of_lt wFn hidxL false]
        simp only [wFn, hidx, ↓reduceDIte, List.getElem_idxOf hidx, decide_eq_true_eq]
        exact hvS
    simp only [V, subsetVerifier, Bool.and_eq_true]
    refine ⟨?_, canonicalGraphMask_eq_true_iff.mpr fun i hi htrue ↦ ?_⟩
    · rw [hP G _ (nodup_selectDistinct _ _) hsel_sub, hsel_eq]
      exact hS.2
    · rw [List.length_ofFn] at hi
      rw [List.getD_ofFn_of_lt wFn hi false] at htrue
      by_contra hge
      change ¬i < dv.length at hge
      simp only [wFn, hge, ↓reduceDIte, Bool.false_eq_true] at htrue
  · simp only [Finset.mem_filter, Finset.mem_powerset] at hS₁ hS₂
    ext v
    constructor <;> intro hvS
    · have hv : v ∈ dv := List.mem_toFinset.mp (hS₁.1 hvS)
      have hidx : dv.idxOf v < dv.length := List.idxOf_lt_length_iff.mpr hv
      have hval := congrFun heq ⟨dv.idxOf v, hidx.trans_le hdv_le⟩
      simp only [hidx, ↓reduceDIte, List.getElem_idxOf hidx, hvS, decide_true] at hval
      exact of_decide_eq_true hval.symm
    · have hv : v ∈ dv := List.mem_toFinset.mp (hS₂.1 hvS)
      have hidx : dv.idxOf v < dv.length := List.idxOf_lt_length_iff.mpr hv
      have hval := (congrFun heq ⟨dv.idxOf v, hidx.trans_le hdv_le⟩).symm
      simp only [hidx, ↓reduceDIte, List.getElem_idxOf hidx, hvS, decide_true] at hval
      exact of_decide_eq_true hval.symm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, V, subsetVerifier,
      Bool.and_eq_true] at hw
    let S := (selectDistinct dv (List.ofFn w)).toFinset
    have hsel_sub : ∀ v ∈ selectDistinct dv (List.ofFn w), v ∈ dv :=
      fun _ hv ↦ (mem_selectDistinct.mp hv).1
    have hS_sub : S ⊆ dv.toFinset := fun v hv ↦
      List.mem_toFinset.mpr (hsel_sub v (List.mem_toFinset.mp hv))
    have hS_P : P G S := (hP G _ (nodup_selectDistinct _ _) hsel_sub).mp hw.1
    refine ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS_sub, hS_P⟩, funext fun i ↦ ?_⟩
    by_cases hi : i.val < dv.length
    · simp only [hi, ↓reduceDIte]
      have hidx : dv.idxOf dv[i.val] = i.val := hdv_nd.idxOf_getElem i.val hi
      have hmemS : dv[i.val] ∈ S ↔ w i = true := by
        rw [List.mem_toFinset, mem_selectDistinct]
        simp only [List.getElem_mem hi, true_and, hidx, List.getD_ofFn]
      cases hwi : w i <;> simp [hmemS, hwi]
    · simp only [hi, ↓reduceDIte]
      cases hwi : w i
      · rfl
      · have hcan := canonicalGraphMask_eq_true_iff.mp hw.2 i.val
          (by rw [List.length_ofFn]; exact i.isLt)
          (by rw [List.getD_ofFn, hwi])
        exact False.elim (hi hcan)

/-- Any counting function filtering `indepFinsets G` by a predicate decided in polynomial time on
duplicate-free independent vertex lists belongs to `SharpP encGraph`. -/
theorem sharpP_of_indepFinsets_filter
    (P : Graph → Finset ℕ → Prop) [∀ G, DecidablePred (P G)]
    (check : Graph × List ℕ → Bool)
    (hcheck : ComputableInPolyTime check (encWithEntries encGraph encNat) encBool)
    (hP : ∀ G (l : List ℕ), l.Nodup → (∀ v ∈ l, v ∈ G.distinctVertices) →
      (∀ u ∈ l, ∀ v ∈ l, G.adjBool u v = false) → (check (G, l) = true ↔ P G l.toFinset)) :
    (fun G : Graph ↦ ((indepFinsets G).filter (P G)).card) ∈ SharpP encGraph := by
  let fullCheck (p : Graph × List ℕ) : Bool :=
    (p.2.all fun u ↦ p.2.all fun v ↦ !p.1.adjBool u v) && check p
  have hfull : ComputableInPolyTime fullCheck (encWithEntries encGraph encNat) encBool := by
    have hind : ComputableInPolyTime
        (fun p : Graph × List ℕ ↦ p.2.all fun u ↦ p.2.all fun v ↦ !p.1.adjBool u v)
        (encWithEntries encGraph encNat) encBool := by
      unfold encWithEntries
      fun_prop
    exact hind.bool_and' hcheck
  have heq : (fun G : Graph ↦ ((indepFinsets G).filter (P G)).card) =
      fun G : Graph ↦ (G.distinctVertices.toFinset.powerset.filter fun S ↦
        (∀ u ∈ S, ∀ v ∈ S, G.adjBool u v = false) ∧ P G S).card := by
    funext G; simp only [indepFinsets, Finset.filter_filter]
  rw [heq]
  refine sharpP_of_distinctVertices_filter _ fullCheck hfull fun G l hnd hsub ↦ ?_
  simp only [fullCheck, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.mem_toFinset]
  exact and_congr_right fun hind ↦ hP G l hnd hsub hind

/-- `#IndependentSet` belongs to `#P`. -/
theorem SharpIndepSet_mem_SharpP : SharpIndepSet ∈ SharpP encGraph := by
  simpa only [Finset.filter_true, card_indepFinsets] using
    sharpP_of_indepFinsets_filter (fun _ _ ↦ True) (fun _ ↦ true)
      (ComputableInPolyTime.const true) (fun _ _ _ _ _ ↦ by simp)

/-! ### Block-clique `2-CNF` interpolation `#2SAT ≤_T^#P #IndependentSet` -/

private def nodeId (r i k : ℕ) : ℕ :=
  i * (r + 2) + k

private lemma nodeId_div_mod (i : ℕ) {r k : ℕ} (hk : k < r + 2) :
    nodeId r i k / (r + 2) = i ∧ nodeId r i k % (r + 2) = k :=
  (Nat.div_mod_unique (by omega)).mpr ⟨by unfold nodeId; rw [Nat.mul_comm]; omega, hk⟩

private lemma nodeId_inj {r i₁ k₁ i₂ k₂ : ℕ} (hk₁ : k₁ < r + 2) (hk₂ : k₂ < r + 2)
    (h : nodeId r i₁ k₁ = nodeId r i₂ k₂) : i₁ = i₂ ∧ k₁ = k₂ := by
  have h₁ := nodeId_div_mod i₁ hk₁
  have h₂ := nodeId_div_mod i₂ hk₂
  rw [h] at h₁
  exact ⟨h₁.1.symm.trans h₂.1, h₁.2.symm.trans h₂.2⟩

private def litAllowed (φ : CNF ℕ) (v : ℕ) (b : Bool) : Bool :=
  !φ.any fun c ↦ !c.isEmpty && c.all fun l ↦ decide (l = (v, !b))

private lemma bool_toNat_lt_add_two (b : Bool) (r : ℕ) : b.toNat < r + 2 := by
  cases b <;> exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 r)

private lemma litAllowed_eq_true_iff {φ : CNF ℕ} {v : ℕ} {b : Bool} :
    litAllowed φ v b = true ↔ ¬∃ c ∈ φ, c ≠ [] ∧ ∀ l ∈ c, l = (v, !b) := by
  unfold litAllowed
  rw [Bool.not_eq_true', List.any_eq_false]
  constructor
  · intro h ⟨c, hc, hne, hall⟩
    refine h c hc ?_
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      decide_eq_true_eq]
    exact ⟨hne, hall⟩
  · intro h c hc hbad
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      decide_eq_true_eq] at hbad
    exact h ⟨c, hc, hbad.1, hbad.2⟩

private def blockVertices (φ : CNF ℕ) (r i v : ℕ) : List ℕ :=
  (if litAllowed φ v false then [nodeId r i 0] else []) ++
    (if litAllowed φ v true then [nodeId r i 1] else []) ++
    ((List.range r).map fun j ↦ nodeId r i (j + 2))

private def blockEdges (φ : CNF ℕ) (r i v : ℕ) : List (ℕ × ℕ) :=
  let vs := blockVertices φ r i v
  vs.flatMap fun u ↦ vs.map fun w ↦ (u, w)

private def clauseConflictEdges (φ : CNF ℕ) (r : ℕ) : List (ℕ × ℕ) :=
  let dv := φ.distinctVars
  φ.flatMap fun c ↦
    c.flatMap fun l₁ ↦
      c.flatMap fun l₂ ↦
        if decide (l₁.1 ≠ l₂.1) then
          [(nodeId r (dv.idxOf l₁.1) (!l₁.2).toNat, nodeId r (dv.idxOf l₂.1) (!l₂.2).toNat)]
        else []

/-- Block-clique interpolation graph `G(φ, r)` for a `2-CNF` formula `φ` and slack parameter `r`:
each occurring variable `v_i` receives a clique on its allowed literal nodes (`(i, false)`,
`(i, true)`) together with `r` auxiliary slack vertices, and each `2`-variable clause adds a
conflict edge between its two falsifying literal nodes. -/
def twoSATIndepGraph (φ : CNF ℕ) (r : ℕ) : Graph where
  vertices := φ.distinctVars.zipIdx.flatMap fun vi ↦ blockVertices φ r vi.2 vi.1
  edges := (φ.distinctVars.zipIdx.flatMap fun vi ↦ blockEdges φ r vi.2 vi.1) ++
    clauseConflictEdges φ r

private lemma mem_blockVertices_iff {φ : CNF ℕ} {r i v w : ℕ} :
    w ∈ blockVertices φ r i v ↔
      (∃ b : Bool, litAllowed φ v b = true ∧ w = nodeId r i b.toNat) ∨
        ∃ j < r, w = nodeId r i (j + 2) := by
  simp only [blockVertices, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro ((hw | hw) | ⟨j, hj, rfl⟩)
    · split_ifs at hw with h0
      · simp only [List.mem_singleton] at hw
        exact Or.inl ⟨false, h0, hw⟩
      · exact False.elim (List.not_mem_nil hw)
    · split_ifs at hw with h1
      · simp only [List.mem_singleton] at hw
        exact Or.inl ⟨true, h1, hw⟩
      · exact False.elim (List.not_mem_nil hw)
    · exact Or.inr ⟨j, hj, rfl⟩
  · rintro (⟨b, hb, rfl⟩ | ⟨j, hj, rfl⟩)
    · cases b
      · exact Or.inl (Or.inl (by simp [hb]))
      · exact Or.inl (Or.inr (by simp [hb]))
    · exact Or.inr ⟨j, hj, rfl⟩

private lemma div_of_mem_blockVertices {φ : CNF ℕ} {r i v w : ℕ}
    (hw : w ∈ blockVertices φ r i v) : w / (r + 2) = i ∧ w % (r + 2) < r + 2 := by
  rcases mem_blockVertices_iff.mp hw with ⟨b, _, rfl⟩ | ⟨j, hj, rfl⟩
  · have hb : b.toNat < r + 2 := bool_toNat_lt_add_two b r
    exact ⟨(nodeId_div_mod i hb).1, by rw [(nodeId_div_mod i hb).2]; exact hb⟩
  · have hj' : j + 2 < r + 2 := by omega
    exact ⟨(nodeId_div_mod i hj').1, by rw [(nodeId_div_mod i hj').2]; exact hj'⟩

private lemma mem_vertices_twoSATIndepGraph {φ : CNF ℕ} {r w : ℕ} :
    w ∈ (twoSATIndepGraph φ r).vertices ↔
      ∃ (i : ℕ) (hi : i < φ.distinctVars.length),
        w ∈ blockVertices φ r i (φ.distinctVars[i]'hi) := by
  simp only [twoSATIndepGraph, List.mem_flatMap, List.mem_zipIdx_iff_getElem?, Prod.exists]
  constructor
  · rintro ⟨v, i, hget, hw⟩
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hget
    exact ⟨i, hi, hw⟩
  · rintro ⟨i, hi, hw⟩
    exact ⟨φ.distinctVars[i]'hi, i, List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩, hw⟩

private lemma block_clique_adj {φ : CNF ℕ} {r i : ℕ} (hi : i < φ.distinctVars.length)
    {u w : ℕ} (hu : u ∈ blockVertices φ r i (φ.distinctVars[i]'hi))
    (hw : w ∈ blockVertices φ r i (φ.distinctVars[i]'hi)) (hne : u ≠ w) :
    (twoSATIndepGraph φ r).toSimpleGraph.Adj u w := by
  rw [Graph.toSimpleGraph_adj]
  refine ⟨hne, Or.inl (List.mem_append_left _ (List.mem_flatMap.mpr ?_))⟩
  refine ⟨(φ.distinctVars[i]'hi, i),
    List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩), ?_⟩
  dsimp only [blockEdges]
  exact List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨w, hw, rfl⟩⟩

private lemma adj_diff_blocks_iff {φ : CNF ℕ} {r i₁ i₂ k₁ k₂ : ℕ}
    (hk₁ : k₁ < r + 2) (hk₂ : k₂ < r + 2) (hi : i₁ ≠ i₂) :
    (twoSATIndepGraph φ r).toSimpleGraph.Adj (nodeId r i₁ k₁) (nodeId r i₂ k₂) ↔
      ∃ c ∈ φ, ∃ l₁ ∈ c, ∃ l₂ ∈ c, l₁.1 ≠ l₂.1 ∧
        i₁ = φ.distinctVars.idxOf l₁.1 ∧ k₁ = (!l₁.2).toNat ∧
        i₂ = φ.distinctVars.idxOf l₂.1 ∧ k₂ = (!l₂.2).toNat := by
  have hne : nodeId r i₁ k₁ ≠ nodeId r i₂ k₂ := fun heq ↦ hi (nodeId_inj hk₁ hk₂ heq).1
  rw [Graph.toSimpleGraph_adj, and_iff_right hne]
  have hnot_blk {u w : ℕ} (hdiv : u / (r + 2) ≠ w / (r + 2)) :
      (u, w) ∉ φ.distinctVars.zipIdx.flatMap fun vi ↦ blockEdges φ r vi.2 vi.1 := by
    intro hmem
    obtain ⟨⟨v, i⟩, _, hbe⟩ := List.mem_flatMap.mp hmem
    dsimp only [blockEdges] at hbe
    obtain ⟨u', hu', hmap⟩ := List.mem_flatMap.mp hbe
    obtain ⟨w', hw', heq⟩ := List.mem_map.mp hmap
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact hdiv ((div_of_mem_blockVertices hu').1.trans (div_of_mem_blockVertices hw').1.symm)
  have hd₁ : nodeId r i₁ k₁ / (r + 2) = i₁ := (nodeId_div_mod i₁ hk₁).1
  have hd₂ : nodeId r i₂ k₂ / (r + 2) = i₂ := (nodeId_div_mod i₂ hk₂).1
  have hnb₁ : (nodeId r i₁ k₁, nodeId r i₂ k₂) ∉
      φ.distinctVars.zipIdx.flatMap fun vi ↦ blockEdges φ r vi.2 vi.1 :=
    hnot_blk (by rw [hd₁, hd₂]; exact hi)
  have hnb₂ : (nodeId r i₂ k₂, nodeId r i₁ k₁) ∉
      φ.distinctVars.zipIdx.flatMap fun vi ↦ blockEdges φ r vi.2 vi.1 :=
    hnot_blk (by rw [hd₂, hd₁]; exact hi.symm)
  simp only [twoSATIndepGraph, List.mem_append, hnb₁, hnb₂, false_or,
    clauseConflictEdges, List.mem_flatMap]
  constructor
  · rintro (⟨c, hc, l₁, hl₁, l₂, hl₂, hif⟩ | ⟨c, hc, l₂, hl₂, l₁, hl₁, hif⟩)
    · split_ifs at hif with hdv
      · simp only [List.mem_singleton, Prod.mk.injEq] at hif
        have hbl₁ : (!l₁.2).toNat < r + 2 := bool_toNat_lt_add_two (!l₁.2) r
        have hbl₂ : (!l₂.2).toNat < r + 2 := bool_toNat_lt_add_two (!l₂.2) r
        obtain ⟨hi₁, hk₁'⟩ := nodeId_inj hk₁ hbl₁ hif.1
        obtain ⟨hi₂, hk₂'⟩ := nodeId_inj hk₂ hbl₂ hif.2
        exact ⟨c, hc, l₁, hl₁, l₂, hl₂, of_decide_eq_true hdv, hi₁, hk₁', hi₂, hk₂'⟩
      · exact False.elim (List.not_mem_nil hif)
    · split_ifs at hif with hdv
      · simp only [List.mem_singleton, Prod.mk.injEq] at hif
        have hbl₁ : (!l₁.2).toNat < r + 2 := bool_toNat_lt_add_two (!l₁.2) r
        have hbl₂ : (!l₂.2).toNat < r + 2 := bool_toNat_lt_add_two (!l₂.2) r
        obtain ⟨hi₂, hk₂'⟩ := nodeId_inj hk₂ hbl₂ hif.1
        obtain ⟨hi₁, hk₁'⟩ := nodeId_inj hk₁ hbl₁ hif.2
        exact ⟨c, hc, l₁, hl₁, l₂, hl₂, (of_decide_eq_true hdv).symm, hi₁, hk₁', hi₂, hk₂'⟩
      · exact False.elim (List.not_mem_nil hif)
  · rintro ⟨c, hc, l₁, hl₁, l₂, hl₂, hneq, rfl, rfl, rfl, rfl⟩
    exact Or.inl ⟨c, hc, l₁, hl₁, l₂, hl₂, by simp [hneq]⟩

private def validPartial (φ : CNF ℕ) (τ : Fin φ.distinctVars.length → Option Bool) : Prop :=
  (∀ i : Fin φ.distinctVars.length, ∀ b : Bool,
    τ i = some b → litAllowed φ φ.distinctVars[i.val] b = true) ∧
  ∀ c ∈ φ, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.1 ≠ l₂.1 →
    ∀ (h₁ : φ.distinctVars.idxOf l₁.1 < φ.distinctVars.length)
      (h₂ : φ.distinctVars.idxOf l₂.1 < φ.distinctVars.length),
      ¬(τ ⟨φ.distinctVars.idxOf l₁.1, h₁⟩ = some (!l₁.2) ∧
        τ ⟨φ.distinctVars.idxOf l₂.1, h₂⟩ = some (!l₂.2))

private noncomputable instance instDecidablePredValidPartial (φ : CNF ℕ) :
    DecidablePred (validPartial φ) :=
  Classical.decPred _

private def blockSlackPred (r : ℕ) (optB : Option Bool) (s : Option (Fin r)) : Prop :=
  optB.isSome = true → s = none

private instance instDecidablePredBlockSlackPred (r : ℕ) (optB : Option Bool) :
    DecidablePred (blockSlackPred r optB) :=
  fun _ ↦ inferInstanceAs (Decidable (_ → _))

private lemma card_blockSlackPred (r : ℕ) (optB : Option Bool) :
    Fintype.card {s : Option (Fin r) // blockSlackPred r optB s} =
      if optB = none then r + 1 else 1 := by
  cases optB with
  | none =>
    simp only [↓reduceIte]
    have heq : Fintype.card {s : Option (Fin r) // blockSlackPred r none s} =
        Fintype.card (Option (Fin r)) :=
      Fintype.card_congr
        ⟨fun x ↦ x.1, fun s ↦ ⟨s, fun h ↦ Bool.noConfusion h⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
    rw [heq, Fintype.card_option, Fintype.card_fin]
  | some b =>
    have huniq : Unique {s : Option (Fin r) // blockSlackPred r (some b) s} :=
      { default := ⟨none, fun _ ↦ rfl⟩
        uniq := fun ⟨s, hs⟩ ↦ Subtype.ext (hs rfl) }
    simpa only [reduceCtorEq, ↓reduceIte] using Fintype.card_unique

private def finsetOfConfig (N r : ℕ) (τ : Fin N → Option Bool) (s : Fin N → Option (Fin r)) :
    Finset ℕ :=
  Finset.univ.biUnion fun i : Fin N ↦
    match τ i, s i with
    | some b, _ => {nodeId r i.val b.toNat}
    | none, some j => {nodeId r i.val (j.val + 2)}
    | none, none => ∅

private lemma mem_finsetOfConfig_iff {N r : ℕ} {τ : Fin N → Option Bool}
    {s : Fin N → Option (Fin r)} {w : ℕ} :
    w ∈ finsetOfConfig N r τ s ↔
      ∃ i : Fin N,
        (∃ b : Bool, τ i = some b ∧ w = nodeId r i.val b.toNat) ∨
        (τ i = none ∧ ∃ j : Fin r, s i = some j ∧ w = nodeId r i.val (j.val + 2)) := by
  simp only [finsetOfConfig, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine exists_congr fun i ↦ ?_
  cases hτ : τ i with
  | some b =>
    simp only [Finset.mem_singleton, Option.some.injEq, reduceCtorEq, false_and, or_false]
    exact ⟨fun hw ↦ ⟨b, rfl, hw⟩, fun ⟨b', hb', hw⟩ ↦ hb' ▸ hw⟩
  | none =>
    simp only [reduceCtorEq, false_and, exists_false, true_and, false_or]
    cases hsi : s i with
    | none => simp
    | some j =>
      simp only [Finset.mem_singleton, Option.some.injEq]
      exact ⟨fun hw ↦ ⟨j, rfl, hw⟩, fun ⟨j', hj', hw⟩ ↦ hj' ▸ hw⟩

private lemma bool_eq_of_toNat_eq {b₁ b₂ : Bool} (h : b₁.toNat = b₂.toNat) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> first | rfl | cases h

private lemma bool_ne_not (b : Bool) : b ≠ !b := by
  cases b <;> decide

private lemma SharpIndepSet_twoSATIndepGraph_eq_sum (φ : CNF ℕ) (r : ℕ) :
    SharpIndepSet (twoSATIndepGraph φ r) =
      ∑ τ : {τ : Fin φ.distinctVars.length → Option Bool // validPartial φ τ},
        (r + 1) ^ (Finset.univ.filter fun i : Fin φ.distinctVars.length ↦ τ.1 i = none).card := by
  classical
  let N := φ.distinctVars.length
  let Total := Σ τ : {τ : Fin N → Option Bool // validPartial φ τ},
    ∀ i : Fin N, {s : Option (Fin r) // blockSlackPred r (τ.1 i) s}
  have hcard : SharpIndepSet (twoSATIndepGraph φ r) = Fintype.card Total := by
    rw [SharpIndepSet, ← Fintype.card_coe]
    symm
    refine Fintype.card_of_bijective
      (f := fun x ↦ ⟨finsetOfConfig N r x.1.1 (fun i ↦ (x.2 i).1), ?_⟩)
      ⟨fun x₁ x₂ heq ↦ ?_, fun ⟨S, hS⟩ ↦ ?_⟩
    · rcases x with ⟨⟨τ, hτ_lit, hτ_cl⟩, sl⟩
      rw [mem_indepFinsets_iff]
      refine ⟨fun w hw ↦ ?_, fun u hu w hw huw ↦ ?_⟩
      · rw [mem_finsetOfConfig_iff] at hw
        obtain ⟨i, ⟨b, hb, rfl⟩ | ⟨_, j, _, rfl⟩⟩ := hw
        · exact mem_vertices_twoSATIndepGraph.mpr
            ⟨i.val, i.isLt, mem_blockVertices_iff.mpr (Or.inl ⟨b, hτ_lit i b hb, rfl⟩)⟩
        · exact mem_vertices_twoSATIndepGraph.mpr
            ⟨i.val, i.isLt, mem_blockVertices_iff.mpr (Or.inr ⟨j.val, j.isLt, rfl⟩)⟩
      · simp only [Finset.mem_coe] at hu hw
        rw [mem_finsetOfConfig_iff] at hu hw
        obtain ⟨i₁, h₁⟩ := hu
        obtain ⟨i₂, h₂⟩ := hw
        have hk_of {i : Fin N} {x : ℕ}
            (hx : (∃ b : Bool, τ i = some b ∧ x = nodeId r i.val b.toNat) ∨
              (τ i = none ∧ ∃ j : Fin r, (sl i).1 = some j ∧ x = nodeId r i.val (j.val + 2))) :
            ∃ k < r + 2, x = nodeId r i.val k ∧
              (k < 2 → ∃ b : Bool, τ i = some b ∧ k = b.toNat) := by
          rcases hx with ⟨b, hb, rfl⟩ | ⟨_, j, _, rfl⟩
          · refine ⟨b.toNat, bool_toNat_lt_add_two b r, rfl, fun _ ↦ ⟨b, hb, rfl⟩⟩
          · refine ⟨j.val + 2, by omega, rfl, fun _ ↦ by omega⟩
        obtain ⟨k₁, hk₁, rfl, hlit₁⟩ := hk_of h₁
        obtain ⟨k₂, hk₂, rfl, hlit₂⟩ := hk_of h₂
        by_cases hi : i₁ = i₂
        · subst hi
          rcases h₁ with ⟨b₁, hb₁, he₁⟩ | ⟨hn₁, j₁, hs₁, he₁⟩ <;>
            rcases h₂ with ⟨b₂, hb₂, he₂⟩ | ⟨hn₂, j₂, hs₂, he₂⟩
          · obtain rfl : b₁ = b₂ := Option.some.inj (hb₁.symm.trans hb₂)
            exact False.elim (huw (he₁.trans he₂.symm))
          · cases hb₁.symm.trans hn₂
          · cases hn₁.symm.trans hb₂
          · obtain rfl : j₁ = j₂ := Option.some.inj (hs₁.symm.trans hs₂)
            exact False.elim (huw (he₁.trans he₂.symm))
        · have hi_val : i₁.val ≠ i₂.val := fun hv ↦ hi (Fin.ext hv)
          intro hadj
          obtain ⟨c, hc, l₁, hl₁, l₂, hl₂, hneq, hi₁_eq, hk₁_eq, hi₂_eq, hk₂_eq⟩ :=
            (adj_diff_blocks_iff hk₁ hk₂ hi_val).mp hadj
          obtain ⟨b₁, hb₁, hkb₁⟩ := hlit₁ (by rw [hk₁_eq]; cases l₁.2 <;> simp)
          obtain ⟨b₂, hb₂, hkb₂⟩ := hlit₂ (by rw [hk₂_eq]; cases l₂.2 <;> simp)
          have hb₁_eq : b₁ = !l₁.2 := bool_eq_of_toNat_eq (hkb₁.symm.trans hk₁_eq)
          have hb₂_eq : b₂ = !l₂.2 := bool_eq_of_toNat_eq (hkb₂.symm.trans hk₂_eq)
          subst hb₁_eq hb₂_eq
          have hidx₁ : φ.distinctVars.idxOf l₁.1 < N := hi₁_eq ▸ i₁.isLt
          have hidx₂ : φ.distinctVars.idxOf l₂.1 < N := hi₂_eq ▸ i₂.isLt
          have hfin₁ : i₁ = ⟨φ.distinctVars.idxOf l₁.1, hidx₁⟩ := Fin.ext hi₁_eq
          have hfin₂ : i₂ = ⟨φ.distinctVars.idxOf l₂.1, hidx₂⟩ := Fin.ext hi₂_eq
          exact hτ_cl c hc l₁ hl₁ l₂ hl₂ hneq hidx₁ hidx₂ ⟨hfin₁ ▸ hb₁, hfin₂ ▸ hb₂⟩
    · rcases x₁ with ⟨⟨τ₁, hτ₁⟩, sl₁⟩
      rcases x₂ with ⟨⟨τ₂, hτ₂⟩, sl₂⟩
      have heqS : finsetOfConfig N r τ₁ (fun i ↦ (sl₁ i).1) =
          finsetOfConfig N r τ₂ (fun i ↦ (sl₂ i).1) := Subtype.mk.inj heq
      have hlit_mem (τ : Fin N → Option Bool) (sl : ∀ i, {s // blockSlackPred r (τ i) s})
          (i : Fin N) (b : Bool) :
          nodeId r i.val b.toNat ∈ finsetOfConfig N r τ (fun i ↦ (sl i).1) ↔ τ i = some b := by
        rw [mem_finsetOfConfig_iff]
        constructor
        · rintro ⟨i', ⟨b', hb', he⟩ | ⟨_, j, _, he⟩⟩
          · have hb_lt : b.toNat < r + 2 := bool_toNat_lt_add_two b r
            have hb'_lt : b'.toNat < r + 2 := bool_toNat_lt_add_two b' r
            obtain ⟨hi', hbk⟩ := nodeId_inj hb_lt hb'_lt he
            obtain rfl : i = i' := Fin.ext hi'
            exact (bool_eq_of_toNat_eq hbk) ▸ hb'
          · have hb_lt : b.toNat < r + 2 := bool_toNat_lt_add_two b r
            have hj_lt : j.val + 2 < r + 2 := by omega
            obtain ⟨_, hbk⟩ := nodeId_inj hb_lt hj_lt he
            cases b <;> simp at hbk
        · intro hb
          exact ⟨i, Or.inl ⟨b, hb, rfl⟩⟩
      have hτ_eq : τ₁ = τ₂ := by
        funext i
        cases h₁ : τ₁ i with
        | some b =>
          have hm : nodeId r i.val b.toNat ∈ finsetOfConfig N r τ₂ (fun i ↦ (sl₂ i).1) := by
            rw [← heqS, hlit_mem τ₁ sl₁]
            exact h₁
          exact ((hlit_mem τ₂ sl₂ i b).mp hm).symm
        | none =>
          cases h₂ : τ₂ i with
          | none => rfl
          | some b =>
            have hm : nodeId r i.val b.toNat ∈ finsetOfConfig N r τ₁ (fun i ↦ (sl₁ i).1) := by
              rw [heqS, hlit_mem τ₂ sl₂]
              exact h₂
            cases h₁.symm.trans ((hlit_mem τ₁ sl₁ i b).mp hm)
      subst hτ_eq
      have hsub : (⟨τ₁, hτ₁⟩ : {τ // validPartial φ τ}) = ⟨τ₁, hτ₂⟩ := rfl
      refine Sigma.ext hsub (heq_of_eq (funext fun i ↦ Subtype.ext ?_))
      cases hτi : τ₁ i with
      | some b =>
        have hs₁ := (sl₁ i).2 (by simp [hτi])
        have hs₂ := (sl₂ i).2 (by simp [hτi])
        exact hs₁.trans hs₂.symm
      | none =>
        have hslack_mem (sl : ∀ i, {s // blockSlackPred r (τ₁ i) s}) (j : Fin r) :
            nodeId r i.val (j.val + 2) ∈ finsetOfConfig N r τ₁ (fun i ↦ (sl i).1) ↔
              (sl i).1 = some j := by
          rw [mem_finsetOfConfig_iff]
          constructor
          · rintro ⟨i', ⟨b', _, he⟩ | ⟨_, j', hs', he⟩⟩
            · have hj_lt : j.val + 2 < r + 2 := by omega
              have hb'_lt : b'.toNat < r + 2 := bool_toNat_lt_add_two b' r
              obtain ⟨_, hbk⟩ := nodeId_inj hj_lt hb'_lt he
              cases b' <;> simp at hbk
            · have hj_lt : j.val + 2 < r + 2 := by omega
              have hj'_lt : j'.val + 2 < r + 2 := by omega
              obtain ⟨hi', hjk⟩ := nodeId_inj hj_lt hj'_lt he
              obtain rfl : i = i' := Fin.ext hi'
              obtain rfl : j = j' := Fin.ext (by omega)
              exact hs'
          · intro hs
            exact ⟨i, Or.inr ⟨hτi, j, hs, rfl⟩⟩
        cases hs₁ : (sl₁ i).1 with
        | some j =>
          have hm : nodeId r i.val (j.val + 2) ∈ finsetOfConfig N r τ₁ (fun i ↦ (sl₂ i).1) := by
            rw [← heqS, hslack_mem sl₁]
            exact hs₁
          exact ((hslack_mem sl₂ j).mp hm).symm
        | none =>
          cases hs₂ : (sl₂ i).1 with
          | none => rfl
          | some j =>
            have hm : nodeId r i.val (j.val + 2) ∈ finsetOfConfig N r τ₁ (fun i ↦ (sl₁ i).1) := by
              rw [heqS, hslack_mem sl₂]
              exact hs₂
            cases hs₁.symm.trans ((hslack_mem sl₁ j).mp hm)
    · obtain ⟨hS_sub, hS_ind⟩ := mem_indepFinsets_iff.mp hS
      have huniq_blk (i : Fin N) {u w : ℕ} (huS : u ∈ S) (hwS : w ∈ S)
          (huB : u ∈ blockVertices φ r i.val φ.distinctVars[i.val])
          (hwB : w ∈ blockVertices φ r i.val φ.distinctVars[i.val]) : u = w := by
        by_contra hne
        exact hS_ind huS hwS hne (block_clique_adj i.isLt huB hwB hne)
      have hmemB_of_S {i : Fin N} {k : ℕ} (hk : k < r + 2) (hmem : nodeId r i.val k ∈ S) :
          nodeId r i.val k ∈ blockVertices φ r i.val φ.distinctVars[i.val] := by
        obtain ⟨i', hi', hB'⟩ := mem_vertices_twoSATIndepGraph.mp (hS_sub _ hmem)
        have hdiv := (div_of_mem_blockVertices hB').1
        rw [(nodeId_div_mod i.val hk).1] at hdiv
        subst hdiv
        exact hB'
      let τ (i : Fin N) : Option Bool :=
        if nodeId r i.val 0 ∈ S then some false
        else if nodeId r i.val 1 ∈ S then some true
        else none
      have hτ_spec (i : Fin N) (b : Bool) : τ i = some b ↔ nodeId r i.val b.toNat ∈ S := by
        dsimp only [τ]
        cases b
        · by_cases h0 : nodeId r i.val 0 ∈ S <;> simp [h0]
        · by_cases h0 : nodeId r i.val 0 ∈ S
          · by_cases h1 : nodeId r i.val 1 ∈ S
            · have hB0 := hmemB_of_S (by omega : 0 < r + 2) h0
              have hB1 := hmemB_of_S (by omega : 1 < r + 2) h1
              have heq := huniq_blk i h0 h1 hB0 hB1
              have := (nodeId_inj (by omega) (by omega) heq).2
              omega
            · simp [h0, h1]
          · by_cases h1 : nodeId r i.val 1 ∈ S <;> simp [h0, h1]
      have hτ_valid : validPartial φ τ := by
        refine ⟨fun i b hb ↦ ?_, fun c hc l₁ hl₁ l₂ hl₂ hneq h₁ h₂ ⟨hb₁, hb₂⟩ ↦ ?_⟩
        · have hm := (hτ_spec i b).mp hb
          have hB := hmemB_of_S (bool_toNat_lt_add_two b r) hm
          rcases mem_blockVertices_iff.mp hB with ⟨b', hb'_ok, heq⟩ | ⟨j, _, heq⟩
          · have hbk := (nodeId_inj (bool_toNat_lt_add_two b r)
              (bool_toNat_lt_add_two b' r) heq).2
            exact (bool_eq_of_toNat_eq hbk) ▸ hb'_ok
          · have hbk := (nodeId_inj (bool_toNat_lt_add_two b r) (by omega) heq).2
            cases b <;> simp at hbk
        · have hm₁ := (hτ_spec ⟨φ.distinctVars.idxOf l₁.1, h₁⟩ (!l₁.2)).mp hb₁
          have hm₂ := (hτ_spec ⟨φ.distinctVars.idxOf l₂.1, h₂⟩ (!l₂.2)).mp hb₂
          have hv₁ : l₁.1 ∈ φ.distinctVars :=
            CNF.mem_distinctVars.mpr
              (List.mem_map.mpr ⟨l₁, List.mem_flatten.mpr ⟨c, hc, hl₁⟩, rfl⟩)
          have hv₂ : l₂.1 ∈ φ.distinctVars :=
            CNF.mem_distinctVars.mpr
              (List.mem_map.mpr ⟨l₂, List.mem_flatten.mpr ⟨c, hc, hl₂⟩, rfl⟩)
          have hi_ne : φ.distinctVars.idxOf l₁.1 ≠ φ.distinctVars.idxOf l₂.1 := by
            intro heq
            have hget := congrArg (fun idx ↦ φ.distinctVars.getD idx 0) heq
            rw [List.getD_idxOf hv₁ 0, List.getD_idxOf hv₂ 0] at hget
            exact hneq hget
          have hk₁_lt : (!l₁.2).toNat < r + 2 := bool_toNat_lt_add_two (!l₁.2) r
          have hk₂_lt : (!l₂.2).toNat < r + 2 := bool_toNat_lt_add_two (!l₂.2) r
          have hadj : (twoSATIndepGraph φ r).toSimpleGraph.Adj
              (nodeId r (φ.distinctVars.idxOf l₁.1) (!l₁.2).toNat)
              (nodeId r (φ.distinctVars.idxOf l₂.1) (!l₂.2).toNat) :=
            (adj_diff_blocks_iff hk₁_lt hk₂_lt hi_ne).mpr
              ⟨c, hc, l₁, hl₁, l₂, hl₂, hneq, rfl, rfl, rfl, rfl⟩
          exact hS_ind hm₁ hm₂ hadj.ne hadj
      let findSlack (i : Fin N) : Option (Fin r) :=
        (List.finRange r).find? fun j ↦ decide (nodeId r i.val (j.val + 2) ∈ S)
      let sl (i : Fin N) : {s : Option (Fin r) // blockSlackPred r (τ i) s} :=
        if hsome : (τ i).isSome = true then
          ⟨none, fun _ ↦ rfl⟩
        else
          ⟨findSlack i, fun h ↦ False.elim (hsome h)⟩
      refine ⟨⟨⟨τ, hτ_valid⟩, sl⟩, Subtype.ext ?_⟩
      ext w
      dsimp only
      rw [mem_finsetOfConfig_iff]
      constructor
      · rintro ⟨i, ⟨b, hb, rfl⟩ | ⟨hnone, j, hsj, rfl⟩⟩
        · exact (hτ_spec i b).mp hb
        · have hns : ¬((τ i).isSome = true) := by rw [hnone]; decide
          dsimp only [sl] at hsj
          split_ifs at hsj
          exact of_decide_eq_true
            (List.find?_some (p := fun j' : Fin r ↦ decide (nodeId r i.val (j'.val + 2) ∈ S)) hsj)
      · intro hwS
        obtain ⟨i_raw, hi_raw, hwB⟩ := mem_vertices_twoSATIndepGraph.mp (hS_sub w hwS)
        let i : Fin N := ⟨i_raw, hi_raw⟩
        rcases mem_blockVertices_iff.mp hwB with ⟨b, _, rfl⟩ | ⟨j_raw, hj_raw, rfl⟩
        · exact ⟨i, Or.inl ⟨b, (hτ_spec i b).mpr hwS, rfl⟩⟩
        · have hnone : τ i = none := by
            cases hτi : τ i with
            | none => rfl
            | some b =>
              have hlitS := (hτ_spec i b).mp hτi
              have hBlit := hmemB_of_S (bool_toNat_lt_add_two b r) hlitS
              have heq := huniq_blk i hlitS hwS hBlit hwB
              have hbk := (nodeId_inj (bool_toNat_lt_add_two b r) (by omega) heq).2
              cases b <;> simp at hbk
          have hns : ¬((τ i).isSome = true) := by rw [hnone]; decide
          let j : Fin r := ⟨j_raw, hj_raw⟩
          have hfind : findSlack i = some j := by
            dsimp only [findSlack]
            cases hfd : (List.finRange r).find? fun j' ↦
                decide (nodeId r i.val (j'.val + 2) ∈ S) with
            | none =>
              have hall := List.find?_eq_none.mp hfd j (List.mem_finRange j)
              exact False.elim (hall (decide_eq_true hwS))
            | some j' =>
              have hj'S : nodeId r i.val (j'.val + 2) ∈ S :=
                of_decide_eq_true
                  (List.find?_some
                    (p := fun j'' : Fin r ↦ decide (nodeId r i.val (j''.val + 2) ∈ S)) hfd)
              have hBj' := hmemB_of_S (by omega) hj'S
              have heq := huniq_blk i hj'S hwS hBj' hwB
              have hjk := (nodeId_inj (by omega) (by omega) heq).2
              exact congrArg some (Fin.ext (Nat.add_right_cancel hjk))
          refine ⟨i, Or.inr ⟨hnone, j, ?_, rfl⟩⟩
          dsimp only [sl]
          split_ifs
          exact hfind
  rw [hcard]
  dsimp only [Total]
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [Fintype.card_pi]
  have hprod : (∏ i : Fin N, Fintype.card {s : Option (Fin r) // blockSlackPred r (τ.1 i) s}) =
      ∏ i : Fin N, (if τ.1 i = none then r + 1 else 1) :=
    Finset.prod_congr rfl fun i _ ↦ card_blockSlackPred r (τ.1 i)
  rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private lemma validPartial_some_iff_eval {φ : CNF ℕ}
    (h2 : ∀ c ∈ φ, c.length ≤ 2) (hne : ∀ c ∈ φ, c ≠ [])
    (σ : Fin φ.distinctVars.length → Bool) :
    validPartial φ (fun i ↦ some (σ i)) ↔
      φ.eval (fun v ↦ if hv : v ∈ φ.distinctVars then
        σ ⟨φ.distinctVars.idxOf v, List.idxOf_lt_length_iff.mpr hv⟩ else false) = true := by
  let σExt (v : ℕ) : Bool :=
    if hv : v ∈ φ.distinctVars then
      σ ⟨φ.distinctVars.idxOf v, List.idxOf_lt_length_iff.mpr hv⟩
    else false
  have hσExt_get (i : Fin φ.distinctVars.length) : σExt φ.distinctVars[i.val] = σ i := by
    have hmem : φ.distinctVars[i.val] ∈ φ.distinctVars := List.getElem_mem i.isLt
    have hidx : φ.distinctVars.idxOf φ.distinctVars[i.val] = i.val :=
      φ.nodup_distinctVars.idxOf_getElem i.val i.isLt
    simp only [σExt, hmem, ↓reduceDIte]
    exact congrArg σ (Fin.ext hidx)
  have hσExt_mem {v : ℕ} (hv : v ∈ φ.distinctVars) :
      σExt v = σ ⟨φ.distinctVars.idxOf v, List.idxOf_lt_length_iff.mpr hv⟩ := by
    simp only [σExt, hv, ↓reduceDIte]
  rw [CNF.eval_eq_true_iff]
  constructor
  · rintro ⟨hlit, hcl⟩ c hc
    by_contra hfalse
    have hcf : c.eval σExt = false := Bool.eq_false_iff.mpr hfalse
    have hall : ∀ l ∈ c, σExt l.1 = !l.2 := (Clause.eval_eq_false_iff σExt c).mp hcf
    have hlen_c := h2 c hc
    have hne_c := hne c hc
    cases c with
    | nil => exact hne_c rfl
    | cons a rest =>
      cases rest with
      | nil =>
        have hva : a.1 ∈ φ.distinctVars :=
          CNF.mem_distinctVars.mpr
            (List.mem_map.mpr ⟨a, List.mem_flatten.mpr ⟨[a], hc, by simp⟩, rfl⟩)
        let ia : Fin φ.distinctVars.length :=
          ⟨φ.distinctVars.idxOf a.1, List.idxOf_lt_length_iff.mpr hva⟩
        have hget_ia : φ.distinctVars[ia.val] = a.1 := List.getElem_idxOf ia.isLt
        have hok := litAllowed_eq_true_iff.mp (hlit ia (σ ia) rfl)
        refine hok ⟨[a], hc, hne_c, fun l hl ↦ ?_⟩
        rw [hget_ia, List.mem_singleton.mp hl]
        have ha_eval := hall a (List.mem_singleton_self a)
        rw [hσExt_mem hva] at ha_eval
        change σ ia = !a.2 at ha_eval
        exact Prod.ext rfl (by rw [ha_eval, Bool.not_not])
      | cons d tail =>
        cases tail with
        | cons _ _ =>
          simp only [List.length_cons] at hlen_c
          omega
        | nil =>
          by_cases had : a.1 = d.1
          · have hva : a.1 ∈ φ.distinctVars :=
              CNF.mem_distinctVars.mpr
                (List.mem_map.mpr ⟨a, List.mem_flatten.mpr ⟨[a, d], hc, by simp⟩, rfl⟩)
            let ia : Fin φ.distinctVars.length :=
              ⟨φ.distinctVars.idxOf a.1, List.idxOf_lt_length_iff.mpr hva⟩
            have hget_ia : φ.distinctVars[ia.val] = a.1 := List.getElem_idxOf ia.isLt
            have hok := litAllowed_eq_true_iff.mp (hlit ia (σ ia) rfl)
            refine hok ⟨[a, d], hc, hne_c, fun l hl ↦ ?_⟩
            rw [hget_ia]
            have ha_eval := hall a (by simp)
            have hd_eval := hall d (by simp)
            rw [← had] at hd_eval
            rw [hσExt_mem hva] at ha_eval hd_eval
            change σ ia = !a.2 at ha_eval
            change σ ia = !d.2 at hd_eval
            rcases List.mem_cons.mp hl with hla | hld
            · rw [hla]
              exact Prod.ext rfl (by rw [ha_eval, Bool.not_not])
            · rw [List.mem_singleton.mp hld]
              exact Prod.ext had.symm (by rw [hd_eval, Bool.not_not])
          · have hva : a.1 ∈ φ.distinctVars :=
              CNF.mem_distinctVars.mpr
                (List.mem_map.mpr ⟨a, List.mem_flatten.mpr ⟨[a, d], hc, by simp⟩, rfl⟩)
            have hvd : d.1 ∈ φ.distinctVars :=
              CNF.mem_distinctVars.mpr
                (List.mem_map.mpr ⟨d, List.mem_flatten.mpr ⟨[a, d], hc, by simp⟩, rfl⟩)
            have hidx_a := List.idxOf_lt_length_iff.mpr hva
            have hidx_d := List.idxOf_lt_length_iff.mpr hvd
            have ha_eval := hall a (by simp)
            have hd_eval := hall d (by simp)
            rw [hσExt_mem hva] at ha_eval
            rw [hσExt_mem hvd] at hd_eval
            exact hcl [a, d] hc a (by simp) d (by simp) had hidx_a hidx_d
              ⟨congrArg some ha_eval, congrArg some hd_eval⟩
  · intro heval
    refine ⟨fun i b hb ↦ ?_, fun c hc l₁ hl₁ l₂ hl₂ hneq h₁ h₂ ⟨hb₁, hb₂⟩ ↦ ?_⟩
    · obtain rfl : b = σ i := (Option.some.inj hb).symm
      rw [litAllowed_eq_true_iff]
      rintro ⟨c, hc, _, hall⟩
      have hce : c.eval σExt = true := heval c hc
      rw [Clause.eval_eq_true_iff] at hce
      obtain ⟨l, hl, hleval⟩ := hce
      have hleq := hall l hl
      rw [hleq] at hleval
      dsimp only at hleval
      rw [hσExt_get i] at hleval
      exact bool_ne_not (σ i) hleval
    · have hce : c.eval σExt = true := heval c hc
      rw [Clause.eval_eq_true_iff] at hce
      obtain ⟨l, hl, hleval⟩ := hce
      have hlen_c := h2 c hc
      cases c with
      | nil => exact False.elim (List.not_mem_nil hl)
      | cons a rest =>
        cases rest with
        | nil =>
          have ha₁ := List.mem_singleton.mp hl₁
          have ha₂ := List.mem_singleton.mp hl₂
          subst ha₁ ha₂
          exact hneq rfl
        | cons d tail =>
          cases tail with
          | cons _ _ =>
            simp only [List.length_cons] at hlen_c
            omega
          | nil =>
            have hmem2 {x : Literal ℕ} (hx : x ∈ [a, d]) : x = a ∨ x = d := by
              simpa using hx
            have hl₁_eval : σExt l₁.1 = !l₁.2 := by
              have hv₁ : l₁.1 ∈ φ.distinctVars := List.idxOf_lt_length_iff.mp h₁
              rw [hσExt_mem hv₁, Option.some.inj hb₁]
            have hl₂_eval : σExt l₂.1 = !l₂.2 := by
              have hv₂ : l₂.1 ∈ φ.distinctVars := List.idxOf_lt_length_iff.mp h₂
              rw [hσExt_mem hv₂, Option.some.inj hb₂]
            have hnot1 (he : σExt l₁.1 = l₁.2) : False :=
              bool_ne_not l₁.2 (he.symm.trans hl₁_eval)
            have hnot2 (he : σExt l₂.1 = l₂.2) : False :=
              bool_ne_not l₂.2 (he.symm.trans hl₂_eval)
            rcases hmem2 hl₁ with rfl | rfl <;> rcases hmem2 hl₂ with rfl | rfl
            · exact hneq rfl
            · rcases hmem2 hl with rfl | rfl
              · exact hnot1 hleval
              · exact hnot2 hleval
            · rcases hmem2 hl with rfl | rfl
              · exact hnot2 hleval
              · exact hnot1 hleval
            · exact hneq rfl

private lemma modelCount_eq_card_validPartial_some {φ : CNF ℕ}
    (h2 : ∀ c ∈ φ, c.length ≤ 2) (hne : ∀ c ∈ φ, c ≠ []) :
    φ.modelCount =
      (Finset.univ.filter
        fun τ : {τ : Fin φ.distinctVars.length → Option Bool // validPartial φ τ} ↦
          (Finset.univ.filter fun i : Fin φ.distinctVars.length ↦ τ.1 i = none).card = 0).card := by
  classical
  let N := φ.distinctVars.length
  have hcard_some :
      (Finset.univ.filter fun σ : Fin N → Bool ↦ validPartial φ (fun i ↦ some (σ i))).card =
      (Finset.univ.filter fun τ : {τ : Fin N → Option Bool // validPartial φ τ} ↦
        (Finset.univ.filter fun i : Fin N ↦ τ.1 i = none).card = 0).card := by
    refine Finset.card_bij (fun σ hσ ↦ ⟨fun i ↦ some (σ i), (Finset.mem_filter.mp hσ).2⟩)
      (fun _ _ ↦ ?_) (fun _ _ _ _ heq ↦ ?_) (fun τ hτ ↦ ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro i _ h
      cases h
    · have hfn := Subtype.mk.inj heq
      funext i
      exact Option.some.inj (congrFun hfn i)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff] at hτ
      let σ (i : Fin N) : Bool := (τ.1 i).getD false
      have hτ_eq : (fun i ↦ some (σ i)) = τ.1 := by
        funext i
        cases hi : τ.1 i with
        | none => exact False.elim (@hτ i trivial hi)
        | some b => simp [σ, hi]
      exact ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ_eq ▸ τ.2⟩, Subtype.ext hτ_eq⟩
  rw [← hcard_some, CNF.modelCount]
  refine Finset.card_bij
    (fun ρ _ ↦ fun i : Fin N ↦
      ρ ⟨φ.distinctVars[i.val], List.mem_toFinset.mpr
        (CNF.mem_distinctVars.mp (List.getElem_mem i.isLt))⟩)
    (fun ρ hρ ↦ ?_) (fun _ _ _ _ heq ↦ ?_) (fun σ hσ ↦ ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    rw [validPartial_some_iff_eval h2 hne]
    refine (CNF.eval_congr fun v hv ↦ ?_).trans hρ
    have hvd : v ∈ φ.distinctVars := CNF.mem_distinctVars.mpr hv
    have hidx : φ.distinctVars.idxOf v < N := List.idxOf_lt_length_iff.mpr hvd
    simp only [hvd, ↓reduceDIte, CNF.extendAssignment_of_mem ρ hv]
    exact congrArg ρ (Subtype.ext (List.getElem_idxOf hidx))
  · funext ⟨v, hv⟩
    have hvd : v ∈ φ.distinctVars := CNF.mem_distinctVars.mpr (List.mem_toFinset.mp hv)
    have hidx : φ.distinctVars.idxOf v < N := List.idxOf_lt_length_iff.mpr hvd
    have hval := congrFun heq ⟨φ.distinctVars.idxOf v, hidx⟩
    simpa only [List.getElem_idxOf hidx] using hval
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have hev := (validPartial_some_iff_eval h2 hne σ).mp hσ
    let ρ : φ.vars.toFinset → Bool := fun ⟨v, hv⟩ ↦
      σ ⟨φ.distinctVars.idxOf v,
        List.idxOf_lt_length_iff.mpr (CNF.mem_distinctVars.mpr (List.mem_toFinset.mp hv))⟩
    refine ⟨ρ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, funext fun i ↦ ?_⟩
    · refine (CNF.eval_congr fun v hv ↦ ?_).trans hev
      have hvd : v ∈ φ.distinctVars := CNF.mem_distinctVars.mpr hv
      simp only [CNF.extendAssignment_of_mem ρ hv, ρ, hvd, ↓reduceDIte]
    · have hidx : φ.distinctVars.idxOf φ.distinctVars[i.val] = i.val :=
        φ.nodup_distinctVars.idxOf_getElem i.val i.isLt
      simp only [ρ]
      exact congrArg σ (Fin.ext hidx)

private lemma SharpTwoSAT_eq_twoSATIndep_sum_int {φ : CNF ℕ}
    (h2 : ∀ c ∈ φ, c.length ≤ 2) (hne : ∀ c ∈ φ, c ≠ []) :
    (SharpTwoSAT φ : ℤ) =
      ∑ r ∈ Finset.range (φ.distinctVars.length + 1),
        (-1 : ℤ) ^ r * ((φ.distinctVars.length + 1).choose (r + 1) : ℤ) *
          (SharpIndepSet (twoSATIndepGraph φ r) : ℤ) := by
  classical
  let N := φ.distinctVars.length
  let noneCount (τ : {τ : Fin N → Option Bool // validPartial φ τ}) : ℕ :=
    (Finset.univ.filter fun i : Fin N ↦ τ.1 i = none).card
  let P : Polynomial ℤ :=
    ∑ τ : {τ : Fin N → Option Bool // validPartial φ τ}, Polynomial.X ^ noneCount τ
  have hdeg : P.natDegree ≤ N := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun τ _ ↦ ?_
    refine (Polynomial.natDegree_X_pow_le _).trans ?_
    exact (Finset.card_filter_le _ _).trans (by simp [N])
  have hevalP (x : ℤ) : P.eval x =
      ∑ τ : {τ : Fin N → Option Bool // validPartial φ τ}, x ^ noneCount τ := by
    simpa only [P, Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X] using
      map_sum (Polynomial.evalRingHom x)
        (fun τ : {τ : Fin N → Option Bool // validPartial φ τ} ↦ Polynomial.X ^ noneCount τ)
        Finset.univ
  have h2sat : SharpTwoSAT φ = φ.modelCount := by
    rw [SharpTwoSAT]
    split_ifs with hall
    · rfl
    · exact False.elim (hall (List.all_eq_true.mpr fun c hc ↦ decide_eq_true (h2 c hc)))
  have hP0 : P.eval 0 = (SharpTwoSAT φ : ℤ) := by
    rw [h2sat, modelCount_eq_card_validPartial_some h2 hne, hevalP 0]
    have hsum : ((Finset.univ.filter
        fun τ : {τ : Fin N → Option Bool // validPartial φ τ} ↦ noneCount τ = 0).card : ℤ) =
        ∑ τ : {τ : Fin N → Option Bool // validPartial φ τ},
          if noneCount τ = 0 then (1 : ℤ) else 0 := by
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    change ∑ τ : {τ : Fin N → Option Bool // validPartial φ τ}, (0 : ℤ) ^ noneCount τ =
      ((Finset.univ.filter fun τ ↦ noneCount τ = 0).card : ℤ)
    rw [hsum]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    by_cases h0 : noneCount τ = 0
    · simp [h0]
    · simp [h0, zero_pow h0]
  have hPr (r : ℕ) : P.eval ((r : ℤ) + 1) = (SharpIndepSet (twoSATIndepGraph φ r) : ℤ) := by
    rw [SharpIndepSet_twoSATIndepGraph_eq_sum, hevalP ((r : ℤ) + 1)]
    simp only [noneCount, N, Nat.cast_sum, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have hid := Polynomial.eval_zero_eq_sum_neg_one_pow_choose_eval_succ hdeg
  rw [hP0] at hid
  refine hid.trans (Finset.sum_congr rfl fun r _ ↦ ?_)
  rw [hPr r]

private def isNonemptyTwoCNF (φ : CNF ℕ) : Bool :=
  φ.all (fun c ↦ decide (c.length ≤ 2)) && !φ.any List.isEmpty

private def twoSATIndepCombine (p : CNF ℕ × List ℕ) : ℕ :=
  if isNonemptyTwoCNF p.1 then
    let n := p.1.distinctVars.length
    let posSum := ((p.2.zipIdx).map fun x ↦
      if !x.2.testBit 0 then (n + 1).choose (x.2 + 1) * x.1 else 0).sum
    let negSum := ((p.2.zipIdx).map fun x ↦
      if x.2.testBit 0 then (n + 1).choose (x.2 + 1) * x.1 else 0).sum
    posSum - negSum
  else 0

private lemma twoSATIndepCombine_spec (φ : CNF ℕ) :
    twoSATIndepCombine (φ, (List.range (φ.distinctVars.length + 1)).map fun r ↦
        SharpIndepSet (twoSATIndepGraph φ r)) = SharpTwoSAT φ := by
  let vals := (List.range (φ.distinctVars.length + 1)).map fun r ↦
    SharpIndepSet (twoSATIndepGraph φ r)
  change twoSATIndepCombine (φ, vals) = SharpTwoSAT φ
  unfold twoSATIndepCombine isNonemptyTwoCNF
  dsimp only
  split_ifs with hguard
  · simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.any_eq_false, List.isEmpty_iff] at hguard
    obtain ⟨h2, hne⟩ := hguard
    let n := φ.distinctVars.length
    have hzip : vals.zipIdx =
        (List.range (n + 1)).map fun r ↦ (SharpIndepSet (twoSATIndepGraph φ r), r) := by
      apply List.ext_getElem (by simp [vals, n]) fun i hi _ ↦ by
        simp only [List.length_zipIdx] at hi
        simp [vals, n]
    have hhalf (wantOdd : Bool) :
        ((((vals.zipIdx).map fun x ↦
          if x.2.testBit 0 = wantOdd then (n + 1).choose (x.2 + 1) * x.1 else 0).sum : ℕ) : ℤ) =
          ∑ r ∈ Finset.range (n + 1),
            if r % 2 = (if wantOdd then 1 else 0) then
              ((n + 1).choose (r + 1) * SharpIndepSet (twoSATIndepGraph φ r) : ℤ)
            else 0 := by
      rw [hzip, List.map_map, List.sum_map_range, Fin.sum_univ_eq_sum_range, Nat.cast_sum]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      dsimp only [Function.comp_apply]
      by_cases hr2 : r % 2 = 0
      · have htb : r.testBit 0 = false := by simp [Nat.testBit_zero, hr2]
        cases wantOdd <;> simp [htb, hr2]
      · have hr1 : r % 2 = 1 := by omega
        have htb : r.testBit 0 = true := by simp [Nat.testBit_zero, hr1]
        cases wantOdd <;> simp [htb, hr1]
    have hpos : ((((vals.zipIdx).map fun x ↦
        if !x.2.testBit 0 then (n + 1).choose (x.2 + 1) * x.1 else 0).sum : ℕ) : ℤ) =
        ∑ r ∈ Finset.range (n + 1),
          if r % 2 = 0 then ((n + 1).choose (r + 1) * SharpIndepSet (twoSATIndepGraph φ r) : ℤ)
          else 0 := by
      simpa only [Bool.not_eq_true', Bool.false_eq_true, ↓reduceIte] using hhalf false
    have hneg : ((((vals.zipIdx).map fun x ↦
        if x.2.testBit 0 then (n + 1).choose (x.2 + 1) * x.1 else 0).sum : ℕ) : ℤ) =
        ∑ r ∈ Finset.range (n + 1),
          if r % 2 = 1 then ((n + 1).choose (r + 1) * SharpIndepSet (twoSATIndepGraph φ r) : ℤ)
          else 0 :=
      hhalf true
    have hsplit : (∑ r ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ r * ((n + 1).choose (r + 1) : ℤ) *
          (SharpIndepSet (twoSATIndepGraph φ r) : ℤ)) =
        (∑ r ∈ Finset.range (n + 1),
          if r % 2 = 0 then
            ((n + 1).choose (r + 1) * SharpIndepSet (twoSATIndepGraph φ r) : ℤ)
          else 0) -
        ∑ r ∈ Finset.range (n + 1),
          if r % 2 = 1 then
            ((n + 1).choose (r + 1) * SharpIndepSet (twoSATIndepGraph φ r) : ℤ)
          else 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rcases Nat.mod_two_eq_zero_or_one r with hr0 | hr1
      · have hs : (-1 : ℤ) ^ r = 1 := Even.neg_one_pow (Nat.even_iff.mpr hr0)
        simp [hr0, hs]
      · have hs : (-1 : ℤ) ^ r = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hr1)
        simp [hr1, hs]
    have hnatle :
        ((vals.zipIdx).map fun x ↦
          if x.2.testBit 0 then (n + 1).choose (x.2 + 1) * x.1 else 0).sum ≤
        ((vals.zipIdx).map fun x ↦
          if !x.2.testBit 0 then (n + 1).choose (x.2 + 1) * x.1 else 0).sum := by
      have hs0 : 0 ≤ (SharpTwoSAT φ : ℤ) := Nat.cast_nonneg _
      rw [SharpTwoSAT_eq_twoSATIndep_sum_int h2 hne] at hs0
      change 0 ≤ ∑ r ∈ Finset.range (n + 1), _ at hs0
      rw [hsplit, ← hpos, ← hneg] at hs0
      exact Int.ofNat_le.mp (Int.sub_nonneg.mp hs0)
    have hdiff :
        ((((vals.zipIdx).map fun x ↦
            if !x.2.testBit 0 then (n + 1).choose (x.2 + 1) * x.1 else 0).sum -
          ((vals.zipIdx).map fun x ↦
            if x.2.testBit 0 then (n + 1).choose (x.2 + 1) * x.1 else 0).sum : ℕ) : ℤ) =
        (SharpTwoSAT φ : ℤ) := by
      rw [Int.ofNat_sub hnatle, hpos, hneg, ← hsplit]
      exact (SharpTwoSAT_eq_twoSATIndep_sum_int h2 hne).symm
    exact Int.ofNat.inj hdiff
  · simp only [Bool.and_eq_true, not_and_or, Bool.not_eq_true] at hguard
    rcases hguard with hnot2 | hemp
    · simp only [SharpTwoSAT, hnot2, Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.not_eq_false', List.any_eq_true, List.isEmpty_iff] at hemp
      obtain ⟨c, hc, rfl⟩ := hemp
      rw [SharpTwoSAT]
      split_ifs
      · symm
        rw [← Nat.le_zero, ← not_lt, CNF.modelCount_pos_iff]
        rintro ⟨σ, hσ⟩
        have hce := (Clause.eval_eq_false_iff σ []).mpr fun l hl ↦ False.elim (List.not_mem_nil hl)
        exact Bool.false_ne_true (hce.symm.trans ((CNF.eval_eq_true_iff σ φ).mp hσ [] hc))
      · rfl

private lemma size_SharpIndepSet_twoSATIndepGraph_le_of_le {φ : CNF ℕ} {r B : ℕ}
    (hN : φ.distinctVars.length ≤ B) (hr : r ≤ B) :
    (SharpIndepSet (twoSATIndepGraph φ r)).size ≤ B * (B + 2) + 1 := by
  have hlen_blk (i v : ℕ) : (blockVertices φ r i v).length ≤ r + 2 := by
    simp only [blockVertices, List.length_append, List.length_map, List.length_range]
    by_cases h0 : litAllowed φ v false = true <;> by_cases h1 : litAllowed φ v true = true <;>
      simp [h0, h1] <;> omega
  have hlen_verts :
      (twoSATIndepGraph φ r).vertices.length ≤ φ.distinctVars.length * (r + 2) := by
    simp only [twoSATIndepGraph, List.length_flatMap]
    let lens := φ.distinctVars.zipIdx.map fun vi : ℕ × ℕ ↦ (blockVertices φ r vi.2 vi.1).length
    calc
      lens.sum ≤ lens.length • (r + 2) :=
        List.sum_le_length_nsmul lens (r + 2) fun x hx ↦ by
          obtain ⟨⟨v, i⟩, _, rfl⟩ := List.mem_map.mp hx
          exact hlen_blk i v
      _ = φ.distinctVars.length * (r + 2) := by simp [lens, smul_eq_mul]
  have hcard_le : SharpIndepSet (twoSATIndepGraph φ r) ≤ 2 ^ (B * (B + 2)) := by
    calc
      SharpIndepSet (twoSATIndepGraph φ r) ≤
          (twoSATIndepGraph φ r).distinctVertices.toFinset.powerset.card :=
        Finset.card_filter_le _ _
      _ = 2 ^ (twoSATIndepGraph φ r).distinctVertices.toFinset.card := Finset.card_powerset _
      _ ≤ 2 ^ (twoSATIndepGraph φ r).vertices.length := by
        refine Nat.pow_le_pow_right (by omega) ?_
        calc
          (twoSATIndepGraph φ r).distinctVertices.toFinset.card ≤
              (twoSATIndepGraph φ r).distinctVertices.length := List.toFinset_card_le _
          _ ≤ (twoSATIndepGraph φ r).vertices.length := by
            rw [Graph.length_distinctVertices]
            exact List.toFinset_card_le _
      _ ≤ 2 ^ (φ.distinctVars.length * (r + 2)) := Nat.pow_le_pow_right (by omega) hlen_verts
      _ ≤ 2 ^ (B * (B + 2)) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul hN (by omega))
  have hpow_pos : 0 < 2 ^ (B * (B + 2)) := Nat.two_pow_pos _
  refine Nat.size_le.mpr ?_
  rw [Nat.pow_succ]
  omega

private lemma size_SharpIndepSet_twoSATIndepGraph_le {φ : CNF ℕ} {r : ℕ}
    (hr : r ≤ φ.distinctVars.length) :
    (SharpIndepSet (twoSATIndepGraph φ r)).size ≤
      φ.distinctVars.length * (φ.distinctVars.length + 2) + 1 :=
  size_SharpIndepSet_twoSATIndepGraph_le_of_le le_rfl hr

@[local fun_prop]
private lemma computableInPolyTime_nodeId {α : Type} {enc : α ↪ List Bool} {f g h : α → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary)
    (hh : ComputableInPolyTime h enc encUnary) :
    ComputableInPolyTime (fun a ↦ nodeId (f a) (g a) (h a)) enc encNat := by
  unfold nodeId
  exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

private lemma computableInPolyTime_allPairs :
    ComputableInPolyTime
      (fun vs : List ℕ ↦ vs.flatMap fun u ↦ vs.map fun w ↦ (u, w))
      (encList encNat) (encList (encPair encNat encNat)) := by
  refine ComputableInPolyTime.flatMapWithInput ComputableInPolyTime.id' ?_
  refine ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.fst (encList encNat) encNat) ?_
  exact ((ComputableInPolyTime.snd (encList encNat) encNat).comp
    (ComputableInPolyTime.fst (encPair (encList encNat) encNat) encNat)).prod
    (ComputableInPolyTime.snd (encPair (encList encNat) encNat) encNat)

private lemma computableInPolyTime_isNonemptyTwoCNF :
    ComputableInPolyTime isNonemptyTwoCNF encCNF encBool := by
  have hne : ComputableInPolyTime (fun φ : CNF ℕ ↦ φ.any List.isEmpty) encCNF encBool := by
    unfold encCNF
    fun_prop
  exact ComputableInPolyTime.bool_and' (computableInPolyTime_all_length_le 2)
    (ComputableInPolyTime.bool_not.comp hne)

private lemma computableInPolyTime_twoSATIndepCombine :
    ComputableInPolyTime twoSATIndepCombine (encPair encCNF (encList encNat)) encNat := by
  have hd : ComputableInPolyTime (CNF.distinctVars (V := ℕ)) encCNF (encList encNat) :=
    SAT.computableInPolyTime_distinctVars
  have hguard : ComputableInPolyTime (fun p : CNF ℕ × List ℕ ↦ isNonemptyTwoCNF p.1)
      (encPair encCNF (encList encNat)) encBool :=
    computableInPolyTime_isNonemptyTwoCNF.comp (ComputableInPolyTime.fst _ _)
  polytime [twoSATIndepCombine]

private lemma computableInPolyTime_twoSATIndepGraph :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ twoSATIndepGraph p.1 p.2)
      (encPair encCNF encUnary) encGraph := by
  have hd : ComputableInPolyTime (CNF.distinctVars (V := ℕ)) encCNF (encList encNat) :=
    SAT.computableInPolyTime_distinctVars
  have hlit : ComputableInPolyTime (fun p : (CNF ℕ × ℕ) × Bool ↦ litAllowed p.1.1 p.1.2 p.2)
      (encPair (encPair encCNF encNat) encBool) encBool := by
    unfold litAllowed encCNF
    polytime
  have hblkV : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × (ℕ × ℕ) ↦ blockVertices p.1.1 p.1.2 p.2.2 p.2.1)
      (encPair (encPair encCNF encUnary) (encPair encNat encUnary)) (encList encNat) := by
    polytime [blockVertices]
  have hblkE : ComputableInPolyTime
      (fun p : (CNF ℕ × ℕ) × (ℕ × ℕ) ↦ blockEdges p.1.1 p.1.2 p.2.2 p.2.1)
      (encPair (encPair encCNF encUnary) (encPair encNat encUnary))
      (encList (encPair encNat encNat)) :=
    computableInPolyTime_allPairs.comp hblkV
  have hclE : ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ clauseConflictEdges p.1 p.2)
      (encPair encCNF encUnary) (encList (encPair encNat encNat)) := by
    unfold clauseConflictEdges encCNF
    polytime
  have hzip : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ p.1.distinctVars.zipIdx)
      (encPair encCNF encUnary) (encList (encPair encNat encUnary)) :=
    (ComputableInPolyTime.zipIdx encNat).comp (hd.comp (ComputableInPolyTime.fst _ _))
  have hverts : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ (twoSATIndepGraph p.1 p.2).vertices)
      (encPair encCNF encUnary) (encList encNat) :=
    ComputableInPolyTime.flatMapWithInput hzip hblkV
  have hedges : ComputableInPolyTime
      (fun p : CNF ℕ × ℕ ↦ (twoSATIndepGraph p.1 p.2).edges)
      (encPair encCNF encUnary) (encList (encPair encNat encNat)) :=
    ComputableInPolyTime.listAppend' (ComputableInPolyTime.flatMapWithInput hzip hblkE) hclE
  exact encGraph_mk_polyTime hverts hedges

/-- **`#2SAT` reduces to `#IndependentSet` under polynomial-time counting Turing reductions.** -/
theorem countingTuringReducible_SharpTwoSAT_SharpIndepSet :
    CountingTuringReducible encCNF encGraph SharpTwoSAT SharpIndepSet := by
  let queries (φ : CNF ℕ) : List Graph :=
    (List.range (φ.distinctVars.length + 1)).map (twoSATIndepGraph φ)
  let bound (φ : CNF ℕ) : ℕ :=
    φ.distinctVars.length * (φ.distinctVars.length + 2) + 1
  have hd : ComputableInPolyTime (CNF.distinctVars (V := ℕ)) encCNF (encList encNat) :=
    SAT.computableInPolyTime_distinctVars
  have hqueries : ComputableInPolyTime queries encCNF (encList encGraph) := by
    have := computableInPolyTime_twoSATIndepGraph
    polytime [queries]
  have hbound : ComputableInPolyTime bound encCNF encUnary := by
    unfold bound
    fun_prop
  refine PolyTimeOracleProgram.of_batchNatBits queries bound twoSATIndepCombine
    hqueries hbound computableInPolyTime_twoSATIndepCombine ?_
    (fun φ ↦ by
      simpa only [queries, List.map_map, Function.comp_def] using twoSATIndepCombine_spec φ)
  intro φ G hG
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hG
  rw [List.mem_range] at hr
  exact size_SharpIndepSet_twoSATIndepGraph_le (by omega)

/-! ### Direct batched `#SAT ≤_T^#P #IndependentSet` and `#P`-completeness -/

private def satStride (φ : CNF ℕ) : ℕ :=
  φ.vars.length + φ.length * (φ.length + 1) + 1

private def satIndepQueries (φ : CNF ℕ) : List Graph :=
  (List.range (φ.length + 1)).flatMap fun r₁ ↦
    (List.range (satStride φ)).map fun r₂ ↦
      twoSATIndepGraph (clauseWeightTwoSAT φ r₁) r₂

private def satIndepCombine (p : CNF ℕ × List ℕ) : ℕ :=
  let φ := p.1
  let S := satStride φ
  let twoSATVals := (List.range (φ.length + 1)).map fun r₁ ↦
    let ψ := clauseWeightTwoSAT φ r₁
    twoSATIndepCombine (ψ, (p.2.drop (r₁ * S)).take (ψ.distinctVars.length + 1))
  clauseWeightCombine (φ, twoSATVals)

private lemma drop_mul_flatMap_range {α : Type*} (m S : ℕ) (f : ℕ → ℕ → α)
    {r₁ : ℕ} (hr₁ : r₁ < m) :
    (((List.range m).flatMap fun i ↦ (List.range S).map (f i)).drop (r₁ * S)).take S =
      (List.range S).map (f r₁) := by
  have haux : ∀ (l : List ℕ) (j : ℕ) (hj : j < l.length),
      ((l.flatMap fun i ↦ (List.range S).map (f i)).drop (j * S)).take S =
        (List.range S).map (f (l[j]'hj)) := by
    intro l j hj
    induction l generalizing j with
    | nil => simp at hj
    | cons a l ih =>
      cases j with
      | zero =>
        simpa only [Nat.zero_mul, List.drop_zero, List.flatMap_cons, List.getElem_cons_zero] using
          List.take_left' (by simp : ((List.range S).map (f a)).length = S)
      | succ j' =>
        rw [List.flatMap_cons, show (j' + 1) * S = S + j' * S by ring, ← List.drop_drop,
          List.drop_left' (by simp : ((List.range S).map (f a)).length = S),
          List.getElem_cons_succ]
        exact ih j' (Nat.lt_of_succ_lt_succ hj)
  have hres := haux (List.range m) r₁ (by simpa using hr₁)
  rwa [List.getElem_range] at hres

private lemma satIndepCombine_spec (φ : CNF ℕ) :
    satIndepCombine (φ, (satIndepQueries φ).map SharpIndepSet) = SharpSAT φ := by
  unfold satIndepCombine
  dsimp only
  have houter : ((List.range (φ.length + 1)).map fun r₁ ↦
      let ψ := clauseWeightTwoSAT φ r₁
      twoSATIndepCombine (ψ,
        (((satIndepQueries φ).map SharpIndepSet).drop (r₁ * satStride φ)).take
          (ψ.distinctVars.length + 1))) =
      (List.range (φ.length + 1)).map fun r₁ ↦ SharpTwoSAT (clauseWeightTwoSAT φ r₁) := by
    refine List.map_congr_left fun r₁ hr₁ ↦ ?_
    rw [List.mem_range] at hr₁
    dsimp only
    have hψ_le : (clauseWeightTwoSAT φ r₁).distinctVars.length + 1 ≤ satStride φ := by
      rw [CNF.length_distinctVars]
      have hnv := numVars_clauseWeightTwoSAT_le φ r₁
      have hmul : φ.length * (r₁ + 1) ≤ φ.length * (φ.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      unfold satStride
      omega
    have hmap_flat : (satIndepQueries φ).map SharpIndepSet =
        (List.range (φ.length + 1)).flatMap fun i ↦
          (List.range (satStride φ)).map fun r₂ ↦
            SharpIndepSet (twoSATIndepGraph (clauseWeightTwoSAT φ i) r₂) := by
      simp only [satIndepQueries, List.map_flatMap, List.map_map, Function.comp_def]
    have hslice :
        ((((satIndepQueries φ).map SharpIndepSet).drop (r₁ * satStride φ)).take
          ((clauseWeightTwoSAT φ r₁).distinctVars.length + 1)) =
        (List.range ((clauseWeightTwoSAT φ r₁).distinctVars.length + 1)).map fun r₂ ↦
          SharpIndepSet (twoSATIndepGraph (clauseWeightTwoSAT φ r₁) r₂) := by
      have hmin : (clauseWeightTwoSAT φ r₁).distinctVars.length + 1 =
          min ((clauseWeightTwoSAT φ r₁).distinctVars.length + 1) (satStride φ) :=
        (Nat.min_eq_left hψ_le).symm
      conv_lhs => rw [hmap_flat, hmin, ← List.take_take]
      have hchunk := drop_mul_flatMap_range (φ.length + 1) (satStride φ)
        (fun i r₂ ↦ SharpIndepSet (twoSATIndepGraph (clauseWeightTwoSAT φ i) r₂)) hr₁
      rw [hchunk, ← List.map_take, List.take_range, Nat.min_eq_left hψ_le]
    rw [hslice, twoSATIndepCombine_spec (clauseWeightTwoSAT φ r₁)]
  rw [houter, clauseWeightCombine_spec φ]

@[local fun_prop]
private lemma computableInPolyTime_zVar_local {α : Type} {enc : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary) :
    ComputableInPolyTime (fun a ↦ zVar (f a) (g a)) enc encNat := by
  unfold zVar; exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

@[local fun_prop]
private lemma computableInPolyTime_uVar_local {α : Type} {enc : α ↪ List Bool} {f g h : α → ℕ}
    (hf : ComputableInPolyTime f enc encUnary) (hg : ComputableInPolyTime g enc encUnary)
    (hh : ComputableInPolyTime h enc encUnary) :
    ComputableInPolyTime (fun a ↦ uVar (f a) (g a) (h a)) enc encNat := by
  unfold uVar; exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

private lemma computableInPolyTime_clauseWeightTwoSAT_local :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ ↦ clauseWeightTwoSAT p.1 p.2)
      (encPair encCNF encUnary) encCNF := by
  have := SAT.computableInPolyTime_distinctVars
  have hgadget : ComputableInPolyTime (fun p : ℕ × (Clause ℕ × ℕ) ↦ clauseWeightGadget p.1 p.2)
      (encPair encUnary (encPair (encClause encNat) encUnary)) encCNF := by
    polytime [clauseWeightGadget]
  polytime [clauseWeightTwoSAT, clauseWeightVarTauts]

private lemma computableInPolyTime_satStride :
    ComputableInPolyTime satStride encCNF encUnary := by
  unfold satStride
  have := SAT.computableInPolyTime_vars_length ComputableInPolyTime.id'
  have := SAT.computableInPolyTime_length ComputableInPolyTime.id'
  fun_prop

private lemma computableInPolyTime_satIndepQueries :
    ComputableInPolyTime satIndepQueries encCNF (encList encGraph) := by
  have := computableInPolyTime_satStride; have := computableInPolyTime_clauseWeightTwoSAT_local
  have := SAT.computableInPolyTime_length ComputableInPolyTime.id'
  have := computableInPolyTime_twoSATIndepGraph
  polytime [satIndepQueries]

private lemma computableInPolyTime_satIndepCombine :
    ComputableInPolyTime satIndepCombine (encPair encCNF (encList encNat)) encNat := by
  have := computableInPolyTime_satStride; have := computableInPolyTime_clauseWeightTwoSAT_local
  have := SAT.computableInPolyTime_length ComputableInPolyTime.id'
  have := SAT.computableInPolyTime_distinctVars; have := computableInPolyTime_twoSATIndepCombine
  have hcomb1 : ComputableInPolyTime clauseWeightCombine
      (encPair encCNF (encList encNat)) encNat := by polytime [clauseWeightCombine]
  polytime [satIndepCombine]

private lemma size_satIndepQueries_le (φ : CNF ℕ) {G : Graph} (hG : G ∈ satIndepQueries φ) :
    (SharpIndepSet G).size ≤ satStride φ * (satStride φ + 2) + 1 := by
  simp only [satIndepQueries, List.mem_flatMap, List.mem_range, List.mem_map] at hG
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hG
  have hnv : (clauseWeightTwoSAT φ r₁).distinctVars.length ≤ satStride φ := by
    rw [CNF.length_distinctVars]
    have := numVars_clauseWeightTwoSAT_le φ r₁
    have := Nat.mul_le_mul_left φ.length (show r₁ + 1 ≤ φ.length + 1 by omega)
    unfold satStride; omega
  exact size_SharpIndepSet_twoSATIndepGraph_le_of_le hnv (by omega)

private lemma countingTuringReducible_SharpSAT_of_add_offset {β : Type} {encB : β ↪ List Bool}
    {g : β → ℕ} {r : Graph → β} {offset : Graph → ℕ}
    (hr : ComputableInPolyTime r encGraph encB) (hoff : ComputableInPolyTime offset encGraph encNat)
    (hspec : ∀ G : Graph, g (r G) = SharpIndepSet G + offset G) (hle : ∀ G : Graph, offset G ≤ 1) :
    CountingTuringReducible encCNF encB SharpSAT g := by
  let queries (φ : CNF ℕ) : List β := (satIndepQueries φ).map r
  let bound (φ : CNF ℕ) : ℕ := satStride φ * (satStride φ + 2) + 2
  let combine (p : CNF ℕ × List ℕ) : ℕ :=
    satIndepCombine (p.1, ((satIndepQueries p.1).zipIdx).map fun gi ↦ p.2.getD gi.2 0 - offset gi.1)
  have hqueries : ComputableInPolyTime queries encCNF (encList encB) :=
    (ComputableInPolyTime.map hr).comp computableInPolyTime_satIndepQueries
  have hbound : ComputableInPolyTime bound encCNF encUnary := by
    have := computableInPolyTime_satStride; unfold bound; fun_prop
  have hcomb : ComputableInPolyTime combine (encPair encCNF (encList encNat)) encNat := by
    have := computableInPolyTime_satIndepQueries; have := computableInPolyTime_satIndepCombine
    polytime [combine]
  refine PolyTimeOracleProgram.of_batchNatBits queries bound combine
    hqueries hbound hcomb (fun φ b hb ↦ ?_) (fun φ ↦ ?_)
  · obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hb
    rw [hspec G]
    have hlt := Nat.size_le.mp (size_satIndepQueries_le φ hG)
    have := hle G
    refine Nat.size_le.mpr ?_
    unfold bound
    rw [show satStride φ * (satStride φ + 2) + 2 =
      (satStride φ * (satStride φ + 2) + 1) + 1 by omega, Nat.pow_succ]
    omega
  · simp only [combine, queries, List.map_map, Function.comp_def]
    have hadj : (((satIndepQueries φ).zipIdx).map fun gi ↦
        (((satIndepQueries φ).map (fun G ↦ g (r G))).getD gi.2 0 - offset gi.1)) =
        (satIndepQueries φ).map SharpIndepSet := by
      refine List.ext_getElem (by simp) fun i _ hi₂ ↦ ?_
      simp only [List.length_map] at hi₂
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₂, hspec]
    rw [hadj, satIndepCombine_spec]

/-- **`#SAT` reduces to `#IndependentSet` under polynomial-time counting Turing reductions.** -/
theorem countingTuringReducible_SharpSAT_SharpIndepSet :
    CountingTuringReducible encCNF encGraph SharpSAT SharpIndepSet :=
  countingTuringReducible_SharpSAT_of_add_offset (r := id) (offset := fun _ ↦ 0)
    ComputableInPolyTime.id' (ComputableInPolyTime.const 0)
    (fun _ ↦ (Nat.add_zero _).symm) (fun _ ↦ Nat.zero_le 1)

/-- **`#IndependentSet` is `#P`-complete under polynomial-time counting Turing reductions.** -/
theorem SharpIndepSet_countingTuringComplete :
    CountingTuringComplete encGraph SharpIndepSet :=
  ⟨SharpIndepSet_mem_SharpP,
    CookLevin.SharpSAT_sharpPHard.trans_countingTuring
      countingTuringReducible_SharpSAT_SharpIndepSet⟩

/-- **Transfer of `#P`-hardness from `#IndependentSet` along an offset-`{0, 1}` reduction**:
if `r : Graph → β` and `offset : Graph → ℕ` are polynomial-time computable with
`g (r G) = SharpIndepSet G + offset G` and `offset G ≤ 1` for every graph `G`, then `g` is
`#P`-hard under polynomial-time counting Turing reductions. -/
theorem countingTuringHard_of_add_offset_SharpIndepSet {β : Type} {encB : β ↪ List Bool}
    {g : β → ℕ} {r : Graph → β} {offset : Graph → ℕ}
    (hr : ComputableInPolyTime r encGraph encB)
    (hoff : ComputableInPolyTime offset encGraph encNat)
    (hspec : ∀ G : Graph, g (r G) = SharpIndepSet G + offset G)
    (hle : ∀ G : Graph, offset G ≤ 1) :
    CountingTuringHard encB g :=
  CookLevin.SharpSAT_sharpPHard.trans_countingTuring
    (countingTuringReducible_SharpSAT_of_add_offset hr hoff hspec hle)

/-- If `#IndependentSet` is computable in polynomial time (`FP`), then `P = NP`. -/
theorem SharpIndepSet_polyTime_implies_P_eq_NP
    (h : ComputableInPolyTime SharpIndepSet encGraph encNat)
    {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc := by
  have h2sat : ComputableInPolyTime SharpTwoSAT encCNF encNat :=
    countingTuringReducible_SharpTwoSAT_SharpIndepSet.computableInPolyTime_of_decoder graphDecoder h
  exact SharpTwoSAT_polyTime_implies_P_eq_NP h2sat enc

/- Non-degeneracy witness: on the 3-vertex path `0 - 1 - 2`, `{0, 2}` belongs to `indepFinsets`
   while `{0, 1}` does not. -/
example :
    let P3 : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2)]⟩
    ({0, 2} : Finset ℕ) ∈ indepFinsets P3 ∧ ({0, 1} : Finset ℕ) ∉ indepFinsets P3 := by
  dsimp only
  simp only [mem_indepFinsets_iff, SimpleGraph.IsIndepSet, Set.Pairwise, Finset.mem_coe,
    Graph.toSimpleGraph_adj]
  refine ⟨⟨by decide, fun u hu v hv huv ⟨_, hadj⟩ ↦ ?_⟩, fun ⟨_, hind⟩ ↦ ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp at huv hadj
  · exact @hind 0 (by simp) 1 (by simp) (by decide) ⟨by decide, Or.inl (by simp)⟩

end CslibFrontier.Complexity
