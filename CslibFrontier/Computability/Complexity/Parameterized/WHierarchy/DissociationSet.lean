/-
Copyright (c) 2026 Cslib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cslib Contributors
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Encoding.Evaluation
public import CslibFrontier.Computability.Complexity.Parameterized.Kernelization
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.XP
public import CslibFrontier.Computability.Complexity.Problems.VertexCover
import CslibFrontier.Computability.Circuit.Encoding.Layer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Parameterized Complexity of Dissociation Set

A *dissociation set* in a simple graph `G` is a subset
`S` of vertices inducing a subgraph of maximum degree at most `1` (equivalently, no `3`-vertex path
has all three vertices in `S`).

This module establishes the `W[1]`-completeness and `XP` membership of `DissociationSet`, together
with the `W[1]`-hardness of `MulticoloredIndependentSet`:

* `Cslib.Complexity.MulticoloredIndependentSet_wHard`: `MulticoloredIndependentSet` is `W[1]`-hard
  parameterized by `k`, by fpt-reduction from `Clique`.
* `Cslib.Complexity.DissociationSet_wHard`: `DissociationSet` is `W[1]`-hard parameterized by `k`,
  by the clique-pendant matching fpt-reduction `(G, k) ↦ (G', 2k)` from
  `MulticoloredIndependentSet`.
* `Cslib.Complexity.DissociationSet_mem_W_one`, `Cslib.Complexity.DissociationSet_wComplete`,
  `Cslib.Complexity.DissociationSet_mem_XP`: `DissociationSet` reduces in polynomial time to
  `WCS 1 4` (weft `1`, depth `4`), hence is `W[1]`-complete and belongs to `XP`.
-/

public section

namespace Cslib.Complexity

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- A subset `S` of vertices of a simple graph `G` is a **dissociation set** (`1`-dependent set) if
no vertex of `S` is adjacent to two distinct vertices of `S`. -/
def IsDissociationSet {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃u v w : V⦄, u ∈ S → v ∈ S → w ∈ S → G.Adj u v → u ≠ w → ¬ G.Adj v w

/-- Instance `(graph, k)` of **Dissociation Set**. -/
@[ext]
structure DissociationSetInstance where
  /-- Input graph on natural-number vertex identifiers. -/
  graph : Graph
  /-- Target dissociation set size `k`. -/
  k : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Equivalence between `DissociationSetInstance` and `Graph × ℕ`. -/
@[expose]
def DissociationSetInstance.equivPair : DissociationSetInstance ≃ Graph × ℕ where
  toFun I := (I.graph, I.k)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Framed binary encoding of `DissociationSetInstance`. -/
@[expose]
def encDissociationSetInstance : DissociationSetInstance ↪ List Bool :=
  DissociationSetInstance.equivPair.toEmbedding.trans (encPair encGraph encNat)

@[fun_prop]
theorem computableInPolyTime_dissociation_graph {γ : Type} {enc : γ ↪ List Bool}
    {f : γ → DissociationSetInstance}
    (hf : ComputableInPolyTime f enc encDissociationSetInstance) :
    ComputableInPolyTime (fun a => (f a).graph) enc encGraph := by
  have ht : ComputableInPolyTime (fun a => DissociationSetInstance.equivPair (f a)) enc
      (encPair encGraph encNat) := hf
  exact (fst _ _).comp ht

@[fun_prop]
theorem computableInPolyTime_dissociation_k {γ : Type} {enc : γ ↪ List Bool}
    {f : γ → DissociationSetInstance}
    (hf : ComputableInPolyTime f enc encDissociationSetInstance) :
    ComputableInPolyTime (fun a => (f a).k) enc encNat := by
  have ht : ComputableInPolyTime (fun a => DissociationSetInstance.equivPair (f a)) enc
      (encPair encGraph encNat) := hf
  exact (snd _ _).comp ht

@[fun_prop]
theorem computableInPolyTime_dissociation_mk {γ : Type} {enc : γ ↪ List Bool}
    {g : γ → Graph} {fk : γ → ℕ}
    (hg : ComputableInPolyTime g enc encGraph)
    (hk : ComputableInPolyTime fk enc encNat) :
    ComputableInPolyTime (fun a => DissociationSetInstance.mk (g a) (fk a))
      enc encDissociationSetInstance :=
  hg.prod hk

/-- **Dissociation Set**: instances `(G, k)` admitting a dissociation set of at least `k` declared
vertices. -/
def DissociationSet : Set DissociationSetInstance :=
  {I | ∃ S : Finset {v // v ∈ I.graph.vertices},
    IsDissociationSet I.graph.induced (S : Set _) ∧ I.k ≤ S.card}

/-! ### Multicolored Independent Set and `W[1]`-hardness -/

/-- Instance `(graph, parts, k)` of **Multicolored Independent Set**. -/
@[ext]
structure MulticoloredIndependentSetInstance where
  /-- Input graph on natural-number vertex identifiers. -/
  graph : Graph
  /-- `k` pairwise-disjoint color classes of declared vertices. -/
  parts : List (List ℕ)
  /-- Target number of colors `k`. -/
  k : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Equivalence between `MulticoloredIndependentSetInstance` and `(Graph × List (List ℕ)) × ℕ`. -/
@[expose]
def MulticoloredIndependentSetInstance.equivTuple :
    MulticoloredIndependentSetInstance ≃ (Graph × List (List ℕ)) × ℕ where
  toFun I := ((I.graph, I.parts), I.k)
  invFun t := ⟨t.1.1, t.1.2, t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Framed binary encoding of `MulticoloredIndependentSetInstance`. -/
@[expose]
def encMulticoloredIndependentSetInstance : MulticoloredIndependentSetInstance ↪ List Bool :=
  MulticoloredIndependentSetInstance.equivTuple.toEmbedding.trans
    (encPair (encPair encGraph (encList (encList encNat))) encNat)

@[fun_prop]
theorem computableInPolyTime_mis_graph {γ : Type} {enc : γ ↪ List Bool}
    {f : γ → MulticoloredIndependentSetInstance}
    (hf : ComputableInPolyTime f enc encMulticoloredIndependentSetInstance) :
    ComputableInPolyTime (fun a => (f a).graph) enc encGraph := by
  have ht : ComputableInPolyTime (fun a => MulticoloredIndependentSetInstance.equivTuple (f a)) enc
      (encPair (encPair encGraph (encList (encList encNat))) encNat) := hf
  exact (fst _ _).comp ((fst _ _).comp ht)

@[fun_prop]
theorem computableInPolyTime_mis_parts {γ : Type} {enc : γ ↪ List Bool}
    {f : γ → MulticoloredIndependentSetInstance}
    (hf : ComputableInPolyTime f enc encMulticoloredIndependentSetInstance) :
    ComputableInPolyTime (fun a => (f a).parts) enc (encList (encList encNat)) := by
  have ht : ComputableInPolyTime (fun a => MulticoloredIndependentSetInstance.equivTuple (f a)) enc
      (encPair (encPair encGraph (encList (encList encNat))) encNat) := hf
  exact (snd _ _).comp ((fst _ _).comp ht)

@[fun_prop]
theorem computableInPolyTime_mis_k {γ : Type} {enc : γ ↪ List Bool}
    {f : γ → MulticoloredIndependentSetInstance}
    (hf : ComputableInPolyTime f enc encMulticoloredIndependentSetInstance) :
    ComputableInPolyTime (fun a => (f a).k) enc encNat := by
  have ht : ComputableInPolyTime (fun a => MulticoloredIndependentSetInstance.equivTuple (f a)) enc
      (encPair (encPair encGraph (encList (encList encNat))) encNat) := hf
  exact (snd _ _).comp ht

@[fun_prop]
theorem computableInPolyTime_mis_mk {γ : Type} {enc : γ ↪ List Bool}
    {g : γ → Graph} {fp : γ → List (List ℕ)} {fk : γ → ℕ}
    (hg : ComputableInPolyTime g enc encGraph)
    (hp : ComputableInPolyTime fp enc (encList (encList encNat)))
    (hk : ComputableInPolyTime fk enc encNat) :
    ComputableInPolyTime (fun a => MulticoloredIndependentSetInstance.mk (g a) (fp a) (fk a))
      enc encMulticoloredIndependentSetInstance :=
  (hg.prod hp).prod hk

/-- **Multicolored Independent Set**: instances `(G, parts, k)` with `k` pairwise-disjoint lists of
declared vertices admitting an independent transversal `s : Fin k → ℕ`. -/
def MulticoloredIndependentSet : Set MulticoloredIndependentSetInstance :=
  {I | I.parts.length = I.k ∧
    I.parts.flatten.Nodup ∧
    (∀ v ∈ I.parts.flatten, v ∈ I.graph.vertices) ∧
    ∃ s : Fin I.k → ℕ,
      (∀ i : Fin I.k, s i ∈ I.parts.getD i.1 []) ∧
      (∀ i j : Fin I.k, i ≠ j → ¬ I.graph.toSimpleGraph.Adj (s i) (s j))}

/-- Polynomial-time fpt-reduction from `Clique` to `MulticoloredIndependentSet`. -/
def reduceCliqueToMIS (x : CliqueInstance) : MulticoloredIndependentSetInstance :=
  let V := x.graph.distinctVertices
  let N := V.length
  let kk := min N x.m
  if decide (kk = x.m) then
    if decide (kk = 0) then
      ⟨⟨[], []⟩, [], 0⟩
    else
      let verts := List.range (kk * N)
      let parts := (List.range kk).map fun i => (List.range N).map fun a => i * N + a
      let edges := (List.range kk).flatMap fun i =>
        ((List.range kk).filter fun j => decide (i ≠ j)).flatMap fun j =>
          (List.range N).flatMap fun a =>
            ((List.range N).filter fun b =>
              decide (a = b) || !x.graph.adjBool (V.getD a 0) (V.getD b 0)).map
              fun b => (i * N + a, j * N + b)
      ⟨⟨verts, edges⟩, parts, kk⟩
  else
    ⟨⟨[0], []⟩, [[]], 1⟩

private lemma computableInPolyTime_reduceCliqueToMIS :
    ComputableInPolyTime reduceCliqueToMIS encCliqueInstance
      encMulticoloredIndependentSetInstance := by
  have hV : ComputableInPolyTime (fun x : CliqueInstance => x.graph.distinctVertices)
      encCliqueInstance (encList encNat) :=
    Graph.computableInPolyTime_distinctVertices.comp (by fun_prop)
  have hN : ComputableInPolyTime (fun x : CliqueInstance => x.graph.distinctVertices.length)
      encCliqueInstance encUnary := (length_list encNat).comp hV
  have hkk : ComputableInPolyTime
      (fun x : CliqueInstance => min x.graph.distinctVertices.length x.m)
      encCliqueInstance encUnary := binary_min_unary' hN (by fun_prop)
  have hb := unary_to_binary
  have hcond1 : ComputableInPolyTime
      (fun x : CliqueInstance => decide (min x.graph.distinctVertices.length x.m = x.m))
      encCliqueInstance encBool := (hb.comp hkk).decide_eq' (by fun_prop)
  have hcond0 : ComputableInPolyTime
      (fun x : CliqueInstance => decide (min x.graph.distinctVertices.length x.m = 0))
      encCliqueInstance encBool := (hb.comp hkk).decide_eq' (const 0)
  have hverts : ComputableInPolyTime
      (fun x : CliqueInstance =>
        List.range (min x.graph.distinctVertices.length x.m * x.graph.distinctVertices.length))
      encCliqueInstance (encList encNat) := by
    have hprod : ComputableInPolyTime
        (fun x : CliqueInstance =>
          min x.graph.distinctVertices.length x.m * x.graph.distinctVertices.length)
        encCliqueInstance encUnary := unary_mul' hkk hN
    simpa only [Function.comp_def, List.map_id'] using (map hb).comp (range.comp hprod)
  let enc1 := encPair encCliqueInstance encUnary
  let enc2 := encPair enc1 encUnary
  let enc3 := encPair enc2 encUnary
  let enc4 := encPair enc3 encUnary
  have hparts : ComputableInPolyTime
      (fun x : CliqueInstance =>
        (List.range (min x.graph.distinctVertices.length x.m)).map fun i =>
          (List.range x.graph.distinctVertices.length).map fun a =>
            i * x.graph.distinctVertices.length + a)
      encCliqueInstance (encList (encList encNat)) := by
    apply mapWithInput (range.comp hkk)
    apply mapWithInput (range.comp (hN.comp (fst encCliqueInstance encUnary)))
    exact hb.comp (unary_add'
      (unary_mul' ((snd encCliqueInstance encUnary).comp (fst enc1 encUnary))
        (hN.comp ((fst encCliqueInstance encUnary).comp (fst enc1 encUnary))))
      (snd enc1 encUnary))
  have hedges : ComputableInPolyTime
      (fun x : CliqueInstance =>
        (List.range (min x.graph.distinctVertices.length x.m)).flatMap fun i =>
          ((List.range (min x.graph.distinctVertices.length x.m)).filter fun j =>
            decide (i ≠ j)).flatMap fun j =>
            (List.range x.graph.distinctVertices.length).flatMap fun a =>
              ((List.range x.graph.distinctVertices.length).filter fun b =>
                decide (a = b) ||
                  !x.graph.adjBool (x.graph.distinctVertices.getD a 0)
                    (x.graph.distinctVertices.getD b 0)).map
                fun b => (i * x.graph.distinctVertices.length + a,
                  j * x.graph.distinctVertices.length + b))
      encCliqueInstance (encList (encPair encNat encNat)) := by
    apply flatMapWithInput (range.comp hkk)
    apply flatMapWithInput
    · apply filterWithInput (range.comp (hkk.comp (fst encCliqueInstance encUnary)))
      exact decide_ne ((snd encCliqueInstance encUnary).comp (fst enc1 encUnary))
        (snd enc1 encUnary)
    · apply flatMapWithInput
        (range.comp (hN.comp ((fst encCliqueInstance encUnary).comp (fst enc1 encUnary))))
      have hx4 : ComputableInPolyTime
          (fun q : ((((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ) => q.1.1.1.1)
          enc4 encCliqueInstance :=
        (fst encCliqueInstance encUnary).comp
          ((fst enc1 encUnary).comp ((fst enc2 encUnary).comp (fst enc3 encUnary)))
      have hi4 : ComputableInPolyTime
          (fun q : ((((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ) => q.1.1.1.2) enc4 encUnary :=
        (snd encCliqueInstance encUnary).comp
          ((fst enc1 encUnary).comp ((fst enc2 encUnary).comp (fst enc3 encUnary)))
      have hj4 : ComputableInPolyTime
          (fun q : ((((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ) => q.1.1.2) enc4 encUnary :=
        (snd enc1 encUnary).comp ((fst enc2 encUnary).comp (fst enc3 encUnary))
      have ha4 : ComputableInPolyTime
          (fun q : ((((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ) => q.1.2) enc4 encUnary :=
        (snd enc2 encUnary).comp (fst enc3 encUnary)
      have hb4 : ComputableInPolyTime
          (fun q : ((((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ) => q.2) enc4 encUnary :=
        snd enc3 encUnary
      apply mapWithInput
      · apply filterWithInput (range.comp (hN.comp
          ((fst encCliqueInstance encUnary).comp ((fst enc1 encUnary).comp (fst enc2 encUnary)))))
        have h1 : ComputableInPolyTime
            (fun q : ((((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ) => decide (q.1.2 = q.2))
            enc4 encBool := ha4.decide_eq' hb4
        have hg : ComputableInPolyTime
            (fun q : ((((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ) => q.1.1.1.1.graph)
            enc4 encGraph :=
          (by fun_prop : ComputableInPolyTime CliqueInstance.graph encCliqueInstance encGraph).comp
            hx4
        have hv : ComputableInPolyTime
            (fun q : ((((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ) => q.1.1.1.1.graph.distinctVertices)
            enc4 (encList encNat) := hV.comp hx4
        have hadj : ComputableInPolyTime
            (fun q : ((((CliqueInstance × ℕ) × ℕ) × ℕ) × ℕ) =>
              q.1.1.1.1.graph.adjBool (q.1.1.1.1.graph.distinctVertices.getD q.1.2 0)
                (q.1.1.1.1.graph.distinctVertices.getD q.2 0)) enc4 encBool :=
          Graph.computableInPolyTime_adjBool_comp hg (listGetDWithInput hv ha4 0)
            (listGetDWithInput hv hb4 0)
        exact h1.bool_or' (bool_not.comp hadj)
      · exact (hb.comp (unary_add' (unary_mul' hi4 (hN.comp hx4)) ha4)).prod
          (hb.comp (unary_add' (unary_mul' hj4 (hN.comp hx4)) hb4))
  have hmain : ComputableInPolyTime
      (fun x : CliqueInstance =>
        let N := x.graph.distinctVertices.length
        let kk := min N x.m
        MulticoloredIndependentSetInstance.mk
          ⟨List.range (kk * N),
            (List.range kk).flatMap fun i =>
              ((List.range kk).filter fun j => decide (i ≠ j)).flatMap fun j =>
                (List.range N).flatMap fun a =>
                  ((List.range N).filter fun b =>
                    decide (a = b) ||
                      !x.graph.adjBool (x.graph.distinctVertices.getD a 0)
                        (x.graph.distinctVertices.getD b 0)).map
                    fun b => (i * N + a, j * N + b)⟩
          ((List.range kk).map fun i => (List.range N).map fun a => i * N + a)
          kk)
      encCliqueInstance encMulticoloredIndependentSetInstance :=
    computableInPolyTime_mis_mk (encGraph_mk_polyTime hverts hedges) hparts (hb.comp hkk)
  unfold reduceCliqueToMIS
  exact ite hcond1 (ite hcond0 (const _) hmain) (const _)

private lemma flatten_grid_eq_range (k N : ℕ) :
    ((List.range k).map fun i => (List.range N).map fun a => i * N + a).flatten =
      List.range (k * N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih, List.map_singleton,
      List.flatten_singleton, Nat.succ_mul, List.range_add]

/-- `Clique` fpt-reduces to `MulticoloredIndependentSet`. -/
theorem fptReducible_Clique_MulticoloredIndependentSet :
    FPTReducible encCliqueInstance encMulticoloredIndependentSetInstance (·.m) (·.k)
      Clique MulticoloredIndependentSet := by
  refine FPTReducible.of_computableInPolyTime computableInPolyTime_reduceCliqueToMIS
    (h := fun m => m + 1) (fun x => ?_) (fun x => ?_)
  · simp only [reduceCliqueToMIS]
    have hmin : min x.graph.distinctVertices.length x.m ≤ x.m := Nat.min_le_right _ _
    split_ifs <;> dsimp only <;> omega
  · obtain ⟨G, m⟩ := x
    simp only [reduceCliqueToMIS]
    set V := G.distinctVertices
    set N := V.length
    by_cases hle : min N m = m
    · simp only [hle, decide_true, ↓reduceIte]
      have hm_le : m ≤ N := hle ▸ Nat.min_le_left N m
      by_cases hm0 : m = 0
      · subst hm0
        simp only [decide_true, ↓reduceIte]
        have h0 : (⟨G, 0⟩ : CliqueInstance) ∈ Clique := Graph.le_cliqueNum_iff.1 (Nat.zero_le _)
        refine iff_of_true h0 ⟨rfl, by simp, by simp, Fin.elim0, fun i => Fin.elim0 i,
          fun i => Fin.elim0 i⟩
      · simp only [hm0, decide_false, Bool.false_eq_true, ↓reduceIte]
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        have hN_pos : 0 < N := lt_of_lt_of_le hm_pos hm_le
        let parts := (List.range m).map fun i => (List.range N).map fun a => i * N + a
        have hflat : parts.flatten = List.range (m * N) := flatten_grid_eq_range m N
        let G' : Graph :=
          ⟨List.range (m * N),
            (List.range m).flatMap fun i =>
              ((List.range m).filter fun j => decide (i ≠ j)).flatMap fun j =>
                (List.range N).flatMap fun a =>
                  ((List.range N).filter fun b =>
                    decide (a = b) || !G.adjBool (V.getD a 0) (V.getD b 0)).map
                    fun b => (i * N + a, j * N + b)⟩
        have hedge_iff : ∀ u v : ℕ, (u, v) ∈ G'.edges ↔
            ∃ i < m, ∃ j < m, i ≠ j ∧ ∃ a < N, ∃ b < N,
              (a = b ∨ ¬ G.toSimpleGraph.Adj (V.getD a 0) (V.getD b 0)) ∧
              u = i * N + a ∧ v = j * N + b := by
          intro u v
          dsimp only [G']
          simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
            Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Graph.adjBool_eq_false_iff,
            Prod.mk.injEq]
          constructor
          · rintro ⟨i, hi, j, ⟨hj, hij⟩, a, ha, b, ⟨hb, hcond⟩, rfl, rfl⟩
            exact ⟨i, hi, j, hj, hij, a, ha, b, hb, hcond, rfl, rfl⟩
          · rintro ⟨i, hi, j, hj, hij, a, ha, b, hb, hcond, rfl, rfl⟩
            exact ⟨i, hi, j, ⟨hj, hij⟩, a, ha, b, ⟨hb, hcond⟩, rfl, rfl⟩
        constructor
        · intro hcl
          rw [mem_Clique_iff_mk] at hcl
          obtain ⟨S, hSV, hScl, hScard⟩ := hcl
          let L := V.filter (fun v => decide (v ∈ S))
          have hL_nd : L.Nodup := G.nodup_distinctVertices.filter _
          have hL_fin : L.toFinset = S := by
            ext v
            dsimp only [L]
            simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
            exact ⟨And.right, fun hv => ⟨Graph.mem_distinctVertices.2 (hSV v hv), hv⟩⟩
          have hL_len : L.length = m := by
            rw [← List.toFinset_card_of_nodup hL_nd, hL_fin, hScard]
          let aOf : Fin m → ℕ := fun i => V.idxOf (L[i.1]'(by omega))
          have ha_lt : ∀ i : Fin m, aOf i < N := fun i =>
            List.idxOf_lt_length_iff.2 (List.mem_filter.1 (List.getElem_mem _)).1
          have hparts_len : parts.length = m := by
            dsimp only [parts]; simp
          refine ⟨hparts_len, hflat ▸ List.nodup_range,
            fun v hv => ?_,
            fun i => i.1 * N + aOf i, ?_, ?_⟩
          · change v ∈ List.range (m * N)
            rwa [← hflat]
          · intro i
            dsimp only
            have hi_len : i.1 < ((List.range m).map
                fun i => (List.range N).map fun a => i * N + a).length := by
              simp only [List.length_map, List.length_range]; exact i.2
            rw [List.getD_eq_getElem _ _ hi_len]
            simp only [List.getElem_map, List.getElem_range, List.mem_map, List.mem_range]
            exact ⟨aOf i, ha_lt i, rfl⟩
          · intro i j hij hadj'
            rw [Graph.toSimpleGraph_adj] at hadj'
            have pair_inj : ∀ i' j' a' b', a' < N → b' < N →
                i' * N + a' = j' * N + b' → i' = j' ∧ a' = b' := by
              intro i' j' a' b' ha' hb' heq
              have hdiv : (i' * N + a') / N = (j' * N + b') / N := congrArg (· / N) heq
              rw [Nat.mul_comm i' N, Nat.mul_comm j' N, Nat.mul_add_div hN_pos,
                Nat.div_eq_of_lt ha', Nat.add_zero, Nat.mul_add_div hN_pos,
                Nat.div_eq_of_lt hb', Nat.add_zero] at hdiv
              exact ⟨hdiv, by subst hdiv; omega⟩
            have check_dir : ∀ u' v' : Fin m, u' ≠ v' →
                (u'.1 * N + aOf u', v'.1 * N + aOf v') ∉ G'.edges := by
              intro u' v' huv' hedge
              rw [hedge_iff] at hedge
              obtain ⟨i', _, j', _, _, a', ha', b', hb', hcond, heq1, heq2⟩ := hedge
              obtain ⟨rfl, rfl⟩ := pair_inj u'.1 i' (aOf u') a' (ha_lt u') ha' heq1
              obtain ⟨rfl, rfl⟩ := pair_inj v'.1 j' (aOf v') b' (ha_lt v') hb' heq2
              have hVu : V.getD (aOf u') 0 = L[u'.1]'(by omega) := by
                rw [List.getD_eq_getElem _ _ (ha_lt u')]; exact List.getElem_idxOf (ha_lt u')
              have hVv : V.getD (aOf v') 0 = L[v'.1]'(by omega) := by
                rw [List.getD_eq_getElem _ _ (ha_lt v')]; exact List.getElem_idxOf (ha_lt v')
              rcases hcond with hab_eq | hnadj
              · have hLuLv : L[u'.1]'(by omega) = L[v'.1]'(by omega) := by
                  rw [← hVu, ← hVv, hab_eq]
                exact huv' (Fin.ext ((List.Nodup.getElem_inj_iff hL_nd).1 hLuLv))
              · rw [hVu, hVv] at hnadj
                have huS : L[u'.1]'(by omega) ∈ S :=
                  (Finset.ext_iff.1 hL_fin _).1 (List.mem_toFinset.2 (List.getElem_mem _))
                have hvS : L[v'.1]'(by omega) ∈ S :=
                  (Finset.ext_iff.1 hL_fin _).1 (List.mem_toFinset.2 (List.getElem_mem _))
                have hneL : L[u'.1]'(by omega) ≠ L[v'.1]'(by omega) := fun h =>
                  huv' (Fin.ext ((List.Nodup.getElem_inj_iff hL_nd).1 h))
                exact hnadj (hScl huS hvS hneL)
            rcases hadj'.2 with h1 | h2
            · exact check_dir i j hij h1
            · exact check_dir j i hij.symm h2
        · rintro ⟨_, _, _, s, hs_mem, hs_ind⟩
          have extract_a : ∀ i : Fin m, ∃ a < N, s i = i.1 * N + a := by
            intro i
            have hi := hs_mem i
            have hi_len : i.1 < ((List.range m).map
                fun i => (List.range N).map fun a => i * N + a).length := by
              simp only [List.length_map, List.length_range]; exact i.2
            rw [List.getD_eq_getElem _ _ hi_len] at hi
            simp only [List.getElem_map, List.getElem_range, List.mem_map,
              List.mem_range] at hi
            obtain ⟨a, ha, heq⟩ := hi
            exact ⟨a, ha, heq.symm⟩
          let aOf : Fin m → ℕ := fun i => (extract_a i).choose
          have ha_lt : ∀ i : Fin m, aOf i < N := fun i => (extract_a i).choose_spec.1
          have hs_eq : ∀ i : Fin m, s i = i.1 * N + aOf i := fun i => (extract_a i).choose_spec.2
          have pair_rel : ∀ i j : Fin m, i ≠ j →
              aOf i ≠ aOf j ∧ G.toSimpleGraph.Adj (V.getD (aOf i) 0) (V.getD (aOf j) 0) := by
            intro i j hij
            by_contra hbad
            rw [not_and_or, not_ne_iff] at hbad
            apply hs_ind i j hij
            rw [Graph.toSimpleGraph_adj]
            refine ⟨?_, Or.inl ?_⟩
            · rw [hs_eq i, hs_eq j]
              intro heq
              have hdiv : (i.1 * N + aOf i) / N = (j.1 * N + aOf j) / N := congrArg (· / N) heq
              rw [Nat.mul_comm i.1 N, Nat.mul_comm j.1 N, Nat.mul_add_div hN_pos,
                Nat.div_eq_of_lt (ha_lt i), Nat.add_zero, Nat.mul_add_div hN_pos,
                Nat.div_eq_of_lt (ha_lt j), Nat.add_zero] at hdiv
              exact hij (Fin.ext hdiv)
            · rw [hedge_iff]
              exact ⟨i.1, i.2, j.1, j.2, Fin.val_ne_of_ne hij, aOf i, ha_lt i, aOf j, ha_lt j,
                hbad, hs_eq i, hs_eq j⟩
          let vOf : Fin m → ℕ := fun i => V.getD (aOf i) 0
          have hv_inj : Function.Injective vOf := by
            intro i j hij_eq
            by_contra hij
            have hne_a := (pair_rel i j hij).1
            dsimp only [vOf] at hij_eq
            rw [List.getD_eq_getElem _ _ (ha_lt i),
              List.getD_eq_getElem _ _ (ha_lt j)] at hij_eq
            exact hne_a ((List.Nodup.getElem_inj_iff G.nodup_distinctVertices).1 hij_eq)
          rw [mem_Clique_iff_mk]
          refine ⟨Finset.univ.map ⟨vOf, hv_inj⟩, ?_, ?_, by simp⟩
          · intro v hv
            obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hv
            change V.getD (aOf i) 0 ∈ G.vertices
            rw [List.getD_eq_getElem _ _ (ha_lt i)]
            exact Graph.mem_distinctVertices.1 (List.getElem_mem _)
          · intro u hu v hv huv
            obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hu)
            obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hv)
            exact (pair_rel i j fun h => huv (congrArg vOf h)).2
    · simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hm_gt : N < m := by omega
      have hncl : (⟨G, m⟩ : CliqueInstance) ∉ Clique := fun hcl => by
        have hcard := Graph.le_card_of_mem_Clique hcl
        rw [← G.length_distinctVertices] at hcard
        change m ≤ N at hcard
        omega
      have hnmis : (⟨⟨[0], []⟩, [[]], 1⟩ : MulticoloredIndependentSetInstance) ∉
          MulticoloredIndependentSet := by
        rintro ⟨_, _, _, s, hs, _⟩
        have h0 := hs ⟨0, Nat.zero_lt_one⟩
        simp [List.getD] at h0
      exact iff_of_false hncl hnmis

/-- **`MulticoloredIndependentSet` is `W[1]`-hard** parameterized by `k`. -/
theorem MulticoloredIndependentSet_wHard :
    WHard 1 encMulticoloredIndependentSetInstance (·.k) MulticoloredIndependentSet :=
  Clique_wHard.trans fptReducible_Clique_MulticoloredIndependentSet

/-! ### `W[1]`-hardness and `W[1]`-completeness of `DissociationSet` -/

private def validMISBool (I : MulticoloredIndependentSetInstance) : Bool :=
  let F := I.parts.flatten
  decide (I.parts.length = I.k) &&
    F.zipIdx.all (fun e => decide (F.idxOf e.1 = e.2)) &&
    F.all (fun v => decide (v ∈ I.graph.vertices))

/-- Polynomial-time fpt-reduction `(G, k) ↦ (G', 2k)` from `MulticoloredIndependentSet` to
`DissociationSet`. -/
def reduceMISToDissociationSet (I : MulticoloredIndependentSetInstance) : DissociationSetInstance :=
  if validMISBool I then
    let F := I.parts.flatten
    let M := F.length
    let kk := I.parts.length
    let origEdges : List (ℕ × ℕ) :=
      (List.range M).flatMap fun a =>
        ((List.range M).filter fun b => I.graph.adjBool (F.getD a 0) (F.getD b 0)).map
          fun b => (a, b)
    let cliqueEdges : List (ℕ × ℕ) :=
      I.parts.flatMap fun P =>
        P.flatMap fun u =>
          (P.filter fun v => decide (u ≠ v)).map fun v => (F.idxOf u, F.idxOf v)
    let pendantEdges : List (ℕ × ℕ) :=
      (List.range kk).flatMap fun i =>
        (I.parts.getD i []).map fun u => (M + i, F.idxOf u)
    ⟨⟨List.range (M + kk), origEdges ++ cliqueEdges ++ pendantEdges⟩, 2 * kk⟩
  else
    ⟨⟨[], []⟩, 1⟩

private lemma computableInPolyTime_reduceMISToDissociationSet :
    ComputableInPolyTime reduceMISToDissociationSet encMulticoloredIndependentSetInstance
      encDissociationSetInstance := by
  have hF : ComputableInPolyTime (·.parts.flatten)
      encMulticoloredIndependentSetInstance (encList encNat) := by fun_prop
  have hM := (length_list encNat).comp hF
  have hkk : ComputableInPolyTime (·.parts.length)
      encMulticoloredIndependentSetInstance encUnary :=
    (length_list (encList encNat)).comp (by fun_prop)
  have hb := unary_to_binary
  have hvalid : ComputableInPolyTime validMISBool
      encMulticoloredIndependentSetInstance encBool := by
    unfold validMISBool
    have hk_mis : ComputableInPolyTime (·.k) encMulticoloredIndependentSetInstance encNat := by
      fun_prop
    have h1 := (hb.comp hkk).decide_eq' hk_mis
    have h2 : ComputableInPolyTime
        (fun I : MulticoloredIndependentSetInstance =>
          I.parts.flatten.zipIdx.all (fun e => decide (I.parts.flatten.idxOf e.1 = e.2)))
        encMulticoloredIndependentSetInstance encBool := by fun_prop
    have h3 : ComputableInPolyTime
        (fun I : MulticoloredIndependentSetInstance =>
          I.parts.flatten.all (fun v => decide (v ∈ I.graph.vertices)))
        encMulticoloredIndependentSetInstance encBool := by fun_prop
    exact (h1.bool_and' h2).bool_and' h3
  have hverts : ComputableInPolyTime
      (fun I : MulticoloredIndependentSetInstance =>
        List.range (I.parts.flatten.length + I.parts.length))
      encMulticoloredIndependentSetInstance (encList encNat) := by
    simpa only [Function.comp_def,
      List.map_id'] using (map hb).comp (range.comp (unary_add' hM hkk))
  let encMU1 := encPair encMulticoloredIndependentSetInstance encUnary
  let encMU2 := encPair encMU1 encUnary
  have horig : ComputableInPolyTime
      (fun I : MulticoloredIndependentSetInstance =>
        (List.range I.parts.flatten.length).flatMap fun a =>
          ((List.range I.parts.flatten.length).filter fun b =>
            I.graph.adjBool (I.parts.flatten.getD a 0) (I.parts.flatten.getD b 0)).map
            fun b => (a, b))
      encMulticoloredIndependentSetInstance (encList (encPair encNat encNat)) := by
    apply flatMapWithInput (range.comp hM)
    apply mapWithInput
    · apply filterWithInput
        (range.comp (hM.comp (fst encMulticoloredIndependentSetInstance encUnary)))
      have hIq := (fst encMulticoloredIndependentSetInstance encUnary).comp (fst encMU1 encUnary)
      have hFq := hF.comp hIq
      exact Graph.computableInPolyTime_adjBool_comp (computableInPolyTime_mis_graph hIq)
        (listGetDWithInput hFq
          ((snd encMulticoloredIndependentSetInstance encUnary).comp (fst encMU1 encUnary)) 0)
        (listGetDWithInput hFq (snd encMU1 encUnary) 0)
    · exact (hb.comp
        ((snd encMulticoloredIndependentSetInstance encUnary).comp (fst encMU1 encUnary))).prod
        (hb.comp (snd encMU1 encUnary))
  let encMP1 := encPair encMulticoloredIndependentSetInstance (encList encNat)
  let encMP2 := encPair encMP1 encNat
  have hcl : ComputableInPolyTime
      (fun I : MulticoloredIndependentSetInstance =>
        I.parts.flatMap fun P => P.flatMap fun u =>
          (P.filter fun v => decide (u ≠ v)).map fun v =>
            (I.parts.flatten.idxOf u, I.parts.flatten.idxOf v))
      encMulticoloredIndependentSetInstance (encList (encPair encNat encNat)) := by
    apply flatMapWithInput (computableInPolyTime_mis_parts id')
    apply flatMapWithInput (snd encMulticoloredIndependentSetInstance (encList encNat))
    apply mapWithInput
    · apply filterWithInput
        ((snd encMulticoloredIndependentSetInstance (encList encNat)).comp (fst encMP1 encNat))
      exact decide_ne ((snd encMP1 encNat).comp (fst encMP2 encNat)) (snd encMP2 encNat)
    · have hFq := hF.comp ((fst encMulticoloredIndependentSetInstance (encList encNat)).comp
        ((fst encMP1 encNat).comp (fst encMP2 encNat)))
      exact (hb.comp (idxOfWithInput hFq ((snd encMP1 encNat).comp (fst encMP2 encNat)))).prod
        (hb.comp (idxOfWithInput hFq (snd encMP2 encNat)))
  have hpend : ComputableInPolyTime
      (fun I : MulticoloredIndependentSetInstance =>
        (List.range I.parts.length).flatMap fun i =>
          (I.parts.getD i []).map fun u => (I.parts.flatten.length + i, I.parts.flatten.idxOf u))
      encMulticoloredIndependentSetInstance (encList (encPair encNat encNat)) := by
    apply flatMapWithInput (range.comp hkk)
    apply mapWithInput
    · exact listGetDWithInput
        (computableInPolyTime_mis_parts (fst encMulticoloredIndependentSetInstance encUnary))
        (snd encMulticoloredIndependentSetInstance encUnary) []
    · have hIq := (fst encMulticoloredIndependentSetInstance encUnary).comp (fst encMU1 encNat)
      exact (hb.comp (unary_add' (hM.comp hIq)
          ((snd encMulticoloredIndependentSetInstance encUnary).comp (fst encMU1 encNat)))).prod
        (hb.comp (idxOfWithInput (hF.comp hIq) (snd encMU1 encNat)))
  have hbranch : ComputableInPolyTime
      (fun I : MulticoloredIndependentSetInstance =>
        let F := I.parts.flatten
        let M := F.length
        let kk := I.parts.length
        let origEdges : List (ℕ × ℕ) :=
          (List.range M).flatMap fun a =>
            ((List.range M).filter fun b => I.graph.adjBool (F.getD a 0) (F.getD b 0)).map
              fun b => (a, b)
        let cliqueEdges : List (ℕ × ℕ) :=
          I.parts.flatMap fun P =>
            P.flatMap fun u =>
              (P.filter fun v => decide (u ≠ v)).map fun v => (F.idxOf u, F.idxOf v)
        let pendantEdges : List (ℕ × ℕ) :=
          (List.range kk).flatMap fun i =>
            (I.parts.getD i []).map fun u => (M + i, F.idxOf u)
        DissociationSetInstance.mk
          ⟨List.range (M + kk), origEdges ++ cliqueEdges ++ pendantEdges⟩ (2 * kk))
      encMulticoloredIndependentSetInstance encDissociationSetInstance :=
    computableInPolyTime_dissociation_mk
      (encGraph_mk_polyTime hverts ((horig.listAppend' hcl).listAppend' hpend))
      (hb.comp (unary_mul' (const 2) hkk))
  unfold reduceMISToDissociationSet
  exact ite hvalid hbranch (const _)

/-- `MulticoloredIndependentSet` fpt-reduces to `DissociationSet`. -/
theorem fptReducible_MulticoloredIndependentSet_DissociationSet :
    FPTReducible encMulticoloredIndependentSetInstance encDissociationSetInstance (·.k) (·.k)
      MulticoloredIndependentSet DissociationSet := by
  have hnodup_iff : ∀ L : List ℕ,
      (L.zipIdx.all fun e => decide (L.idxOf e.1 = e.2)) = true ↔ L.Nodup := by
    intro L
    simp only [List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h
      rw [List.nodup_iff_injective_get]
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [List.get_eq_getElem] at hij
      have hi' := h (L[i], i) (List.mem_zipIdx_iff_getElem?.2 (by simp))
      have hj' := h (L[j], j) (List.mem_zipIdx_iff_getElem?.2 (by simp))
      rw [hij] at hi'
      exact Fin.ext (hi'.symm.trans hj')
    · intro hnd e he
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 he)
      rw [← heq, hnd.idxOf_getElem]
  refine FPTReducible.of_computableInPolyTime computableInPolyTime_reduceMISToDissociationSet
    (h := fun k => 2 * k + 1) (fun I => ?_) (fun I => ?_)
  · unfold reduceMISToDissociationSet
    by_cases hv : validMISBool I = true
    · simp only [hv, ↓reduceIte]
      simp only [validMISBool, Bool.and_eq_true, decide_eq_true_eq] at hv
      have := hv.1.1
      omega
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]; omega
  · unfold reduceMISToDissociationSet
    by_cases hv : validMISBool I = true
    · simp only [hv, ↓reduceIte]
      simp only [validMISBool, Bool.and_eq_true, decide_eq_true_eq, hnodup_iff,
        List.all_eq_true] at hv
      obtain ⟨⟨hk_len, hF_nd⟩, hF_sub⟩ := hv
      set F := I.parts.flatten
      set M := F.length
      set kk := I.parts.length
      set G' := (⟨List.range (M + kk),
        ((List.range M).flatMap fun a =>
          ((List.range M).filter fun b => I.graph.adjBool (F.getD a 0) (F.getD b 0)).map
            fun b => (a, b)) ++
        (I.parts.flatMap fun P =>
          P.flatMap fun u =>
            (P.filter fun v => decide (u ≠ v)).map fun v => (F.idxOf u, F.idxOf v)) ++
        ((List.range kk).flatMap fun i =>
          (I.parts.getD i []).map fun u => (M + i, F.idxOf u))⟩ : Graph)
      have hedge_iff : ∀ x y : ℕ, (x, y) ∈ G'.edges ↔
          (x < M ∧ y < M ∧ I.graph.toSimpleGraph.Adj (F.getD x 0) (F.getD y 0)) ∨
          (∃ P ∈ I.parts, ∃ u ∈ P, ∃ v ∈ P, u ≠ v ∧ x = F.idxOf u ∧ y = F.idxOf v) ∨
          (∃ i < kk, ∃ u ∈ I.parts.getD i [], x = M + i ∧ y = F.idxOf u) := by
        intro x y
        dsimp only [G']
        simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
          List.mem_range, Graph.adjBool_eq_true_iff, decide_eq_true_eq, Prod.mk.injEq]
        constructor
        · rintro ((⟨a, ha, b, ⟨hb, hadj⟩, rfl, rfl⟩ | ⟨P, hP, u, hu, v, ⟨hv, huv⟩, rfl, rfl⟩) |
              ⟨i, hi, u, hu, rfl, rfl⟩)
          · exact Or.inl ⟨ha, hb, hadj⟩
          · exact Or.inr (Or.inl ⟨P, hP, u, hu, v, hv, huv, rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨i, hi, u, hu, rfl, rfl⟩)
        · rintro (⟨hx, hy, hadj⟩ | ⟨P, hP, u, hu, v, hv, huv, rfl, rfl⟩ | ⟨i, hi, u, hu, rfl, rfl⟩)
          · exact Or.inl (Or.inl ⟨x, hx, y, ⟨hy, hadj⟩, rfl, rfl⟩)
          · exact Or.inl (Or.inr ⟨P, hP, u, hu, v, ⟨hv, huv⟩, rfl, rfl⟩)
          · exact Or.inr ⟨i, hi, u, hu, rfl, rfl⟩
      have part_disj : ∀ i < kk, ∀ j < kk, i ≠ j →
          ∀ u ∈ I.parts.getD i [], u ∉ I.parts.getD j [] := by
        intro i hi j hj hij u hui huj
        rw [List.getD_eq_getElem _ _ hi] at hui
        rw [List.getD_eq_getElem _ _ hj] at huj
        have hpair := (List.nodup_flatten.1 hF_nd).2
        rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
        · exact List.pairwise_iff_getElem.1 hpair i j hi hj hlt hui huj
        · exact absurd rfl hij
        · exact List.pairwise_iff_getElem.1 hpair j i hj hi hgt huj hui
      have mem_F_of_part : ∀ i < kk, ∀ u ∈ I.parts.getD i [], u ∈ F := by
        intro i hi u hu
        rw [List.getD_eq_getElem _ _ hi] at hu
        exact List.mem_flatten.2 ⟨I.parts[i], List.getElem_mem hi, hu⟩
      change (kk = I.k ∧ F.Nodup ∧ (∀ v ∈ F, v ∈ I.graph.vertices) ∧
        ∃ s : Fin I.k → ℕ,
          (∀ i : Fin I.k, s i ∈ I.parts.getD i.1 []) ∧
          (∀ i j : Fin I.k, i ≠ j → ¬ I.graph.toSimpleGraph.Adj (s i) (s j))) ↔
        ∃ S : Finset {v // v ∈ G'.vertices},
          IsDissociationSet G'.induced (S : Set _) ∧ 2 * kk ≤ S.card
      rw [← hk_len]
      constructor
      · rintro ⟨_, _, _, s, hs_mem, hs_ind⟩
        let sIdx : Fin kk → {v // v ∈ G'.vertices} := fun i =>
          ⟨F.idxOf (s i), by
            simp only [G', List.mem_range]
            exact (List.idxOf_lt_length_iff.2 (mem_F_of_part i.1 i.2 (s i) (hs_mem i))).trans_le
              (by omega)⟩
        let uIdx : Fin kk → {v // v ∈ G'.vertices} := fun i =>
          ⟨M + i.1, by simp only [G', List.mem_range]; omega⟩
        have hs_inj : Function.Injective sIdx := by
          intro i j hij
          by_contra hne
          have hsi_F := mem_F_of_part i.1 i.2 (s i) (hs_mem i)
          have hsj_F := mem_F_of_part j.1 j.2 (s j) (hs_mem j)
          have hval : F.idxOf (s i) = F.idxOf (s j) := Subtype.mk.inj hij
          have heq_s : s i = s j := by
            have h1 := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hsi_F)
            have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hsj_F)
            rw [← h1, ← h2]; simp [hval]
          exact part_disj i.1 i.2 j.1 j.2 (Fin.val_ne_of_ne hne) (s i) (hs_mem i) (heq_s ▸ hs_mem j)
        have hu_inj : Function.Injective uIdx := fun i j h =>
          Fin.ext (by have := Subtype.mk.inj h; omega)
        have hdisj_su : Disjoint (Finset.univ.map ⟨sIdx, hs_inj⟩)
            (Finset.univ.map ⟨uIdx, hu_inj⟩) := by
          rw [Finset.disjoint_left]
          intro w hws hwu
          obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hws
          obtain ⟨j, _, hjeq⟩ := Finset.mem_map.1 hwu
          have hlt : F.idxOf (s i) < M :=
            List.idxOf_lt_length_iff.2 (mem_F_of_part i.1 i.2 (s i) (hs_mem i))
          have hval : M + j.1 = F.idxOf (s i) := Subtype.mk.inj hjeq
          omega
        let S' : Finset {v // v ∈ G'.vertices} :=
          (Finset.univ.map ⟨sIdx, hs_inj⟩) ∪ (Finset.univ.map ⟨uIdx, hu_inj⟩)
        have hScard : S'.card = 2 * kk := by
          rw [Finset.card_union_of_disjoint hdisj_su, Finset.card_map, Finset.card_map,
            Finset.card_fin]; omega
        have hadj_S' : ∀ x ∈ S', ∀ y ∈ S', G'.induced.Adj x y →
            ∃ i : Fin kk, (x = sIdx i ∧ y = uIdx i) ∨ (x = uIdx i ∧ y = sIdx i) := by
          intro x hx y hy hadj_xy
          rw [Graph.induced_adj, Graph.toSimpleGraph_adj, hedge_iff, hedge_iff] at hadj_xy
          have check_edge : ∀ a b, a ∈ S' → b ∈ S' →
              ((a.1 < M ∧ b.1 < M ∧ I.graph.toSimpleGraph.Adj (F.getD a.1 0) (F.getD b.1 0)) ∨
               (∃ P ∈ I.parts, ∃ u ∈ P, ∃ v ∈ P, u ≠ v ∧ a.1 = F.idxOf u ∧ b.1 = F.idxOf v) ∨
               (∃ i < kk, ∃ u ∈ I.parts.getD i [], a.1 = M + i ∧ b.1 = F.idxOf u)) →
              ∃ i : Fin kk, (a = sIdx i ∧ b = uIdx i) ∨ (a = uIdx i ∧ b = sIdx i) := by
            intro a b haS hbS hcases
            simp only [S', Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and,
              Function.Embedding.coeFn_mk] at haS hbS
            rcases haS with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hbS with ⟨j, rfl⟩ | ⟨j, rfl⟩
            · have hsi_lt : F.idxOf (s i) < M :=
                List.idxOf_lt_length_iff.2 (mem_F_of_part i.1 i.2 _ (hs_mem i))
              have hsj_lt : F.idxOf (s j) < M :=
                List.idxOf_lt_length_iff.2 (mem_F_of_part j.1 j.2 _ (hs_mem j))
              rcases hcases with ⟨_, _, hadjG⟩ | ⟨P, hP, u, hu, v, hv, huv, hxu, hyv⟩ |
                  ⟨_, _, _, _, hMidx, _⟩
              · dsimp only [sIdx] at hadjG
                rw [List.getD_eq_getElem _ _ hsi_lt, List.getElem_idxOf hsi_lt,
                  List.getD_eq_getElem _ _ hsj_lt, List.getElem_idxOf hsj_lt] at hadjG
                have hij_ne : i ≠ j := fun h => by
                  subst h; exact I.graph.toSimpleGraph.loopless.irrefl _ hadjG
                exact (hs_ind i j hij_ne hadjG).elim
              · obtain ⟨kP, hkP, rfl⟩ := List.getElem_of_mem hP
                have hsu : s i = u := by
                  have h1 := List.getElem_idxOf hsi_lt
                  have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.2
                    (List.mem_flatten.2 ⟨I.parts[kP], List.getElem_mem hkP, hu⟩))
                  dsimp only [sIdx] at hxu
                  rw [← h1, ← h2]; simp [hxu]
                have hsv : s j = v := by
                  have h1 := List.getElem_idxOf hsj_lt
                  have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.2
                    (List.mem_flatten.2 ⟨I.parts[kP], List.getElem_mem hkP, hv⟩))
                  dsimp only [sIdx] at hyv
                  rw [← h1, ← h2]; simp [hyv]
                have hik : i.1 = kP := by
                  by_contra hne_ik
                  exact part_disj i.1 i.2 kP hkP hne_ik (s i) (hs_mem i)
                    (by rwa [List.getD_eq_getElem _ _ hkP, hsu])
                have hjk : j.1 = kP := by
                  by_contra hne_jk
                  exact part_disj j.1 j.2 kP hkP hne_jk (s j) (hs_mem j)
                    (by rwa [List.getD_eq_getElem _ _ hkP, hsv])
                have hij_eq : i = j := Fin.ext (hik.trans hjk.symm)
                subst hij_eq
                exact (huv (hsu.symm.trans hsv)).elim
              · dsimp only [sIdx] at hMidx; omega
            · rcases hcases with ⟨_, hlt, _⟩ | ⟨P, hP, _, _, v, hv, _, _, hyv⟩ |
                  ⟨_, _, _, _, hMidx, _⟩
              · dsimp only [uIdx] at hlt; omega
              · have hv_lt : F.idxOf v < M :=
                  List.idxOf_lt_length_iff.2 (List.mem_flatten.2 ⟨P, hP, hv⟩)
                dsimp only [uIdx] at hyv; omega
              · have hsi_lt : F.idxOf (s i) < M :=
                  List.idxOf_lt_length_iff.2 (mem_F_of_part i.1 i.2 _ (hs_mem i))
                dsimp only [sIdx] at hMidx; omega
            · rcases hcases with ⟨hlt, _, _⟩ | ⟨P, hP, u, hu, _, _, _, hxu, _⟩ |
                  ⟨idx, _, u, hu, hMidx, hju⟩
              · dsimp only [uIdx] at hlt; omega
              · have hu_lt : F.idxOf u < M :=
                  List.idxOf_lt_length_iff.2 (List.mem_flatten.2 ⟨P, hP, hu⟩)
                dsimp only [uIdx] at hxu; omega
              · dsimp only [uIdx, sIdx] at hMidx hju
                have hi_idx : i.1 = idx := by omega
                subst hi_idx
                have hsj_lt : F.idxOf (s j) < M :=
                  List.idxOf_lt_length_iff.2 (mem_F_of_part j.1 j.2 _ (hs_mem j))
                have hu_lt : F.idxOf u < M :=
                  List.idxOf_lt_length_iff.2 (mem_F_of_part i.1 i.2 u hu)
                have hsju : s j = u := by
                  rw [← List.getElem_idxOf hsj_lt, ← List.getElem_idxOf hu_lt]; simp [hju]
                have hij_eq : j = i := by
                  by_contra hne_ji
                  exact part_disj j.1 j.2 i.1 i.2 (Fin.val_ne_of_ne hne_ji) (s j) (hs_mem j)
                    (hsju ▸ hu)
                subst hij_eq
                exact ⟨j, Or.inr ⟨rfl, rfl⟩⟩
            · rcases hcases with ⟨hlt, _, _⟩ | ⟨P, hP, u, hu, _, _, _, hxu, _⟩ |
                  ⟨idx, hidx, u, hu, _, hyv⟩
              · dsimp only [uIdx] at hlt; omega
              · have hu_lt : F.idxOf u < M :=
                  List.idxOf_lt_length_iff.2 (List.mem_flatten.2 ⟨P, hP, hu⟩)
                dsimp only [uIdx] at hxu; omega
              · have hu_lt : F.idxOf u < M :=
                  List.idxOf_lt_length_iff.2 (mem_F_of_part idx hidx u hu)
                dsimp only [uIdx] at hyv; omega
          rcases hadj_xy.2 with hxy | hyx
          · exact check_edge x y hx hy hxy
          · obtain ⟨i, hsym⟩ := check_edge y x hy hx hyx
            exact ⟨i, hsym.symm.imp And.symm And.symm⟩
        refine ⟨S', fun a b c ha hb hc hab hac hbc => ?_, hScard.ge⟩
        have h12 := hadj_S' a ha b hb hab
        have h23 := hadj_S' b hb c hc hbc
        rcases h12 with ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
          rcases h23 with ⟨j, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · have hlt : F.idxOf (s j) < M :=
            List.idxOf_lt_length_iff.2 (mem_F_of_part j.1 j.2 _ (hs_mem j))
          have hval := congrArg Subtype.val h1; dsimp only [uIdx, sIdx] at hval; omega
        · have hij := hu_inj h1; subst hij; exact hac h2.symm
        · have hij := hs_inj h1; subst hij; exact hac h2.symm
        · have hlt : F.idxOf (s i) < M :=
            List.idxOf_lt_length_iff.2 (mem_F_of_part i.1 i.2 _ (hs_mem i))
          have hval := congrArg Subtype.val h1; dsimp only [uIdx, sIdx] at hval; omega
      · rintro ⟨S', hS'gp, hS'card⟩
        let C : Fin kk → Finset {v // v ∈ G'.vertices} := fun i =>
          Finset.univ.filter fun w =>
            w.1 = M + i.1 ∨ (w.1 < M ∧ F.getD w.1 0 ∈ I.parts.getD i.1 [])
        have hC_clique : ∀ i : Fin kk, G'.induced.IsClique (C i : Set _) := by
          intro i a ha b hb hab
          dsimp only [C] at ha hb
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          rw [Graph.induced_adj, Graph.toSimpleGraph_adj, hedge_iff, hedge_iff]
          refine ⟨Subtype.coe_ne_coe.2 hab, ?_⟩
          rcases ha with haM | ⟨ha_lt, haP⟩ <;> rcases hb with hbM | ⟨hb_lt, hbP⟩
          · exact absurd (Subtype.ext (haM.trans hbM.symm)) hab
          · left; right; right
            refine ⟨i.1, i.2, F.getD b.1 0, hbP, haM, ?_⟩
            rw [List.getD_eq_getElem _ _ hb_lt]; exact (hF_nd.idxOf_getElem b.1 hb_lt).symm
          · right; right; right
            refine ⟨i.1, i.2, F.getD a.1 0, haP, hbM, ?_⟩
            rw [List.getD_eq_getElem _ _ ha_lt]; exact (hF_nd.idxOf_getElem a.1 ha_lt).symm
          · left; right; left
            have hne_F : F.getD a.1 0 ≠ F.getD b.1 0 := by
              rw [List.getD_eq_getElem _ _ ha_lt, List.getD_eq_getElem _ _ hb_lt]
              intro heq; exact hab (Subtype.ext ((List.Nodup.getElem_inj_iff hF_nd).1 heq))
            refine ⟨I.parts.getD i.1 [], ?_, F.getD a.1 0, haP, F.getD b.1 0, hbP, hne_F, ?_, ?_⟩
            · rw [List.getD_eq_getElem _ _ i.2]; exact List.getElem_mem i.2
            · rw [List.getD_eq_getElem _ _ ha_lt]; exact (hF_nd.idxOf_getElem a.1 ha_lt).symm
            · rw [List.getD_eq_getElem _ _ hb_lt]; exact (hF_nd.idxOf_getElem b.1 hb_lt).symm
        have hC_disj : Pairwise (fun i j : Fin kk => Disjoint (C i) (C j)) := by
          intro i j hij
          rw [Finset.disjoint_left]
          intro w hwi hwj
          dsimp only [C] at hwi hwj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hwi hwj
          rcases hwi with h1 | ⟨_, hP1⟩ <;> rcases hwj with h2 | ⟨_, hP2⟩
          · exact hij (Fin.ext (by omega))
          · omega
          · omega
          · exact part_disj i.1 i.2 j.1 j.2 (Fin.val_ne_of_ne hij) _ hP1 hP2
        have hSC_le2 : ∀ i : Fin kk, (S' ∩ C i).card ≤ 2 := by
          intro i; by_contra hgt
          obtain ⟨T, hTS, hT3⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ (S' ∩ C i).card)
          obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hT3
          have ha := Finset.mem_inter.1 (@hTS a (by simp))
          have hb := Finset.mem_inter.1 (@hTS b (by simp))
          have hc := Finset.mem_inter.1 (@hTS c (by simp))
          exact hS'gp ha.1 hb.1 hc.1 (hC_clique i ha.2 hb.2 hab) hac (hC_clique i hb.2 hc.2 hbc)
        have hS'_sub_union : S' ⊆ Finset.univ.biUnion C := by
          intro w _
          rw [Finset.mem_biUnion]
          have hw_lt : w.1 < M + kk := List.mem_range.1 w.2
          by_cases hwM : w.1 < M
          · obtain ⟨P, hP, hwP⟩ := List.mem_flatten.1 (List.getElem_mem hwM)
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP
            refine ⟨⟨i, hi⟩, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ?_⟩⟩
            exact ⟨hwM, by rwa [List.getD_eq_getElem _ _ hwM, List.getD_eq_getElem _ _ hi]⟩
          · exact ⟨⟨w.1 - M, by omega⟩, Finset.mem_univ _,
              Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl (by dsimp; omega)⟩⟩
        have hS'_eq_union : S' = Finset.univ.biUnion (fun i => S' ∩ C i) := by
          ext w
          simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_inter, true_and]
          exact ⟨fun hw => let ⟨i, _, hi⟩ := Finset.mem_biUnion.1 (hS'_sub_union hw); ⟨i, hw, hi⟩,
            fun ⟨_, hw, _⟩ => hw⟩
        have hsum_eq : ∑ i : Fin kk, (S' ∩ C i).card = S'.card := by
          conv_rhs => rw [hS'_eq_union]
          exact (Finset.card_biUnion fun i _ j _ hij =>
            (hC_disj hij).mono inf_le_right inf_le_right).symm
        have hSC_eq2 : ∀ i : Fin kk, (S' ∩ C i).card = 2 := by
          intro i; by_contra hne2
          have hsum_lt : ∑ j : Fin kk, (S' ∩ C j).card < ∑ _ : Fin kk, 2 :=
            Finset.sum_lt_sum (fun j _ => hSC_le2 j)
              ⟨i, Finset.mem_univ i, by have := hSC_le2 i; omega⟩
          simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul] at hsum_lt
          omega
        have exists_in_part : ∀ i : Fin kk,
            ∃ w ∈ S' ∩ C i, w.1 < M ∧ F.getD w.1 0 ∈ I.parts.getD i.1 [] := by
          intro i
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by rw [hSC_eq2 i]; omega)
          have haC := (Finset.mem_inter.1 ha).2
          have hbC := (Finset.mem_inter.1 hb).2
          dsimp only [C] at haC hbC
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at haC hbC
          rcases haC with haM | haP
          · rcases hbC with hbM | hbP
            · exact absurd (Subtype.ext (haM.trans hbM.symm)) hab
            · exact ⟨b, hb, hbP⟩
          · exact ⟨a, ha, haP⟩
        let wOf : Fin kk → {v // v ∈ G'.vertices} := fun i => (exists_in_part i).choose
        have hw_mem : ∀ i : Fin kk, wOf i ∈ S' ∩ C i := fun i => (exists_in_part i).choose_spec.1
        have hw_lt : ∀ i : Fin kk, (wOf i).1 < M := fun i => (exists_in_part i).choose_spec.2.1
        have hw_part : ∀ i : Fin kk, F.getD (wOf i).1 0 ∈ I.parts.getD i.1 [] :=
          fun i => (exists_in_part i).choose_spec.2.2
        refine ⟨rfl, hF_nd, hF_sub, fun i => F.getD (wOf i).1 0, hw_part,
          fun i j hij hadj_orig => ?_⟩
        obtain ⟨z, hz, hzw⟩ : ∃ z ∈ S' ∩ C i, z ≠ wOf i := by
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by rw [hSC_eq2 i]; omega)
          by_cases haw : a = wOf i
          · exact ⟨b, hb, fun h => hab (haw.trans h.symm)⟩
          · exact ⟨a, ha, haw⟩
        have hadj_zw : G'.induced.Adj z (wOf i) :=
          hC_clique i (Finset.mem_inter.1 hz).2 (Finset.mem_inter.1 (hw_mem i)).2 hzw
        have hadj_wj : G'.induced.Adj (wOf i) (wOf j) := by
          rw [Graph.induced_adj, Graph.toSimpleGraph_adj, hedge_iff]
          have hne_ij : (wOf i).1 ≠ (wOf j).1 := fun h =>
            Finset.disjoint_left.1 (hC_disj hij) (Finset.mem_inter.1 (hw_mem i)).2
              (Subtype.ext h ▸ (Finset.mem_inter.1 (hw_mem j)).2)
          exact ⟨hne_ij, Or.inl (Or.inl ⟨hw_lt i, hw_lt j, hadj_orig⟩)⟩
        have hne_zj : z ≠ wOf j := fun h =>
          Finset.disjoint_left.1 (hC_disj hij) (Finset.mem_inter.1 hz).2
            (h ▸ (Finset.mem_inter.1 (hw_mem j)).2)
        exact hS'gp (Finset.mem_inter.1 hz).1 (Finset.mem_inter.1 (hw_mem i)).1
          (Finset.mem_inter.1 (hw_mem j)).1 hadj_zw hne_zj hadj_wj
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
      have hnmis : I ∉ MulticoloredIndependentSet := by
        rintro ⟨hk_len, hF_nd, hF_sub, _⟩
        apply hv
        simp only [validMISBool, Bool.and_eq_true, decide_eq_true_eq, hnodup_iff, List.all_eq_true]
        exact ⟨⟨hk_len, hF_nd⟩, hF_sub⟩
      have hndiss : (⟨⟨[], []⟩, 1⟩ : DissociationSetInstance) ∉ DissociationSet := by
        rintro ⟨S, _, hcard⟩; dsimp only at hcard
        obtain ⟨v, _⟩ := Finset.card_pos.1 (by omega : 0 < S.card)
        exact List.not_mem_nil v.2
      exact iff_of_false hnmis hndiss

/-- **`DissociationSet` is `W[1]`-hard** parameterized by `k`. -/
theorem DissociationSet_wHard :
    WHard 1 encDissociationSetInstance (·.k) DissociationSet :=
  MulticoloredIndependentSet_wHard.trans fptReducible_MulticoloredIndependentSet_DissociationSet

private def p3TripleIndices (G : Graph) : List ((ℕ × ℕ) × ℕ) :=
  let V := G.distinctVertices
  let n := V.length
  (List.range n).flatMap fun i =>
    (List.range n).flatMap fun j =>
      ((List.range n).filter fun l =>
        decide (i ≠ l) && G.adjBool (V.getD i 0) (V.getD j 0) &&
          G.adjBool (V.getD j 0) (V.getD l 0)).map
        fun l => ((i, j), l)

private lemma lt_of_mem_p3TripleIndices {G : Graph} {t : (ℕ × ℕ) × ℕ}
    (ht : t ∈ p3TripleIndices G) :
    t.1.1 < G.distinctVertices.length ∧
    t.1.2 < G.distinctVertices.length ∧
    t.2 < G.distinctVertices.length := by
  simp only [p3TripleIndices, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_range] at ht
  obtain ⟨i, hi, j, hj, l, ⟨hl, _⟩, rfl⟩ := ht
  exact ⟨hi, hj, hl⟩

private def p3CircuitGates (n : ℕ) (T : List ((ℕ × ℕ) × ℕ)) :
    List (Unbounded.Op × List ℕ) :=
  (List.range n).map (fun i => (.not, [i])) ++
    T.map (fun t => (.or 2, [n + t.1.1, n + t.1.2])) ++
    (List.range T.length).map (fun idx =>
      (.or 2, [n + n + idx, n + (T.getD idx ((0, 0), 0)).2])) ++
    [(.and T.length, (List.range T.length).map (n + n + T.length + ·))]

private def p3CircuitCode (G : Graph) : List (Unbounded.Op × List ℕ) × List ℕ :=
  let n := G.distinctVertices.length
  let T := p3TripleIndices G
  (p3CircuitGates n T, [n + n + T.length + T.length])

private lemma isCodeFrom_p3CircuitGates {n : ℕ} {T : List ((ℕ × ℕ) × ℕ)}
    (hT : ∀ t ∈ T, t.1.1 < n ∧ t.1.2 < n ∧ t.2 < n) :
    Program.IsCodeFrom Unbounded.signature n 0 (p3CircuitGates n T) := by
  rw [p3CircuitGates, Program.isCodeFrom_append, Program.isCodeFrom_append,
    Program.isCodeFrom_append]
  refine ⟨⟨⟨Program.isCodeFrom_of_forall
        (List.forall_mem_map.2 fun i hi => ⟨rfl, fun _ hx => by simp_all⟩),
      Program.isCodeFrom_of_forall (List.forall_mem_map.2 fun t ht => ⟨rfl, fun x hx => ?_⟩)⟩,
      Program.isCodeFrom_of_forall (List.forall_mem_map.2 fun idx hidx => ⟨rfl, fun x hx => ?_⟩)⟩,
    Program.isCodeFrom_of_forall (List.forall_mem_singleton.2 ⟨by simp,
      List.forall_mem_map.2 fun j hj => ?_⟩)⟩
  · obtain ⟨h1, h2, _⟩ := hT t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.length_map,
      List.length_range] at hx ⊢
    omega
  · rw [List.mem_range] at hidx
    obtain ⟨_, _, h3⟩ := hT (T.getD idx ((0, 0), 0))
      (by rw [List.getD_eq_getElem _ _ hidx]; exact List.getElem_mem hidx)
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.length_append, List.length_map,
      List.length_range] at hx ⊢
    omega
  · simp only [List.mem_range, List.length_append, List.length_map, List.length_range] at hj ⊢
    omega

private lemma isSome_ofCode_p3CircuitCode (G : Graph) :
    (Circuit.ofCode G.distinctVertices.length 1 (p3CircuitCode G) :
      Option (Circuit Unbounded.signature _ 1)).isSome := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨isCodeFrom_p3CircuitGates fun t ht => lt_of_mem_p3TripleIndices ht, rfl, ?_⟩
  simp only [p3CircuitCode, p3CircuitGates, List.mem_singleton, forall_eq, List.length_append,
    List.length_map, List.length_range, List.length_singleton]
  omega

private def p3ToCircuit (G : Graph) : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨G.distinctVertices.length,
    (Circuit.ofCode _ 1 (p3CircuitCode G)).get (isSome_ofCode_p3CircuitCode G)⟩

private lemma code_p3ToCircuit (G : Graph) : (p3ToCircuit G).2.code = p3CircuitCode G :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

private lemma evalCode_p3CircuitGates {n : ℕ} {T : List ((ℕ × ℕ) × ℕ)}
    (hT : ∀ t ∈ T, t.1.1 < n ∧ t.1.2 < n ∧ t.2 < n)
    (x : List Bool) (hx : x.length = n) :
    (evalCode Unbounded.interpretation false x (p3CircuitGates n T)).getD
        (n + n + T.length + T.length) false =
      decide (∀ t ∈ T, ¬(x.getD t.1.1 false = true ∧ x.getD t.1.2 false = true ∧
        x.getD t.2 false = true)) := by
  subst hx
  rw [p3CircuitGates, evalCode_append, evalCode_append, evalCode_append]
  have h1 : evalCode Unbounded.interpretation false x
      ((List.range x.length).map fun i => (Unbounded.Op.not, [i])) = x ++ x.map (!·) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.ext_getElem (by simp) fun i h₁ _ => ?_
      simp only [List.length_map, List.length_range] at h₁
      simp [List.getElem?_eq_getElem h₁]
    · exact List.forall_mem_map.2 fun j hj _ hi => by simp_all
  let L1 := x ++ x.map (!·)
  have h2 : evalCode Unbounded.interpretation false L1
      (T.map fun t => (Unbounded.Op.or 2, [x.length + t.1.1, x.length + t.1.2])) =
      L1 ++ T.map fun t => (!x.getD t.1.1 false || !x.getD t.1.2 false) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.map_congr_left fun t ht => ?_
      obtain ⟨h₁, h₂, _⟩ := hT t ht
      have hL1_1 : L1.getD (x.length + t.1.1) false = !x.getD t.1.1 false := by
        dsimp only [L1]
        rw [List.getD_append_right _ _ _ _ (by simp), Nat.add_sub_cancel_left,
          List.getD_eq_getElem _ _ (by simpa using h₁), List.getElem_map,
          List.getD_eq_getElem _ _ h₁]
      have hL1_2 : L1.getD (x.length + t.1.2) false = !x.getD t.1.2 false := by
        dsimp only [L1]
        rw [List.getD_append_right _ _ _ _ (by simp), Nat.add_sub_cancel_left,
          List.getD_eq_getElem _ _ (by simpa using h₂), List.getElem_map,
          List.getD_eq_getElem _ _ h₂]
      simpa [Fin.exists_fin_two] using congrArg₂ Bool.or hL1_1 hL1_2
    · refine List.forall_mem_map.2 fun t ht i hi => ?_
      obtain ⟨h₁, h₂, _⟩ := hT t ht
      dsimp only [L1]
      simp only [List.mem_cons, List.not_mem_nil, or_false, List.length_append,
        List.length_map] at hi ⊢
      omega
  let L2 := L1 ++ T.map fun t => (!x.getD t.1.1 false || !x.getD t.1.2 false)
  have h3 : evalCode Unbounded.interpretation false L2
      ((List.range T.length).map fun idx =>
        (Unbounded.Op.or 2,
          [x.length + x.length + idx, x.length + (T.getD idx ((0, 0), 0)).2])) =
      L2 ++ T.map fun t => ((!x.getD t.1.1 false || !x.getD t.1.2 false) || !x.getD t.2 false) := by
    rw [evalCode_layer]
    · simp only [List.map_map]
      congr 1
      refine List.ext_getElem (by simp) fun idx h₁ _ => ?_
      simp only [List.length_map, List.length_range] at h₁
      obtain ⟨_, _, h₃⟩ := hT T[idx] (List.getElem_mem h₁)
      have hL2_idx : L2.getD (x.length + x.length + idx) false =
          (!x.getD T[idx].1.1 false || !x.getD T[idx].1.2 false) := by
        dsimp only [L2, L1]
        rw [List.getD_append_right _ _ _ _ (by simp),
          show x.length + x.length + idx - (x ++ x.map (!·)).length = idx by simp,
          List.getD_eq_getElem _ _ (by simpa using h₁), List.getElem_map]
      have hL2_l : L2.getD (x.length + T[idx].2) false = !x.getD T[idx].2 false := by
        dsimp only [L2, L1]
        rw [List.getD_append _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp),
          show x.length + T[idx].2 - x.length = T[idx].2 by omega,
          List.getD_eq_getElem _ _ (by simpa using h₃), List.getElem_map,
          List.getD_eq_getElem _ _ h₃]
      dsimp only [Function.comp_def]
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem _ _ h₁]
      simpa [Fin.exists_fin_two] using congrArg₂ Bool.or hL2_idx hL2_l
    · refine List.forall_mem_map.2 fun idx hidx i hi => ?_
      rw [List.mem_range] at hidx
      obtain ⟨_, _, h₃⟩ := hT T[idx] (List.getElem_mem hidx)
      dsimp only [L2, L1]
      simp only [List.getD_eq_getElem _ _ hidx, List.mem_cons, List.not_mem_nil, or_false,
        List.length_append, List.length_map] at hi ⊢
      omega
  rw [h1, h2, h3, evalCode_layer]
  · let L3 := L2 ++ T.map fun t =>
      ((!x.getD t.1.1 false || !x.getD t.1.2 false) || !x.getD t.2 false)
    have hlen : L3.length = x.length + x.length + T.length + T.length := by
      dsimp only [L3, L2, L1]; simp [Nat.add_assoc]
    rw [← hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    simp only [List.map_singleton, List.getD_cons_zero, Unbounded.interpretation_and]
    rw [decide_eq_decide, List.forall_mem_iff_getElem, Fin.forall_iff]
    refine forall_congr' fun j => forall_congr' fun hj => ?_
    rw [List.getElem?_eq_getElem (by simpa using hj)]
    simp only [Option.elim_some, List.getElem_map, List.getElem_range]
    have hL2_len : x.length + x.length + T.length + j = L2.length + j := by
      dsimp only [L2, L1]; simp [Nat.add_assoc]
    rw [hL2_len,
      List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
    cases x.getD T[j].1.1 false <;> cases x.getD T[j].1.2 false <;>
      cases x.getD T[j].2 false <;> decide
  · refine List.forall_mem_singleton.2 (List.forall_mem_map.2 fun j hj => ?_)
    dsimp only [L2, L1]
    simp only [List.mem_range, List.length_append, List.length_map] at hj ⊢
    omega

private lemma le_of_mem_evalCode_p3CircuitGates (cost : Unbounded.Op → ℕ) {n : ℕ}
    {T : List ((ℕ × ℕ) × ℕ)} (hT : ∀ t ∈ T, t.1.1 < n ∧ t.1.2 < n ∧ t.2 < n)
    {c₁ c₂ c₃ c₄ : ℕ}
    (h₁ : cost Unbounded.Op.not ≤ c₁) (h₂ : cost (Unbounded.Op.or 2) ≤ c₂)
    (h₃ : cost (Unbounded.Op.or 2) ≤ c₃) (h₄ : cost (Unbounded.Op.and T.length) ≤ c₄) :
    ∀ v ∈ evalCode (depthInterpretation (σ := Unbounded.signature) cost) 0 (List.replicate n 0)
      (p3CircuitGates n T),
      v ≤ 0 + c₁ + c₂ + c₃ + c₄ := by
  rw [p3CircuitGates, evalCode_append, evalCode_append, evalCode_append]
  refine le_of_mem_evalCode_depth_layer _ _ _
    (List.forall_mem_singleton.2 (List.forall_mem_map.2 fun j hj => ?_))
    (le_of_mem_evalCode_depth_layer _ _ _ (List.forall_mem_map.2 fun idx hidx i hi => ?_)
      (le_of_mem_evalCode_depth_layer _ _ _ (List.forall_mem_map.2 fun t ht i hi => ?_)
        (le_of_mem_evalCode_depth_layer _ _ _
          (List.forall_mem_map.2 fun j hj _ hi => by simp_all)
          (fun _ hv => (List.eq_of_mem_replicate hv).le)
          (by simp [h₁]))
        (List.forall_mem_map.2 fun _ _ => h₂))
      (List.forall_mem_map.2 fun _ _ => h₃))
    (by simp [h₄])
  · simp only [List.mem_range, length_evalCode, List.length_replicate, List.length_map,
      List.length_range] at hj ⊢
    omega
  · rw [List.mem_range] at hidx
    obtain ⟨_, _, h3⟩ := hT T[idx] (List.getElem_mem hidx)
    simp only [List.getD_eq_getElem _ _ hidx, List.mem_cons, List.not_mem_nil, or_false,
      length_evalCode, List.length_replicate, List.length_map, List.length_range] at hi ⊢
    omega
  · obtain ⟨he₁, he₂, _⟩ := hT t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, length_evalCode, List.length_replicate,
      List.length_map, List.length_range] at hi ⊢
    omega

private lemma weft_p3ToCircuit_le (G : Graph) : (p3ToCircuit G).2.weft ≤ 1 := by
  refine Circuit.depthWith_le_of_evalCode _ _ fun v hv => ?_
  simpa using le_of_mem_evalCode_p3CircuitGates (largeGateCost Unbounded.signature)
    (fun t ht => lt_of_mem_p3TripleIndices ht) (c₁ := 0) (c₂ := 0) (c₃ := 0)
    (by decide) (by decide) (by decide) (largeGateCost_le_one _) v (code_p3ToCircuit G ▸ hv)

private lemma depth_p3ToCircuit_le (G : Graph) : (p3ToCircuit G).2.depth ≤ 4 := by
  rw [← Circuit.depthWith_one]
  refine Circuit.depthWith_le_of_evalCode _ _ fun v hv => ?_
  simpa using le_of_mem_evalCode_p3CircuitGates 1
    (fun t ht => lt_of_mem_p3TripleIndices ht) le_rfl le_rfl le_rfl le_rfl v
    (code_p3ToCircuit G ▸ hv)

private lemma p3ToCircuit_satisfiableWithWeight_iff (G : Graph) (k : ℕ) :
    (p3ToCircuit G).2.SatisfiableWithWeight Unbounded.interpretation k ↔
      (⟨G, k⟩ : DissociationSetInstance) ∈ DissociationSet := by
  have hout : ((p3ToCircuit G).2.outputs 0).toNat =
      G.distinctVertices.length + G.distinctVertices.length +
        (p3TripleIndices G).length + (p3TripleIndices G).length :=
    congrArg (fun c => c.2.headD 0) (code_p3ToCircuit G)
  have heval : ∀ x : Cslib.BitString (p3ToCircuit G).1,
      (p3ToCircuit G).2.eval Unbounded.interpretation x 0 =
        decide (∀ t ∈ p3TripleIndices G,
          ¬((List.ofFn x).getD t.1.1 false = true ∧
            (List.ofFn x).getD t.1.2 false = true ∧
            (List.ofFn x).getD t.2 false = true)) := fun x => by
    rw [Circuit.eval_eq_getD _ _ false, hout, code_p3ToCircuit]
    exact evalCode_p3CircuitGates (fun t ht => lt_of_mem_p3TripleIndices ht) _ List.length_ofFn
  simp only [Circuit.SatisfiableWithWeight, heval, decide_eq_true_eq, DissociationSet,
    Set.mem_ofPred_eq]
  have hn_eq : (p3ToCircuit G).1 = G.distinctVertices.length := rfl
  let V := G.distinctVertices
  let emb : Fin (p3ToCircuit G).1 ↪ {v // v ∈ G.vertices} :=
    ⟨fun i => ⟨V[i.1]'(hn_eq ▸ i.2), Graph.mem_distinctVertices.1 (List.getElem_mem (hn_eq ▸ i.2))⟩,
      fun i j h => Fin.ext ((List.Nodup.getElem_inj_iff G.nodup_distinctVertices).1
        (Subtype.mk.inj h))⟩
  constructor
  · rintro ⟨x, hwt, hno_t⟩
    let S : Finset {v // v ∈ G.vertices} :=
      (Finset.univ.filter fun i : Fin (p3ToCircuit G).1 => x i = true).map emb
    have hScard : S.card = k := (Finset.card_map _).trans hwt
    refine ⟨S, fun u v w hu hv hw huv huw hvw => ?_, hScard.ge⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hu)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hv)
    obtain ⟨l, hl, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hw)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hl
    have hi2 : i.1 < V.length := hn_eq ▸ i.2
    have hj2 : j.1 < V.length := hn_eq ▸ j.2
    have hl2 : l.1 < V.length := hn_eq ▸ l.2
    have hil : i.1 ≠ l.1 := fun h => huw (congrArg emb (Fin.ext h))
    have ht_mem : ((i.1, j.1), l.1) ∈ p3TripleIndices G := by
      simp only [p3TripleIndices, List.mem_flatMap, List.mem_map, List.mem_filter,
        List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff]
      refine ⟨i.1, hi2, j.1, hj2, l.1, ⟨hl2, ⟨⟨hil, ?_⟩, ?_⟩⟩, rfl⟩
      · rw [List.getD_eq_getElem _ _ hi2, List.getD_eq_getElem _ _ hj2]; exact huv
      · rw [List.getD_eq_getElem _ _ hj2, List.getD_eq_getElem _ _ hl2]; exact hvw
    apply hno_t _ ht_mem
    refine ⟨?_, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.2), List.getElem_ofFn]
      exact hi
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.2), List.getElem_ofFn]
      exact hj
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact l.2), List.getElem_ofFn]
      exact hl
  · rintro ⟨S₀, hS₀gp, hS₀card⟩
    obtain ⟨S, hSS₀, hScard⟩ := Finset.exists_subset_card_eq hS₀card
    have hSgp : IsDissociationSet G.induced (S : Set _) :=
      fun _ _ _ hu hv hw => hS₀gp (hSS₀ hu) (hSS₀ hv) (hSS₀ hw)
    let x : Cslib.BitString (p3ToCircuit G).1 := fun i => decide (emb i ∈ S)
    have hmap_S :
        (Finset.univ.filter fun i : Fin (p3ToCircuit G).1 => x i = true).map emb = S := by
      ext u
      dsimp only [x]
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      refine ⟨fun ⟨_, huS, heq⟩ => heq ▸ huS, fun huS => ?_⟩
      have huV : u.1 ∈ V := Graph.mem_distinctVertices.2 u.2
      have hlt : V.idxOf u.1 < (p3ToCircuit G).1 := hn_eq.symm ▸ List.idxOf_lt_length_iff.2 huV
      have hemb_u : emb ⟨V.idxOf u.1, hlt⟩ = u :=
        Subtype.ext (List.getElem_idxOf (List.idxOf_lt_length_iff.2 huV))
      exact ⟨⟨V.idxOf u.1, hlt⟩, hemb_u.symm ▸ huS, hemb_u⟩
    have hwt : Cslib.BitString.weight x = k := by
      change (Finset.univ.filter fun i : Fin (p3ToCircuit G).1 => x i = true).card = k
      rw [← Finset.card_map emb, hmap_S, hScard]
    refine ⟨x, hwt, fun t ht ⟨h1, h2, h3⟩ => ?_⟩
    simp only [p3TripleIndices, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq, Graph.adjBool_eq_true_iff] at ht
    obtain ⟨i, hi, j, hj, l, ⟨hl, ⟨⟨hil, hij_adj⟩, hjl_adj⟩⟩, rfl⟩ := ht
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hij_adj
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hl] at hjl_adj
    have hi' : i < (p3ToCircuit G).1 := hn_eq.symm ▸ hi
    have hj' : j < (p3ToCircuit G).1 := hn_eq.symm ▸ hj
    have hl' : l < (p3ToCircuit G).1 := hn_eq.symm ▸ hl
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi'), List.getElem_ofFn] at h1
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hj'), List.getElem_ofFn] at h2
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hl'), List.getElem_ofFn] at h3
    have h1S : emb ⟨i, hi'⟩ ∈ S := of_decide_eq_true h1
    have h2S : emb ⟨j, hj'⟩ ∈ S := of_decide_eq_true h2
    have h3S : emb ⟨l, hl'⟩ ∈ S := of_decide_eq_true h3
    have hul_ne : emb ⟨i, hi'⟩ ≠ emb ⟨l, hl'⟩ := fun heq =>
      hil ((List.Nodup.getElem_inj_iff G.nodup_distinctVertices).1 (Subtype.mk.inj heq))
    exact hSgp h1S h2S h3S hij_adj hul_ne hjl_adj

private lemma computableInPolyTime_p3CircuitCode :
    ComputableInPolyTime p3CircuitCode encGraph (Circuit.encCode Unbounded.encOp) := by
  have hV := Graph.computableInPolyTime_distinctVertices
  have hn : ComputableInPolyTime (fun G : Graph => G.distinctVertices.length) encGraph encUnary :=
    (length_list encNat).comp hV
  have hb := unary_to_binary
  let encG1 := encPair encGraph encUnary
  let encG2 := encPair encG1 encUnary
  let encG3 := encPair encG2 encUnary
  let encTr := encPair (encPair encUnary encUnary) encUnary
  have hT : ComputableInPolyTime p3TripleIndices encGraph (encList encTr) := by
    unfold p3TripleIndices
    apply flatMapWithInput (range.comp hn)
    apply flatMapWithInput (range.comp (hn.comp (fst encGraph encUnary)))
    apply mapWithInput
    · apply filterWithInput
        (range.comp (hn.comp ((fst encGraph encUnary).comp (fst encG1 encUnary))))
      have hi3 : ComputableInPolyTime (fun q : ((Graph × ℕ) × ℕ) × ℕ => q.1.1.2) encG3 encUnary :=
        (snd encGraph encUnary).comp ((fst encG1 encUnary).comp (fst encG2 encUnary))
      have hj3 : ComputableInPolyTime (fun q : ((Graph × ℕ) × ℕ) × ℕ => q.1.2) encG3 encUnary :=
        (snd encG1 encUnary).comp (fst encG2 encUnary)
      have hl3 : ComputableInPolyTime (fun q : ((Graph × ℕ) × ℕ) × ℕ => q.2) encG3 encUnary :=
        snd encG2 encUnary
      have hne : ComputableInPolyTime
          (fun q : ((Graph × ℕ) × ℕ) × ℕ => decide (q.1.1.2 ≠ q.2)) encG3 encBool :=
        decide_ne hi3 hl3
      have hgq : ComputableInPolyTime
          (fun q : ((Graph × ℕ) × ℕ) × ℕ => q.1.1.1) encG3 encGraph :=
        (fst encGraph encUnary).comp ((fst encG1 encUnary).comp (fst encG2 encUnary))
      have hVq : ComputableInPolyTime
          (fun q : ((Graph × ℕ) × ℕ) × ℕ => q.1.1.1.distinctVertices) encG3 (encList encNat) :=
        hV.comp hgq
      have ha1 : ComputableInPolyTime
          (fun q : ((Graph × ℕ) × ℕ) × ℕ =>
            q.1.1.1.adjBool (q.1.1.1.distinctVertices.getD q.1.1.2 0)
              (q.1.1.1.distinctVertices.getD q.1.2 0)) encG3 encBool :=
        Graph.computableInPolyTime_adjBool_comp hgq
          (listGetDWithInput hVq hi3 0) (listGetDWithInput hVq hj3 0)
      have ha2 : ComputableInPolyTime
          (fun q : ((Graph × ℕ) × ℕ) × ℕ =>
            q.1.1.1.adjBool (q.1.1.1.distinctVertices.getD q.1.2 0)
              (q.1.1.1.distinctVertices.getD q.2 0)) encG3 encBool :=
        Graph.computableInPolyTime_adjBool_comp hgq
          (listGetDWithInput hVq hj3 0) (listGetDWithInput hVq hl3 0)
      exact (hne.bool_and' ha1).bool_and' ha2
    · exact (((snd encGraph encUnary).comp ((fst encG1 encUnary).comp (fst encG2 encUnary))).prod
        ((snd encG1 encUnary).comp (fst encG2 encUnary))).prod (snd encG2 encUnary)
  have hm : ComputableInPolyTime (fun G : Graph => (p3TripleIndices G).length)
      encGraph encUnary := (length_list encTr).comp hT
  have hnot : ComputableInPolyTime
      (fun G : Graph => (List.range G.distinctVertices.length).map
        fun i => ((Unbounded.Op.not, [i]) : Unbounded.Op × List ℕ))
      encGraph (encList (Circuit.encGate Unbounded.encOp)) :=
    (range.comp hn).mapWithInput
      ((const Unbounded.Op.not).prod (cons' (hb.comp (snd encGraph encUnary)) (const [])))
  have hor1 : ComputableInPolyTime
      (fun G : Graph => (p3TripleIndices G).map fun t =>
        ((Unbounded.Op.or 2,
          [G.distinctVertices.length + t.1.1, G.distinctVertices.length + t.1.2]) :
          Unbounded.Op × List ℕ))
      encGraph (encList (Circuit.encGate Unbounded.encOp)) := by
    apply hT.mapWithInput
    have hng : ComputableInPolyTime
        (fun q : Graph × ((ℕ × ℕ) × ℕ) => q.1.distinctVertices.length)
        (encPair encGraph encTr) encUnary := hn.comp (fst encGraph encTr)
    have ht1 : ComputableInPolyTime
        (fun q : Graph × ((ℕ × ℕ) × ℕ) => q.2.1.1) (encPair encGraph encTr) encUnary :=
      (fst encUnary encUnary).comp ((fst (encPair encUnary encUnary) encUnary).comp
        (snd encGraph encTr))
    have ht2 : ComputableInPolyTime
        (fun q : Graph × ((ℕ × ℕ) × ℕ) => q.2.1.2) (encPair encGraph encTr) encUnary :=
      (snd encUnary encUnary).comp ((fst (encPair encUnary encUnary) encUnary).comp
        (snd encGraph encTr))
    exact (const (Unbounded.Op.or 2)).prod
      (cons' (hb.comp (unary_add' hng ht1)) (cons' (hb.comp (unary_add' hng ht2)) (const [])))
  have hor2 : ComputableInPolyTime
      (fun G : Graph => (List.range (p3TripleIndices G).length).map fun idx =>
        ((Unbounded.Op.or 2,
          [G.distinctVertices.length + G.distinctVertices.length + idx,
           G.distinctVertices.length + ((p3TripleIndices G).getD idx ((0, 0), 0)).2]) :
          Unbounded.Op × List ℕ))
      encGraph (encList (Circuit.encGate Unbounded.encOp)) := by
    apply (range.comp hm).mapWithInput
    have hTq : ComputableInPolyTime (fun q : Graph × ℕ => p3TripleIndices q.1) encG1
        (encList encTr) := hT.comp (fst encGraph encUnary)
    have hnq : ComputableInPolyTime (fun q : Graph × ℕ => q.1.distinctVertices.length) encG1
        encUnary := hn.comp (fst encGraph encUnary)
    have hl_idx : ComputableInPolyTime
        (fun q : Graph × ℕ => ((p3TripleIndices q.1).getD q.2 ((0, 0), 0)).2) encG1 encUnary :=
      (snd (encPair encUnary encUnary) encUnary).comp
        (listGetDWithInput hTq (snd encGraph encUnary) ((0, 0), 0))
    exact (const (Unbounded.Op.or 2)).prod
      (cons' (hb.comp (unary_add' (unary_add' hnq hnq) (snd encGraph encUnary)))
        (cons' (hb.comp (unary_add' hnq hl_idx)) (const [])))
  have hand : ComputableInPolyTime
      (fun G : Graph => [((Unbounded.Op.and (p3TripleIndices G).length,
        (List.range (p3TripleIndices G).length).map
          (G.distinctVertices.length + G.distinctVertices.length +
            (p3TripleIndices G).length + ·)) : Unbounded.Op × List ℕ)])
      encGraph (encList (Circuit.encGate Unbounded.encOp)) :=
    cons' ((Unbounded.computableInPolyTime_and.comp hm).prod
      ((range.comp hm).mapWithInput
        (hb.comp (unary_add'
          ((unary_add' (unary_add' hn hn) hm).comp (fst encGraph encUnary))
          (snd encGraph encUnary))))) (const [])
  unfold p3CircuitCode p3CircuitGates
  dsimp only
  exact (((hnot.listAppend' hor1).listAppend' hor2).listAppend' hand).prod
    (cons' (hb.comp (unary_add' (unary_add' (unary_add' hn hn) hm) hm)) (const []))

private def dissocToWCS (I : DissociationSetInstance) : WCSInstance 1 4 :=
  ⟨⟨p3ToCircuit I.graph, weft_p3ToCircuit_le I.graph, depth_p3ToCircuit_le I.graph⟩, I.k⟩

private lemma computableInPolyTime_dissocToWCS :
    ComputableInPolyTime dissocToWCS encDissociationSetInstance (encWCS 1 4) := by
  have hc := computableInPolyTime_p3CircuitCode
  have hV := Graph.computableInPolyTime_distinctVertices
  have hn : ComputableInPolyTime
      (fun I : DissociationSetInstance => I.graph.distinctVertices.length)
      encDissociationSetInstance encUnary :=
    (length_list encNat).comp (hV.comp (by fun_prop))
  refine (by fun_prop : ComputableInPolyTime
      (fun I : DissociationSetInstance =>
        ((I.graph.distinctVertices.length, p3CircuitCode I.graph), I.k))
      encDissociationSetInstance
      (encPair (encPair encUnary (Circuit.encCode Unbounded.encOp)) encNat)).of_enc_eq
    fun ⟨G, k⟩ => ?_
  simp only [dissocToWCS, encWCS_apply, encPair_apply, encWeftCircuit_apply,
    Circuit.encCircuit_apply, code_p3ToCircuit]
  rfl

/-- **`DissociationSet` belongs to `W[1]`**, via a weft-`1`, depth-`4` Boolean circuit
(`WCS 1 4`). -/
theorem DissociationSet_mem_W_one :
    DissociationSet ∈ W 1 encDissociationSetInstance (·.k) :=
  ⟨4, FPTReducible.of_computableInPolyTime computableInPolyTime_dissocToWCS (h := id)
    (fun _ => le_rfl) fun ⟨G, k⟩ => (p3ToCircuit_satisfiableWithWeight_iff G k).symm⟩

/-- **`DissociationSet` is `W[1]`-complete** parameterized by `k`. -/
theorem DissociationSet_wComplete :
    DissociationSet ∈ W 1 encDissociationSetInstance (·.k) ∧
      WHard 1 encDissociationSetInstance (·.k) DissociationSet :=
  ⟨DissociationSet_mem_W_one, DissociationSet_wHard⟩

/-- **`DissociationSet` belongs to `XP`** parameterized by `k`. -/
theorem DissociationSet_mem_XP :
    DissociationSet ∈ XP encDissociationSetInstance (·.k) :=
  W_subset_XP 1 DissociationSet_mem_W_one

end Cslib.Complexity
