/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.VertexCover
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Strong `NP`-completeness of `IndependentSet` and `VertexCover` with unary target sizes

In contrast to `Knapsack` (`Cslib.Complexity.Knapsack.unary_mem_P`), both `IndependentSet` and
`VertexCover` remain `NP`-complete when their target parameter (`m` or `k`) is encoded in unary
(`encIndependentSetUnary`, `encVertexCoverUnary`), because every satisfiable instance `(G, t)` has
`t ≤ |G.distinctVertices|` and any instance with `t > |G.distinctVertices|` can be clamped in
polynomial time (via `ComputableInPolyTime.binary_min_unary'`) to the unsatisfiable unary target
`|G.distinctVertices| + 1` [Garey and Johnson].

This provides reusable unary-target `NP`-completeness sources for strong `NP`-completeness
reductions whose output encodings require the target size in `encUnary`.

## Main definitions

* `Cslib.Complexity.encIndependentSetUnary`: `IndependentSetInstance` with target `m` in unary.
* `Cslib.Complexity.encVertexCoverUnary`: `VertexCoverInstance` with target `k` in unary.
* `Cslib.Complexity.IndependentSet.clampTarget`, `Cslib.Complexity.VertexCover.clampTarget`:
  polynomial-time binary-to-unary target clamping reductions.

## Main results

* `Cslib.Complexity.IndependentSet.unary_mem_NP`,
  `Cslib.Complexity.IndependentSet.unary_npHard`,
  `Cslib.Complexity.IndependentSet.unary_npComplete`: `NPComplete encIndependentSetUnary
  IndependentSet`.
* `Cslib.Complexity.VertexCover.unary_mem_NP`,
  `Cslib.Complexity.VertexCover.unary_npHard`,
  `Cslib.Complexity.VertexCover.unary_npComplete`: `NPComplete encVertexCoverUnary VertexCover`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- Encoding of `IndependentSetInstance` with framed `encGraph` and unary target `m`. -/
enc_structure encIndependentSetUnary : IndependentSetInstance where
  graph : encGraph,
  m : encUnary

attribute [fun_prop] encIndependentSetUnary_graph_polyTime
  encIndependentSetUnary_m_polyTime encIndependentSetUnary_mk_polyTime

/-- Encoding of `VertexCoverInstance` with framed `encGraph` and unary target `k`. -/
enc_structure encVertexCoverUnary : VertexCoverInstance where
  graph : encGraph,
  k : encUnary

attribute [fun_prop] encVertexCoverUnary_graph_polyTime
  encVertexCoverUnary_k_polyTime encVertexCoverUnary_mk_polyTime

namespace IndependentSet

/-- Converting `encIndependentSetUnary` to binary `encIndependentSetInstance` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_unary_to_binary :
    ComputableInPolyTime (fun x : IndependentSetInstance => x)
      encIndependentSetUnary encIndependentSetInstance :=
  (encIndependentSetInstance_mk_polyTime
    (encIndependentSetUnary_graph_polyTime id')
    (unary_to_binary.comp (encIndependentSetUnary_m_polyTime id'))).of_enc_eq fun _ => rfl

/-- Clamp a binary target `x.m` to `x.graph.distinctVertices.length + 1` whenever it exceeds the
number of distinct declared vertices, preserving membership in `IndependentSet` while bounding the
output target in unary. -/
def clampTarget (x : IndependentSetInstance) : IndependentSetInstance :=
  let n := x.graph.distinctVertices.length
  let mMin := min n x.m
  ⟨x.graph, if mMin == x.m then mMin else n + 1⟩

/-- `clampTarget` preserves membership in `IndependentSet`. -/
theorem clampTarget_mem_iff (x : IndependentSetInstance) :
    clampTarget x ∈ IndependentSet ↔ x ∈ IndependentSet := by
  have hm_le_of_mem : ∀ y : IndependentSetInstance, y ∈ IndependentSet →
      y.m ≤ y.graph.distinctVertices.length := by
    intro y hy
    classical
    obtain ⟨S, hsub, _, hcard⟩ := mem_IndependentSet_iff.mp hy
    rw [← hcard]
    have hsub' : S ⊆ y.graph.distinctVertices.toFinset := fun v hv =>
      List.mem_toFinset.mpr (y.graph.mem_distinctVertices.mpr (hsub v hv))
    simpa [List.toFinset_card_of_nodup y.graph.nodup_distinctVertices] using
      Finset.card_le_card hsub'
  unfold clampTarget
  dsimp only
  set n := x.graph.distinctVertices.length
  by_cases hle : x.m ≤ n
  · simp only [Nat.min_eq_right hle, beq_self_eq_true, ↓reduceIte]
  · have hne : (min n x.m == x.m) = false := beq_eq_false_iff_ne.mpr (by omega)
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact iff_of_false (fun h => by have := hm_le_of_mem _ h; dsimp at this; omega)
      (fun h => hle (hm_le_of_mem x h))

/-- `clampTarget` runs in polynomial time from binary `encIndependentSetInstance` to unary
`encIndependentSetUnary`. -/
@[fun_prop]
theorem computableInPolyTime_clampTarget :
    ComputableInPolyTime clampTarget encIndependentSetInstance encIndependentSetUnary := by
  have hg := encIndependentSetInstance_graph_polyTime id'
  have hm := encIndependentSetInstance_m_polyTime id'
  have hn := (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp hg)
  have hmMin := binary_min_unary' hn hm
  have htest := ComputableInPolyTime.beq (unary_to_binary.comp hmMin) hm
  exact (encIndependentSetUnary_mk_polyTime hg
    (ite htest hmMin (unary_add' hn (const 1)))).of_enc_eq fun _ => rfl

/-- `IndependentSet` with unary target size belongs to `NP`. -/
theorem unary_mem_NP : IndependentSet ∈ NP encIndependentSetUnary :=
  PolyTimeReducible.mem_NP
    ⟨id, computableInPolyTime_unary_to_binary, fun _ => Iff.rfl⟩
    IndependentSet_npComplete.1

/-- `IndependentSet` remains `NP`-hard when the target size `m` is encoded in unary. -/
theorem unary_npHard : NPHard encIndependentSetUnary IndependentSet :=
  IndependentSet_npHard.trans
    ⟨clampTarget, computableInPolyTime_clampTarget, fun x => (clampTarget_mem_iff x).symm⟩

/-- **Strong `NP`-completeness of `IndependentSet`**: `IndependentSet` is `NP`-complete under
`encIndependentSetUnary`. -/
theorem unary_npComplete : NPComplete encIndependentSetUnary IndependentSet :=
  ⟨unary_mem_NP, unary_npHard⟩

end IndependentSet

namespace VertexCover

/-- Converting `encVertexCoverUnary` to binary `encVertexCoverInstance` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_unary_to_binary :
    ComputableInPolyTime (fun x : VertexCoverInstance => x)
      encVertexCoverUnary encVertexCoverInstance :=
  (encVertexCoverInstance_mk_polyTime
    (encVertexCoverUnary_graph_polyTime id')
    (unary_to_binary.comp (encVertexCoverUnary_k_polyTime id'))).of_enc_eq fun _ => rfl

/-- Clamp a binary target `x.k` to `x.graph.distinctVertices.length + 1` whenever it exceeds the
number of distinct declared vertices, preserving membership in `VertexCover` while bounding the
output target in unary. -/
def clampTarget (x : VertexCoverInstance) : VertexCoverInstance :=
  let n := x.graph.distinctVertices.length
  let kMin := min n x.k
  ⟨x.graph, if kMin == x.k then kMin else n + 1⟩

/-- `clampTarget` preserves membership in `VertexCover`. -/
theorem clampTarget_mem_iff (x : VertexCoverInstance) :
    clampTarget x ∈ VertexCover ↔ x ∈ VertexCover := by
  have hk_le_of_mem : ∀ y : VertexCoverInstance, y ∈ VertexCover →
      y.k ≤ y.graph.distinctVertices.length := by
    intro y hy
    classical
    obtain ⟨S, hsub, _, hcard⟩ := mem_VertexCover_iff.mp hy
    rw [← hcard]
    have hsub' : S ⊆ y.graph.distinctVertices.toFinset := fun v hv =>
      List.mem_toFinset.mpr (y.graph.mem_distinctVertices.mpr (hsub v hv))
    simpa [List.toFinset_card_of_nodup y.graph.nodup_distinctVertices] using
      Finset.card_le_card hsub'
  unfold clampTarget
  dsimp only
  set n := x.graph.distinctVertices.length
  by_cases hle : x.k ≤ n
  · simp only [Nat.min_eq_right hle, beq_self_eq_true, ↓reduceIte]
  · have hne : (min n x.k == x.k) = false := beq_eq_false_iff_ne.mpr (by omega)
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact iff_of_false (fun h => by have := hk_le_of_mem _ h; dsimp at this; omega)
      (fun h => hle (hk_le_of_mem x h))

/-- `clampTarget` runs in polynomial time from binary `encVertexCoverInstance` to unary
`encVertexCoverUnary`. -/
@[fun_prop]
theorem computableInPolyTime_clampTarget :
    ComputableInPolyTime clampTarget encVertexCoverInstance encVertexCoverUnary := by
  have hg := encVertexCoverInstance_graph_polyTime id'
  have hk := encVertexCoverInstance_k_polyTime id'
  have hn := (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp hg)
  have hkMin := binary_min_unary' hn hk
  have htest := ComputableInPolyTime.beq (unary_to_binary.comp hkMin) hk
  exact (encVertexCoverUnary_mk_polyTime hg
    (ite htest hkMin (unary_add' hn (const 1)))).of_enc_eq fun _ => rfl

/-- `VertexCover` with unary target size belongs to `NP`. -/
theorem unary_mem_NP : VertexCover ∈ NP encVertexCoverUnary :=
  PolyTimeReducible.mem_NP
    ⟨id, computableInPolyTime_unary_to_binary, fun _ => Iff.rfl⟩
    VertexCover_npComplete.1

/-- `VertexCover` remains `NP`-hard when the target size `k` is encoded in unary. -/
theorem unary_npHard : NPHard encVertexCoverUnary VertexCover :=
  VertexCover_npHard.trans
    ⟨clampTarget, computableInPolyTime_clampTarget, fun x => (clampTarget_mem_iff x).symm⟩

/-- **Strong `NP`-completeness of `VertexCover`**: `VertexCover` is `NP`-complete under
`encVertexCoverUnary`. -/
theorem unary_npComplete : NPComplete encVertexCoverUnary VertexCover :=
  ⟨unary_mem_NP, unary_npHard⟩

end VertexCover

end Cslib.Complexity
