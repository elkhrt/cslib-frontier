/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.NNRat.Defs

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Foundations.Data.Rat.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.GetD

/-!
# Polynomial-time rational summation and weighted independent set

This module contributes two reusable complexity-theoretic building blocks to `cslib-frontier`:

1. **Polynomial-time summation on `ℚ` and `ℚ≥0`**:
   `Turing.MultiTapeTM.ComputableInPolyTime.rat_list_sum` proves that summing a framed list of
   rational numbers (`List ℚ`) is computable in polynomial time under `encList encRat` and `encRat`
   via the multiplicative numerator-plus-denominator potential `|q.num| + q.den`, together with the
   induced binary encoding `Turing.MultiTapeTM.encNNRat` and polynomial-time arithmetic/summation
   rules for nonnegative rationals `ℚ≥0`.
2. **`NP`-completeness of `WeightedIndependentSet`**:
   `Cslib.Complexity.WeightedIndependentSet` formulates the nonnegative rational vertex-weighted
   independent set decision problem on `Cslib.Complexity.Graph` and proves `NP`-completeness
   (`Cslib.Complexity.WeightedIndependentSet_npComplete`) via a polynomial-time verifier and Karp
   reduction from `Cslib.Complexity.IndependentSet`.

## Main definitions

* `Turing.MultiTapeTM.encNNRat`: binary encoding of `ℚ≥0` via `encRat`.
* `Cslib.Complexity.WeightedIndependentSetInstance`,
  `Cslib.Complexity.encWeightedIndependentSetInstance`,
  `Cslib.Complexity.WeightedIndependentSet`: decision problem for rational-weighted independent set.
* `Cslib.Complexity.IndependentSet.toWeightedIndependentSet`: unit-weight reduction from
  `IndependentSet` to `WeightedIndependentSet`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.rat_list_sum`,
  `Turing.MultiTapeTM.ComputableInPolyTime.nnrat_list_sum`: summing framed `ℚ` and `ℚ≥0` lists in
  polynomial time.
* `Cslib.Complexity.WeightedIndependentSet.mem_NP`,
  `Cslib.Complexity.polyTimeReducible_IndependentSet_WeightedIndependentSet`,
  `Cslib.Complexity.WeightedIndependentSet_npHard`,
  `Cslib.Complexity.WeightedIndependentSet_npComplete`: `NP`-completeness of
  `WeightedIndependentSet`.
-/

public section

namespace Turing.MultiTapeTM

/-- Binary encoding of nonnegative rationals `ℚ≥0` via coercion into `encRat`. -/
@[expose] def encNNRat : ℚ≥0 ↪ List Bool where
  toFun q := encRat (q : ℚ)
  inj' _ _ h := NNRat.coe_injective (encRat.injective h)

@[simp]
theorem encNNRat_apply (q : ℚ≥0) : encNNRat q = encRat (q : ℚ) := rfl

namespace ComputableInPolyTime

/-- Coercing `ℚ≥0 → ℚ` is computable in polynomial time. -/
@[fun_prop]
theorem nnrat_coe : ComputableInPolyTime (fun q : ℚ≥0 => (q : ℚ)) encNNRat encRat :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Casting a binary natural `ℕ → ℚ≥0` is computable in polynomial time. -/
@[fun_prop]
theorem nnrat_natCast : ComputableInPolyTime (fun n : ℕ => (n : ℚ≥0)) encNat encNNRat :=
  rat_natCast.of_enc_eq fun n => by simp [encNNRat_apply]

/-- Addition on `ℚ≥0` is computable in polynomial time. -/
@[fun_prop]
theorem nnrat_add :
    ComputableInPolyTime (fun p : ℚ≥0 × ℚ≥0 => p.1 + p.2) (encPair encNNRat encNNRat) encNNRat :=
  (rat_add' (nnrat_coe.comp (fst encNNRat encNNRat))
    (nnrat_coe.comp (snd encNNRat encNNRat))).of_enc_eq fun p => by
      simp [encNNRat_apply]

/-- Order comparison `≤` on `ℚ≥0` is computable in polynomial time. -/
@[fun_prop]
theorem nnrat_le :
    ComputableInPolyTime (fun p : ℚ≥0 × ℚ≥0 => decide (p.1 ≤ p.2))
      (encPair encNNRat encNNRat) encBool :=
  (rat_le' (nnrat_coe.comp (fst encNNRat encNNRat))
    (nnrat_coe.comp (snd encNNRat encNNRat))).of_enc_eq fun _ =>
      congrArg encBool (decide_eq_decide.mpr NNRat.coe_le_coe.symm)

/-- Order comparison `≤` on computed `ℚ≥0` values is computable in polynomial time. -/
theorem nnrat_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℚ≥0}
    (hleft : ComputableInPolyTime left input encNNRat)
    (hright : ComputableInPolyTime right input encNNRat) :
    ComputableInPolyTime (fun x => decide (left x ≤ right x)) input encBool :=
  (hleft.prod hright).trans nnrat_le

private def ratPot (q : ℚ) : ℕ := q.num.natAbs + q.den

private theorem ratPot_add_le (a b : ℚ) : ratPot (a + b) ≤ ratPot a * ratPot b := by
  unfold ratPot
  have hnum := Rat.natAbs_num_add_le a b
  have hden := Rat.den_add_le a b
  have hid : (a.num.natAbs + a.den) * (b.num.natAbs + b.den) =
      a.num.natAbs * b.num.natAbs + (a.num.natAbs * b.den + b.num.natAbs * a.den) +
        a.den * b.den := by ring
  omega

private theorem ratPot_le_two_pow_succ (q : ℚ) : ratPot q ≤ 2 ^ ((encRat q).length + 1) := by
  unfold ratPot
  have h1 : q.num.natAbs < 2 ^ (encRat q).length := natAbs_num_lt_two_pow_length_encRat q
  have h2 : q.den < 2 ^ (encRat q).length := den_lt_two_pow_length_encRat q
  have : 2 ^ ((encRat q).length + 1) = 2 ^ (encRat q).length + 2 ^ (encRat q).length := by
    ring
  omega

private theorem ratPot_foldl_add_le (xs : List ℚ) (acc : ℚ) {L : ℕ}
    (hxs : ∀ q ∈ xs, (encRat q).length ≤ L) :
    ratPot (xs.foldl (· + ·) acc) ≤ ratPot acc * (2 ^ (L + 1)) ^ xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons q xs ih =>
    rw [List.foldl_cons, List.length_cons, Nat.pow_succ (2 ^ (L + 1)) xs.length]
    have hq : ratPot q ≤ 2 ^ (L + 1) := (ratPot_le_two_pow_succ q).trans
      (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right (hxs q List.mem_cons_self) 1))
    have hstep : ratPot (acc + q) ≤ ratPot acc * 2 ^ (L + 1) :=
      (ratPot_add_le acc q).trans (Nat.mul_le_mul_left _ hq)
    exact (ih (acc + q) fun r hr => hxs r (List.mem_cons_of_mem _ hr)).trans <| by
      calc ratPot (acc + q) * (2 ^ (L + 1)) ^ xs.length
          ≤ (ratPot acc * 2 ^ (L + 1)) * (2 ^ (L + 1)) ^ xs.length :=
            Nat.mul_le_mul_right _ hstep
        _ = ratPot acc * ((2 ^ (L + 1)) ^ xs.length * 2 ^ (L + 1)) := by ring

private theorem foldl_add_eq_add_sum {M : Type*} [AddCommMonoid M] (xs : List M) (acc : M) :
    xs.foldl (· + ·) acc = acc + xs.sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

/-- Summing a framed list of rational numbers is computable in polynomial time. -/
@[fun_prop]
theorem rat_list_sum :
    ComputableInPolyTime (fun l : List ℚ => l.sum) (encList encRat) encRat := by
  have hB : PolyBounded (fun l : List ℚ => (encList encRat l).length)
      (fun l => 6 * (((encList encRat l).length + 1) * (encList encRat l).length) + 6) :=
    PolyBounded.of_polynomiallyBounded (fun l : List ℚ => (encList encRat l).length)
      (bound := fun L => 6 * ((L + 1) * L) + 6) (by fun_prop)
  have hfold := foldl' (encA := encRat) (encL := encList encRat) (encB := encRat)
    (list := id) (init := fun _ => (0 : ℚ)) (step := (· + ·)) id' (const 0) rat_add hB
    (fun l i _ => by
      dsimp only [id_eq]
      set L := (encList encRat l).length
      set M := (L + 1) * L
      set s := (l.take i).foldl (· + ·) (0 : ℚ)
      have htake_mem : ∀ q ∈ l.take i, (encRat q).length ≤ L := fun q hq =>
        SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat) l q
          (List.mem_of_mem_take hq)
      have hlen_le : (l.take i).length ≤ L :=
        (List.length_take_le' i l).trans
          (SizedListEncoding.length_le (encA := encRat) (encL := encList encRat) l)
      have hpot0 : ratPot (0 : ℚ) = 1 := by simp [ratPot]
      have hpot : ratPot s ≤ 2 ^ M := by
        calc ratPot s ≤ 1 * (2 ^ (L + 1)) ^ (l.take i).length := by
              simpa [s, hpot0] using ratPot_foldl_add_le (l.take i) 0 htake_mem
          _ = 2 ^ ((L + 1) * (l.take i).length) := by rw [one_mul, ← Nat.pow_mul]
          _ ≤ 2 ^ M :=
              Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left (L + 1) hlen_le)
      have hnum : s.num.natAbs ≤ 2 ^ M := le_trans (by simp [ratPot]) hpot
      have hden : s.den ≤ 2 ^ M := le_trans (by simp [ratPot]) hpot
      have hsize : (2 ^ M).size ≤ M * 2 + 1 := by
        simpa [show (2 : ℕ).size = 2 by decide] using Nat.size_pow_le 2 M
      have henc : (encRat s).length ≤ 2 * (2 ^ M).size + (2 ^ M).size + 3 :=
        length_encRat_le s hnum hden
      omega)
  simpa only [foldl_add_eq_add_sum, zero_add, id_eq] using hfold

private theorem coe_nnrat_list_sum (l : List ℚ≥0) :
    ((l.sum : ℚ≥0) : ℚ) = (l.map fun q : ℚ≥0 => (q : ℚ)).sum := by
  induction l with
  | nil => simp
  | cons q qs ih => simp [ih]

/-- Summing a framed list of nonnegative rationals is computable in polynomial time. -/
@[fun_prop]
theorem nnrat_list_sum :
    ComputableInPolyTime (fun l : List ℚ≥0 => l.sum) (encList encNNRat) encNNRat := by
  have hmap : ComputableInPolyTime (fun l : List ℚ≥0 => l.map fun q : ℚ≥0 => (q : ℚ))
      (encList encNNRat) (encList encRat) := by fun_prop
  exact (rat_list_sum.comp hmap).of_enc_eq fun l => by
    simp [encNNRat_apply, coe_nnrat_list_sum]

/-- Summing a computed framed list of nonnegative rationals is computable in polynomial time. -/
@[fun_prop]
theorem nnrat_list_sum' {α : Type} {input : α ↪ List Bool} {f : α → List ℚ≥0}
    (hf : ComputableInPolyTime f input (encList encNNRat)) :
    ComputableInPolyTime (fun x => (f x).sum) input encNNRat :=
  nnrat_list_sum.comp hf

end ComputableInPolyTime

end Turing.MultiTapeTM

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- An instance `(graph, weights, threshold)` of **Weighted Independent Set** on `Graph`, where
`weights.getD i 0` assigns a nonnegative rational weight to the `i`-th distinct declared vertex
`graph.distinctVertices[i]`. -/
@[ext]
structure WeightedIndependentSetInstance where
  /-- Underlying graph on declared natural-number vertices. -/
  graph : Graph
  /-- Nonnegative rational weights indexed along `graph.distinctVertices`. -/
  weights : List ℚ≥0
  /-- Target total weight threshold. -/
  threshold : ℚ≥0
  deriving DecidableEq

/-- Framed multi-tape Turing encoding of `WeightedIndependentSetInstance`. -/
enc_structure encWeightedIndependentSetInstance : WeightedIndependentSetInstance where
  graph : encGraph,
  weights : (encList encNNRat),
  threshold : encNNRat

attribute [fun_prop] encWeightedIndependentSetInstance_graph_polyTime
  encWeightedIndependentSetInstance_weights_polyTime
  encWeightedIndependentSetInstance_threshold_polyTime
  encWeightedIndependentSetInstance_mk_polyTime

/-- Weight of the `i`-th distinct declared vertex in `x`. -/
def WeightedIndependentSetInstance.vertexWeight (x : WeightedIndependentSetInstance)
    (i : Fin x.graph.distinctVertices.length) : ℚ≥0 :=
  x.weights.getD i.val 0

/-- Instances admitting an independent subset of declared vertices of total weight at least
`threshold`. -/
def WeightedIndependentSet : Set WeightedIndependentSetInstance :=
  {x | ∃ S : Finset (Fin x.graph.distinctVertices.length),
    x.graph.induced.IsIndepSet ((S.map x.graph.vertexEquiv.toEmbedding :
      Finset {v // v ∈ x.graph.vertices}) : Set {v // v ∈ x.graph.vertices}) ∧
    x.threshold ≤ ∑ i ∈ S, x.vertexWeight i}

/-- Executable certificate verifier for `WeightedIndependentSet`. -/
def WeightedIndependentSet.verifier (p : WeightedIndependentSetInstance × List Bool) : Bool :=
  let vs := p.1.graph.distinctVertices
  let n := vs.length
  let mask := p.2
  let indep := (List.range n).all fun i =>
    (List.range n).all fun j =>
      !(mask.getD i false && mask.getD j false && p.1.graph.adjBool (vs.getD i 0) (vs.getD j 0))
  let wt := ((List.range n).map fun i =>
    if mask.getD i false then p.1.weights.getD i 0 else 0).sum
  indep && decide (p.1.threshold ≤ wt)

@[fun_prop]
theorem WeightedIndependentSet.computableInPolyTime_verifier :
    ComputableInPolyTime WeightedIndependentSet.verifier
      (encPair encWeightedIndependentSetInstance encBits) encBool := by
  unfold WeightedIndependentSet.verifier
  dsimp only
  refine bool_and' ?_ ?_
  · apply allWithInput (range.comp (by fun_prop))
    apply allWithInput (range.comp (by fun_prop))
    refine bool_not.comp (bool_and' (bool_and' (by fun_prop) (by fun_prop)) ?_)
    exact Graph.computableInPolyTime_adjBool_comp (by fun_prop) (by fun_prop) (by fun_prop)
  · exact nnrat_le' (by fun_prop) (nnrat_list_sum' (by fun_prop))

private theorem sum_map_range_eq_sum_fin {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ a : Fin n, f a.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_singleton,
      List.sum_singleton, Fin.sum_univ_castSucc]
    rfl

/-- `WeightedIndependentSet` belongs to `NP`. -/
theorem WeightedIndependentSet.mem_NP :
    WeightedIndependentSet ∈ NP encWeightedIndependentSetInstance := by
  refine ⟨Polynomial.X, WeightedIndependentSet.verifier,
    WeightedIndependentSet.computableInPolyTime_verifier, fun x => ?_⟩
  set vs := x.graph.distinctVertices
  set n := vs.length
  simp only [WeightedIndependentSet, Set.mem_ofPred_eq, Polynomial.eval_X,
    WeightedIndependentSet.verifier, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨S, hS_ind, hS_wt⟩
    let L := (encWeightedIndependentSetInstance x).length
    let cert0 : List Bool := (List.range n).map fun i =>
      if h : i < n then decide (⟨i, h⟩ ∈ S) else false
    let cert : List Bool := cert0 ++ List.replicate (L - n) false
    have hn_le : n ≤ L :=
      x.graph.length_distinctVertices_le.trans (encWeightedIndependentSetInstance_graph_length_le x)
    have hcert_len : cert.length = L := by
      simp only [cert, cert0, List.length_append, List.length_map, List.length_range,
        List.length_replicate]
      omega
    have hcert_get : ∀ i : Fin n, cert.getD i.val false = decide (i ∈ S) := fun i => by
      have hi0 : i.val < cert0.length := by simp [cert0]
      simp [cert, cert0, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0, i.isLt]
    refine ⟨cert, hcert_len, ?_, ?_⟩
    · simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_imp,
        Bool.and_eq_true]
      intro i hi j hj ⟨hmi, hmj⟩
      let iF : Fin n := ⟨i, hi⟩
      let jF : Fin n := ⟨j, hj⟩
      have hiS : iF ∈ S := decide_eq_true_eq.mp ((hcert_get iF).symm.trans hmi)
      have hjS : jF ∈ S := decide_eq_true_eq.mp ((hcert_get jF).symm.trans hmj)
      rw [Bool.eq_false_iff, ne_eq, Graph.adjBool_eq_true_iff]
      intro hadj
      have hij : iF ≠ jF := by
        intro heq
        have hv : vs.getD i 0 = vs.getD j 0 := by rw [show i = j from congrArg Fin.val heq]
        exact x.graph.toSimpleGraph.ne_of_adj hadj hv
      have hadj_ind : x.graph.induced.Adj (x.graph.vertexEquiv iF) (x.graph.vertexEquiv jF) := by
        rw [Graph.induced_adj, x.graph.vertexEquiv_apply, x.graph.vertexEquiv_apply]
        exact hadj
      exact hS_ind (Finset.mem_coe.mpr (Finset.mem_map_of_mem _ hiS))
        (Finset.mem_coe.mpr (Finset.mem_map_of_mem _ hjS))
        (x.graph.vertexEquiv.injective.ne hij) hadj_ind
    · have hsum : ((List.range n).map fun i =>
          if cert.getD i false = true then x.weights.getD i 0 else 0).sum =
          ∑ i ∈ S, x.vertexWeight i := by
        rw [sum_map_range_eq_sum_fin]
        simp only [hcert_get, decide_eq_true_eq, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.univ_inter]
        rfl
      rwa [hsum]
  · rintro ⟨cert, -, hind, hwt⟩
    let S : Finset (Fin n) := Finset.univ.filter fun i => cert.getD i.val false = true
    refine ⟨S, ?_, ?_⟩
    · rw [Finset.coe_map]
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ _ hadj
      simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_imp,
        Bool.and_eq_true] at hind
      have hi_cert : cert.getD i.val false = true := (Finset.mem_filter.mp hi).2
      have hj_cert : cert.getD j.val false = true := (Finset.mem_filter.mp hj).2
      have hfalse := hind i.val i.isLt j.val j.isLt ⟨hi_cert, hj_cert⟩
      change x.graph.induced.Adj (x.graph.vertexEquiv i) (x.graph.vertexEquiv j) at hadj
      rw [Graph.induced_adj, x.graph.vertexEquiv_apply, x.graph.vertexEquiv_apply,
        ← Graph.adjBool_eq_true_iff] at hadj
      exact Bool.false_ne_true (hfalse.symm.trans hadj)
    · have hsum : ((List.range n).map fun i =>
          if cert.getD i false = true then x.weights.getD i 0 else 0).sum =
          ∑ i ∈ S, x.vertexWeight i := by
        rw [sum_map_range_eq_sum_fin, ← Finset.sum_filter]
        rfl
      rwa [← hsum]

/-- Unit-weight reduction from `IndependentSet` to `WeightedIndependentSet`. -/
def IndependentSet.toWeightedIndependentSet (x : IndependentSetInstance) :
    WeightedIndependentSetInstance where
  graph := x.graph
  weights := List.replicate x.graph.distinctVertices.length (1 : ℚ≥0)
  threshold := (x.m : ℚ≥0)

@[fun_prop]
theorem IndependentSet.computableInPolyTime_toWeightedIndependentSet :
    ComputableInPolyTime IndependentSet.toWeightedIndependentSet
      encIndependentSetInstance encWeightedIndependentSetInstance := by
  unfold IndependentSet.toWeightedIndependentSet
  fun_prop

theorem IndependentSet.toWeightedIndependentSet_mem_iff {x : IndependentSetInstance} :
    IndependentSet.toWeightedIndependentSet x ∈ WeightedIndependentSet ↔ x ∈ IndependentSet := by
  simp only [WeightedIndependentSet, IndependentSet, Set.mem_ofPred_eq,
    SimpleGraph.isNIndepSet_iff]
  dsimp only [IndependentSet.toWeightedIndependentSet, WeightedIndependentSetInstance.vertexWeight]
  let e := x.graph.vertexEquiv
  have hwt : ∀ S : Finset (Fin x.graph.distinctVertices.length),
      (∑ i ∈ S, (List.replicate x.graph.distinctVertices.length (1 : ℚ≥0)).getD i.val 0) =
        (S.card : ℚ≥0) := by
    intro S
    have h1 : ∀ i : Fin x.graph.distinctVertices.length,
        (List.replicate x.graph.distinctVertices.length (1 : ℚ≥0)).getD i.val 0 = 1 :=
      fun i => by simp [List.getD_eq_getElem?_getD, i.isLt]
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    simp
  refine ⟨?_, ?_⟩
  · rintro ⟨S, hS_ind, hS_le⟩
    rw [hwt S] at hS_le
    have hm : x.m ≤ S.card := (Nat.cast_le (α := ℚ≥0)).mp hS_le
    obtain ⟨S₀, hS₀_sub, hS₀_card⟩ := Finset.exists_subset_card_eq hm
    refine ⟨S₀.map e.toEmbedding, ?_, (Finset.card_map _).trans hS₀_card⟩
    exact hS_ind.mono (Finset.coe_subset.mpr (Finset.map_subset_map.mpr hS₀_sub))
  · rintro ⟨T, hT_ind, hT_card⟩
    let S : Finset (Fin x.graph.distinctVertices.length) := T.map e.symm.toEmbedding
    have hmap : S.map e.toEmbedding = T := by
      ext v
      simp [S, e]
    refine ⟨S, by rw [hmap]; exact hT_ind, ?_⟩
    rw [hwt S]
    have hcard : S.card = x.m := (Finset.card_map _).trans hT_card
    exact le_of_eq (congrArg Nat.cast hcard.symm)

/-- `IndependentSet` reduces in polynomial time to `WeightedIndependentSet`. -/
theorem polyTimeReducible_IndependentSet_WeightedIndependentSet :
    PolyTimeReducible encIndependentSetInstance encWeightedIndependentSetInstance
      IndependentSet WeightedIndependentSet :=
  ⟨IndependentSet.toWeightedIndependentSet,
    IndependentSet.computableInPolyTime_toWeightedIndependentSet,
    fun _ => IndependentSet.toWeightedIndependentSet_mem_iff.symm⟩

/-- `WeightedIndependentSet` is `NP`-hard. -/
theorem WeightedIndependentSet_npHard :
    NPHard encWeightedIndependentSetInstance WeightedIndependentSet :=
  IndependentSet_npComplete.2.trans polyTimeReducible_IndependentSet_WeightedIndependentSet

/-- `WeightedIndependentSet` is `NP`-complete. -/
theorem WeightedIndependentSet_npComplete :
    NPComplete encWeightedIndependentSetInstance WeightedIndependentSet :=
  ⟨WeightedIndependentSet.mem_NP, WeightedIndependentSet_npHard⟩

end Cslib.Complexity
