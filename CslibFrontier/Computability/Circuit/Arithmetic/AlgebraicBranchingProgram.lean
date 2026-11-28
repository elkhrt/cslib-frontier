/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant.Projection
public import CslibFrontier.Computability.Circuit.Arithmetic.DeterminantalComplexity
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type

import CslibFrontier.Foundations.LinearAlgebra.Matrix.BranchingProgramDeterminant
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algebraic Branching Programs and Determinant Equivalence

This module defines edge-labeled directed acyclic algebraic branching programs (ABPs) over a
commutative ring `K` allowing parallel edges, establishes their closure under addition,
multiplication, affine substitution, and constant-arity composition over `ZMod p`, and proves
the polynomial equivalence between ABP size and determinantal complexity
.

## Main definitions

* `CslibFrontier.Computability.Circuit.ABP`: an edge-labeled DAG on `Fin (innerVerts + 2)` in
  topological order with source `0`, sink `Fin.last (innerVerts + 1)`, and parallel edges
  labeled by variables or constants.
* `CslibFrontier.Computability.Circuit.ABP.size`: number of vertices plus number of edges.
* `CslibFrontier.Computability.Circuit.ABP.poly`: the formal multivariate polynomial computed as the
  sum of edge-label products over all source-to-sink paths.
* `CslibFrontier.Computability.Circuit.abpComplexity`: minimum ABP size of a polynomial in `ℕ∞`.
* `CslibFrontier.Computability.Circuit.projDetComplexity`: minimum dimension `m` of a specialization
  matrix (projection of `(genericMatrix K m).det`) computing a polynomial.

## Main results

* `CslibFrontier.Computability.Circuit.ABP.isSubstABP_subdivide`: eliminating parallel edges by
  subdivision turns an ABP of size `s` into a strictly upper-triangular specialization matrix.
* `CslibFrontier.Computability.Circuit.ABP.isProjection_det`: every polynomial computed by an ABP
  of size `s` is a projection of `(genericMatrix K s).det`.
* `CslibFrontier.Computability.Circuit.ABP.add`, `ABP.mul`: closure under addition and
  multiplication with size at most `P.size + Q.size`.
* `CslibFrontier.Computability.Circuit.projDetComplexity_le_abpComplexity`:
  `projDetComplexity f ≤ abpComplexity f`.
-/

public section

namespace CslibFrontier.Computability.Circuit

open MvPolynomial
open Cslib.Circuits.Arithmetic
open scoped Matrix

universe u v

/-! ### Edge-labeled DAG algebraic branching programs -/

/-- A single directed edge in a topological-order algebraic branching program on `Fin (k + 2)`,
labeled by a variable `σ` or ring constant `K`. -/
@[ext]
public structure ABPEdge (K : Type u) (σ : Type v) (k : ℕ) where
  /-- Source vertex in `Fin (k + 2)`. -/
  src : Fin (k + 2)
  /-- Target vertex in `Fin (k + 2)`. -/
  dst : Fin (k + 2)
  /-- Strict topological ordering constraint. -/
  lt : src < dst
  /-- Variable (`Sum.inl`) or ring constant (`Sum.inr`) edge label. -/
  label : σ ⊕ K

/-- The polynomial `X i` or `C c` attached to an ABP edge label. -/
@[expose]
public noncomputable def abpLabelPoly {K : Type u} [CommSemiring K] {σ : Type v} (l : σ ⊕ K) :
    MvPolynomial σ K :=
  Sum.elim MvPolynomial.X MvPolynomial.C l

@[simp]
public theorem abpLabelPoly_inl {K : Type u} [CommSemiring K] {σ : Type v} (i : σ) :
    abpLabelPoly (K := K) (Sum.inl i) = MvPolynomial.X i := rfl

@[simp]
public theorem abpLabelPoly_inr {K : Type u} [CommSemiring K] {σ : Type v} (c : K) :
    abpLabelPoly (K := K) (σ := σ) (Sum.inr c) = MvPolynomial.C c := rfl

/-- Every ABP edge label evaluates to a projection substitution entry. -/
public theorem isSubstEntry_abpLabelPoly {K : Type u} [CommSemiring K] {σ : Type v} (l : σ ⊕ K) :
    IsSubstEntry (abpLabelPoly l) :=
  ⟨l, rfl⟩

/-- An algebraic branching program (ABP) over a commutative ring `K` in variables `σ`: a directed
acyclic graph on `Fin (innerVerts + 2)` in topological order with source `0`, sink
`Fin.last (innerVerts + 1)`, and a list of labeled edges allowing parallel edges. -/
@[ext]
public structure ABP (K : Type u) (σ : Type v) where
  /-- Number of internal vertices beyond the source `0` and sink `Fin.last (innerVerts + 1)`. -/
  innerVerts : ℕ
  /-- Edge list in topological order; parallel edges are allowed. -/
  edges : List (ABPEdge K σ innerVerts)

namespace ABP

variable {K : Type u} {σ : Type v}

/-- Number of vertices `innerVerts + 2` in an ABP. -/
@[expose]
public def numVerts (P : ABP K σ) : ℕ := P.innerVerts + 2

/-- Size of an ABP: total number of vertices plus total number of edges. -/
@[expose]
public def size (P : ABP K σ) : ℕ := P.numVerts + P.edges.length

@[simp]
public theorem numVerts_mk (k : ℕ) (es : List (ABPEdge K σ k)) :
    (ABP.mk k es).numVerts = k + 2 := rfl

@[simp]
public theorem size_mk (k : ℕ) (es : List (ABPEdge K σ k)) :
    (ABP.mk k es).size = k + 2 + es.length := rfl

/-- Explicit vertex-plus-edge decomposition of `ABP.size`. -/
public theorem size_eq_innerVerts_add_two_add_length (P : ABP K σ) :
    P.size = P.innerVerts + 2 + P.edges.length := rfl

/-- Every ABP has size at least `2` (source and sink). -/
public theorem two_le_size (P : ABP K σ) : 2 ≤ P.size := by
  simp only [size, numVerts]; omega

/-- The vertex count `innerVerts + 2` is bounded by `P.size`. -/
public theorem innerVerts_add_two_le_size (P : ABP K σ) : P.innerVerts + 2 ≤ P.size :=
  Nat.le_add_right _ _

/-- The edge count `edges.length` is bounded by `P.size`. -/
public theorem edges_length_le_size (P : ABP K σ) : P.edges.length ≤ P.size :=
  Nat.le_add_left _ _

/-- Strong-recursive sum of edge-label products over all paths from source `0` to `j`. -/
public noncomputable def nodePoly [CommSemiring K] (P : ABP K σ) (j : Fin (P.innerVerts + 2)) :
    MvPolynomial σ K :=
  if j = 0 then 1
  else
    (P.edges.map fun e : ABPEdge K σ P.innerVerts =>
      if h : e.dst = j then
        have : e.src.1 < j.1 := h ▸ e.lt
        nodePoly P e.src * abpLabelPoly e.label
      else 0).sum
termination_by j.1

/-- Path-sum polynomial at source `0` is `1`. -/
@[simp]
public theorem nodePoly_zero [CommSemiring K] (P : ABP K σ) : P.nodePoly 0 = 1 := by
  unfold nodePoly; simp

/-- Unfolding equation for `nodePoly` at a nonzero vertex `j ≠ 0`. -/
public theorem nodePoly_of_ne_zero [CommSemiring K] (P : ABP K σ) {j : Fin (P.innerVerts + 2)}
    (hj : j ≠ 0) :
    P.nodePoly j =
      (P.edges.map fun e =>
        if e.dst = j then P.nodePoly e.src * abpLabelPoly e.label else 0).sum := by
  conv_lhs => unfold nodePoly
  simp only [hj, ↓reduceIte]
  rfl

/-- The formal multivariate polynomial computed by an ABP (path sum at the sink). -/
@[expose]
public noncomputable def poly [CommSemiring K] (P : ABP K σ) : MvPolynomial σ K :=
  P.nodePoly (Fin.last (P.innerVerts + 1))

/-- Characterization of `P.poly` as the path-sum polynomial at the sink
`Fin.last (innerVerts + 1)`. -/
public theorem poly_eq_nodePoly_last [CommSemiring K] (P : ABP K σ) :
    P.poly = P.nodePoly (Fin.last (P.innerVerts + 1)) := rfl

/-- Evaluation of an ABP at a variable assignment `v : σ → K`. -/
@[expose]
public noncomputable def eval [CommSemiring K] (P : ABP K σ) (v : σ → K) : K :=
  MvPolynomial.aeval v P.poly

/-- Characterization of `P.eval v` as `MvPolynomial.aeval v P.poly`. -/
public theorem eval_eq_aeval_poly [CommSemiring K] (P : ABP K σ) (v : σ → K) :
    P.eval v = MvPolynomial.aeval v P.poly := rfl

/-- Weighted adjacency matrix of an ABP (summing parallel edge labels). -/
public noncomputable def adjMatrix [CommSemiring K] (P : ABP K σ) :
    Matrix (Fin (P.innerVerts + 2)) (Fin (P.innerVerts + 2)) (MvPolynomial σ K) :=
  Matrix.of fun i j =>
    (P.edges.map fun e => if e.src = i ∧ e.dst = j then abpLabelPoly e.label else 0).sum

/-- The adjacency matrix of an ABP is strictly upper triangular. -/
public theorem adjMatrix_eq_zero_of_le [CommSemiring K] (P : ABP K σ)
    (i j : Fin (P.innerVerts + 2)) (hji : j ≤ i) :
    P.adjMatrix i j = 0 := by
  simp only [adjMatrix, Matrix.of_apply]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
  split_ifs with h
  · exact absurd (lt_of_lt_of_le (h.1 ▸ h.2 ▸ e.lt) hji) (lt_irrefl _)
  · rfl

/-- Uniqueness of the path-sum vector `q = Pi.single 0 1 + q ᵥ* N` for a strictly
upper-triangular matrix `N`. -/
public theorem pathSum_unique {R : Type*} [CommSemiring R] {m : ℕ} [NeZero m]
    {N : Matrix (Fin m) (Fin m) R} (hN : ∀ i j, j ≤ i → N i j = 0)
    {q₁ q₂ : Fin m → R} (hq₁ : q₁ = Pi.single 0 1 + q₁ ᵥ* N)
    (hq₂ : q₂ = Pi.single 0 1 + q₂ ᵥ* N) :
    q₁ = q₂ := by
  suffices h : ∀ (k : ℕ) (j : Fin m), j.1 = k → q₁ j = q₂ j from
    funext fun j => h j.1 j rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro j hj
    rw [congrFun hq₁ j, congrFun hq₂ j]
    simp only [Pi.add_apply, Matrix.vecMul, dotProduct]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : i < j
    · rw [ih i.1 (hj ▸ hij) i rfl]
    · rw [hN i j (not_lt.mp hij), mul_zero, mul_zero]

private theorem list_sum_if_dst_eq {R : Type*} [CommSemiring R] {k : ℕ}
    (edges : List (ABPEdge K σ k)) (f : Fin (k + 2) → R)
    (g : ABPEdge K σ k → R) (j : Fin (k + 2)) :
    (edges.map fun e => if e.dst = j then f e.src * g e else 0).sum =
      ∑ i : Fin (k + 2),
        f i * (edges.map fun e => if e.src = i ∧ e.dst = j then g e else 0).sum := by
  induction edges with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have hsplit : (if e.dst = j then f e.src * g e else 0) =
        ∑ i : Fin (k + 2), f i * (if e.src = i ∧ e.dst = j then g e else 0) := by
      by_cases hd : e.dst = j
      · simp [hd]
      · simp [hd]
    rw [hsplit, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring

/-- `nodePoly` satisfies the linear path-sum equation `q = Pi.single 0 1 + q ᵥ* adjMatrix`. -/
public theorem nodePoly_eq_pathSum [CommSemiring K] (P : ABP K σ) :
    P.nodePoly = Pi.single 0 1 + P.nodePoly ᵥ* P.adjMatrix := by
  funext j
  by_cases hj : j = 0
  · subst hj
    have h0 : (P.nodePoly ᵥ* P.adjMatrix) 0 = 0 := by
      simp only [Matrix.vecMul, dotProduct]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [P.adjMatrix_eq_zero_of_le i 0 (Fin.zero_le i), mul_zero]
    simp [h0]
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, zero_add, Matrix.vecMul, dotProduct]
    rw [P.nodePoly_of_ne_zero hj]
    exact list_sum_if_dst_eq P.edges P.nodePoly (fun e => abpLabelPoly e.label) j

/-! ### Reusable order-preserving block subdivision of vertices -/

section Subdivision

/-- Vertex index of original vertex `v` after inserting `w` midpoints per edge. -/
@[expose]
public def subPosVal {k m : ℕ} (dstOf : Fin m → Fin (k + 2)) (w : ℕ) (v : Fin (k + 2)) : ℕ :=
  v.1 + w * (Finset.univ.filter fun r : Fin m => dstOf r ≤ v).card

/-- Vertex index of the `j`-th midpoint inserted on edge `r`. -/
@[expose]
public def subMidVal {k m w : ℕ} (dstOf : Fin m → Fin (k + 2)) (r : Fin m) (j : Fin w) : ℕ :=
  (dstOf r).1 + w * (Finset.univ.filter fun r' : Fin m => dstOf r' < dstOf r).card +
    w * (Finset.univ.filter fun r' : Fin m => r' < r ∧ dstOf r' = dstOf r).card + j.1

public theorem subPosVal_zero {k m : ℕ} {dstOf : Fin m → Fin (k + 2)}
    (hdst : ∀ r, 0 < dstOf r) (w : ℕ) :
    subPosVal dstOf w 0 = 0 := by
  simp only [subPosVal, Fin.val_zero, zero_add, mul_eq_zero, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  right; intro r _; exact not_le_of_gt (hdst r)

public theorem subPosVal_last {k m : ℕ} (dstOf : Fin m → Fin (k + 2)) (w : ℕ) :
    subPosVal dstOf w (Fin.last (k + 1)) = (k + w * m) + 1 := by
  have hf : (Finset.univ.filter fun r : Fin m => dstOf r ≤ Fin.last (k + 1)) = Finset.univ := by
    ext r; simp [Fin.le_last]
  simp only [subPosVal, Fin.val_last, hf, Finset.card_univ, Fintype.card_fin]
  omega

public theorem subPosVal_strictMono {k m : ℕ} (dstOf : Fin m → Fin (k + 2)) (w : ℕ) :
    StrictMono (subPosVal dstOf w) := by
  intro a b hab
  have hsub : (Finset.univ.filter fun r : Fin m => dstOf r ≤ a) ⊆
      (Finset.univ.filter fun r : Fin m => dstOf r ≤ b) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact le_trans hr (le_of_lt hab)
  have hc := Nat.mul_le_mul_left w (Finset.card_le_card hsub)
  have hv : a.1 < b.1 := hab
  simp only [subPosVal]
  omega

public theorem subPosVal_lt_subMidVal {k m w : ℕ} {dstOf : Fin m → Fin (k + 2)}
    {v : Fin (k + 2)} {r : Fin m} (hv : v < dstOf r) (j : Fin w) :
    subPosVal dstOf w v < subMidVal dstOf r j := by
  have hsub : (Finset.univ.filter fun r' : Fin m => dstOf r' ≤ v) ⊆
      (Finset.univ.filter fun r' : Fin m => dstOf r' < dstOf r) := by
    intro r' hr'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr' ⊢
    exact lt_of_le_of_lt hr' hv
  have hc := Nat.mul_le_mul_left w (Finset.card_le_card hsub)
  have hlt : v.1 < (dstOf r).1 := hv
  simp only [subPosVal, subMidVal]
  omega

public theorem subMidVal_lt_subPosVal {k m w : ℕ} (dstOf : Fin m → Fin (k + 2))
    (r : Fin m) (j : Fin w) :
    subMidVal dstOf r j < subPosVal dstOf w (dstOf r) := by
  have hdisj : Disjoint
      (Finset.univ.filter fun r' : Fin m => dstOf r' < dstOf r)
      (Finset.univ.filter fun r' : Fin m => dstOf r' = dstOf r) := by
    rw [Finset.disjoint_filter]
    intro r' _ h1 h2; exact ne_of_lt h1 h2
  have hunion :
      (Finset.univ.filter fun r' : Fin m => dstOf r' < dstOf r) ∪
        (Finset.univ.filter fun r' : Fin m => dstOf r' = dstOf r) =
      (Finset.univ.filter fun r' : Fin m => dstOf r' ≤ dstOf r) := by
    ext r'; simp [le_iff_lt_or_eq]
  have hstrict :
      (Finset.univ.filter fun r' : Fin m => r' < r ∧ dstOf r' = dstOf r) ⊂
      (Finset.univ.filter fun r' : Fin m => dstOf r' = dstOf r) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun r' hr' => ?_, fun heq => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr' ⊢; exact hr'.2
    · have hr : r ∈ Finset.univ.filter fun r' : Fin m => dstOf r' = dstOf r := by simp
      rw [← heq] at hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      exact lt_irrefl r hr.1
  have hlt1 : (Finset.univ.filter fun r' : Fin m => r' < r ∧ dstOf r' = dstOf r).card + 1 ≤
      (Finset.univ.filter fun r' : Fin m => dstOf r' = dstOf r).card :=
    Finset.card_lt_card hstrict
  have hcard_eq : (Finset.univ.filter fun r' : Fin m => dstOf r' < dstOf r).card +
      (Finset.univ.filter fun r' : Fin m => dstOf r' = dstOf r).card =
      (Finset.univ.filter fun r' : Fin m => dstOf r' ≤ dstOf r).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hj := j.2
  have hmul : w * ((Finset.univ.filter fun r' : Fin m => r' < r ∧ dstOf r' = dstOf r).card) + w ≤
      w * (Finset.univ.filter fun r' : Fin m => dstOf r' = dstOf r).card := by
    calc w * _ + w = w * (_ + 1) := by ring
      _ ≤ w * _ := Nat.mul_le_mul_left w hlt1
  have hmul2 : w * (Finset.univ.filter fun r' : Fin m => dstOf r' < dstOf r).card +
      w * (Finset.univ.filter fun r' : Fin m => dstOf r' = dstOf r).card =
      w * (Finset.univ.filter fun r' : Fin m => dstOf r' ≤ dstOf r).card := by
    rw [← mul_add, hcard_eq]
  simp only [subPosVal, subMidVal]
  omega

public theorem subPosVal_ne_subMidVal {k m w : ℕ} (dstOf : Fin m → Fin (k + 2))
    (v : Fin (k + 2)) (r : Fin m) (j : Fin w) :
    subPosVal dstOf w v ≠ subMidVal dstOf r j := by
  by_cases hdv : dstOf r ≤ v
  · exact ne_of_gt (lt_of_lt_of_le (subMidVal_lt_subPosVal dstOf r j)
      ((subPosVal_strictMono dstOf w).monotone hdv))
  · exact ne_of_lt (subPosVal_lt_subMidVal (not_le.mp hdv) j)

public theorem subMidVal_injective {k m w : ℕ} (dstOf : Fin m → Fin (k + 2)) :
    Function.Injective (fun p : Fin m × Fin w => subMidVal dstOf p.1 p.2) := by
  rintro ⟨r₁, j₁⟩ ⟨r₂, j₂⟩ h
  dsimp only at h
  by_cases hr : r₁ = r₂
  · subst hr
    have hj : j₁.1 = j₂.1 := by simp only [subMidVal] at h; omega
    exact Prod.ext rfl (Fin.ext hj)
  · exfalso
    by_cases hd : dstOf r₁ = dstOf r₂
    · rcases lt_or_gt_of_ne hr with hlt | hlt
      · have hss : (Finset.univ.filter fun r' : Fin m => r' < r₁ ∧ dstOf r' = dstOf r₁) ⊂
            (Finset.univ.filter fun r' : Fin m => r' < r₂ ∧ dstOf r' = dstOf r₂) := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun r' hr' => ?_, fun heq => ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr' ⊢
            exact ⟨lt_trans hr'.1 hlt, hr'.2.trans hd⟩
          · have hmem : r₁ ∈ Finset.univ.filter fun r' : Fin m =>
                r' < r₂ ∧ dstOf r' = dstOf r₂ := by simp [hlt, hd]
            rw [← heq] at hmem
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
            exact lt_irrefl r₁ hmem.1
        have hltc : (Finset.univ.filter fun r' : Fin m => r' < r₁ ∧ dstOf r' = dstOf r₁).card + 1 ≤
            (Finset.univ.filter fun r' : Fin m => r' < r₂ ∧ dstOf r' = dstOf r₂).card :=
          Finset.card_lt_card hss
        have hmul := Nat.mul_le_mul_left w hltc
        rw [mul_add, mul_one, hd] at hmul
        have hj1 := j₁.2
        simp only [subMidVal, hd] at h
        omega
      · have hss : (Finset.univ.filter fun r' : Fin m => r' < r₂ ∧ dstOf r' = dstOf r₂) ⊂
            (Finset.univ.filter fun r' : Fin m => r' < r₁ ∧ dstOf r' = dstOf r₁) := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun r' hr' => ?_, fun heq => ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr' ⊢
            exact ⟨lt_trans hr'.1 hlt, hr'.2.trans hd.symm⟩
          · have hmem : r₂ ∈ Finset.univ.filter fun r' : Fin m =>
                r' < r₁ ∧ dstOf r' = dstOf r₁ := by simp [hlt, hd.symm]
            rw [← heq] at hmem
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
            exact lt_irrefl r₂ hmem.1
        have hltc : (Finset.univ.filter fun r' : Fin m => r' < r₂ ∧ dstOf r' = dstOf r₂).card + 1 ≤
            (Finset.univ.filter fun r' : Fin m => r' < r₁ ∧ dstOf r' = dstOf r₁).card :=
          Finset.card_lt_card hss
        have hmul := Nat.mul_le_mul_left w hltc
        rw [mul_add, mul_one, hd] at hmul
        have hj2 := j₂.2
        simp only [subMidVal, hd] at h
        omega
    · rcases lt_or_gt_of_ne hd with hlt | hlt
      · have h1 := subMidVal_lt_subPosVal dstOf r₁ j₁
        have h2 := subPosVal_lt_subMidVal hlt j₂
        omega
      · have h1 := subMidVal_lt_subPosVal dstOf r₂ j₂
        have h2 := subPosVal_lt_subMidVal hlt j₁
        omega

/-- Bijection between original+midpoint indices and `Fin ((k + w * m) + 2)`. -/
public noncomputable def subEquiv {k m w : ℕ} (dstOf : Fin m → Fin (k + 2)) :
    Fin (k + 2) ⊕ (Fin m × Fin w) ≃ Fin ((k + w * m) + 2) :=
  have hpos_lt : ∀ v : Fin (k + 2), subPosVal dstOf w v < (k + w * m) + 2 := fun v => by
    have hle := (subPosVal_strictMono dstOf w).monotone (Fin.le_last v)
    rw [subPosVal_last] at hle; omega
  have hmid_lt : ∀ p : Fin m × Fin w, subMidVal dstOf p.1 p.2 < (k + w * m) + 2 := fun p =>
    lt_trans (subMidVal_lt_subPosVal dstOf p.1 p.2) (hpos_lt (dstOf p.1))
  let emb : Fin (k + 2) ⊕ (Fin m × Fin w) → Fin ((k + w * m) + 2) :=
    Sum.elim (fun v => ⟨subPosVal dstOf w v, hpos_lt v⟩)
             (fun p => ⟨subMidVal dstOf p.1 p.2, hmid_lt p⟩)
  have hinj : Function.Injective emb := by
    rintro (v₁ | p₁) (v₂ | p₂) h
    · exact congrArg Sum.inl ((subPosVal_strictMono dstOf w).injective (congrArg Fin.val h))
    · exact absurd (congrArg Fin.val h) (subPosVal_ne_subMidVal dstOf v₁ p₂.1 p₂.2)
    · exact absurd (congrArg Fin.val h).symm (subPosVal_ne_subMidVal dstOf v₂ p₁.1 p₁.2)
    · exact congrArg Sum.inr (subMidVal_injective dstOf (congrArg Fin.val h))
  have hbij : Function.Bijective emb := by
    refine (Fintype.bijective_iff_injective_and_card emb).mpr ⟨hinj, ?_⟩
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  Equiv.ofBijective emb hbij

public theorem subEquiv_inl_val {k m w : ℕ} (dstOf : Fin m → Fin (k + 2)) (v : Fin (k + 2)) :
    (subEquiv (w := w) dstOf (.inl v)).1 = subPosVal dstOf w v := by
  exact rfl

public theorem subEquiv_inr_val {k m w : ℕ} (dstOf : Fin m → Fin (k + 2))
    (r : Fin m) (j : Fin w) :
    (subEquiv (w := w) dstOf (.inr (r, j))).1 = subMidVal dstOf r j := by
  exact rfl

end Subdivision

/-- Every ABP subdivides into a strictly upper-triangular specialization matrix on
`Fin (P.innerVerts + P.edges.length + 2)` whose path-sum vector evaluates to `P.poly` at the sink
(inserting one midpoint vertex per edge eliminates parallel edges while keeping every matrix entry
an `IsSubstEntry`). -/
public theorem isSubstABP_subdivide [CommRing K] (P : ABP K σ) :
    ∃ (N : Matrix (Fin (P.innerVerts + P.edges.length + 2))
        (Fin (P.innerVerts + P.edges.length + 2)) (MvPolynomial σ K))
      (q : Fin (P.innerVerts + P.edges.length + 2) → MvPolynomial σ K),
      IsSubstMatrix N ∧ (∀ i j, j ≤ i → N i j = 0) ∧
        q = Pi.single 0 1 + q ᵥ* N ∧
        q (Fin.last (P.innerVerts + P.edges.length + 1)) = P.poly := by
  let k := P.innerVerts
  let m := P.edges.length
  let dstOf (r : Fin m) : Fin (k + 2) := (P.edges.get r).dst
  have hdst0 : ∀ r : Fin m, 0 < dstOf r := fun r =>
    lt_of_le_of_lt (Fin.zero_le _) (P.edges.get r).lt
  let eEquiv : Fin (k + 2) ⊕ (Fin m × Fin 1) ≃ Fin ((k + 1 * m) + 2) :=
    subEquiv (w := 1) dstOf
  let eFin : Fin ((k + 1 * m) + 2) ≃ Fin ((k + m) + 2) := finCongr (by omega)
  let eqv : Fin (k + 2) ⊕ (Fin m × Fin 1) ≃ Fin ((k + m) + 2) := eEquiv.trans eFin
  let N : Matrix (Fin ((k + m) + 2)) (Fin ((k + m) + 2)) (MvPolynomial σ K) :=
    Matrix.of fun i j =>
      match eqv.symm i, eqv.symm j with
      | .inl v, .inr (r, _) =>
          if (P.edges.get r).src = v then abpLabelPoly (P.edges.get r).label else 0
      | .inr (r, _), .inl w => if dstOf r = w then 1 else 0
      | _, _ => 0
  let q : Fin ((k + m) + 2) → MvPolynomial σ K := fun i =>
    match eqv.symm i with
    | .inl v => P.nodePoly v
    | .inr (r, _) => P.nodePoly (P.edges.get r).src * abpLabelPoly (P.edges.get r).label
  refine ⟨N, q, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [N, Matrix.of_apply]
    cases eqv.symm i with
    | inl v =>
      cases eqv.symm j with
      | inl w => exact .zero
      | inr p =>
        rcases p with ⟨r, s⟩
        dsimp only
        split_ifs <;> [exact isSubstEntry_abpLabelPoly _; exact .zero]
    | inr p =>
      rcases p with ⟨r, s⟩
      cases eqv.symm j with
      | inl w =>
        dsimp only
        split_ifs <;> [exact .one; exact .zero]
      | inr p' => exact .zero
  · intro i j hji
    simp only [N, Matrix.of_apply]
    have hij : ¬ i < j := not_lt.mpr hji
    have hi_eq := eqv.apply_symm_apply i
    have hj_eq := eqv.apply_symm_apply j
    cases hi : eqv.symm i with
    | inl v =>
      cases hj : eqv.symm j with
      | inl w => rfl
      | inr p =>
        rcases p with ⟨r, s⟩
        dsimp only
        split_ifs with hsrc
        · exfalso; apply hij
          rw [← hi_eq, ← hj_eq, hi, hj]
          change (eEquiv (.inl v)).1 < (eEquiv (.inr (r, s))).1
          rw [subEquiv_inl_val, subEquiv_inr_val, ← hsrc]
          exact subPosVal_lt_subMidVal (P.edges.get r).lt s
        · rfl
    | inr p =>
      rcases p with ⟨r, s⟩
      cases hj : eqv.symm j with
      | inl w =>
        dsimp only
        split_ifs with hdst
        · exfalso; apply hij
          rw [← hi_eq, ← hj_eq, hi, hj]
          change (eEquiv (.inr (r, s))).1 < (eEquiv (.inl w)).1
          rw [subEquiv_inr_val, subEquiv_inl_val, ← hdst]
          exact subMidVal_lt_subPosVal dstOf r s
        · rfl
      | inr p' => rfl
  · have hpos0 : eqv (.inl 0) = 0 := by
      apply Fin.ext
      change (eEquiv (.inl 0)).1 = 0
      rw [subEquiv_inl_val, subPosVal_zero hdst0]
    funext j
    have hvm : (q ᵥ* N) j = ∑ x : Fin (k + 2) ⊕ (Fin m × Fin 1), q (eqv x) * N (eqv x) j := by
      simp only [Matrix.vecMul, dotProduct]
      exact (eqv.sum_comp fun y => q y * N y j).symm
    rw [Pi.add_apply, hvm]
    cases hj : eqv.symm j with
    | inl w =>
      have hj_eq : j = eqv (.inl w) := by rw [← hj, eqv.apply_symm_apply]
      rw [hj_eq]
      simp only [q, eqv.symm_apply_apply, N, Matrix.of_apply, Fintype.sum_sum_type,
        Pi.single_apply, ← hpos0, Equiv.apply_eq_iff_eq, Sum.inl.injEq, Fintype.sum_prod_type,
        Fin.sum_univ_one]
      have hfst : (∑ v : Fin (k + 2), P.nodePoly v * 0) = 0 := by simp
      rw [hfst, zero_add]
      have hrewrite :
          (∑ r : Fin m,
            P.nodePoly (P.edges.get r).src * abpLabelPoly (P.edges.get r).label *
              (if dstOf r = w then (1 : MvPolynomial σ K) else 0)) =
          (P.edges.map fun e =>
            if e.dst = w then P.nodePoly e.src * abpLabelPoly e.label else 0).sum := by
        have hmul :
            (∑ r : Fin m,
              P.nodePoly (P.edges.get r).src * abpLabelPoly (P.edges.get r).label *
                (if dstOf r = w then (1 : MvPolynomial σ K) else 0)) =
            ∑ r : Fin m,
              if dstOf r = w then
                P.nodePoly (P.edges.get r).src * abpLabelPoly (P.edges.get r).label
              else 0 :=
          Finset.sum_congr rfl fun r _ => by split_ifs <;> ring
        rw [hmul, ← List.sum_ofFn (f := fun r : Fin m =>
          if dstOf r = w then
            P.nodePoly (P.edges.get r).src * abpLabelPoly (P.edges.get r).label
          else 0)]
        congr 1
        apply List.ext_getElem (by simp [m])
        intro i h1 h2; simp [dstOf]
      by_cases hw : w = 0
      · subst hw
        have hzero_sum : (∑ r : Fin m,
            P.nodePoly (P.edges.get r).src * abpLabelPoly (P.edges.get r).label *
              (if dstOf r = 0 then (1 : MvPolynomial σ K) else 0)) = 0 := by
          refine Finset.sum_eq_zero fun r _ => ?_
          simp [ne_of_gt (hdst0 r)]
        rw [hzero_sum, nodePoly_zero, add_zero]
        simp
      · simp only [hw, ↓reduceIte, zero_add, hrewrite]
        exact P.nodePoly_of_ne_zero hw
    | inr p =>
      have hj_eq : j = eqv (.inr p) := by rw [← hj, eqv.apply_symm_apply]
      rw [hj_eq]
      have hne0 : eqv (.inr p) ≠ 0 := by
        rw [← hpos0]; exact fun h => nomatch eqv.injective h
      rcases p with ⟨r, s⟩
      simp only [q, eqv.symm_apply_apply, N, Matrix.of_apply, Fintype.sum_sum_type,
        Pi.single_eq_of_ne hne0, zero_add, Fintype.sum_prod_type, Fin.sum_univ_one]
      have hsnd : (∑ r' : Fin m,
          P.nodePoly (P.edges.get r').src * abpLabelPoly (P.edges.get r').label * 0) = 0 := by
        simp
      rw [hsnd, add_zero]
      simp
  · have hlast : eqv (.inl (Fin.last (k + 1))) = Fin.last ((k + m) + 1) := by
      apply Fin.ext
      change (eEquiv (.inl (Fin.last (k + 1)))).1 = (k + m) + 1
      rw [subEquiv_inl_val, subPosVal_last]; omega
    rw [← hlast]
    simp only [q, eqv.symm_apply_apply, poly]
    rfl

/-- Every polynomial computed by an ABP of size `s` is a projection of
`(genericMatrix K s).det`. -/
public theorem isProjection_det [CommRing K] (P : ABP K σ) :
    IsProjection P.poly (genericMatrix K P.size).det := by
  obtain ⟨N, q, hM, hN, hq, hq_last⟩ := P.isSubstABP_subdivide
  have h1 : IsProjection P.poly (genericMatrix K (P.innerVerts + P.edges.length + 1)).det := by
    refine isProjection_det_iff_exists_isSubstMatrix.mpr
      ⟨(N - 1).submatrix Fin.castSucc Fin.succ, fun a b => ?_, ?_⟩
    · simp only [Matrix.submatrix_apply, Matrix.sub_apply]
      by_cases hab : a.castSucc = b.succ
      · rw [hN a.castSucc b.succ hab.symm.le, hab, Matrix.one_apply_eq, zero_sub]
        exact .neg_one
      · rw [Matrix.one_apply_ne hab, sub_zero]
        exact hM a.castSucc b.succ
    · rw [← hq_last]
      exact (Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul N hN hq).symm
  have hle : P.innerVerts + P.edges.length + 1 ≤ P.size := by
    simp only [size, numVerts]; omega
  exact isProjection_det_mono hle h1

/-- Every polynomial computed by an ABP of size `s` has a determinantal representation of
dimension `s`. -/
public theorem hasDeterminantalRepresentation [CommRing K] (P : ABP K σ) :
    HasDeterminantalRepresentation P.poly P.size :=
  hasDeterminantalRepresentation_of_isProjection P.isProjection_det

/-! ### Basic constructors and algebraic closure -/

/-- The zero ABP (no edges, 2 vertices, size 2). -/
public def zero : ABP K σ := ⟨0, []⟩

@[simp]
public theorem size_zero : (zero : ABP K σ).size = 2 := by exact rfl

@[simp]
public theorem poly_zero [CommSemiring K] : (zero : ABP K σ).poly = 0 := by
  simp [poly, zero, nodePoly_of_ne_zero]

/-- An ABP with a single edge from source `0` to sink `1` (size 3). -/
public def singleEdge (l : σ ⊕ K) : ABP K σ :=
  ⟨0, [⟨0, 1, by decide, l⟩]⟩

@[simp]
public theorem size_singleEdge (l : σ ⊕ K) : (singleEdge l).size = 3 := by exact rfl

@[simp]
public theorem poly_singleEdge [CommSemiring K] (l : σ ⊕ K) :
    (singleEdge l).poly = abpLabelPoly l := by
  simp [poly, singleEdge, nodePoly_of_ne_zero]

/-- Constant ABP computing `C c` in size `3`. -/
public def const (c : K) : ABP K σ := singleEdge (.inr c)

@[simp]
public theorem size_const (c : K) : (const (σ := σ) c).size = 3 := by exact rfl

@[simp]
public theorem poly_const [CommSemiring K] (c : K) : (const (σ := σ) c).poly = MvPolynomial.C c :=
  poly_singleEdge (.inr c)

/-- Variable ABP computing `X i` in size `3`. -/
public def var (i : σ) : ABP K σ := singleEdge (.inl i)

@[simp]
public theorem size_var (i : σ) : (var (K := K) i).size = 3 := by exact rfl

@[simp]
public theorem poly_var [CommSemiring K] (i : σ) : (var (K := K) i).poly = MvPolynomial.X i :=
  poly_singleEdge (.inl i)

/-- Parallel sum of two ABPs: identifies sources and sinks; size `≤ P.size + Q.size`. -/
public def add (P Q : ABP K σ) : ABP K σ :=
  let mapP (v : Fin (P.innerVerts + 2)) : Fin (P.innerVerts + Q.innerVerts + 2) :=
    if v.1 = P.innerVerts + 1 then Fin.last (P.innerVerts + Q.innerVerts + 1)
    else ⟨v.1, by omega⟩
  let mapQ (v : Fin (Q.innerVerts + 2)) : Fin (P.innerVerts + Q.innerVerts + 2) :=
    if v.1 = 0 then 0
    else if v.1 = Q.innerVerts + 1 then Fin.last (P.innerVerts + Q.innerVerts + 1)
    else ⟨P.innerVerts + v.1, by omega⟩
  have hP : StrictMono mapP := by
    intro a b hab
    simp only [mapP, Fin.lt_def] at hab ⊢
    split_ifs <;> simp only [Fin.val_last] <;> omega
  have hQ : StrictMono mapQ := by
    intro a b hab
    simp only [mapQ, Fin.lt_def] at hab ⊢
    split_ifs <;> simp only [Fin.val_zero, Fin.val_last] <;> omega
  ⟨P.innerVerts + Q.innerVerts,
    P.edges.map (fun e => ⟨mapP e.src, mapP e.dst, hP e.lt, e.label⟩) ++
    Q.edges.map (fun e => ⟨mapQ e.src, mapQ e.dst, hQ e.lt, e.label⟩)⟩

public theorem size_add_le (P Q : ABP K σ) : (P.add Q).size ≤ P.size + Q.size := by
  simp only [add, size, numVerts, List.length_append, List.length_map]
  omega

/-- Series product of two ABPs: identifies the sink of `P` with the source of `Q`;
size `≤ P.size + Q.size`. -/
public def mul (P Q : ABP K σ) : ABP K σ :=
  let mapP (v : Fin (P.innerVerts + 2)) : Fin (P.innerVerts + Q.innerVerts + 1 + 2) :=
    ⟨v.1, by omega⟩
  let mapQ (v : Fin (Q.innerVerts + 2)) : Fin (P.innerVerts + Q.innerVerts + 1 + 2) :=
    ⟨P.innerVerts + 1 + v.1, by omega⟩
  have hP : StrictMono mapP := fun _ _ hab => hab
  have hQ : StrictMono mapQ := fun _ _ hab => Nat.add_lt_add_left hab _
  ⟨P.innerVerts + Q.innerVerts + 1,
    P.edges.map (fun e => ⟨mapP e.src, mapP e.dst, hP e.lt, e.label⟩) ++
    Q.edges.map (fun e => ⟨mapQ e.src, mapQ e.dst, hQ e.lt, e.label⟩)⟩

public theorem size_mul_le (P Q : ABP K σ) : (P.mul Q).size ≤ P.size + Q.size := by
  simp only [mul, size, numVerts, List.length_append, List.length_map]
  omega

public theorem poly_add [CommSemiring K] (P Q : ABP K σ) :
    (P.add Q).poly = P.poly + Q.poly := by
  let k₁ := P.innerVerts
  let k₂ := Q.innerVerts
  let mapP : Fin (k₁ + 2) → Fin (k₁ + k₂ + 2) := fun v =>
    if v.1 = k₁ + 1 then Fin.last (k₁ + k₂ + 1) else ⟨v.1, by omega⟩
  let mapQ : Fin (k₂ + 2) → Fin (k₁ + k₂ + 2) := fun v =>
    if v.1 = 0 then 0
    else if v.1 = k₂ + 1 then Fin.last (k₁ + k₂ + 1)
    else ⟨k₁ + v.1, by omega⟩
  have hmapP_eq : ∀ (v : Fin (k₁ + 2)) (w : Fin (k₂ + 2)),
      mapP v = mapQ w → (v = 0 ∧ w = 0) ∨ (v = Fin.last (k₁ + 1) ∧ w = Fin.last (k₂ + 1)) := by
    intro v w h
    have hv := congrArg Fin.val h
    simp only [mapP, mapQ] at hv
    by_cases hv1 : v.1 = k₁ + 1
    · by_cases hw0 : w.1 = 0
      · simp only [hv1, hw0, ↓reduceIte, Fin.val_last, Fin.val_zero] at hv; omega
      · by_cases hw1 : w.1 = k₂ + 1
        · right; exact ⟨Fin.ext hv1, Fin.ext hw1⟩
        · simp only [hv1, hw0, hw1, ↓reduceIte, Fin.val_last] at hv
          have := w.2; omega
    · by_cases hw0 : w.1 = 0
      · simp only [hv1, hw0, ↓reduceIte, Fin.val_zero] at hv
        left; exact ⟨Fin.ext hv, Fin.ext hw0⟩
      · by_cases hw1 : w.1 = k₂ + 1
        · simp only [hv1, hw1, Nat.succ_ne_zero, ↓reduceIte, Fin.val_last] at hv
          have := v.2; omega
        · simp only [hv1, hw0, hw1, ↓reduceIte] at hv
          have := v.2; omega
  have hP_sm : StrictMono mapP := by
    intro a b hab
    simp only [mapP, Fin.lt_def] at hab ⊢
    split_ifs <;> simp only [Fin.val_last] <;> omega
  have hQ_sm : StrictMono mapQ := by
    intro a b hab
    simp only [mapQ, Fin.lt_def] at hab ⊢
    split_ifs <;> simp only [Fin.val_zero, Fin.val_last] <;> omega
  have hedges_add : (P.add Q).edges =
      P.edges.map (fun e => ⟨mapP e.src, mapP e.dst, hP_sm e.lt, e.label⟩) ++
      Q.edges.map (fun e => ⟨mapQ e.src, mapQ e.dst, hQ_sm e.lt, e.label⟩) := rfl
  have hP_inner : ∀ v : Fin (k₁ + 2), v ≠ Fin.last (k₁ + 1) →
      (P.add Q).nodePoly (mapP v) = P.nodePoly v := by
    suffices h : ∀ (m : ℕ) (v : Fin (k₁ + 2)), v.1 = m → v ≠ Fin.last (k₁ + 1) →
        (P.add Q).nodePoly (mapP v) = P.nodePoly v from fun v hv => h v.1 v rfl hv
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro v hvm hv_last
      by_cases hv0 : v = 0
      · subst hv0
        have h0 : mapP 0 = (0 : Fin ((P.add Q).innerVerts + 2)) := Fin.ext (by simp [mapP])
        rw [h0, (P.add Q).nodePoly_zero, P.nodePoly_zero]
      · have hmv0 : (mapP v : Fin ((P.add Q).innerVerts + 2)) ≠ 0 := by
          intro h
          have hv1 : v.1 ≠ k₁ + 1 := fun h' => hv_last (Fin.ext h')
          have hval := congrArg Fin.val h
          simp only [mapP, hv1, ↓reduceIte, Fin.val_zero] at hval
          exact hv0 (Fin.ext hval)
        rw [nodePoly_of_ne_zero (P.add Q) hmv0, nodePoly_of_ne_zero P hv0]
        change ((P.add Q).edges.map _).sum = _
        rw [hedges_add, List.map_append, List.sum_append, List.map_map, List.map_map]
        change (P.edges.map fun e => if mapP e.dst = mapP v then
            (P.add Q).nodePoly (mapP e.src) * abpLabelPoly e.label else 0).sum +
          (Q.edges.map fun e => if mapQ e.dst = mapP v then
            (P.add Q).nodePoly (mapQ e.src) * abpLabelPoly e.label else 0).sum = _
        have hQzero :
            ((Q.edges.map fun e =>
              if mapQ e.dst = mapP v then
                (P.add Q).nodePoly (mapQ e.src) * abpLabelPoly e.label
              else 0)).sum = 0 := by
          refine List.sum_eq_zero fun x hx => ?_
          obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
          split_ifs with h
          · rcases hmapP_eq v e.dst h.symm with ⟨_, hd0⟩ | ⟨hv', _⟩
            · exact absurd hd0 (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) e.lt))
            · exact absurd hv' hv_last
          · rfl
        rw [hQzero, add_zero]
        congr 1
        refine List.map_congr_left fun e _ => ?_
        have hmapP_inj : Function.Injective mapP := by
          intro a b hab
          have := congrArg Fin.val hab
          simp only [mapP] at this
          split_ifs at this <;> simp only [Fin.val_last] at this
          · exact Fin.ext (by omega)
          · have := b.2; omega
          · have := a.2; omega
          · exact Fin.ext this
        simp only [hmapP_inj.eq_iff]
        split_ifs with h
        · rw [ih e.src.1 (hvm ▸ (h ▸ e.lt)) e.src rfl
            (ne_of_lt (lt_of_lt_of_le e.lt (Fin.le_last _)))]
        · rfl
  have hQ_inner : ∀ v : Fin (k₂ + 2), v ≠ Fin.last (k₂ + 1) →
      (P.add Q).nodePoly (mapQ v) = Q.nodePoly v := by
    suffices h : ∀ (m : ℕ) (v : Fin (k₂ + 2)), v.1 = m → v ≠ Fin.last (k₂ + 1) →
        (P.add Q).nodePoly (mapQ v) = Q.nodePoly v from fun v hv => h v.1 v rfl hv
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro v hvm hv_last
      by_cases hv0 : v = 0
      · subst hv0
        have h0 : mapQ 0 = (0 : Fin ((P.add Q).innerVerts + 2)) := Fin.ext (by simp [mapQ])
        rw [h0, (P.add Q).nodePoly_zero, Q.nodePoly_zero]
      · have hmv0 : (mapQ v : Fin ((P.add Q).innerVerts + 2)) ≠ 0 := by
          intro h
          have hv1 : v.1 ≠ 0 := fun h' => hv0 (Fin.ext h')
          have hv2 : v.1 ≠ k₂ + 1 := fun h' => hv_last (Fin.ext h')
          have hval := congrArg Fin.val h
          simp only [mapQ, hv1, hv2, ↓reduceIte, Fin.val_zero] at hval
          omega
        rw [nodePoly_of_ne_zero (P.add Q) hmv0, nodePoly_of_ne_zero Q hv0]
        change ((P.add Q).edges.map _).sum = _
        rw [hedges_add, List.map_append, List.sum_append, List.map_map, List.map_map]
        change (P.edges.map fun e => if mapP e.dst = mapQ v then
            (P.add Q).nodePoly (mapP e.src) * abpLabelPoly e.label else 0).sum +
          (Q.edges.map fun e => if mapQ e.dst = mapQ v then
            (P.add Q).nodePoly (mapQ e.src) * abpLabelPoly e.label else 0).sum = _
        have hPzero :
            ((P.edges.map fun e =>
              if mapP e.dst = mapQ v then
                (P.add Q).nodePoly (mapP e.src) * abpLabelPoly e.label
              else 0)).sum = 0 := by
          refine List.sum_eq_zero fun x hx => ?_
          obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
          split_ifs with h
          · rcases hmapP_eq e.dst v h with ⟨hd0, _⟩ | ⟨_, hv'⟩
            · exact absurd hd0 (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) e.lt))
            · exact absurd hv' hv_last
          · rfl
        rw [hPzero, zero_add]
        congr 1
        refine List.map_congr_left fun e _ => ?_
        have hmapQ_inj : Function.Injective mapQ := by
          intro a b hab
          have := congrArg Fin.val hab
          simp only [mapQ] at this
          split_ifs at this <;> simp only [Fin.val_zero, Fin.val_last] at this
          · exact Fin.ext (by omega)
          · omega
          · have := b.2; omega
          · omega
          · exact Fin.ext (by omega)
          · have := b.2; omega
          · have := a.2; omega
          · have := a.2; omega
          · exact Fin.ext (by omega)
        simp only [hmapQ_inj.eq_iff]
        split_ifs with h
        · rw [ih e.src.1 (hvm ▸ (h ▸ e.lt)) e.src rfl
            (ne_of_lt (lt_of_lt_of_le e.lt (Fin.le_last _)))]
        · rfl
  have hlast_ne : (Fin.last (k₁ + k₂ + 1) : Fin ((P.add Q).innerVerts + 2)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  have hlastP_ne : Fin.last (k₁ + 1) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  have hlastQ_ne : Fin.last (k₂ + 1) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  simp only [poly]
  change (P.add Q).nodePoly (Fin.last (k₁ + k₂ + 1)) =
    P.nodePoly (Fin.last (k₁ + 1)) + Q.nodePoly (Fin.last (k₂ + 1))
  rw [nodePoly_of_ne_zero (P.add Q) hlast_ne, nodePoly_of_ne_zero P hlastP_ne,
    nodePoly_of_ne_zero Q hlastQ_ne]
  change ((P.add Q).edges.map _).sum = _
  rw [hedges_add, List.map_append, List.sum_append, List.map_map, List.map_map]
  have hmapP_last : ∀ w : Fin (k₁ + 2),
      mapP w = Fin.last (k₁ + k₂ + 1) ↔ w = Fin.last (k₁ + 1) := by
    intro w
    constructor
    · intro h
      have hv := congrArg Fin.val h
      by_cases hw : w.1 = k₁ + 1
      · exact Fin.ext hw
      · simp only [mapP, hw, ↓reduceIte, Fin.val_last] at hv
        have := w.2; omega
    · rintro rfl; simp [mapP]
  have hmapQ_last : ∀ w : Fin (k₂ + 2),
      mapQ w = Fin.last (k₁ + k₂ + 1) ↔ w = Fin.last (k₂ + 1) := by
    intro w
    constructor
    · intro h
      have hv := congrArg Fin.val h
      by_cases hw1 : w.1 = 0
      · simp only [mapQ, hw1, ↓reduceIte, Fin.val_zero, Fin.val_last] at hv; omega
      · by_cases hw2 : w.1 = k₂ + 1
        · exact Fin.ext hw2
        · simp only [mapQ, hw1, hw2, ↓reduceIte, Fin.val_last] at hv
          have := w.2; omega
    · rintro rfl; simp [mapQ]
  congr 1
  · congr 1
    refine List.map_congr_left fun e _ => ?_
    change (if mapP e.dst = Fin.last (k₁ + k₂ + 1) then
      (P.add Q).nodePoly (mapP e.src) * abpLabelPoly e.label else 0) = _
    simp only [hmapP_last]
    split_ifs with h
    · rw [hP_inner e.src (ne_of_lt (lt_of_lt_of_le e.lt (Fin.le_last _)))]
    · rfl
  · congr 1
    refine List.map_congr_left fun e _ => ?_
    change (if mapQ e.dst = Fin.last (k₁ + k₂ + 1) then
      (P.add Q).nodePoly (mapQ e.src) * abpLabelPoly e.label else 0) = _
    simp only [hmapQ_last]
    split_ifs with h
    · rw [hQ_inner e.src (ne_of_lt (lt_of_lt_of_le e.lt (Fin.le_last _)))]
    · rfl

public theorem poly_mul [CommSemiring K] (P Q : ABP K σ) :
    (P.mul Q).poly = P.poly * Q.poly := by
  let k₁ := P.innerVerts
  let k₂ := Q.innerVerts
  let mapP : Fin (k₁ + 2) → Fin (k₁ + k₂ + 1 + 2) := fun v => ⟨v.1, by omega⟩
  let mapQ : Fin (k₂ + 2) → Fin (k₁ + k₂ + 1 + 2) := fun v => ⟨k₁ + 1 + v.1, by omega⟩
  have hedges_mul : (P.mul Q).edges =
      P.edges.map (fun e => ⟨mapP e.src, mapP e.dst, e.lt, e.label⟩) ++
      Q.edges.map (fun e => ⟨mapQ e.src, mapQ e.dst, Nat.add_lt_add_left e.lt _, e.label⟩) := rfl
  have hP_part : ∀ v : Fin (k₁ + 2), (P.mul Q).nodePoly (mapP v) = P.nodePoly v := by
    suffices h : ∀ (m : ℕ) (v : Fin (k₁ + 2)), v.1 = m →
        (P.mul Q).nodePoly (mapP v) = P.nodePoly v from fun v => h v.1 v rfl
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro v hvm
      by_cases hv0 : v = 0
      · subst hv0
        have h0 : mapP 0 = (0 : Fin ((P.mul Q).innerVerts + 2)) := Fin.ext rfl
        rw [h0, (P.mul Q).nodePoly_zero, P.nodePoly_zero]
      · have hmv0 : (mapP v : Fin ((P.mul Q).innerVerts + 2)) ≠ 0 :=
          fun h => hv0 (Fin.ext (by simpa [mapP] using congrArg Fin.val h))
        rw [nodePoly_of_ne_zero (P.mul Q) hmv0, nodePoly_of_ne_zero P hv0]
        change ((P.mul Q).edges.map _).sum = _
        rw [hedges_mul, List.map_append, List.sum_append, List.map_map, List.map_map]
        change (P.edges.map fun e => if mapP e.dst = mapP v then
            (P.mul Q).nodePoly (mapP e.src) * abpLabelPoly e.label else 0).sum +
          (Q.edges.map fun e => if mapQ e.dst = mapP v then
            (P.mul Q).nodePoly (mapQ e.src) * abpLabelPoly e.label else 0).sum = _
        have hQzero :
            ((Q.edges.map fun e =>
              if mapQ e.dst = mapP v then
                (P.mul Q).nodePoly (mapQ e.src) * abpLabelPoly e.label
              else 0)).sum = 0 := by
          refine List.sum_eq_zero fun x hx => ?_
          obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
          split_ifs with h
          · exfalso
            have hv := congrArg Fin.val h
            simp only [mapQ, mapP] at hv
            have hlt : 0 < e.dst.1 := lt_of_le_of_lt (Fin.zero_le _) e.lt
            have := v.2; omega
          · rfl
        rw [hQzero, add_zero]
        congr 1
        refine List.map_congr_left fun e _ => ?_
        have hmapP_inj : Function.Injective mapP := fun a b hab =>
          Fin.ext (by simpa [mapP] using congrArg Fin.val hab)
        simp only [hmapP_inj.eq_iff]
        split_ifs with h
        · rw [ih e.src.1 (hvm ▸ (h ▸ e.lt)) e.src rfl]
        · rfl
  have hQ_part : ∀ v : Fin (k₂ + 2), (P.mul Q).nodePoly (mapQ v) = P.poly * Q.nodePoly v := by
    suffices h : ∀ (m : ℕ) (v : Fin (k₂ + 2)), v.1 = m →
        (P.mul Q).nodePoly (mapQ v) = P.poly * Q.nodePoly v from fun v => h v.1 v rfl
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro v hvm
      by_cases hv0 : v = 0
      · subst hv0
        have hsink : mapQ 0 = mapP (Fin.last (k₁ + 1)) := by ext; simp [mapQ, mapP]
        rw [hsink, hP_part, nodePoly_zero, mul_one]; rfl
      · have hmv0 : (mapQ v : Fin ((P.mul Q).innerVerts + 2)) ≠ 0 := by
          intro h; have := congrArg Fin.val h; simp [mapQ] at this
        rw [nodePoly_of_ne_zero (P.mul Q) hmv0, nodePoly_of_ne_zero Q hv0]
        change ((P.mul Q).edges.map _).sum = _
        rw [hedges_mul, List.map_append, List.sum_append, List.map_map, List.map_map]
        change (P.edges.map fun e => if mapP e.dst = mapQ v then
            (P.mul Q).nodePoly (mapP e.src) * abpLabelPoly e.label else 0).sum +
          (Q.edges.map fun e => if mapQ e.dst = mapQ v then
            (P.mul Q).nodePoly (mapQ e.src) * abpLabelPoly e.label else 0).sum = _
        have hPzero :
            ((P.edges.map fun e =>
              if mapP e.dst = mapQ v then
                (P.mul Q).nodePoly (mapP e.src) * abpLabelPoly e.label
              else 0)).sum = 0 := by
          refine List.sum_eq_zero fun x hx => ?_
          obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
          split_ifs with h
          · exfalso
            have hv := congrArg Fin.val h
            simp only [mapQ, mapP] at hv
            have hne0 : v.1 ≠ 0 := fun h' => hv0 (Fin.ext h')
            have := e.dst.2; omega
          · rfl
        have hmul_sum : ∀ (c : MvPolynomial σ K) (l : List (MvPolynomial σ K)),
            c * l.sum = (l.map (c * ·)).sum := fun c l => by
          induction l with
          | nil => simp
          | cons x xs ih => simp [mul_add, ih]
        rw [hPzero, zero_add, hmul_sum, List.map_map]
        congr 1
        refine List.map_congr_left fun e _ => ?_
        have hmapQ_inj : Function.Injective mapQ := fun a b hab => by
          apply Fin.ext
          have := congrArg Fin.val hab
          simp only [mapQ] at this; omega
        simp only [Function.comp_apply, hmapQ_inj.eq_iff]
        split_ifs with h
        · rw [ih e.src.1 (hvm ▸ (h ▸ e.lt)) e.src rfl]; ring
        · ring
  have hlast : mapQ (Fin.last (k₂ + 1)) = Fin.last (k₁ + k₂ + 1 + 1) := by
    ext; simp [mapQ]; omega
  simp only [poly]
  change (P.mul Q).nodePoly (Fin.last (k₁ + k₂ + 1 + 1)) =
    P.nodePoly (Fin.last (k₁ + 1)) * Q.nodePoly (Fin.last (k₂ + 1))
  rw [← hlast, hQ_part]
  rfl

/-- Sum of a list of ABPs. -/
public def sumList : List (ABP K σ) → ABP K σ
  | [] => zero
  | P :: Ps => P.add (sumList Ps)

public theorem poly_sumList [CommSemiring K] (Ps : List (ABP K σ)) :
    (sumList Ps).poly = (Ps.map ABP.poly).sum := by
  induction Ps with
  | nil => simp [sumList]
  | cons P Ps ih => simp [sumList, poly_add, ih]

public theorem size_sumList_le (Ps : List (ABP K σ)) :
    (sumList Ps).size ≤ (Ps.map ABP.size).sum + 2 := by
  induction Ps with
  | nil => simp [sumList]
  | cons P Ps ih =>
    simp only [sumList, List.map_cons, List.sum_cons]
    have h := size_add_le P (sumList Ps)
    omega

/-- Product of a list of ABPs. -/
public def prodList [One K] : List (ABP K σ) → ABP K σ
  | [] => const 1
  | P :: Ps => P.mul (prodList Ps)

public theorem poly_prodList [CommSemiring K] (Ps : List (ABP K σ)) :
    (prodList Ps).poly = (Ps.map ABP.poly).prod := by
  induction Ps with
  | nil => simp [prodList]
  | cons P Ps ih => simp [prodList, poly_mul, ih]

public theorem size_prodList_le [One K] (Ps : List (ABP K σ)) :
    (prodList Ps).size ≤ (Ps.map ABP.size).sum + 3 := by
  induction Ps with
  | nil => simp [prodList, const]
  | cons P Ps ih =>
    simp only [prodList, List.map_cons, List.sum_cons]
    have h := size_mul_le P (prodList Ps)
    omega

@[simp]
public theorem eval_const [CommSemiring K] (c : K) (v : σ → K) :
    (const (σ := σ) c).eval v = c := by
  simp [eval, poly_const]

@[simp]
public theorem eval_var [CommSemiring K] (i : σ) (v : σ → K) :
    (var (K := K) i).eval v = v i := by
  simp [eval, poly_var]

@[simp]
public theorem eval_add [CommSemiring K] (P Q : ABP K σ) (v : σ → K) :
    (P.add Q).eval v = P.eval v + Q.eval v := by
  simp [eval, poly_add]

@[simp]
public theorem eval_mul [CommSemiring K] (P Q : ABP K σ) (v : σ → K) :
    (P.mul Q).eval v = P.eval v * Q.eval v := by
  simp [eval, poly_mul]

/-- Evaluation of `sumList Ps` equals the sum of evaluations of `Ps`. -/
public theorem eval_sumList [CommSemiring K] (Ps : List (ABP K σ)) (v : σ → K) :
    (sumList Ps).eval v = (Ps.map fun P => P.eval v).sum := by
  induction Ps with
  | nil => simp [sumList, eval, poly_zero]
  | cons P Ps ih => simp [sumList, eval_add, ih]


end ABP

end CslibFrontier.Computability.Circuit
