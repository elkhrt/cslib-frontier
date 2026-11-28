/-
Copyright (c) 2026 The cslib-frontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Order.Partition.Finpartition

import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.Rat.ClearDenom
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Euclidean `k`-Means and `2`-Means Decision Problems and `NP` Membership

This module defines the multi-tape Turing-machine decision formulations of **Euclidean `k`-Means
(`EuclideanKMeans`)** and **Euclidean `2`-Means (`TwoMeans`)** over rational point sets in `ℚ^d`,
establishes the exact second-moment, pairwise-distance, and centroid-optimality identities for
within-cluster sum-of-squares cost, and proves membership of both problems in `NP`.

## Main definitions

- `CslibFrontier.Computability.Complexity.EuclideanKMeansInstance`,
  `CslibFrontier.Computability.Complexity.encEuclideanKMeans`: encoded Euclidean `k`-means instance.
- `CslibFrontier.Computability.Complexity.pointCoord`,
  `CslibFrontier.Computability.Complexity.centroidCoord`,
  `CslibFrontier.Computability.Complexity.kmeansClusterCost`,
  `CslibFrontier.Computability.Complexity.kmeansCost`: rational point coordinates, cluster
  centroids, and within-cluster sum-of-squares objective.
- `CslibFrontier.Computability.Complexity.EuclideanKMeans`,
  `CslibFrontier.Computability.Complexity.TwoMeans`: Euclidean `k`-means and `2`-means decision
  problems.

## Main results

- `CslibFrontier.Computability.Complexity.kmeansClusterCost_eq_sum_sq_sub`,
  `CslibFrontier.Computability.Complexity.kmeansClusterCost_eq_half_pairwise`,
  `CslibFrontier.Computability.Complexity.kmeansClusterCost_le_sum_sq_sub_center`.
- `CslibFrontier.Computability.Complexity.EuclideanKMeans.exists_finpartition_sum_of_assign`,
  `CslibFrontier.Computability.Complexity.EuclideanKMeans.mem_NP`,
  `CslibFrontier.Computability.Complexity.TwoMeans.mem_NP`.

## Tags

computational complexity, NP, k-means clustering, 2-means, within-cluster sum of squares
-/

public section

namespace CslibFrontier.Computability.Complexity

open Finset Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Internal Rational List-Sum Helpers -/

private def kmDenomProd (l : List ℚ) : ℕ :=
  (l.map Rat.den).prod

private lemma kmDenomProd_pos (l : List ℚ) : 0 < kmDenomProd l :=
  List.prod_pos fun _ hd ↦ by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    exact q.pos

private lemma dvd_kmDenomProd {l : List ℚ} {q : ℚ} (hq : q ∈ l) :
    q.den ∣ kmDenomProd l :=
  List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)

private def kmScaledNumSum (l : List ℚ) : ℤ :=
  (l.map fun q ↦ q.num * ((kmDenomProd l / q.den : ℕ) : ℤ)).sum

private lemma cast_sum_clearDenom_km (D : ℕ) :
    ∀ (s : List ℚ), (∀ q ∈ s, q.den ∣ D) →
      (((s.map fun q ↦ q.num * ((D / q.den : ℕ) : ℤ)).sum : ℤ) : ℚ) = (D : ℚ) * s.sum
  | [], _ => by simp
  | q :: s, h => by
    simp only [List.map_cons, List.sum_cons, Int.cast_add, mul_add]
    rw [← Rat.clearDenom_entry (h q List.mem_cons_self),
      cast_sum_clearDenom_km D s fun r hr ↦ h r (List.mem_cons_of_mem q hr)]

private lemma divInt_kmScaledNumSum (l : List ℚ) :
    Rat.divInt (kmScaledNumSum l) (kmDenomProd l : ℤ) = l.sum := by
  have hD : (kmDenomProd l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (kmDenomProd_pos l).ne'
  rw [Rat.divInt_eq_div, Int.cast_natCast, kmScaledNumSum,
    cast_sum_clearDenom_km (kmDenomProd l) l fun _ hq ↦ dvd_kmDenomProd hq,
    mul_div_cancel_left₀ _ hD]

@[local fun_prop]
private theorem computableInPolyTime_kmDenomProd :
    ComputableInPolyTime kmDenomProd (encList encRat) encNat := by
  unfold kmDenomProd
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_kmScaledNumSum :
    ComputableInPolyTime kmScaledNumSum (encList encRat) encIntBin := by
  unfold kmScaledNumSum
  exact intBin_sum.comp (mapWithInput id' (by fun_prop))

private theorem km_ratListSum_polyTime {α : Type} {enc : α ↪ List Bool} {f : α → List ℚ}
    (hf : ComputableInPolyTime f enc (encList encRat)) :
    ComputableInPolyTime (fun a ↦ (f a).sum) enc encRat :=
  ((show ComputableInPolyTime
      (fun l : List ℚ ↦ Rat.divInt (kmScaledNumSum l) ((kmDenomProd l : ℕ) : ℤ))
      (encList encRat) encRat by fun_prop).of_enc_eq fun l ↦
    congrArg encRat (divInt_kmScaledNumSum l).symm).comp hf

private lemma km_sum_map_range (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ, List.map_singleton, List.sum_singleton]

/-! ### 2. Euclidean `k`-Means Definitions and Variance Identities -/

/-- An instance `(n, d, points, k, bound)` of **Euclidean `k`-Means**: `n` points (unary) in
ambient dimension `d` (unary), explicit `n × d` rational coordinate matrix `points`, target number
of clusters `k` (binary), and rational WCSS threshold `bound`. -/
@[ext]
structure EuclideanKMeansInstance where
  /-- Number of data points, encoded in unary. -/
  n : ℕ
  /-- Ambient Euclidean dimension, encoded in unary. -/
  d : ℕ
  /-- Explicit `n × d` list of rational point coordinates. -/
  points : List (List ℚ)
  /-- Target number of clusters `k`, encoded in binary. -/
  k : ℕ
  /-- Upper bound on the within-cluster sum-of-squares cost. -/
  bound : ℚ
  deriving DecidableEq, Repr

/-- Encoding of `EuclideanKMeansInstance`. -/
enc_structure encEuclideanKMeans : EuclideanKMeansInstance where
  n : encUnary,
  d : encUnary,
  points : (encList (encList encRat)),
  k : encNat,
  bound : encRat

attribute [fun_prop] encEuclideanKMeans_n_polyTime encEuclideanKMeans_d_polyTime
  encEuclideanKMeans_points_polyTime encEuclideanKMeans_k_polyTime
  encEuclideanKMeans_bound_polyTime encEuclideanKMeans_mk_polyTime

/-- Coordinate `r` of point `i` in `points`, defaulting to `0` out of bounds. -/
@[expose]
def pointCoord (points : List (List ℚ)) (i r : ℕ) : ℚ :=
  (points.getD i []).getD r 0

@[fun_prop]
theorem computableInPolyTime_pointCoord_unary {α : Type} {enc : α ↪ List Bool}
    {points : α → List (List ℚ)} {i r : α → ℕ}
    (hp : ComputableInPolyTime points enc (encList (encList encRat)))
    (hi : ComputableInPolyTime i enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary) :
    ComputableInPolyTime (fun a ↦ pointCoord (points a) (i a) (r a)) enc encRat :=
  listGetDWithInput (listGetDWithInput hp hi ([] : List ℚ)) hr (0 : ℚ)

/-- Coordinate `r` of the empirical centroid of cluster `C ⊆ Fin n`. -/
@[expose]
def centroidCoord {n : ℕ} (points : List (List ℚ)) (C : Finset (Fin n)) (r : ℕ) : ℚ :=
  (∑ i ∈ C, pointCoord points i.1 r) / (C.card : ℚ)

/-- Within-cluster sum-of-squares cost of a cluster `C ⊆ Fin n` in dimension `d`. -/
@[expose]
def kmeansClusterCost {n : ℕ} (d : ℕ) (points : List (List ℚ)) (C : Finset (Fin n)) : ℚ :=
  ∑ i ∈ C, ∑ r ∈ Finset.range d, (pointCoord points i.1 r - centroidCoord points C r) ^ 2

/-- Total within-cluster sum-of-squares cost of a partition `P` of `Fin n`. -/
@[expose]
def kmeansCost (n d : ℕ) (points : List (List ℚ))
    (P : Finpartition (univ : Finset (Fin n))) : ℚ :=
  ∑ C ∈ P.parts, kmeansClusterCost d points C

theorem kmeansClusterCost_nonneg {n : ℕ} (d : ℕ) (points : List (List ℚ))
    (C : Finset (Fin n)) : 0 ≤ kmeansClusterCost d points C :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _

theorem kmeansCost_nonneg (n d : ℕ) (points : List (List ℚ))
    (P : Finpartition (univ : Finset (Fin n))) : 0 ≤ kmeansCost n d points P :=
  sum_nonneg fun C _ ↦ kmeansClusterCost_nonneg d points C

/-- Coordinatewise second-moment identity on a nonempty finite set `C`. -/
theorem coord_variance_eq {ι : Type*} (C : Finset ι) (hC : C.Nonempty) (a : ι → ℚ) :
    ∑ i ∈ C, (a i - (∑ j ∈ C, a j) / (C.card : ℚ)) ^ 2 =
      (∑ i ∈ C, (a i) ^ 2) - (∑ i ∈ C, a i) ^ 2 / (C.card : ℚ) := by
  have hm : (C.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hC.card_pos.ne'
  set S := ∑ j ∈ C, a j
  have h1 : ∀ i ∈ C, (a i - S / (C.card : ℚ)) ^ 2 =
      (a i) ^ 2 - (2 * S / (C.card : ℚ)) * a i + (S / (C.card : ℚ)) ^ 2 := fun _ _ ↦ by ring
  rw [sum_congr rfl h1, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  field_simp [hm]
  ring

/-- Second-moment decomposition of `kmeansClusterCost` for a nonempty cluster `C`. -/
theorem kmeansClusterCost_eq_sum_sq_sub {n : ℕ} (d : ℕ) (points : List (List ℚ))
    {C : Finset (Fin n)} (hC : C.Nonempty) :
    kmeansClusterCost d points C =
      (∑ i ∈ C, ∑ r ∈ Finset.range d, (pointCoord points i.1 r) ^ 2) -
        (∑ r ∈ Finset.range d, (∑ i ∈ C, pointCoord points i.1 r) ^ 2) / (C.card : ℚ) := by
  unfold kmeansClusterCost centroidCoord
  rw [sum_comm]
  have hr : ∀ r ∈ Finset.range d,
      ∑ i ∈ C, (pointCoord points i.1 r - (∑ j ∈ C, pointCoord points j.1 r) / (C.card : ℚ)) ^ 2 =
        (∑ i ∈ C, (pointCoord points i.1 r) ^ 2) -
          (∑ i ∈ C, pointCoord points i.1 r) ^ 2 / (C.card : ℚ) :=
    fun r _ ↦ coord_variance_eq C hC (fun i ↦ pointCoord points i.1 r)
  rw [sum_congr rfl hr, sum_sub_distrib, sum_comm (s := Finset.range d), sum_div]

/-- Pairwise squared-distance identity for `kmeansClusterCost` on a nonempty cluster `C`. -/
theorem kmeansClusterCost_eq_half_pairwise {n : ℕ} (d : ℕ) (points : List (List ℚ))
    {C : Finset (Fin n)} (hC : C.Nonempty) :
    kmeansClusterCost d points C =
      (∑ i ∈ C, ∑ j ∈ C, ∑ r ∈ Finset.range d,
        (pointCoord points i.1 r - pointCoord points j.1 r) ^ 2) / (2 * (C.card : ℚ)) := by
  have hm : (C.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hC.card_pos.ne'
  rw [kmeansClusterCost_eq_sum_sq_sub d points hC]
  have hcoord : ∀ r ∈ Finset.range d,
      ∑ i ∈ C, ∑ j ∈ C, (pointCoord points i.1 r - pointCoord points j.1 r) ^ 2 =
        2 * (C.card : ℚ) * (∑ i ∈ C, (pointCoord points i.1 r) ^ 2) -
          2 * (∑ i ∈ C, pointCoord points i.1 r) ^ 2 := by
    intro r _
    have h1 : ∀ i ∈ C, ∑ j ∈ C, (pointCoord points i.1 r - pointCoord points j.1 r) ^ 2 =
        (C.card : ℚ) * (pointCoord points i.1 r) ^ 2 -
          2 * pointCoord points i.1 r * (∑ j ∈ C, pointCoord points j.1 r) +
          ∑ j ∈ C, (pointCoord points j.1 r) ^ 2 := by
      intro i _
      have h2 : ∀ j ∈ C, (pointCoord points i.1 r - pointCoord points j.1 r) ^ 2 =
          (pointCoord points i.1 r) ^ 2 -
            2 * pointCoord points i.1 r * pointCoord points j.1 r +
            (pointCoord points j.1 r) ^ 2 := fun _ _ ↦ by ring
      rw [sum_congr rfl h2, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    rw [sum_congr rfl h1, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    have hmul : ∑ x ∈ C, 2 * pointCoord points x.1 r * ∑ j ∈ C, pointCoord points j.1 r =
        2 * (∑ i ∈ C, pointCoord points i.1 r) ^ 2 := by
      rw [← sum_mul]
      have h2 : ∑ x ∈ C, 2 * pointCoord points x.1 r = 2 * ∑ x ∈ C, pointCoord points x.1 r := by
        rw [← mul_sum]
      rw [h2]
      ring
    rw [hmul]
    ring
  have hswap :
      ∑ i ∈ C, ∑ j ∈ C, ∑ r ∈ Finset.range d,
        (pointCoord points i.1 r - pointCoord points j.1 r) ^ 2 =
      ∑ r ∈ Finset.range d, ∑ i ∈ C, ∑ j ∈ C,
        (pointCoord points i.1 r - pointCoord points j.1 r) ^ 2 := by
    have h1 : ∑ i ∈ C, ∑ j ∈ C, ∑ r ∈ Finset.range d,
        (pointCoord points i.1 r - pointCoord points j.1 r) ^ 2 =
      ∑ i ∈ C, ∑ r ∈ Finset.range d, ∑ j ∈ C,
        (pointCoord points i.1 r - pointCoord points j.1 r) ^ 2 :=
      sum_congr rfl fun _ _ ↦ sum_comm
    rw [h1, sum_comm]
  rw [hswap, sum_congr rfl hcoord, sum_sub_distrib, ← mul_sum, ← mul_sum,
    sum_comm (s := Finset.range d)]
  field_simp [hm]

/-- Sample centroid optimality: for any candidate center `μ : ℕ → ℚ`, the empirical centroid
minimizes the sum of squared Euclidean distances over a nonempty cluster `C`. -/
theorem kmeansClusterCost_le_sum_sq_sub_center {n : ℕ} (d : ℕ) (points : List (List ℚ))
    {C : Finset (Fin n)} (hC : C.Nonempty) (μ : ℕ → ℚ) :
    kmeansClusterCost d points C ≤
      ∑ i ∈ C, ∑ r ∈ Finset.range d, (pointCoord points i.1 r - μ r) ^ 2 := by
  unfold kmeansClusterCost
  rw [sum_comm (s := C), sum_comm (s := C)]
  refine sum_le_sum fun r _ ↦ ?_
  have hm : (C.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hC.card_pos.ne'
  set c := centroidCoord points C r
  have hsum_sub : ∑ i ∈ C, (pointCoord points i.1 r - c) = 0 := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    dsimp [c, centroidCoord]
    rw [mul_div_cancel₀ _ hm, sub_self]
  have hdecomp : ∀ i ∈ C, (pointCoord points i.1 r - μ r) ^ 2 =
      (pointCoord points i.1 r - c) ^ 2 +
        2 * (c - μ r) * (pointCoord points i.1 r - c) + (c - μ r) ^ 2 := fun _ _ ↦ by ring
  rw [sum_congr rfl hdecomp, sum_add_distrib, sum_add_distrib, ← mul_sum, hsum_sub, mul_zero,
    add_zero, sum_const, nsmul_eq_mul]
  have hnn : 0 ≤ (C.card : ℚ) * (c - μ r) ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  linarith

/-- **Euclidean `k`-Means**: instances admitting a `k`-partition of `Fin n` with WCSS at most
`bound`. -/
@[expose]
def EuclideanKMeans : Set EuclideanKMeansInstance :=
  {x | ∃ P : Finpartition (univ : Finset (Fin x.n)),
    P.parts.card = x.k ∧ kmeansCost x.n x.d x.points P ≤ x.bound}

/-- **Euclidean `2`-Means**: Euclidean `k`-means restricted to `k = 2`. -/
@[expose]
def TwoMeans : Set EuclideanKMeansInstance :=
  {x | x.k = 2 ∧ x ∈ EuclideanKMeans}

/-! ### 3. Membership of `EuclideanKMeans` and `TwoMeans` in `NP` -/

namespace EuclideanKMeans

/-- Construct an opaque `k`-partition from a surjective label assignment `α : V → ℕ` witnessed by
right-inverse representatives `cOf : ℕ → V`, rewriting `∑ C ∈ P.parts, f C` as a range sum. -/
theorem exists_finpartition_sum_of_assign {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (α : V → ℕ) (cOf : ℕ → V) (hlt : ∀ v : V, α v < k)
    (hc : ∀ a < k, α (cOf a) = a) (f : Finset V → ℚ) :
    ∃ P : Finpartition (univ : Finset V), P.parts.card = k ∧
      ∑ C ∈ P.parts, f C = ∑ a ∈ Finset.range k, f (univ.filter fun v ↦ α v = a) := by
  let clusterOf (a : ℕ) : Finset V := univ.filter fun v ↦ α v = a
  let parts : Finset (Finset V) := (Finset.range k).image clusterOf
  have hinj : Set.InjOn clusterOf (Finset.range k : Set ℕ) := by
    intro a₁ ha₁ a₂ _ hEq
    have ha₁' : a₁ < k := Finset.mem_range.mp ha₁
    have hmem1 : cOf a₁ ∈ clusterOf a₁ := mem_filter.mpr ⟨mem_univ _, hc a₁ ha₁'⟩
    have hmem2 : cOf a₁ ∈ clusterOf a₂ := hEq ▸ hmem1
    exact (hc a₁ ha₁').symm.trans (mem_filter.mp hmem2).2
  have hpw : (parts : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA B hB hAB
    simp only [parts, coe_image, Set.mem_image, mem_coe] at hA hB
    rcases hA with ⟨a₁, _, rfl⟩
    rcases hB with ⟨a₂, _, rfl⟩
    refine Finset.disjoint_left.mpr fun v hv1 hv2 ↦ hAB ?_
    simp only [id_eq, clusterOf, mem_filter, mem_univ, true_and] at hv1 hv2
    rw [← hv1, hv2]
  have hsup : parts.sup id = (univ : Finset V) := by
    ext v
    simp only [parts, sup_image, id_eq, Function.comp_def, sup_eq_biUnion, mem_biUnion,
      Finset.mem_range, clusterOf, mem_filter, mem_univ, true_and, iff_true]
    exact ⟨α v, hlt v, rfl⟩
  have hbot : (⊥ : Finset V) ∉ parts := by
    simp only [parts, bot_eq_empty, mem_image, Finset.mem_range]
    rintro ⟨a, ha, hEmpty⟩
    have hmem : cOf a ∈ clusterOf a := mem_filter.mpr ⟨mem_univ _, hc a ha⟩
    rw [hEmpty] at hmem
    exact notMem_empty _ hmem
  let P : Finpartition (univ : Finset V) := ⟨parts, hpw.supIndep, hsup, hbot⟩
  refine ⟨P, ?_, ?_⟩
  · dsimp [P, parts]
    rw [card_image_of_injOn hinj, card_range]
  · dsimp [P, parts]
    exact sum_image fun a₁ ha₁ a₂ ha₂ hEq ↦ hinj ha₁ ha₂ hEq

private def execClusterCost (x : EuclideanKMeansInstance) (labels : List ℕ) (a : ℕ) : ℚ :=
  let cnt : ℚ :=
    ((List.range x.n).map fun i ↦ if decide (labels.getD i 0 = a) then (1 : ℚ) else 0).sum
  let sqSum : ℚ :=
    ((List.range x.n).map fun i ↦
      if decide (labels.getD i 0 = a) then
        ((List.range x.d).map fun r ↦ pointCoord x.points i r * pointCoord x.points i r).sum
      else 0).sum
  let centSq : ℚ :=
    ((List.range x.d).map fun r ↦
      let s := ((List.range x.n).map fun i ↦
        if decide (labels.getD i 0 = a) then pointCoord x.points i r else 0).sum
      s * s).sum
  sqSum - centSq / cnt

private def check (p : EuclideanKMeansInstance × (List ℕ × List ℕ)) : Bool :=
  let x := p.1
  let labels := p.2.1
  let reps := p.2.2
  if decide (x.n = 0) then decide (x.k = 0) && decide (0 ≤ x.bound)
  else
    decide (1 ≤ x.k) && decide (x.k ≤ x.n) &&
    decide (labels.length = x.n) &&
    decide (reps.length = x.k) &&
    ((List.range x.n).all fun i ↦ decide (labels.getD i 0 < x.k)) &&
    ((List.range reps.length).all fun a ↦
      decide (reps.getD a 0 < x.n) &&
      decide (labels.getD (reps.getD a 0) 0 = a)) &&
    decide (((List.range reps.length).map fun a ↦ execClusterCost x labels a).sum ≤ x.bound)

private theorem computableInPolyTime_check :
    ComputableInPolyTime check
      (encPair encEuclideanKMeans (encPair (encList encNat) (encList encNat))) encBool := by
  let E := encPair encEuclideanKMeans (encPair (encList encNat) (encList encNat))
  have hX : ComputableInPolyTime (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦ p.1)
      E encEuclideanKMeans := fst _ _
  have hn : ComputableInPolyTime (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦ p.1.n)
      E encUnary := encEuclideanKMeans_n_polyTime hX
  have hn_bin : ComputableInPolyTime (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦ p.1.n)
      E encNat := unary_to_binary.comp hn
  have hd : ComputableInPolyTime (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦ p.1.d)
      E encUnary := encEuclideanKMeans_d_polyTime hX
  have hpts : ComputableInPolyTime
      (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦ p.1.points)
      E (encList (encList encRat)) := encEuclideanKMeans_points_polyTime hX
  have hk : ComputableInPolyTime (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦ p.1.k)
      E encNat := encEuclideanKMeans_k_polyTime hX
  have hB : ComputableInPolyTime (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦ p.1.bound)
      E encRat := encEuclideanKMeans_bound_polyTime hX
  have hlab : ComputableInPolyTime (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦ p.2.1)
      E (encList encNat) := (fst _ _).comp (snd _ _)
  have hrep : ComputableInPolyTime (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦ p.2.2)
      E (encList encNat) := (snd _ _).comp (snd _ _)
  have hall1 : ComputableInPolyTime
      (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦
        (List.range p.1.n).all fun i ↦ decide (p.2.1.getD i 0 < p.1.k)) E encBool :=
    allWithInput (ComputableInPolyTime.range.comp hn)
      (binary_lt' (listGetDWithInput (hlab.comp (fst _ _)) (snd _ _) 0)
        (hk.comp (fst _ _)))
  have hall2 : ComputableInPolyTime
      (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦
        (List.range p.2.2.length).all fun a ↦
          decide (p.2.2.getD a 0 < p.1.n) &&
          decide (p.2.1.getD (p.2.2.getD a 0) 0 = a)) E encBool := by
    apply allWithInput (ComputableInPolyTime.range.comp ((length_list encNat).comp hrep))
    have hra : ComputableInPolyTime
        (fun q : (EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ ↦ q.1.2.2.getD q.2 0)
        (encPair E encUnary) encNat :=
      listGetDWithInput (hrep.comp (fst _ _)) (snd _ _) 0
    exact bool_and'
      (binary_lt' hra (hn_bin.comp (fst _ _)))
      (decide_eq' (listGetD_binary (encA := encNat) 0 (hlab.comp (fst _ _)) hra)
        (unary_to_binary.comp (snd _ _)))
  have hcost : ComputableInPolyTime
      (fun p : EuclideanKMeansInstance × (List ℕ × List ℕ) ↦
        decide (((List.range p.2.2.length).map fun a ↦
          execClusterCost p.1 p.2.1 a).sum ≤ p.1.bound)) E encBool := by
    refine rat_le'
      (km_ratListSum_polyTime
        (mapWithInput (ComputableInPolyTime.range.comp ((length_list encNat).comp hrep)) ?_)) hB
    let E1 := encPair E encUnary
    let E2 := encPair E1 encUnary
    let E3 := encPair E2 encUnary
    have hcnt : ComputableInPolyTime
        (fun q : (EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ ↦
          ((List.range q.1.1.n).map fun i ↦
            if decide (q.1.2.1.getD i 0 = q.2) then (1 : ℚ) else 0).sum)
        E1 encRat := by
      refine km_ratListSum_polyTime
        (mapWithInput (ComputableInPolyTime.range.comp (hn.comp (fst _ _))) ?_)
      have hli : ComputableInPolyTime
          (fun r : ((EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ) × ℕ ↦
            r.1.1.2.1.getD r.2 0) E2 encNat :=
        listGetDWithInput (hlab.comp ((fst _ _).comp (fst _ _))) (snd _ _) 0
      exact ite' (decide_eq' hli (unary_to_binary.comp ((snd _ _).comp (fst _ _))))
        (const (1 : ℚ)) (const (0 : ℚ))
    have hsqSum : ComputableInPolyTime
        (fun q : (EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ ↦
          ((List.range q.1.1.n).map fun i ↦
            if decide (q.1.2.1.getD i 0 = q.2) then
              ((List.range q.1.1.d).map fun r ↦
                pointCoord q.1.1.points i r * pointCoord q.1.1.points i r).sum
            else 0).sum)
        E1 encRat := by
      refine km_ratListSum_polyTime
        (mapWithInput (ComputableInPolyTime.range.comp (hn.comp (fst _ _))) ?_)
      have hli : ComputableInPolyTime
          (fun s : ((EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ) × ℕ ↦
            s.1.1.2.1.getD s.2 0) E2 encNat :=
        listGetDWithInput (hlab.comp ((fst _ _).comp (fst _ _))) (snd _ _) 0
      have hptSq : ComputableInPolyTime
          (fun s : ((EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ) × ℕ ↦
            ((List.range s.1.1.1.d).map fun r ↦
              pointCoord s.1.1.1.points s.2 r * pointCoord s.1.1.1.points s.2 r).sum)
          E2 encRat := by
        refine km_ratListSum_polyTime
          (mapWithInput (ComputableInPolyTime.range.comp (hd.comp ((fst _ _).comp (fst _ _)))) ?_)
        have hc : ComputableInPolyTime
            (fun t : (((EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ) × ℕ) × ℕ ↦
              pointCoord t.1.1.1.1.points t.1.2 t.2) E3 encRat :=
          computableInPolyTime_pointCoord_unary
            (hpts.comp ((fst _ _).comp ((fst _ _).comp (fst _ _))))
            ((snd _ _).comp (fst _ _)) (snd _ _)
        exact rat_mul' hc hc
      exact ite' (decide_eq' hli (unary_to_binary.comp ((snd _ _).comp (fst _ _))))
        hptSq (const (0 : ℚ))
    have hcentSq : ComputableInPolyTime
        (fun q : (EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ ↦
          ((List.range q.1.1.d).map fun r ↦
            let s := ((List.range q.1.1.n).map fun i ↦
              if decide (q.1.2.1.getD i 0 = q.2) then pointCoord q.1.1.points i r else 0).sum
            s * s).sum)
        E1 encRat := by
      refine km_ratListSum_polyTime
        (mapWithInput (ComputableInPolyTime.range.comp (hd.comp (fst _ _))) ?_)
      have hs : ComputableInPolyTime
          (fun u : ((EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ) × ℕ ↦
            ((List.range u.1.1.1.n).map fun i ↦
              if decide (u.1.1.2.1.getD i 0 = u.1.2) then
                pointCoord u.1.1.1.points i u.2
              else 0).sum) E2 encRat := by
        refine km_ratListSum_polyTime
          (mapWithInput (ComputableInPolyTime.range.comp (hn.comp ((fst _ _).comp (fst _ _)))) ?_)
        have hli : ComputableInPolyTime
            (fun t : (((EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ) × ℕ) × ℕ ↦
              t.1.1.1.2.1.getD t.2 0) E3 encNat :=
          listGetDWithInput (hlab.comp ((fst _ _).comp ((fst _ _).comp (fst _ _)))) (snd _ _) 0
        have hc : ComputableInPolyTime
            (fun t : (((EuclideanKMeansInstance × (List ℕ × List ℕ)) × ℕ) × ℕ) × ℕ ↦
              pointCoord t.1.1.1.1.points t.2 t.1.2) E3 encRat :=
          computableInPolyTime_pointCoord_unary
            (hpts.comp ((fst _ _).comp ((fst _ _).comp (fst _ _))))
            (snd _ _) ((snd _ _).comp (fst _ _))
        exact ite'
          (decide_eq' hli (unary_to_binary.comp ((snd _ _).comp ((fst _ _).comp (fst _ _)))))
          hc (const (0 : ℚ))
      exact rat_mul' hs hs
    unfold execClusterCost
    dsimp only
    exact rat_sub' hsqSum (rat_div' hcentSq hcnt)
  unfold check
  dsimp only
  refine ite' (decide_eq' hn (const 0))
    (bool_and' (decide_eq' hk (const 0)) (rat_le' (const 0) hB)) ?_
  exact bool_and'
    (bool_and'
      (bool_and'
        (bool_and'
          (bool_and'
            (bool_and' (binary_le' (const 1) hk) (binary_le' hk hn_bin))
            (decide_eq' ((length_list encNat).comp hlab) hn))
          (decide_eq' (unary_to_binary.comp ((length_list encNat).comp hrep)) hk))
        hall1)
      hall2)
    hcost

private lemma execClusterCost_eq_kmeansClusterCost (x : EuclideanKMeansInstance)
    (labels : List ℕ) (a : ℕ)
    (hnonempty : (univ.filter fun v : Fin x.n ↦ labels.getD v.1 0 = a).Nonempty) :
    execClusterCost x labels a =
      kmeansClusterCost x.d x.points (univ.filter fun v : Fin x.n ↦ labels.getD v.1 0 = a) := by
  set C := univ.filter fun v : Fin x.n ↦ labels.getD v.1 0 = a
  rw [kmeansClusterCost_eq_sum_sq_sub x.d x.points hnonempty]
  unfold execClusterCost
  dsimp only
  have hcnt : ((List.range x.n).map fun i ↦
      if decide (labels.getD i 0 = a) then (1 : ℚ) else 0).sum = (C.card : ℚ) := by
    rw [km_sum_map_range,
      ← Fin.sum_univ_eq_sum_range (fun i ↦ if decide (labels.getD i 0 = a) then (1 : ℚ) else 0)]
    simp only [decide_eq_true_eq, sum_boole, C]
  have hsq : ((List.range x.n).map fun i ↦
      if decide (labels.getD i 0 = a) then
        ((List.range x.d).map fun r ↦ pointCoord x.points i r * pointCoord x.points i r).sum
      else 0).sum = ∑ i ∈ C, ∑ r ∈ Finset.range x.d, (pointCoord x.points i.1 r) ^ 2 := by
    rw [km_sum_map_range, ← Fin.sum_univ_eq_sum_range
      (fun i ↦ if decide (labels.getD i 0 = a) then
        ((List.range x.d).map fun r ↦ pointCoord x.points i r * pointCoord x.points i r).sum
      else 0)]
    simp only [decide_eq_true_eq]
    rw [← sum_filter]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [km_sum_map_range]
    exact sum_congr rfl fun r _ ↦ (sq (pointCoord x.points i.1 r)).symm
  have hcent : ((List.range x.d).map fun r ↦
      let s := ((List.range x.n).map fun i ↦
        if decide (labels.getD i 0 = a) then pointCoord x.points i r else 0).sum
      s * s).sum = ∑ r ∈ Finset.range x.d, (∑ i ∈ C, pointCoord x.points i.1 r) ^ 2 := by
    rw [km_sum_map_range]
    refine sum_congr rfl fun r _ ↦ ?_
    dsimp only
    have hs : ((List.range x.n).map fun i ↦
        if decide (labels.getD i 0 = a) then pointCoord x.points i r else 0).sum =
        ∑ i ∈ C, pointCoord x.points i.1 r := by
      rw [km_sum_map_range, ← Fin.sum_univ_eq_sum_range
        (fun i ↦ if decide (labels.getD i 0 = a) then pointCoord x.points i r else 0)]
      simp only [decide_eq_true_eq]
      rw [← sum_filter]
    rw [hs, sq]
  rw [hcnt, hsq, hcent]

private theorem mem_of_check {x : EuclideanKMeansInstance} {w : List ℕ × List ℕ}
    (h : check (x, w) = true) : x ∈ EuclideanKMeans := by
  unfold check at h
  dsimp only at h
  by_cases hn0 : x.n = 0
  · simp only [hn0, decide_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hk0, hB0⟩
    have hemp : (univ : Finset (Fin x.n)) = ⊥ :=
      card_eq_zero.mp (by rw [card_univ, Fintype.card_fin, hn0])
    let P : Finpartition (univ : Finset (Fin x.n)) := (Finpartition.empty _).copy hemp.symm
    have hPparts : P.parts = ∅ := by simp [P]
    refine ⟨P, by rw [hPparts, card_empty, hk0], ?_⟩
    simpa [kmeansCost, hPparts] using hB0
  · simp only [hn0, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
    rcases h with ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hreplen⟩, hall1⟩, hall2⟩, hcost⟩
    have hn_pos : 0 < x.n := Nat.pos_of_ne_zero hn0
    let α : Fin x.n → ℕ := fun i ↦ w.1.getD i.1 0
    let cOf : ℕ → Fin x.n := fun a ↦
      if hlt : w.2.getD a 0 < x.n then ⟨w.2.getD a 0, hlt⟩ else ⟨0, hn_pos⟩
    have hα_lt : ∀ i : Fin x.n, α i < x.k := fun i ↦ hall1 i.1 i.2
    have hc_eq : ∀ a < x.k, α (cOf a) = a := by
      intro a ha
      have ha' : a < w.2.length := hreplen.symm ▸ ha
      obtain ⟨hlt, hlab⟩ := hall2 a ha'
      dsimp [α, cOf]
      split_ifs
      exact hlab
    obtain ⟨P, hPcard, hPsum⟩ :=
      exists_finpartition_sum_of_assign α cOf hα_lt hc_eq (kmeansClusterCost x.d x.points)
    refine ⟨P, hPcard, ?_⟩
    rw [kmeansCost, hPsum]
    have hexec : ((List.range w.2.length).map fun a ↦ execClusterCost x w.1 a).sum =
        ∑ a ∈ Finset.range x.k,
          kmeansClusterCost x.d x.points (univ.filter fun v : Fin x.n ↦ α v = a) := by
      rw [hreplen, km_sum_map_range]
      refine sum_congr rfl fun a ha ↦ ?_
      have ha' : a < x.k := Finset.mem_range.mp ha
      exact execClusterCost_eq_kmeansClusterCost x w.1 a
        ⟨cOf a, mem_filter.mpr ⟨mem_univ _, hc_eq a ha'⟩⟩
    rw [← hexec]
    exact hcost

private theorem exists_check_of_mem {x : EuclideanKMeansInstance} (hx : x ∈ EuclideanKMeans) :
    ∃ w : List ℕ × List ℕ, check (x, w) = true ∧
      (encPair (encList encNat) (encList encNat) w).length ≤
        ((4 * Polynomial.X + 4) * (2 * Polynomial.X + 3)).eval (encEuclideanKMeans x).length := by
  obtain ⟨P, hPcard, hcost⟩ := hx
  let L := (encEuclideanKMeans x).length
  have hnL : x.n ≤ L := by
    have h := encEuclideanKMeans_n_length_le x
    rw [encUnary_apply, List.length_replicate] at h
    exact h
  have hpoly_val : ((4 * Polynomial.X + 4) * (2 * Polynomial.X + 3)).eval L =
      (4 * L + 4) * (2 * L + 3) := by simp
  by_cases hn0 : x.n = 0
  · have hPemp : P.parts = ∅ := by
      by_contra hne
      obtain ⟨C, hC⟩ := nonempty_iff_ne_empty.mpr hne
      obtain ⟨v, _⟩ := P.nonempty_of_mem_parts hC
      exact Fin.elim0 (hn0 ▸ v)
    have hk0 : x.k = 0 := by rw [← hPcard, hPemp, card_empty]
    have hB0 : 0 ≤ x.bound := by simpa [kmeansCost, hPemp] using hcost
    refine ⟨([], []), ?_, ?_⟩
    · unfold check
      simp [hn0, hk0, hB0]
    · rw [hpoly_val]
      have h0 : (encPair (encList encNat) (encList encNat) ([], [])).length = 1 := rfl
      rw [h0]
      exact Nat.mul_pos (by omega) (by omega)
  · have hkle : x.k ≤ x.n := by
      have hs : (P.parts.sup id).card = x.n := by rw [P.sup_parts, card_univ, Fintype.card_fin]
      calc
        x.k = P.parts.card := hPcard.symm
        _ = ∑ _C ∈ P.parts, 1 := by simp
        _ ≤ ∑ C ∈ P.parts, C.card :=
          sum_le_sum fun C hC ↦ (P.nonempty_of_mem_parts hC).card_pos
        _ = (P.parts.sup id).card := by
          rw [sup_eq_biUnion, card_biUnion (fun A hA B hB hAB ↦ P.disjoint hA hB hAB)]
          rfl
        _ = x.n := hs
    have hkpos : 1 ≤ x.k := by
      by_contra hk0
      have hk0' : x.k = 0 := by omega
      have hPemp : P.parts = ∅ := card_eq_zero.mp (hPcard.trans hk0')
      have hs := P.sup_parts
      rw [hPemp, sup_empty, bot_eq_empty] at hs
      have hcard0 : (univ : Finset (Fin x.n)).card = 0 := by rw [← hs, card_empty]
      rw [card_univ, Fintype.card_fin] at hcard0
      exact hn0 hcard0
    let e : P.parts ≃ Fin x.k := P.parts.equivFin.trans (finCongr hPcard)
    have hcov : ∀ i : Fin x.n, ∃ C : P.parts, i ∈ C.1 := by
      intro i
      have hi : i ∈ P.parts.sup id := by rw [P.sup_parts]; exact mem_univ i
      rw [sup_eq_biUnion, mem_biUnion] at hi
      obtain ⟨C, hC, hiC⟩ := hi
      exact ⟨⟨C, hC⟩, hiC⟩
    let partOf (i : Fin x.n) : P.parts := Classical.choose (hcov i)
    have hpartOf_mem : ∀ i : Fin x.n, i ∈ (partOf i).1 :=
      fun i ↦ Classical.choose_spec (hcov i)
    have hpartOf_eq : ∀ (C : P.parts) {i : Fin x.n}, i ∈ C.1 → partOf i = C := by
      intro C i hi
      by_contra hne
      exact Finset.disjoint_left.mp (P.disjoint (partOf i).2 C.2 (Subtype.coe_ne_coe.mpr hne))
        (hpartOf_mem i) hi
    let repOf (C : P.parts) : Fin x.n := Classical.choose (P.nonempty_of_mem_parts C.2)
    have hrepOf_mem : ∀ C : P.parts, repOf C ∈ C.1 :=
      fun C ↦ Classical.choose_spec (P.nonempty_of_mem_parts C.2)
    let labels : List ℕ := List.ofFn fun i : Fin x.n ↦ (e (partOf i)).1
    let reps : List ℕ := List.ofFn fun a : Fin x.k ↦ (repOf (e.symm a)).1
    refine ⟨(labels, reps), ?_, ?_⟩
    · unfold check
      dsimp only
      simp only [hn0, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true, List.mem_range]
      refine ⟨⟨⟨⟨⟨⟨hkpos, hkle⟩, List.length_ofFn⟩, List.length_ofFn⟩, ?_⟩, ?_⟩, ?_⟩
      · intro i hi
        have hget : labels.getD i 0 = (e (partOf ⟨i, hi⟩)).1 := by
          simp [labels, List.getD_eq_getElem?_getD, hi]
        rw [hget]
        exact (e (partOf ⟨i, hi⟩)).2
      · intro a ha
        rw [List.length_ofFn] at ha
        have hrget : reps.getD a 0 = (repOf (e.symm ⟨a, ha⟩)).1 := by
          simp [reps, List.getD_eq_getElem?_getD, ha]
        rw [hrget]
        refine ⟨(repOf (e.symm ⟨a, ha⟩)).2, ?_⟩
        have hlget : labels.getD (repOf (e.symm ⟨a, ha⟩)).1 0 =
            (e (partOf (repOf (e.symm ⟨a, ha⟩)))).1 := by
          simp [labels, List.getD_eq_getElem?_getD, (repOf (e.symm ⟨a, ha⟩)).2]
        rw [hlget, hpartOf_eq (e.symm ⟨a, ha⟩) (hrepOf_mem _), e.apply_symm_apply]
      · have hfilter_eq : ∀ a : Fin x.k,
            (univ.filter fun v : Fin x.n ↦ labels.getD v.1 0 = a.1) = (e.symm a).1 := by
          intro a
          ext v
          simp only [mem_filter, mem_univ, true_and, labels, List.getD_eq_getElem?_getD, v.2,
            List.getElem?_ofFn, ↓reduceDIte, Fin.eta, Option.getD_some]
          constructor
          · intro hEq
            have he : e (partOf v) = a := Fin.ext hEq
            rw [← he, e.symm_apply_apply]
            exact hpartOf_mem v
          · intro hv
            rw [hpartOf_eq (e.symm a) hv, e.apply_symm_apply]
        have hsum_eq : ((List.range reps.length).map fun a ↦ execClusterCost x labels a).sum =
            kmeansCost x.n x.d x.points P := by
          have hlen : reps.length = x.k := List.length_ofFn
          rw [hlen, km_sum_map_range, ← Fin.sum_univ_eq_sum_range
            (fun a ↦ execClusterCost x labels a)]
          have h1 : ∀ a : Fin x.k,
              execClusterCost x labels a.1 = kmeansClusterCost x.d x.points (e.symm a).1 := by
            intro a
            have hne : (univ.filter fun v : Fin x.n ↦ labels.getD v.1 0 = a.1).Nonempty := by
              rw [hfilter_eq a]
              exact P.nonempty_of_mem_parts (e.symm a).2
            rw [execClusterCost_eq_kmeansClusterCost x labels a.1 hne, hfilter_eq a]
          rw [sum_congr rfl fun a _ ↦ h1 a]
          rw [kmeansCost, ← sum_attach P.parts (kmeansClusterCost x.d x.points)]
          exact Fintype.sum_equiv e.symm
            (fun a ↦ kmeansClusterCost x.d x.points (e.symm a).1)
            (fun C ↦ kmeansClusterCost x.d x.points C.1) fun _ ↦ rfl
        rw [hsum_eq]
        exact hcost
    · rw [hpoly_val, length_encPair]
      have hlen_nat : ∀ v : ℕ, v < x.n → (encNat v).length ≤ L := by
        intro v hv
        rw [encNat_apply, Nat.size_eq_bits_len]
        exact Nat.size_le.mpr (hv.trans_le (hnL.trans Nat.lt_two_pow_self.le))
      have h1 : (encList encNat labels).length ≤ x.n * (2 * L + 1) := by
        have := length_encList_le encNat labels (b := L) fun v hv ↦ by
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hv
          exact hlen_nat _ ((e (partOf i)).2.trans_le hkle)
        simpa [labels] using this
      have h2 : (encList encNat reps).length ≤ x.k * (2 * L + 1) := by
        have := length_encList_le encNat reps (b := L) fun v hv ↦ by
          obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).mp hv
          exact hlen_nat _ (repOf (e.symm a)).2
        simpa [reps] using this
      have hkL : x.k ≤ L := hkle.trans hnL
      nlinarith

/-- `EuclideanKMeans` belongs to `NP`. -/
theorem mem_NP : EuclideanKMeans ∈ NP encEuclideanKMeans :=
  mem_NP_of_check (.pair (.list .nat) (.list .nat)) computableInPolyTime_check
    (fun _ _ h ↦ mem_of_check h) fun _ hx ↦ exists_check_of_mem hx

end EuclideanKMeans

/-- `TwoMeans` belongs to `NP`. -/
theorem TwoMeans.mem_NP : TwoMeans ∈ NP encEuclideanKMeans :=
  mem_NP_of_guard (c := fun x ↦ decide (x.k = 2))
    (decide_eq' (encEuclideanKMeans_k_polyTime id') (const 2))
    EuclideanKMeans.mem_NP fun x ↦ by simp [TwoMeans]

end CslibFrontier.Computability.Complexity
