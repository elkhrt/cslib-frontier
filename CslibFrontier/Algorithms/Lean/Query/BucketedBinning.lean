/-
Copyright (c) 2026 Formal Papers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Query.BinarySearch
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Histogram-Guided Bucketed Binary Search for Non-Uniform Interval Location

Given `m ≥ 1` strictly increasing real endpoints `b₀ < b₁ < ⋯ < b_m` defining `m` half-open
intervals `[b_i, b_{i+1})`, direct binary search in the threshold-probe query model (`FreeM
ProbeQuery`) locates the interval containing a query point `x ∈ [b₀, b_m)` in at most
`Nat.log 2 (m - 1) + 1` comparisons.

This module formalizes a two-level histogram-guided bucket index of arbitrary resolution `u ≥ 1`:
1. Subdivide `[b₀, b_m)` uniformly into `u` buckets of width `Δ = (b_m - b₀) / u`.
2. Precompute the interior-endpoint occupancy histogram `H : Fin u → ℕ` (with `∑ q, H q = m - 1`)
   and its cumulative prefix-sum offset array `S : Fin (u + 1) → ℕ` (`S 0 = 1`,
   `S (q + 1) = S q + H q`, `S u = m`).
3. To locate `x ∈ [b₀, b_m)`, compute its uniform bucket `q = ⌊(x - b₀) / Δ⌋`, dispatch on
   `H q ∈ {0, 1, 2}` in `0`, `1`, or at most `2` threshold probes, and otherwise invoke
   `Cslib.Query.lowerBoundBy` exclusively over the `H q` interior endpoints inside bucket `q`.

Under a uniform ensemble over weak compositions of `n` interior endpoints across `u` buckets
(`n ≤ u`, `2 ≤ u`), the conditional mean occupancy among buckets with `H q ≥ 3` equals
`3 + (n - 3) / u < 4`, and by concavity of `log₂` the expected lookup cost per query is bounded
by a universal constant (`≤ 3`), independent of `n` and `u`.

## Main definitions

* `CslibFrontier.Algorithms.Lean.Query.BucketedBinning.MonotonePartition`: strictly increasing
  real partition `b₀ < ⋯ < b_m` (`m ≥ 1`).
* `CslibFrontier.Algorithms.Lean.Query.BucketedBinning.MonotonePartition.intervalIndex`: exact
  1-based interval rank `#{i | b_i ≤ x}` (`0` below `b₀`, `m + 1` at or above `b_m`).
* `CslibFrontier.Algorithms.Lean.Query.BucketedBinning.MonotonePartition.bucketCount`,
  `bucketOffset`: uniform bucket histogram and prefix-sum offsets for arbitrary resolution `u ≥ 1`.
* `CslibFrontier.Algorithms.Lean.Query.BucketedBinning.MonotonePartition.bucketedSearchQ`:
  threshold-probe query program (`FreeM ProbeQuery ℕ`) implementing bucketed interval location.
* `CslibFrontier.Algorithms.Lean.Query.BucketedBinning.expectedBucketLookupCost`: expected
  per-query step cost over all weak compositions of `n` interior endpoints into `u` buckets.

## Main results

* `sum_bucketCount`, `exists_bucketCount_eq_zero`: the histogram sums to `m - 1`, guaranteeing an
  empty bucket whenever `m ≤ u`.
* `eval_bucketedSearchQ`: exact agreement of `bucketedSearchQ` with `intervalIndex` on all `x : ℝ`.
* `countQueries_bucketedSearchQ_le`: exact per-bucket threshold-probe query bounds (`0`, `1`,
  `≤ 2`, and `≤ Nat.log 2 (H q) + 1`).
* `expectedBucketLookupCost_le_three`: for all `2 ≤ u` and `n ≤ u`, the expected per-query lookup
  cost over all weak compositions of `n` interior endpoints across `u` buckets is at most `3`.
-/

public section

namespace CslibFrontier.Algorithms.Lean.Query.BucketedBinning

open scoped BigOperators Finset

/-- A strictly increasing real partition `b₀ < b₁ < ⋯ < b_m` defining `m ≥ 1` half-open
intervals `[b_i, b_{i+1})`. -/
@[ext]
structure MonotonePartition (m : ℕ) where
  /-- Positivity of the number of intervals `m ≥ 1`. -/
  bins_pos : 0 < m
  /-- Strictly increasing boundary values `b₀, …, b_m`. -/
  boundary : Fin (m + 1) → ℝ
  /-- Strict monotonicity of the boundaries. -/
  strictMono : StrictMono boundary

namespace MonotonePartition

variable {m : ℕ} (P : MonotonePartition m)

/-- Leftmost endpoint `b₀`. -/
@[expose] def lower : ℝ := P.boundary 0

/-- Rightmost endpoint `b_m`. -/
@[expose] def upper : ℝ := P.boundary (Fin.last m)

/-- Strict span positivity `b₀ < b_m`. -/
theorem lower_lt_upper : P.lower < P.upper :=
  P.strictMono (Fin.mk_lt_mk.mpr P.bins_pos)

/-- Exact interval rank `#{i : Fin (m + 1) | b_i ≤ x}` (`0` when `x < b₀`, `q ∈ {1, …, m}` when
`b_{q-1} ≤ x < b_q`, and `m + 1` when `b_m ≤ x`). -/
noncomputable def intervalIndex (x : ℝ) : ℕ := by
  classical
  exact #{i : Fin (m + 1) | P.boundary i ≤ x}

private lemma card_fin_filter_lt {n k : ℕ} (hk : k ≤ n) :
    #{j : Fin n | j.val < k} = k := by
  calc #{j : Fin n | j.val < k}
    _ = #(Finset.univ : Finset (Fin k)) := by
        refine Finset.card_bij
          (fun (j : Fin n) hj ↦ (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin k))
          (fun _ _ ↦ Finset.mem_univ _)
          (fun _ _ _ _ h ↦ Fin.ext (by simpa using congr_arg Fin.val h))
          (fun t _ ↦ ⟨⟨t.val, by omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, by ext; rfl⟩)
    _ = k := by simp

/-- Threshold equivalence `b_i ≤ x ↔ i < intervalIndex P x`. -/
theorem boundary_le_iff_lt_intervalIndex (x : ℝ) (i : Fin (m + 1)) :
    P.boundary i ≤ x ↔ i.val < P.intervalIndex x := by
  classical
  rw [intervalIndex]
  constructor
  · intro hbx
    have hcard_le : #{j : Fin (m + 1) | j.val < i.val + 1} ≤
        #{j : Fin (m + 1) | P.boundary j ≤ x} :=
      Finset.card_le_card fun j hj ↦
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (P.strictMono.monotone (Fin.mk_le_mk.mpr (Nat.lt_succ_iff.mp
            (Finset.mem_filter.mp hj).2))).trans hbx⟩
    rw [card_fin_filter_lt (by omega)] at hcard_le
    omega
  · contrapose!
    intro hlt
    have hcard_le : #{j : Fin (m + 1) | P.boundary j ≤ x} ≤ #{j : Fin (m + 1) | j.val < i.val} :=
      Finset.card_le_card fun j hj ↦
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Fin.mk_lt_mk.mp (P.strictMono.lt_iff_lt.mp
            ((Finset.mem_filter.mp hj).2.trans_lt hlt))⟩
    rw [card_fin_filter_lt (by omega)] at hcard_le
    omega

/-- Upper bound `intervalIndex P x ≤ m + 1`. -/
theorem intervalIndex_le (x : ℝ) : P.intervalIndex x ≤ m + 1 := by
  classical
  rw [intervalIndex]
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- Interval characterization for `1 ≤ q ≤ m`: `intervalIndex P x = q ↔ b_{q-1} ≤ x ∧ x < b_q`. -/
theorem intervalIndex_eq_iff {q : ℕ} (hq1 : 1 ≤ q) (hqm : q ≤ m) (x : ℝ) :
    P.intervalIndex x = q ↔
      P.boundary ⟨q - 1, by omega⟩ ≤ x ∧ x < P.boundary ⟨q, by omega⟩ := by
  have h1 := P.boundary_le_iff_lt_intervalIndex x ⟨q - 1, by omega⟩
  have h2 := P.boundary_le_iff_lt_intervalIndex x ⟨q, by omega⟩
  dsimp only at h1 h2
  constructor
  · intro hq
    exact ⟨h1.mpr (by omega), not_le.mp fun hle ↦ by have := h2.mp hle; omega⟩
  · rintro ⟨hlo, hhi⟩
    have ha := h1.mp hlo
    have hb : ¬(q < P.intervalIndex x) := fun hc ↦ not_le.mpr hhi (h2.mpr hc)
    omega

/-- Uniform bucket width `Δ = (b_m - b₀) / u` for `u ≥ 1` buckets. -/
@[expose] noncomputable def bucketWidth (u : ℕ) : ℝ :=
  (P.upper - P.lower) / (u : ℝ)

/-- Positivity of `bucketWidth` when `0 < u`. -/
theorem bucketWidth_pos {u : ℕ} (hu : 0 < u) : 0 < P.bucketWidth u :=
  div_pos (sub_pos.mpr P.lower_lt_upper) (Nat.cast_pos.mpr hu)

/-- Uniform bucket boundary `b₀ + i · Δ` for `i : Fin (u + 1)`. -/
@[expose] noncomputable def bucketBoundary (u : ℕ) (i : Fin (u + 1)) : ℝ :=
  P.lower + (i.val : ℝ) * P.bucketWidth u

/-- Constant-time 1-based uniform bucket lookup `⌊(x - b₀) / Δ⌋ + 1` on `x ≥ b₀` (`0` for
`x < b₀`). -/
noncomputable def uniformBucket (u : ℕ) (x : ℝ) : ℕ := by
  classical
  exact if x < P.lower then 0 else (⌊(x - P.lower) / P.bucketWidth u⌋).toNat + 1

/-- Threshold equivalence for uniform buckets: `b₀ + k · Δ ≤ x ↔ k < uniformBucket P u x`. -/
theorem bucketBoundary_le_iff_lt_uniformBucket {u : ℕ} (hu : 0 < u) (x : ℝ) (i : Fin (u + 1)) :
    P.bucketBoundary u i ≤ x ↔ i.val < P.uniformBucket u x := by
  classical
  rw [uniformBucket]
  have hstep := P.bucketWidth_pos hu
  by_cases hx : x < P.lower
  · simp only [ite_eq_left hx, Nat.not_lt_zero, iff_false, not_le, bucketBoundary]
    have hi0 : 0 ≤ (i.val : ℝ) * P.bucketWidth u := mul_nonneg (Nat.cast_nonneg _) hstep.le
    linarith
  · simp only [ite_eq_right hx]
    have hx0 : 0 ≤ (x - P.lower) / P.bucketWidth u :=
      div_nonneg (sub_nonneg.mpr (not_lt.mp hx)) hstep.le
    have hfl_nonneg : 0 ≤ ⌊(x - P.lower) / P.bucketWidth u⌋ := Int.floor_nonneg.mpr hx0
    calc P.bucketBoundary u i ≤ x
      _ ↔ (i.val : ℝ) * P.bucketWidth u ≤ x - P.lower := by
            rw [bucketBoundary]; constructor <;> intro h <;> linarith
      _ ↔ (i.val : ℝ) ≤ (x - P.lower) / P.bucketWidth u := (le_div_iff₀ hstep).symm
      _ ↔ (i.val : ℤ) ≤ ⌊(x - P.lower) / P.bucketWidth u⌋ := by
            simpa using
              (Int.le_floor (a := (x - P.lower) / P.bucketWidth u) (z := (i.val : ℤ))).symm
      _ ↔ i.val < ⌊(x - P.lower) / P.bucketWidth u⌋.toNat + 1 := by omega

/-- Interior endpoint index `j ↦ j + 1` in `Fin (m + 1)`. -/
@[expose] def interiorIdx (j : Fin (m - 1)) : Fin (m + 1) :=
  ⟨j.val + 1, by omega⟩

/-- Number of interior partition endpoints `b₁, …, b_{m-1}` lying in uniform bucket `q : Fin u`. -/
noncomputable def bucketCount (u : ℕ) (q : Fin u) : ℕ := by
  classical
  exact #{j : Fin (m - 1) | P.uniformBucket u (P.boundary (interiorIdx j)) = q.val + 1}

/-- Cumulative offset array `S(i) = 1 + ∑_{q < i} bucketCount P u q`. -/
noncomputable def bucketOffset (u : ℕ) (i : Fin (u + 1)) : ℕ :=
  1 + ∑ q : Fin u with q.val < i.val, P.bucketCount u q

/-- Threshold comparison predicate `b_k ≤ x` (`false` out of bounds). -/
@[expose] noncomputable def probeCmp (x : ℝ) (k : ℕ) : Bool := by
  classical
  exact if hk : k < m + 1 then decide (P.boundary ⟨k, hk⟩ ≤ x) else false

/-- Threshold-probe oracle for `x : ℝ`. -/
@[expose] noncomputable def probeOracle (x : ℝ) :
    {ι : Type} → Cslib.Query.ProbeQuery ι → ι :=
  Cslib.Query.ProbeQuery.oracleOf (P.probeCmp x)

/-- Query-monad two-level bucketed interval search program over `u ≥ 1` uniform buckets. -/
noncomputable def bucketedSearchQ (u : ℕ) (x : ℝ) : Cslib.FreeM Cslib.Query.ProbeQuery ℕ := by
  classical
  if hxlo : x < P.lower then
    exact pure 0
  else if hxhi : P.upper ≤ x then
    exact pure (m + 1)
  else
    let qNat := P.uniformBucket u x - 1
    if hq : qNat < u then
      let q : Fin u := ⟨qNat, hq⟩
      let h := P.bucketCount u q
      let r := P.bucketOffset u q.castSucc
      exact
        if h = 0 then
          pure r
        else if h = 1 then
          do
            let c ← Cslib.Query.ProbeQuery.ask r
            if c then pure (r + 1) else pure r
        else if h = 2 then
          do
            let c2 ← Cslib.Query.ProbeQuery.ask (r + 1)
            if c2 then pure (r + 2)
            else
              let c1 ← Cslib.Query.ProbeQuery.ask r
              if !c1 then pure r else pure (r + 1)
        else
          do
            let offset ←
              Cslib.Query.lowerBoundBy (fun k ↦ Cslib.Query.ProbeQuery.ask (r + k)) 0 h
            pure (r + offset)
    else
      exact pure (m + 1)

private lemma bucketBoundary_last {u : ℕ} (hu : 0 < u) :
    P.bucketBoundary u (Fin.last u) = P.upper := by
  have hu0 : (u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hu.ne'
  simp only [bucketBoundary, Fin.val_last, bucketWidth]
  rw [mul_div_cancel₀ _ hu0]
  ring

private lemma uniformBucket_mem_Icc {u : ℕ} (hu : 0 < u) {x : ℝ}
    (hlo : P.lower ≤ x) (hhi : x < P.upper) :
    1 ≤ P.uniformBucket u x ∧ P.uniformBucket u x ≤ u := by
  have h0 := (P.bucketBoundary_le_iff_lt_uniformBucket hu x 0).mp
    (by simp [bucketBoundary, hlo])
  have hu_not : ¬(u < P.uniformBucket u x) := fun hc ↦ by
    have hge := (P.bucketBoundary_le_iff_lt_uniformBucket hu x (Fin.last u)).mpr hc
    rw [P.bucketBoundary_last hu] at hge
    linarith
  simp only [Fin.val_zero] at h0
  omega

private lemma uniformBucket_interior_mem_Icc {u : ℕ} (hu : 0 < u) (j : Fin (m - 1)) :
    1 ≤ P.uniformBucket u (P.boundary (interiorIdx j)) ∧
      P.uniformBucket u (P.boundary (interiorIdx j)) ≤ u := by
  refine P.uniformBucket_mem_Icc hu ?_ ?_
  · exact (P.strictMono (show (0 : Fin (m + 1)) < interiorIdx j by
      simp [interiorIdx, Fin.lt_def])).le
  · exact P.strictMono (show interiorIdx j < Fin.last m by
      simp only [interiorIdx, Fin.lt_def, Fin.val_last]; omega)

private lemma bucketOffset_eq_one_add_card_lt {u : ℕ} (hu : 0 < u) (i : Fin (u + 1)) :
    P.bucketOffset u i =
      1 + #{j : Fin (m - 1) | P.boundary (interiorIdx j) < P.bucketBoundary u i} := by
  classical
  rw [bucketOffset]
  congr 1
  have hpart :
      (∑ q : Fin u with q.val < i.val, P.bucketCount u q) =
        #{j : Fin (m - 1) | P.uniformBucket u (P.boundary (interiorIdx j)) - 1 < i.val} := by
    simp only [bucketCount]
    rw [← Finset.card_biUnion]
    · congr 1; ext j
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      have hj := P.uniformBucket_interior_mem_Icc hu j
      constructor
      · rintro ⟨q, hqi, hju⟩; omega
      · intro hlt
        exact ⟨⟨P.uniformBucket u (P.boundary (interiorIdx j)) - 1, by omega⟩, hlt, by dsimp; omega⟩
    · intro q₁ _ q₂ _ hne
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj1 hj2; apply hne; ext; omega
  rw [hpart]
  congr 1; ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hj := P.uniformBucket_interior_mem_Icc hu j
  have hiff := P.bucketBoundary_le_iff_lt_uniformBucket hu (P.boundary (interiorIdx j)) i
  constructor
  · intro hlt; exact not_le.mp fun hle ↦ by have := hiff.mp hle; omega
  · intro hlt
    have hnot : ¬(i.val < P.uniformBucket u (P.boundary (interiorIdx j))) :=
      fun hc ↦ not_le.mpr hlt (hiff.mpr hc)
    omega

/-- The uniform-bucket histogram sums to `m - 1`, the number of interior endpoints. -/
theorem sum_bucketCount {u : ℕ} (hu : 0 < u) :
    ∑ q : Fin u, P.bucketCount u q = m - 1 := by
  have hlast := P.bucketOffset_eq_one_add_card_lt hu (Fin.last u)
  rw [bucketOffset, Fin.val_last, P.bucketBoundary_last hu] at hlast
  have hfilt : (Finset.univ.filter fun q : Fin u ↦ q.val < u) = Finset.univ := by
    ext q; simp
  rw [hfilt] at hlast
  have hall : #{j : Fin (m - 1) | P.boundary (interiorIdx j) < P.upper} = m - 1 := by
    rw [Finset.filter_true_of_mem]
    · simp
    · intro j _
      exact P.strictMono (show interiorIdx j < Fin.last m by
        simp only [interiorIdx, Fin.lt_def, Fin.val_last]; omega)
  omega

/-- Pigeonhole empty-bucket guarantee: whenever `m ≤ u`, at least one uniform bucket holds `0`
interior endpoints. -/
theorem exists_bucketCount_eq_zero {u : ℕ} (hmu : m ≤ u) :
    ∃ q : Fin u, P.bucketCount u q = 0 := by
  have hu : 0 < u := lt_of_lt_of_le P.bins_pos hmu
  by_contra! hpos
  have hge : u ≤ ∑ q : Fin u, P.bucketCount u q := by
    calc u = ∑ _ : Fin u, 1 := by simp
      _ ≤ ∑ q : Fin u, P.bucketCount u q :=
        Finset.sum_le_sum fun q _ ↦ Nat.pos_of_ne_zero (hpos q)
  have hsum := P.sum_bucketCount hu
  have hm := P.bins_pos
  omega

private lemma bucketOffset_succ {u : ℕ} (q : Fin u) :
    P.bucketOffset u q.succ = P.bucketOffset u q.castSucc + P.bucketCount u q := by
  rw [bucketOffset, bucketOffset]
  have hsplit :
      (Finset.univ.filter fun k : Fin u ↦ k.val < q.val + 1) =
        insert q (Finset.univ.filter fun k : Fin u ↦ k.val < q.val) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with heq | hlt
      · left; exact Fin.ext heq
      · right; exact hlt
    · rintro (rfl | hlt) <;> omega
  have hnotmem : q ∉ (Finset.univ.filter fun k : Fin u ↦ k.val < q.val) := by simp
  simp only [Fin.val_succ, Fin.val_castSucc, hsplit, Finset.sum_insert hnotmem]
  omega

private lemma bucketOffset_last {u : ℕ} (hu : 0 < u) :
    P.bucketOffset u (Fin.last u) = m := by
  have hpos := P.bins_pos
  rw [bucketOffset, Fin.val_last]
  have hfilt : (Finset.univ.filter fun q : Fin u ↦ q.val < u) = Finset.univ := by
    ext q; simp
  rw [hfilt, P.sum_bucketCount hu]
  omega

private lemma bucketOffset_add_count_le {u : ℕ} (hu : 0 < u) (q : Fin u) :
    1 ≤ P.bucketOffset u q.castSucc ∧ P.bucketOffset u q.castSucc + P.bucketCount u q ≤ m := by
  refine ⟨by rw [bucketOffset]; omega, ?_⟩
  calc P.bucketOffset u q.castSucc + P.bucketCount u q
    _ = P.bucketOffset u q.succ := (P.bucketOffset_succ q).symm
    _ ≤ P.bucketOffset u (Fin.last u) := by
        rw [bucketOffset, bucketOffset]
        refine Nat.add_le_add_left
          (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ Nat.zero_le _) 1
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last] at hk ⊢
        exact k.isLt
    _ = m := P.bucketOffset_last hu

private lemma boundary_interior_lt_bucket_iff {u : ℕ} (hu : 0 < u) (i : Fin (u + 1))
    (j : Fin (m - 1)) :
    P.boundary (interiorIdx j) < P.bucketBoundary u i ↔ j.val + 1 < P.bucketOffset u i := by
  classical
  rw [P.bucketOffset_eq_one_add_card_lt hu i]
  constructor
  · intro hjlt
    have hcard :
        #{k : Fin (m - 1) | k.val < j.val + 1} ≤
          #{k : Fin (m - 1) | P.boundary (interiorIdx k) < P.bucketBoundary u i} :=
      Finset.card_le_card fun k hk ↦ by
        have hkj := Nat.lt_succ_iff.mp (Finset.mem_filter.mp hk).2
        have hle : interiorIdx k ≤ interiorIdx j := by simp [interiorIdx, Fin.le_def, hkj]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (P.strictMono.monotone hle).trans_lt hjlt⟩
    rw [card_fin_filter_lt (by omega)] at hcard
    omega
  · contrapose!
    intro hjge
    have hcard :
        #{k : Fin (m - 1) | P.boundary (interiorIdx k) < P.bucketBoundary u i} ≤
          #{k : Fin (m - 1) | k.val < j.val} :=
      Finset.card_le_card fun k hk ↦ by
        have hkb := (Finset.mem_filter.mp hk).2
        have hlt : P.boundary (interiorIdx k) < P.boundary (interiorIdx j) := hkb.trans_le hjge
        have hidx : k.val + 1 < j.val + 1 := Fin.lt_def.mp (P.strictMono.lt_iff_lt.mp hlt)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    rw [card_fin_filter_lt (by omega)] at hcard
    omega

private lemma boundary_le_bucketBoundary_of_lt_offset {u : ℕ} (hu : 0 < u) (q : Fin u)
    {k : Fin (m + 1)} (hk : k.val < P.bucketOffset u q.castSucc) :
    P.boundary k ≤ P.bucketBoundary u q.castSucc := by
  rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
  · have hkeq : k = 0 := Fin.ext hk0
    rw [hkeq, show P.boundary 0 = P.lower from rfl, bucketBoundary]
    have h0 : 0 ≤ (q.castSucc.val : ℝ) * P.bucketWidth u :=
      mul_nonneg (Nat.cast_nonneg _) (P.bucketWidth_pos hu).le
    linarith
  · have hle := (P.bucketOffset_add_count_le hu q).2
    let j : Fin (m - 1) := ⟨k.val - 1, by omega⟩
    have hkj : interiorIdx j = k := by ext; simp [interiorIdx, j]; omega
    rw [← hkj]
    exact ((P.boundary_interior_lt_bucket_iff hu q.castSucc j).mpr (by simp [j]; omega)).le

private lemma bucketBoundary_succ_le_boundary {u : ℕ} (hu : 0 < u) (q : Fin u) :
    P.bucketBoundary u q.succ ≤
      P.boundary ⟨P.bucketOffset u q.castSucc + P.bucketCount u q,
        by have := (P.bucketOffset_add_count_le hu q).2; omega⟩ := by
  have hsum_eq := P.bucketOffset_succ q
  have hr1 := (P.bucketOffset_add_count_le hu q).1
  have hle_m := (P.bucketOffset_add_count_le hu q).2
  rcases eq_or_lt_of_le hle_m with heq | hlt
  · have hidx : (⟨P.bucketOffset u q.castSucc + P.bucketCount u q, by omega⟩ : Fin (m + 1)) =
        Fin.last m := Fin.ext heq
    rw [hidx, show P.boundary (Fin.last m) = P.upper from rfl, ← P.bucketBoundary_last hu]
    simp only [bucketBoundary, Fin.val_last]
    have hqle : (q.succ.val : ℝ) ≤ (u : ℝ) := Nat.cast_le.mpr (by omega)
    nlinarith [P.bucketWidth_pos hu]
  · let j : Fin (m - 1) := ⟨P.bucketOffset u q.castSucc + P.bucketCount u q - 1, by omega⟩
    have hj_not_lt : ¬(j.val + 1 < P.bucketOffset u q.succ) := by
      rw [hsum_eq]; simp only [j]; omega
    have hge := not_lt.mp (mt (P.boundary_interior_lt_bucket_iff hu q.succ j).mp hj_not_lt)
    have hidx : interiorIdx j = ⟨P.bucketOffset u q.castSucc + P.bucketCount u q, by omega⟩ := by
      ext; simp [interiorIdx, j]; omega
    rwa [hidx] at hge

private lemma offset_add_lowerBound_eq {u : ℕ} (hu : 0 < u) {x : ℝ} (q : Fin u)
    (hxlo : P.bucketBoundary u q.castSucc ≤ x) (hxhi : x < P.bucketBoundary u q.succ) :
    P.bucketOffset u q.castSucc +
        Cslib.Algorithms.Lean.lowerBound
          (fun k ↦ P.probeCmp x (P.bucketOffset u q.castSucc + k)) 0 (P.bucketCount u q) =
      P.intervalIndex x := by
  set r := P.bucketOffset u q.castSucc
  set h := P.bucketCount u q
  have hr_bounds := P.bucketOffset_add_count_le hu q
  have hmono : ∀ a a', 0 ≤ a → a ≤ a' → a' < h →
      P.probeCmp x (r + a') = true → P.probeCmp x (r + a) = true := by
    intro a a' _ haa' ha'h htrue
    have ha_lt : r + a < m + 1 := by omega
    have ha'_lt : r + a' < m + 1 := by omega
    simp only [probeCmp, dite_eq_left ha'_lt, decide_eq_true_eq] at htrue
    simp only [probeCmp, dite_eq_left ha_lt, decide_eq_true_eq]
    exact (P.strictMono.monotone (Fin.mk_le_mk.mpr (by omega))).trans htrue
  obtain ⟨hk0, hkh, htrue, hfalse⟩ := Cslib.Algorithms.Lean.lowerBound_spec
    (fun k ↦ P.probeCmp x (r + k)) hmono
  set k := Cslib.Algorithms.Lean.lowerBound (fun k ↦ P.probeCmp x (r + k)) 0 h
  have hkh' : k ≤ h := by simpa using hkh
  symm
  rw [P.intervalIndex_eq_iff (by omega) (by omega)]
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with hk0_eq | hkpos
    · have hidx : (⟨r + k - 1, by omega⟩ : Fin (m + 1)) = ⟨r - 1, by omega⟩ := by
        ext; dsimp; omega
      rw [hidx]
      exact (P.boundary_le_bucketBoundary_of_lt_offset hu q (k := ⟨r - 1, by omega⟩)
        (by dsimp; omega)).trans hxlo
    · have ht := htrue (k - 1) (Nat.zero_le _) (by omega)
      have hidx_lt : r + (k - 1) < m + 1 := by omega
      simp only [probeCmp, dite_eq_left hidx_lt, decide_eq_true_eq] at ht
      have hidx : (⟨r + k - 1, by omega⟩ : Fin (m + 1)) = ⟨r + (k - 1), hidx_lt⟩ := by
        ext; dsimp; omega
      rwa [hidx]
  · rcases eq_or_lt_of_le hkh' with hkh_eq | hklt
    · have hidx : (⟨r + k, by omega⟩ : Fin (m + 1)) = ⟨r + h, by omega⟩ := by
        ext; dsimp; omega
      rw [hidx]
      exact hxhi.trans_le (P.bucketBoundary_succ_le_boundary hu q)
    · have hf := hfalse k le_rfl hklt
      have hidx_lt : r + k < m + 1 := by omega
      simp only [probeCmp, dite_eq_left hidx_lt, decide_eq_false_iff_not, not_le] at hf
      exact hf

/-- **Exactness of `bucketedSearchQ`**: for every resolution `u ≥ 1` and every real query `x`,
evaluating `bucketedSearchQ P u x` against `probeOracle P x` returns `intervalIndex P x`. -/
theorem eval_bucketedSearchQ {u : ℕ} (hu : 0 < u) (x : ℝ) :
    (P.bucketedSearchQ u x).eval (P.probeOracle x) = P.intervalIndex x := by
  classical
  rw [bucketedSearchQ]
  by_cases hxlo : x < P.lower
  · rw [dite_eq_left hxlo, Cslib.FreeM.eval_pure]
    have h0 := P.boundary_le_iff_lt_intervalIndex x 0
    simp only [Fin.val_zero] at h0
    exact (Nat.eq_zero_of_not_pos fun hp ↦ not_lt.mpr (h0.mpr hp) hxlo).symm
  · rw [dite_eq_right hxlo]
    by_cases hxhi : P.upper ≤ x
    · rw [dite_eq_left hxhi, Cslib.FreeM.eval_pure]
      have hm := (P.boundary_le_iff_lt_intervalIndex x (Fin.last m)).mp hxhi
      have hle := P.intervalIndex_le x
      simp only [Fin.val_last] at hm
      omega
    · rw [dite_eq_right hxhi]
      have hlo : P.lower ≤ x := not_lt.mp hxlo
      have hhi : x < P.upper := not_le.mp hxhi
      have hu_range := P.uniformBucket_mem_Icc hu hlo hhi
      have hq : P.uniformBucket u x - 1 < u := by omega
      dsimp only
      rw [dite_eq_left hq]
      set q : Fin u := ⟨P.uniformBucket u x - 1, hq⟩
      have hxq_lo : P.bucketBoundary u q.castSucc ≤ x :=
        (P.bucketBoundary_le_iff_lt_uniformBucket hu x q.castSucc).mpr (by dsimp [q]; omega)
      have hxq_hi : x < P.bucketBoundary u q.succ := by
        by_contra hge
        have hlt := (P.bucketBoundary_le_iff_lt_uniformBucket hu x q.succ).mp (not_lt.mp hge)
        simp only [q, Fin.val_succ] at hlt
        omega
      have hgen := P.offset_add_lowerBound_eq hu q hxq_lo hxq_hi
      set r := P.bucketOffset u q.castSucc
      have hr_bounds := P.bucketOffset_add_count_le hu q
      by_cases hh0 : P.bucketCount u q = 0
      · rw [ite_eq_left hh0, Cslib.FreeM.eval_pure]
        rw [hh0, Cslib.Algorithms.Lean.lowerBound_of_le _ le_rfl, add_zero] at hgen
        exact hgen
      · rw [ite_eq_right hh0]
        by_cases hh1 : P.bucketCount u q = 1
        · rw [ite_eq_left hh1, Cslib.FreeM.eval_bind]
          have hev1 : (Cslib.Query.ProbeQuery.ask r).eval (P.probeOracle x) = P.probeCmp x r := rfl
          rw [hev1]
          rw [hh1, Cslib.Algorithms.Lean.lowerBound, dite_eq_left (by omega : 0 < 1)] at hgen
          have hmid : (0 + 1) / 2 = 0 := rfl
          rw [hmid, Nat.add_zero] at hgen
          by_cases hcmp : P.probeCmp x r = true
          · rw [ite_eq_left hcmp, Cslib.FreeM.eval_pure]
            simp only [hcmp, ↓reduceIte, Cslib.Algorithms.Lean.lowerBound_of_le _ le_rfl] at hgen
            exact hgen
          · rw [ite_eq_right hcmp, Cslib.FreeM.eval_pure]
            rw [ite_eq_right hcmp, Cslib.Algorithms.Lean.lowerBound_of_le _ le_rfl,
              add_zero] at hgen
            exact hgen
        · rw [ite_eq_right hh1]
          by_cases hh2 : P.bucketCount u q = 2
          · rw [ite_eq_left hh2, Cslib.FreeM.eval_bind]
            have hev2 : (Cslib.Query.ProbeQuery.ask (r + 1)).eval (P.probeOracle x) =
                P.probeCmp x (r + 1) := rfl
            rw [hev2]
            have hr1_lt : r + 1 < m + 1 := by omega
            have hr0_lt : r < m + 1 := by omega
            have hlo_r : P.boundary ⟨r - 1, by omega⟩ ≤ x :=
              (P.boundary_le_bucketBoundary_of_lt_offset hu q (k := ⟨r - 1, by omega⟩)
                (by dsimp; omega)).trans hxq_lo
            have hhi_r2 : x < P.boundary ⟨r + 2, by omega⟩ := by
              have hup := P.bucketBoundary_succ_le_boundary hu q
              have hidx : (⟨r + 2, by omega⟩ : Fin (m + 1)) =
                  ⟨P.bucketOffset u q.castSucc + P.bucketCount u q, by omega⟩ := by
                ext; dsimp; omega
              rw [hidx]
              exact hxq_hi.trans_le hup
            by_cases hc2 : P.probeCmp x (r + 1) = true
            · rw [ite_eq_left hc2, Cslib.FreeM.eval_pure]
              simp only [probeCmp, dite_eq_left hr1_lt, decide_eq_true_eq] at hc2
              exact ((P.intervalIndex_eq_iff (by omega) (by omega) x).mpr ⟨hc2, hhi_r2⟩).symm
            · rw [ite_eq_right hc2, Cslib.FreeM.eval_bind]
              have hev1 : (Cslib.Query.ProbeQuery.ask r).eval (P.probeOracle x) =
                  P.probeCmp x r := rfl
              rw [hev1]
              simp only [probeCmp, dite_eq_left hr1_lt, decide_eq_true_eq, not_le] at hc2
              by_cases hc1 : (!P.probeCmp x r) = true
              · rw [ite_eq_left hc1, Cslib.FreeM.eval_pure]
                simp only [Bool.not_eq_true', probeCmp, dite_eq_left hr0_lt,
                  decide_eq_false_iff_not, not_le] at hc1
                exact ((P.intervalIndex_eq_iff (by omega) (by omega) x).mpr ⟨hlo_r, hc1⟩).symm
              · rw [ite_eq_right hc1, Cslib.FreeM.eval_pure]
                simp only [Bool.not_eq_true', Bool.not_eq_false, probeCmp, dite_eq_left hr0_lt,
                  decide_eq_true_eq] at hc1
                exact ((P.intervalIndex_eq_iff (by omega) (by omega) x).mpr ⟨hc1, hc2⟩).symm
          · rw [ite_eq_right hh2, Cslib.FreeM.eval_bind]
            simp only [probeOracle, Cslib.Query.eval_lowerBoundBy, Cslib.FreeM.eval_pure,
              Cslib.Query.ProbeQuery.eval_ask, Cslib.Query.ProbeQuery.oracleOf_probe]
            exact hgen

/-- Per-bucket threshold-probe query bound: for `x ∈ [b₀, b_m)` falling in bucket `q`,
`bucketedSearchQ` uses `0` probes when `bucketCount = 0`, `1` when `bucketCount = 1`, at most `2`
when `bucketCount = 2`, and at most `Nat.log 2 (bucketCount P u q) + 1` in general. -/
theorem countQueries_bucketedSearchQ_le {u : ℕ} {x : ℝ}
    (hlo : P.lower ≤ x) (hhi : x < P.upper) {q : Fin u}
    (hxq : P.uniformBucket u x = q.val + 1) :
    (P.bucketedSearchQ u x).countQueries (P.probeOracle x) ≤
      if P.bucketCount u q = 0 then 0
      else if P.bucketCount u q = 1 then 1
      else if P.bucketCount u q = 2 then 2
      else Nat.log 2 (P.bucketCount u q) + 1 := by
  classical
  have hnot_lo : ¬(x < P.lower) := not_lt.mpr hlo
  have hnot_hi : ¬(P.upper ≤ x) := not_le.mpr hhi
  have hq_lt : P.uniformBucket u x - 1 < u := by omega
  have hq_eq : (⟨P.uniformBucket u x - 1, hq_lt⟩ : Fin u) = q := by ext; dsimp; omega
  rw [bucketedSearchQ, dite_eq_right hnot_lo, dite_eq_right hnot_hi]
  dsimp only
  rw [dite_eq_left hq_lt, hq_eq]
  by_cases hh0 : P.bucketCount u q = 0
  · simp [hh0]
  · rw [ite_eq_right hh0, ite_eq_right hh0]
    by_cases hh1 : P.bucketCount u q = 1
    · rw [ite_eq_left hh1, ite_eq_left hh1]
      simp only [Cslib.FreeM.countQueries_bind, Cslib.Query.ProbeQuery.ask,
        Cslib.FreeM.countQueries_lift]
      split_ifs <;> simp
    · rw [ite_eq_right hh1, ite_eq_right hh1]
      by_cases hh2 : P.bucketCount u q = 2
      · rw [ite_eq_left hh2, ite_eq_left hh2]
        simp only [Cslib.FreeM.countQueries_bind, Cslib.Query.ProbeQuery.ask,
          Cslib.FreeM.countQueries_lift]
        split_ifs
        · simp
        · simp only [Cslib.FreeM.countQueries_bind, Cslib.FreeM.countQueries_lift]
          split_ifs <;> simp
      · rw [ite_eq_right hh2, ite_eq_right hh2]
        simp only [Cslib.FreeM.countQueries_bind, Cslib.FreeM.countQueries_pure, add_zero]
        have hle := Cslib.Query.countQueries_lowerBoundBy_le (P.probeOracle x)
          (fun k ↦ Cslib.Query.ProbeQuery.ask (P.bucketOffset u q.castSucc + k))
          (c := 1) (lo := 0) (hi := P.bucketCount u q)
          fun _ _ _ ↦ by simp [Cslib.Query.ProbeQuery.ask]
        simpa using hle

end MonotonePartition

/-! ### Expected Per-Query Cost over the Uniform Weak-Composition Ensemble -/

/-- Per-bucket lookup step cost (`1` bucket lookup plus threshold-probe upper bound: `1` for
`h = 0`, `2` for `h = 1`, `3` for `h = 2`, and `1 + log₂ h` for `h ≥ 3`). -/
@[expose] noncomputable def bucketLookupCost (h : ℕ) : ℝ :=
  if h = 0 then 1
  else if h = 1 then 2
  else if h = 2 then 3
  else 1 + Real.logb 2 (h : ℝ)

/-- Uniform average of `bucketLookupCost (f i)` over all weak compositions
`f ∈ Finset.finAntidiagonal u n` of `n` interior endpoints into `u` buckets and all buckets
`i : Fin u`. -/
@[expose] noncomputable def expectedBucketLookupCost (n u : ℕ) : ℝ :=
  (∑ f ∈ Finset.finAntidiagonal u n, ∑ i : Fin u, bucketLookupCost (f i)) /
    ((u * #(Finset.finAntidiagonal u n) : ℕ) : ℝ)

private lemma card_finAntidiagonal_pos {u : ℕ} (hu : 0 < u) (n : ℕ) :
    0 < #(Finset.finAntidiagonal u n) := by
  let i₀ : Fin u := ⟨0, hu⟩
  refine Finset.card_pos.mpr ⟨Function.update 0 i₀ n, ?_⟩
  rw [Finset.mem_finAntidiagonal, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
    Function.update_self]
  have hz : ∑ k ∈ Finset.univ.erase i₀, Function.update (0 : Fin u → ℕ) i₀ n k = 0 :=
    Finset.sum_eq_zero fun k hk ↦ by simp [Finset.ne_of_mem_erase hk]
  omega

private lemma sum_finAntidiagonal_apply_eq {u : ℕ} (i j : Fin u) (n : ℕ) (g : ℕ → ℝ) :
    ∑ f ∈ Finset.finAntidiagonal u n, g (f i) = ∑ f ∈ Finset.finAntidiagonal u n, g (f j) := by
  let σ := Equiv.swap i j
  refine Finset.sum_bij (fun f _ ↦ f ∘ σ) ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_finAntidiagonal] at hf ⊢
    exact (Equiv.sum_comp σ f).trans hf
  · intro f₁ _ f₂ _ hfg
    ext k
    have hk := congr_fun hfg (σ k)
    simpa [σ, Equiv.swap_apply_self] using hk
  · intro h hh
    rw [Finset.mem_finAntidiagonal] at hh
    refine ⟨h ∘ σ, Finset.mem_finAntidiagonal.mpr ((Equiv.sum_comp σ h).trans hh), ?_⟩
    ext k; simp [σ, Equiv.swap_apply_self]
  · intro f _; simp [σ, Equiv.swap_apply_right]

private lemma mul_sum_finAntidiagonal_apply_eq {u : ℕ} (i : Fin u) (n : ℕ) :
    u * ∑ f ∈ Finset.finAntidiagonal u n, f i = n * #(Finset.finAntidiagonal u n) := by
  have hcast :
      (u : ℝ) * ∑ f ∈ Finset.finAntidiagonal u n, (f i : ℝ) =
        (n : ℝ) * (#(Finset.finAntidiagonal u n) : ℝ) := by
    calc (u : ℝ) * ∑ f ∈ Finset.finAntidiagonal u n, (f i : ℝ)
      _ = ∑ j : Fin u, ∑ f ∈ Finset.finAntidiagonal u n, (f i : ℝ) := by simp
      _ = ∑ j : Fin u, ∑ f ∈ Finset.finAntidiagonal u n, (f j : ℝ) :=
          Finset.sum_congr rfl fun j _ ↦ sum_finAntidiagonal_apply_eq i j n (Nat.cast)
      _ = ∑ f ∈ Finset.finAntidiagonal u n, ∑ j : Fin u, (f j : ℝ) := Finset.sum_comm
      _ = ∑ f ∈ Finset.finAntidiagonal u n, (n : ℝ) := by
          refine Finset.sum_congr rfl fun f hf ↦ ?_
          exact_mod_cast Finset.mem_finAntidiagonal.mp hf
      _ = (n : ℝ) * (#(Finset.finAntidiagonal u n) : ℝ) := by simp [mul_comm]
  exact_mod_cast hcast

private lemma sum_finAntidiagonal_filter_le {u : ℕ} (i : Fin u) {n r : ℕ} (hr : r ≤ n) :
    u * ∑ f ∈ Finset.finAntidiagonal u n with r ≤ f i, f i =
      (u * r + (n - r)) * #({f ∈ Finset.finAntidiagonal u n | r ≤ f i}) := by
  have hsub_mem : ∀ f ∈ {f ∈ Finset.finAntidiagonal u n | r ≤ f i},
      Function.update f i (f i - r) ∈ Finset.finAntidiagonal u (n - r) := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_finAntidiagonal] at hf ⊢
    have h1 := Finset.add_sum_erase Finset.univ (Function.update f i (f i - r)) (Finset.mem_univ i)
    have h2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
    have he : ∑ k ∈ Finset.univ.erase i, Function.update f i (f i - r) k =
        ∑ k ∈ Finset.univ.erase i, f k :=
      Finset.sum_congr rfl fun k hk ↦ by simp [Finset.ne_of_mem_erase hk]
    rw [← h1, Function.update_self, he]; omega
  have hsub_inj : ∀ f₁ ∈ {f ∈ Finset.finAntidiagonal u n | r ≤ f i},
      ∀ f₂ ∈ {f ∈ Finset.finAntidiagonal u n | r ≤ f i},
      Function.update f₁ i (f₁ i - r) = Function.update f₂ i (f₂ i - r) → f₁ = f₂ := by
    intro f₁ hf₁ f₂ hf₂ hup
    simp only [Finset.mem_filter] at hf₁ hf₂
    ext k
    by_cases hki : k = i
    · subst hki; have hk := congr_fun hup k; simp only [Function.update_self] at hk; omega
    · have hk := congr_fun hup k; simpa [hki] using hk
  have hsub_surj : ∀ g ∈ Finset.finAntidiagonal u (n - r),
      ∃ f ∈ {f ∈ Finset.finAntidiagonal u n | r ≤ f i},
        Function.update f i (f i - r) = g := by
    intro g hg
    simp only [Finset.mem_finAntidiagonal] at hg
    refine ⟨Function.update g i (g i + r), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_finAntidiagonal, Function.update_self]
      refine ⟨?_, Nat.le_add_left r (g i)⟩
      have h1 := Finset.add_sum_erase Finset.univ (Function.update g i (g i + r))
        (Finset.mem_univ i)
      have h2 := Finset.add_sum_erase Finset.univ g (Finset.mem_univ i)
      have he : ∑ k ∈ Finset.univ.erase i, Function.update g i (g i + r) k =
          ∑ k ∈ Finset.univ.erase i, g k :=
        Finset.sum_congr rfl fun k hk ↦ by simp [Finset.ne_of_mem_erase hk]
      rw [← h1, Function.update_self, he]; omega
    · ext k; by_cases hki : k = i
      · subst hki; simp
      · simp [hki]
  have hcard :
      #({f ∈ Finset.finAntidiagonal u n | r ≤ f i}) = #(Finset.finAntidiagonal u (n - r)) :=
    Finset.card_bij (fun f _ ↦ Function.update f i (f i - r)) hsub_mem hsub_inj
      fun g hg ↦ let ⟨f, hf, hfg⟩ := hsub_surj g hg; ⟨f, hf, hfg⟩
  have hsum : ∑ f ∈ Finset.finAntidiagonal u n with r ≤ f i, f i =
      ∑ g ∈ Finset.finAntidiagonal u (n - r), (r + g i) :=
    Finset.sum_bij (fun f _ ↦ Function.update f i (f i - r)) hsub_mem hsub_inj
      (fun g hg ↦ let ⟨f, hf, hfg⟩ := hsub_surj g hg; ⟨f, hf, hfg⟩)
      fun f hf ↦ by simp only [Finset.mem_filter] at hf; simp only [Function.update_self]; omega
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_add, ← Nat.mul_assoc,
    mul_sum_finAntidiagonal_apply_eq i (n - r), hcard]
  ring

/-- **Constant expected per-query lookup cost**: over the uniform ensemble of all weak compositions
of `n` interior endpoints across `u` uniform buckets (`2 ≤ u`, `n ≤ u`), the expected per-query
lookup cost is at most `3` (`O(1)`, independent of `n` and `u`). -/
theorem expectedBucketLookupCost_le_three {n u : ℕ} (hu : 2 ≤ u) (hle : n ≤ u) :
    expectedBucketLookupCost n u ≤ 3 := by
  have hu_pos : 0 < u := by omega
  let i₀ : Fin u := ⟨0, hu_pos⟩
  have hC_pos : 0 < #(Finset.finAntidiagonal u n) := card_finAntidiagonal_pos hu_pos n
  have hden_pos : (0 : ℝ) < ((u * #(Finset.finAntidiagonal u n) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos hu_pos hC_pos)
  rw [expectedBucketLookupCost, div_le_iff₀ hden_pos]
  have hsym :
      ∑ f ∈ Finset.finAntidiagonal u n, ∑ i : Fin u, bucketLookupCost (f i) =
        (u : ℝ) * ∑ f ∈ Finset.finAntidiagonal u n, bucketLookupCost (f i₀) := by
    rw [Finset.sum_comm]
    calc ∑ i : Fin u, ∑ f ∈ Finset.finAntidiagonal u n, bucketLookupCost (f i)
      _ = ∑ _i : Fin u, ∑ f ∈ Finset.finAntidiagonal u n, bucketLookupCost (f i₀) :=
          Finset.sum_congr rfl fun i _ ↦ sum_finAntidiagonal_apply_eq i i₀ n bucketLookupCost
      _ = (u : ℝ) * ∑ f ∈ Finset.finAntidiagonal u n, bucketLookupCost (f i₀) := by simp
  rw [hsym, Nat.cast_mul]
  suffices h1 : ∑ f ∈ Finset.finAntidiagonal u n, bucketLookupCost (f i₀) ≤
      3 * (#(Finset.finAntidiagonal u n) : ℝ) by
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    nlinarith
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.finAntidiagonal u n)
    (fun f ↦ 3 ≤ f i₀) (fun f ↦ bucketLookupCost (f i₀))
  have hlow : ∑ f ∈ Finset.finAntidiagonal u n with ¬(3 ≤ f i₀), bucketLookupCost (f i₀) ≤
      3 * (#({f ∈ Finset.finAntidiagonal u n | ¬(3 ≤ f i₀)}) : ℝ) := by
    calc ∑ f ∈ Finset.finAntidiagonal u n with ¬(3 ≤ f i₀), bucketLookupCost (f i₀)
      _ ≤ ∑ _f ∈ Finset.finAntidiagonal u n with ¬(3 ≤ _f i₀), (3 : ℝ) := by
          refine Finset.sum_le_sum fun f hf ↦ ?_
          have hlt : f i₀ ≤ 2 := by have := (Finset.mem_filter.mp hf).2; omega
          simp only [bucketLookupCost]
          split_ifs <;> first | omega | norm_num
      _ = 3 * (#({f ∈ Finset.finAntidiagonal u n | ¬(3 ≤ f i₀)}) : ℝ) := by simp [mul_comm]
  have hhigh : ∑ f ∈ Finset.finAntidiagonal u n with 3 ≤ f i₀, bucketLookupCost (f i₀) ≤
      3 * (#({f ∈ Finset.finAntidiagonal u n | 3 ≤ f i₀}) : ℝ) := by
    by_cases hn3 : 3 ≤ n
    · set T := {f ∈ Finset.finAntidiagonal u n | 3 ≤ f i₀}
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hbound_log : ∀ f ∈ T, bucketLookupCost (f i₀) ≤
          3 + ((f i₀ : ℝ) / 4 - 1) / Real.log 2 := by
        intro f hf
        have hge3 : 3 ≤ f i₀ := (Finset.mem_filter.mp hf).2
        have h0 : f i₀ ≠ 0 := by omega
        have h1 : f i₀ ≠ 1 := by omega
        have h2 : f i₀ ≠ 2 := by omega
        simp only [bucketLookupCost, h0, h1, h2, ↓reduceIte]
        have hf_pos : (0 : ℝ) < (f i₀ : ℝ) := Nat.cast_pos.mpr (by omega)
        have h4 : Real.log 4 / Real.log 2 = 2 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
          have hne : Real.log 2 ≠ 0 := hlog2_pos.ne'
          field_simp
          norm_num
        have hsub : Real.logb 2 (f i₀ : ℝ) - 2 = Real.log ((f i₀ : ℝ) / 4) / Real.log 2 := by
          rw [Real.logb, Real.log_div hf_pos.ne' (by norm_num : (4 : ℝ) ≠ 0), sub_div, h4]
        have hlog_le := Real.log_le_sub_one_of_pos (div_pos hf_pos (by norm_num : (0 : ℝ) < 4))
        have hdiv_le : Real.log ((f i₀ : ℝ) / 4) / Real.log 2 ≤ ((f i₀ : ℝ) / 4 - 1) / Real.log 2 :=
          div_le_div_of_nonneg_right hlog_le hlog2_pos.le
        linarith
      have hsum_le := Finset.sum_le_sum hbound_log
      have hmoment := sum_finAntidiagonal_filter_le i₀ hn3
      have hmoment_r : (u : ℝ) * ∑ f ∈ T, (f i₀ : ℝ) =
          ((u : ℝ) * 3 + ((n - 3 : ℕ) : ℝ)) * (#T : ℝ) := by
        have h := congr_arg (Nat.cast (R := ℝ)) hmoment
        simpa [T, Nat.cast_sum, Nat.cast_mul, Nat.cast_add] using h
      have hsum_le_4 : ∑ f ∈ T, (f i₀ : ℝ) ≤ 4 * (#T : ℝ) := by
        have hnu : ((n - 3 : ℕ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : n - 3 ≤ u)
        have hT0 : (0 : ℝ) ≤ (#T : ℝ) := Nat.cast_nonneg _
        have hu_r : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu_pos
        nlinarith
      have hrhs : ∑ f ∈ T, (3 + ((f i₀ : ℝ) / 4 - 1) / Real.log 2) =
          3 * (#T : ℝ) + ((∑ f ∈ T, (f i₀ : ℝ)) / 4 - (#T : ℝ)) / Real.log 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm (#T : ℝ) 3,
          ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
          nsmul_eq_mul, mul_one]
      have hnonpos : ((∑ f ∈ T, (f i₀ : ℝ)) / 4 - (#T : ℝ)) / Real.log 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hlog2_pos.le
      linarith
    · have hemp : {f ∈ Finset.finAntidiagonal u n | 3 ≤ f i₀} = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro f hf
        have hsum : ∑ i : Fin u, f i = n := Finset.mem_finAntidiagonal.mp hf
        have hle_n : f i₀ ≤ n :=
          hsum ▸ Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i₀)
        omega
      simp [hemp]
  have hcard_add :
      (#({f ∈ Finset.finAntidiagonal u n | 3 ≤ f i₀}) : ℝ) +
          (#({f ∈ Finset.finAntidiagonal u n | ¬(3 ≤ f i₀)}) : ℝ) =
        (#(Finset.finAntidiagonal u n) : ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := Finset.finAntidiagonal u n)
      (p := fun f ↦ 3 ≤ f i₀)
  linarith

end CslibFrontier.Algorithms.Lean.Query.BucketedBinning
