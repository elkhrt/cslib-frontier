/-
Copyright (c) 2026 FormalPapers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Assignment.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel

/-!
# Munkres Matrix Reductions, Zero-Line Covers, and Dual Line Adjustments

Formalizes the matrix-reduction and König zero-line-cover characterization of the assignment
problem over an arbitrary finite index type `ι` and linearly ordered
additive commutative group `α`, complementing `CslibFrontier.Algorithms.Lean.Assignment.Basic`
(`IsEpsCompSlack`, `sum_add_sum_le_sum_perm`) and `CslibFrontier.Algorithms.Lean.MaxFlow.Hungarian`.

## Main definitions

* `CslibFrontier.Algorithms.Lean.Assignment.rowMin`, `rowReduce`, `colMin`, `colReduce`,
  `reduceMatrix`: two-stage row and column reductions of `c : ι × ι → α`.
* `CslibFrontier.Algorithms.Lean.Assignment.ZeroLineCover`: pair of row and column `Finset`s
  covering zero entries of a reduced cost table.
* `CslibFrontier.Algorithms.Lean.Assignment.uncoveredPairs`, `minUncovered`, `lineAdjust`:
  uncovered positions, minimum uncovered cost, and Munkres dual line adjustment.

## Main results

* `CslibFrontier.Algorithms.Lean.Assignment.reduceMatrix_nonneg`,
  `exists_reduceMatrix_row_eq_zero`, `exists_reduceMatrix_col_eq_zero`,
  `sum_reduceMatrix_perm_eq`: nonnegativity, row/column zero existence, and uniform cost shift of
  `reduceMatrix`.
* `CslibFrontier.Algorithms.Lean.Assignment.forall_coversZeros_card_le_iff_exists_zero_perm`:
  every zero-line cover has size at least `Fintype.card ι` iff `c` admits a zero-cost permutation.
* `CslibFrontier.Algorithms.Lean.Assignment.isEpsCompSlack_zero_of_nonneg_of_zero_perm`: any
  zero-cost permutation of a nonnegative reduced matrix `c (i, j) - u i - v j` satisfies exact
  `0`-complementary slackness `Cslib.Algorithms.Lean.Assignment.IsEpsCompSlack c 0 σ (-v)` and
  minimizes `∑ i, c (i, τ i)` over all `τ : Equiv.Perm ι`.
* `CslibFrontier.Algorithms.Lean.Assignment.minUncovered_pos`, `lineAdjust_nonneg`,
  `exists_uncovered_lineAdjust_eq_zero`, `sum_lineAdjust_perm_eq`: positivity, nonnegativity
  preservation, zero creation, and uniform cost shift of the Munkres uncovered-minimum step.
-/

public section

namespace CslibFrontier.Algorithms.Lean.Assignment

section ReductionOrder

variable {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]

/-- Minimum entry `min_j c (i, j)` in row `i`. -/
@[expose] def rowMin (c : ι × ι → α) (i : ι) : α :=
  Finset.univ.inf' Finset.univ_nonempty (fun j ↦ c (i, j))

/-- Minimum entry `min_i c (i, j)` in column `j`. -/
@[expose] def colMin (c : ι × ι → α) (j : ι) : α :=
  Finset.univ.inf' Finset.univ_nonempty (fun i ↦ c (i, j))

theorem rowMin_le (c : ι × ι → α) (i j : ι) : rowMin c i ≤ c (i, j) :=
  Finset.inf'_le (fun k ↦ c (i, k)) (Finset.mem_univ j)

theorem colMin_le (c : ι × ι → α) (i j : ι) : colMin c j ≤ c (i, j) :=
  Finset.inf'_le (fun k ↦ c (k, j)) (Finset.mem_univ i)

end ReductionOrder

section ReductionGroup

variable {ι α : Type*} [Fintype ι] [Nonempty ι] [AddCommGroup α] [LinearOrder α]

/-- Row-reduced cost table `(i, j) ↦ c (i, j) - rowMin c i`. -/
@[expose] def rowReduce (c : ι × ι → α) (p : ι × ι) : α :=
  c p - rowMin c p.1

/-- Column-reduced cost table `(i, j) ↦ c (i, j) - colMin c j`. -/
@[expose] def colReduce (c : ι × ι → α) (p : ι × ι) : α :=
  c p - colMin c p.2

/-- Two-stage Munkres reduced cost table `colReduce (rowReduce c)`. -/
@[expose] def reduceMatrix (c : ι × ι → α) : ι × ι → α :=
  colReduce (rowReduce c)

theorem exists_rowReduce_eq_zero (c : ι × ι → α) (i : ι) : ∃ j, rowReduce c (i, j) = 0 := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun k ↦ c (i, k))
  exact ⟨j, sub_eq_zero.mpr hj.symm⟩

theorem exists_colReduce_eq_zero (c : ι × ι → α) (j : ι) : ∃ i, colReduce c (i, j) = 0 := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun k ↦ c (k, j))
  exact ⟨i, sub_eq_zero.mpr hi.symm⟩

/-- Every column of `reduceMatrix c` contains at least one zero entry. -/
theorem exists_reduceMatrix_col_eq_zero (c : ι × ι → α) (j : ι) :
    ∃ i, reduceMatrix c (i, j) = 0 :=
  exists_colReduce_eq_zero (rowReduce c) j

/-- Row and column reductions shift every permutation's cost by the sum of extracted minima. -/
theorem sum_reduceMatrix_perm_eq (c : ι × ι → α) (σ : Equiv.Perm ι) :
    (∑ i, reduceMatrix c (i, σ i)) +
        (∑ i, rowMin c i + ∑ j, colMin (rowReduce c) j) =
      ∑ i, c (i, σ i) := by
  simp only [reduceMatrix, colReduce, rowReduce, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp σ (colMin (rowReduce c))]
  abel

end ReductionGroup

section ReductionOrderedGroup

variable {ι α : Type*} [Fintype ι] [Nonempty ι]
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem rowReduce_nonneg (c : ι × ι → α) (p : ι × ι) : 0 ≤ rowReduce c p :=
  sub_nonneg.mpr (rowMin_le c p.1 p.2)

theorem colReduce_nonneg (c : ι × ι → α) (p : ι × ι) : 0 ≤ colReduce c p :=
  sub_nonneg.mpr (colMin_le c p.1 p.2)

/-- Every entry of `reduceMatrix c` is nonnegative. -/
theorem reduceMatrix_nonneg (c : ι × ι → α) (p : ι × ι) : 0 ≤ reduceMatrix c p :=
  colReduce_nonneg (rowReduce c) p

/-- Every row of `reduceMatrix c` contains at least one zero entry. -/
theorem exists_reduceMatrix_row_eq_zero (c : ι × ι → α) (i : ι) :
    ∃ j, reduceMatrix c (i, j) = 0 := by
  obtain ⟨j, hj⟩ := exists_rowReduce_eq_zero c i
  refine ⟨j, ?_⟩
  have hle : colMin (rowReduce c) j ≤ 0 := hj ▸ colMin_le (rowReduce c) i j
  have hge : 0 ≤ colMin (rowReduce c) j :=
    Finset.le_inf' _ _ fun k _ ↦ rowReduce_nonneg c (k, j)
  have hcol : colMin (rowReduce c) j = 0 := le_antisymm hle hge
  simp [reduceMatrix, colReduce, hj, hcol]

end ReductionOrderedGroup

section ZeroLineCover

variable {ι α : Type*}

/-- A pair of horizontal (row) and vertical (column) covering sets on `ι × ι`. -/
@[ext]
structure ZeroLineCover (ι : Type*) where
  /-- Covered row indices. -/
  rows : Finset ι
  /-- Covered column indices. -/
  cols : Finset ι
  deriving DecidableEq

/-- Total number of covering lines `rows.card + cols.card`. -/
@[expose] def ZeroLineCover.size (L : ZeroLineCover ι) : ℕ :=
  L.rows.card + L.cols.card

/-- `L` covers all zero entries of `c` if `c (i, j) = 0` implies `i ∈ L.rows ∨ j ∈ L.cols`. -/
@[expose] def ZeroLineCover.CoversZeros [Zero α] (L : ZeroLineCover ι) (c : ι × ι → α) : Prop :=
  ∀ i j, c (i, j) = 0 → i ∈ L.rows ∨ j ∈ L.cols

/-- **König–Munkres Zero-Line-Cover Theorem**: every zero-line cover of `c` has size at least
`Fintype.card ι` iff `c` admits a zero-cost permutation `σ`. -/
theorem forall_coversZeros_card_le_iff_exists_zero_perm [Fintype ι] [Zero α] {c : ι × ι → α} :
    (∀ L : ZeroLineCover ι, L.CoversZeros c → Fintype.card ι ≤ L.size) ↔
      ∃ σ : Equiv.Perm ι, ∀ i, c (i, σ i) = 0 := by
  classical
  constructor
  · intro hcover
    let t : ι → Finset ι := fun i ↦ Finset.univ.filter (fun j ↦ c (i, j) = 0)
    have hHall : ∀ S : Finset ι, S.card ≤ (S.biUnion t).card := by
      intro S
      let L : ZeroLineCover ι := ⟨Finset.univ \ S, S.biUnion t⟩
      have hL : L.CoversZeros c := by
        intro i j hij
        by_cases hi : i ∈ S
        · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ j,
          hij⟩⟩)
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
      have hsz := hcover L hL
      have hsdiff : (Finset.univ \ S).card = Fintype.card ι - S.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
      have hSle : S.card ≤ Fintype.card ι := S.card_le_univ
      dsimp only [ZeroLineCover.size, L] at hsz
      omega
    obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj), fun i ↦ ?_⟩
    simpa [t] using hft i
  · rintro ⟨σ, hσ⟩ L hL
    have huniv : (Finset.univ : Finset ι) ⊆ L.rows ∪ L.cols.image σ.symm := by
      intro i _
      rcases hL i (σ i) (hσ i) with hi | hj
      · exact Finset.mem_union_left _ hi
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨σ i, hj, by simp⟩)
    calc
      Fintype.card ι = (Finset.univ : Finset ι).card := Finset.card_univ.symm
      _ ≤ (L.rows ∪ L.cols.image σ.symm).card := Finset.card_le_card huniv
      _ ≤ L.rows.card + (L.cols.image σ.symm).card := Finset.card_union_le _ _
      _ ≤ L.rows.card + L.cols.card := Nat.add_le_add_left Finset.card_image_le _
      _ = L.size := rfl

/-- Bridge to `Cslib.Algorithms.Lean.Assignment.IsEpsCompSlack`: if `u, v` are feasible potentials
(`u i + v j ≤ c (i, j)`) and `σ` selects tight edges (`c (i, σ i) - u i - v (σ i) = 0`), then `σ`
satisfies `0`-complementary slackness with prices `-v` and minimizes `∑ i, c (i, τ i)`. -/
theorem isEpsCompSlack_zero_of_nonneg_of_zero_perm [Fintype ι] [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] {c : ι × ι → α} {u v : ι → α} {σ : Equiv.Perm ι}
    (hfeas : ∀ i j, u i + v j ≤ c (i, j))
    (htight : ∀ i, c (i, σ i) - u i - v (σ i) = 0) :
    Cslib.Algorithms.Lean.Assignment.IsEpsCompSlack c 0 σ (fun j ↦ -v j) ∧
      ∀ τ : Equiv.Perm ι, ∑ i, c (i, σ i) ≤ ∑ i, c (i, τ i) := by
  have hcσ : ∀ i, c (i, σ i) = u i + v (σ i) := fun i ↦
    (sub_eq_iff_eq_add.mp (sub_eq_zero.mp (htight i))).trans (add_comm _ _)
  have hcs : Cslib.Algorithms.Lean.Assignment.IsEpsCompSlack c 0 σ (fun j ↦ -v j) := by
    intro i k
    have hfk := hfeas i k
    rw [hcσ i, add_zero]
    calc
      u i + v (σ i) + -v (σ i) = u i := by abel
      _ = u i + v k + -v k := by abel
      _ ≤ c (i, k) + -v k := add_le_add_left hfk (-v k)
  refine ⟨hcs, fun τ ↦ ?_⟩
  simpa using hcs.sum_le_sum_add τ

/-- Set of index pairs `(i, j)` uncovered by `L`. -/
@[expose] def uncoveredPairs [Fintype ι] [DecidableEq ι] (L : ZeroLineCover ι) : Finset (ι × ι) :=
  (Finset.univ \ L.rows) ×ˢ (Finset.univ \ L.cols)

theorem uncoveredPairs_nonempty_of_size_lt [Fintype ι] [DecidableEq ι] {L : ZeroLineCover ι}
    (h : L.size < Fintype.card ι) : (uncoveredPairs L).Nonempty := by
  have hr : L.rows.card < Fintype.card ι := by dsimp only [ZeroLineCover.size] at h; omega
  have hc : L.cols.card < Fintype.card ι := by dsimp only [ZeroLineCover.size] at h; omega
  have hr_ne : (Finset.univ \ L.rows).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ L.rows),
      Finset.card_univ]
    omega
  have hc_ne : (Finset.univ \ L.cols).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ L.cols),
      Finset.card_univ]
    omega
  exact hr_ne.product hc_ne

/-- Minimum uncovered cost entry when `L.size < Fintype.card ι`. -/
@[expose] def minUncovered [Fintype ι] [DecidableEq ι] [LinearOrder α] (c : ι × ι → α)
    {L : ZeroLineCover ι} (h : L.size < Fintype.card ι) : α :=
  (uncoveredPairs L).inf' (uncoveredPairs_nonempty_of_size_lt h) c

theorem minUncovered_pos [Fintype ι] [DecidableEq ι] [Zero α] [LinearOrder α] {c : ι × ι → α}
    {L : ZeroLineCover ι} (hc : ∀ p, 0 ≤ c p) (hcov : L.CoversZeros c)
    (h : L.size < Fintype.card ι) :
    0 < minUncovered c h := by
  obtain ⟨⟨i, j⟩, hp, hmin⟩ :=
    Finset.exists_mem_eq_inf' (uncoveredPairs_nonempty_of_size_lt h) c
  simp only [uncoveredPairs, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
  have hne : c (i, j) ≠ 0 := fun hz ↦ (hcov i j hz).elim hp.1 hp.2
  unfold minUncovered
  rw [hmin]
  exact lt_of_le_of_ne (hc (i, j)) hne.symm

/-- Munkres uncovered-minimum dual line adjustment: subtract `δ` from uncovered rows and add `δ`
to covered columns. -/
@[expose] def lineAdjust [DecidableEq ι] [AddCommGroup α] (c : ι × ι → α) (L : ZeroLineCover ι)
    (δ : α) (p : ι × ι) : α :=
  c p - (if p.1 ∈ L.rows then 0 else δ) + (if p.2 ∈ L.cols then δ else 0)

theorem lineAdjust_nonneg [DecidableEq ι] [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {c : ι × ι → α} {L : ZeroLineCover ι} {δ : α}
    (hc : ∀ p, 0 ≤ c p) (hδ : 0 ≤ δ)
    (huncov : ∀ i ∉ L.rows, ∀ j ∉ L.cols, δ ≤ c (i, j)) (p : ι × ι) :
    0 ≤ lineAdjust c L δ p := by
  rcases p with ⟨i, j⟩
  unfold lineAdjust
  by_cases hi : i ∈ L.rows <;> by_cases hj : j ∈ L.cols <;>
    simp only [hi, hj, ↓reduceIte, sub_zero, add_zero, sub_add_cancel, sub_nonneg]
  · exact add_nonneg (hc (i, j)) hδ
  · exact hc (i, j)
  · exact hc (i, j)
  · exact huncov i hi j hj

theorem exists_uncovered_lineAdjust_eq_zero [Fintype ι] [DecidableEq ι]
    [AddCommGroup α] [LinearOrder α]
    (c : ι × ι → α) {L : ZeroLineCover ι} (h : L.size < Fintype.card ι) :
    ∃ p ∈ uncoveredPairs L, lineAdjust c L (minUncovered c h) p = 0 := by
  obtain ⟨⟨i, j⟩, hp, hmin⟩ :=
    Finset.exists_mem_eq_inf' (uncoveredPairs_nonempty_of_size_lt h) c
  refine ⟨(i, j), hp, ?_⟩
  simp only [uncoveredPairs, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and] at hp
  unfold minUncovered
  simp [lineAdjust, hp.1, hp.2, hmin]

theorem sum_lineAdjust_perm_eq [Fintype ι] [DecidableEq ι] [AddCommGroup α]
    (c : ι × ι → α) (L : ZeroLineCover ι) (δ : α) (σ : Equiv.Perm ι) :
    (∑ i, lineAdjust c L δ (i, σ i)) =
      (∑ i, c (i, σ i)) - (Fintype.card ι - L.rows.card) • δ + L.cols.card • δ := by
  simp only [lineAdjust, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp σ (fun j ↦ if j ∈ L.cols then δ else 0)]
  have hrows : (∑ i : ι, if i ∈ L.rows then (0 : α) else δ) =
      (Fintype.card ι - L.rows.card) • δ := by
    have heq : (∑ i : ι, if i ∈ L.rows then (0 : α) else δ) =
        ∑ _i ∈ Finset.univ.filter (fun i : ι ↦ i ∉ L.rows), δ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hi : i ∈ L.rows <;> simp [hi]
    have hcard : (Finset.univ.filter (fun i : ι ↦ i ∉ L.rows)).card =
        Fintype.card ι - L.rows.card := by
      have hsdiff : Finset.univ.filter (fun i : ι ↦ i ∉ L.rows) = Finset.univ \ L.rows := by
        ext x; simp
      rw [hsdiff, Finset.card_sdiff_of_subset (Finset.subset_univ L.rows), Finset.card_univ]
    rw [heq, Finset.sum_const, hcard]
  have hcols : (∑ j : ι, if j ∈ L.cols then δ else 0) = L.cols.card • δ := by
    have heq : (∑ j : ι, if j ∈ L.cols then δ else 0) =
        ∑ _j ∈ Finset.univ.filter (fun j : ι ↦ j ∈ L.cols), δ := by
      rw [Finset.sum_filter]
    have hcard : Finset.univ.filter (fun j : ι ↦ j ∈ L.cols) = L.cols := by ext x; simp
    rw [heq, hcard, Finset.sum_const]
  rw [hrows, hcols]

end ZeroLineCover

end CslibFrontier.Algorithms.Lean.Assignment
