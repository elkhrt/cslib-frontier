/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalPapers Contributors
-/
module

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Kronecker

import CslibFrontier.Foundations.LinearAlgebra.Matrix.KroneckerRank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Nullstellensatz

/-!
# Matrix Row–Column Rigidity, Monomial Invariance, and Valiant Non-Rigidity

This module develops entrywise and row/column matrix support counts, row–column rigidity
$R_{\mathbb{F}}^{rc}(A, r)$ alongside Valiant's matrix rigidity `Matrix.rigidity`
($R_{\mathbb{F}}(A, r)$), permutation and monomial matrix invariance, algebraic-closure rigidity
invariance via Hilbert's Nullstellensatz, submatrix minor lower bounds, and Valiant non-rigidity
predicates for families of square matrices.

## Main definitions

* `CslibFrontier.Matrix.supportCard`, `CslibFrontier.Matrix.rowSupportCount`,
  `CslibFrontier.Matrix.colSupportCount`, `CslibFrontier.Matrix.maxRowSupport`,
  `CslibFrontier.Matrix.maxColSupport`, `CslibFrontier.Matrix.maxRowColSupport`: entrywise and
  row/column nonzero support counts.
* `CslibFrontier.Matrix.rowColumnRigidity`: row–column rigidity $R_{\mathbb{F}}^{rc}(A, r)$, the
  least $t \in \mathbb{N}$ such that $\mathrm{rank}(A - Z) \le r$ for some matrix $Z$ with at most
  $t$ nonzero entries in every row and every column.
* `CslibFrontier.Matrix.IsPermMatrix`, `CslibFrontier.Matrix.IsMonomialMatrix`: permutation and
  monomial matrices.
* `CslibFrontier.Matrix.IsValiantRigidSeq`, `CslibFrontier.Matrix.IsNotValiantRigidFamily`,
  `CslibFrontier.Matrix.IsNotAbsolutelyValiantRigidFamily`: Valiant-rigidity of matrix sequences and
  strict versus absolute non-rigidity over `AlgebraicClosure F`.

## Main results

* `CslibFrontier.Matrix.maxRowColSupport_add_le`, `CslibFrontier.Matrix.maxRowColSupport_sub_le`,
  `CslibFrontier.Matrix.maxRowColSupport_mul_le`,
  `CslibFrontier.Matrix.maxRowColSupport_kronecker_le`: subadditivity and submultiplicativity of
  `maxRowColSupport`.
* `CslibFrontier.Matrix.rigidity_eq_sInf_supportCard`, `CslibFrontier.Matrix.rigidity_reindex`,
  `CslibFrontier.Matrix.rigidity_smul_le`, `CslibFrontier.Matrix.rigidity_map_le`,
  `CslibFrontier.Matrix.rigidity_map_eq_of_isAlgClosed`: structural properties and algebraic-closure
  field-extension invariance of `Matrix.rigidity`.
* `CslibFrontier.Matrix.rigidity_le_card_mul_rowColumnRigidity`,
  `CslibFrontier.Matrix.rowColumnRigidity_mul_le`,
  `CslibFrontier.Matrix.rowColumnRigidity_kronecker_le`: comparison with Valiant rigidity and
  submultiplicativity under matrix and Kronecker products.
* `CslibFrontier.Matrix.le_rowColumnRigidity_of_det_submatrix_ne_zero`,
  `CslibFrontier.Matrix.one_le_rowColumnRigidity_of_lt_rank`: rank and nonsingular minor lower
  bounds.
* `CslibFrontier.Matrix.rowColumnRigidity_mul_monomial_left`,
  `CslibFrontier.Matrix.rowColumnRigidity_mul_monomial_right`,
  `CslibFrontier.Matrix.rowColumnRigidity_mul_perm_left`,
  `CslibFrontier.Matrix.rowColumnRigidity_mul_perm_right`: monotonicity under monomial
  multiplication and invariance under permutation multiplication.
* `CslibFrontier.Matrix.IsNotValiantRigidFamily.isNotAbsolutelyValiantRigidFamily`: strict Valiant
  non-rigidity implies absolute Valiant non-rigidity.
-/

public section

namespace CslibFrontier.Matrix

open scoped BigOperators Kronecker _root_.Matrix

/-! ### 1. Matrix support and row/column support counts -/

section Support

/-- Total number of nonzero entries of a matrix `A : Matrix m n R`. -/
noncomputable def supportCard {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : ℕ :=
  (@Finset.filter (m × n) (fun p ↦ A p.1 p.2 ≠ 0) (Classical.decPred _) Finset.univ).card

/-- Rewrites `supportCard A` using any `DecidablePred` instance on `A p.1 p.2 ≠ 0`. -/
theorem supportCard_eq_card_filter {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) [DecidablePred fun p : m × n ↦ A p.1 p.2 ≠ 0] :
    supportCard A = (Finset.univ.filter fun p : m × n ↦ A p.1 p.2 ≠ 0).card := by
  unfold supportCard
  congr 1
  ext p
  simp

/-- `supportCard A` agrees with `_root_.Matrix.diffCount A 0`. -/
theorem supportCard_eq_diffCount_zero {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : supportCard A = _root_.Matrix.diffCount A 0 := by
  classical
  rw [supportCard_eq_card_filter, _root_.Matrix.diffCount_eq_card_filter]
  rfl

/-- `_root_.Matrix.diffCount A B` equals `supportCard (A - B)` over any additive group. -/
theorem diffCount_eq_supportCard_sub {m n R : Type*} [Fintype m] [Fintype n] [AddGroup R]
    (A B : Matrix m n R) : _root_.Matrix.diffCount A B = supportCard (A - B) := by
  classical
  rw [supportCard_eq_card_filter, _root_.Matrix.diffCount_eq_card_filter]
  congr 1
  ext p
  simp [sub_ne_zero]

/-- Number of nonzero entries in row `i` of `A : Matrix m n R`. -/
noncomputable def rowSupportCount {m n R : Type*} [Fintype n] [Zero R]
    (A : Matrix m n R) (i : m) : ℕ :=
  (@Finset.filter n (fun j ↦ A i j ≠ 0) (Classical.decPred _) Finset.univ).card

/-- Rewrites `rowSupportCount A i` using any `DecidablePred` on `A i j ≠ 0`. -/
theorem rowSupportCount_eq_card_filter {m n R : Type*} [Fintype n] [Zero R]
    (A : Matrix m n R) (i : m) [DecidablePred fun j : n ↦ A i j ≠ 0] :
    rowSupportCount A i = (Finset.univ.filter fun j : n ↦ A i j ≠ 0).card := by
  unfold rowSupportCount
  congr 1
  ext j
  simp

/-- Number of nonzero entries in column `j` of `A : Matrix m n R`. -/
noncomputable def colSupportCount {m n R : Type*} [Fintype m] [Zero R]
    (A : Matrix m n R) (j : n) : ℕ :=
  (@Finset.filter m (fun i ↦ A i j ≠ 0) (Classical.decPred _) Finset.univ).card

/-- Rewrites `colSupportCount A j` using any `DecidablePred` on `A i j ≠ 0`. -/
theorem colSupportCount_eq_card_filter {m n R : Type*} [Fintype m] [Zero R]
    (A : Matrix m n R) (j : n) [DecidablePred fun i : m ↦ A i j ≠ 0] :
    colSupportCount A j = (Finset.univ.filter fun i : m ↦ A i j ≠ 0).card := by
  unfold colSupportCount
  congr 1
  ext i
  simp

/-- Maximum number of nonzero entries in any row of `A : Matrix m n R` (`0` if `m` is empty). -/
noncomputable def maxRowSupport {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : ℕ :=
  Finset.univ.sup (rowSupportCount A)

/-- Maximum number of nonzero entries in any column of `A : Matrix m n R` (`0` if `n` is empty). -/
noncomputable def maxColSupport {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : ℕ :=
  Finset.univ.sup (colSupportCount A)

/-- Maximum number of nonzero entries in any row or column of `A : Matrix m n R`. -/
noncomputable def maxRowColSupport {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : ℕ :=
  max (maxRowSupport A) (maxColSupport A)

@[simp]
theorem supportCard_zero {m n R : Type*} [Fintype m] [Fintype n] [Zero R] :
    supportCard (0 : Matrix m n R) = 0 := by
  classical
  simp [supportCard_eq_card_filter]

@[simp]
theorem rowSupportCount_zero {m n R : Type*} [Fintype n] [Zero R] (i : m) :
    rowSupportCount (0 : Matrix m n R) i = 0 := by
  classical
  simp [rowSupportCount_eq_card_filter]

@[simp]
theorem colSupportCount_zero {m n R : Type*} [Fintype m] [Zero R] (j : n) :
    colSupportCount (0 : Matrix m n R) j = 0 := by
  classical
  simp [colSupportCount_eq_card_filter]

@[simp]
theorem maxRowSupport_zero {m n R : Type*} [Fintype m] [Fintype n] [Zero R] :
    maxRowSupport (0 : Matrix m n R) = 0 := by
  simp [maxRowSupport]

@[simp]
theorem maxColSupport_zero {m n R : Type*} [Fintype m] [Fintype n] [Zero R] :
    maxColSupport (0 : Matrix m n R) = 0 := by
  simp [maxColSupport]

@[simp]
theorem maxRowColSupport_zero {m n R : Type*} [Fintype m] [Fintype n] [Zero R] :
    maxRowColSupport (0 : Matrix m n R) = 0 := by
  simp [maxRowColSupport]

/-- Every row support count is at most the column index cardinality. -/
theorem rowSupportCount_le_card {m n R : Type*} [Fintype n] [Zero R]
    (A : Matrix m n R) (i : m) : rowSupportCount A i ≤ Fintype.card n := by
  classical
  rw [rowSupportCount_eq_card_filter]
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- Every column support count is at most the row index cardinality. -/
theorem colSupportCount_le_card {m n R : Type*} [Fintype m] [Zero R]
    (A : Matrix m n R) (j : n) : colSupportCount A j ≤ Fintype.card m := by
  classical
  rw [colSupportCount_eq_card_filter]
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- Every row support count is bounded by `maxRowSupport`. -/
theorem rowSupportCount_le_maxRowSupport {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) (i : m) : rowSupportCount A i ≤ maxRowSupport A :=
  Finset.le_sup (f := rowSupportCount A) (Finset.mem_univ i)

/-- Every column support count is bounded by `maxColSupport`. -/
theorem colSupportCount_le_maxColSupport {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) (j : n) : colSupportCount A j ≤ maxColSupport A :=
  Finset.le_sup (f := colSupportCount A) (Finset.mem_univ j)

/-- Every row support count is bounded by `maxRowColSupport`. -/
theorem rowSupportCount_le_maxRowColSupport {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) (i : m) : rowSupportCount A i ≤ maxRowColSupport A :=
  (rowSupportCount_le_maxRowSupport A i).trans (le_max_left _ _)

/-- Every column support count is bounded by `maxRowColSupport`. -/
theorem colSupportCount_le_maxRowColSupport {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) (j : n) : colSupportCount A j ≤ maxRowColSupport A :=
  (colSupportCount_le_maxColSupport A j).trans (le_max_right _ _)

/-- Characterization of `maxRowColSupport A ≤ t` via row and column support counts. -/
theorem maxRowColSupport_le_iff {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    {A : Matrix m n R} {t : ℕ} :
    maxRowColSupport A ≤ t ↔
      (∀ i : m, rowSupportCount A i ≤ t) ∧ (∀ j : n, colSupportCount A j ≤ t) := by
  simp [maxRowColSupport, maxRowSupport, maxColSupport]

/-- `maxRowColSupport A` is bounded by `max (Fintype.card n) (Fintype.card m)`. -/
theorem maxRowColSupport_le_card {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : maxRowColSupport A ≤ max (Fintype.card n) (Fintype.card m) :=
  maxRowColSupport_le_iff.mpr
    ⟨fun i ↦ (rowSupportCount_le_card A i).trans (le_max_left _ _),
     fun j ↦ (colSupportCount_le_card A j).trans (le_max_right _ _)⟩

/-- A matrix has zero `supportCard` if and only if it is the zero matrix. -/
theorem supportCard_eq_zero_iff {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : supportCard A = 0 ↔ A = 0 := by
  classical
  rw [supportCard_eq_card_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, forall_true_left, not_not, Prod.forall]
  exact ⟨fun h ↦ _root_.Matrix.ext h, fun h i j ↦ by simp [h]⟩

/-- A matrix has zero `maxRowColSupport` if and only if it is the zero matrix. -/
theorem maxRowColSupport_eq_zero_iff {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : maxRowColSupport A = 0 ↔ A = 0 := by
  classical
  rw [← Nat.le_zero, maxRowColSupport_le_iff]
  simp only [Nat.le_zero, rowSupportCount_eq_card_filter, colSupportCount_eq_card_filter,
    Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, forall_true_left, not_not]
  exact ⟨fun ⟨h, _⟩ ↦ _root_.Matrix.ext h,
    fun h ↦ ⟨fun i j ↦ by simp [h], fun j i ↦ by simp [h]⟩⟩

/-- Total nonzero entries of `A` equal the sum of row support counts. -/
theorem supportCard_eq_sum_rowSupportCount {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : supportCard A = ∑ i : m, rowSupportCount A i := by
  classical
  rw [supportCard_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [rowSupportCount_eq_card_filter]
  refine Finset.card_bij (fun p _ ↦ p.2) ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp', hpi⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi ▸ (Finset.mem_filter.mp hp').2⟩
  · intro p₁ hp₁ p₂ hp₂ h
    have h₁ : p₁.1 = i := (Finset.mem_filter.mp hp₁).2
    have h₂ : p₂.1 = i := (Finset.mem_filter.mp hp₂).2
    exact Prod.ext (h₁.trans h₂.symm) h
  · intro j hj
    exact ⟨(i, j),
      Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩, rfl⟩, rfl⟩

/-- Total nonzero entries of `A` are bounded by `Fintype.card m * maxRowColSupport A`. -/
theorem supportCard_le_card_mul_maxRowColSupport {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : supportCard A ≤ Fintype.card m * maxRowColSupport A := by
  calc supportCard A = ∑ i : m, rowSupportCount A i := supportCard_eq_sum_rowSupportCount A
    _ ≤ ∑ _i : m, maxRowColSupport A :=
        Finset.sum_le_sum fun i _ ↦ rowSupportCount_le_maxRowColSupport A i
    _ = Fintype.card m * maxRowColSupport A := by simp

/-- Row support count is subadditive under matrix addition. -/
theorem rowSupportCount_add_le {m n R : Type*} [Fintype n] [AddZeroClass R]
    (A B : Matrix m n R) (i : m) :
    rowSupportCount (A + B) i ≤ rowSupportCount A i + rowSupportCount B i := by
  classical
  simp only [rowSupportCount_eq_card_filter]
  have hsub : (Finset.univ.filter fun j : n ↦ (A + B) i j ≠ 0) ⊆
      (Finset.univ.filter fun j : n ↦ A i j ≠ 0) ∪
        (Finset.univ.filter fun j : n ↦ B i j ≠ 0) := by
    intro j hj
    have hj' : A i j + B i j ≠ 0 := (Finset.mem_filter.mp hj).2
    refine Finset.mem_union.mpr ?_
    by_cases hA : A i j = 0
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hB ↦ hj' (by simp [hA, hB])⟩)
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Column support count is subadditive under matrix addition. -/
theorem colSupportCount_add_le {m n R : Type*} [Fintype m] [AddZeroClass R]
    (A B : Matrix m n R) (j : n) :
    colSupportCount (A + B) j ≤ colSupportCount A j + colSupportCount B j := by
  classical
  simp only [colSupportCount_eq_card_filter]
  have hsub : (Finset.univ.filter fun i : m ↦ (A + B) i j ≠ 0) ⊆
      (Finset.univ.filter fun i : m ↦ A i j ≠ 0) ∪
        (Finset.univ.filter fun i : m ↦ B i j ≠ 0) := by
    intro i hi
    have hi' : A i j + B i j ≠ 0 := (Finset.mem_filter.mp hi).2
    refine Finset.mem_union.mpr ?_
    by_cases hA : A i j = 0
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hB ↦ hi' (by simp [hA, hB])⟩)
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- `maxRowColSupport` is subadditive under matrix addition. -/
theorem maxRowColSupport_add_le {m n R : Type*} [Fintype m] [Fintype n] [AddZeroClass R]
    (A B : Matrix m n R) :
    maxRowColSupport (A + B) ≤ maxRowColSupport A + maxRowColSupport B :=
  maxRowColSupport_le_iff.mpr
    ⟨fun i ↦ (rowSupportCount_add_le A B i).trans
        (Nat.add_le_add (rowSupportCount_le_maxRowColSupport A i)
          (rowSupportCount_le_maxRowColSupport B i)),
     fun j ↦ (colSupportCount_add_le A B j).trans
        (Nat.add_le_add (colSupportCount_le_maxRowColSupport A j)
          (colSupportCount_le_maxRowColSupport B j))⟩

@[simp]
theorem maxRowColSupport_neg {m n R : Type*} [Fintype m] [Fintype n] [AddGroup R]
    (A : Matrix m n R) : maxRowColSupport (-A) = maxRowColSupport A := by
  classical
  have hr : rowSupportCount (-A) = rowSupportCount A := funext fun i ↦ by
    simp [rowSupportCount_eq_card_filter]
  have hc : colSupportCount (-A) = colSupportCount A := funext fun j ↦ by
    simp [colSupportCount_eq_card_filter]
  simp only [maxRowColSupport, maxRowSupport, maxColSupport, hr, hc]

/-- `maxRowColSupport` is subadditive under matrix subtraction. -/
theorem maxRowColSupport_sub_le {m n R : Type*} [Fintype m] [Fintype n] [AddGroup R]
    (A B : Matrix m n R) :
    maxRowColSupport (A - B) ≤ maxRowColSupport A + maxRowColSupport B := by
  rw [sub_eq_add_neg]
  exact (maxRowColSupport_add_le A (-B)).trans (by rw [maxRowColSupport_neg])

/-- Scalar multiplication does not increase `supportCard`. -/
theorem supportCard_smul_le {m n R : Type*} [Fintype m] [Fintype n] [MulZeroClass R]
    (c : R) (A : Matrix m n R) : supportCard (c • A) ≤ supportCard A := by
  classical
  simp only [supportCard_eq_card_filter]
  refine Finset.card_le_card fun p hp ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact right_ne_zero_of_mul (Finset.mem_filter.mp hp).2

/-- Scalar multiplication does not increase `maxRowColSupport`. -/
theorem maxRowColSupport_smul_le {m n R : Type*} [Fintype m] [Fintype n] [MulZeroClass R]
    (c : R) (A : Matrix m n R) : maxRowColSupport (c • A) ≤ maxRowColSupport A := by
  classical
  refine maxRowColSupport_le_iff.mpr ⟨fun i ↦ ?_, fun j ↦ ?_⟩
  · refine (le_trans ?_ (rowSupportCount_le_maxRowColSupport A i))
    simp only [rowSupportCount_eq_card_filter]
    exact Finset.card_le_card fun j hj ↦
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, right_ne_zero_of_mul (Finset.mem_filter.mp hj).2⟩
  · refine (le_trans ?_ (colSupportCount_le_maxRowColSupport A j))
    simp only [colSupportCount_eq_card_filter]
    exact Finset.card_le_card fun i hi ↦
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, right_ne_zero_of_mul (Finset.mem_filter.mp hi).2⟩

/-- `maxRowColSupport` is submultiplicative under matrix multiplication. -/
theorem maxRowColSupport_mul_le {m n p R : Type*} [Fintype m] [Fintype n] [Fintype p]
    [NonUnitalNonAssocSemiring R] (A : Matrix m n R) (B : Matrix n p R) :
    maxRowColSupport (A * B) ≤ maxRowColSupport A * maxRowColSupport B := by
  classical
  refine maxRowColSupport_le_iff.mpr ⟨fun i ↦ ?_, fun k ↦ ?_⟩
  · rw [rowSupportCount_eq_card_filter]
    have hsub : (Finset.univ.filter fun k : p ↦ (A * B) i k ≠ 0) ⊆
        (Finset.univ.filter fun j : n ↦ A i j ≠ 0).biUnion
          (fun j ↦ Finset.univ.filter fun k : p ↦ B j k ≠ 0) := by
      intro k hk
      obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Finset.mem_filter.mp hk).2
      exact Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, left_ne_zero_of_mul hj⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, right_ne_zero_of_mul hj⟩⟩
    calc (Finset.univ.filter fun k : p ↦ (A * B) i k ≠ 0).card
        ≤ ∑ j ∈ Finset.univ.filter (fun j : n ↦ A i j ≠ 0),
            (Finset.univ.filter fun k : p ↦ B j k ≠ 0).card :=
          (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : n ↦ A i j ≠ 0), maxRowColSupport B :=
          Finset.sum_le_sum fun j _ ↦ by
            rw [← rowSupportCount_eq_card_filter]
            exact rowSupportCount_le_maxRowColSupport B j
      _ = rowSupportCount A i * maxRowColSupport B := by
          rw [Finset.sum_const, smul_eq_mul, ← rowSupportCount_eq_card_filter]
      _ ≤ maxRowColSupport A * maxRowColSupport B :=
          Nat.mul_le_mul_right _ (rowSupportCount_le_maxRowColSupport A i)
  · rw [colSupportCount_eq_card_filter]
    have hsub : (Finset.univ.filter fun i : m ↦ (A * B) i k ≠ 0) ⊆
        (Finset.univ.filter fun j : n ↦ B j k ≠ 0).biUnion
          (fun j ↦ Finset.univ.filter fun i : m ↦ A i j ≠ 0) := by
      intro i hi
      obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Finset.mem_filter.mp hi).2
      exact Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, right_ne_zero_of_mul hj⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, left_ne_zero_of_mul hj⟩⟩
    calc (Finset.univ.filter fun i : m ↦ (A * B) i k ≠ 0).card
        ≤ ∑ j ∈ Finset.univ.filter (fun j : n ↦ B j k ≠ 0),
            (Finset.univ.filter fun i : m ↦ A i j ≠ 0).card :=
          (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : n ↦ B j k ≠ 0), maxRowColSupport A :=
          Finset.sum_le_sum fun j _ ↦ by
            rw [← colSupportCount_eq_card_filter]
            exact colSupportCount_le_maxRowColSupport A j
      _ = colSupportCount B k * maxRowColSupport A := by
          rw [Finset.sum_const, smul_eq_mul, ← colSupportCount_eq_card_filter]
      _ ≤ maxRowColSupport B * maxRowColSupport A :=
          Nat.mul_le_mul_right _ (colSupportCount_le_maxRowColSupport B k)
      _ = maxRowColSupport A * maxRowColSupport B := Nat.mul_comm _ _

/-- `maxRowColSupport` is submultiplicative under the Kronecker product. -/
theorem maxRowColSupport_kronecker_le {m n p q R : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q] [MulZeroClass R]
    (A : Matrix m n R) (B : Matrix p q R) :
    maxRowColSupport (A ⊗ₖ B) ≤ maxRowColSupport A * maxRowColSupport B := by
  classical
  refine maxRowColSupport_le_iff.mpr ⟨fun ⟨i, ip⟩ ↦ ?_, fun ⟨j, jq⟩ ↦ ?_⟩
  · rw [rowSupportCount_eq_card_filter]
    have hsub : (Finset.univ.filter fun k : n × q ↦ (A ⊗ₖ B) (i, ip) k ≠ 0) ⊆
        (Finset.univ.filter fun j : n ↦ A i j ≠ 0) ×ˢ
          (Finset.univ.filter fun jq : q ↦ B ip jq ≠ 0) := by
      intro ⟨j, jq⟩ hk
      have hk' : A i j * B ip jq ≠ 0 := (Finset.mem_filter.mp hk).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, left_ne_zero_of_mul hk'⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, right_ne_zero_of_mul hk'⟩⟩
    calc (Finset.univ.filter fun k : n × q ↦ (A ⊗ₖ B) (i, ip) k ≠ 0).card
        ≤ ((Finset.univ.filter fun j : n ↦ A i j ≠ 0) ×ˢ
            (Finset.univ.filter fun jq : q ↦ B ip jq ≠ 0)).card := Finset.card_le_card hsub
      _ = rowSupportCount A i * rowSupportCount B ip := by
          rw [Finset.card_product, ← rowSupportCount_eq_card_filter,
            ← rowSupportCount_eq_card_filter]
      _ ≤ maxRowColSupport A * maxRowColSupport B :=
          Nat.mul_le_mul (rowSupportCount_le_maxRowColSupport A i)
            (rowSupportCount_le_maxRowColSupport B ip)
  · rw [colSupportCount_eq_card_filter]
    have hsub : (Finset.univ.filter fun r : m × p ↦ (A ⊗ₖ B) r (j, jq) ≠ 0) ⊆
        (Finset.univ.filter fun i : m ↦ A i j ≠ 0) ×ˢ
          (Finset.univ.filter fun ip : p ↦ B ip jq ≠ 0) := by
      intro ⟨i, ip⟩ hr
      have hr' : A i j * B ip jq ≠ 0 := (Finset.mem_filter.mp hr).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, left_ne_zero_of_mul hr'⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, right_ne_zero_of_mul hr'⟩⟩
    calc (Finset.univ.filter fun r : m × p ↦ (A ⊗ₖ B) r (j, jq) ≠ 0).card
        ≤ ((Finset.univ.filter fun i : m ↦ A i j ≠ 0) ×ˢ
            (Finset.univ.filter fun ip : p ↦ B ip jq ≠ 0)).card := Finset.card_le_card hsub
      _ = colSupportCount A j * colSupportCount B jq := by
          rw [Finset.card_product, ← colSupportCount_eq_card_filter,
            ← colSupportCount_eq_card_filter]
      _ ≤ maxRowColSupport A * maxRowColSupport B :=
          Nat.mul_le_mul (colSupportCount_le_maxRowColSupport A j)
            (colSupportCount_le_maxRowColSupport B jq)

@[simp]
theorem maxRowColSupport_transpose {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (A : Matrix m n R) : maxRowColSupport Aᵀ = maxRowColSupport A := by
  have hr : rowSupportCount Aᵀ = colSupportCount A := funext fun _ ↦ rfl
  have hc : colSupportCount Aᵀ = rowSupportCount A := funext fun _ ↦ rfl
  simp only [maxRowColSupport, maxRowSupport, maxColSupport, hr, hc, max_comm]

/-- `supportCard` is invariant under row and column reindexing. -/
theorem supportCard_reindex {m n m' n' R : Type*} [Fintype m] [Fintype n] [Fintype m']
    [Fintype n'] [Zero R] (em : m ≃ m') (en : n ≃ n') (A : Matrix m n R) :
    supportCard (_root_.Matrix.reindex em en A) = supportCard A := by
  classical
  simp only [supportCard_eq_card_filter]
  refine Finset.card_bij (fun p _ ↦ (em.symm p.1, en.symm p.2)) ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  · intro _ _ _ _ h
    exact Prod.ext (em.symm.injective (Prod.ext_iff.mp h).1)
      (en.symm.injective (Prod.ext_iff.mp h).2)
  · intro q hq
    refine ⟨(em q.1, en q.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    simpa [_root_.Matrix.reindex_apply] using (Finset.mem_filter.mp hq).2

/-- `maxRowColSupport` is invariant under row and column reindexing. -/
theorem maxRowColSupport_reindex {m n m' n' R : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n'] [Zero R] (em : m ≃ m') (en : n ≃ n') (A : Matrix m n R) :
    maxRowColSupport (_root_.Matrix.reindex em en A) = maxRowColSupport A := by
  classical
  have hr : ∀ i' : m',
      rowSupportCount (_root_.Matrix.reindex em en A) i' = rowSupportCount A (em.symm i') :=
    fun i' ↦ by
      simp only [rowSupportCount_eq_card_filter]
      refine Finset.card_bij (fun j' _ ↦ en.symm j') ?_ ?_ ?_
      · intro j' hj'
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj').2⟩
      · intro _ _ _ _ h
        exact en.symm.injective h
      · intro j hj
        refine ⟨en j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
        simpa using (Finset.mem_filter.mp hj).2
  have hc : ∀ j' : n',
      colSupportCount (_root_.Matrix.reindex em en A) j' = colSupportCount A (en.symm j') :=
    fun j' ↦ by
      simp only [colSupportCount_eq_card_filter]
      refine Finset.card_bij (fun i' _ ↦ em.symm i') ?_ ?_ ?_
      · intro i' hi'
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi').2⟩
      · intro _ _ _ _ h
        exact em.symm.injective h
      · intro i hi
        refine ⟨em i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
        simpa using (Finset.mem_filter.mp hi).2
  refine le_antisymm ?_ ?_
  · refine maxRowColSupport_le_iff.mpr ⟨fun i' ↦ ?_, fun j' ↦ ?_⟩
    · rw [hr]; exact rowSupportCount_le_maxRowColSupport A _
    · rw [hc]; exact colSupportCount_le_maxRowColSupport A _
  · refine maxRowColSupport_le_iff.mpr ⟨fun i ↦ ?_, fun j ↦ ?_⟩
    · have h := rowSupportCount_le_maxRowColSupport (_root_.Matrix.reindex em en A) (em i)
      rwa [hr, Equiv.symm_apply_apply] at h
    · have h := colSupportCount_le_maxRowColSupport (_root_.Matrix.reindex em en A) (en j)
      rwa [hc, Equiv.symm_apply_apply] at h

end Support

/-! ### 2. Valiant rigidity, field extensions, and row–column rigidity -/

section Rigidity

/-- Existence of a perturbation `Z` realizing `A.rigidity r` with `(A - Z).rank ≤ r`. -/
theorem exists_supportCard_eq_rigidity {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    (A : Matrix m n F) (r : ℕ) :
    ∃ Z : Matrix m n F, (A - Z).rank ≤ r ∧ supportCard Z = A.rigidity r := by
  obtain ⟨B, hB, hcard⟩ := _root_.Matrix.exists_rigidity_eq A r
  refine ⟨A - B, by simpa using hB, ?_⟩
  rwa [← diffCount_eq_supportCard_sub]

/-- Upper bound on `A.rigidity r` from a perturbation `Z` with `(A - Z).rank ≤ r`. -/
theorem rigidity_le_supportCard_of_rank_le {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    {A : Matrix m n F} {r : ℕ} {Z : Matrix m n F} (hZ : (A - Z).rank ≤ r) :
    A.rigidity r ≤ supportCard Z := by
  have h := _root_.Matrix.rigidity_le (A := A) (B := A - Z) hZ
  rwa [diffCount_eq_supportCard_sub, sub_sub_cancel] at h

/-- Characterization of `_root_.Matrix.rigidity A r` as the infimum of `supportCard Z` over
perturbations `Z` with `(A - Z).rank ≤ r`. -/
theorem rigidity_eq_sInf_supportCard {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    (A : Matrix m n F) (r : ℕ) :
    A.rigidity r = sInf { k : ℕ | ∃ Z : Matrix m n F, (A - Z).rank ≤ r ∧ supportCard Z = k } := by
  obtain ⟨Z, hZ, hcard⟩ := exists_supportCard_eq_rigidity A r
  refine le_antisymm ?_ ?_
  · exact le_csInf ⟨supportCard Z, Z, hZ, rfl⟩ fun _ ⟨Z', hZ', hk⟩ ↦
      hk ▸ rigidity_le_supportCard_of_rank_le hZ'
  · exact csInf_le ⟨0, fun _ _ ↦ Nat.zero_le _⟩ ⟨Z, hZ, hcard⟩

/-- `_root_.Matrix.rigidity` is invariant under row and column reindexing. -/
theorem rigidity_reindex {m n m' n' F : Type*} [Finite m] [Fintype n] [Finite m'] [Fintype n']
    [Field F] (em : m ≃ m') (en : n ≃ n') (A : Matrix m n F) (r : ℕ) :
    (_root_.Matrix.reindex em en A).rigidity r = A.rigidity r := by
  cases nonempty_fintype m
  cases nonempty_fintype m'
  refine le_antisymm ?_ ?_
  · obtain ⟨Z, hZ, hcard⟩ := exists_supportCard_eq_rigidity A r
    have hrk : (_root_.Matrix.reindex em en A - _root_.Matrix.reindex em en Z).rank ≤ r := by
      have heq : _root_.Matrix.reindex em en A - _root_.Matrix.reindex em en Z =
          (A - Z).submatrix em.symm en.symm := by
        ext i j; simp
      rw [heq, _root_.Matrix.rank_submatrix]
      exact hZ
    exact (rigidity_le_supportCard_of_rank_le hrk).trans (by rw [supportCard_reindex, hcard])
  · obtain ⟨Z', hZ', hcard⟩ := exists_supportCard_eq_rigidity (_root_.Matrix.reindex em en A) r
    have hrk : (A - _root_.Matrix.reindex em.symm en.symm Z').rank ≤ r := by
      have heq : A - _root_.Matrix.reindex em.symm en.symm Z' =
          (_root_.Matrix.reindex em en A - Z').submatrix em en := by
        ext i j; simp
      rw [heq, _root_.Matrix.rank_submatrix]
      exact hZ'
    exact (rigidity_le_supportCard_of_rank_le hrk).trans (by rw [supportCard_reindex, hcard])

/-- Scalar multiplication does not increase `_root_.Matrix.rigidity`. -/
theorem rigidity_smul_le {m n F : Type*} [Finite m] [Fintype n] [Field F]
    (c : F) (A : Matrix m n F) (r : ℕ) : (c • A).rigidity r ≤ A.rigidity r := by
  cases nonempty_fintype m
  obtain ⟨Z, hZ, hcard⟩ := exists_supportCard_eq_rigidity A r
  have hrk : (c • A - c • Z).rank ≤ r := by
    rw [← smul_sub]
    exact (_root_.Matrix.rank_smul_le c (A - Z)).trans hZ
  exact (rigidity_le_supportCard_of_rank_le hrk).trans ((supportCard_smul_le c Z).trans_eq hcard)

/-- Matrix rigidity can only decrease under a field homomorphism. -/
theorem rigidity_map_le {m n F L : Type*} [Finite m] [Fintype n] [Field F] [Field L]
    (φ : F →+* L) (A : Matrix m n F) (r : ℕ) : (A.map φ).rigidity r ≤ A.rigidity r := by
  cases nonempty_fintype m
  classical
  obtain ⟨Z, hZ, hcard⟩ := exists_supportCard_eq_rigidity A r
  have hrk : (A.map φ - Z.map φ).rank ≤ r := by
    have hsub : A.map φ - Z.map φ = (A - Z).map φ := by
      ext i j; simp
    rw [hsub, _root_.Matrix.rank_map_of_field]
    exact hZ
  have hsupp : supportCard (Z.map φ) = supportCard Z := by
    simp [supportCard_eq_card_filter]
  exact (rigidity_le_supportCard_of_rank_le hrk).trans (by rw [hsupp, hcard])

/-- **Algebraic-closure invariance of matrix rigidity**: if `K` is an algebraically closed field
and `φ : K →+* L` is any field homomorphism, then `(A.map φ).rigidity r = A.rigidity r`. -/
theorem rigidity_map_eq_of_isAlgClosed {m n K L : Type*} [Finite m] [Fintype n]
    [Field K] [IsAlgClosed K] [Field L] (φ : K →+* L) (A : Matrix m n K) (r : ℕ) :
    (A.map φ).rigidity r = A.rigidity r := by
  cases nonempty_fintype m
  refine le_antisymm (rigidity_map_le φ A r) ?_
  classical
  obtain ⟨Z_L, hZ_L_rk, hZ_L_card⟩ := exists_supportCard_eq_rigidity (A.map φ) r
  have hUV_L_ex : ∃ (U : Matrix m (Fin r) L) (V : Matrix (Fin r) n L),
      A.map φ - Z_L = U * V := by
    set B := A.map φ - Z_L
    obtain ⟨s, hs, C, D, hCD⟩ : ∃ s, s ≤ r ∧
        ∃ (C : Matrix m (Fin s) L) (D : Matrix (Fin s) n L), B = C * D :=
      ⟨B.rank, hZ_L_rk, B.exists_eq_mul_rank⟩
    refine ⟨_root_.Matrix.of fun i t ↦ if ht : t.1 < s then C i ⟨t.1, ht⟩ else 0,
      _root_.Matrix.of fun t j ↦ if ht : t.1 < s then D ⟨t.1, ht⟩ j else 0, ?_⟩
    ext i j
    rw [hCD, _root_.Matrix.mul_apply, _root_.Matrix.mul_apply]
    let emb : Fin s ↪ Fin r :=
      ⟨fun a ↦ ⟨a.1, lt_of_lt_of_le a.2 hs⟩, fun _ _ h ↦ Fin.ext (Fin.mk.inj h)⟩
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map emb)) (fun t _ ht ↦ by
      have hge : ¬ t.1 < s := fun hlt ↦
        ht (Finset.mem_map.mpr ⟨⟨t.1, hlt⟩, Finset.mem_univ _, rfl⟩)
      simp [hge]), Finset.sum_map]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have ha : (emb a).1 < s := a.2
    simp only [_root_.Matrix.of_apply, dite_eq_left ha]
    rfl
  obtain ⟨U_L, V_L, hUV_L⟩ := hUV_L_ex
  let S_zero : Finset (m × n) := Finset.univ.filter fun ij : m × n ↦ Z_L ij.1 ij.2 = 0
  let σ := (m × Fin r) ⊕ (Fin r × n)
  let poly : m × n → MvPolynomial σ K := fun ij ↦
    (∑ t : Fin r, MvPolynomial.X (Sum.inl (ij.1, t)) * MvPolynomial.X (Sum.inr (t, ij.2))) -
      MvPolynomial.C (A ij.1 ij.2)
  let S : Set (MvPolynomial σ K) := poly '' (S_zero : Set (m × n))
  let algKL : Algebra K L := φ.toAlgebra
  let x_L : σ → L := Sum.elim (fun p ↦ U_L p.1 p.2) (fun q ↦ V_L q.1 q.2)
  have hx_L_zero : ∀ p ∈ S, @MvPolynomial.aeval K L _ _ _ algKL x_L p = 0 := by
    rintro _ ⟨⟨i, j⟩, hij, rfl⟩
    have hZij : Z_L i j = 0 := (Finset.mem_filter.mp hij).2
    have hUVij : (U_L * V_L) i j = φ (A i j) := by
      have h := congrFun (congrFun hUV_L i) j
      simp only [_root_.Matrix.sub_apply, _root_.Matrix.map_apply, hZij, sub_zero] at h
      exact h.symm
    have hev : @MvPolynomial.aeval K L _ _ _ algKL x_L (poly (i, j)) =
        (∑ t : Fin r, U_L i t * V_L t j) - φ (A i j) := by
      simp [poly, x_L, algKL, RingHom.algebraMap_toAlgebra]
    rw [hev, ← _root_.Matrix.mul_apply, hUVij, sub_self]
  have hspan_ne_top : Ideal.span S ≠ ⊤ := by
    intro htop
    have h1_mem : (1 : MvPolynomial σ K) ∈ Ideal.span S := htop ▸ Submodule.mem_top
    rw [Submodule.mem_span_set] at h1_mem
    obtain ⟨c, hc_supp, hc_sum⟩ := h1_mem
    have heval := congrArg (@MvPolynomial.aeval K L _ _ _ algKL x_L) hc_sum
    rw [map_one, Finsupp.sum, map_sum] at heval
    have hzero :
        (∑ p ∈ c.support, (@MvPolynomial.aeval K L _ _ _ algKL x_L) (c p • p)) = 0 := by
      refine Finset.sum_eq_zero fun p hp ↦ ?_
      rw [smul_eq_mul, map_mul, hx_L_zero p (hc_supp (Finset.mem_coe.mpr hp)), mul_zero]
    rw [hzero] at heval
    exact zero_ne_one heval
  have hex_K : ∃ x_K : σ → K, ∀ p ∈ S, MvPolynomial.aeval x_K p = 0 := by
    by_contra hno
    have hzl : MvPolynomial.zeroLocus K (Ideal.span S) = ∅ := by
      ext x_K
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hall
      exact hno ⟨x_K, fun p hp ↦ hall p (Ideal.subset_span hp)⟩
    have hrad : (Ideal.span S).radical = ⊤ := by
      have hve : MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K (Ideal.span S)) =
          (Ideal.span S).radical := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical _
      rw [← hve, hzl, MvPolynomial.vanishingIdeal_empty]
    exact hspan_ne_top ((Ideal.radical_eq_top).mp hrad)
  obtain ⟨x_K, hx_K⟩ := hex_K
  let U_K : Matrix m (Fin r) K := fun i t ↦ x_K (Sum.inl (i, t))
  let V_K : Matrix (Fin r) n K := fun t j ↦ x_K (Sum.inr (t, j))
  let Z_K : Matrix m n K := A - U_K * V_K
  have hZ_K_rk : (A - Z_K).rank ≤ r := by
    rw [show A - Z_K = U_K * V_K from sub_sub_cancel A (U_K * V_K)]
    exact (U_K.rank_mul_le_left V_K).trans (U_K.rank_le_card_width.trans_eq (Fintype.card_fin r))
  have hsupp_sub :
      (Finset.univ.filter fun ij : m × n ↦ Z_K ij.1 ij.2 ≠ 0) ⊆
        (Finset.univ.filter fun ij : m × n ↦ Z_L ij.1 ij.2 ≠ 0) := by
    intro ⟨i, j⟩ hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
    intro hZij
    have hmem : poly (i, j) ∈ S :=
      ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hZij⟩, rfl⟩
    have hev : MvPolynomial.aeval x_K (poly (i, j)) =
        (∑ t : Fin r, U_K i t * V_K t j) - A i j := by
      simp [poly, U_K, V_K]
    rw [hx_K (poly (i, j)) hmem, ← _root_.Matrix.mul_apply, eq_comm, sub_eq_zero] at hev
    exact hij (by simp only [Z_K, _root_.Matrix.sub_apply, hev, sub_self])
  calc
    A.rigidity r ≤ supportCard Z_K := rigidity_le_supportCard_of_rank_le hZ_K_rk
    _ = (Finset.univ.filter fun ij : m × n ↦ Z_K ij.1 ij.2 ≠ 0).card :=
          supportCard_eq_card_filter Z_K
    _ ≤ (Finset.univ.filter fun ij : m × n ↦ Z_L ij.1 ij.2 ≠ 0).card :=
          Finset.card_le_card hsupp_sub
    _ = supportCard Z_L := (supportCard_eq_card_filter Z_L).symm
    _ = (A.map φ).rigidity r := hZ_L_card

/-- **Row–column rigidity**: $R_{\mathbb{F}}^{rc}(A, r)$ is the least `t : ℕ` for which there
exists a matrix `Z` over `F` with `(A - Z).rank ≤ r` and at most `t` nonzero entries in every row
and every column. -/
noncomputable def rowColumnRigidity {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    (A : Matrix m n F) (r : ℕ) : ℕ :=
  sInf { t : ℕ | ∃ Z : Matrix m n F, (A - Z).rank ≤ r ∧ maxRowColSupport Z ≤ t }

/-- Existence of a perturbation `Z` realizing `rowColumnRigidity A r`. -/
theorem exists_maxRowColSupport_le_rowColumnRigidity {m n F : Type*} [Fintype m] [Fintype n]
    [Field F]
    (A : Matrix m n F) (r : ℕ) :
    ∃ Z : Matrix m n F, (A - Z).rank ≤ r ∧ maxRowColSupport Z ≤ rowColumnRigidity A r :=
  Nat.sInf_mem
    (s := { t : ℕ | ∃ Z : Matrix m n F, (A - Z).rank ≤ r ∧ maxRowColSupport Z ≤ t })
    ⟨maxRowColSupport A, A, by simp, le_rfl⟩

/-- Upper bound on `rowColumnRigidity A r` from any matrix `Z` with `(A - Z).rank ≤ r`. -/
theorem rowColumnRigidity_le_of_rank_le {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    {A : Matrix m n F} {r : ℕ} {Z : Matrix m n F} (hZ : (A - Z).rank ≤ r) :
    rowColumnRigidity A r ≤ maxRowColSupport Z :=
  Nat.sInf_le ⟨Z, hZ, le_rfl⟩

/-- `rowColumnRigidity A` is antitone in the target rank `r`. -/
theorem rowColumnRigidity_anti {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    (A : Matrix m n F) {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) :
    rowColumnRigidity A r₂ ≤ rowColumnRigidity A r₁ := by
  obtain ⟨Z, hZ, hsupp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A r₁
  exact (rowColumnRigidity_le_of_rank_le (hZ.trans hr)).trans hsupp

/-- If `A.rank ≤ r`, then `rowColumnRigidity A r = 0`. -/
theorem rowColumnRigidity_eq_zero_of_rank_le {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    {A : Matrix m n F} {r : ℕ} (hA : A.rank ≤ r) : rowColumnRigidity A r = 0 :=
  Nat.eq_zero_of_le_zero
    ((rowColumnRigidity_le_of_rank_le (Z := 0) (by simpa using hA)).trans_eq maxRowColSupport_zero)

/-- `rowColumnRigidity A r = 0` if and only if `A.rank ≤ r`. -/
theorem rowColumnRigidity_eq_zero_iff {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    {A : Matrix m n F} {r : ℕ} : rowColumnRigidity A r = 0 ↔ A.rank ≤ r := by
  refine ⟨fun h ↦ ?_, rowColumnRigidity_eq_zero_of_rank_le⟩
  obtain ⟨Z, hZ, hsupp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A r
  have hZ0 : Z = 0 := (maxRowColSupport_eq_zero_iff Z).mp (Nat.eq_zero_of_le_zero (h ▸ hsupp))
  simpa [hZ0] using hZ

/-- At target rank zero, `rowColumnRigidity A 0` equals `maxRowColSupport A`. -/
theorem rowColumnRigidity_zero {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    (A : Matrix m n F) : rowColumnRigidity A 0 = maxRowColSupport A := by
  refine le_antisymm (rowColumnRigidity_le_of_rank_le (Z := A) (by simp)) ?_
  obtain ⟨Z, hZ, hsupp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A 0
  have hAZ : A = Z := sub_eq_zero.mp (_root_.Matrix.rank_eq_zero_iff.mp (Nat.le_zero.mp hZ))
  simpa [hAZ] using hsupp

/-- Trivial upper bound `rowColumnRigidity A r ≤ max (Fintype.card n) (Fintype.card m)`. -/
theorem rowColumnRigidity_le_card {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    (A : Matrix m n F) (r : ℕ) :
    rowColumnRigidity A r ≤ max (Fintype.card n) (Fintype.card m) :=
  (rowColumnRigidity_le_of_rank_le (Z := A) (by simp)).trans (maxRowColSupport_le_card A)

@[simp]
theorem rowColumnRigidity_transpose {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    (A : Matrix m n F) (r : ℕ) : rowColumnRigidity Aᵀ r = rowColumnRigidity A r := by
  refine le_antisymm ?_ ?_
  · obtain ⟨Z, hZ, hsupp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A r
    have hrk : (Aᵀ - Zᵀ).rank ≤ r := by
      rw [← _root_.Matrix.transpose_sub, _root_.Matrix.rank_transpose]
      exact hZ
    exact (rowColumnRigidity_le_of_rank_le hrk).trans (by rwa [maxRowColSupport_transpose])
  · obtain ⟨Z, hZ, hsupp⟩ := exists_maxRowColSupport_le_rowColumnRigidity Aᵀ r
    have hrk : (A - Zᵀ).rank ≤ r := by
      rw [← _root_.Matrix.transpose_transpose A, ← _root_.Matrix.transpose_sub,
        _root_.Matrix.rank_transpose]
      exact hZ
    exact (rowColumnRigidity_le_of_rank_le hrk).trans (by rwa [maxRowColSupport_transpose])

/-- `rowColumnRigidity` is invariant under row and column reindexing. -/
theorem rowColumnRigidity_reindex {m n m' n' F : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n'] [Field F] (em : m ≃ m') (en : n ≃ n')
    (A : Matrix m n F) (r : ℕ) :
    rowColumnRigidity (_root_.Matrix.reindex em en A) r = rowColumnRigidity A r := by
  refine le_antisymm ?_ ?_
  · obtain ⟨Z, hZ, hsupp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A r
    have hrk : (_root_.Matrix.reindex em en A - _root_.Matrix.reindex em en Z).rank ≤ r := by
      have heq : _root_.Matrix.reindex em en A - _root_.Matrix.reindex em en Z =
          (A - Z).submatrix em.symm en.symm := by
        ext i j; simp
      rw [heq, _root_.Matrix.rank_submatrix]
      exact hZ
    exact (rowColumnRigidity_le_of_rank_le hrk).trans (by rwa [maxRowColSupport_reindex])
  · obtain ⟨Z', hZ', hsupp⟩ :=
      exists_maxRowColSupport_le_rowColumnRigidity (_root_.Matrix.reindex em en A) r
    have hrk : (A - _root_.Matrix.reindex em.symm en.symm Z').rank ≤ r := by
      have heq : A - _root_.Matrix.reindex em.symm en.symm Z' =
          (_root_.Matrix.reindex em en A - Z').submatrix em en := by
        ext i j; simp
      rw [heq, _root_.Matrix.rank_submatrix]
      exact hZ'
    exact (rowColumnRigidity_le_of_rank_le hrk).trans (by rwa [maxRowColSupport_reindex])

/-- Scalar multiplication does not increase `rowColumnRigidity`. -/
theorem rowColumnRigidity_smul_le {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    (c : F) (A : Matrix m n F) (r : ℕ) :
    rowColumnRigidity (c • A) r ≤ rowColumnRigidity A r := by
  obtain ⟨Z, hZ, hsupp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A r
  have hrk : (c • A - c • Z).rank ≤ r := by
    rw [← smul_sub]
    exact (_root_.Matrix.rank_smul_le c (A - Z)).trans hZ
  exact (rowColumnRigidity_le_of_rank_le hrk).trans ((maxRowColSupport_smul_le c Z).trans hsupp)

/-- Row–column rigidity can only decrease under a field homomorphism. -/
theorem rowColumnRigidity_map_le {m n F L : Type*} [Fintype m] [Fintype n] [Field F] [Field L]
    (φ : F →+* L) (A : Matrix m n F) (r : ℕ) :
    rowColumnRigidity (A.map φ) r ≤ rowColumnRigidity A r := by
  classical
  obtain ⟨Z, hZ, hsupp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A r
  have hrk : (A.map φ - Z.map φ).rank ≤ r := by
    have hsub : A.map φ - Z.map φ = (A - Z).map φ := by
      ext i j; simp
    rw [hsub, _root_.Matrix.rank_map_of_field]
    exact hZ
  have hmax : maxRowColSupport (Z.map φ) = maxRowColSupport Z := by
    have hr : rowSupportCount (Z.map φ) = rowSupportCount Z := funext fun i ↦ by
      simp [rowSupportCount_eq_card_filter]
    have hc : colSupportCount (Z.map φ) = colSupportCount Z := funext fun j ↦ by
      simp [colSupportCount_eq_card_filter]
    simp only [maxRowColSupport, maxRowSupport, maxColSupport, hr, hc]
  exact (rowColumnRigidity_le_of_rank_le hrk).trans (hmax.trans_le hsupp)

/-- Comparison between Valiant rigidity and row–column rigidity:
$R_{\mathbb{F}}(A, r) \le |m| \cdot R_{\mathbb{F}}^{rc}(A, r)$. -/
theorem rigidity_le_card_mul_rowColumnRigidity {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    (A : Matrix m n F) (r : ℕ) :
    A.rigidity r ≤ Fintype.card m * rowColumnRigidity A r := by
  obtain ⟨Z, hZ, hsupp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A r
  exact (rigidity_le_supportCard_of_rank_le hZ).trans
    ((supportCard_le_card_mul_maxRowColSupport Z).trans (Nat.mul_le_mul_left _ hsupp))

/-- **Product submultiplicativity of row–column rigidity**:
$R_{\mathbb{F}}^{rc}(A B, r + s) \le R_{\mathbb{F}}^{rc}(A, r) \cdot R_{\mathbb{F}}^{rc}(B, s)$.
-/
theorem rowColumnRigidity_mul_le {m n p F : Type*} [Fintype m] [Fintype n] [Fintype p] [Field F]
    (A : Matrix m n F) (B : Matrix n p F) (r s : ℕ) :
    rowColumnRigidity (A * B) (r + s) ≤ rowColumnRigidity A r * rowColumnRigidity B s := by
  obtain ⟨ZA, hZA_rank, hZA_supp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A r
  obtain ⟨ZB, hZB_rank, hZB_supp⟩ := exists_maxRowColSupport_le_rowColumnRigidity B s
  have hdecomp : A * B - ZA * ZB = (A - ZA) * B + ZA * (B - ZB) := by
    rw [_root_.Matrix.sub_mul, _root_.Matrix.mul_sub, sub_add_sub_cancel]
  have hrk : (A * B - ZA * ZB).rank ≤ r + s := by
    rw [hdecomp]
    exact (_root_.Matrix.rank_add_le _ _).trans
      (Nat.add_le_add ((_root_.Matrix.rank_mul_le_left _ _).trans hZA_rank)
        ((_root_.Matrix.rank_mul_le_right _ _).trans hZB_rank))
  exact (rowColumnRigidity_le_of_rank_le hrk).trans
    ((maxRowColSupport_mul_le ZA ZB).trans (Nat.mul_le_mul hZA_supp hZB_supp))

/-- **Kronecker product bound for row–column rigidity**:
$R_{\mathbb{F}}^{rc}(A \otimes B, r_a |p| + r_b |m|)
\le R_{\mathbb{F}}^{rc}(A, r_a) \cdot R_{\mathbb{F}}^{rc}(B, r_b)$.
-/
theorem rowColumnRigidity_kronecker_le {m n p q F : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Field F]
    (A : Matrix m n F) (B : Matrix p q F) (ra rb : ℕ) :
    rowColumnRigidity (A ⊗ₖ B) (ra * Fintype.card p + rb * Fintype.card m) ≤
      rowColumnRigidity A ra * rowColumnRigidity B rb := by
  obtain ⟨ZA, hZA_rank, hZA_supp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A ra
  obtain ⟨ZB, hZB_rank, hZB_supp⟩ := exists_maxRowColSupport_le_rowColumnRigidity B rb
  have hdecomp : A ⊗ₖ B - ZA ⊗ₖ ZB = (A - ZA) ⊗ₖ B + ZA ⊗ₖ (B - ZB) := by
    ext ⟨i, ip⟩ ⟨j, jp⟩
    simp [sub_mul, mul_sub]
  have hrk : (A ⊗ₖ B - ZA ⊗ₖ ZB).rank ≤ ra * Fintype.card p + rb * Fintype.card m := by
    rw [hdecomp]
    refine (_root_.Matrix.rank_add_le _ _).trans ?_
    rw [_root_.Matrix.rank_kronecker, _root_.Matrix.rank_kronecker]
    refine Nat.add_le_add ?_ ?_
    · exact Nat.mul_le_mul hZA_rank B.rank_le_card_height
    · rw [Nat.mul_comm rb]
      exact Nat.mul_le_mul ZA.rank_le_card_height hZB_rank
  exact (rowColumnRigidity_le_of_rank_le hrk).trans
    ((maxRowColSupport_kronecker_le ZA ZB).trans (Nat.mul_le_mul hZA_supp hZB_supp))

/-- If `r < A.rank`, then `1 ≤ rowColumnRigidity A r`. -/
theorem one_le_rowColumnRigidity_of_lt_rank {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    {A : Matrix m n F} {r : ℕ} (h : r < A.rank) : 1 ≤ rowColumnRigidity A r := by
  by_contra hlt
  have h0 : rowColumnRigidity A r = 0 := by omega
  exact h.not_ge (rowColumnRigidity_eq_zero_iff.mp h0)

/-- **Submatrix minor lower bound for row–column rigidity**: if `(r + 1) * (t + 1) ≤ Fintype.card n`
and there is a row embedding `f : Fin (r + 1) ↪ m` such that `(A.submatrix f g).det ≠ 0` for every
column embedding `g : Fin (r + 1) ↪ n`, then `t + 1 ≤ rowColumnRigidity A r`. -/
theorem le_rowColumnRigidity_of_det_submatrix_ne_zero {m n F : Type*}
    [Fintype m] [Fintype n] [Field F] {A : Matrix m n F} {r t : ℕ}
    (hcard : (r + 1) * (t + 1) ≤ Fintype.card n) (f : Fin (r + 1) ↪ m)
    (hdet : ∀ g : Fin (r + 1) ↪ n, (A.submatrix f g).det ≠ 0) :
    t + 1 ≤ rowColumnRigidity A r := by
  classical
  obtain ⟨Z, hZ_rk, hZ_supp⟩ := exists_maxRowColSupport_le_rowColumnRigidity A r
  by_contra hlt
  have hZt : maxRowColSupport Z ≤ t := hZ_supp.trans (by omega)
  let bad : Finset n :=
    Finset.univ.biUnion fun a : Fin (r + 1) ↦ Finset.univ.filter fun j : n ↦ Z (f a) j ≠ 0
  have hbad_card : bad.card ≤ (r + 1) * t := by
    calc bad.card
        ≤ ∑ a : Fin (r + 1), (Finset.univ.filter fun j : n ↦ Z (f a) j ≠ 0).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _a : Fin (r + 1), t := Finset.sum_le_sum fun a _ ↦ by
          rw [← rowSupportCount_eq_card_filter]
          exact (rowSupportCount_le_maxRowColSupport Z (f a)).trans hZt
      _ = (r + 1) * t := by simp
  let good : Finset n := Finset.univ \ bad
  have hgood_card : r + 1 ≤ good.card := by
    have hbad_le : bad.card ≤ (Finset.univ : Finset n).card :=
      Finset.card_le_card (Finset.subset_univ _)
    have hsdiff : good.card = Fintype.card n - bad.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have hmul : (r + 1) * (t + 1) = (r + 1) * t + (r + 1) := by ring
    omega
  let e := good.equivFin
  let gFun : Fin (r + 1) → n := fun b ↦ (e.symm (Fin.castLE hgood_card b)).1
  have hg_inj : Function.Injective gFun := fun _ _ h ↦
    Fin.castLE_injective hgood_card (e.symm.injective (Subtype.ext h))
  let g : Fin (r + 1) ↪ n := ⟨gFun, hg_inj⟩
  have hZzero : ∀ a b : Fin (r + 1), Z (f a) (g b) = 0 := by
    intro a b
    have hmem : g b ∈ good := (e.symm (Fin.castLE hgood_card b)).2
    have hnot : g b ∉ bad := (Finset.mem_sdiff.mp hmem).2
    by_contra hne
    exact hnot (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩)
  have hsub_eq : (A - Z).submatrix f g = A.submatrix f g := by
    ext a b
    simp [hZzero a b]
  have hrk_sub : ((A - Z).submatrix f g).rank = r + 1 := by
    rw [hsub_eq, _root_.Matrix.rank_of_det_ne_zero (hdet g), Fintype.card_fin]
  have hle_sub : ((A - Z).submatrix f g).rank ≤ r :=
    (_root_.Matrix.rank_submatrix_le (A - Z) f g).trans hZ_rk
  omega

end Rigidity

/-! ### 3. Permutation and monomial matrices -/

section Monomial

/-- A square matrix `P : Matrix n n R` is a **permutation matrix** if there is a permutation
`σ : Equiv.Perm n` such that `P i j = 1` when `i = σ j` and `P i j = 0` otherwise. -/
@[expose]
def IsPermMatrix {n R : Type*} [Zero R] [One R] (P : Matrix n n R) : Prop :=
  ∃ σ : Equiv.Perm n,
    P = _root_.Matrix.of fun i j ↦ @ite _ (i = σ j) (Classical.propDecidable _) (1 : R) 0

/-- A matrix `P : Matrix m n R` is a **monomial matrix** if every row and every column contains at
most one nonzero entry (`maxRowColSupport P ≤ 1`). -/
@[expose]
def IsMonomialMatrix {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    (P : Matrix m n R) : Prop :=
  maxRowColSupport P ≤ 1

/-- The identity matrix is a permutation matrix. -/
theorem isPermMatrix_one {n R : Type*} [DecidableEq n] [Zero R] [One R] :
    IsPermMatrix (1 : Matrix n n R) := by
  refine ⟨Equiv.refl n, ?_⟩
  ext i j
  simp only [_root_.Matrix.one_apply, Equiv.refl_apply, _root_.Matrix.of_apply]
  congr 1

/-- Permutation matrices are closed under matrix multiplication. -/
theorem IsPermMatrix.mul {n R : Type*} [Fintype n] [Semiring R] {P Q : Matrix n n R}
    (hP : IsPermMatrix P) (hQ : IsPermMatrix Q) : IsPermMatrix (P * Q) := by
  classical
  obtain ⟨σ, rfl⟩ := hP
  obtain ⟨τ, rfl⟩ := hQ
  refine ⟨σ * τ, ?_⟩
  ext i k
  simp only [_root_.Matrix.mul_apply, _root_.Matrix.of_apply, Equiv.Perm.coe_mul,
    Function.comp_apply]
  rw [Finset.sum_eq_single (τ k)]
  · simp
    congr 1
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Permutation matrices are closed under transposition. -/
theorem IsPermMatrix.transpose {n R : Type*} [Zero R] [One R] {P : Matrix n n R}
    (hP : IsPermMatrix P) : IsPermMatrix Pᵀ := by
  classical
  obtain ⟨σ, rfl⟩ := hP
  refine ⟨σ.symm, ?_⟩
  ext i j
  simp only [_root_.Matrix.transpose_apply, _root_.Matrix.of_apply]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (σ.symm_apply_eq.mpr h₁).symm h₂
  · exact absurd (σ.symm_apply_eq.mp h₂.symm) h₁
  · rfl

/-- Permutation matrices are closed under Kronecker products. -/
theorem IsPermMatrix.kronecker {m n R : Type*} [MulZeroOneClass R]
    {P : Matrix m m R} {Q : Matrix n n R} (hP : IsPermMatrix P) (hQ : IsPermMatrix Q) :
    IsPermMatrix (P ⊗ₖ Q) := by
  classical
  obtain ⟨σ, rfl⟩ := hP
  obtain ⟨τ, rfl⟩ := hQ
  refine ⟨Equiv.prodCongr σ τ, ?_⟩
  ext ⟨i, ip⟩ ⟨j, jp⟩
  simp only [_root_.Matrix.kronecker_apply, _root_.Matrix.of_apply, Equiv.prodCongr_apply]
  split_ifs <;> simp_all

/-- Every permutation matrix `P` satisfies `P * Pᵀ = 1`. -/
theorem IsPermMatrix.mul_transpose_self {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    {P : Matrix n n R} (hP : IsPermMatrix P) : P * Pᵀ = 1 := by
  classical
  obtain ⟨σ, rfl⟩ := hP
  ext i k
  simp only [_root_.Matrix.mul_apply, _root_.Matrix.of_apply, _root_.Matrix.transpose_apply,
    _root_.Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  · intro j _ hj
    have hij : i ≠ σ j := fun h ↦ hj (σ.injective (by simp [h]))
    simp [hij]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Every permutation matrix `P` satisfies `Pᵀ * P = 1`. -/
theorem IsPermMatrix.transpose_mul_self {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    {P : Matrix n n R} (hP : IsPermMatrix P) : Pᵀ * P = 1 := by
  simpa using hP.transpose.mul_transpose_self

/-- Every diagonal matrix is a monomial matrix. -/
theorem isMonomialMatrix_diagonal {n R : Type*} [Fintype n] [DecidableEq n] [Zero R]
    (d : n → R) : IsMonomialMatrix (_root_.Matrix.diagonal d) := by
  classical
  refine maxRowColSupport_le_iff.mpr ⟨fun i ↦ ?_, fun j ↦ ?_⟩
  · rw [rowSupportCount_eq_card_filter]
    refine (Finset.card_le_card (t := {i}) ?_).trans (by simp)
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    simp only [Finset.mem_singleton]
    by_contra h
    exact hj' (_root_.Matrix.diagonal_apply_ne d (Ne.symm h))
  · rw [colSupportCount_eq_card_filter]
    refine (Finset.card_le_card (t := {j}) ?_).trans (by simp)
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_singleton]
    by_contra h
    exact hi' (_root_.Matrix.diagonal_apply_ne d h)

/-- The identity matrix is a monomial matrix. -/
theorem isMonomialMatrix_one {n R : Type*} [Fintype n] [DecidableEq n] [Zero R] [One R] :
    IsMonomialMatrix (1 : Matrix n n R) := by
  simpa using isMonomialMatrix_diagonal (fun _ : n ↦ (1 : R))

/-- Monomial matrices are closed under matrix multiplication. -/
theorem IsMonomialMatrix.mul {m n p R : Type*} [Fintype m] [Fintype n] [Fintype p]
    [NonUnitalNonAssocSemiring R] {P : Matrix m n R} {Q : Matrix n p R}
    (hP : IsMonomialMatrix P) (hQ : IsMonomialMatrix Q) : IsMonomialMatrix (P * Q) :=
  (maxRowColSupport_mul_le P Q).trans (by simpa using Nat.mul_le_mul hP hQ)

/-- Monomial matrices are closed under transposition. -/
theorem IsMonomialMatrix.transpose {m n R : Type*} [Fintype m] [Fintype n] [Zero R]
    {P : Matrix m n R} (hP : IsMonomialMatrix P) : IsMonomialMatrix Pᵀ := by
  unfold IsMonomialMatrix
  rwa [maxRowColSupport_transpose]

/-- Monomial matrices are closed under Kronecker products. -/
theorem IsMonomialMatrix.kronecker {m n p q R : Type*} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [MulZeroClass R] {P : Matrix m n R} {Q : Matrix p q R}
    (hP : IsMonomialMatrix P) (hQ : IsMonomialMatrix Q) : IsMonomialMatrix (P ⊗ₖ Q) :=
  (maxRowColSupport_kronecker_le P Q).trans (by simpa using Nat.mul_le_mul hP hQ)

/-- Every permutation matrix is a monomial matrix. -/
theorem IsPermMatrix.isMonomialMatrix {n R : Type*} [Fintype n] [Zero R] [One R]
    {P : Matrix n n R} (hP : IsPermMatrix P) : IsMonomialMatrix P := by
  classical
  obtain ⟨σ, rfl⟩ := hP
  refine maxRowColSupport_le_iff.mpr ⟨fun i ↦ ?_, fun j ↦ ?_⟩
  · rw [rowSupportCount_eq_card_filter]
    refine (Finset.card_le_card (t := {σ.symm i}) ?_).trans (by simp)
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    simp only [_root_.Matrix.of_apply] at hj'
    simp only [Finset.mem_singleton]
    by_contra h
    have hij : i ≠ σ j := fun heq ↦ h (σ.injective (by simp [heq]))
    exact hj' (ite_eq_right_iff.mpr fun h' ↦ absurd h' hij)
  · rw [colSupportCount_eq_card_filter]
    refine (Finset.card_le_card (t := {σ j}) ?_).trans (by simp)
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    simp only [_root_.Matrix.of_apply] at hi'
    simp only [Finset.mem_singleton]
    by_contra h
    exact hi' (ite_eq_right_iff.mpr fun h' ↦ absurd h' h)

/-- Every monomial matrix has zero-rank row–column rigidity at most `1`. -/
theorem rowColumnRigidity_zero_le_one_of_isMonomialMatrix {m n F : Type*} [Fintype m] [Fintype n]
    [Field F] {P : Matrix m n F} (hP : IsMonomialMatrix P) :
    rowColumnRigidity P 0 ≤ 1 :=
  (rowColumnRigidity_zero P).trans_le hP

/-- Every nonzero monomial matrix has zero-rank row–column rigidity equal to `1`. -/
theorem rowColumnRigidity_zero_eq_one_of_isMonomialMatrix {m n F : Type*} [Fintype m] [Fintype n]
    [Field F] {P : Matrix m n F} (hP : IsMonomialMatrix P) (hne : P ≠ 0) :
    rowColumnRigidity P 0 = 1 := by
  have hle := rowColumnRigidity_zero_le_one_of_isMonomialMatrix hP
  have hne0 : rowColumnRigidity P 0 ≠ 0 := by
    rw [rowColumnRigidity_zero, ne_eq, maxRowColSupport_eq_zero_iff]
    exact hne
  omega

/-- Left multiplication by a monomial matrix does not increase row–column rigidity. -/
theorem rowColumnRigidity_mul_monomial_left {m n p F : Type*} [Fintype m] [Fintype n] [Fintype p]
    [Field F] {P : Matrix m n F} (hP : IsMonomialMatrix P) (A : Matrix n p F) (r : ℕ) :
    rowColumnRigidity (P * A) r ≤ rowColumnRigidity A r := by
  have h := rowColumnRigidity_mul_le P A 0 r
  rw [zero_add] at h
  exact h.trans
    (by simpa using Nat.mul_le_mul_right _ (rowColumnRigidity_zero_le_one_of_isMonomialMatrix hP))

/-- Right multiplication by a monomial matrix does not increase row–column rigidity. -/
theorem rowColumnRigidity_mul_monomial_right {m n p F : Type*} [Fintype m] [Fintype n] [Fintype p]
    [Field F] (A : Matrix m n F) {P : Matrix n p F} (hP : IsMonomialMatrix P) (r : ℕ) :
    rowColumnRigidity (A * P) r ≤ rowColumnRigidity A r := by
  have h := rowColumnRigidity_mul_le A P r 0
  rw [add_zero] at h
  exact h.trans
    (by simpa using Nat.mul_le_mul_left _ (rowColumnRigidity_zero_le_one_of_isMonomialMatrix hP))

/-- Left multiplication by a permutation matrix preserves row–column rigidity. -/
theorem rowColumnRigidity_mul_perm_left {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    {P : Matrix m m F} (hP : IsPermMatrix P) (A : Matrix m n F) (r : ℕ) :
    rowColumnRigidity (P * A) r = rowColumnRigidity A r := by
  classical
  refine le_antisymm (rowColumnRigidity_mul_monomial_left hP.isMonomialMatrix A r) ?_
  calc rowColumnRigidity A r = rowColumnRigidity ((1 : Matrix m m F) * A) r := by
        rw [_root_.Matrix.one_mul]
    _ = rowColumnRigidity (Pᵀ * (P * A)) r := by
        rw [← _root_.Matrix.mul_assoc, hP.transpose_mul_self]
    _ ≤ rowColumnRigidity (P * A) r :=
        rowColumnRigidity_mul_monomial_left hP.transpose.isMonomialMatrix (P * A) r

/-- Right multiplication by a permutation matrix preserves row–column rigidity. -/
theorem rowColumnRigidity_mul_perm_right {m n F : Type*} [Fintype m] [Fintype n] [Field F]
    (A : Matrix m n F) {P : Matrix n n F} (hP : IsPermMatrix P) (r : ℕ) :
    rowColumnRigidity (A * P) r = rowColumnRigidity A r := by
  classical
  refine le_antisymm (rowColumnRigidity_mul_monomial_right A hP.isMonomialMatrix r) ?_
  calc rowColumnRigidity A r = rowColumnRigidity (A * (1 : Matrix n n F)) r := by
        rw [_root_.Matrix.mul_one]
    _ = rowColumnRigidity ((A * P) * Pᵀ) r := by
        rw [_root_.Matrix.mul_assoc, hP.mul_transpose_self]
    _ ≤ rowColumnRigidity (A * P) r :=
        rowColumnRigidity_mul_monomial_right (A * P) hP.transpose.isMonomialMatrix r

end Monomial

/-! ### 4. Valiant-rigidity and strict versus absolute non-rigidity -/

section ValiantRigid

/-- **Valiant-rigid sequence**: a sequence $A_k \in \mathbb{F}^{d_k \times d_k}$ is
Valiant-rigid over $\mathbb{F}$ if there exists $\varepsilon > 0$ such that for all sufficiently
large $k$, $R_{\mathbb{F}}(A_k, \lfloor d_k / \log\log d_k \rfloor) \ge d_k^{1 + \varepsilon}$.
-/
def IsValiantRigidSeq {F : Type*} [Field F] (d : ℕ → ℕ)
    (A : ∀ k : ℕ, Matrix (Fin (d k)) (Fin (d k)) F) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    (d k : ℝ) ^ (1 + ε) ≤
      ((A k).rigidity ⌊(d k : ℝ) / Real.log (Real.log (d k))⌋₊ : ℝ)

/-- Characterization of `IsValiantRigidSeq`. -/
theorem isValiantRigidSeq_iff {F : Type*} [Field F] (d : ℕ → ℕ)
    (A : ∀ k : ℕ, Matrix (Fin (d k)) (Fin (d k)) F) :
    IsValiantRigidSeq d A ↔
      ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        (d k : ℝ) ^ (1 + ε) ≤
          ((A k).rigidity ⌊(d k : ℝ) / Real.log (Real.log (d k))⌋₊ : ℝ) :=
  Iff.rfl

/-- A family $\mathcal{F}$ of square matrices over $\mathbb{F}$ is **not Valiant-rigid** (strictly
over $\mathbb{F}$) if no sequence of matrices in $\mathcal{F}$ of strictly increasing order is
Valiant-rigid over $\mathbb{F}$. -/
def IsNotValiantRigidFamily {F : Type*} [Field F]
    (𝓕 : Set (Σ n : ℕ, Matrix (Fin n) (Fin n) F)) : Prop :=
  ∀ (d : ℕ → ℕ) (A : ∀ k : ℕ, Matrix (Fin (d k)) (Fin (d k)) F),
    StrictMono d → (∀ k : ℕ, ⟨d k, A k⟩ ∈ 𝓕) → ¬ IsValiantRigidSeq d A

/-- Characterization of `IsNotValiantRigidFamily`. -/
theorem isNotValiantRigidFamily_iff {F : Type*} [Field F]
    (𝓕 : Set (Σ n : ℕ, Matrix (Fin n) (Fin n) F)) :
    IsNotValiantRigidFamily 𝓕 ↔
      ∀ (d : ℕ → ℕ) (A : ∀ k : ℕ, Matrix (Fin (d k)) (Fin (d k)) F),
        StrictMono d → (∀ k : ℕ, ⟨d k, A k⟩ ∈ 𝓕) → ¬ IsValiantRigidSeq d A :=
  Iff.rfl

/-- A family $\mathcal{F}$ of square matrices over $\mathbb{F}$ is **not absolutely Valiant-rigid**
 if it is not Valiant-rigid after base change to `AlgebraicClosure F`.
-/
def IsNotAbsolutelyValiantRigidFamily {F : Type*} [Field F]
    (𝓕 : Set (Σ n : ℕ, Matrix (Fin n) (Fin n) F)) : Prop :=
  ∀ (d : ℕ → ℕ) (A : ∀ k : ℕ, Matrix (Fin (d k)) (Fin (d k)) F),
    StrictMono d → (∀ k : ℕ, ⟨d k, A k⟩ ∈ 𝓕) →
      ¬ IsValiantRigidSeq d fun k ↦ (A k).map (algebraMap F (AlgebraicClosure F))

/-- Characterization of `IsNotAbsolutelyValiantRigidFamily`. -/
theorem isNotAbsolutelyValiantRigidFamily_iff {F : Type*} [Field F]
    (𝓕 : Set (Σ n : ℕ, Matrix (Fin n) (Fin n) F)) :
    IsNotAbsolutelyValiantRigidFamily 𝓕 ↔
      ∀ (d : ℕ → ℕ) (A : ∀ k : ℕ, Matrix (Fin (d k)) (Fin (d k)) F),
        StrictMono d → (∀ k : ℕ, ⟨d k, A k⟩ ∈ 𝓕) →
          ¬ IsValiantRigidSeq d fun k ↦ (A k).map (algebraMap F (AlgebraicClosure F)) :=
  Iff.rfl

/-- Strict Valiant non-rigidity over `F` implies absolute Valiant non-rigidity over
`AlgebraicClosure F`. -/
theorem IsNotValiantRigidFamily.isNotAbsolutelyValiantRigidFamily {F : Type*} [Field F]
    {𝓕 : Set (Σ n : ℕ, Matrix (Fin n) (Fin n) F)}
    (h : IsNotValiantRigidFamily 𝓕) : IsNotAbsolutelyValiantRigidFamily 𝓕 := by
  intro d A hd hmem hrigid
  refine h d A hd hmem ?_
  obtain ⟨ε, hε, K, hK⟩ := hrigid
  refine ⟨ε, hε, K, fun k hk ↦ (hK k hk).trans ?_⟩
  exact Nat.cast_le.mpr (rigidity_map_le (algebraMap F (AlgebraicClosure F)) (A k) _)

end ValiantRigid

end CslibFrontier.Matrix
