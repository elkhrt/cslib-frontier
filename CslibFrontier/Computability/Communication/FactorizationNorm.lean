/-
Copyright (c) 2026 Google DeepMind. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Google DeepMind
-/

module
-- upstream: candidate

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Trace

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Matrix `γ₂` Factorization Norm

This module develops the real matrix `γ₂` factorization norm (also known as the max-norm or
Schur-multiplier factorization norm) under standard Lean axioms. For a finite real matrix
`M : Matrix m n ℝ`, `gamma2Norm M` is defined as the infimum of `rowL2Norm U * colL2Norm V` over
all finite-dimensional factorizations `U * V = M`, where `rowL2Norm U` is the maximum Euclidean
norm of a row of `U` and `colL2Norm V` is the maximum Euclidean norm of a column of `V`.

We establish the basic norm and monotonicity laws (nonnegativity, definiteness, transposition
invariance, submatrix and row/column-duplication monotonicity, homogeneity, the triangle
inequality, and Schur submultiplicativity under the Hadamard product), the Bessel biorthonormal
pairing bound, the Cheung–Hatami–Hosseini–Nikolov–Pitassi–Shirley fourth-moment trace lower bound
via Hölder's inequality, and the exact evaluation of `gamma2Norm` on matrices diagonalized by
unit-modulus orthogonal characters.

## Main definitions

* `CslibFrontier.Matrix.rowL2Norm`: maximum Euclidean `ℓ₂`-norm of the rows of a finite real matrix.
* `CslibFrontier.Matrix.colL2Norm`: maximum Euclidean `ℓ₂`-norm of the columns of a finite real
matrix.
* `CslibFrontier.Matrix.frobeniusNorm`: Frobenius (Hilbert–Schmidt) norm `√(∑ i, ∑ j, M i j ^ 2)`.
* `CslibFrontier.Matrix.gamma2Norm`: the `γ₂` factorization norm of a finite real matrix.

## Main results

* `CslibFrontier.Matrix.gamma2Norm_submatrix_le`: monotonicity under submatrices and row/column
maps.
* `CslibFrontier.Matrix.gamma2Norm_add_le`: triangle inequality for `gamma2Norm`.
* `CslibFrontier.Matrix.gamma2Norm_hadamard_le`: Schur submultiplicativity under `Matrix.hadamard`.
* `CslibFrontier.Matrix.sum_abs_bilinear_le_sqrt_card_mul_gamma2Norm`: Bessel pairing lower bound.
* `CslibFrontier.Matrix.frobeniusNorm_cube_div_le_gamma2Norm`: Hölder fourth-moment trace lower
bound
  `frobeniusNorm M ^ 3 / (Fintype.card n * √((Mᵀ * M * (Mᵀ * M)).trace)) ≤ gamma2Norm M`.
* `CslibFrontier.Matrix.gamma2Norm_eq_sum_abs_of_flat_orthogonal`: exact `ℓ₁` spectral formula for
  matrices expanded in unit-modulus pairwise orthogonal vectors.
-/

public section

open Finset
open scoped BigOperators Matrix NNReal

namespace CslibFrontier.Matrix

section RowColFrobenius

variable {m n k m' n' : Type*}

/-- Maximum Euclidean `ℓ₂`-norm of the rows of a finite real matrix `U`, defaulting to `0` when
`m` is empty. -/
noncomputable def rowL2Norm [Fintype m] [Fintype k] (U : Matrix m k ℝ) : ℝ :=
  (((Finset.univ : Finset m).sup (fun i ↦ Real.toNNReal √(∑ r : k, U i r ^ 2)) : ℝ≥0) : ℝ)

/-- Maximum Euclidean `ℓ₂`-norm of the columns of a finite real matrix `V`, defaulting to `0` when
`n` is empty. -/
noncomputable def colL2Norm [Fintype k] [Fintype n] (V : Matrix k n ℝ) : ℝ :=
  rowL2Norm Vᵀ

/-- Frobenius (Hilbert–Schmidt) norm `√(∑ i, ∑ j, M i j ^ 2)` of a finite real matrix `M`. -/
noncomputable def frobeniusNorm [Fintype m] [Fintype n] (M : Matrix m n ℝ) : ℝ :=
  √(∑ i : m, ∑ j : n, M i j ^ 2)

/-- The maximum row `ℓ₂`-norm is nonnegative. -/
theorem rowL2Norm_nonneg [Fintype m] [Fintype k] (U : Matrix m k ℝ) : 0 ≤ rowL2Norm U := by
  exact NNReal.coe_nonneg _

/-- The maximum column `ℓ₂`-norm is nonnegative. -/
theorem colL2Norm_nonneg [Fintype k] [Fintype n] (V : Matrix k n ℝ) : 0 ≤ colL2Norm V :=
  rowL2Norm_nonneg Vᵀ

/-- The maximum column `ℓ₂`-norm of a transpose equals the maximum row `ℓ₂`-norm. -/
theorem colL2Norm_transpose [Fintype m] [Fintype k] (U : Matrix m k ℝ) :
    colL2Norm Uᵀ = rowL2Norm U := by rfl

/-- The maximum row `ℓ₂`-norm of a transpose equals the maximum column `ℓ₂`-norm. -/
theorem rowL2Norm_transpose [Fintype k] [Fintype n] (V : Matrix k n ℝ) :
    rowL2Norm Vᵀ = colL2Norm V := by rfl

/-- Every row of `U` has Euclidean norm at most `rowL2Norm U`. -/
theorem sqrt_sum_row_sq_le_rowL2Norm [Fintype m] [Fintype k] (U : Matrix m k ℝ) (i : m) :
    √(∑ r : k, U i r ^ 2) ≤ rowL2Norm U := by
  have hle : Real.toNNReal √(∑ r : k, U i r ^ 2) ≤
      (Finset.univ : Finset m).sup (fun i ↦ Real.toNNReal √(∑ r : k, U i r ^ 2)) :=
    Finset.le_sup (f := fun i ↦ Real.toNNReal √(∑ r : k, U i r ^ 2)) (Finset.mem_univ i)
  have hcoe : (Real.toNNReal √(∑ r : k, U i r ^ 2) : ℝ) ≤ rowL2Norm U :=
    NNReal.coe_le_coe.mpr hle
  rwa [Real.coe_toNNReal _ (Real.sqrt_nonneg _)] at hcoe

/-- Every row of `U` has squared Euclidean norm at most `rowL2Norm U ^ 2`. -/
theorem sum_row_sq_le_rowL2Norm_sq [Fintype m] [Fintype k] (U : Matrix m k ℝ) (i : m) :
    ∑ r : k, U i r ^ 2 ≤ rowL2Norm U ^ 2 := by
  have hnn : 0 ≤ ∑ r : k, U i r ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  calc ∑ r : k, U i r ^ 2 = √(∑ r : k, U i r ^ 2) ^ 2 := (Real.sq_sqrt hnn).symm
    _ ≤ rowL2Norm U ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_sum_row_sq_le_rowL2Norm U i) 2

/-- Every column of `V` has Euclidean norm at most `colL2Norm V`. -/
theorem sqrt_sum_col_sq_le_colL2Norm [Fintype k] [Fintype n] (V : Matrix k n ℝ) (j : n) :
    √(∑ r : k, V r j ^ 2) ≤ colL2Norm V :=
  sqrt_sum_row_sq_le_rowL2Norm Vᵀ j

/-- Every column of `V` has squared Euclidean norm at most `colL2Norm V ^ 2`. -/
theorem sum_col_sq_le_colL2Norm_sq [Fintype k] [Fintype n] (V : Matrix k n ℝ) (j : n) :
    ∑ r : k, V r j ^ 2 ≤ colL2Norm V ^ 2 :=
  sum_row_sq_le_rowL2Norm_sq Vᵀ j

/-- `rowL2Norm U ≤ c` follows from a nonnegative uniform bound `c` on all row norms. -/
theorem rowL2Norm_le [Fintype m] [Fintype k] {U : Matrix m k ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : m, √(∑ r : k, U i r ^ 2) ≤ c) : rowL2Norm U ≤ c := by
  have hsup : (Finset.univ : Finset m).sup (fun i ↦ Real.toNNReal √(∑ r : k, U i r ^ 2)) ≤
      Real.toNNReal c :=
    Finset.sup_le (fun i _ ↦ Real.toNNReal_le_toNNReal (h i))
  have hcoe : rowL2Norm U ≤ (Real.toNNReal c : ℝ) := NNReal.coe_le_coe.mpr hsup
  rwa [Real.coe_toNNReal c hc] at hcoe

/-- `rowL2Norm U ≤ c` follows from bounding all squared row sums by `c ^ 2` for `c ≥ 0`. -/
theorem rowL2Norm_le_of_sq [Fintype m] [Fintype k] {U : Matrix m k ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : m, ∑ r : k, U i r ^ 2 ≤ c ^ 2) : rowL2Norm U ≤ c :=
  rowL2Norm_le hc (fun i ↦ Real.sqrt_le_iff.mpr ⟨hc, h i⟩)

/-- `colL2Norm V ≤ c` follows from a nonnegative uniform bound `c` on all column norms. -/
theorem colL2Norm_le [Fintype k] [Fintype n] {V : Matrix k n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j : n, √(∑ r : k, V r j ^ 2) ≤ c) : colL2Norm V ≤ c :=
  rowL2Norm_le hc h

/-- `colL2Norm V ≤ c` follows from bounding all squared column sums by `c ^ 2` for `c ≥ 0`. -/
theorem colL2Norm_le_of_sq [Fintype k] [Fintype n] {V : Matrix k n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j : n, ∑ r : k, V r j ^ 2 ≤ c ^ 2) : colL2Norm V ≤ c :=
  rowL2Norm_le_of_sq hc h

/-- Reindexing columns by an equivalence preserves `rowL2Norm`. -/
theorem rowL2Norm_submatrix_equiv [Fintype m] [Fintype k] {k' : Type*} [Fintype k']
    (U : Matrix m k ℝ) (e : k' ≃ k) :
    rowL2Norm (U.submatrix id e) = rowL2Norm U := by
  unfold rowL2Norm
  congr 1
  refine Finset.sup_congr rfl (fun i _ ↦ ?_)
  have heq : ∑ r : k', U i (e r) ^ 2 = ∑ r : k, U i r ^ 2 :=
    Equiv.sum_comp e (fun r ↦ U i r ^ 2)
  exact congr_arg (fun x ↦ Real.toNNReal √x) heq

/-- Reindexing rows by an equivalence preserves `colL2Norm`. -/
theorem colL2Norm_submatrix_equiv [Fintype k] [Fintype n] {k' : Type*} [Fintype k']
    (V : Matrix k n ℝ) (e : k' ≃ k) :
    colL2Norm (V.submatrix e id) = colL2Norm V :=
  rowL2Norm_submatrix_equiv Vᵀ e

/-- Pulling back rows along any map does not increase `rowL2Norm`. -/
theorem rowL2Norm_submatrix_left_le [Fintype m] [Fintype m'] [Fintype k]
    (U : Matrix m k ℝ) (f : m' → m) :
    rowL2Norm (U.submatrix f id) ≤ rowL2Norm U :=
  rowL2Norm_le (rowL2Norm_nonneg U) (fun i' ↦ sqrt_sum_row_sq_le_rowL2Norm U (f i'))

/-- Pulling back columns along any map does not increase `colL2Norm`. -/
theorem colL2Norm_submatrix_right_le [Fintype k] [Fintype n] [Fintype n']
    (V : Matrix k n ℝ) (g : n' → n) :
    colL2Norm (V.submatrix id g) ≤ colL2Norm V :=
  rowL2Norm_submatrix_left_le Vᵀ g

/-- Scaling a matrix by `c : ℝ` scales `rowL2Norm` by `|c|`. -/
theorem rowL2Norm_smul [Fintype m] [Fintype k] (c : ℝ) (U : Matrix m k ℝ) :
    rowL2Norm (c • U) = |c| * rowL2Norm U := by
  apply le_antisymm
  · refine rowL2Norm_le_of_sq (mul_nonneg (abs_nonneg c) (rowL2Norm_nonneg U)) (fun i ↦ ?_)
    have hsum : ∑ r : k, (c * U i r) ^ 2 = c ^ 2 * ∑ r : k, U i r ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ ↦ by ring)
    simp only [_root_.Matrix.smul_apply, smul_eq_mul]
    rw [hsum, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left (sum_row_sq_le_rowL2Norm_sq U i) (sq_nonneg c)
  · by_cases hc : c = 0
    · simp [hc, rowL2Norm_nonneg]
    · have hpos : 0 < |c| := abs_pos.mpr hc
      rw [← le_div_iff₀' hpos]
      refine rowL2Norm_le (div_nonneg (rowL2Norm_nonneg _) hpos.le) (fun i ↦ ?_)
      rw [le_div_iff₀' hpos]
      have hrow : |c| * √(∑ r : k, U i r ^ 2) = √(∑ r : k, (c • U) i r ^ 2) := by
        rw [← Real.sqrt_sq_eq_abs c,
          ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun r _ ↦ ?_)
        simp only [_root_.Matrix.smul_apply, smul_eq_mul]
        ring
      rw [hrow]
      exact sqrt_sum_row_sq_le_rowL2Norm (c • U) i

/-- Scaling a matrix by `c : ℝ` scales `colL2Norm` by `|c|`. -/
theorem colL2Norm_smul [Fintype k] [Fintype n] (c : ℝ) (V : Matrix k n ℝ) :
    colL2Norm (c • V) = |c| * colL2Norm V := by
  simpa [colL2Norm] using rowL2Norm_smul c Vᵀ

/-- The row `ℓ₂`-norm of the zero matrix is `0`. -/
@[simp]
theorem rowL2Norm_zero [Fintype m] [Fintype k] : rowL2Norm (0 : Matrix m k ℝ) = 0 := by
  apply le_antisymm _ (rowL2Norm_nonneg _)
  exact rowL2Norm_le_of_sq le_rfl (fun _ ↦ by simp)

/-- The column `ℓ₂`-norm of the zero matrix is `0`. -/
@[simp]
theorem colL2Norm_zero [Fintype k] [Fintype n] : colL2Norm (0 : Matrix k n ℝ) = 0 :=
  rowL2Norm_zero

/-- The row `ℓ₂`-norm of an identity matrix is at most `1`. -/
theorem rowL2Norm_one_le [Fintype m] [DecidableEq m] : rowL2Norm (1 : Matrix m m ℝ) ≤ 1 := by
  refine rowL2Norm_le_of_sq zero_le_one (fun i ↦ ?_)
  simp [_root_.Matrix.one_apply]

/-- The column `ℓ₂`-norm of an identity matrix is at most `1`. -/
theorem colL2Norm_one_le [Fintype m] [DecidableEq m] : colL2Norm (1 : Matrix m m ℝ) ≤ 1 := by
  change rowL2Norm (1 : Matrix m m ℝ)ᵀ ≤ 1
  rw [_root_.Matrix.transpose_one]
  exact rowL2Norm_one_le

/-- The Frobenius norm is nonnegative. -/
theorem frobeniusNorm_nonneg [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    0 ≤ frobeniusNorm M :=
  Real.sqrt_nonneg _

/-- Squaring `frobeniusNorm M` recovers the sum of squared entries. -/
theorem sq_frobeniusNorm [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    frobeniusNorm M ^ 2 = ∑ i : m, ∑ j : n, M i j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- The squared Frobenius norm equals `trace (Mᵀ * M)`. -/
theorem sq_frobeniusNorm_eq_trace [Fintype m] [Fintype n] (M : Matrix m n ℝ) :
    frobeniusNorm M ^ 2 = (Mᵀ * M).trace := by
  rw [sq_frobeniusNorm, _root_.Matrix.trace, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ ↦ Finset.sum_congr rfl (fun i _ ↦ ?_))
  simp [sq]

/-- The Frobenius norm vanishes if and only if the matrix is zero. -/
@[simp]
theorem frobeniusNorm_eq_zero [Fintype m] [Fintype n] {M : Matrix m n ℝ} :
    frobeniusNorm M = 0 ↔ M = 0 := by
  constructor
  · intro h
    have hsq : ∑ i : m, ∑ j : n, M i j ^ 2 = 0 := by
      rw [← sq_frobeniusNorm, h, zero_pow two_ne_zero]
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (M i j))).mp hsq
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg (M i j))).mp (h0 i (Finset.mem_univ i))
    exact sq_eq_zero_iff.mp (hi j (Finset.mem_univ j))
  · rintro rfl
    simp [frobeniusNorm]

/-- The Frobenius norm is bounded by `√(card m) * rowL2Norm U`. -/
theorem frobeniusNorm_le_sqrt_card_mul_rowL2Norm [Fintype m] [Fintype k] (U : Matrix m k ℝ) :
    frobeniusNorm U ≤ √(Fintype.card m : ℝ) * rowL2Norm U := by
  rw [frobeniusNorm, Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (rowL2Norm_nonneg U), ?_⟩
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc ∑ i : m, ∑ r : k, U i r ^ 2
      ≤ ∑ _i : m, rowL2Norm U ^ 2 :=
        Finset.sum_le_sum (fun i _ ↦ sum_row_sq_le_rowL2Norm_sq U i)
    _ = (Fintype.card m : ℝ) * rowL2Norm U ^ 2 := by simp

/-- The Frobenius norm is bounded by `√(card n) * colL2Norm V`. -/
theorem frobeniusNorm_le_sqrt_card_mul_colL2Norm [Fintype k] [Fintype n] (V : Matrix k n ℝ) :
    frobeniusNorm V ≤ √(Fintype.card n : ℝ) * colL2Norm V := by
  have htr : frobeniusNorm V = frobeniusNorm Vᵀ := by
    simp only [frobeniusNorm]
    rw [Finset.sum_comm]
    rfl
  rw [htr]
  exact frobeniusNorm_le_sqrt_card_mul_rowL2Norm Vᵀ

/-- Cauchy–Schwarz bound on every entry of a matrix product `U * V` in terms of row and column
`ℓ₂`-norms. -/
theorem abs_mul_apply_le_rowL2Norm_mul_colL2Norm [Fintype m] [Fintype k] [Fintype n]
    (U : Matrix m k ℝ) (V : Matrix k n ℝ) (i : m) (j : n) :
    |(U * V) i j| ≤ rowL2Norm U * colL2Norm V := by
  have hcs : (∑ r : k, U i r * V r j) ^ 2 ≤
      (∑ r : k, U i r ^ 2) * (∑ r : k, V r j ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun r ↦ U i r) (fun r ↦ V r j)
  have hle : (∑ r : k, U i r * V r j) ^ 2 ≤ (rowL2Norm U * colL2Norm V) ^ 2 := by
    rw [mul_pow]
    exact hcs.trans (mul_le_mul (sum_row_sq_le_rowL2Norm_sq U i)
      (sum_col_sq_le_colL2Norm_sq V j) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      (sq_nonneg _))
  rw [_root_.Matrix.mul_apply, abs_le]
  exact abs_le_of_sq_le_sq' hle (mul_nonneg (rowL2Norm_nonneg U) (colL2Norm_nonneg V))

end RowColFrobenius

section Gamma2Basic

variable {m n m' n' : Type*} [Fintype m] [Fintype n]

private def factorizationCosts (M : Matrix m n ℝ) : Set ℝ :=
  { c : ℝ | ∃ (d : ℕ) (U : Matrix m (Fin d) ℝ) (V : Matrix (Fin d) n ℝ),
      U * V = M ∧ rowL2Norm U * colL2Norm V = c }

private theorem factorizationCosts_bddBelow (M : Matrix m n ℝ) :
    BddBelow (factorizationCosts M) := by
  refine ⟨0, ?_⟩
  rintro c ⟨d, U, V, -, rfl⟩
  exact mul_nonneg (rowL2Norm_nonneg U) (colL2Norm_nonneg V)

private theorem mem_factorizationCosts_of_fintype {κ : Type*} [Fintype κ]
    {M : Matrix m n ℝ} (U : Matrix m κ ℝ) (V : Matrix κ n ℝ) (h : U * V = M) :
    rowL2Norm U * colL2Norm V ∈ factorizationCosts M := by
  let e := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, U.submatrix id e, V.submatrix e id, ?_, ?_⟩
  · ext i j
    simp only [_root_.Matrix.mul_apply, _root_.Matrix.submatrix_apply, id_eq]
    rw [Equiv.sum_comp e (fun r ↦ U i r * V r j), ← h, _root_.Matrix.mul_apply]
  · rw [rowL2Norm_submatrix_equiv U e, colL2Norm_submatrix_equiv V e]

private theorem factorizationCosts_nonempty (M : Matrix m n ℝ) :
    (factorizationCosts M).Nonempty := by
  classical
  exact ⟨_, mem_factorizationCosts_of_fintype M 1 (_root_.Matrix.mul_one M)⟩

/-- The `γ₂` factorization norm of a finite real matrix `M`, defined as the infimum of
`rowL2Norm U * colL2Norm V` over all finite-dimensional factorizations `U * V = M`. -/
noncomputable def gamma2Norm (M : Matrix m n ℝ) : ℝ :=
  sInf (factorizationCosts M)

/-- Any factorization `U * V = M` over an arbitrary finite inner index type `κ` gives an upper
bound `gamma2Norm M ≤ rowL2Norm U * colL2Norm V`. -/
theorem gamma2Norm_le_of_factorization {κ : Type*} [Fintype κ] {M : Matrix m n ℝ}
    (U : Matrix m κ ℝ) (V : Matrix κ n ℝ) (h : U * V = M) :
    gamma2Norm M ≤ rowL2Norm U * colL2Norm V :=
  csInf_le (factorizationCosts_bddBelow M) (mem_factorizationCosts_of_fintype U V h)

/-- Lower-bound principle for `gamma2Norm M`: `b ≤ gamma2Norm M` if and only if every
finite-dimensional factorization `U * V = M` satisfies `b ≤ rowL2Norm U * colL2Norm V`. -/
theorem le_gamma2Norm_iff {M : Matrix m n ℝ} {b : ℝ} :
    b ≤ gamma2Norm M ↔
      ∀ (d : ℕ) (U : Matrix m (Fin d) ℝ) (V : Matrix (Fin d) n ℝ),
        U * V = M → b ≤ rowL2Norm U * colL2Norm V := by
  rw [gamma2Norm, le_csInf_iff (factorizationCosts_bddBelow M) (factorizationCosts_nonempty M)]
  constructor
  · intro h d U V hUV
    exact h _ ⟨d, U, V, hUV, rfl⟩
  · rintro h c ⟨d, U, V, hUV, rfl⟩
    exact h d U V hUV

/-- Elimination principle for upper bounds on `gamma2Norm M`: for every `ε > 0`, there exists a
finite-dimensional factorization `U * V = M` with cost strictly less than `gamma2Norm M + ε`. -/
theorem exists_factorization_lt_add {M : Matrix m n ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (U : Matrix m (Fin d) ℝ) (V : Matrix (Fin d) n ℝ),
      U * V = M ∧ rowL2Norm U * colL2Norm V < gamma2Norm M + ε := by
  obtain ⟨c, ⟨d, U, V, hUV, rfl⟩, hc⟩ :=
    exists_lt_of_csInf_lt (factorizationCosts_nonempty M) (lt_add_of_pos_right (gamma2Norm M) hε)
  exact ⟨d, U, V, hUV, hc⟩

/-- The `γ₂` factorization norm is always nonnegative. -/
theorem gamma2Norm_nonneg (M : Matrix m n ℝ) : 0 ≤ gamma2Norm M :=
  le_gamma2Norm_iff.mpr (fun _ U V _ ↦ mul_nonneg (rowL2Norm_nonneg U) (colL2Norm_nonneg V))

/-- Every entry of `M` is bounded in absolute value by `gamma2Norm M`. -/
theorem abs_apply_le_gamma2Norm (M : Matrix m n ℝ) (i : m) (j : n) :
    |M i j| ≤ gamma2Norm M :=
  le_gamma2Norm_iff.mpr (fun _ U V hUV ↦ hUV ▸ abs_mul_apply_le_rowL2Norm_mul_colL2Norm U V i j)

/-- The `γ₂` factorization norm of the zero matrix is `0`. -/
@[simp]
theorem gamma2Norm_zero : gamma2Norm (0 : Matrix m n ℝ) = 0 := by
  apply le_antisymm _ (gamma2Norm_nonneg _)
  have h0 : (0 : Matrix m (Fin 0) ℝ) * (0 : Matrix (Fin 0) n ℝ) = 0 := by ext i j; simp
  simpa using gamma2Norm_le_of_factorization (0 : Matrix m (Fin 0) ℝ) (0 : Matrix (Fin 0) n ℝ) h0

/-- `gamma2Norm M = 0` if and only if `M = 0`. -/
@[simp]
theorem gamma2Norm_eq_zero {M : Matrix m n ℝ} : gamma2Norm M = 0 ↔ M = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ gamma2Norm_zero⟩
  ext i j
  exact abs_nonpos_iff.mp ((abs_apply_le_gamma2Norm M i j).trans h.le)

/-- `gamma2Norm M` is strictly positive whenever `M ≠ 0`. -/
theorem gamma2Norm_pos_of_ne_zero {M : Matrix m n ℝ} (hM : M ≠ 0) : 0 < gamma2Norm M :=
  (gamma2Norm_nonneg M).lt_of_ne' (gamma2Norm_eq_zero.not.mpr hM)

/-- The `γ₂` factorization norm of an identity matrix is at most `1`. -/
theorem gamma2Norm_one_le [DecidableEq m] : gamma2Norm (1 : Matrix m m ℝ) ≤ 1 := by
  calc gamma2Norm (1 : Matrix m m ℝ)
      ≤ rowL2Norm (1 : Matrix m m ℝ) * colL2Norm (1 : Matrix m m ℝ) :=
        gamma2Norm_le_of_factorization 1 1 (_root_.Matrix.mul_one 1)
    _ ≤ 1 * 1 := mul_le_mul rowL2Norm_one_le colL2Norm_one_le (colL2Norm_nonneg _) zero_le_one
    _ = 1 := mul_one 1

/-- The `γ₂` factorization norm of a nonempty identity matrix equals `1`. -/
theorem gamma2Norm_one [DecidableEq m] [Nonempty m] : gamma2Norm (1 : Matrix m m ℝ) = 1 := by
  apply le_antisymm gamma2Norm_one_le
  obtain ⟨i⟩ := ‹Nonempty m›
  simpa using abs_apply_le_gamma2Norm (1 : Matrix m m ℝ) i i

/-- The `γ₂` factorization norm of the all-ones matrix is at most `1`. -/
theorem gamma2Norm_ones_le :
    gamma2Norm (_root_.Matrix.of fun (_ : m) (_ : n) ↦ (1 : ℝ)) ≤ 1 := by
  let U : Matrix m Unit ℝ := _root_.Matrix.of fun _ _ ↦ 1
  let V : Matrix Unit n ℝ := _root_.Matrix.of fun _ _ ↦ 1
  have hUV : U * V = _root_.Matrix.of fun (_ : m) (_ : n) ↦ (1 : ℝ) := by
    ext i j
    simp [U, V, _root_.Matrix.mul_apply]
  have hU : rowL2Norm U ≤ 1 := rowL2Norm_le_of_sq zero_le_one (fun _ ↦ by simp [U])
  have hV : colL2Norm V ≤ 1 := colL2Norm_le_of_sq zero_le_one (fun _ ↦ by simp [V])
  calc gamma2Norm (_root_.Matrix.of fun (_ : m) (_ : n) ↦ (1 : ℝ))
      ≤ rowL2Norm U * colL2Norm V := gamma2Norm_le_of_factorization U V hUV
    _ ≤ 1 * 1 := mul_le_mul hU hV (colL2Norm_nonneg V) zero_le_one
    _ = 1 := mul_one 1

/-- The `γ₂` norm of a rank-one outer product `vecMulVec u v` is bounded by the product of
uniform entrywise bounds on `u` and `v`. -/
theorem gamma2Norm_vecMulVec_le {u : m → ℝ} {v : n → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : ∀ i, |u i| ≤ a) (hv : ∀ j, |v j| ≤ b) :
    gamma2Norm (_root_.Matrix.vecMulVec u v) ≤ a * b := by
  let U : Matrix m Unit ℝ := _root_.Matrix.of fun i _ ↦ u i
  let V : Matrix Unit n ℝ := _root_.Matrix.of fun _ j ↦ v j
  have hUV : U * V = _root_.Matrix.vecMulVec u v := by
    ext i j
    simp [U, V, _root_.Matrix.mul_apply, _root_.Matrix.vecMulVec_apply]
  have hU : rowL2Norm U ≤ a := rowL2Norm_le_of_sq ha (fun i ↦ by
    have : u i ^ 2 ≤ a ^ 2 := by
      rw [← sq_abs (u i)]; exact pow_le_pow_left₀ (abs_nonneg _) (hu i) 2
    simpa [U] using this)
  have hV : colL2Norm V ≤ b := colL2Norm_le_of_sq hb (fun j ↦ by
    have : v j ^ 2 ≤ b ^ 2 := by
      rw [← sq_abs (v j)]; exact pow_le_pow_left₀ (abs_nonneg _) (hv j) 2
    simpa [V] using this)
  exact (gamma2Norm_le_of_factorization U V hUV).trans
    (mul_le_mul hU hV (colL2Norm_nonneg V) ha)

/-- Transposing a matrix preserves its `γ₂` factorization norm. -/
@[simp]
theorem gamma2Norm_transpose (M : Matrix m n ℝ) : gamma2Norm Mᵀ = gamma2Norm M := by
  apply le_antisymm
  · refine le_gamma2Norm_iff.mpr (fun d U V hUV ↦ ?_)
    have hUVt : Vᵀ * Uᵀ = Mᵀ := by rw [← _root_.Matrix.transpose_mul, hUV]
    rw [← colL2Norm_transpose U, ← rowL2Norm_transpose V, mul_comm]
    exact gamma2Norm_le_of_factorization Vᵀ Uᵀ hUVt
  · refine le_gamma2Norm_iff.mpr (fun d U V hUV ↦ ?_)
    have hUVt : Vᵀ * Uᵀ = M := by
      simpa using congr_arg _root_.Matrix.transpose hUV
    rw [← colL2Norm_transpose U, ← rowL2Norm_transpose V, mul_comm]
    exact gamma2Norm_le_of_factorization Vᵀ Uᵀ hUVt

/-- Taking any submatrix (including permuting, deleting, or duplicating rows and columns) does not
increase `gamma2Norm`. -/
theorem gamma2Norm_submatrix_le [Fintype m'] [Fintype n'] (M : Matrix m n ℝ)
    (f : m' → m) (g : n' → n) :
    gamma2Norm (M.submatrix f g) ≤ gamma2Norm M := by
  refine le_gamma2Norm_iff.mpr (fun d U V hUV ↦ ?_)
  have hsub : U.submatrix f id * V.submatrix id g = M.submatrix f g := by
    rw [← hUV]
    ext i' j'
    simp [_root_.Matrix.mul_apply]
  calc gamma2Norm (M.submatrix f g)
      ≤ rowL2Norm (U.submatrix f id) * colL2Norm (V.submatrix id g) :=
        gamma2Norm_le_of_factorization _ _ hsub
    _ ≤ rowL2Norm U * colL2Norm V :=
        mul_le_mul (rowL2Norm_submatrix_left_le U f) (colL2Norm_submatrix_right_le V g)
          (colL2Norm_nonneg _) (rowL2Norm_nonneg U)

/-- Positive homogeneity of `gamma2Norm`: `gamma2Norm (c • M) = |c| * gamma2Norm M`. -/
theorem gamma2Norm_smul (c : ℝ) (M : Matrix m n ℝ) :
    gamma2Norm (c • M) = |c| * gamma2Norm M := by
  by_cases hc : c = 0
  · simp [hc]
  · have hle : ∀ (a : ℝ) (A : Matrix m n ℝ), gamma2Norm (a • A) ≤ |a| * gamma2Norm A := by
      intro a A
      by_cases ha : a = 0
      · simp [ha]
      · have hpos : 0 < |a| := abs_pos.mpr ha
        rw [← div_le_iff₀' hpos]
        refine le_gamma2Norm_iff.mpr (fun d U V hUV ↦ ?_)
        rw [div_le_iff₀' hpos]
        have hfac : (a • U) * V = a • A := by rw [_root_.Matrix.smul_mul, hUV]
        calc gamma2Norm (a • A)
            ≤ rowL2Norm (a • U) * colL2Norm V := gamma2Norm_le_of_factorization _ _ hfac
          _ = |a| * (rowL2Norm U * colL2Norm V) := by rw [rowL2Norm_smul, mul_assoc]
    apply le_antisymm (hle c M)
    calc |c| * gamma2Norm M
        = |c| * gamma2Norm (c⁻¹ • (c • M)) := by rw [inv_smul_smul₀ hc]
      _ ≤ |c| * (|c⁻¹| * gamma2Norm (c • M)) :=
          mul_le_mul_of_nonneg_left (hle c⁻¹ (c • M)) (abs_nonneg c)
      _ = gamma2Norm (c • M) := by
          rw [abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul]

/-- Negation invariance of `gamma2Norm`. -/
@[simp]
theorem gamma2Norm_neg (M : Matrix m n ℝ) : gamma2Norm (-M) = gamma2Norm M := by
  simpa using gamma2Norm_smul (-1 : ℝ) M

private theorem gamma2Norm_add_le_cost {A B : Matrix m n ℝ} {d₁ d₂ : ℕ}
    (U₁ : Matrix m (Fin d₁) ℝ) (V₁ : Matrix (Fin d₁) n ℝ) (h₁ : U₁ * V₁ = A)
    (U₂ : Matrix m (Fin d₂) ℝ) (V₂ : Matrix (Fin d₂) n ℝ) (h₂ : U₂ * V₂ = B) :
    gamma2Norm (A + B) ≤ rowL2Norm U₁ * colL2Norm V₁ + rowL2Norm U₂ * colL2Norm V₂ := by
  set a₁ := rowL2Norm U₁
  set b₁ := colL2Norm V₁
  set a₂ := rowL2Norm U₂
  set b₂ := colL2Norm V₂
  by_cases hc₁ : a₁ * b₁ = 0
  · have hA : A = 0 := by
      ext i j
      exact abs_nonpos_iff.mp ((h₁ ▸ abs_mul_apply_le_rowL2Norm_mul_colL2Norm U₁ V₁ i j).trans
        hc₁.le)
    rw [hA, zero_add, hc₁, zero_add]
    exact gamma2Norm_le_of_factorization U₂ V₂ h₂
  · by_cases hc₂ : a₂ * b₂ = 0
    · have hB : B = 0 := by
        ext i j
        exact abs_nonpos_iff.mp ((h₂ ▸ abs_mul_apply_le_rowL2Norm_mul_colL2Norm U₂ V₂ i j).trans
          hc₂.le)
      rw [hB, add_zero, hc₂, add_zero]
      exact gamma2Norm_le_of_factorization U₁ V₁ h₁
    · have ha₁ : 0 < a₁ := (rowL2Norm_nonneg U₁).lt_of_ne' (left_ne_zero_of_mul hc₁)
      have hb₁ : 0 < b₁ := (colL2Norm_nonneg V₁).lt_of_ne' (right_ne_zero_of_mul hc₁)
      have ha₂ : 0 < a₂ := (rowL2Norm_nonneg U₂).lt_of_ne' (left_ne_zero_of_mul hc₂)
      have hb₂ : 0 < b₂ := (colL2Norm_nonneg V₂).lt_of_ne' (right_ne_zero_of_mul hc₂)
      let s₁ : ℝ := √(b₁ / a₁)
      let s₂ : ℝ := √(b₂ / a₂)
      have hs₁ : 0 < s₁ := Real.sqrt_pos.mpr (div_pos hb₁ ha₁)
      have hs₂ : 0 < s₂ := Real.sqrt_pos.mpr (div_pos hb₂ ha₂)
      let U : Matrix m (Fin d₁ ⊕ Fin d₂) ℝ := _root_.Matrix.of fun i r ↦
        Sum.elim (fun r₁ ↦ s₁ * U₁ i r₁) (fun r₂ ↦ s₂ * U₂ i r₂) r
      let V : Matrix (Fin d₁ ⊕ Fin d₂) n ℝ := _root_.Matrix.of fun r j ↦
        Sum.elim (fun r₁ ↦ s₁⁻¹ * V₁ r₁ j) (fun r₂ ↦ s₂⁻¹ * V₂ r₂ j) r
      have hUV : U * V = A + B := by
        ext i j
        rw [← h₁, ← h₂]
        simp only [_root_.Matrix.mul_apply, _root_.Matrix.add_apply, U, V,
          _root_.Matrix.of_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
        congr 1
        · refine Finset.sum_congr rfl (fun r₁ _ ↦ ?_)
          field_simp [hs₁.ne']
        · refine Finset.sum_congr rfl (fun r₂ _ ↦ ?_)
          field_simp [hs₂.ne']
      have hc_nn : 0 ≤ a₁ * b₁ + a₂ * b₂ := by positivity
      have hU : rowL2Norm U ≤ √(a₁ * b₁ + a₂ * b₂) := by
        refine rowL2Norm_le_of_sq (Real.sqrt_nonneg _) (fun i ↦ ?_)
        rw [Real.sq_sqrt hc_nn]
        simp only [U, _root_.Matrix.of_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
        have hrow₁ : ∑ r₁ : Fin d₁, (s₁ * U₁ i r₁) ^ 2 ≤ a₁ * b₁ := by
          have : ∑ r₁ : Fin d₁, (s₁ * U₁ i r₁) ^ 2 = s₁ ^ 2 * ∑ r₁, U₁ i r₁ ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
          rw [this, Real.sq_sqrt (div_nonneg hb₁.le ha₁.le)]
          calc (b₁ / a₁) * ∑ r₁, U₁ i r₁ ^ 2
              ≤ (b₁ / a₁) * a₁ ^ 2 :=
                mul_le_mul_of_nonneg_left (sum_row_sq_le_rowL2Norm_sq U₁ i) (by positivity)
            _ = a₁ * b₁ := by field_simp [ha₁.ne']
        have hrow₂ : ∑ r₂ : Fin d₂, (s₂ * U₂ i r₂) ^ 2 ≤ a₂ * b₂ := by
          have : ∑ r₂ : Fin d₂, (s₂ * U₂ i r₂) ^ 2 = s₂ ^ 2 * ∑ r₂, U₂ i r₂ ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
          rw [this, Real.sq_sqrt (div_nonneg hb₂.le ha₂.le)]
          calc (b₂ / a₂) * ∑ r₂, U₂ i r₂ ^ 2
              ≤ (b₂ / a₂) * a₂ ^ 2 :=
                mul_le_mul_of_nonneg_left (sum_row_sq_le_rowL2Norm_sq U₂ i) (by positivity)
            _ = a₂ * b₂ := by field_simp [ha₂.ne']
        exact add_le_add hrow₁ hrow₂
      have hV : colL2Norm V ≤ √(a₁ * b₁ + a₂ * b₂) := by
        refine colL2Norm_le_of_sq (Real.sqrt_nonneg _) (fun j ↦ ?_)
        rw [Real.sq_sqrt hc_nn]
        simp only [V, _root_.Matrix.of_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
        have hcol₁ : ∑ r₁ : Fin d₁, (s₁⁻¹ * V₁ r₁ j) ^ 2 ≤ a₁ * b₁ := by
          have : ∑ r₁ : Fin d₁, (s₁⁻¹ * V₁ r₁ j) ^ 2 = (s₁ ^ 2)⁻¹ * ∑ r₁, V₁ r₁ j ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
          rw [this, Real.sq_sqrt (div_nonneg hb₁.le ha₁.le), inv_div]
          calc (a₁ / b₁) * ∑ r₁, V₁ r₁ j ^ 2
              ≤ (a₁ / b₁) * b₁ ^ 2 :=
                mul_le_mul_of_nonneg_left (sum_col_sq_le_colL2Norm_sq V₁ j) (by positivity)
            _ = a₁ * b₁ := by field_simp [hb₁.ne']
        have hcol₂ : ∑ r₂ : Fin d₂, (s₂⁻¹ * V₂ r₂ j) ^ 2 ≤ a₂ * b₂ := by
          have : ∑ r₂ : Fin d₂, (s₂⁻¹ * V₂ r₂ j) ^ 2 = (s₂ ^ 2)⁻¹ * ∑ r₂, V₂ r₂ j ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
          rw [this, Real.sq_sqrt (div_nonneg hb₂.le ha₂.le), inv_div]
          calc (a₂ / b₂) * ∑ r₂, V₂ r₂ j ^ 2
              ≤ (a₂ / b₂) * b₂ ^ 2 :=
                mul_le_mul_of_nonneg_left (sum_col_sq_le_colL2Norm_sq V₂ j) (by positivity)
            _ = a₂ * b₂ := by field_simp [hb₂.ne']
        exact add_le_add hcol₁ hcol₂
      calc gamma2Norm (A + B)
          ≤ rowL2Norm U * colL2Norm V := gamma2Norm_le_of_factorization U V hUV
        _ ≤ √(a₁ * b₁ + a₂ * b₂) * √(a₁ * b₁ + a₂ * b₂) :=
            mul_le_mul hU hV (colL2Norm_nonneg V) (Real.sqrt_nonneg _)
        _ = a₁ * b₁ + a₂ * b₂ := Real.mul_self_sqrt hc_nn

/-- Triangle inequality for the `γ₂` factorization norm. -/
theorem gamma2Norm_add_le (A B : Matrix m n ℝ) :
    gamma2Norm (A + B) ≤ gamma2Norm A + gamma2Norm B := by
  refine le_of_forall_pos_lt_add (fun ε hε ↦ ?_)
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨d₁, U₁, V₁, h₁, hc₁⟩ := exists_factorization_lt_add (M := A) hε2
  obtain ⟨d₂, U₂, V₂, h₂, hc₂⟩ := exists_factorization_lt_add (M := B) hε2
  linarith [gamma2Norm_add_le_cost U₁ V₁ h₁ U₂ V₂ h₂]

/-- Triangle inequality for matrix differences under `gamma2Norm`. -/
theorem gamma2Norm_sub_le (A B : Matrix m n ℝ) :
    gamma2Norm (A - B) ≤ gamma2Norm A + gamma2Norm B := by
  simpa [sub_eq_add_neg] using gamma2Norm_add_le A (-B)

/-- Finite-sum triangle inequality for `gamma2Norm`. -/
theorem gamma2Norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrix m n ℝ) :
    gamma2Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, gamma2Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (gamma2Norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- Schur submultiplicativity of `gamma2Norm` under the entrywise Hadamard product. -/
theorem gamma2Norm_hadamard_le (A B : Matrix m n ℝ) :
    gamma2Norm (_root_.Matrix.hadamard A B) ≤ gamma2Norm A * gamma2Norm B := by
  have hcost : ∀ {d₁ d₂ : ℕ} (U₁ : Matrix m (Fin d₁) ℝ) (V₁ : Matrix (Fin d₁) n ℝ),
      U₁ * V₁ = A → ∀ (U₂ : Matrix m (Fin d₂) ℝ) (V₂ : Matrix (Fin d₂) n ℝ), U₂ * V₂ = B →
        gamma2Norm (_root_.Matrix.hadamard A B) ≤
          (rowL2Norm U₁ * colL2Norm V₁) * (rowL2Norm U₂ * colL2Norm V₂) := by
    intro d₁ d₂ U₁ V₁ h₁ U₂ V₂ h₂
    let U : Matrix m (Fin d₁ × Fin d₂) ℝ :=
      _root_.Matrix.of fun i p ↦ U₁ i p.1 * U₂ i p.2
    let V : Matrix (Fin d₁ × Fin d₂) n ℝ :=
      _root_.Matrix.of fun p j ↦ V₁ p.1 j * V₂ p.2 j
    have hUV : U * V = _root_.Matrix.hadamard A B := by
      ext i j
      rw [← h₁, ← h₂]
      simp only [_root_.Matrix.hadamard_apply, _root_.Matrix.mul_apply, U, V,
        _root_.Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun r₁ _ ↦ Finset.sum_congr rfl (fun r₂ _ ↦ by ring))
    have hU : rowL2Norm U ≤ rowL2Norm U₁ * rowL2Norm U₂ := by
      refine rowL2Norm_le_of_sq (mul_nonneg (rowL2Norm_nonneg U₁) (rowL2Norm_nonneg U₂))
        (fun i ↦ ?_)
      have hprod : ∑ p : Fin d₁ × Fin d₂, (U₁ i p.1 * U₂ i p.2) ^ 2 =
          (∑ r₁, U₁ i r₁ ^ 2) * (∑ r₂, U₂ i r₂ ^ 2) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun r₁ _ ↦ Finset.sum_congr rfl (fun r₂ _ ↦ by ring))
      simp only [U, _root_.Matrix.of_apply]
      rw [hprod, mul_pow]
      exact mul_le_mul (sum_row_sq_le_rowL2Norm_sq U₁ i) (sum_row_sq_le_rowL2Norm_sq U₂ i)
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (sq_nonneg _)
    have hV : colL2Norm V ≤ colL2Norm V₁ * colL2Norm V₂ := by
      refine colL2Norm_le_of_sq (mul_nonneg (colL2Norm_nonneg V₁) (colL2Norm_nonneg V₂))
        (fun j ↦ ?_)
      have hprod : ∑ p : Fin d₁ × Fin d₂, (V₁ p.1 j * V₂ p.2 j) ^ 2 =
          (∑ r₁, V₁ r₁ j ^ 2) * (∑ r₂, V₂ r₂ j ^ 2) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun r₁ _ ↦ Finset.sum_congr rfl (fun r₂ _ ↦ by ring))
      simp only [V, _root_.Matrix.of_apply]
      rw [hprod, mul_pow]
      exact mul_le_mul (sum_col_sq_le_colL2Norm_sq V₁ j) (sum_col_sq_le_colL2Norm_sq V₂ j)
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (sq_nonneg _)
    calc gamma2Norm (_root_.Matrix.hadamard A B)
        ≤ rowL2Norm U * colL2Norm V := gamma2Norm_le_of_factorization U V hUV
      _ ≤ (rowL2Norm U₁ * rowL2Norm U₂) * (colL2Norm V₁ * colL2Norm V₂) :=
          mul_le_mul hU hV (colL2Norm_nonneg V)
            (mul_nonneg (rowL2Norm_nonneg U₁) (rowL2Norm_nonneg U₂))
      _ = (rowL2Norm U₁ * colL2Norm V₁) * (rowL2Norm U₂ * colL2Norm V₂) := by ring
  by_cases hB : B = 0
  · have h0 : _root_.Matrix.hadamard A B = 0 := by ext i j; simp [hB]
    rw [h0, hB]
    simp
  · have hBp : 0 < gamma2Norm B := gamma2Norm_pos_of_ne_zero hB
    have hstep : ∀ (d₂ : ℕ) (U₂ : Matrix m (Fin d₂) ℝ) (V₂ : Matrix (Fin d₂) n ℝ),
        U₂ * V₂ = B →
          gamma2Norm (_root_.Matrix.hadamard A B) ≤
            gamma2Norm A * (rowL2Norm U₂ * colL2Norm V₂) := by
      intro d₂ U₂ V₂ h₂
      have hc₂ : 0 < rowL2Norm U₂ * colL2Norm V₂ :=
        hBp.trans_le (gamma2Norm_le_of_factorization U₂ V₂ h₂)
      rw [← div_le_iff₀ hc₂]
      refine le_gamma2Norm_iff.mpr (fun d₁ U₁ V₁ h₁ ↦ ?_)
      rw [div_le_iff₀ hc₂]
      exact hcost U₁ V₁ h₁ U₂ V₂ h₂
    by_cases hA : A = 0
    · have h0 : _root_.Matrix.hadamard A B = 0 := by ext i j; simp [hA]
      rw [h0, hA]
      simp
    · have hAp : 0 < gamma2Norm A := gamma2Norm_pos_of_ne_zero hA
      rw [← div_le_iff₀' hAp]
      refine le_gamma2Norm_iff.mpr (fun d₂ U₂ V₂ h₂ ↦ ?_)
      rw [div_le_iff₀' hAp]
      exact hstep d₂ U₂ V₂ h₂

end Gamma2Basic

section SpectralAndHolder

variable {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]

private theorem sum_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    ∑ i ∈ s, a i * b i ≤ √(∑ i ∈ s, a i ^ 2) * √(∑ i ∈ s, b i ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le (Finset.sum_mul_sq_le_sq_mul_sq s a b)

/-- **Bessel biorthonormal pairing bound for `gamma2Norm`**: if families `e : κ → m → ℝ` and
`f : κ → n → ℝ` satisfy Bessel's inequality, then the `ℓ₁` sum of bilinear pairings `⟨e_a, M f_a⟩`
is at most `√(card m * card n) * gamma2Norm M`. -/
theorem sum_abs_bilinear_le_sqrt_card_mul_gamma2Norm (M : Matrix m n ℝ)
    (e : κ → m → ℝ) (f : κ → n → ℝ)
    (he : ∀ x : m → ℝ, ∑ a : κ, (∑ i : m, e a i * x i) ^ 2 ≤ ∑ i : m, x i ^ 2)
    (hf : ∀ y : n → ℝ, ∑ a : κ, (∑ j : n, f a j * y j) ^ 2 ≤ ∑ j : n, y j ^ 2) :
    ∑ a : κ, |∑ i : m, ∑ j : n, e a i * M i j * f a j| ≤
      √((Fintype.card m : ℝ) * Fintype.card n) * gamma2Norm M := by
  by_cases hcard : Fintype.card m * Fintype.card n = 0
  · rcases mul_eq_zero.mp hcard with hm | hn
    · have : IsEmpty m := Fintype.card_eq_zero_iff.mp hm
      simp
    · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
      simp
  · have hpos : 0 < √((Fintype.card m : ℝ) * Fintype.card n) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hcard)
    rw [← div_le_iff₀' hpos]
    refine le_gamma2Norm_iff.mpr (fun d U V hUV ↦ ?_)
    rw [div_le_iff₀' hpos]
    -- Step 1: Apply Cauchy-Schwarz across the inner factorization index `r : Fin d`.
    have hterm : ∀ a : κ, |∑ i : m, ∑ j : n, e a i * M i j * f a j| ≤
        √(∑ r : Fin d, (∑ i : m, e a i * U i r) ^ 2) *
          √(∑ r : Fin d, (∑ j : n, f a j * V r j) ^ 2) := by
      intro a
      have hrewrite : ∑ i : m, ∑ j : n, e a i * M i j * f a j =
          ∑ r : Fin d, (∑ i : m, e a i * U i r) * (∑ j : n, f a j * V r j) := by
        calc ∑ i : m, ∑ j : n, e a i * M i j * f a j
            = ∑ i : m, ∑ j : n, ∑ r : Fin d, (e a i * U i r) * (f a j * V r j) := by
              refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ ?_))
              rw [← hUV, _root_.Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl (fun r _ ↦ by ring)
          _ = ∑ r : Fin d, ∑ i : m, ∑ j : n, (e a i * U i r) * (f a j * V r j) := by
              rw [Finset.sum_congr rfl (fun i _ ↦ Finset.sum_comm), Finset.sum_comm]
          _ = ∑ r : Fin d, (∑ i : m, e a i * U i r) * (∑ j : n, f a j * V r j) :=
              Finset.sum_congr rfl (fun r _ ↦ (Finset.sum_mul_sum _ _ _ _).symm)
      rw [hrewrite]
      calc |∑ r : Fin d, (∑ i : m, e a i * U i r) * (∑ j : n, f a j * V r j)|
          ≤ ∑ r : Fin d, |∑ i : m, e a i * U i r| * |∑ j : n, f a j * V r j| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl (fun r _ ↦ abs_mul _ _)
        _ ≤ √(∑ r : Fin d, |∑ i : m, e a i * U i r| ^ 2) *
              √(∑ r : Fin d, |∑ j : n, f a j * V r j| ^ 2) :=
            sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
        _ = √(∑ r : Fin d, (∑ i : m, e a i * U i r) ^ 2) *
              √(∑ r : Fin d, (∑ j : n, f a j * V r j) ^ 2) := by simp [sq_abs]
    -- Step 2: Apply Cauchy-Schwarz across `a : κ` and invoke Bessel on columns of `U`, rows of `V`.
    have hU_bessel : ∑ a : κ, ∑ r : Fin d, (∑ i : m, e a i * U i r) ^ 2 ≤
        frobeniusNorm U ^ 2 := by
      calc ∑ a : κ, ∑ r : Fin d, (∑ i : m, e a i * U i r) ^ 2
          = ∑ r : Fin d, ∑ a : κ, (∑ i : m, e a i * U i r) ^ 2 := Finset.sum_comm
        _ ≤ ∑ r : Fin d, ∑ i : m, U i r ^ 2 :=
            Finset.sum_le_sum (fun r _ ↦ he (fun i ↦ U i r))
        _ = ∑ i : m, ∑ r : Fin d, U i r ^ 2 := Finset.sum_comm
        _ = frobeniusNorm U ^ 2 := (sq_frobeniusNorm U).symm
    have hV_bessel : ∑ a : κ, ∑ r : Fin d, (∑ j : n, f a j * V r j) ^ 2 ≤
        frobeniusNorm V ^ 2 := by
      rw [Finset.sum_comm, sq_frobeniusNorm]
      exact Finset.sum_le_sum (fun r _ ↦ hf (fun j ↦ V r j))
    calc ∑ a : κ, |∑ i : m, ∑ j : n, e a i * M i j * f a j|
        ≤ ∑ a : κ, √(∑ r : Fin d, (∑ i : m, e a i * U i r) ^ 2) *
            √(∑ r : Fin d, (∑ j : n, f a j * V r j) ^ 2) :=
          Finset.sum_le_sum (fun a _ ↦ hterm a)
      _ ≤ √(∑ a : κ, √(∑ r : Fin d, (∑ i : m, e a i * U i r) ^ 2) ^ 2) *
            √(∑ a : κ, √(∑ r : Fin d, (∑ j : n, f a j * V r j) ^ 2) ^ 2) :=
          sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
      _ = √(∑ a : κ, ∑ r : Fin d, (∑ i : m, e a i * U i r) ^ 2) *
            √(∑ a : κ, ∑ r : Fin d, (∑ j : n, f a j * V r j) ^ 2) := by
          congr 2 <;> refine Finset.sum_congr rfl (fun _ _ ↦
            Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      _ ≤ frobeniusNorm U * frobeniusNorm V := by
          refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (frobeniusNorm_nonneg U)
          · exact Real.sqrt_le_iff.mpr ⟨frobeniusNorm_nonneg U, hU_bessel⟩
          · exact Real.sqrt_le_iff.mpr ⟨frobeniusNorm_nonneg V, hV_bessel⟩
      _ ≤ (√(Fintype.card m : ℝ) * rowL2Norm U) * (√(Fintype.card n : ℝ) * colL2Norm V) :=
          mul_le_mul (frobeniusNorm_le_sqrt_card_mul_rowL2Norm U)
            (frobeniusNorm_le_sqrt_card_mul_colL2Norm V) (frobeniusNorm_nonneg V)
            (mul_nonneg (Real.sqrt_nonneg _) (rowL2Norm_nonneg U))
      _ = √((Fintype.card m : ℝ) * Fintype.card n) * (rowL2Norm U * colL2Norm V) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _)]
          ring

private theorem bessel_of_suborthonormal {ι α : Type*} [Fintype ι] [Fintype α]
    (e : α → ι → ℝ)
    (horth : ∀ a b : α, a ≠ b → ∑ i : ι, e a i * e b i = 0)
    (hnorm : ∀ a : α, ∑ i : ι, e a i ^ 2 ≤ 1)
    (x : ι → ℝ) :
    ∑ a : α, (∑ i : ι, e a i * x i) ^ 2 ≤ ∑ i : ι, x i ^ 2 := by
  classical
  let c : α → ℝ := fun a ↦ ∑ i : ι, e a i * x i
  have hnonneg : 0 ≤ ∑ i : ι, (x i - ∑ a : α, c a * e a i) ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hexpand : ∑ i : ι, (x i - ∑ a : α, c a * e a i) ^ 2 =
      (∑ i : ι, x i ^ 2) - 2 * (∑ a : α, c a ^ 2) +
        ∑ a : α, ∑ b : α, c a * c b * (∑ i : ι, e a i * e b i) := by
    have h1 : ∀ i : ι, (x i - ∑ a : α, c a * e a i) ^ 2 =
        x i ^ 2 - 2 * (∑ a : α, c a * (e a i * x i)) +
          ∑ a : α, ∑ b : α, c a * c b * (e a i * e b i) := by
      intro i
      have hsq : (∑ a : α, c a * e a i) ^ 2 =
          ∑ a : α, ∑ b : α, c a * c b * (e a i * e b i) := by
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun a _ ↦ Finset.sum_congr rfl (fun b _ ↦ by ring))
      have hmid : x i * ∑ a : α, c a * e a i = ∑ a : α, c a * (e a i * x i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ ↦ by ring)
      linarith [sub_sq (x i) (∑ a : α, c a * e a i)]
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    · congr 2
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun a _ ↦ by rw [← Finset.mul_sum, sq])
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ ↦ ?_)
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun b _ ↦ by rw [← Finset.mul_sum])
  have hdiag : ∑ a : α, ∑ b : α, c a * c b * (∑ i : ι, e a i * e b i) ≤
      ∑ a : α, c a ^ 2 := by
    refine Finset.sum_le_sum (fun a _ ↦ ?_)
    rw [Finset.sum_eq_single a (fun b _ hba ↦ by rw [horth a b hba.symm, mul_zero])
      (fun ha ↦ absurd (Finset.mem_univ a) ha)]
    calc c a * c a * ∑ i : ι, e a i * e a i
        = c a ^ 2 * ∑ i : ι, e a i ^ 2 := by simp [sq]
      _ ≤ c a ^ 2 * 1 := mul_le_mul_of_nonneg_left (hnorm a) (sq_nonneg _)
      _ = c a ^ 2 := mul_one _
  linarith

/-- **Exact `γ₂` norm for flat orthogonal expansions**: if `χ : κ → m → ℝ` is a family of
unit-modulus pairwise orthogonal vectors on a nonempty finite set `m`, and
`M i j = ∑ a, c a * χ a i * χ a j`, then `gamma2Norm M = ∑ a, |c a|`. -/
theorem gamma2Norm_eq_sum_abs_of_flat_orthogonal [Nonempty m] (χ : κ → m → ℝ)
    (hmod : ∀ a i, |χ a i| = 1)
    (horth : ∀ a b, a ≠ b → ∑ i : m, χ a i * χ b i = 0)
    (c : κ → ℝ) :
    gamma2Norm (_root_.Matrix.of fun i j : m ↦ ∑ a : κ, c a * χ a i * χ a j) =
      ∑ a : κ, |c a| := by
  set M : Matrix m m ℝ := _root_.Matrix.of fun i j ↦ ∑ a : κ, c a * χ a i * χ a j
  have hχsq : ∀ a i, χ a i ^ 2 = 1 := fun a i ↦ by rw [← sq_abs, hmod, one_pow]
  apply le_antisymm
  · -- Upper bound via explicit symmetric factorization `U * V = M`.
    let U : Matrix m κ ℝ := _root_.Matrix.of fun i a ↦ √(|c a|) * χ a i
    let V : Matrix κ m ℝ :=
      _root_.Matrix.of fun a j ↦ (if 0 ≤ c a then 1 else -1) * √(|c a|) * χ a j
    have hUV : U * V = M := by
      ext i j
      simp only [_root_.Matrix.mul_apply, U, V, M, _root_.Matrix.of_apply]
      refine Finset.sum_congr rfl (fun a _ ↦ ?_)
      have hsign : (if 0 ≤ c a then (1 : ℝ) else -1) * |c a| = c a := by
        split_ifs with hca
        · simp [abs_of_nonneg hca]
        · rw [abs_of_neg (lt_of_not_ge hca)]; ring
      calc √(|c a|) * χ a i * ((if 0 ≤ c a then 1 else -1) * √(|c a|) * χ a j)
          = (if 0 ≤ c a then 1 else -1) * (√(|c a|) * √(|c a|)) * χ a i * χ a j := by ring
        _ = c a * χ a i * χ a j := by rw [Real.mul_self_sqrt (abs_nonneg _), hsign]
    have hsum_nn : 0 ≤ ∑ a : κ, |c a| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    have hU : rowL2Norm U ≤ √(∑ a : κ, |c a|) := by
      refine rowL2Norm_le_of_sq (Real.sqrt_nonneg _) (fun i ↦ ?_)
      rw [Real.sq_sqrt hsum_nn]
      refine le_of_eq (Finset.sum_congr rfl fun a _ ↦ ?_)
      simp [U, mul_pow, hχsq, Real.sq_sqrt (abs_nonneg _)]
    have hV : colL2Norm V ≤ √(∑ a : κ, |c a|) := by
      refine colL2Norm_le_of_sq (Real.sqrt_nonneg _) (fun j ↦ ?_)
      rw [Real.sq_sqrt hsum_nn]
      refine le_of_eq (Finset.sum_congr rfl fun a _ ↦ ?_)
      by_cases hca : 0 ≤ c a <;>
        simp [V, hca, mul_pow, hχsq, Real.sq_sqrt (abs_nonneg _)]
    calc gamma2Norm M ≤ rowL2Norm U * colL2Norm V := gamma2Norm_le_of_factorization U V hUV
      _ ≤ √(∑ a : κ, |c a|) * √(∑ a : κ, |c a|) :=
          mul_le_mul hU hV (colL2Norm_nonneg V) (Real.sqrt_nonneg _)
      _ = ∑ a : κ, |c a| := Real.mul_self_sqrt hsum_nn
  · -- Lower bound via the normalized orthonormal family `χ a i / √(card m)`.
    set N : ℝ := (Fintype.card m : ℝ)
    have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
    let e : κ → m → ℝ := fun a i ↦ χ a i / √N
    have he_bessel : ∀ x : m → ℝ, ∑ a : κ, (∑ i : m, e a i * x i) ^ 2 ≤ ∑ i : m, x i ^ 2 := by
      refine bessel_of_suborthonormal e (fun a b hab ↦ ?_) (fun a ↦ ?_)
      · calc ∑ i : m, e a i * e b i
            = (∑ i : m, χ a i * χ b i) / N := by
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl (fun i _ ↦ ?_)
              simp only [e, div_mul_div_comm, Real.mul_self_sqrt hN.le]
          _ = 0 := by rw [horth a b hab, zero_div]
      · refine le_of_eq ?_
        calc ∑ i : m, e a i ^ 2
            = (∑ i : m, χ a i ^ 2) / N := by
              rw [Finset.sum_div]
              exact Finset.sum_congr rfl (fun i _ ↦ by simp [e, div_pow, Real.sq_sqrt hN.le])
          _ = 1 := by simp [hχsq, N]
    have hpair := sum_abs_bilinear_le_sqrt_card_mul_gamma2Norm M e e he_bessel he_bessel
    have hdiag : ∀ a : κ, ∑ i : m, ∑ j : m, e a i * M i j * e a j = N * c a := by
      intro a
      have hself : ∑ i : m, χ a i * χ a i = N := by
        calc ∑ i : m, χ a i * χ a i
            = ∑ i : m, χ a i ^ 2 := Finset.sum_congr rfl (fun _ _ ↦ (sq _).symm)
          _ = N := by simp [hχsq, N]
      calc ∑ i : m, ∑ j : m, e a i * (∑ b : κ, c b * χ b i * χ b j) * e a j
          = ∑ i : m, ∑ j : m, ∑ b : κ, c b * (χ a i * χ b i) * (χ a j * χ b j) / N := by
            refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ ?_))
            rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun b _ ↦ ?_)
            simp only [e]
            have hsq : √N * √N = N := Real.mul_self_sqrt hN.le
            calc χ a i / √N * (c b * χ b i * χ b j) * (χ a j / √N)
                = c b * (χ a i * χ b i) * (χ a j * χ b j) / (√N * √N) := by ring
              _ = c b * (χ a i * χ b i) * (χ a j * χ b j) / N := by rw [hsq]
        _ = ∑ b : κ, ∑ i : m, ∑ j : m, c b * (χ a i * χ b i) * (χ a j * χ b j) / N := by
            rw [Finset.sum_congr rfl (fun i _ ↦ Finset.sum_comm), Finset.sum_comm]
        _ = (∑ b : κ, c b * (∑ i : m, χ a i * χ b i) * (∑ j : m, χ a j * χ b j)) / N := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun b _ ↦ ?_)
            simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
            exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ by ring))
        _ = (c a * N * N) / N := by
            congr 1
            rw [Finset.sum_eq_single a (fun b _ hba ↦ by rw [horth a b hba.symm]; ring)
              (fun ha ↦ absurd (Finset.mem_univ a) ha), hself]
        _ = N * c a := by field_simp [hN.ne']
    have hsum : ∑ a : κ, |∑ i : m, ∑ j : m, e a i * M i j * e a j| = N * ∑ a : κ, |c a| := by
      simp_rw [hdiag, abs_mul, abs_of_pos hN, ← Finset.mul_sum]
    have hsqrt : √((Fintype.card m : ℝ) * Fintype.card m) = N := Real.sqrt_mul_self hN.le
    rw [hsum, hsqrt] at hpair
    exact le_of_mul_le_mul_left hpair hN

/-- Pairing lower bound against unit-modulus pairwise orthogonal characters for an arbitrary square
matrix `G`: `∑ a, |(1 / card m ^ 2) * ∑ i, ∑ j, χ a i * G i j * χ a j| ≤ gamma2Norm G`. -/
theorem sum_abs_flat_orthogonal_pairing_le_gamma2Norm [Nonempty m] (G : Matrix m m ℝ)
    (χ : κ → m → ℝ) (hmod : ∀ a i, |χ a i| = 1)
    (horth : ∀ a b, a ≠ b → ∑ i : m, χ a i * χ b i = 0) :
    ∑ a : κ, |(∑ i : m, ∑ j : m, χ a i * G i j * χ a j) / (Fintype.card m : ℝ) ^ 2| ≤
      gamma2Norm G := by
  set N : ℝ := (Fintype.card m : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hχsq : ∀ a i, χ a i ^ 2 = 1 := fun a i ↦ by rw [← sq_abs, hmod, one_pow]
  let e : κ → m → ℝ := fun a i ↦ χ a i / √N
  have he_bessel : ∀ x : m → ℝ, ∑ a : κ, (∑ i : m, e a i * x i) ^ 2 ≤ ∑ i : m, x i ^ 2 := by
    refine bessel_of_suborthonormal e (fun a b hab ↦ ?_) (fun a ↦ ?_)
    · calc ∑ i : m, e a i * e b i
          = (∑ i : m, χ a i * χ b i) / N := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl (fun i _ ↦ by
              simp only [e, div_mul_div_comm, Real.mul_self_sqrt hN.le])
        _ = 0 := by rw [horth a b hab, zero_div]
    · refine le_of_eq ?_
      calc ∑ i : m, e a i ^ 2
          = (∑ i : m, χ a i ^ 2) / N := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl (fun i _ ↦ by simp [e, div_pow, Real.sq_sqrt hN.le])
        _ = 1 := by simp [hχsq, N]
  have hpair := sum_abs_bilinear_le_sqrt_card_mul_gamma2Norm G e e he_bessel he_bessel
  rw [Real.sqrt_mul_self hN.le] at hpair
  have hlhs : ∑ a : κ, |∑ i : m, ∑ j : m, e a i * G i j * e a j| =
      N * ∑ a : κ, |(∑ i : m, ∑ j : m, χ a i * G i j * χ a j) / N ^ 2| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    have hinner : ∑ i : m, ∑ j : m, e a i * G i j * e a j =
        (∑ i : m, ∑ j : m, χ a i * G i j * χ a j) / N := by
      simp_rw [Finset.sum_div, e]
      refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ ?_))
      have hsq : √N * √N = N := Real.mul_self_sqrt hN.le
      calc χ a i / √N * G i j * (χ a j / √N)
          = χ a i * G i j * χ a j / (√N * √N) := by ring
        _ = χ a i * G i j * χ a j / N := by rw [hsq]
    rw [hinner, abs_div, abs_div, abs_of_pos hN, abs_of_pos (sq_pos_of_pos hN)]
    field_simp [hN.ne']
  rw [hlhs] at hpair
  exact le_of_mul_le_mul_left hpair hN

private theorem cube_sum_le_sq_sum_sqrt_mul_sum_sq {α : Type*} (s : Finset α) (lam : α → ℝ)
    (hlam : ∀ a ∈ s, 0 ≤ lam a) :
    (∑ a ∈ s, lam a) ^ 3 ≤ (∑ a ∈ s, √(lam a)) ^ 2 * (∑ a ∈ s, lam a ^ 2) := by
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  let f : α → ℝ := fun a ↦ lam a ^ (1 / 3 : ℝ)
  let g : α → ℝ := fun a ↦ lam a ^ (2 / 3 : ℝ)
  have hf : ∀ a ∈ s, 0 ≤ f a := fun a ha ↦ Real.rpow_nonneg (hlam a ha) _
  have hg : ∀ a ∈ s, 0 ≤ g a := fun a ha ↦ Real.rpow_nonneg (hlam a ha) _
  have hholder := Real.inner_le_Lp_mul_Lq s f g hpq
  have hfg : ∑ a ∈ s, f a * g a = ∑ a ∈ s, lam a := by
    refine Finset.sum_congr rfl (fun a ha ↦ ?_)
    dsimp only [f, g]
    rw [← Real.rpow_add' (hlam a ha) (by norm_num)]
    norm_num
  have hfp : ∑ a ∈ s, |f a| ^ (3 / 2 : ℝ) = ∑ a ∈ s, √(lam a) := by
    refine Finset.sum_congr rfl (fun a ha ↦ ?_)
    rw [abs_of_nonneg (hf a ha), ← Real.rpow_mul (hlam a ha), Real.sqrt_eq_rpow]
    norm_num
  have hgq : ∑ a ∈ s, |g a| ^ (3 : ℝ) = ∑ a ∈ s, lam a ^ 2 := by
    refine Finset.sum_congr rfl (fun a ha ↦ ?_)
    rw [abs_of_nonneg (hg a ha), ← Real.rpow_mul (hlam a ha)]
    norm_num
  rw [hfg, hfp, hgq] at hholder
  have hsum_nn : 0 ≤ ∑ a ∈ s, lam a := Finset.sum_nonneg hlam
  have h1_nn : 0 ≤ ∑ a ∈ s, √(lam a) := Finset.sum_nonneg (fun _ _ ↦ Real.sqrt_nonneg _)
  have h2_nn : 0 ≤ ∑ a ∈ s, lam a ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  calc (∑ a ∈ s, lam a) ^ 3
      ≤ ((∑ a ∈ s, √(lam a)) ^ (1 / (3 / 2 : ℝ)) * (∑ a ∈ s, lam a ^ 2) ^ (1 / (3 : ℝ))) ^ 3 :=
        pow_le_pow_left₀ hsum_nn hholder 3
    _ = ((∑ a ∈ s, √(lam a)) ^ (1 / (3 / 2 : ℝ))) ^ (3 : ℝ) *
          ((∑ a ∈ s, lam a ^ 2) ^ (1 / (3 : ℝ))) ^ (3 : ℝ) := by
        rw [← Real.rpow_natCast,
          Real.mul_rpow (Real.rpow_nonneg h1_nn _) (Real.rpow_nonneg h2_nn _)]
        norm_num
    _ = (∑ a ∈ s, √(lam a)) ^ 2 * (∑ a ∈ s, lam a ^ 2) := by
        rw [← Real.rpow_mul h1_nn, ← Real.rpow_mul h2_nn]
        norm_num

/-- `trace ((Mᵀ * M) * (Mᵀ * M))` equals the four-cycle entry sum
`∑ i₁, ∑ i₂, ∑ j₁, ∑ j₂, M i₁ j₁ * M i₁ j₂ * M i₂ j₁ * M i₂ j₂`. -/
theorem trace_transpose_mul_self_sq (M : Matrix m n ℝ) :
    ((Mᵀ * M) * (Mᵀ * M)).trace =
      ∑ i₁ : m, ∑ i₂ : m, ∑ j₁ : n, ∑ j₂ : n, M i₁ j₁ * M i₁ j₂ * M i₂ j₁ * M i₂ j₂ := by
  calc ((Mᵀ * M) * (Mᵀ * M)).trace
      = ∑ j₁ : n, ∑ j₂ : n, ∑ i₁ : m, ∑ i₂ : m, M i₁ j₁ * M i₁ j₂ * M i₂ j₁ * M i₂ j₂ := by
        simp only [_root_.Matrix.trace, _root_.Matrix.diag_apply, _root_.Matrix.mul_apply,
          _root_.Matrix.transpose_apply]
        refine Finset.sum_congr rfl (fun j₁ _ ↦ Finset.sum_congr rfl (fun j₂ _ ↦ ?_))
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun i₁ _ ↦ Finset.sum_congr rfl (fun i₂ _ ↦ by ring))
    _ = ∑ j₁ : n, ∑ i₁ : m, ∑ i₂ : m, ∑ j₂ : n, M i₁ j₁ * M i₁ j₂ * M i₂ j₁ * M i₂ j₂ := by
        refine Finset.sum_congr rfl (fun j₁ _ ↦ ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i₁ _ ↦ Finset.sum_comm)
    _ = ∑ i₁ : m, ∑ i₂ : m, ∑ j₁ : n, ∑ j₂ : n, M i₁ j₁ * M i₁ j₂ * M i₂ j₁ * M i₂ j₂ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i₁ _ ↦ Finset.sum_comm)

/-- `trace ((Mᵀ * M) * (Mᵀ * M))` is always nonnegative (it is `frobeniusNorm (Mᵀ * M) ^ 2`). -/
theorem trace_transpose_mul_self_sq_nonneg (M : Matrix m n ℝ) :
    0 ≤ ((Mᵀ * M) * (Mᵀ * M)).trace := by
  have heq : ((Mᵀ * M) * (Mᵀ * M)).trace = frobeniusNorm (Mᵀ * M) ^ 2 := by
    rw [sq_frobeniusNorm_eq_trace, _root_.Matrix.transpose_mul, _root_.Matrix.transpose_transpose]
  rw [heq]
  exact sq_nonneg _

/-- `trace ((Mᵀ * M) * (Mᵀ * M))` is strictly positive for every nonzero real matrix `M`. -/
theorem trace_transpose_mul_self_sq_pos {M : Matrix m n ℝ} (hM : M ≠ 0) :
    0 < ((Mᵀ * M) * (Mᵀ * M)).trace := by
  have heq : ((Mᵀ * M) * (Mᵀ * M)).trace = frobeniusNorm (Mᵀ * M) ^ 2 := by
    rw [sq_frobeniusNorm_eq_trace, _root_.Matrix.transpose_mul, _root_.Matrix.transpose_transpose]
  rw [heq]
  apply sq_pos_of_ne_zero
  rw [ne_eq, frobeniusNorm_eq_zero]
  intro hzero
  apply hM
  rw [← frobeniusNorm_eq_zero]
  have hsq : frobeniusNorm M ^ 2 = 0 := by
    rw [sq_frobeniusNorm_eq_trace, hzero, _root_.Matrix.trace_zero]
  exact sq_eq_zero_iff.mp hsq

/-- **Multiplicative Hölder fourth-moment lower bound on `gamma2Norm`**
: for every rectangular finite real matrix
`M : Matrix m n ℝ`,
`frobeniusNorm M ^ 3 ≤ √(card m * card n) * gamma2Norm M * √(((Mᵀ * M) * (Mᵀ * M)).trace)`.
-/
theorem frobeniusNorm_cube_le_sqrt_card_mul_gamma2Norm_mul_sqrt_trace (M : Matrix m n ℝ) :
    frobeniusNorm M ^ 3 ≤
      √((Fintype.card m : ℝ) * Fintype.card n) * gamma2Norm M *
        √(((Mᵀ * M) * (Mᵀ * M)).trace) := by
  classical
  set S : Matrix n n ℝ := Mᵀ * M
  have hPSD : S.PosSemidef := _root_.Matrix.posSemidef_conjTranspose_mul_self M
  have hS : S.IsHermitian := hPSD.isHermitian
  let b := hS.eigenvectorBasis
  let lam : n → ℝ := hS.eigenvalues
  have hlam_nn : ∀ a : n, 0 ≤ lam a := hPSD.eigenvalues_nonneg
  let v : n → n → ℝ := fun a j ↦ (b a).ofLp j
  have hv_orth : ∀ a c : n, ∑ j : n, v a j * v c j = if a = c then 1 else 0 := by
    intro a c
    have hinner : @inner ℝ (EuclideanSpace ℝ n) _ (b a) (b c) = ∑ j : n, v a j * v c j := by
      simp [PiLp.inner_apply, v, mul_comm]
    rw [← hinner]
    by_cases hac : a = c
    · subst hac
      simp [b.orthonormal.1 a]
    · simp [hac, b.orthonormal.2 hac]
  have hv_eig : ∀ a : n, S *ᵥ v a = lam a • v a := fun a ↦ hS.mulVec_eigenvectorBasis a
  have hMv_inner : ∀ a c : n, ∑ i : m, (M *ᵥ v a) i * (M *ᵥ v c) i =
      if a = c then lam a else 0 := by
    intro a c
    have hdot : (M *ᵥ v a) ⬝ᵥ (M *ᵥ v c) = v a ⬝ᵥ (S *ᵥ v c) := by
      calc (M *ᵥ v a) ⬝ᵥ (M *ᵥ v c)
          = ∑ i : m, ∑ k : n, ∑ j : n, v a k * M i k * M i j * v c j := by
            simp only [dotProduct, _root_.Matrix.mulVec]
            refine Finset.sum_congr rfl (fun i _ ↦ ?_)
            rw [Finset.sum_mul_sum]
            exact Finset.sum_congr rfl (fun k _ ↦ Finset.sum_congr rfl (fun j _ ↦ by ring))
        _ = ∑ k : n, ∑ i : m, ∑ j : n, v a k * M i k * M i j * v c j := Finset.sum_comm
        _ = v a ⬝ᵥ (S *ᵥ v c) := by
            rw [show S *ᵥ v c = Mᵀ *ᵥ (M *ᵥ v c) from (_root_.Matrix.mulVec_mulVec _ _ _).symm]
            simp only [dotProduct, _root_.Matrix.mulVec, _root_.Matrix.transpose_apply]
            refine Finset.sum_congr rfl (fun k _ ↦ ?_)
            simp_rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ by ring))
    change (M *ᵥ v a) ⬝ᵥ (M *ᵥ v c) = _
    rw [hdot, hv_eig c, dotProduct_smul, smul_eq_mul]
    change lam c * ∑ j : n, v a j * v c j = _
    rw [hv_orth a c]
    by_cases hac : a = c
    · subst hac; simp
    · simp [hac]
  -- Step 1: Build left singular vectors `e a` and verify Bessel's inequality for `e` and `v`.
  let e : n → m → ℝ := fun a i ↦ if lam a = 0 then 0 else (M *ᵥ v a) i / √(lam a)
  have he_bessel : ∀ x : m → ℝ, ∑ a : n, (∑ i : m, e a i * x i) ^ 2 ≤ ∑ i : m, x i ^ 2 := by
    refine bessel_of_suborthonormal e (fun a c hac ↦ ?_) (fun a ↦ ?_)
    · by_cases ha : lam a = 0
      · simp [e, ha]
      · by_cases hc : lam c = 0
        · simp [e, hc]
        · simp only [e, ha, hc, ↓reduceIte]
          calc ∑ i : m, (M *ᵥ v a) i / √(lam a) * ((M *ᵥ v c) i / √(lam c))
              = (∑ i : m, (M *ᵥ v a) i * (M *ᵥ v c) i) / (√(lam a) * √(lam c)) := by
                rw [Finset.sum_div]
                exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
            _ = 0 := by simp [hMv_inner a c, hac]
    · by_cases ha : lam a = 0
      · simp [e, ha]
      · have hpos : 0 < lam a := (hlam_nn a).lt_of_ne' ha
        refine le_of_eq ?_
        simp only [e, ha, ↓reduceIte]
        calc ∑ i : m, ((M *ᵥ v a) i / √(lam a)) ^ 2
            = (∑ i : m, (M *ᵥ v a) i * (M *ᵥ v a) i) / lam a := by
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl (fun _ _ ↦ ?_)
              rw [div_pow, Real.sq_sqrt hpos.le, sq]
          _ = 1 := by simp [hMv_inner a a, div_self ha]
  have hv_bessel : ∀ y : n → ℝ, ∑ a : n, (∑ j : n, v a j * y j) ^ 2 ≤ ∑ j : n, y j ^ 2 := by
    refine bessel_of_suborthonormal v (fun a c hac ↦ by simp [hv_orth, hac]) (fun a ↦ ?_)
    simp [sq, hv_orth]
  -- Step 2: Apply the Bessel pairing bound to obtain `∑ √(lam a) ≤ √(|m| |n|) * gamma2Norm M`.
  have htrace_norm : ∑ a : n, √(lam a) ≤
      √((Fintype.card m : ℝ) * Fintype.card n) * gamma2Norm M := by
    refine le_trans (le_of_eq ?_)
      (sum_abs_bilinear_le_sqrt_card_mul_gamma2Norm M e v he_bessel hv_bessel)
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    have hval : ∑ i : m, ∑ j : n, e a i * M i j * v a j = √(lam a) := by
      by_cases ha : lam a = 0
      · simp [e, ha]
      · simp only [e, ha, ↓reduceIte]
        calc ∑ i : m, ∑ j : n, ((M *ᵥ v a) i / √(lam a)) * M i j * v a j
            = (∑ i : m, (M *ᵥ v a) i * (M *ᵥ v a) i) / √(lam a) := by
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl (fun i _ ↦ ?_)
              calc ∑ j : n, (M *ᵥ v a) i / √(lam a) * M i j * v a j
                  = (M *ᵥ v a) i * (∑ j : n, M i j * v a j) / √(lam a) := by
                    rw [Finset.mul_sum, Finset.sum_div]
                    exact Finset.sum_congr rfl (fun j _ ↦ by ring)
                _ = (M *ᵥ v a) i * (M *ᵥ v a) i / √(lam a) := rfl
          _ = lam a / √(lam a) := by simp [hMv_inner a a]
          _ = √(lam a) := Real.div_sqrt
    rw [hval, abs_of_nonneg (Real.sqrt_nonneg _)]
  -- Step 3: Relate `∑ lam a` to `frobeniusNorm M ^ 2` and `∑ lam a ^ 2` to `trace (S * S)`.
  have hsum_lam : ∑ a : n, lam a = frobeniusNorm M ^ 2 := by
    rw [sq_frobeniusNorm_eq_trace]
    exact hS.trace_eq_sum_eigenvalues.symm
  have hsum_lam_sq : ∑ a : n, lam a ^ 2 = (S * S).trace := by
    have hparseval : ∀ j : n, (S * S) j j = ∑ a : n, lam a ^ 2 * v a j ^ 2 := by
      intro j
      let ej : EuclideanSpace ℝ n := EuclideanSpace.single j 1
      have hrepr : ∀ x : EuclideanSpace ℝ n,
          @inner ℝ (EuclideanSpace ℝ n) _ ej x = x.ofLp j := by
        intro x
        simp [ej, EuclideanSpace.inner_single_left]
      have hexp := b.sum_repr ej
      have hcoeff : ∀ a : n, b.repr ej a = v a j := by
        intro a
        rw [OrthonormalBasis.repr_apply_apply, real_inner_comm, hrepr]
      have hS2v : ∀ a : n, (S * S) *ᵥ v a = (lam a ^ 2) • v a := by
        intro a
        rw [← _root_.Matrix.mulVec_mulVec, hv_eig, _root_.Matrix.mulVec_smul, hv_eig,
          smul_smul, sq]
      have hej_sum : ∀ k : n, (if k = j then (1 : ℝ) else 0) = ∑ a : n, v a j * v a k := by
        intro k
        have hk := congr_arg (fun x : EuclideanSpace ℝ n ↦ x.ofLp k) hexp
        have hlhs : (∑ a : n, b.repr ej a • b a).ofLp k = ∑ a : n, v a j * v a k := by
          simp [hcoeff, v]
        have hrhs : ej.ofLp k = if k = j then (1 : ℝ) else 0 := by
          simp [ej]
        linarith
      calc (S * S) j j
          = ∑ k : n, (S * S) j k * (if k = j then 1 else 0) := by simp
        _ = ∑ k : n, (S * S) j k * ∑ a : n, v a j * v a k := by simp_rw [hej_sum]
        _ = ∑ a : n, v a j * ((S * S) *ᵥ v a) j := by
            simp_rw [Finset.mul_sum, _root_.Matrix.mulVec, dotProduct, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun a _ ↦ Finset.sum_congr rfl (fun k _ ↦ by ring))
        _ = ∑ a : n, lam a ^ 2 * v a j ^ 2 := by
            refine Finset.sum_congr rfl (fun a _ ↦ ?_)
            rw [hS2v a]
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
    rw [_root_.Matrix.trace]
    simp_rw [_root_.Matrix.diag_apply, hparseval]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    rw [← Finset.mul_sum]
    have hv1 : ∑ j : n, v a j ^ 2 = 1 := by simpa [sq] using hv_orth a a
    rw [hv1, mul_one]
  -- Step 4: Combine with the Hölder cube inequality and extract square roots.
  have hcube := cube_sum_le_sq_sum_sqrt_mul_sum_sq Finset.univ lam (fun a _ ↦ hlam_nn a)
  rw [hsum_lam, hsum_lam_sq] at hcube
  have hsq : (frobeniusNorm M ^ 3) ^ 2 ≤
      ((∑ a : n, √(lam a)) * √((S * S).trace)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (trace_transpose_mul_self_sq_nonneg M)]
    linarith [show (frobeniusNorm M ^ 2) ^ 3 = (frobeniusNorm M ^ 3) ^ 2 by ring]
  have hroot : frobeniusNorm M ^ 3 ≤ (∑ a : n, √(lam a)) * √((S * S).trace) := by
    have hrhs_nn : 0 ≤ (∑ a : n, √(lam a)) * √((S * S).trace) :=
      mul_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact (abs_le_of_sq_le_sq' hsq hrhs_nn).2
  exact hroot.trans
    (mul_le_mul_of_nonneg_right htrace_norm (Real.sqrt_nonneg _))

/-- **Hölder fourth-moment trace lower bound on `gamma2Norm` for rectangular matrices**:
`frobeniusNorm M ^ 3 / (√(card m * card n) * √(((Mᵀ * M) * (Mᵀ * M)).trace)) ≤ gamma2Norm M`. -/
theorem frobeniusNorm_cube_div_sqrt_card_le_gamma2Norm (M : Matrix m n ℝ) :
    frobeniusNorm M ^ 3 /
        (√((Fintype.card m : ℝ) * Fintype.card n) * √(((Mᵀ * M) * (Mᵀ * M)).trace)) ≤
      gamma2Norm M := by
  set D := √((Fintype.card m : ℝ) * Fintype.card n) * √(((Mᵀ * M) * (Mᵀ * M)).trace)
  have hD : 0 ≤ D := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases hD.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    exact gamma2Norm_nonneg M
  · rw [div_le_iff₀ hpos]
    calc frobeniusNorm M ^ 3
        ≤ √((Fintype.card m : ℝ) * Fintype.card n) * gamma2Norm M *
            √(((Mᵀ * M) * (Mᵀ * M)).trace) :=
          frobeniusNorm_cube_le_sqrt_card_mul_gamma2Norm_mul_sqrt_trace M
      _ = gamma2Norm M * D := by ring

/-- **Hölder fourth-moment trace lower bound on `gamma2Norm` for square matrices**
: for every `M : Matrix n n ℝ`,
`(1 / card n) * (frobeniusNorm M ^ 3 / √(((Mᵀ * M) * (Mᵀ * M)).trace)) ≤ gamma2Norm M`.
-/
theorem frobeniusNorm_cube_div_le_gamma2Norm (M : Matrix n n ℝ) :
    (1 / (Fintype.card n : ℝ)) * (frobeniusNorm M ^ 3 / √(((Mᵀ * M) * (Mᵀ * M)).trace)) ≤
      gamma2Norm M := by
  have h := frobeniusNorm_cube_div_sqrt_card_le_gamma2Norm M
  rw [Real.sqrt_mul_self (Nat.cast_nonneg _)] at h
  rwa [one_div_mul_eq_div, div_div, mul_comm (√(((Mᵀ * M) * (Mᵀ * M)).trace))]

-- Non-vacuity check on the `2 × 2` Hadamard matrix `[[1, 1], [1, -1]]`: `γ₂ ≥ √2 > 1`.
example : gamma2Norm (_root_.Matrix.of fun i j : Fin 2 ↦
    if i = 1 ∧ j = 1 then (-1 : ℝ) else 1) ≥ √2 := by
  let H : Matrix (Fin 2) (Fin 2) ℝ :=
    _root_.Matrix.of fun i j ↦ if i = 1 ∧ j = 1 then -1 else 1
  have hF : frobeniusNorm H ^ 2 = 4 := by
    rw [sq_frobeniusNorm, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [H]
  have hFval : frobeniusNorm H = 2 := by
    nlinarith [frobeniusNorm_nonneg H]
  have hHTH : Hᵀ * H = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [H, _root_.Matrix.mul_apply, Fin.sum_univ_two, Function.swap]
  have htr : ((Hᵀ * H) * (Hᵀ * H)).trace = 8 := by
    rw [hHTH, smul_mul_smul_comm, mul_one, _root_.Matrix.trace_smul,
      _root_.Matrix.trace_one]
    norm_num
  have hbound := frobeniusNorm_cube_div_le_gamma2Norm H
  rw [hFval, htr, Fintype.card_fin] at hbound
  have hsqrt8 : √(8 : ℝ) = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [hsqrt8] at hbound
  have hcalc : (1 / (2 : ℝ)) * ((2 : ℝ) ^ 3 / (2 * √2)) = √2 := by
    have h2 : √(2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp [h2]
    rw [Real.sq_sqrt (by norm_num)]
  linarith

end SpectralAndHolder

end CslibFrontier.Matrix
