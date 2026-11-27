/-
Copyright (c) 2026 FormalPapers Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.PolarDecomposition

import CslibFrontier.Foundations.LinearAlgebra.Matrix.BlockDiagonalOrder
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Matrix Norms for Quantum Communication Complexity

This module defines the standard real matrix norms used in the pattern-matrix and factorization-norm
methods for quantum communication complexity: the entrywise $\ell_1$ norm, the Frobenius inner
product, the Frobenius norm, the spectral ($\ell^2$ operator) norm, and the real trace (nuclear)
norm, and proves the two fundamental inequalities:

1. `CslibFrontier.CommunicationComplexity.realTraceNorm_mul_le_frobeniusNorm`:
   $\|A B\|_\Sigma \le \|A\|_F \|B\|_F$.
2. `CslibFrontier.CommunicationComplexity.matrixInner_le_realTraceNorm_mul_spectralNorm`:
   $\langle A, B \rangle \le \|A\|_\Sigma \|B\|$.

## Main definitions

* `CslibFrontier.CommunicationComplexity.matrixL1Norm`: entrywise $\ell_1$ norm $\|A\|_1$.
* `CslibFrontier.CommunicationComplexity.matrixInner`: Frobenius inner product $\langle A, B
  \rangle$.
* `CslibFrontier.CommunicationComplexity.frobeniusNorm`: Frobenius norm $\|A\|_F$.
* `CslibFrontier.CommunicationComplexity.spectralNorm`: spectral ($\ell^2$ operator) norm $\|A\|$.
* `CslibFrontier.CommunicationComplexity.realTraceNorm`: trace (nuclear) norm $\|A\|_\Sigma$.

## Main results

* `CslibFrontier.CommunicationComplexity.realTraceNorm_mul_le_frobeniusNorm`:
  $\|A B\|_\Sigma \le \|A\|_F \|B\|_F$.
* `CslibFrontier.CommunicationComplexity.matrixInner_le_realTraceNorm_mul_spectralNorm`:
  $\langle A, B \rangle \le \|A\|_\Sigma \|B\|$.
-/

public section

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Finset Matrix

namespace CslibFrontier.CommunicationComplexity

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Entrywise $\ell_1$ norm of a real matrix: $\|A\|_1 = \sum_{x, y} |A_{x, y}|$. -/
noncomputable def matrixL1Norm (A : Matrix X Y ℝ) : ℝ :=
  ∑ x, ∑ y, |A x y|

/-- Frobenius inner product of two real matrices:
$\langle A, B \rangle = \sum_{x, y} A_{x,y} B_{x,y}$. -/
noncomputable def matrixInner (A B : Matrix X Y ℝ) : ℝ :=
  ∑ x, ∑ y, A x y * B x y

/-- Frobenius norm of a real matrix: $\|A\|_F = \sqrt{\sum_{x, y} A_{x, y}^2}$. -/
noncomputable def frobeniusNorm (A : Matrix X Y ℝ) : ℝ :=
  Real.sqrt (∑ x, ∑ y, A x y ^ 2)

/-- Spectral ($\ell^2$ operator) norm of a real matrix. -/
noncomputable def spectralNorm [DecidableEq Y] (A : Matrix X Y ℝ) : ℝ :=
  ‖A‖

/-- Trace (nuclear) norm of a real matrix, defined via the complex lift `Matrix.traceNorm`. -/
noncomputable def realTraceNorm [DecidableEq Y] (A : Matrix X Y ℝ) : ℝ :=
  (A.map (Complex.ofReal : ℝ → ℂ)).traceNorm

lemma matrixL1Norm_eq_sum (A : Matrix X Y ℝ) :
    matrixL1Norm A = ∑ x, ∑ y, |A x y| := by rfl

@[simp]
lemma matrixL1Norm_zero : matrixL1Norm (0 : Matrix X Y ℝ) = 0 := by
  simp [matrixL1Norm]

@[simp]
lemma matrixL1Norm_neg (A : Matrix X Y ℝ) : matrixL1Norm (-A) = matrixL1Norm A := by
  simp [matrixL1Norm]

lemma matrixL1Norm_smul (c : ℝ) (A : Matrix X Y ℝ) :
    matrixL1Norm (c • A) = |c| * matrixL1Norm A := by
  simp [matrixL1Norm, abs_mul, Finset.mul_sum]

lemma matrixL1Norm_nonneg (A : Matrix X Y ℝ) : 0 ≤ matrixL1Norm A := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma matrixInner_eq_sum (A B : Matrix X Y ℝ) :
    matrixInner A B = ∑ x, ∑ y, A x y * B x y := by rfl

@[simp]
lemma matrixInner_zero_left (B : Matrix X Y ℝ) :
    matrixInner (0 : Matrix X Y ℝ) B = 0 := by
  simp [matrixInner]

@[simp]
lemma matrixInner_zero_right (A : Matrix X Y ℝ) :
    matrixInner A (0 : Matrix X Y ℝ) = 0 := by
  simp [matrixInner]

@[simp]
lemma matrixInner_neg_right (A B : Matrix X Y ℝ) :
    matrixInner A (-B) = -matrixInner A B := by
  simp [matrixInner, mul_neg, Finset.sum_neg_distrib]

lemma matrixInner_comm (A B : Matrix X Y ℝ) :
    matrixInner A B = matrixInner B A := by
  simp only [matrixInner, mul_comm]

lemma frobeniusNorm_eq_sqrt_sum (A : Matrix X Y ℝ) :
    frobeniusNorm A = Real.sqrt (∑ x, ∑ y, A x y ^ 2) := by rfl

@[simp]
lemma frobeniusNorm_zero : frobeniusNorm (0 : Matrix X Y ℝ) = 0 := by
  simp [frobeniusNorm]

lemma frobeniusNorm_nonneg (A : Matrix X Y ℝ) : 0 ≤ frobeniusNorm A := by
  exact Real.sqrt_nonneg _

lemma sq_frobeniusNorm (A : Matrix X Y ℝ) :
    frobeniusNorm A ^ 2 = ∑ x, ∑ y, A x y ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma spectralNorm_eq_opNorm [DecidableEq Y] (A : Matrix X Y ℝ) :
    spectralNorm A = ‖A‖ := by rfl

@[simp]
lemma spectralNorm_zero [DecidableEq Y] :
    spectralNorm (0 : Matrix X Y ℝ) = 0 := by
  exact norm_zero

@[simp]
lemma spectralNorm_neg [DecidableEq Y] (A : Matrix X Y ℝ) :
    spectralNorm (-A) = spectralNorm A := by
  exact norm_neg A

lemma spectralNorm_nonneg [DecidableEq Y] (A : Matrix X Y ℝ) : 0 ≤ spectralNorm A := by
  exact norm_nonneg A

lemma spectralNorm_smul [DecidableEq Y] (c : ℝ) (A : Matrix X Y ℝ) :
    spectralNorm (c • A) = |c| * spectralNorm A := by
  simpa [spectralNorm, Real.norm_eq_abs] using norm_smul c A

lemma spectralNorm_mulVec_le [DecidableEq Y] (A : Matrix X Y ℝ) (v : EuclideanSpace ℝ Y) :
    ‖Matrix.toEuclideanLin A v‖ ≤ spectralNorm A * ‖v‖ := by
  simpa [spectralNorm, Matrix.toLpLin_apply] using Matrix.l2_opNorm_mulVec A v

lemma spectralNorm_le_of_mulVec_le [DecidableEq Y] {A : Matrix X Y ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : EuclideanSpace ℝ Y, ‖Matrix.toEuclideanLin A v‖ ≤ c * ‖v‖) :
    spectralNorm A ≤ c := by
  rw [spectralNorm, Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hc h

omit [Fintype X] [Fintype Y] in
/-- Lifting a real matrix to `ℂ` preserves multiplication. -/
private lemma map_ofReal_mul (A : Matrix X Z ℝ) (B : Matrix Z Y ℝ) :
    (A * B).map (Complex.ofReal : ℝ → ℂ) =
      A.map (Complex.ofReal : ℝ → ℂ) * B.map (Complex.ofReal : ℝ → ℂ) := by
  ext x y
  simp [Matrix.mul_apply, Complex.ofReal_sum]

/-- Trace norm of an off-diagonal block matrix `fromBlocks 0 C 0 0` equals `C.traceNorm`. -/
private lemma traceNorm_fromBlocks_zero_left [DecidableEq X] [DecidableEq Y] (C : Matrix X Y ℂ) :
    (Matrix.fromBlocks (0 : Matrix X X ℂ) C (0 : Matrix Y X ℂ) (0 : Matrix Y Y ℂ)).traceNorm =
      C.traceNorm := by
  let M : Matrix (X ⊕ Y) (X ⊕ Y) ℂ := Matrix.fromBlocks 0 C 0 0
  have hMM : Mᴴ * M = Matrix.fromBlocks (0 : Matrix X X ℂ) 0 0 (Cᴴ * C) := by
    simp [M, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  have hsqrt : CFC.sqrt (Mᴴ * M) =
      Matrix.fromBlocks (0 : Matrix X X ℂ) 0 0 (CFC.sqrt (Cᴴ * C)) := by
    rw [hMM]
    refine CFC.sqrt_unique ?_ ?_
    · simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
        CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self C).nonneg]
    · have hpsd : (Matrix.fromBlocks (0 : Matrix X X ℂ) 0 0 (CFC.sqrt (Cᴴ * C))).PosSemidef :=
        Matrix.fromBlocks_posSemidef_diagonal 0 (CFC.sqrt (Cᴴ * C)) Matrix.PosSemidef.zero
          (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Cᴴ * C)))
      exact hpsd.nonneg
  change (CFC.sqrt (Mᴴ * M)).trace.re = (CFC.sqrt (Cᴴ * C)).trace.re
  rw [hsqrt]
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- Complex Euclidean operator norm of a real matrix lifted to `ℂ` is bounded by `spectralNorm`. -/
private lemma norm_mulVec_ofReal_le [DecidableEq Y] (B : Matrix X Y ℝ)
    (w : EuclideanSpace ℂ Y) :
    ‖(B.map (Complex.ofReal : ℝ → ℂ)).toEuclideanLin w‖ ≤ spectralNorm B * ‖w‖ := by
  have hsq : ‖(B.map (Complex.ofReal : ℝ → ℂ)).toEuclideanLin w‖ ^ 2 ≤
      (spectralNorm B * ‖w‖) ^ 2 := by
    let wre : EuclideanSpace ℝ Y := WithLp.toLp 2 fun y => (w.ofLp y).re
    let wim : EuclideanSpace ℝ Y := WithLp.toLp 2 fun y => (w.ofLp y).im
    have hsplit : ‖(B.map (Complex.ofReal : ℝ → ℂ)).toEuclideanLin w‖ ^ 2 =
        ‖Matrix.toEuclideanLin B wre‖ ^ 2 + ‖Matrix.toEuclideanLin B wim‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
        Matrix.map_apply, Real.norm_eq_abs, sq_abs, wre, wim]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hre : (∑ y, (B x y : ℂ) * w.ofLp y).re = ∑ y, B x y * (w.ofLp y).re := by
        simp [Complex.re_sum]
      have him : (∑ y, (B x y : ℂ) * w.ofLp y).im = ∑ y, B x y * (w.ofLp y).im := by
        simp [Complex.im_sum]
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
    have hw_split : ‖w‖ ^ 2 = ‖wre‖ ^ 2 + ‖wim‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, wre, wim]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h1sq : ‖Matrix.toEuclideanLin B wre‖ ^ 2 ≤ (spectralNorm B * ‖wre‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (spectralNorm_mulVec_le B wre) 2
    have h2sq : ‖Matrix.toEuclideanLin B wim‖ ^ 2 ≤ (spectralNorm B * ‖wim‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (spectralNorm_mulVec_le B wim) 2
    rw [hsplit, mul_pow, hw_split]
    nlinarith [h1sq, h2sq]
  have hrhs : 0 ≤ spectralNorm B * ‖w‖ := mul_nonneg (spectralNorm_nonneg B) (norm_nonneg w)
  nlinarith [sq_nonneg (‖(B.map (Complex.ofReal : ℝ → ℂ)).toEuclideanLin w‖ - spectralNorm B * ‖w‖),
    norm_nonneg ((B.map (Complex.ofReal : ℝ → ℂ)).toEuclideanLin w)]

/-- Unitary matrices preserve the complex Euclidean norm. -/
private lemma norm_toEuclideanLin_conjTranspose_of_unitary {ι : Type*} [Fintype ι]
    [DecidableEq ι] {U : Matrix ι ι ℂ} (hU : U ∈ unitaryGroup ι ℂ) (w : EuclideanSpace ℂ ι) :
    ‖Uᴴ.toEuclideanLin w‖ = ‖w‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  have heq : inner ℂ (Uᴴ.toEuclideanLin w) (Uᴴ.toEuclideanLin w) =
      inner ℂ w ((U * Uᴴ).toEuclideanLin w) := by
    calc inner ℂ (Uᴴ.toEuclideanLin w) (Uᴴ.toEuclideanLin w)
        = inner ℂ (U.toEuclideanLin.adjoint w) (Uᴴ.toEuclideanLin w) := by
          rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      _ = inner ℂ w (U.toEuclideanLin (Uᴴ.toEuclideanLin w)) := LinearMap.adjoint_inner_left _ _ _
      _ = inner ℂ w ((U * Uᴴ).toEuclideanLin w) := by
          change _ = inner ℂ w (Matrix.toLpLin 2 2 (U * Uᴴ) w)
          rw [Matrix.toLpLin_mul_same]; rfl
  rw [heq, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp hU]
  simp

/-- The lower-left subblock of a unitary matrix is contractive in the Euclidean norm. -/
private lemma sum_norm_sq_unitary_subblock_le [DecidableEq X] [DecidableEq Y]
    {U : Matrix (X ⊕ Y) (X ⊕ Y) ℂ} (hU : U ∈ unitaryGroup (X ⊕ Y) ℂ) (w : X → ℂ) :
    ∑ y : Y, ‖((Matrix.of fun y x => Uᴴ (Sum.inr y) (Sum.inl x)) *ᵥ w) y‖ ^ 2 ≤
      ∑ x : X, ‖w x‖ ^ 2 := by
  let V : Matrix Y X ℂ := Matrix.of fun y x => Uᴴ (Sum.inr y) (Sum.inl x)
  let w' : EuclideanSpace ℂ (X ⊕ Y) := WithLp.toLp 2 (Sum.elim w (fun _ => 0))
  have hnorm : ‖Uᴴ.toEuclideanLin w'‖ ^ 2 = ‖w'‖ ^ 2 := by
    rw [norm_toEuclideanLin_conjTranspose_of_unitary hU w']
  have hlhs : ∑ y : Y, ‖(V *ᵥ w) y‖ ^ 2 ≤ ‖Uᴴ.toEuclideanLin w'‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
    have hge : ∑ y : Y, ‖(Uᴴ.toEuclideanLin w').ofLp (Sum.inr y)‖ ^ 2 ≤
        ∑ x : X, ‖(Uᴴ.toEuclideanLin w').ofLp (Sum.inl x)‖ ^ 2 +
        ∑ y : Y, ‖(Uᴴ.toEuclideanLin w').ofLp (Sum.inr y)‖ ^ 2 :=
      le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    refine le_trans (le_of_eq ?_) hge
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      w', Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero, V,
      Matrix.of_apply]
  have hrhs : ‖w'‖ ^ 2 = ∑ x : X, ‖w x‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, w']
  exact (hlhs.trans_eq hnorm).trans_eq hrhs

/-- Trace of `Uᴴ * fromBlocks 0 (Aℂ * Bℂ) 0 0` in terms of the lower-left subblock of `Uᴴ`. -/
private lemma trace_conjTranspose_fromBlocks_zero_left
    (U : Matrix (X ⊕ Y) (X ⊕ Y) ℂ) (Aℂ : Matrix X Z ℂ) (Bℂ : Matrix Z Y ℂ) :
    (Uᴴ * Matrix.fromBlocks (0 : Matrix X X ℂ) (Aℂ * Bℂ) 0 0).trace =
      ∑ y : Y, ∑ z : Z, ((Matrix.of fun y x => Uᴴ (Sum.inr y) (Sum.inl x)) * Aℂ) y z * Bℂ z y := by
  let V : Matrix Y X ℂ := Matrix.of fun y x => Uᴴ (Sum.inr y) (Sum.inl x)
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.mul_apply]
  have hX0 : ∑ x : X, (∑ x' : X, Uᴴ (Sum.inl x) (Sum.inl x') *
        (Matrix.fromBlocks (0 : Matrix X X ℂ) (Aℂ * Bℂ) (0 : Matrix Y X ℂ) (0 : Matrix Y Y ℂ))
          (Sum.inl x') (Sum.inl x) +
      ∑ y' : Y, Uᴴ (Sum.inl x) (Sum.inr y') *
        (Matrix.fromBlocks (0 : Matrix X X ℂ) (Aℂ * Bℂ) (0 : Matrix Y X ℂ) (0 : Matrix Y Y ℂ))
          (Sum.inr y') (Sum.inl x)) = 0 := by
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]
  rw [hX0, zero_add]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero, Matrix.mul_apply, Matrix.of_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => by ring

/-- **Trace norm of a product is bounded by the product of Frobenius norms**:
$\|A B\|_\Sigma \le \|A\|_F \|B\|_F$. -/
theorem realTraceNorm_mul_le_frobeniusNorm [DecidableEq Y]
    (A : Matrix X Z ℝ) (B : Matrix Z Y ℝ) :
    realTraceNorm (A * B) ≤ frobeniusNorm A * frobeniusNorm B := by
  classical
  let Aℂ : Matrix X Z ℂ := A.map (Complex.ofReal : ℝ → ℂ)
  let Bℂ : Matrix Z Y ℂ := B.map (Complex.ofReal : ℝ → ℂ)
  let M : Matrix (X ⊕ Y) (X ⊕ Y) ℂ := Matrix.fromBlocks 0 (Aℂ * Bℂ) 0 0
  have htr : realTraceNorm (A * B) = M.traceNorm := by
    rw [realTraceNorm, map_ofReal_mul, ← traceNorm_fromBlocks_zero_left]
  rw [htr]
  obtain ⟨U, hU, hUmax, _⟩ := M.traceNorm_eq_max_re_trace
  rw [← hUmax]
  let V : Matrix Y X ℂ := Matrix.of fun y x => Uᴴ (Sum.inr y) (Sum.inl x)
  have htrace_eq : (Uᴴ * M).trace = ∑ y : Y, ∑ z : Z, (V * Aℂ) y z * Bℂ z y :=
    trace_conjTranspose_fromBlocks_zero_left U Aℂ Bℂ
  have hVA_sq : ∑ y : Y, ∑ z : Z, ‖(V * Aℂ) y z‖ ^ 2 ≤ frobeniusNorm A ^ 2 := by
    rw [sq_frobeniusNorm, Finset.sum_comm]
    calc ∑ z : Z, ∑ y : Y, ‖(V * Aℂ) y z‖ ^ 2
        = ∑ z : Z, ∑ y : Y, ‖(V *ᵥ fun x => Aℂ x z) y‖ ^ 2 := by
          refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
          simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      _ ≤ ∑ z : Z, ∑ x : X, ‖Aℂ x z‖ ^ 2 :=
          Finset.sum_le_sum fun z _ => sum_norm_sq_unitary_subblock_le hU _
      _ = ∑ x : X, ∑ z : Z, A x z ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
          simp [Aℂ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hB_sq : ∑ y : Y, ∑ z : Z, ‖Bℂ z y‖ ^ 2 = frobeniusNorm B ^ 2 := by
    rw [sq_frobeniusNorm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    simp [Bℂ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [htrace_eq, Complex.re_sum]
  calc ∑ y : Y, (∑ z : Z, (V * Aℂ) y z * Bℂ z y).re
      ≤ ∑ y : Y, ∑ z : Z, ‖(V * Aℂ) y z‖ * ‖Bℂ z y‖ := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_le_sum fun z _ => ?_
        calc ((V * Aℂ) y z * Bℂ z y).re ≤ ‖(V * Aℂ) y z * Bℂ z y‖ := Complex.re_le_norm _
          _ = ‖(V * Aℂ) y z‖ * ‖Bℂ z y‖ := norm_mul _ _
    _ = ∑ p : Y × Z, ‖(V * Aℂ) p.1 p.2‖ * ‖Bℂ p.2 p.1‖ :=
        (Fintype.sum_prod_type fun p : Y × Z => ‖(V * Aℂ) p.1 p.2‖ * ‖Bℂ p.2 p.1‖).symm
    _ ≤ Real.sqrt (∑ p : Y × Z, ‖(V * Aℂ) p.1 p.2‖ ^ 2) *
          Real.sqrt (∑ p : Y × Z, ‖Bℂ p.2 p.1‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun p : Y × Z => ‖(V * Aℂ) p.1 p.2‖) (fun p : Y × Z => ‖Bℂ p.2 p.1‖)
    _ ≤ Real.sqrt (frobeniusNorm A ^ 2) * Real.sqrt (frobeniusNorm B ^ 2) := by
        rw [Fintype.sum_prod_type (fun p : Y × Z => ‖(V * Aℂ) p.1 p.2‖ ^ 2),
          Fintype.sum_prod_type (fun p : Y × Z => ‖Bℂ p.2 p.1‖ ^ 2), hB_sq]
        exact mul_le_mul (Real.sqrt_le_sqrt hVA_sq) le_rfl (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = frobeniusNorm A * frobeniusNorm B := by
        rw [Real.sqrt_sq (frobeniusNorm_nonneg A), Real.sqrt_sq (frobeniusNorm_nonneg B)]

/-- **Hölder / duality inequality for trace and spectral norms**:
$\langle A, B \rangle \le \|A\|_\Sigma \|B\|$. -/
theorem matrixInner_le_realTraceNorm_mul_spectralNorm [DecidableEq Y]
    (A B : Matrix X Y ℝ) :
    matrixInner A B ≤ realTraceNorm A * spectralNorm B := by
  classical
  let Aℂ : Matrix X Y ℂ := A.map (Complex.ofReal : ℝ → ℂ)
  let Bℂ : Matrix X Y ℂ := B.map (Complex.ofReal : ℝ → ℂ)
  let M : Matrix (X ⊕ Y) (X ⊕ Y) ℂ := Matrix.fromBlocks 0 Aℂ 0 0
  let N : Matrix (X ⊕ Y) (X ⊕ Y) ℂ := Matrix.fromBlocks 0 Bℂ 0 0
  have hinner_eq : matrixInner A B = (Mᴴ * N).trace.re := by
    have hMN : Mᴴ * N = Matrix.fromBlocks (0 : Matrix X X ℂ) 0 0 (Aℂᴴ * Bℂ) := by
      simp [M, N, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    rw [hMN]
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Finset.sum_const_zero, zero_add,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Aℂ, Bℂ, Matrix.map_apply, Complex.star_def,
      Complex.conj_ofReal, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, matrixInner]
    rw [Finset.sum_comm]
  have hM_norm : M.traceNorm = realTraceNorm A := traceNorm_fromBlocks_zero_left Aℂ
  obtain ⟨U, hU, hpolar⟩ := M.exists_unitary_polar
  let H : Matrix (X ⊕ Y) (X ⊕ Y) ℂ := CFC.sqrt (Mᴴ * M)
  have hH_psd : H.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Mᴴ * M))
  have hH_herm : H.IsHermitian := hH_psd.isHermitian
  let K : Matrix (X ⊕ Y) (X ⊕ Y) ℂ := Uᴴ * N
  have hMN_eq : (Mᴴ * N).trace = (K * H).trace := by
    have hM_eq : Mᴴ = H * Uᴴ := by
      rw [← hpolar, Matrix.conjTranspose_mul, hH_herm.eq]
    rw [hM_eq, Matrix.mul_assoc, Matrix.trace_mul_comm]
  let v := hH_herm.eigenvectorBasis
  let lam := hH_herm.eigenvalues
  have htrace_basis : ∀ C : Matrix (X ⊕ Y) (X ⊕ Y) ℂ,
      C.trace = ∑ i : X ⊕ Y, inner ℂ (v i) (C.toEuclideanLin (v i)) := by
    intro C
    let P : Matrix (X ⊕ Y) (X ⊕ Y) ℂ := Matrix.of fun p i => (v i).ofLp p
    have hP_unit : Pᴴ * P = 1 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, P, Matrix.of_apply,
        Matrix.one_apply]
      have hinner : inner ℂ (v i) (v j) = ∑ p, star ((v i).ofLp p) * (v j).ofLp p := by
        simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
      rw [← hinner]
      by_cases hij : i = j
      · subst hij; simp [v.orthonormal.1 i]
      · simp [hij, v.orthonormal.2 hij]
    have hP_unit' : P * Pᴴ = 1 := mul_eq_one_comm.mp hP_unit
    have htr_P : C.trace = (Pᴴ * C * P).trace := by
      rw [Matrix.trace_mul_cycle, hP_unit', Matrix.one_mul]
    rw [htr_P]
    simp only [Matrix.trace, Matrix.diag]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.toLpLin_apply,
      Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply, P, Matrix.of_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      change star ((v i).ofLp p) * C p q * (v i).ofLp q = C p q * (v i).ofLp q * star ((v i).ofLp p)
      ring
  have hKH_re : (K * H).trace.re =
      ∑ i : X ⊕ Y, lam i * (inner ℂ (v i) (K.toEuclideanLin (v i))).re := by
    rw [htrace_basis (K * H), Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hKH_v : (K * H).toEuclideanLin (v i) = (lam i : ℂ) • K.toEuclideanLin (v i) := by
      have h1 : (K * H).toEuclideanLin (v i) = K.toEuclideanLin (H.toEuclideanLin (v i)) := by
        change Matrix.toLpLin 2 2 (K * H) (v i) = _
        rw [Matrix.toLpLin_mul_same]; rfl
      rw [h1]
      have h2 : H.toEuclideanLin (v i) = (lam i : ℂ) • v i := by
        ext p
        change (H *ᵥ ⇑(v i)) p = _
        rw [hH_herm.mulVec_eigenvectorBasis i]
        simp; rfl
      rw [h2, map_smul]
    rw [hKH_v, inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hsum_lam : ∑ i : X ⊕ Y, lam i = realTraceNorm A := by
    rw [← hM_norm]
    have htrH : H.trace = ∑ i : X ⊕ Y, (lam i : ℂ) := by
      rw [htrace_basis H]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h2 : H.toEuclideanLin (v i) = (lam i : ℂ) • v i := by
        ext p
        change (H *ᵥ ⇑(v i)) p = _
        rw [hH_herm.mulVec_eigenvectorBasis i]
        simp; rfl
      rw [h2, inner_smul_right, orthonormal_iff_ite.mp v.orthonormal i i]
      simp
    change _ = H.trace.re
    rw [htrH, Complex.re_sum]
    simp
  have hK_bound : ∀ i : X ⊕ Y, ‖K.toEuclideanLin (v i)‖ ≤ spectralNorm B := by
    intro i
    have hU_norm : ‖K.toEuclideanLin (v i)‖ = ‖N.toEuclideanLin (v i)‖ := by
      have h1 : K.toEuclideanLin (v i) = Uᴴ.toEuclideanLin (N.toEuclideanLin (v i)) := by
        change Matrix.toLpLin 2 2 (Uᴴ * N) (v i) = _
        rw [Matrix.toLpLin_mul_same]; rfl
      rw [h1, norm_toEuclideanLin_conjTranspose_of_unitary hU]
    rw [hU_norm]
    let wY : EuclideanSpace ℂ Y := WithLp.toLp 2 fun y => (v i).ofLp (Sum.inr y)
    have hNw : ‖N.toEuclideanLin (v i)‖ = ‖Bℂ.toEuclideanLin wY‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
        EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
      have hY0 : ∑ y : Y, ‖(N.toEuclideanLin (v i)).ofLp (Sum.inr y)‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun y _ => ?_
        simp [N, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
      rw [hY0, add_zero]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      simp [N, Bℂ, wY, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
    have hwY_le : ‖wY‖ ≤ 1 := by
      have hsq : ‖wY‖ ^ 2 ≤ 1 := by
        calc ‖wY‖ ^ 2 = ∑ y : Y, ‖(v i).ofLp (Sum.inr y)‖ ^ 2 := by
              simp [EuclideanSpace.norm_sq_eq, wY]
          _ ≤ ∑ x : X, ‖(v i).ofLp (Sum.inl x)‖ ^ 2 +
              ∑ y : Y, ‖(v i).ofLp (Sum.inr y)‖ ^ 2 :=
              le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          _ = ‖v i‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
          _ = 1 := by rw [v.orthonormal.1 i, one_pow]
      nlinarith [norm_nonneg wY]
    rw [hNw]
    exact (norm_mulVec_ofReal_le B wY).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hwY_le (spectralNorm_nonneg B))
  rw [hinner_eq, hMN_eq, hKH_re]
  calc ∑ i : X ⊕ Y, lam i * (inner ℂ (v i) (K.toEuclideanLin (v i))).re
      ≤ ∑ i : X ⊕ Y, lam i * spectralNorm B := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hlam_nn : 0 ≤ lam i := hH_psd.eigenvalues_nonneg i
        have hre_le : (inner ℂ (v i) (K.toEuclideanLin (v i))).re ≤ spectralNorm B := by
          calc (inner ℂ (v i) (K.toEuclideanLin (v i))).re
              ≤ ‖inner ℂ (v i) (K.toEuclideanLin (v i))‖ := Complex.re_le_norm _
            _ ≤ ‖v i‖ * ‖K.toEuclideanLin (v i)‖ := norm_inner_le_norm _ _
            _ = ‖K.toEuclideanLin (v i)‖ := by rw [v.orthonormal.1 i, one_mul]
            _ ≤ spectralNorm B := hK_bound i
        exact mul_le_mul_of_nonneg_left hre_le hlam_nn
    _ = (∑ i : X ⊕ Y, lam i) * spectralNorm B := (Finset.sum_mul _ _ _).symm
    _ = realTraceNorm A * spectralNorm B := by rw [hsum_lam]

end CslibFrontier.CommunicationComplexity
